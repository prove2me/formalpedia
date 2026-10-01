-- Prove2me | solution 1 for syracuse_descends_range_1991435_1993435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:24.376825+00:00
-- url     : https://prove2.me/submissions/a74343e7-c0a7-4672-8fe2-1688a9e9a804

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

theorem B2240365 : Blo 1991435 2240365 := bbase (se 3 (by rfl) ⟨420068, by rfl⟩ : syracuseStep 2240365 = 840137) (by norm_num)
theorem B2987153 : Blo 1991435 2987153 := bstep (se 2 (by rfl) ⟨1120182, by rfl⟩ : syracuseStep 2987153 = 2240365) B2240365
theorem B1991435 : Blo 1991435 1991435 := bstep (se 1 (by rfl) ⟨1493576, by rfl⟩ : syracuseStep 1991435 = 2987153) B2987153
theorem B6721109 : Blo 1991435 6721109 := bbase (se 8 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 6721109 = 78763) (by norm_num)
theorem B4480739 : Blo 1991435 4480739 := bstep (se 1 (by rfl) ⟨3360554, by rfl⟩ : syracuseStep 4480739 = 6721109) B6721109
theorem B2987159 : Blo 1991435 2987159 := bstep (se 1 (by rfl) ⟨2240369, by rfl⟩ : syracuseStep 2987159 = 4480739) B4480739
theorem B1991439 : Blo 1991435 1991439 := bstep (se 1 (by rfl) ⟨1493579, by rfl⟩ : syracuseStep 1991439 = 2987159) B2987159
theorem B2987165 : Blo 1991435 2987165 := bbase (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) (by norm_num)
theorem B1991443 : Blo 1991435 1991443 := bstep (se 1 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 1991443 = 2987165) B2987165
theorem B4480757 : Blo 1991435 4480757 := bbase (se 5 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 4480757 = 420071) (by norm_num)
theorem B2987171 : Blo 1991435 2987171 := bstep (se 1 (by rfl) ⟨2240378, by rfl⟩ : syracuseStep 2987171 = 4480757) B4480757
theorem B1991447 : Blo 1991435 1991447 := bstep (se 1 (by rfl) ⟨1493585, by rfl⟩ : syracuseStep 1991447 = 2987171) B2987171
theorem B9569765 : Blo 1991435 9569765 := bbase (se 4 (by rfl) ⟨897165, by rfl⟩ : syracuseStep 9569765 = 1794331) (by norm_num)
theorem B25519373 : Blo 1991435 25519373 := bstep (se 3 (by rfl) ⟨4784882, by rfl⟩ : syracuseStep 25519373 = 9569765) B9569765
theorem B17012915 : Blo 1991435 17012915 := bstep (se 1 (by rfl) ⟨12759686, by rfl⟩ : syracuseStep 17012915 = 25519373) B25519373
theorem B11341943 : Blo 1991435 11341943 := bstep (se 1 (by rfl) ⟨8506457, by rfl⟩ : syracuseStep 11341943 = 17012915) B17012915
theorem B7561295 : Blo 1991435 7561295 := bstep (se 1 (by rfl) ⟨5670971, by rfl⟩ : syracuseStep 7561295 = 11341943) B11341943
theorem B5040863 : Blo 1991435 5040863 := bstep (se 1 (by rfl) ⟨3780647, by rfl⟩ : syracuseStep 5040863 = 7561295) B7561295
theorem B3360575 : Blo 1991435 3360575 := bstep (se 1 (by rfl) ⟨2520431, by rfl⟩ : syracuseStep 3360575 = 5040863) B5040863
theorem B2240383 : Blo 1991435 2240383 := bstep (se 1 (by rfl) ⟨1680287, by rfl⟩ : syracuseStep 2240383 = 3360575) B3360575
theorem B2987177 : Blo 1991435 2987177 := bstep (se 2 (by rfl) ⟨1120191, by rfl⟩ : syracuseStep 2987177 = 2240383) B2240383
theorem B1991451 : Blo 1991435 1991451 := bstep (se 1 (by rfl) ⟨1493588, by rfl⟩ : syracuseStep 1991451 = 2987177) B2987177
theorem B4253237 : Blo 1991435 4253237 := bbase (se 5 (by rfl) ⟨199370, by rfl⟩ : syracuseStep 4253237 = 398741) (by norm_num)
theorem B2835491 : Blo 1991435 2835491 := bstep (se 1 (by rfl) ⟨2126618, by rfl⟩ : syracuseStep 2835491 = 4253237) B4253237
theorem B7561309 : Blo 1991435 7561309 := bstep (se 3 (by rfl) ⟨1417745, by rfl⟩ : syracuseStep 7561309 = 2835491) B2835491
theorem B10081745 : Blo 1991435 10081745 := bstep (se 2 (by rfl) ⟨3780654, by rfl⟩ : syracuseStep 10081745 = 7561309) B7561309
theorem B6721163 : Blo 1991435 6721163 := bstep (se 1 (by rfl) ⟨5040872, by rfl⟩ : syracuseStep 6721163 = 10081745) B10081745
theorem B4480775 : Blo 1991435 4480775 := bstep (se 1 (by rfl) ⟨3360581, by rfl⟩ : syracuseStep 4480775 = 6721163) B6721163
theorem B2987183 : Blo 1991435 2987183 := bstep (se 1 (by rfl) ⟨2240387, by rfl⟩ : syracuseStep 2987183 = 4480775) B4480775
theorem B1991455 : Blo 1991435 1991455 := bstep (se 1 (by rfl) ⟨1493591, by rfl⟩ : syracuseStep 1991455 = 2987183) B2987183
theorem B2987189 : Blo 1991435 2987189 := bbase (se 5 (by rfl) ⟨140024, by rfl⟩ : syracuseStep 2987189 = 280049) (by norm_num)
theorem B1991459 : Blo 1991435 1991459 := bstep (se 1 (by rfl) ⟨1493594, by rfl⟩ : syracuseStep 1991459 = 2987189) B2987189
theorem B5040893 : Blo 1991435 5040893 := bbase (se 3 (by rfl) ⟨945167, by rfl⟩ : syracuseStep 5040893 = 1890335) (by norm_num)
theorem B3360595 : Blo 1991435 3360595 := bstep (se 1 (by rfl) ⟨2520446, by rfl⟩ : syracuseStep 3360595 = 5040893) B5040893
theorem B4480793 : Blo 1991435 4480793 := bstep (se 2 (by rfl) ⟨1680297, by rfl⟩ : syracuseStep 4480793 = 3360595) B3360595
theorem B2987195 : Blo 1991435 2987195 := bstep (se 1 (by rfl) ⟨2240396, by rfl⟩ : syracuseStep 2987195 = 4480793) B4480793
theorem B1991463 : Blo 1991435 1991463 := bstep (se 1 (by rfl) ⟨1493597, by rfl⟩ : syracuseStep 1991463 = 2987195) B2987195
theorem B2240401 : Blo 1991435 2240401 := bbase (se 2 (by rfl) ⟨840150, by rfl⟩ : syracuseStep 2240401 = 1680301) (by norm_num)
theorem B2987201 : Blo 1991435 2987201 := bstep (se 2 (by rfl) ⟨1120200, by rfl⟩ : syracuseStep 2987201 = 2240401) B2240401
theorem B1991467 : Blo 1991435 1991467 := bstep (se 1 (by rfl) ⟨1493600, by rfl⟩ : syracuseStep 1991467 = 2987201) B2987201
theorem B3780685 : Blo 1991435 3780685 := bbase (se 3 (by rfl) ⟨708878, by rfl⟩ : syracuseStep 3780685 = 1417757) (by norm_num)
theorem B5040913 : Blo 1991435 5040913 := bstep (se 2 (by rfl) ⟨1890342, by rfl⟩ : syracuseStep 5040913 = 3780685) B3780685
theorem B6721217 : Blo 1991435 6721217 := bstep (se 2 (by rfl) ⟨2520456, by rfl⟩ : syracuseStep 6721217 = 5040913) B5040913
theorem B4480811 : Blo 1991435 4480811 := bstep (se 1 (by rfl) ⟨3360608, by rfl⟩ : syracuseStep 4480811 = 6721217) B6721217
theorem B2987207 : Blo 1991435 2987207 := bstep (se 1 (by rfl) ⟨2240405, by rfl⟩ : syracuseStep 2987207 = 4480811) B4480811
theorem B1991471 : Blo 1991435 1991471 := bstep (se 1 (by rfl) ⟨1493603, by rfl⟩ : syracuseStep 1991471 = 2987207) B2987207
theorem B2987213 : Blo 1991435 2987213 := bbase (se 3 (by rfl) ⟨560102, by rfl⟩ : syracuseStep 2987213 = 1120205) (by norm_num)
theorem B1991475 : Blo 1991435 1991475 := bstep (se 1 (by rfl) ⟨1493606, by rfl⟩ : syracuseStep 1991475 = 2987213) B2987213
theorem B4480829 : Blo 1991435 4480829 := bbase (se 3 (by rfl) ⟨840155, by rfl⟩ : syracuseStep 4480829 = 1680311) (by norm_num)
theorem B2987219 : Blo 1991435 2987219 := bstep (se 1 (by rfl) ⟨2240414, by rfl⟩ : syracuseStep 2987219 = 4480829) B4480829
theorem B1991479 : Blo 1991435 1991479 := bstep (se 1 (by rfl) ⟨1493609, by rfl⟩ : syracuseStep 1991479 = 2987219) B2987219
theorem B3360629 : Blo 1991435 3360629 := bbase (se 5 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 3360629 = 315059) (by norm_num)
theorem B2240419 : Blo 1991435 2240419 := bstep (se 1 (by rfl) ⟨1680314, by rfl⟩ : syracuseStep 2240419 = 3360629) B3360629
theorem B2987225 : Blo 1991435 2987225 := bstep (se 2 (by rfl) ⟨1120209, by rfl⟩ : syracuseStep 2987225 = 2240419) B2240419
theorem B1991483 : Blo 1991435 1991483 := bstep (se 1 (by rfl) ⟨1493612, by rfl⟩ : syracuseStep 1991483 = 2987225) B2987225
theorem B3027989 : Blo 1991435 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B8074637 : Blo 1991435 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B5383091 : Blo 1991435 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B3588727 : Blo 1991435 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B4784969 : Blo 1991435 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B3189979 : Blo 1991435 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B4253305 : Blo 1991435 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B5671073 : Blo 1991435 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B15122861 : Blo 1991435 15122861 := bstep (se 3 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 15122861 = 5671073) B5671073
theorem B10081907 : Blo 1991435 10081907 := bstep (se 1 (by rfl) ⟨7561430, by rfl⟩ : syracuseStep 10081907 = 15122861) B15122861
theorem B6721271 : Blo 1991435 6721271 := bstep (se 1 (by rfl) ⟨5040953, by rfl⟩ : syracuseStep 6721271 = 10081907) B10081907
theorem B4480847 : Blo 1991435 4480847 := bstep (se 1 (by rfl) ⟨3360635, by rfl⟩ : syracuseStep 4480847 = 6721271) B6721271
theorem B2987231 : Blo 1991435 2987231 := bstep (se 1 (by rfl) ⟨2240423, by rfl⟩ : syracuseStep 2987231 = 4480847) B4480847
theorem B1991487 : Blo 1991435 1991487 := bstep (se 1 (by rfl) ⟨1493615, by rfl⟩ : syracuseStep 1991487 = 2987231) B2987231
theorem B2987237 : Blo 1991435 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B1991491 : Blo 1991435 1991491 := bstep (se 1 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 1991491 = 2987237) B2987237
theorem B4784989 : Blo 1991435 4784989 := bbase (se 3 (by rfl) ⟨897185, by rfl⟩ : syracuseStep 4784989 = 1794371) (by norm_num)
theorem B6379985 : Blo 1991435 6379985 := bstep (se 2 (by rfl) ⟨2392494, by rfl⟩ : syracuseStep 6379985 = 4784989) B4784989
theorem B4253323 : Blo 1991435 4253323 := bstep (se 1 (by rfl) ⟨3189992, by rfl⟩ : syracuseStep 4253323 = 6379985) B6379985
theorem B5671097 : Blo 1991435 5671097 := bstep (se 2 (by rfl) ⟨2126661, by rfl⟩ : syracuseStep 5671097 = 4253323) B4253323
theorem B3780731 : Blo 1991435 3780731 := bstep (se 1 (by rfl) ⟨2835548, by rfl⟩ : syracuseStep 3780731 = 5671097) B5671097
theorem B2520487 : Blo 1991435 2520487 := bstep (se 1 (by rfl) ⟨1890365, by rfl⟩ : syracuseStep 2520487 = 3780731) B3780731
theorem B3360649 : Blo 1991435 3360649 := bstep (se 2 (by rfl) ⟨1260243, by rfl⟩ : syracuseStep 3360649 = 2520487) B2520487
theorem B4480865 : Blo 1991435 4480865 := bstep (se 2 (by rfl) ⟨1680324, by rfl⟩ : syracuseStep 4480865 = 3360649) B3360649
theorem B2987243 : Blo 1991435 2987243 := bstep (se 1 (by rfl) ⟨2240432, by rfl⟩ : syracuseStep 2987243 = 4480865) B4480865
theorem B1991495 : Blo 1991435 1991495 := bstep (se 1 (by rfl) ⟨1493621, by rfl⟩ : syracuseStep 1991495 = 2987243) B2987243
theorem B2240437 : Blo 1991435 2240437 := bbase (se 5 (by rfl) ⟨105020, by rfl⟩ : syracuseStep 2240437 = 210041) (by norm_num)
theorem B2987249 : Blo 1991435 2987249 := bstep (se 2 (by rfl) ⟨1120218, by rfl⟩ : syracuseStep 2987249 = 2240437) B2240437
theorem B1991499 : Blo 1991435 1991499 := bstep (se 1 (by rfl) ⟨1493624, by rfl⟩ : syracuseStep 1991499 = 2987249) B2987249
theorem B2520497 : Blo 1991435 2520497 := bbase (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) (by norm_num)
theorem B6721325 : Blo 1991435 6721325 := bstep (se 3 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 6721325 = 2520497) B2520497
theorem B4480883 : Blo 1991435 4480883 := bstep (se 1 (by rfl) ⟨3360662, by rfl⟩ : syracuseStep 4480883 = 6721325) B6721325
theorem B2987255 : Blo 1991435 2987255 := bstep (se 1 (by rfl) ⟨2240441, by rfl⟩ : syracuseStep 2987255 = 4480883) B4480883
theorem B1991503 : Blo 1991435 1991503 := bstep (se 1 (by rfl) ⟨1493627, by rfl⟩ : syracuseStep 1991503 = 2987255) B2987255
theorem B2987261 : Blo 1991435 2987261 := bbase (se 3 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 2987261 = 1120223) (by norm_num)
theorem B1991507 : Blo 1991435 1991507 := bstep (se 1 (by rfl) ⟨1493630, by rfl⟩ : syracuseStep 1991507 = 2987261) B2987261
theorem B4480901 : Blo 1991435 4480901 := bbase (se 4 (by rfl) ⟨420084, by rfl⟩ : syracuseStep 4480901 = 840169) (by norm_num)
theorem B2987267 : Blo 1991435 2987267 := bstep (se 1 (by rfl) ⟨2240450, by rfl⟩ : syracuseStep 2987267 = 4480901) B4480901
theorem B1991511 : Blo 1991435 1991511 := bstep (se 1 (by rfl) ⟨1493633, by rfl⟩ : syracuseStep 1991511 = 2987267) B2987267
theorem B2271025 : Blo 1991435 2271025 := bbase (se 2 (by rfl) ⟨851634, by rfl⟩ : syracuseStep 2271025 = 1703269) (by norm_num)
theorem B3028033 : Blo 1991435 3028033 := bstep (se 2 (by rfl) ⟨1135512, by rfl⟩ : syracuseStep 3028033 = 2271025) B2271025
theorem B4037377 : Blo 1991435 4037377 := bstep (se 2 (by rfl) ⟨1514016, by rfl⟩ : syracuseStep 4037377 = 3028033) B3028033
theorem B5383169 : Blo 1991435 5383169 := bstep (se 2 (by rfl) ⟨2018688, by rfl⟩ : syracuseStep 5383169 = 4037377) B4037377
theorem B3588779 : Blo 1991435 3588779 := bstep (se 1 (by rfl) ⟨2691584, by rfl⟩ : syracuseStep 3588779 = 5383169) B5383169
theorem B2392519 : Blo 1991435 2392519 := bstep (se 1 (by rfl) ⟨1794389, by rfl⟩ : syracuseStep 2392519 = 3588779) B3588779
theorem B3190025 : Blo 1991435 3190025 := bstep (se 2 (by rfl) ⟨1196259, by rfl⟩ : syracuseStep 3190025 = 2392519) B2392519
theorem B2126683 : Blo 1991435 2126683 := bstep (se 1 (by rfl) ⟨1595012, by rfl⟩ : syracuseStep 2126683 = 3190025) B3190025
theorem B2835577 : Blo 1991435 2835577 := bstep (se 2 (by rfl) ⟨1063341, by rfl⟩ : syracuseStep 2835577 = 2126683) B2126683
theorem B3780769 : Blo 1991435 3780769 := bstep (se 2 (by rfl) ⟨1417788, by rfl⟩ : syracuseStep 3780769 = 2835577) B2835577
theorem B5041025 : Blo 1991435 5041025 := bstep (se 2 (by rfl) ⟨1890384, by rfl⟩ : syracuseStep 5041025 = 3780769) B3780769
theorem B3360683 : Blo 1991435 3360683 := bstep (se 1 (by rfl) ⟨2520512, by rfl⟩ : syracuseStep 3360683 = 5041025) B5041025
theorem B2240455 : Blo 1991435 2240455 := bstep (se 1 (by rfl) ⟨1680341, by rfl⟩ : syracuseStep 2240455 = 3360683) B3360683
theorem B2987273 : Blo 1991435 2987273 := bstep (se 2 (by rfl) ⟨1120227, by rfl⟩ : syracuseStep 2987273 = 2240455) B2240455
theorem B1991515 : Blo 1991435 1991515 := bstep (se 1 (by rfl) ⟨1493636, by rfl⟩ : syracuseStep 1991515 = 2987273) B2987273
theorem B10082069 : Blo 1991435 10082069 := bbase (se 6 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 10082069 = 472597) (by norm_num)
theorem B6721379 : Blo 1991435 6721379 := bstep (se 1 (by rfl) ⟨5041034, by rfl⟩ : syracuseStep 6721379 = 10082069) B10082069
theorem B4480919 : Blo 1991435 4480919 := bstep (se 1 (by rfl) ⟨3360689, by rfl⟩ : syracuseStep 4480919 = 6721379) B6721379
theorem B2987279 : Blo 1991435 2987279 := bstep (se 1 (by rfl) ⟨2240459, by rfl⟩ : syracuseStep 2987279 = 4480919) B4480919
theorem B1991519 : Blo 1991435 1991519 := bstep (se 1 (by rfl) ⟨1493639, by rfl⟩ : syracuseStep 1991519 = 2987279) B2987279
theorem B2987285 : Blo 1991435 2987285 := bbase (se 6 (by rfl) ⟨70014, by rfl⟩ : syracuseStep 2987285 = 140029) (by norm_num)
theorem B1991523 : Blo 1991435 1991523 := bstep (se 1 (by rfl) ⟨1493642, by rfl⟩ : syracuseStep 1991523 = 2987285) B2987285
theorem B9084149 : Blo 1991435 9084149 := bbase (se 5 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 9084149 = 851639) (by norm_num)
theorem B6056099 : Blo 1991435 6056099 := bstep (se 1 (by rfl) ⟨4542074, by rfl⟩ : syracuseStep 6056099 = 9084149) B9084149
theorem B4037399 : Blo 1991435 4037399 := bstep (se 1 (by rfl) ⟨3028049, by rfl⟩ : syracuseStep 4037399 = 6056099) B6056099
theorem B2691599 : Blo 1991435 2691599 := bstep (se 1 (by rfl) ⟨2018699, by rfl⟩ : syracuseStep 2691599 = 4037399) B4037399
theorem B28710389 : Blo 1991435 28710389 := bstep (se 5 (by rfl) ⟨1345799, by rfl⟩ : syracuseStep 28710389 = 2691599) B2691599
theorem B19140259 : Blo 1991435 19140259 := bstep (se 1 (by rfl) ⟨14355194, by rfl⟩ : syracuseStep 19140259 = 28710389) B28710389
theorem B25520345 : Blo 1991435 25520345 := bstep (se 2 (by rfl) ⟨9570129, by rfl⟩ : syracuseStep 25520345 = 19140259) B19140259
theorem B17013563 : Blo 1991435 17013563 := bstep (se 1 (by rfl) ⟨12760172, by rfl⟩ : syracuseStep 17013563 = 25520345) B25520345
theorem B11342375 : Blo 1991435 11342375 := bstep (se 1 (by rfl) ⟨8506781, by rfl⟩ : syracuseStep 11342375 = 17013563) B17013563
theorem B7561583 : Blo 1991435 7561583 := bstep (se 1 (by rfl) ⟨5671187, by rfl⟩ : syracuseStep 7561583 = 11342375) B11342375
theorem B5041055 : Blo 1991435 5041055 := bstep (se 1 (by rfl) ⟨3780791, by rfl⟩ : syracuseStep 5041055 = 7561583) B7561583
theorem B3360703 : Blo 1991435 3360703 := bstep (se 1 (by rfl) ⟨2520527, by rfl⟩ : syracuseStep 3360703 = 5041055) B5041055
theorem B4480937 : Blo 1991435 4480937 := bstep (se 2 (by rfl) ⟨1680351, by rfl⟩ : syracuseStep 4480937 = 3360703) B3360703
theorem B2987291 : Blo 1991435 2987291 := bstep (se 1 (by rfl) ⟨2240468, by rfl⟩ : syracuseStep 2987291 = 4480937) B4480937
theorem B1991527 : Blo 1991435 1991527 := bstep (se 1 (by rfl) ⟨1493645, by rfl⟩ : syracuseStep 1991527 = 2987291) B2987291
theorem B2240473 : Blo 1991435 2240473 := bbase (se 2 (by rfl) ⟨840177, by rfl⟩ : syracuseStep 2240473 = 1680355) (by norm_num)
theorem B2987297 : Blo 1991435 2987297 := bstep (se 2 (by rfl) ⟨1120236, by rfl⟩ : syracuseStep 2987297 = 2240473) B2240473
theorem B1991531 : Blo 1991435 1991531 := bstep (se 1 (by rfl) ⟨1493648, by rfl⟩ : syracuseStep 1991531 = 2987297) B2987297
theorem B2835605 : Blo 1991435 2835605 := bbase (se 6 (by rfl) ⟨66459, by rfl⟩ : syracuseStep 2835605 = 132919) (by norm_num)
theorem B7561613 : Blo 1991435 7561613 := bstep (se 3 (by rfl) ⟨1417802, by rfl⟩ : syracuseStep 7561613 = 2835605) B2835605
theorem B5041075 : Blo 1991435 5041075 := bstep (se 1 (by rfl) ⟨3780806, by rfl⟩ : syracuseStep 5041075 = 7561613) B7561613
theorem B6721433 : Blo 1991435 6721433 := bstep (se 2 (by rfl) ⟨2520537, by rfl⟩ : syracuseStep 6721433 = 5041075) B5041075
theorem B4480955 : Blo 1991435 4480955 := bstep (se 1 (by rfl) ⟨3360716, by rfl⟩ : syracuseStep 4480955 = 6721433) B6721433
theorem B2987303 : Blo 1991435 2987303 := bstep (se 1 (by rfl) ⟨2240477, by rfl⟩ : syracuseStep 2987303 = 4480955) B4480955
theorem B1991535 : Blo 1991435 1991535 := bstep (se 1 (by rfl) ⟨1493651, by rfl⟩ : syracuseStep 1991535 = 2987303) B2987303
theorem B2987309 : Blo 1991435 2987309 := bbase (se 3 (by rfl) ⟨560120, by rfl⟩ : syracuseStep 2987309 = 1120241) (by norm_num)
theorem B1991539 : Blo 1991435 1991539 := bstep (se 1 (by rfl) ⟨1493654, by rfl⟩ : syracuseStep 1991539 = 2987309) B2987309
theorem B4480973 : Blo 1991435 4480973 := bbase (se 3 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 4480973 = 1680365) (by norm_num)
theorem B2987315 : Blo 1991435 2987315 := bstep (se 1 (by rfl) ⟨2240486, by rfl⟩ : syracuseStep 2987315 = 4480973) B4480973
theorem B1991543 : Blo 1991435 1991543 := bstep (se 1 (by rfl) ⟨1493657, by rfl⟩ : syracuseStep 1991543 = 2987315) B2987315
theorem B2520553 : Blo 1991435 2520553 := bbase (se 2 (by rfl) ⟨945207, by rfl⟩ : syracuseStep 2520553 = 1890415) (by norm_num)
theorem B3360737 : Blo 1991435 3360737 := bstep (se 2 (by rfl) ⟨1260276, by rfl⟩ : syracuseStep 3360737 = 2520553) B2520553
theorem B2240491 : Blo 1991435 2240491 := bstep (se 1 (by rfl) ⟨1680368, by rfl⟩ : syracuseStep 2240491 = 3360737) B3360737
theorem B2987321 : Blo 1991435 2987321 := bstep (se 2 (by rfl) ⟨1120245, by rfl⟩ : syracuseStep 2987321 = 2240491) B2240491
theorem B1991547 : Blo 1991435 1991547 := bstep (se 1 (by rfl) ⟨1493660, by rfl⟩ : syracuseStep 1991547 = 2987321) B2987321
theorem B2392561 : Blo 1991435 2392561 := bbase (se 2 (by rfl) ⟨897210, by rfl⟩ : syracuseStep 2392561 = 1794421) (by norm_num)
theorem B12760325 : Blo 1991435 12760325 := bstep (se 4 (by rfl) ⟨1196280, by rfl⟩ : syracuseStep 12760325 = 2392561) B2392561
theorem B8506883 : Blo 1991435 8506883 := bstep (se 1 (by rfl) ⟨6380162, by rfl⟩ : syracuseStep 8506883 = 12760325) B12760325
theorem B22685021 : Blo 1991435 22685021 := bstep (se 3 (by rfl) ⟨4253441, by rfl⟩ : syracuseStep 22685021 = 8506883) B8506883
theorem B15123347 : Blo 1991435 15123347 := bstep (se 1 (by rfl) ⟨11342510, by rfl⟩ : syracuseStep 15123347 = 22685021) B22685021
theorem B10082231 : Blo 1991435 10082231 := bstep (se 1 (by rfl) ⟨7561673, by rfl⟩ : syracuseStep 10082231 = 15123347) B15123347
theorem B6721487 : Blo 1991435 6721487 := bstep (se 1 (by rfl) ⟨5041115, by rfl⟩ : syracuseStep 6721487 = 10082231) B10082231
theorem B4480991 : Blo 1991435 4480991 := bstep (se 1 (by rfl) ⟨3360743, by rfl⟩ : syracuseStep 4480991 = 6721487) B6721487
theorem B2987327 : Blo 1991435 2987327 := bstep (se 1 (by rfl) ⟨2240495, by rfl⟩ : syracuseStep 2987327 = 4480991) B4480991
theorem B1991551 : Blo 1991435 1991551 := bstep (se 1 (by rfl) ⟨1493663, by rfl⟩ : syracuseStep 1991551 = 2987327) B2987327
theorem B2987333 : Blo 1991435 2987333 := bbase (se 4 (by rfl) ⟨280062, by rfl⟩ : syracuseStep 2987333 = 560125) (by norm_num)
theorem B1991555 : Blo 1991435 1991555 := bstep (se 1 (by rfl) ⟨1493666, by rfl⟩ : syracuseStep 1991555 = 2987333) B2987333
theorem B3360757 : Blo 1991435 3360757 := bbase (se 5 (by rfl) ⟨157535, by rfl⟩ : syracuseStep 3360757 = 315071) (by norm_num)
theorem B4481009 : Blo 1991435 4481009 := bstep (se 2 (by rfl) ⟨1680378, by rfl⟩ : syracuseStep 4481009 = 3360757) B3360757
theorem B2987339 : Blo 1991435 2987339 := bstep (se 1 (by rfl) ⟨2240504, by rfl⟩ : syracuseStep 2987339 = 4481009) B4481009
theorem B1991559 : Blo 1991435 1991559 := bstep (se 1 (by rfl) ⟨1493669, by rfl⟩ : syracuseStep 1991559 = 2987339) B2987339
theorem B2240509 : Blo 1991435 2240509 := bbase (se 3 (by rfl) ⟨420095, by rfl⟩ : syracuseStep 2240509 = 840191) (by norm_num)
theorem B2987345 : Blo 1991435 2987345 := bstep (se 2 (by rfl) ⟨1120254, by rfl⟩ : syracuseStep 2987345 = 2240509) B2240509
theorem B1991563 : Blo 1991435 1991563 := bstep (se 1 (by rfl) ⟨1493672, by rfl⟩ : syracuseStep 1991563 = 2987345) B2987345
theorem B6721541 : Blo 1991435 6721541 := bbase (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) (by norm_num)
theorem B4481027 : Blo 1991435 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B2987351 : Blo 1991435 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B1991567 : Blo 1991435 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B2987357 : Blo 1991435 2987357 := bbase (se 3 (by rfl) ⟨560129, by rfl⟩ : syracuseStep 2987357 = 1120259) (by norm_num)
theorem B1991571 : Blo 1991435 1991571 := bstep (se 1 (by rfl) ⟨1493678, by rfl⟩ : syracuseStep 1991571 = 2987357) B2987357
theorem B4481045 : Blo 1991435 4481045 := bbase (se 6 (by rfl) ⟨105024, by rfl⟩ : syracuseStep 4481045 = 210049) (by norm_num)
theorem B2987363 : Blo 1991435 2987363 := bstep (se 1 (by rfl) ⟨2240522, by rfl⟩ : syracuseStep 2987363 = 4481045) B4481045
theorem B1991575 : Blo 1991435 1991575 := bstep (se 1 (by rfl) ⟨1493681, by rfl⟩ : syracuseStep 1991575 = 2987363) B2987363
theorem B7561781 : Blo 1991435 7561781 := bbase (se 5 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 7561781 = 708917) (by norm_num)
theorem B5041187 : Blo 1991435 5041187 := bstep (se 1 (by rfl) ⟨3780890, by rfl⟩ : syracuseStep 5041187 = 7561781) B7561781
theorem B3360791 : Blo 1991435 3360791 := bstep (se 1 (by rfl) ⟨2520593, by rfl⟩ : syracuseStep 3360791 = 5041187) B5041187
theorem B2240527 : Blo 1991435 2240527 := bstep (se 1 (by rfl) ⟨1680395, by rfl⟩ : syracuseStep 2240527 = 3360791) B3360791
theorem B2987369 : Blo 1991435 2987369 := bstep (se 2 (by rfl) ⟨1120263, by rfl⟩ : syracuseStep 2987369 = 2240527) B2240527
theorem B1991579 : Blo 1991435 1991579 := bstep (se 1 (by rfl) ⟨1493684, by rfl⟩ : syracuseStep 1991579 = 2987369) B2987369
theorem B3190133 : Blo 1991435 3190133 := bbase (se 5 (by rfl) ⟨149537, by rfl⟩ : syracuseStep 3190133 = 299075) (by norm_num)
theorem B2126755 : Blo 1991435 2126755 := bstep (se 1 (by rfl) ⟨1595066, by rfl⟩ : syracuseStep 2126755 = 3190133) B3190133
theorem B11342693 : Blo 1991435 11342693 := bstep (se 4 (by rfl) ⟨1063377, by rfl⟩ : syracuseStep 11342693 = 2126755) B2126755
theorem B7561795 : Blo 1991435 7561795 := bstep (se 1 (by rfl) ⟨5671346, by rfl⟩ : syracuseStep 7561795 = 11342693) B11342693
theorem B10082393 : Blo 1991435 10082393 := bstep (se 2 (by rfl) ⟨3780897, by rfl⟩ : syracuseStep 10082393 = 7561795) B7561795
theorem B6721595 : Blo 1991435 6721595 := bstep (se 1 (by rfl) ⟨5041196, by rfl⟩ : syracuseStep 6721595 = 10082393) B10082393
theorem B4481063 : Blo 1991435 4481063 := bstep (se 1 (by rfl) ⟨3360797, by rfl⟩ : syracuseStep 4481063 = 6721595) B6721595
theorem B2987375 : Blo 1991435 2987375 := bstep (se 1 (by rfl) ⟨2240531, by rfl⟩ : syracuseStep 2987375 = 4481063) B4481063
theorem B1991583 : Blo 1991435 1991583 := bstep (se 1 (by rfl) ⟨1493687, by rfl⟩ : syracuseStep 1991583 = 2987375) B2987375
theorem B2987381 : Blo 1991435 2987381 := bbase (se 5 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 2987381 = 280067) (by norm_num)
theorem B1991587 : Blo 1991435 1991587 := bstep (se 1 (by rfl) ⟨1493690, by rfl⟩ : syracuseStep 1991587 = 2987381) B2987381
theorem B2835685 : Blo 1991435 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B3780913 : Blo 1991435 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B5041217 : Blo 1991435 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B3360811 : Blo 1991435 3360811 := bstep (se 1 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 3360811 = 5041217) B5041217
theorem B4481081 : Blo 1991435 4481081 := bstep (se 2 (by rfl) ⟨1680405, by rfl⟩ : syracuseStep 4481081 = 3360811) B3360811
theorem B2987387 : Blo 1991435 2987387 := bstep (se 1 (by rfl) ⟨2240540, by rfl⟩ : syracuseStep 2987387 = 4481081) B4481081
theorem B1991591 : Blo 1991435 1991591 := bstep (se 1 (by rfl) ⟨1493693, by rfl⟩ : syracuseStep 1991591 = 2987387) B2987387
theorem B2240545 : Blo 1991435 2240545 := bbase (se 2 (by rfl) ⟨840204, by rfl⟩ : syracuseStep 2240545 = 1680409) (by norm_num)
theorem B2987393 : Blo 1991435 2987393 := bstep (se 2 (by rfl) ⟨1120272, by rfl⟩ : syracuseStep 2987393 = 2240545) B2240545
theorem B1991595 : Blo 1991435 1991595 := bstep (se 1 (by rfl) ⟨1493696, by rfl⟩ : syracuseStep 1991595 = 2987393) B2987393
theorem B5041237 : Blo 1991435 5041237 := bbase (se 8 (by rfl) ⟨29538, by rfl⟩ : syracuseStep 5041237 = 59077) (by norm_num)
theorem B6721649 : Blo 1991435 6721649 := bstep (se 2 (by rfl) ⟨2520618, by rfl⟩ : syracuseStep 6721649 = 5041237) B5041237
theorem B4481099 : Blo 1991435 4481099 := bstep (se 1 (by rfl) ⟨3360824, by rfl⟩ : syracuseStep 4481099 = 6721649) B6721649
theorem B2987399 : Blo 1991435 2987399 := bstep (se 1 (by rfl) ⟨2240549, by rfl⟩ : syracuseStep 2987399 = 4481099) B4481099
theorem B1991599 : Blo 1991435 1991599 := bstep (se 1 (by rfl) ⟨1493699, by rfl⟩ : syracuseStep 1991599 = 2987399) B2987399
theorem B2987405 : Blo 1991435 2987405 := bbase (se 3 (by rfl) ⟨560138, by rfl⟩ : syracuseStep 2987405 = 1120277) (by norm_num)
theorem B1991603 : Blo 1991435 1991603 := bstep (se 1 (by rfl) ⟨1493702, by rfl⟩ : syracuseStep 1991603 = 2987405) B2987405
theorem B4481117 : Blo 1991435 4481117 := bbase (se 3 (by rfl) ⟨840209, by rfl⟩ : syracuseStep 4481117 = 1680419) (by norm_num)
theorem B2987411 : Blo 1991435 2987411 := bstep (se 1 (by rfl) ⟨2240558, by rfl⟩ : syracuseStep 2987411 = 4481117) B4481117
theorem B1991607 : Blo 1991435 1991607 := bstep (se 1 (by rfl) ⟨1493705, by rfl⟩ : syracuseStep 1991607 = 2987411) B2987411
theorem B3360845 : Blo 1991435 3360845 := bbase (se 3 (by rfl) ⟨630158, by rfl⟩ : syracuseStep 3360845 = 1260317) (by norm_num)
theorem B2240563 : Blo 1991435 2240563 := bstep (se 1 (by rfl) ⟨1680422, by rfl⟩ : syracuseStep 2240563 = 3360845) B3360845
theorem B2987417 : Blo 1991435 2987417 := bstep (se 2 (by rfl) ⟨1120281, by rfl⟩ : syracuseStep 2987417 = 2240563) B2240563
theorem B1991611 : Blo 1991435 1991611 := bstep (se 1 (by rfl) ⟨1493708, by rfl⟩ : syracuseStep 1991611 = 2987417) B2987417
theorem B7207957 : Blo 1991435 7207957 := bbase (se 6 (by rfl) ⟨168936, by rfl⟩ : syracuseStep 7207957 = 337873) (by norm_num)
theorem B9610609 : Blo 1991435 9610609 := bstep (se 2 (by rfl) ⟨3603978, by rfl⟩ : syracuseStep 9610609 = 7207957) B7207957
theorem B12814145 : Blo 1991435 12814145 := bstep (se 2 (by rfl) ⟨4805304, by rfl⟩ : syracuseStep 12814145 = 9610609) B9610609
theorem B8542763 : Blo 1991435 8542763 := bstep (se 1 (by rfl) ⟨6407072, by rfl⟩ : syracuseStep 8542763 = 12814145) B12814145
theorem B5695175 : Blo 1991435 5695175 := bstep (se 1 (by rfl) ⟨4271381, by rfl⟩ : syracuseStep 5695175 = 8542763) B8542763
theorem B3796783 : Blo 1991435 3796783 := bstep (se 1 (by rfl) ⟨2847587, by rfl⟩ : syracuseStep 3796783 = 5695175) B5695175
theorem B20249509 : Blo 1991435 20249509 := bstep (se 4 (by rfl) ⟨1898391, by rfl⟩ : syracuseStep 20249509 = 3796783) B3796783
theorem B26999345 : Blo 1991435 26999345 := bstep (se 2 (by rfl) ⟨10124754, by rfl⟩ : syracuseStep 26999345 = 20249509) B20249509
theorem B17999563 : Blo 1991435 17999563 := bstep (se 1 (by rfl) ⟨13499672, by rfl⟩ : syracuseStep 17999563 = 26999345) B26999345
theorem B23999417 : Blo 1991435 23999417 := bstep (se 2 (by rfl) ⟨8999781, by rfl⟩ : syracuseStep 23999417 = 17999563) B17999563
theorem B15999611 : Blo 1991435 15999611 := bstep (se 1 (by rfl) ⟨11999708, by rfl⟩ : syracuseStep 15999611 = 23999417) B23999417
theorem B42665629 : Blo 1991435 42665629 := bstep (se 3 (by rfl) ⟨7999805, by rfl⟩ : syracuseStep 42665629 = 15999611) B15999611
theorem B56887505 : Blo 1991435 56887505 := bstep (se 2 (by rfl) ⟨21332814, by rfl⟩ : syracuseStep 56887505 = 42665629) B42665629
theorem B37925003 : Blo 1991435 37925003 := bstep (se 1 (by rfl) ⟨28443752, by rfl⟩ : syracuseStep 37925003 = 56887505) B56887505
theorem B25283335 : Blo 1991435 25283335 := bstep (se 1 (by rfl) ⟨18962501, by rfl⟩ : syracuseStep 25283335 = 37925003) B37925003
theorem B33711113 : Blo 1991435 33711113 := bstep (se 2 (by rfl) ⟨12641667, by rfl⟩ : syracuseStep 33711113 = 25283335) B25283335
theorem B89896301 : Blo 1991435 89896301 := bstep (se 3 (by rfl) ⟨16855556, by rfl⟩ : syracuseStep 89896301 = 33711113) B33711113
theorem B59930867 : Blo 1991435 59930867 := bstep (se 1 (by rfl) ⟨44948150, by rfl⟩ : syracuseStep 59930867 = 89896301) B89896301
theorem B39953911 : Blo 1991435 39953911 := bstep (se 1 (by rfl) ⟨29965433, by rfl⟩ : syracuseStep 39953911 = 59930867) B59930867
theorem B53271881 : Blo 1991435 53271881 := bstep (se 2 (by rfl) ⟨19976955, by rfl⟩ : syracuseStep 53271881 = 39953911) B39953911
theorem B35514587 : Blo 1991435 35514587 := bstep (se 1 (by rfl) ⟨26635940, by rfl⟩ : syracuseStep 35514587 = 53271881) B53271881
theorem B23676391 : Blo 1991435 23676391 := bstep (se 1 (by rfl) ⟨17757293, by rfl⟩ : syracuseStep 23676391 = 35514587) B35514587
theorem B31568521 : Blo 1991435 31568521 := bstep (se 2 (by rfl) ⟨11838195, by rfl⟩ : syracuseStep 31568521 = 23676391) B23676391
theorem B42091361 : Blo 1991435 42091361 := bstep (se 2 (by rfl) ⟨15784260, by rfl⟩ : syracuseStep 42091361 = 31568521) B31568521
theorem B448974517 : Blo 1991435 448974517 := bstep (se 5 (by rfl) ⟨21045680, by rfl⟩ : syracuseStep 448974517 = 42091361) B42091361
theorem B598632689 : Blo 1991435 598632689 := bstep (se 2 (by rfl) ⟨224487258, by rfl⟩ : syracuseStep 598632689 = 448974517) B448974517
theorem B399088459 : Blo 1991435 399088459 := bstep (se 1 (by rfl) ⟨299316344, by rfl⟩ : syracuseStep 399088459 = 598632689) B598632689
theorem B532117945 : Blo 1991435 532117945 := bstep (se 2 (by rfl) ⟨199544229, by rfl⟩ : syracuseStep 532117945 = 399088459) B399088459
theorem B709490593 : Blo 1991435 709490593 := bstep (se 2 (by rfl) ⟨266058972, by rfl⟩ : syracuseStep 709490593 = 532117945) B532117945
theorem B945987457 : Blo 1991435 945987457 := bstep (se 2 (by rfl) ⟨354745296, by rfl⟩ : syracuseStep 945987457 = 709490593) B709490593
theorem B1261316609 : Blo 1991435 1261316609 := bstep (se 2 (by rfl) ⟨472993728, by rfl⟩ : syracuseStep 1261316609 = 945987457) B945987457
theorem B840877739 : Blo 1991435 840877739 := bstep (se 1 (by rfl) ⟨630658304, by rfl⟩ : syracuseStep 840877739 = 1261316609) B1261316609
theorem B560585159 : Blo 1991435 560585159 := bstep (se 1 (by rfl) ⟨420438869, by rfl⟩ : syracuseStep 560585159 = 840877739) B840877739
theorem B373723439 : Blo 1991435 373723439 := bstep (se 1 (by rfl) ⟨280292579, by rfl⟩ : syracuseStep 373723439 = 560585159) B560585159
theorem B3986383349 : Blo 1991435 3986383349 := bstep (se 5 (by rfl) ⟨186861719, by rfl⟩ : syracuseStep 3986383349 = 373723439) B373723439
theorem B10630355597 : Blo 1991435 10630355597 := bstep (se 3 (by rfl) ⟨1993191674, by rfl⟩ : syracuseStep 10630355597 = 3986383349) B3986383349
theorem B7086903731 : Blo 1991435 7086903731 := bstep (se 1 (by rfl) ⟨5315177798, by rfl⟩ : syracuseStep 7086903731 = 10630355597) B10630355597
theorem B4724602487 : Blo 1991435 4724602487 := bstep (se 1 (by rfl) ⟨3543451865, by rfl⟩ : syracuseStep 4724602487 = 7086903731) B7086903731
theorem B3149734991 : Blo 1991435 3149734991 := bstep (se 1 (by rfl) ⟨2362301243, by rfl⟩ : syracuseStep 3149734991 = 4724602487) B4724602487
theorem B8399293309 : Blo 1991435 8399293309 := bstep (se 3 (by rfl) ⟨1574867495, by rfl⟩ : syracuseStep 8399293309 = 3149734991) B3149734991
theorem B11199057745 : Blo 1991435 11199057745 := bstep (se 2 (by rfl) ⟨4199646654, by rfl⟩ : syracuseStep 11199057745 = 8399293309) B8399293309
theorem B14932076993 : Blo 1991435 14932076993 := bstep (se 2 (by rfl) ⟨5599528872, by rfl⟩ : syracuseStep 14932076993 = 11199057745) B11199057745
theorem B9954717995 : Blo 1991435 9954717995 := bstep (se 1 (by rfl) ⟨7466038496, by rfl⟩ : syracuseStep 9954717995 = 14932076993) B14932076993
theorem B6636478663 : Blo 1991435 6636478663 := bstep (se 1 (by rfl) ⟨4977358997, by rfl⟩ : syracuseStep 6636478663 = 9954717995) B9954717995
theorem B8848638217 : Blo 1991435 8848638217 := bstep (se 2 (by rfl) ⟨3318239331, by rfl⟩ : syracuseStep 8848638217 = 6636478663) B6636478663
theorem B11798184289 : Blo 1991435 11798184289 := bstep (se 2 (by rfl) ⟨4424319108, by rfl⟩ : syracuseStep 11798184289 = 8848638217) B8848638217
theorem B15730912385 : Blo 1991435 15730912385 := bstep (se 2 (by rfl) ⟨5899092144, by rfl⟩ : syracuseStep 15730912385 = 11798184289) B11798184289
theorem B10487274923 : Blo 1991435 10487274923 := bstep (se 1 (by rfl) ⟨7865456192, by rfl⟩ : syracuseStep 10487274923 = 15730912385) B15730912385
theorem B6991516615 : Blo 1991435 6991516615 := bstep (se 1 (by rfl) ⟨5243637461, by rfl⟩ : syracuseStep 6991516615 = 10487274923) B10487274923
theorem B9322022153 : Blo 1991435 9322022153 := bstep (se 2 (by rfl) ⟨3495758307, by rfl⟩ : syracuseStep 9322022153 = 6991516615) B6991516615
theorem B6214681435 : Blo 1991435 6214681435 := bstep (se 1 (by rfl) ⟨4661011076, by rfl⟩ : syracuseStep 6214681435 = 9322022153) B9322022153
theorem B8286241913 : Blo 1991435 8286241913 := bstep (se 2 (by rfl) ⟨3107340717, by rfl⟩ : syracuseStep 8286241913 = 6214681435) B6214681435
theorem B5524161275 : Blo 1991435 5524161275 := bstep (se 1 (by rfl) ⟨4143120956, by rfl⟩ : syracuseStep 5524161275 = 8286241913) B8286241913
theorem B3682774183 : Blo 1991435 3682774183 := bstep (se 1 (by rfl) ⟨2762080637, by rfl⟩ : syracuseStep 3682774183 = 5524161275) B5524161275
theorem B4910365577 : Blo 1991435 4910365577 := bstep (se 2 (by rfl) ⟨1841387091, by rfl⟩ : syracuseStep 4910365577 = 3682774183) B3682774183
theorem B3273577051 : Blo 1991435 3273577051 := bstep (se 1 (by rfl) ⟨2455182788, by rfl⟩ : syracuseStep 3273577051 = 4910365577) B4910365577
theorem B4364769401 : Blo 1991435 4364769401 := bstep (se 2 (by rfl) ⟨1636788525, by rfl⟩ : syracuseStep 4364769401 = 3273577051) B3273577051
theorem B2909846267 : Blo 1991435 2909846267 := bstep (se 1 (by rfl) ⟨2182384700, by rfl⟩ : syracuseStep 2909846267 = 4364769401) B4364769401
theorem B1939897511 : Blo 1991435 1939897511 := bstep (se 1 (by rfl) ⟨1454923133, by rfl⟩ : syracuseStep 1939897511 = 2909846267) B2909846267
theorem B1293265007 : Blo 1991435 1293265007 := bstep (se 1 (by rfl) ⟨969948755, by rfl⟩ : syracuseStep 1293265007 = 1939897511) B1939897511
theorem B862176671 : Blo 1991435 862176671 := bstep (se 1 (by rfl) ⟨646632503, by rfl⟩ : syracuseStep 862176671 = 1293265007) B1293265007
theorem B574784447 : Blo 1991435 574784447 := bstep (se 1 (by rfl) ⟨431088335, by rfl⟩ : syracuseStep 574784447 = 862176671) B862176671
theorem B6131034101 : Blo 1991435 6131034101 := bstep (se 5 (by rfl) ⟨287392223, by rfl⟩ : syracuseStep 6131034101 = 574784447) B574784447
theorem B4087356067 : Blo 1991435 4087356067 := bstep (se 1 (by rfl) ⟨3065517050, by rfl⟩ : syracuseStep 4087356067 = 6131034101) B6131034101
theorem B5449808089 : Blo 1991435 5449808089 := bstep (se 2 (by rfl) ⟨2043678033, by rfl⟩ : syracuseStep 5449808089 = 4087356067) B4087356067
theorem B7266410785 : Blo 1991435 7266410785 := bstep (se 2 (by rfl) ⟨2724904044, by rfl⟩ : syracuseStep 7266410785 = 5449808089) B5449808089
theorem B9688547713 : Blo 1991435 9688547713 := bstep (se 2 (by rfl) ⟨3633205392, by rfl⟩ : syracuseStep 9688547713 = 7266410785) B7266410785
theorem B12918063617 : Blo 1991435 12918063617 := bstep (se 2 (by rfl) ⟨4844273856, by rfl⟩ : syracuseStep 12918063617 = 9688547713) B9688547713
theorem B8612042411 : Blo 1991435 8612042411 := bstep (se 1 (by rfl) ⟨6459031808, by rfl⟩ : syracuseStep 8612042411 = 12918063617) B12918063617
theorem B5741361607 : Blo 1991435 5741361607 := bstep (se 1 (by rfl) ⟨4306021205, by rfl⟩ : syracuseStep 5741361607 = 8612042411) B8612042411
theorem B7655148809 : Blo 1991435 7655148809 := bstep (se 2 (by rfl) ⟨2870680803, by rfl⟩ : syracuseStep 7655148809 = 5741361607) B5741361607
theorem B5103432539 : Blo 1991435 5103432539 := bstep (se 1 (by rfl) ⟨3827574404, by rfl⟩ : syracuseStep 5103432539 = 7655148809) B7655148809
theorem B3402288359 : Blo 1991435 3402288359 := bstep (se 1 (by rfl) ⟨2551716269, by rfl⟩ : syracuseStep 3402288359 = 5103432539) B5103432539
theorem B2268192239 : Blo 1991435 2268192239 := bstep (se 1 (by rfl) ⟨1701144179, by rfl⟩ : syracuseStep 2268192239 = 3402288359) B3402288359
theorem B1512128159 : Blo 1991435 1512128159 := bstep (se 1 (by rfl) ⟨1134096119, by rfl⟩ : syracuseStep 1512128159 = 2268192239) B2268192239
theorem B1008085439 : Blo 1991435 1008085439 := bstep (se 1 (by rfl) ⟨756064079, by rfl⟩ : syracuseStep 1008085439 = 1512128159) B1512128159
theorem B2688227837 : Blo 1991435 2688227837 := bstep (se 3 (by rfl) ⟨504042719, by rfl⟩ : syracuseStep 2688227837 = 1008085439) B1008085439
theorem B1792151891 : Blo 1991435 1792151891 := bstep (se 1 (by rfl) ⟨1344113918, by rfl⟩ : syracuseStep 1792151891 = 2688227837) B2688227837
theorem B1194767927 : Blo 1991435 1194767927 := bstep (se 1 (by rfl) ⟨896075945, by rfl⟩ : syracuseStep 1194767927 = 1792151891) B1792151891
theorem B796511951 : Blo 1991435 796511951 := bstep (se 1 (by rfl) ⟨597383963, by rfl⟩ : syracuseStep 796511951 = 1194767927) B1194767927
theorem B531007967 : Blo 1991435 531007967 := bstep (se 1 (by rfl) ⟨398255975, by rfl⟩ : syracuseStep 531007967 = 796511951) B796511951
theorem B354005311 : Blo 1991435 354005311 := bstep (se 1 (by rfl) ⟨265503983, by rfl⟩ : syracuseStep 354005311 = 531007967) B531007967
theorem B472007081 : Blo 1991435 472007081 := bstep (se 2 (by rfl) ⟨177002655, by rfl⟩ : syracuseStep 472007081 = 354005311) B354005311
theorem B314671387 : Blo 1991435 314671387 := bstep (se 1 (by rfl) ⟨236003540, by rfl⟩ : syracuseStep 314671387 = 472007081) B472007081
theorem B419561849 : Blo 1991435 419561849 := bstep (se 2 (by rfl) ⟨157335693, by rfl⟩ : syracuseStep 419561849 = 314671387) B314671387
theorem B279707899 : Blo 1991435 279707899 := bstep (se 1 (by rfl) ⟨209780924, by rfl⟩ : syracuseStep 279707899 = 419561849) B419561849
theorem B372943865 : Blo 1991435 372943865 := bstep (se 2 (by rfl) ⟨139853949, by rfl⟩ : syracuseStep 372943865 = 279707899) B279707899
theorem B994516973 : Blo 1991435 994516973 := bstep (se 3 (by rfl) ⟨186471932, by rfl⟩ : syracuseStep 994516973 = 372943865) B372943865
theorem B663011315 : Blo 1991435 663011315 := bstep (se 1 (by rfl) ⟨497258486, by rfl⟩ : syracuseStep 663011315 = 994516973) B994516973
theorem B442007543 : Blo 1991435 442007543 := bstep (se 1 (by rfl) ⟨331505657, by rfl⟩ : syracuseStep 442007543 = 663011315) B663011315
theorem B294671695 : Blo 1991435 294671695 := bstep (se 1 (by rfl) ⟨221003771, by rfl⟩ : syracuseStep 294671695 = 442007543) B442007543
theorem B392895593 : Blo 1991435 392895593 := bstep (se 2 (by rfl) ⟨147335847, by rfl⟩ : syracuseStep 392895593 = 294671695) B294671695
theorem B261930395 : Blo 1991435 261930395 := bstep (se 1 (by rfl) ⟨196447796, by rfl⟩ : syracuseStep 261930395 = 392895593) B392895593
theorem B698481053 : Blo 1991435 698481053 := bstep (se 3 (by rfl) ⟨130965197, by rfl⟩ : syracuseStep 698481053 = 261930395) B261930395
theorem B465654035 : Blo 1991435 465654035 := bstep (se 1 (by rfl) ⟨349240526, by rfl⟩ : syracuseStep 465654035 = 698481053) B698481053
theorem B310436023 : Blo 1991435 310436023 := bstep (se 1 (by rfl) ⟨232827017, by rfl⟩ : syracuseStep 310436023 = 465654035) B465654035
theorem B413914697 : Blo 1991435 413914697 := bstep (se 2 (by rfl) ⟨155218011, by rfl⟩ : syracuseStep 413914697 = 310436023) B310436023
theorem B275943131 : Blo 1991435 275943131 := bstep (se 1 (by rfl) ⟨206957348, by rfl⟩ : syracuseStep 275943131 = 413914697) B413914697
theorem B183962087 : Blo 1991435 183962087 := bstep (se 1 (by rfl) ⟨137971565, by rfl⟩ : syracuseStep 183962087 = 275943131) B275943131
theorem B122641391 : Blo 1991435 122641391 := bstep (se 1 (by rfl) ⟨91981043, by rfl⟩ : syracuseStep 122641391 = 183962087) B183962087
theorem B81760927 : Blo 1991435 81760927 := bstep (se 1 (by rfl) ⟨61320695, by rfl⟩ : syracuseStep 81760927 = 122641391) B122641391
theorem B109014569 : Blo 1991435 109014569 := bstep (se 2 (by rfl) ⟨40880463, by rfl⟩ : syracuseStep 109014569 = 81760927) B81760927
theorem B72676379 : Blo 1991435 72676379 := bstep (se 1 (by rfl) ⟨54507284, by rfl⟩ : syracuseStep 72676379 = 109014569) B109014569
theorem B48450919 : Blo 1991435 48450919 := bstep (se 1 (by rfl) ⟨36338189, by rfl⟩ : syracuseStep 48450919 = 72676379) B72676379
theorem B64601225 : Blo 1991435 64601225 := bstep (se 2 (by rfl) ⟨24225459, by rfl⟩ : syracuseStep 64601225 = 48450919) B48450919
theorem B43067483 : Blo 1991435 43067483 := bstep (se 1 (by rfl) ⟨32300612, by rfl⟩ : syracuseStep 43067483 = 64601225) B64601225
theorem B28711655 : Blo 1991435 28711655 := bstep (se 1 (by rfl) ⟨21533741, by rfl⟩ : syracuseStep 28711655 = 43067483) B43067483
theorem B19141103 : Blo 1991435 19141103 := bstep (se 1 (by rfl) ⟨14355827, by rfl⟩ : syracuseStep 19141103 = 28711655) B28711655
theorem B12760735 : Blo 1991435 12760735 := bstep (se 1 (by rfl) ⟨9570551, by rfl⟩ : syracuseStep 12760735 = 19141103) B19141103
theorem B17014313 : Blo 1991435 17014313 := bstep (se 2 (by rfl) ⟨6380367, by rfl⟩ : syracuseStep 17014313 = 12760735) B12760735
theorem B11342875 : Blo 1991435 11342875 := bstep (se 1 (by rfl) ⟨8507156, by rfl⟩ : syracuseStep 11342875 = 17014313) B17014313
theorem B15123833 : Blo 1991435 15123833 := bstep (se 2 (by rfl) ⟨5671437, by rfl⟩ : syracuseStep 15123833 = 11342875) B11342875
theorem B10082555 : Blo 1991435 10082555 := bstep (se 1 (by rfl) ⟨7561916, by rfl⟩ : syracuseStep 10082555 = 15123833) B15123833
theorem B6721703 : Blo 1991435 6721703 := bstep (se 1 (by rfl) ⟨5041277, by rfl⟩ : syracuseStep 6721703 = 10082555) B10082555
theorem B4481135 : Blo 1991435 4481135 := bstep (se 1 (by rfl) ⟨3360851, by rfl⟩ : syracuseStep 4481135 = 6721703) B6721703
theorem B2987423 : Blo 1991435 2987423 := bstep (se 1 (by rfl) ⟨2240567, by rfl⟩ : syracuseStep 2987423 = 4481135) B4481135
theorem B1991615 : Blo 1991435 1991615 := bstep (se 1 (by rfl) ⟨1493711, by rfl⟩ : syracuseStep 1991615 = 2987423) B2987423
theorem B2987429 : Blo 1991435 2987429 := bbase (se 4 (by rfl) ⟨280071, by rfl⟩ : syracuseStep 2987429 = 560143) (by norm_num)
theorem B1991619 : Blo 1991435 1991619 := bstep (se 1 (by rfl) ⟨1493714, by rfl⟩ : syracuseStep 1991619 = 2987429) B2987429
theorem B2520649 : Blo 1991435 2520649 := bbase (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) (by norm_num)
theorem B3360865 : Blo 1991435 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B4481153 : Blo 1991435 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B2987435 : Blo 1991435 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B1991623 : Blo 1991435 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B2240581 : Blo 1991435 2240581 := bbase (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) (by norm_num)
theorem B2987441 : Blo 1991435 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B1991627 : Blo 1991435 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B3780989 : Blo 1991435 3780989 := bbase (se 3 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 3780989 = 1417871) (by norm_num)
theorem B2520659 : Blo 1991435 2520659 := bstep (se 1 (by rfl) ⟨1890494, by rfl⟩ : syracuseStep 2520659 = 3780989) B3780989
theorem B6721757 : Blo 1991435 6721757 := bstep (se 3 (by rfl) ⟨1260329, by rfl⟩ : syracuseStep 6721757 = 2520659) B2520659
theorem B4481171 : Blo 1991435 4481171 := bstep (se 1 (by rfl) ⟨3360878, by rfl⟩ : syracuseStep 4481171 = 6721757) B6721757
theorem B2987447 : Blo 1991435 2987447 := bstep (se 1 (by rfl) ⟨2240585, by rfl⟩ : syracuseStep 2987447 = 4481171) B4481171
theorem B1991631 : Blo 1991435 1991631 := bstep (se 1 (by rfl) ⟨1493723, by rfl⟩ : syracuseStep 1991631 = 2987447) B2987447
theorem B2987453 : Blo 1991435 2987453 := bbase (se 3 (by rfl) ⟨560147, by rfl⟩ : syracuseStep 2987453 = 1120295) (by norm_num)
theorem B1991635 : Blo 1991435 1991635 := bstep (se 1 (by rfl) ⟨1493726, by rfl⟩ : syracuseStep 1991635 = 2987453) B2987453
theorem B4481189 : Blo 1991435 4481189 := bbase (se 4 (by rfl) ⟨420111, by rfl⟩ : syracuseStep 4481189 = 840223) (by norm_num)
theorem B2987459 : Blo 1991435 2987459 := bstep (se 1 (by rfl) ⟨2240594, by rfl⟩ : syracuseStep 2987459 = 4481189) B4481189
theorem B1991639 : Blo 1991435 1991639 := bstep (se 1 (by rfl) ⟨1493729, by rfl⟩ : syracuseStep 1991639 = 2987459) B2987459
theorem B5041349 : Blo 1991435 5041349 := bbase (se 4 (by rfl) ⟨472626, by rfl⟩ : syracuseStep 5041349 = 945253) (by norm_num)
theorem B3360899 : Blo 1991435 3360899 := bstep (se 1 (by rfl) ⟨2520674, by rfl⟩ : syracuseStep 3360899 = 5041349) B5041349
theorem B2240599 : Blo 1991435 2240599 := bstep (se 1 (by rfl) ⟨1680449, by rfl⟩ : syracuseStep 2240599 = 3360899) B3360899
theorem B2987465 : Blo 1991435 2987465 := bstep (se 2 (by rfl) ⟨1120299, by rfl⟩ : syracuseStep 2987465 = 2240599) B2240599
theorem B1991643 : Blo 1991435 1991643 := bstep (se 1 (by rfl) ⟨1493732, by rfl⟩ : syracuseStep 1991643 = 2987465) B2987465
theorem B8075285 : Blo 1991435 8075285 := bbase (se 6 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 8075285 = 378529) (by norm_num)
theorem B5383523 : Blo 1991435 5383523 := bstep (se 1 (by rfl) ⟨4037642, by rfl⟩ : syracuseStep 5383523 = 8075285) B8075285
theorem B14356061 : Blo 1991435 14356061 := bstep (se 3 (by rfl) ⟨2691761, by rfl⟩ : syracuseStep 14356061 = 5383523) B5383523
theorem B9570707 : Blo 1991435 9570707 := bstep (se 1 (by rfl) ⟨7178030, by rfl⟩ : syracuseStep 9570707 = 14356061) B14356061
theorem B6380471 : Blo 1991435 6380471 := bstep (se 1 (by rfl) ⟨4785353, by rfl⟩ : syracuseStep 6380471 = 9570707) B9570707
theorem B4253647 : Blo 1991435 4253647 := bstep (se 1 (by rfl) ⟨3190235, by rfl⟩ : syracuseStep 4253647 = 6380471) B6380471
theorem B5671529 : Blo 1991435 5671529 := bstep (se 2 (by rfl) ⟨2126823, by rfl⟩ : syracuseStep 5671529 = 4253647) B4253647
theorem B3781019 : Blo 1991435 3781019 := bstep (se 1 (by rfl) ⟨2835764, by rfl⟩ : syracuseStep 3781019 = 5671529) B5671529
theorem B10082717 : Blo 1991435 10082717 := bstep (se 3 (by rfl) ⟨1890509, by rfl⟩ : syracuseStep 10082717 = 3781019) B3781019
theorem B6721811 : Blo 1991435 6721811 := bstep (se 1 (by rfl) ⟨5041358, by rfl⟩ : syracuseStep 6721811 = 10082717) B10082717
theorem B4481207 : Blo 1991435 4481207 := bstep (se 1 (by rfl) ⟨3360905, by rfl⟩ : syracuseStep 4481207 = 6721811) B6721811
theorem B2987471 : Blo 1991435 2987471 := bstep (se 1 (by rfl) ⟨2240603, by rfl⟩ : syracuseStep 2987471 = 4481207) B4481207
theorem B1991647 : Blo 1991435 1991647 := bstep (se 1 (by rfl) ⟨1493735, by rfl⟩ : syracuseStep 1991647 = 2987471) B2987471
theorem B2987477 : Blo 1991435 2987477 := bbase (se 7 (by rfl) ⟨35009, by rfl⟩ : syracuseStep 2987477 = 70019) (by norm_num)
theorem B1991651 : Blo 1991435 1991651 := bstep (se 1 (by rfl) ⟨1493738, by rfl⟩ : syracuseStep 1991651 = 2987477) B2987477
theorem B7562069 : Blo 1991435 7562069 := bbase (se 9 (by rfl) ⟨22154, by rfl⟩ : syracuseStep 7562069 = 44309) (by norm_num)
theorem B5041379 : Blo 1991435 5041379 := bstep (se 1 (by rfl) ⟨3781034, by rfl⟩ : syracuseStep 5041379 = 7562069) B7562069
theorem B3360919 : Blo 1991435 3360919 := bstep (se 1 (by rfl) ⟨2520689, by rfl⟩ : syracuseStep 3360919 = 5041379) B5041379
theorem B4481225 : Blo 1991435 4481225 := bstep (se 2 (by rfl) ⟨1680459, by rfl⟩ : syracuseStep 4481225 = 3360919) B3360919
theorem B2987483 : Blo 1991435 2987483 := bstep (se 1 (by rfl) ⟨2240612, by rfl⟩ : syracuseStep 2987483 = 4481225) B4481225
theorem B1991655 : Blo 1991435 1991655 := bstep (se 1 (by rfl) ⟨1493741, by rfl⟩ : syracuseStep 1991655 = 2987483) B2987483
theorem B2240617 : Blo 1991435 2240617 := bbase (se 2 (by rfl) ⟨840231, by rfl⟩ : syracuseStep 2240617 = 1680463) (by norm_num)
theorem B2987489 : Blo 1991435 2987489 := bstep (se 2 (by rfl) ⟨1120308, by rfl⟩ : syracuseStep 2987489 = 2240617) B2240617
theorem B1991659 : Blo 1991435 1991659 := bstep (se 1 (by rfl) ⟨1493744, by rfl⟩ : syracuseStep 1991659 = 2987489) B2987489
theorem B3190261 : Blo 1991435 3190261 := bbase (se 5 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 3190261 = 299087) (by norm_num)
theorem B4253681 : Blo 1991435 4253681 := bstep (se 2 (by rfl) ⟨1595130, by rfl⟩ : syracuseStep 4253681 = 3190261) B3190261
theorem B11343149 : Blo 1991435 11343149 := bstep (se 3 (by rfl) ⟨2126840, by rfl⟩ : syracuseStep 11343149 = 4253681) B4253681
theorem B7562099 : Blo 1991435 7562099 := bstep (se 1 (by rfl) ⟨5671574, by rfl⟩ : syracuseStep 7562099 = 11343149) B11343149
theorem B5041399 : Blo 1991435 5041399 := bstep (se 1 (by rfl) ⟨3781049, by rfl⟩ : syracuseStep 5041399 = 7562099) B7562099
theorem B6721865 : Blo 1991435 6721865 := bstep (se 2 (by rfl) ⟨2520699, by rfl⟩ : syracuseStep 6721865 = 5041399) B5041399
theorem B4481243 : Blo 1991435 4481243 := bstep (se 1 (by rfl) ⟨3360932, by rfl⟩ : syracuseStep 4481243 = 6721865) B6721865
theorem B2987495 : Blo 1991435 2987495 := bstep (se 1 (by rfl) ⟨2240621, by rfl⟩ : syracuseStep 2987495 = 4481243) B4481243
theorem B1991663 : Blo 1991435 1991663 := bstep (se 1 (by rfl) ⟨1493747, by rfl⟩ : syracuseStep 1991663 = 2987495) B2987495
theorem B2987501 : Blo 1991435 2987501 := bbase (se 3 (by rfl) ⟨560156, by rfl⟩ : syracuseStep 2987501 = 1120313) (by norm_num)
theorem B1991667 : Blo 1991435 1991667 := bstep (se 1 (by rfl) ⟨1493750, by rfl⟩ : syracuseStep 1991667 = 2987501) B2987501
theorem B4481261 : Blo 1991435 4481261 := bbase (se 3 (by rfl) ⟨840236, by rfl⟩ : syracuseStep 4481261 = 1680473) (by norm_num)
theorem B2987507 : Blo 1991435 2987507 := bstep (se 1 (by rfl) ⟨2240630, by rfl⟩ : syracuseStep 2987507 = 4481261) B4481261
theorem B1991671 : Blo 1991435 1991671 := bstep (se 1 (by rfl) ⟨1493753, by rfl⟩ : syracuseStep 1991671 = 2987507) B2987507
theorem B2835805 : Blo 1991435 2835805 := bbase (se 3 (by rfl) ⟨531713, by rfl⟩ : syracuseStep 2835805 = 1063427) (by norm_num)
theorem B3781073 : Blo 1991435 3781073 := bstep (se 2 (by rfl) ⟨1417902, by rfl⟩ : syracuseStep 3781073 = 2835805) B2835805
theorem B2520715 : Blo 1991435 2520715 := bstep (se 1 (by rfl) ⟨1890536, by rfl⟩ : syracuseStep 2520715 = 3781073) B3781073
theorem B3360953 : Blo 1991435 3360953 := bstep (se 2 (by rfl) ⟨1260357, by rfl⟩ : syracuseStep 3360953 = 2520715) B2520715
theorem B2240635 : Blo 1991435 2240635 := bstep (se 1 (by rfl) ⟨1680476, by rfl⟩ : syracuseStep 2240635 = 3360953) B3360953
theorem B2987513 : Blo 1991435 2987513 := bstep (se 2 (by rfl) ⟨1120317, by rfl⟩ : syracuseStep 2987513 = 2240635) B2240635
theorem B1991675 : Blo 1991435 1991675 := bstep (se 1 (by rfl) ⟨1493756, by rfl⟩ : syracuseStep 1991675 = 2987513) B2987513
theorem B76566869 : Blo 1991435 76566869 := bbase (se 10 (by rfl) ⟨112158, by rfl⟩ : syracuseStep 76566869 = 224317) (by norm_num)
theorem B51044579 : Blo 1991435 51044579 := bstep (se 1 (by rfl) ⟨38283434, by rfl⟩ : syracuseStep 51044579 = 76566869) B76566869
theorem B34029719 : Blo 1991435 34029719 := bstep (se 1 (by rfl) ⟨25522289, by rfl⟩ : syracuseStep 34029719 = 51044579) B51044579
theorem B22686479 : Blo 1991435 22686479 := bstep (se 1 (by rfl) ⟨17014859, by rfl⟩ : syracuseStep 22686479 = 34029719) B34029719
theorem B15124319 : Blo 1991435 15124319 := bstep (se 1 (by rfl) ⟨11343239, by rfl⟩ : syracuseStep 15124319 = 22686479) B22686479
theorem B10082879 : Blo 1991435 10082879 := bstep (se 1 (by rfl) ⟨7562159, by rfl⟩ : syracuseStep 10082879 = 15124319) B15124319
theorem B6721919 : Blo 1991435 6721919 := bstep (se 1 (by rfl) ⟨5041439, by rfl⟩ : syracuseStep 6721919 = 10082879) B10082879
theorem B4481279 : Blo 1991435 4481279 := bstep (se 1 (by rfl) ⟨3360959, by rfl⟩ : syracuseStep 4481279 = 6721919) B6721919
theorem B2987519 : Blo 1991435 2987519 := bstep (se 1 (by rfl) ⟨2240639, by rfl⟩ : syracuseStep 2987519 = 4481279) B4481279
theorem B1991679 : Blo 1991435 1991679 := bstep (se 1 (by rfl) ⟨1493759, by rfl⟩ : syracuseStep 1991679 = 2987519) B2987519
theorem B2987525 : Blo 1991435 2987525 := bbase (se 4 (by rfl) ⟨280080, by rfl⟩ : syracuseStep 2987525 = 560161) (by norm_num)
theorem B1991683 : Blo 1991435 1991683 := bstep (se 1 (by rfl) ⟨1493762, by rfl⟩ : syracuseStep 1991683 = 2987525) B2987525
theorem B3360973 : Blo 1991435 3360973 := bbase (se 3 (by rfl) ⟨630182, by rfl⟩ : syracuseStep 3360973 = 1260365) (by norm_num)
theorem B4481297 : Blo 1991435 4481297 := bstep (se 2 (by rfl) ⟨1680486, by rfl⟩ : syracuseStep 4481297 = 3360973) B3360973
theorem B2987531 : Blo 1991435 2987531 := bstep (se 1 (by rfl) ⟨2240648, by rfl⟩ : syracuseStep 2987531 = 4481297) B4481297
theorem B1991687 : Blo 1991435 1991687 := bstep (se 1 (by rfl) ⟨1493765, by rfl⟩ : syracuseStep 1991687 = 2987531) B2987531
theorem B2240653 : Blo 1991435 2240653 := bbase (se 3 (by rfl) ⟨420122, by rfl⟩ : syracuseStep 2240653 = 840245) (by norm_num)
theorem B2987537 : Blo 1991435 2987537 := bstep (se 2 (by rfl) ⟨1120326, by rfl⟩ : syracuseStep 2987537 = 2240653) B2240653
theorem B1991691 : Blo 1991435 1991691 := bstep (se 1 (by rfl) ⟨1493768, by rfl⟩ : syracuseStep 1991691 = 2987537) B2987537
theorem B6721973 : Blo 1991435 6721973 := bbase (se 5 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 6721973 = 630185) (by norm_num)
theorem B4481315 : Blo 1991435 4481315 := bstep (se 1 (by rfl) ⟨3360986, by rfl⟩ : syracuseStep 4481315 = 6721973) B6721973
theorem B2987543 : Blo 1991435 2987543 := bstep (se 1 (by rfl) ⟨2240657, by rfl⟩ : syracuseStep 2987543 = 4481315) B4481315
theorem B1991695 : Blo 1991435 1991695 := bstep (se 1 (by rfl) ⟨1493771, by rfl⟩ : syracuseStep 1991695 = 2987543) B2987543
theorem B2987549 : Blo 1991435 2987549 := bbase (se 3 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 2987549 = 1120331) (by norm_num)
theorem B1991699 : Blo 1991435 1991699 := bstep (se 1 (by rfl) ⟨1493774, by rfl⟩ : syracuseStep 1991699 = 2987549) B2987549
theorem B4481333 : Blo 1991435 4481333 := bbase (se 5 (by rfl) ⟨210062, by rfl⟩ : syracuseStep 4481333 = 420125) (by norm_num)
theorem B2987555 : Blo 1991435 2987555 := bstep (se 1 (by rfl) ⟨2240666, by rfl⟩ : syracuseStep 2987555 = 4481333) B4481333
theorem B1991703 : Blo 1991435 1991703 := bstep (se 1 (by rfl) ⟨1493777, by rfl⟩ : syracuseStep 1991703 = 2987555) B2987555
theorem B3153973 : Blo 1991435 3153973 := bbase (se 5 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 3153973 = 295685) (by norm_num)
theorem B4205297 : Blo 1991435 4205297 := bstep (se 2 (by rfl) ⟨1576986, by rfl⟩ : syracuseStep 4205297 = 3153973) B3153973
theorem B11214125 : Blo 1991435 11214125 := bstep (se 3 (by rfl) ⟨2102648, by rfl⟩ : syracuseStep 11214125 = 4205297) B4205297
theorem B7476083 : Blo 1991435 7476083 := bstep (se 1 (by rfl) ⟨5607062, by rfl⟩ : syracuseStep 7476083 = 11214125) B11214125
theorem B4984055 : Blo 1991435 4984055 := bstep (se 1 (by rfl) ⟨3738041, by rfl⟩ : syracuseStep 4984055 = 7476083) B7476083
theorem B3322703 : Blo 1991435 3322703 := bstep (se 1 (by rfl) ⟨2492027, by rfl⟩ : syracuseStep 3322703 = 4984055) B4984055
theorem B2215135 : Blo 1991435 2215135 := bstep (se 1 (by rfl) ⟨1661351, by rfl⟩ : syracuseStep 2215135 = 3322703) B3322703
theorem B2953513 : Blo 1991435 2953513 := bstep (se 2 (by rfl) ⟨1107567, by rfl⟩ : syracuseStep 2953513 = 2215135) B2215135
theorem B15752069 : Blo 1991435 15752069 := bstep (se 4 (by rfl) ⟨1476756, by rfl⟩ : syracuseStep 15752069 = 2953513) B2953513
theorem B10501379 : Blo 1991435 10501379 := bstep (se 1 (by rfl) ⟨7876034, by rfl⟩ : syracuseStep 10501379 = 15752069) B15752069
theorem B7000919 : Blo 1991435 7000919 := bstep (se 1 (by rfl) ⟨5250689, by rfl⟩ : syracuseStep 7000919 = 10501379) B10501379
theorem B4667279 : Blo 1991435 4667279 := bstep (se 1 (by rfl) ⟨3500459, by rfl⟩ : syracuseStep 4667279 = 7000919) B7000919
theorem B12446077 : Blo 1991435 12446077 := bstep (se 3 (by rfl) ⟨2333639, by rfl⟩ : syracuseStep 12446077 = 4667279) B4667279
theorem B16594769 : Blo 1991435 16594769 := bstep (se 2 (by rfl) ⟨6223038, by rfl⟩ : syracuseStep 16594769 = 12446077) B12446077
theorem B44252717 : Blo 1991435 44252717 := bstep (se 3 (by rfl) ⟨8297384, by rfl⟩ : syracuseStep 44252717 = 16594769) B16594769
theorem B118007245 : Blo 1991435 118007245 := bstep (se 3 (by rfl) ⟨22126358, by rfl⟩ : syracuseStep 118007245 = 44252717) B44252717
theorem B629371973 : Blo 1991435 629371973 := bstep (se 4 (by rfl) ⟨59003622, by rfl⟩ : syracuseStep 629371973 = 118007245) B118007245
theorem B419581315 : Blo 1991435 419581315 := bstep (se 1 (by rfl) ⟨314685986, by rfl⟩ : syracuseStep 419581315 = 629371973) B629371973
theorem B2237767013 : Blo 1991435 2237767013 := bstep (se 4 (by rfl) ⟨209790657, by rfl⟩ : syracuseStep 2237767013 = 419581315) B419581315
theorem B1491844675 : Blo 1991435 1491844675 := bstep (se 1 (by rfl) ⟨1118883506, by rfl⟩ : syracuseStep 1491844675 = 2237767013) B2237767013
theorem B1989126233 : Blo 1991435 1989126233 := bstep (se 2 (by rfl) ⟨745922337, by rfl⟩ : syracuseStep 1989126233 = 1491844675) B1491844675
theorem B1326084155 : Blo 1991435 1326084155 := bstep (se 1 (by rfl) ⟨994563116, by rfl⟩ : syracuseStep 1326084155 = 1989126233) B1989126233
theorem B884056103 : Blo 1991435 884056103 := bstep (se 1 (by rfl) ⟨663042077, by rfl⟩ : syracuseStep 884056103 = 1326084155) B1326084155
theorem B589370735 : Blo 1991435 589370735 := bstep (se 1 (by rfl) ⟨442028051, by rfl⟩ : syracuseStep 589370735 = 884056103) B884056103
theorem B392913823 : Blo 1991435 392913823 := bstep (se 1 (by rfl) ⟨294685367, by rfl⟩ : syracuseStep 392913823 = 589370735) B589370735
theorem B523885097 : Blo 1991435 523885097 := bstep (se 2 (by rfl) ⟨196456911, by rfl⟩ : syracuseStep 523885097 = 392913823) B392913823
theorem B349256731 : Blo 1991435 349256731 := bstep (se 1 (by rfl) ⟨261942548, by rfl⟩ : syracuseStep 349256731 = 523885097) B523885097
theorem B465675641 : Blo 1991435 465675641 := bstep (se 2 (by rfl) ⟨174628365, by rfl⟩ : syracuseStep 465675641 = 349256731) B349256731
theorem B310450427 : Blo 1991435 310450427 := bstep (se 1 (by rfl) ⟨232837820, by rfl⟩ : syracuseStep 310450427 = 465675641) B465675641
theorem B206966951 : Blo 1991435 206966951 := bstep (se 1 (by rfl) ⟨155225213, by rfl⟩ : syracuseStep 206966951 = 310450427) B310450427
theorem B137977967 : Blo 1991435 137977967 := bstep (se 1 (by rfl) ⟨103483475, by rfl⟩ : syracuseStep 137977967 = 206966951) B206966951
theorem B91985311 : Blo 1991435 91985311 := bstep (se 1 (by rfl) ⟨68988983, by rfl⟩ : syracuseStep 91985311 = 137977967) B137977967
theorem B122647081 : Blo 1991435 122647081 := bstep (se 2 (by rfl) ⟨45992655, by rfl⟩ : syracuseStep 122647081 = 91985311) B91985311
theorem B163529441 : Blo 1991435 163529441 := bstep (se 2 (by rfl) ⟨61323540, by rfl⟩ : syracuseStep 163529441 = 122647081) B122647081
theorem B109019627 : Blo 1991435 109019627 := bstep (se 1 (by rfl) ⟨81764720, by rfl⟩ : syracuseStep 109019627 = 163529441) B163529441
theorem B72679751 : Blo 1991435 72679751 := bstep (se 1 (by rfl) ⟨54509813, by rfl⟩ : syracuseStep 72679751 = 109019627) B109019627
theorem B48453167 : Blo 1991435 48453167 := bstep (se 1 (by rfl) ⟨36339875, by rfl⟩ : syracuseStep 48453167 = 72679751) B72679751
theorem B32302111 : Blo 1991435 32302111 := bstep (se 1 (by rfl) ⟨24226583, by rfl⟩ : syracuseStep 32302111 = 48453167) B48453167
theorem B43069481 : Blo 1991435 43069481 := bstep (se 2 (by rfl) ⟨16151055, by rfl⟩ : syracuseStep 43069481 = 32302111) B32302111
theorem B28712987 : Blo 1991435 28712987 := bstep (se 1 (by rfl) ⟨21534740, by rfl⟩ : syracuseStep 28712987 = 43069481) B43069481
theorem B19141991 : Blo 1991435 19141991 := bstep (se 1 (by rfl) ⟨14356493, by rfl⟩ : syracuseStep 19141991 = 28712987) B28712987
theorem B12761327 : Blo 1991435 12761327 := bstep (se 1 (by rfl) ⟨9570995, by rfl⟩ : syracuseStep 12761327 = 19141991) B19141991
theorem B8507551 : Blo 1991435 8507551 := bstep (se 1 (by rfl) ⟨6380663, by rfl⟩ : syracuseStep 8507551 = 12761327) B12761327
theorem B11343401 : Blo 1991435 11343401 := bstep (se 2 (by rfl) ⟨4253775, by rfl⟩ : syracuseStep 11343401 = 8507551) B8507551
theorem B7562267 : Blo 1991435 7562267 := bstep (se 1 (by rfl) ⟨5671700, by rfl⟩ : syracuseStep 7562267 = 11343401) B11343401
theorem B5041511 : Blo 1991435 5041511 := bstep (se 1 (by rfl) ⟨3781133, by rfl⟩ : syracuseStep 5041511 = 7562267) B7562267
theorem B3361007 : Blo 1991435 3361007 := bstep (se 1 (by rfl) ⟨2520755, by rfl⟩ : syracuseStep 3361007 = 5041511) B5041511
theorem B2240671 : Blo 1991435 2240671 := bstep (se 1 (by rfl) ⟨1680503, by rfl⟩ : syracuseStep 2240671 = 3361007) B3361007
theorem B2987561 : Blo 1991435 2987561 := bstep (se 2 (by rfl) ⟨1120335, by rfl⟩ : syracuseStep 2987561 = 2240671) B2240671
theorem B1991707 : Blo 1991435 1991707 := bstep (se 1 (by rfl) ⟨1493780, by rfl⟩ : syracuseStep 1991707 = 2987561) B2987561
theorem B18169973 : Blo 1991435 18169973 := bbase (se 5 (by rfl) ⟨851717, by rfl⟩ : syracuseStep 18169973 = 1703435) (by norm_num)
theorem B12113315 : Blo 1991435 12113315 := bstep (se 1 (by rfl) ⟨9084986, by rfl⟩ : syracuseStep 12113315 = 18169973) B18169973
theorem B8075543 : Blo 1991435 8075543 := bstep (se 1 (by rfl) ⟨6056657, by rfl⟩ : syracuseStep 8075543 = 12113315) B12113315
theorem B21534781 : Blo 1991435 21534781 := bstep (se 3 (by rfl) ⟨4037771, by rfl⟩ : syracuseStep 21534781 = 8075543) B8075543
theorem B28713041 : Blo 1991435 28713041 := bstep (se 2 (by rfl) ⟨10767390, by rfl⟩ : syracuseStep 28713041 = 21534781) B21534781
theorem B19142027 : Blo 1991435 19142027 := bstep (se 1 (by rfl) ⟨14356520, by rfl⟩ : syracuseStep 19142027 = 28713041) B28713041
theorem B12761351 : Blo 1991435 12761351 := bstep (se 1 (by rfl) ⟨9571013, by rfl⟩ : syracuseStep 12761351 = 19142027) B19142027
theorem B8507567 : Blo 1991435 8507567 := bstep (se 1 (by rfl) ⟨6380675, by rfl⟩ : syracuseStep 8507567 = 12761351) B12761351
theorem B5671711 : Blo 1991435 5671711 := bstep (se 1 (by rfl) ⟨4253783, by rfl⟩ : syracuseStep 5671711 = 8507567) B8507567
theorem B7562281 : Blo 1991435 7562281 := bstep (se 2 (by rfl) ⟨2835855, by rfl⟩ : syracuseStep 7562281 = 5671711) B5671711
theorem B10083041 : Blo 1991435 10083041 := bstep (se 2 (by rfl) ⟨3781140, by rfl⟩ : syracuseStep 10083041 = 7562281) B7562281
theorem B6722027 : Blo 1991435 6722027 := bstep (se 1 (by rfl) ⟨5041520, by rfl⟩ : syracuseStep 6722027 = 10083041) B10083041
theorem B4481351 : Blo 1991435 4481351 := bstep (se 1 (by rfl) ⟨3361013, by rfl⟩ : syracuseStep 4481351 = 6722027) B6722027
theorem B2987567 : Blo 1991435 2987567 := bstep (se 1 (by rfl) ⟨2240675, by rfl⟩ : syracuseStep 2987567 = 4481351) B4481351
theorem B1991711 : Blo 1991435 1991711 := bstep (se 1 (by rfl) ⟨1493783, by rfl⟩ : syracuseStep 1991711 = 2987567) B2987567
theorem B2987573 : Blo 1991435 2987573 := bbase (se 5 (by rfl) ⟨140042, by rfl⟩ : syracuseStep 2987573 = 280085) (by norm_num)
theorem B1991715 : Blo 1991435 1991715 := bstep (se 1 (by rfl) ⟨1493786, by rfl⟩ : syracuseStep 1991715 = 2987573) B2987573
theorem B5041541 : Blo 1991435 5041541 := bbase (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) (by norm_num)
theorem B3361027 : Blo 1991435 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B4481369 : Blo 1991435 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B2987579 : Blo 1991435 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B1991719 : Blo 1991435 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B2240689 : Blo 1991435 2240689 := bbase (se 2 (by rfl) ⟨840258, by rfl⟩ : syracuseStep 2240689 = 1680517) (by norm_num)
theorem B2987585 : Blo 1991435 2987585 := bstep (se 2 (by rfl) ⟨1120344, by rfl⟩ : syracuseStep 2987585 = 2240689) B2240689
theorem B1991723 : Blo 1991435 1991723 := bstep (se 1 (by rfl) ⟨1493792, by rfl⟩ : syracuseStep 1991723 = 2987585) B2987585
theorem B2126909 : Blo 1991435 2126909 := bbase (se 3 (by rfl) ⟨398795, by rfl⟩ : syracuseStep 2126909 = 797591) (by norm_num)
theorem B5671757 : Blo 1991435 5671757 := bstep (se 3 (by rfl) ⟨1063454, by rfl⟩ : syracuseStep 5671757 = 2126909) B2126909
theorem B3781171 : Blo 1991435 3781171 := bstep (se 1 (by rfl) ⟨2835878, by rfl⟩ : syracuseStep 3781171 = 5671757) B5671757
theorem B5041561 : Blo 1991435 5041561 := bstep (se 2 (by rfl) ⟨1890585, by rfl⟩ : syracuseStep 5041561 = 3781171) B3781171
theorem B6722081 : Blo 1991435 6722081 := bstep (se 2 (by rfl) ⟨2520780, by rfl⟩ : syracuseStep 6722081 = 5041561) B5041561
theorem B4481387 : Blo 1991435 4481387 := bstep (se 1 (by rfl) ⟨3361040, by rfl⟩ : syracuseStep 4481387 = 6722081) B6722081
theorem B2987591 : Blo 1991435 2987591 := bstep (se 1 (by rfl) ⟨2240693, by rfl⟩ : syracuseStep 2987591 = 4481387) B4481387
theorem B1991727 : Blo 1991435 1991727 := bstep (se 1 (by rfl) ⟨1493795, by rfl⟩ : syracuseStep 1991727 = 2987591) B2987591
theorem B2987597 : Blo 1991435 2987597 := bbase (se 3 (by rfl) ⟨560174, by rfl⟩ : syracuseStep 2987597 = 1120349) (by norm_num)
theorem B1991731 : Blo 1991435 1991731 := bstep (se 1 (by rfl) ⟨1493798, by rfl⟩ : syracuseStep 1991731 = 2987597) B2987597
theorem B4481405 : Blo 1991435 4481405 := bbase (se 3 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 4481405 = 1680527) (by norm_num)
theorem B2987603 : Blo 1991435 2987603 := bstep (se 1 (by rfl) ⟨2240702, by rfl⟩ : syracuseStep 2987603 = 4481405) B4481405
theorem B1991735 : Blo 1991435 1991735 := bstep (se 1 (by rfl) ⟨1493801, by rfl⟩ : syracuseStep 1991735 = 2987603) B2987603
theorem B3361061 : Blo 1991435 3361061 := bbase (se 4 (by rfl) ⟨315099, by rfl⟩ : syracuseStep 3361061 = 630199) (by norm_num)
theorem B2240707 : Blo 1991435 2240707 := bstep (se 1 (by rfl) ⟨1680530, by rfl⟩ : syracuseStep 2240707 = 3361061) B3361061
theorem B2987609 : Blo 1991435 2987609 := bstep (se 2 (by rfl) ⟨1120353, by rfl⟩ : syracuseStep 2987609 = 2240707) B2240707
theorem B1991739 : Blo 1991435 1991739 := bstep (se 1 (by rfl) ⟨1493804, by rfl⟩ : syracuseStep 1991739 = 2987609) B2987609
theorem B2835901 : Blo 1991435 2835901 := bbase (se 3 (by rfl) ⟨531731, by rfl⟩ : syracuseStep 2835901 = 1063463) (by norm_num)
theorem B15124805 : Blo 1991435 15124805 := bstep (se 4 (by rfl) ⟨1417950, by rfl⟩ : syracuseStep 15124805 = 2835901) B2835901
theorem B10083203 : Blo 1991435 10083203 := bstep (se 1 (by rfl) ⟨7562402, by rfl⟩ : syracuseStep 10083203 = 15124805) B15124805
theorem B6722135 : Blo 1991435 6722135 := bstep (se 1 (by rfl) ⟨5041601, by rfl⟩ : syracuseStep 6722135 = 10083203) B10083203
theorem B4481423 : Blo 1991435 4481423 := bstep (se 1 (by rfl) ⟨3361067, by rfl⟩ : syracuseStep 4481423 = 6722135) B6722135
theorem B2987615 : Blo 1991435 2987615 := bstep (se 1 (by rfl) ⟨2240711, by rfl⟩ : syracuseStep 2987615 = 4481423) B4481423
theorem B1991743 : Blo 1991435 1991743 := bstep (se 1 (by rfl) ⟨1493807, by rfl⟩ : syracuseStep 1991743 = 2987615) B2987615
theorem B2987621 : Blo 1991435 2987621 := bbase (se 4 (by rfl) ⟨280089, by rfl⟩ : syracuseStep 2987621 = 560179) (by norm_num)
theorem B1991747 : Blo 1991435 1991747 := bstep (se 1 (by rfl) ⟨1493810, by rfl⟩ : syracuseStep 1991747 = 2987621) B2987621
theorem B4785605 : Blo 1991435 4785605 := bbase (se 4 (by rfl) ⟨448650, by rfl⟩ : syracuseStep 4785605 = 897301) (by norm_num)
theorem B3190403 : Blo 1991435 3190403 := bstep (se 1 (by rfl) ⟨2392802, by rfl⟩ : syracuseStep 3190403 = 4785605) B4785605
theorem B2126935 : Blo 1991435 2126935 := bstep (se 1 (by rfl) ⟨1595201, by rfl⟩ : syracuseStep 2126935 = 3190403) B3190403
theorem B2835913 : Blo 1991435 2835913 := bstep (se 2 (by rfl) ⟨1063467, by rfl⟩ : syracuseStep 2835913 = 2126935) B2126935
theorem B3781217 : Blo 1991435 3781217 := bstep (se 2 (by rfl) ⟨1417956, by rfl⟩ : syracuseStep 3781217 = 2835913) B2835913
theorem B2520811 : Blo 1991435 2520811 := bstep (se 1 (by rfl) ⟨1890608, by rfl⟩ : syracuseStep 2520811 = 3781217) B3781217
theorem B3361081 : Blo 1991435 3361081 := bstep (se 2 (by rfl) ⟨1260405, by rfl⟩ : syracuseStep 3361081 = 2520811) B2520811
theorem B4481441 : Blo 1991435 4481441 := bstep (se 2 (by rfl) ⟨1680540, by rfl⟩ : syracuseStep 4481441 = 3361081) B3361081
theorem B2987627 : Blo 1991435 2987627 := bstep (se 1 (by rfl) ⟨2240720, by rfl⟩ : syracuseStep 2987627 = 4481441) B4481441
theorem B1991751 : Blo 1991435 1991751 := bstep (se 1 (by rfl) ⟨1493813, by rfl⟩ : syracuseStep 1991751 = 2987627) B2987627
theorem B2240725 : Blo 1991435 2240725 := bbase (se 7 (by rfl) ⟨26258, by rfl⟩ : syracuseStep 2240725 = 52517) (by norm_num)
theorem B2987633 : Blo 1991435 2987633 := bstep (se 2 (by rfl) ⟨1120362, by rfl⟩ : syracuseStep 2987633 = 2240725) B2240725
theorem B1991755 : Blo 1991435 1991755 := bstep (se 1 (by rfl) ⟨1493816, by rfl⟩ : syracuseStep 1991755 = 2987633) B2987633
theorem B2520821 : Blo 1991435 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B6722189 : Blo 1991435 6722189 := bstep (se 3 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 6722189 = 2520821) B2520821
theorem B4481459 : Blo 1991435 4481459 := bstep (se 1 (by rfl) ⟨3361094, by rfl⟩ : syracuseStep 4481459 = 6722189) B6722189
theorem B2987639 : Blo 1991435 2987639 := bstep (se 1 (by rfl) ⟨2240729, by rfl⟩ : syracuseStep 2987639 = 4481459) B4481459
theorem B1991759 : Blo 1991435 1991759 := bstep (se 1 (by rfl) ⟨1493819, by rfl⟩ : syracuseStep 1991759 = 2987639) B2987639
theorem B2987645 : Blo 1991435 2987645 := bbase (se 3 (by rfl) ⟨560183, by rfl⟩ : syracuseStep 2987645 = 1120367) (by norm_num)
theorem B1991763 : Blo 1991435 1991763 := bstep (se 1 (by rfl) ⟨1493822, by rfl⟩ : syracuseStep 1991763 = 2987645) B2987645
theorem B4481477 : Blo 1991435 4481477 := bbase (se 4 (by rfl) ⟨420138, by rfl⟩ : syracuseStep 4481477 = 840277) (by norm_num)
theorem B2987651 : Blo 1991435 2987651 := bstep (se 1 (by rfl) ⟨2240738, by rfl⟩ : syracuseStep 2987651 = 4481477) B4481477
theorem B1991767 : Blo 1991435 1991767 := bstep (se 1 (by rfl) ⟨1493825, by rfl⟩ : syracuseStep 1991767 = 2987651) B2987651
theorem B6380869 : Blo 1991435 6380869 := bbase (se 4 (by rfl) ⟨598206, by rfl⟩ : syracuseStep 6380869 = 1196413) (by norm_num)
theorem B8507825 : Blo 1991435 8507825 := bstep (se 2 (by rfl) ⟨3190434, by rfl⟩ : syracuseStep 8507825 = 6380869) B6380869
theorem B5671883 : Blo 1991435 5671883 := bstep (se 1 (by rfl) ⟨4253912, by rfl⟩ : syracuseStep 5671883 = 8507825) B8507825
theorem B3781255 : Blo 1991435 3781255 := bstep (se 1 (by rfl) ⟨2835941, by rfl⟩ : syracuseStep 3781255 = 5671883) B5671883
theorem B5041673 : Blo 1991435 5041673 := bstep (se 2 (by rfl) ⟨1890627, by rfl⟩ : syracuseStep 5041673 = 3781255) B3781255
theorem B3361115 : Blo 1991435 3361115 := bstep (se 1 (by rfl) ⟨2520836, by rfl⟩ : syracuseStep 3361115 = 5041673) B5041673
theorem B2240743 : Blo 1991435 2240743 := bstep (se 1 (by rfl) ⟨1680557, by rfl⟩ : syracuseStep 2240743 = 3361115) B3361115
theorem B2987657 : Blo 1991435 2987657 := bstep (se 2 (by rfl) ⟨1120371, by rfl⟩ : syracuseStep 2987657 = 2240743) B2240743
theorem B1991771 : Blo 1991435 1991771 := bstep (se 1 (by rfl) ⟨1493828, by rfl⟩ : syracuseStep 1991771 = 2987657) B2987657
theorem B10083365 : Blo 1991435 10083365 := bbase (se 4 (by rfl) ⟨945315, by rfl⟩ : syracuseStep 10083365 = 1890631) (by norm_num)
theorem B6722243 : Blo 1991435 6722243 := bstep (se 1 (by rfl) ⟨5041682, by rfl⟩ : syracuseStep 6722243 = 10083365) B10083365
theorem B4481495 : Blo 1991435 4481495 := bstep (se 1 (by rfl) ⟨3361121, by rfl⟩ : syracuseStep 4481495 = 6722243) B6722243
theorem B2987663 : Blo 1991435 2987663 := bstep (se 1 (by rfl) ⟨2240747, by rfl⟩ : syracuseStep 2987663 = 4481495) B4481495
theorem B1991775 : Blo 1991435 1991775 := bstep (se 1 (by rfl) ⟨1493831, by rfl⟩ : syracuseStep 1991775 = 2987663) B2987663
theorem B2987669 : Blo 1991435 2987669 := bbase (se 6 (by rfl) ⟨70023, by rfl⟩ : syracuseStep 2987669 = 140047) (by norm_num)
theorem B1991779 : Blo 1991435 1991779 := bstep (se 1 (by rfl) ⟨1493834, by rfl⟩ : syracuseStep 1991779 = 2987669) B2987669
theorem B12761813 : Blo 1991435 12761813 := bbase (se 7 (by rfl) ⟨149552, by rfl⟩ : syracuseStep 12761813 = 299105) (by norm_num)
theorem B8507875 : Blo 1991435 8507875 := bstep (se 1 (by rfl) ⟨6380906, by rfl⟩ : syracuseStep 8507875 = 12761813) B12761813
theorem B11343833 : Blo 1991435 11343833 := bstep (se 2 (by rfl) ⟨4253937, by rfl⟩ : syracuseStep 11343833 = 8507875) B8507875
theorem B7562555 : Blo 1991435 7562555 := bstep (se 1 (by rfl) ⟨5671916, by rfl⟩ : syracuseStep 7562555 = 11343833) B11343833
theorem B5041703 : Blo 1991435 5041703 := bstep (se 1 (by rfl) ⟨3781277, by rfl⟩ : syracuseStep 5041703 = 7562555) B7562555
theorem B3361135 : Blo 1991435 3361135 := bstep (se 1 (by rfl) ⟨2520851, by rfl⟩ : syracuseStep 3361135 = 5041703) B5041703
theorem B4481513 : Blo 1991435 4481513 := bstep (se 2 (by rfl) ⟨1680567, by rfl⟩ : syracuseStep 4481513 = 3361135) B3361135
theorem B2987675 : Blo 1991435 2987675 := bstep (se 1 (by rfl) ⟨2240756, by rfl⟩ : syracuseStep 2987675 = 4481513) B4481513
theorem B1991783 : Blo 1991435 1991783 := bstep (se 1 (by rfl) ⟨1493837, by rfl⟩ : syracuseStep 1991783 = 2987675) B2987675
theorem B2240761 : Blo 1991435 2240761 := bbase (se 2 (by rfl) ⟨840285, by rfl⟩ : syracuseStep 2240761 = 1680571) (by norm_num)
theorem B2987681 : Blo 1991435 2987681 := bstep (se 2 (by rfl) ⟨1120380, by rfl⟩ : syracuseStep 2987681 = 2240761) B2240761
theorem B1991787 : Blo 1991435 1991787 := bstep (se 1 (by rfl) ⟨1493840, by rfl⟩ : syracuseStep 1991787 = 2987681) B2987681
theorem B8507909 : Blo 1991435 8507909 := bbase (se 4 (by rfl) ⟨797616, by rfl⟩ : syracuseStep 8507909 = 1595233) (by norm_num)
theorem B5671939 : Blo 1991435 5671939 := bstep (se 1 (by rfl) ⟨4253954, by rfl⟩ : syracuseStep 5671939 = 8507909) B8507909
theorem B7562585 : Blo 1991435 7562585 := bstep (se 2 (by rfl) ⟨2835969, by rfl⟩ : syracuseStep 7562585 = 5671939) B5671939
theorem B5041723 : Blo 1991435 5041723 := bstep (se 1 (by rfl) ⟨3781292, by rfl⟩ : syracuseStep 5041723 = 7562585) B7562585
theorem B6722297 : Blo 1991435 6722297 := bstep (se 2 (by rfl) ⟨2520861, by rfl⟩ : syracuseStep 6722297 = 5041723) B5041723
theorem B4481531 : Blo 1991435 4481531 := bstep (se 1 (by rfl) ⟨3361148, by rfl⟩ : syracuseStep 4481531 = 6722297) B6722297
theorem B2987687 : Blo 1991435 2987687 := bstep (se 1 (by rfl) ⟨2240765, by rfl⟩ : syracuseStep 2987687 = 4481531) B4481531
theorem B1991791 : Blo 1991435 1991791 := bstep (se 1 (by rfl) ⟨1493843, by rfl⟩ : syracuseStep 1991791 = 2987687) B2987687
theorem B2987693 : Blo 1991435 2987693 := bbase (se 3 (by rfl) ⟨560192, by rfl⟩ : syracuseStep 2987693 = 1120385) (by norm_num)
theorem B1991795 : Blo 1991435 1991795 := bstep (se 1 (by rfl) ⟨1493846, by rfl⟩ : syracuseStep 1991795 = 2987693) B2987693
theorem B4481549 : Blo 1991435 4481549 := bbase (se 3 (by rfl) ⟨840290, by rfl⟩ : syracuseStep 4481549 = 1680581) (by norm_num)
theorem B2987699 : Blo 1991435 2987699 := bstep (se 1 (by rfl) ⟨2240774, by rfl⟩ : syracuseStep 2987699 = 4481549) B4481549
theorem B1991799 : Blo 1991435 1991799 := bstep (se 1 (by rfl) ⟨1493849, by rfl⟩ : syracuseStep 1991799 = 2987699) B2987699
theorem B2520877 : Blo 1991435 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B3361169 : Blo 1991435 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B2240779 : Blo 1991435 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B2987705 : Blo 1991435 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B1991803 : Blo 1991435 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B2590141 : Blo 1991435 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B3453521 : Blo 1991435 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B9209389 : Blo 1991435 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B12279185 : Blo 1991435 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B8186123 : Blo 1991435 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B5457415 : Blo 1991435 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B7276553 : Blo 1991435 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B4851035 : Blo 1991435 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B3234023 : Blo 1991435 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B2156015 : Blo 1991435 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B5749373 : Blo 1991435 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B3832915 : Blo 1991435 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B5110553 : Blo 1991435 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B3407035 : Blo 1991435 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B4542713 : Blo 1991435 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B3028475 : Blo 1991435 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B8075933 : Blo 1991435 8075933 := bstep (se 3 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 8075933 = 3028475) B3028475
theorem B5383955 : Blo 1991435 5383955 := bstep (se 1 (by rfl) ⟨4037966, by rfl⟩ : syracuseStep 5383955 = 8075933) B8075933
theorem B3589303 : Blo 1991435 3589303 := bstep (se 1 (by rfl) ⟨2691977, by rfl⟩ : syracuseStep 3589303 = 5383955) B5383955
theorem B4785737 : Blo 1991435 4785737 := bstep (se 2 (by rfl) ⟨1794651, by rfl⟩ : syracuseStep 4785737 = 3589303) B3589303
theorem B12761965 : Blo 1991435 12761965 := bstep (se 3 (by rfl) ⟨2392868, by rfl⟩ : syracuseStep 12761965 = 4785737) B4785737
theorem B17015953 : Blo 1991435 17015953 := bstep (se 2 (by rfl) ⟨6380982, by rfl⟩ : syracuseStep 17015953 = 12761965) B12761965
theorem B22687937 : Blo 1991435 22687937 := bstep (se 2 (by rfl) ⟨8507976, by rfl⟩ : syracuseStep 22687937 = 17015953) B17015953
theorem B15125291 : Blo 1991435 15125291 := bstep (se 1 (by rfl) ⟨11343968, by rfl⟩ : syracuseStep 15125291 = 22687937) B22687937
theorem B10083527 : Blo 1991435 10083527 := bstep (se 1 (by rfl) ⟨7562645, by rfl⟩ : syracuseStep 10083527 = 15125291) B15125291
theorem B6722351 : Blo 1991435 6722351 := bstep (se 1 (by rfl) ⟨5041763, by rfl⟩ : syracuseStep 6722351 = 10083527) B10083527
theorem B4481567 : Blo 1991435 4481567 := bstep (se 1 (by rfl) ⟨3361175, by rfl⟩ : syracuseStep 4481567 = 6722351) B6722351
theorem B2987711 : Blo 1991435 2987711 := bstep (se 1 (by rfl) ⟨2240783, by rfl⟩ : syracuseStep 2987711 = 4481567) B4481567
theorem B1991807 : Blo 1991435 1991807 := bstep (se 1 (by rfl) ⟨1493855, by rfl⟩ : syracuseStep 1991807 = 2987711) B2987711
theorem B2987717 : Blo 1991435 2987717 := bbase (se 4 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 2987717 = 560197) (by norm_num)
theorem B1991811 : Blo 1991435 1991811 := bstep (se 1 (by rfl) ⟨1493858, by rfl⟩ : syracuseStep 1991811 = 2987717) B2987717
theorem B3361189 : Blo 1991435 3361189 := bbase (se 4 (by rfl) ⟨315111, by rfl⟩ : syracuseStep 3361189 = 630223) (by norm_num)
theorem B4481585 : Blo 1991435 4481585 := bstep (se 2 (by rfl) ⟨1680594, by rfl⟩ : syracuseStep 4481585 = 3361189) B3361189
theorem B2987723 : Blo 1991435 2987723 := bstep (se 1 (by rfl) ⟨2240792, by rfl⟩ : syracuseStep 2987723 = 4481585) B4481585
theorem B1991815 : Blo 1991435 1991815 := bstep (se 1 (by rfl) ⟨1493861, by rfl⟩ : syracuseStep 1991815 = 2987723) B2987723
theorem B2240797 : Blo 1991435 2240797 := bbase (se 3 (by rfl) ⟨420149, by rfl⟩ : syracuseStep 2240797 = 840299) (by norm_num)
theorem B2987729 : Blo 1991435 2987729 := bstep (se 2 (by rfl) ⟨1120398, by rfl⟩ : syracuseStep 2987729 = 2240797) B2240797
theorem B1991819 : Blo 1991435 1991819 := bstep (se 1 (by rfl) ⟨1493864, by rfl⟩ : syracuseStep 1991819 = 2987729) B2987729
theorem B6722405 : Blo 1991435 6722405 := bbase (se 4 (by rfl) ⟨630225, by rfl⟩ : syracuseStep 6722405 = 1260451) (by norm_num)
theorem B4481603 : Blo 1991435 4481603 := bstep (se 1 (by rfl) ⟨3361202, by rfl⟩ : syracuseStep 4481603 = 6722405) B6722405
theorem B2987735 : Blo 1991435 2987735 := bstep (se 1 (by rfl) ⟨2240801, by rfl⟩ : syracuseStep 2987735 = 4481603) B4481603
theorem B1991823 : Blo 1991435 1991823 := bstep (se 1 (by rfl) ⟨1493867, by rfl⟩ : syracuseStep 1991823 = 2987735) B2987735
theorem B2987741 : Blo 1991435 2987741 := bbase (se 3 (by rfl) ⟨560201, by rfl⟩ : syracuseStep 2987741 = 1120403) (by norm_num)
theorem B1991827 : Blo 1991435 1991827 := bstep (se 1 (by rfl) ⟨1493870, by rfl⟩ : syracuseStep 1991827 = 2987741) B2987741
theorem B4481621 : Blo 1991435 4481621 := bbase (se 8 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 4481621 = 52519) (by norm_num)
theorem B2987747 : Blo 1991435 2987747 := bstep (se 1 (by rfl) ⟨2240810, by rfl⟩ : syracuseStep 2987747 = 4481621) B4481621
theorem B1991831 : Blo 1991435 1991831 := bstep (se 1 (by rfl) ⟨1493873, by rfl⟩ : syracuseStep 1991831 = 2987747) B2987747
theorem B7665941 : Blo 1991435 7665941 := bbase (se 6 (by rfl) ⟨179670, by rfl⟩ : syracuseStep 7665941 = 359341) (by norm_num)
theorem B5110627 : Blo 1991435 5110627 := bstep (se 1 (by rfl) ⟨3832970, by rfl⟩ : syracuseStep 5110627 = 7665941) B7665941
theorem B6814169 : Blo 1991435 6814169 := bstep (se 2 (by rfl) ⟨2555313, by rfl⟩ : syracuseStep 6814169 = 5110627) B5110627
theorem B4542779 : Blo 1991435 4542779 := bstep (se 1 (by rfl) ⟨3407084, by rfl⟩ : syracuseStep 4542779 = 6814169) B6814169
theorem B3028519 : Blo 1991435 3028519 := bstep (se 1 (by rfl) ⟨2271389, by rfl⟩ : syracuseStep 3028519 = 4542779) B4542779
theorem B4038025 : Blo 1991435 4038025 := bstep (se 2 (by rfl) ⟨1514259, by rfl⟩ : syracuseStep 4038025 = 3028519) B3028519
theorem B5384033 : Blo 1991435 5384033 := bstep (se 2 (by rfl) ⟨2019012, by rfl⟩ : syracuseStep 5384033 = 4038025) B4038025
theorem B3589355 : Blo 1991435 3589355 := bstep (se 1 (by rfl) ⟨2692016, by rfl⟩ : syracuseStep 3589355 = 5384033) B5384033
theorem B2392903 : Blo 1991435 2392903 := bstep (se 1 (by rfl) ⟨1794677, by rfl⟩ : syracuseStep 2392903 = 3589355) B3589355
theorem B3190537 : Blo 1991435 3190537 := bstep (se 2 (by rfl) ⟨1196451, by rfl⟩ : syracuseStep 3190537 = 2392903) B2392903
theorem B4254049 : Blo 1991435 4254049 := bstep (se 2 (by rfl) ⟨1595268, by rfl⟩ : syracuseStep 4254049 = 3190537) B3190537
theorem B5672065 : Blo 1991435 5672065 := bstep (se 2 (by rfl) ⟨2127024, by rfl⟩ : syracuseStep 5672065 = 4254049) B4254049
theorem B7562753 : Blo 1991435 7562753 := bstep (se 2 (by rfl) ⟨2836032, by rfl⟩ : syracuseStep 7562753 = 5672065) B5672065
theorem B5041835 : Blo 1991435 5041835 := bstep (se 1 (by rfl) ⟨3781376, by rfl⟩ : syracuseStep 5041835 = 7562753) B7562753
theorem B3361223 : Blo 1991435 3361223 := bstep (se 1 (by rfl) ⟨2520917, by rfl⟩ : syracuseStep 3361223 = 5041835) B5041835
theorem B2240815 : Blo 1991435 2240815 := bstep (se 1 (by rfl) ⟨1680611, by rfl⟩ : syracuseStep 2240815 = 3361223) B3361223
theorem B2987753 : Blo 1991435 2987753 := bstep (se 2 (by rfl) ⟨1120407, by rfl⟩ : syracuseStep 2987753 = 2240815) B2240815
theorem B1991835 : Blo 1991435 1991835 := bstep (se 1 (by rfl) ⟨1493876, by rfl⟩ : syracuseStep 1991835 = 2987753) B2987753
theorem B2692021 : Blo 1991435 2692021 := bbase (se 5 (by rfl) ⟨126188, by rfl⟩ : syracuseStep 2692021 = 252377) (by norm_num)
theorem B3589361 : Blo 1991435 3589361 := bstep (se 2 (by rfl) ⟨1346010, by rfl⟩ : syracuseStep 3589361 = 2692021) B2692021
theorem B2392907 : Blo 1991435 2392907 := bstep (se 1 (by rfl) ⟨1794680, by rfl⟩ : syracuseStep 2392907 = 3589361) B3589361
theorem B25524341 : Blo 1991435 25524341 := bstep (se 5 (by rfl) ⟨1196453, by rfl⟩ : syracuseStep 25524341 = 2392907) B2392907
theorem B17016227 : Blo 1991435 17016227 := bstep (se 1 (by rfl) ⟨12762170, by rfl⟩ : syracuseStep 17016227 = 25524341) B25524341
theorem B11344151 : Blo 1991435 11344151 := bstep (se 1 (by rfl) ⟨8508113, by rfl⟩ : syracuseStep 11344151 = 17016227) B17016227
theorem B7562767 : Blo 1991435 7562767 := bstep (se 1 (by rfl) ⟨5672075, by rfl⟩ : syracuseStep 7562767 = 11344151) B11344151
theorem B10083689 : Blo 1991435 10083689 := bstep (se 2 (by rfl) ⟨3781383, by rfl⟩ : syracuseStep 10083689 = 7562767) B7562767
theorem B6722459 : Blo 1991435 6722459 := bstep (se 1 (by rfl) ⟨5041844, by rfl⟩ : syracuseStep 6722459 = 10083689) B10083689
theorem B4481639 : Blo 1991435 4481639 := bstep (se 1 (by rfl) ⟨3361229, by rfl⟩ : syracuseStep 4481639 = 6722459) B6722459
theorem B2987759 : Blo 1991435 2987759 := bstep (se 1 (by rfl) ⟨2240819, by rfl⟩ : syracuseStep 2987759 = 4481639) B4481639
theorem B1991839 : Blo 1991435 1991839 := bstep (se 1 (by rfl) ⟨1493879, by rfl⟩ : syracuseStep 1991839 = 2987759) B2987759
theorem B2987765 : Blo 1991435 2987765 := bbase (se 5 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 2987765 = 280103) (by norm_num)
theorem B1991843 : Blo 1991435 1991843 := bstep (se 1 (by rfl) ⟨1493882, by rfl⟩ : syracuseStep 1991843 = 2987765) B2987765
theorem B8508149 : Blo 1991435 8508149 := bbase (se 5 (by rfl) ⟨398819, by rfl⟩ : syracuseStep 8508149 = 797639) (by norm_num)
theorem B5672099 : Blo 1991435 5672099 := bstep (se 1 (by rfl) ⟨4254074, by rfl⟩ : syracuseStep 5672099 = 8508149) B8508149
theorem B3781399 : Blo 1991435 3781399 := bstep (se 1 (by rfl) ⟨2836049, by rfl⟩ : syracuseStep 3781399 = 5672099) B5672099
theorem B5041865 : Blo 1991435 5041865 := bstep (se 2 (by rfl) ⟨1890699, by rfl⟩ : syracuseStep 5041865 = 3781399) B3781399
theorem B3361243 : Blo 1991435 3361243 := bstep (se 1 (by rfl) ⟨2520932, by rfl⟩ : syracuseStep 3361243 = 5041865) B5041865
theorem B4481657 : Blo 1991435 4481657 := bstep (se 2 (by rfl) ⟨1680621, by rfl⟩ : syracuseStep 4481657 = 3361243) B3361243
theorem B2987771 : Blo 1991435 2987771 := bstep (se 1 (by rfl) ⟨2240828, by rfl⟩ : syracuseStep 2987771 = 4481657) B4481657
theorem B1991847 : Blo 1991435 1991847 := bstep (se 1 (by rfl) ⟨1493885, by rfl⟩ : syracuseStep 1991847 = 2987771) B2987771
theorem B2240833 : Blo 1991435 2240833 := bbase (se 2 (by rfl) ⟨840312, by rfl⟩ : syracuseStep 2240833 = 1680625) (by norm_num)
theorem B2987777 : Blo 1991435 2987777 := bstep (se 2 (by rfl) ⟨1120416, by rfl⟩ : syracuseStep 2987777 = 2240833) B2240833
theorem B1991851 : Blo 1991435 1991851 := bstep (se 1 (by rfl) ⟨1493888, by rfl⟩ : syracuseStep 1991851 = 2987777) B2987777
theorem B5041885 : Blo 1991435 5041885 := bbase (se 3 (by rfl) ⟨945353, by rfl⟩ : syracuseStep 5041885 = 1890707) (by norm_num)
theorem B6722513 : Blo 1991435 6722513 := bstep (se 2 (by rfl) ⟨2520942, by rfl⟩ : syracuseStep 6722513 = 5041885) B5041885
theorem B4481675 : Blo 1991435 4481675 := bstep (se 1 (by rfl) ⟨3361256, by rfl⟩ : syracuseStep 4481675 = 6722513) B6722513
theorem B2987783 : Blo 1991435 2987783 := bstep (se 1 (by rfl) ⟨2240837, by rfl⟩ : syracuseStep 2987783 = 4481675) B4481675
theorem B1991855 : Blo 1991435 1991855 := bstep (se 1 (by rfl) ⟨1493891, by rfl⟩ : syracuseStep 1991855 = 2987783) B2987783
theorem B2987789 : Blo 1991435 2987789 := bbase (se 3 (by rfl) ⟨560210, by rfl⟩ : syracuseStep 2987789 = 1120421) (by norm_num)
theorem B1991859 : Blo 1991435 1991859 := bstep (se 1 (by rfl) ⟨1493894, by rfl⟩ : syracuseStep 1991859 = 2987789) B2987789
theorem B4481693 : Blo 1991435 4481693 := bbase (se 3 (by rfl) ⟨840317, by rfl⟩ : syracuseStep 4481693 = 1680635) (by norm_num)
theorem B2987795 : Blo 1991435 2987795 := bstep (se 1 (by rfl) ⟨2240846, by rfl⟩ : syracuseStep 2987795 = 4481693) B4481693
theorem B1991863 : Blo 1991435 1991863 := bstep (se 1 (by rfl) ⟨1493897, by rfl⟩ : syracuseStep 1991863 = 2987795) B2987795
theorem B3361277 : Blo 1991435 3361277 := bbase (se 3 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 3361277 = 1260479) (by norm_num)
theorem B2240851 : Blo 1991435 2240851 := bstep (se 1 (by rfl) ⟨1680638, by rfl⟩ : syracuseStep 2240851 = 3361277) B3361277
theorem B2987801 : Blo 1991435 2987801 := bstep (se 2 (by rfl) ⟨1120425, by rfl⟩ : syracuseStep 2987801 = 2240851) B2240851
theorem B1991867 : Blo 1991435 1991867 := bstep (se 1 (by rfl) ⟨1493900, by rfl⟩ : syracuseStep 1991867 = 2987801) B2987801
theorem B4254125 : Blo 1991435 4254125 := bbase (se 3 (by rfl) ⟨797648, by rfl⟩ : syracuseStep 4254125 = 1595297) (by norm_num)
theorem B11344333 : Blo 1991435 11344333 := bstep (se 3 (by rfl) ⟨2127062, by rfl⟩ : syracuseStep 11344333 = 4254125) B4254125
theorem B15125777 : Blo 1991435 15125777 := bstep (se 2 (by rfl) ⟨5672166, by rfl⟩ : syracuseStep 15125777 = 11344333) B11344333
theorem B10083851 : Blo 1991435 10083851 := bstep (se 1 (by rfl) ⟨7562888, by rfl⟩ : syracuseStep 10083851 = 15125777) B15125777
theorem B6722567 : Blo 1991435 6722567 := bstep (se 1 (by rfl) ⟨5041925, by rfl⟩ : syracuseStep 6722567 = 10083851) B10083851
theorem B4481711 : Blo 1991435 4481711 := bstep (se 1 (by rfl) ⟨3361283, by rfl⟩ : syracuseStep 4481711 = 6722567) B6722567
theorem B2987807 : Blo 1991435 2987807 := bstep (se 1 (by rfl) ⟨2240855, by rfl⟩ : syracuseStep 2987807 = 4481711) B4481711
theorem B1991871 : Blo 1991435 1991871 := bstep (se 1 (by rfl) ⟨1493903, by rfl⟩ : syracuseStep 1991871 = 2987807) B2987807
theorem B2987813 : Blo 1991435 2987813 := bbase (se 4 (by rfl) ⟨280107, by rfl⟩ : syracuseStep 2987813 = 560215) (by norm_num)
theorem B1991875 : Blo 1991435 1991875 := bstep (se 1 (by rfl) ⟨1493906, by rfl⟩ : syracuseStep 1991875 = 2987813) B2987813
theorem B2520973 : Blo 1991435 2520973 := bbase (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) (by norm_num)
theorem B3361297 : Blo 1991435 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B4481729 : Blo 1991435 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B2987819 : Blo 1991435 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B1991879 : Blo 1991435 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B2240869 : Blo 1991435 2240869 := bbase (se 4 (by rfl) ⟨210081, by rfl⟩ : syracuseStep 2240869 = 420163) (by norm_num)
theorem B2987825 : Blo 1991435 2987825 := bstep (se 2 (by rfl) ⟨1120434, by rfl⟩ : syracuseStep 2987825 = 2240869) B2240869
theorem B1991883 : Blo 1991435 1991883 := bstep (se 1 (by rfl) ⟨1493912, by rfl⟩ : syracuseStep 1991883 = 2987825) B2987825
theorem B5672213 : Blo 1991435 5672213 := bbase (se 6 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 5672213 = 265885) (by norm_num)
theorem B3781475 : Blo 1991435 3781475 := bstep (se 1 (by rfl) ⟨2836106, by rfl⟩ : syracuseStep 3781475 = 5672213) B5672213
theorem B2520983 : Blo 1991435 2520983 := bstep (se 1 (by rfl) ⟨1890737, by rfl⟩ : syracuseStep 2520983 = 3781475) B3781475
theorem B6722621 : Blo 1991435 6722621 := bstep (se 3 (by rfl) ⟨1260491, by rfl⟩ : syracuseStep 6722621 = 2520983) B2520983
theorem B4481747 : Blo 1991435 4481747 := bstep (se 1 (by rfl) ⟨3361310, by rfl⟩ : syracuseStep 4481747 = 6722621) B6722621
theorem B2987831 : Blo 1991435 2987831 := bstep (se 1 (by rfl) ⟨2240873, by rfl⟩ : syracuseStep 2987831 = 4481747) B4481747
theorem B1991887 : Blo 1991435 1991887 := bstep (se 1 (by rfl) ⟨1493915, by rfl⟩ : syracuseStep 1991887 = 2987831) B2987831
theorem B2987837 : Blo 1991435 2987837 := bbase (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) (by norm_num)
theorem B1991891 : Blo 1991435 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B4481765 : Blo 1991435 4481765 := bbase (se 4 (by rfl) ⟨420165, by rfl⟩ : syracuseStep 4481765 = 840331) (by norm_num)
theorem B2987843 : Blo 1991435 2987843 := bstep (se 1 (by rfl) ⟨2240882, by rfl⟩ : syracuseStep 2987843 = 4481765) B4481765
theorem B1991895 : Blo 1991435 1991895 := bstep (se 1 (by rfl) ⟨1493921, by rfl⟩ : syracuseStep 1991895 = 2987843) B2987843
theorem B5041997 : Blo 1991435 5041997 := bbase (se 3 (by rfl) ⟨945374, by rfl⟩ : syracuseStep 5041997 = 1890749) (by norm_num)
theorem B3361331 : Blo 1991435 3361331 := bstep (se 1 (by rfl) ⟨2520998, by rfl⟩ : syracuseStep 3361331 = 5041997) B5041997
theorem B2240887 : Blo 1991435 2240887 := bstep (se 1 (by rfl) ⟨1680665, by rfl⟩ : syracuseStep 2240887 = 3361331) B3361331
theorem B2987849 : Blo 1991435 2987849 := bstep (se 2 (by rfl) ⟨1120443, by rfl⟩ : syracuseStep 2987849 = 2240887) B2240887
theorem B1991899 : Blo 1991435 1991899 := bstep (se 1 (by rfl) ⟨1493924, by rfl⟩ : syracuseStep 1991899 = 2987849) B2987849
theorem B2127097 : Blo 1991435 2127097 := bbase (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) (by norm_num)
theorem B2836129 : Blo 1991435 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B3781505 : Blo 1991435 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B10084013 : Blo 1991435 10084013 := bstep (se 3 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 10084013 = 3781505) B3781505
theorem B6722675 : Blo 1991435 6722675 := bstep (se 1 (by rfl) ⟨5042006, by rfl⟩ : syracuseStep 6722675 = 10084013) B10084013
theorem B4481783 : Blo 1991435 4481783 := bstep (se 1 (by rfl) ⟨3361337, by rfl⟩ : syracuseStep 4481783 = 6722675) B6722675
theorem B2987855 : Blo 1991435 2987855 := bstep (se 1 (by rfl) ⟨2240891, by rfl⟩ : syracuseStep 2987855 = 4481783) B4481783
theorem B1991903 : Blo 1991435 1991903 := bstep (se 1 (by rfl) ⟨1493927, by rfl⟩ : syracuseStep 1991903 = 2987855) B2987855
theorem B2987861 : Blo 1991435 2987861 := bbase (se 9 (by rfl) ⟨8753, by rfl⟩ : syracuseStep 2987861 = 17507) (by norm_num)
theorem B1991907 : Blo 1991435 1991907 := bstep (se 1 (by rfl) ⟨1493930, by rfl⟩ : syracuseStep 1991907 = 2987861) B2987861
theorem B6381317 : Blo 1991435 6381317 := bbase (se 4 (by rfl) ⟨598248, by rfl⟩ : syracuseStep 6381317 = 1196497) (by norm_num)
theorem B4254211 : Blo 1991435 4254211 := bstep (se 1 (by rfl) ⟨3190658, by rfl⟩ : syracuseStep 4254211 = 6381317) B6381317
theorem B5672281 : Blo 1991435 5672281 := bstep (se 2 (by rfl) ⟨2127105, by rfl⟩ : syracuseStep 5672281 = 4254211) B4254211
theorem B7563041 : Blo 1991435 7563041 := bstep (se 2 (by rfl) ⟨2836140, by rfl⟩ : syracuseStep 7563041 = 5672281) B5672281
theorem B5042027 : Blo 1991435 5042027 := bstep (se 1 (by rfl) ⟨3781520, by rfl⟩ : syracuseStep 5042027 = 7563041) B7563041
theorem B3361351 : Blo 1991435 3361351 := bstep (se 1 (by rfl) ⟨2521013, by rfl⟩ : syracuseStep 3361351 = 5042027) B5042027
theorem B4481801 : Blo 1991435 4481801 := bstep (se 2 (by rfl) ⟨1680675, by rfl⟩ : syracuseStep 4481801 = 3361351) B3361351
theorem B2987867 : Blo 1991435 2987867 := bstep (se 1 (by rfl) ⟨2240900, by rfl⟩ : syracuseStep 2987867 = 4481801) B4481801
theorem B1991911 : Blo 1991435 1991911 := bstep (se 1 (by rfl) ⟨1493933, by rfl⟩ : syracuseStep 1991911 = 2987867) B2987867
theorem B2240905 : Blo 1991435 2240905 := bbase (se 2 (by rfl) ⟨840339, by rfl⟩ : syracuseStep 2240905 = 1680679) (by norm_num)
theorem B2987873 : Blo 1991435 2987873 := bstep (se 2 (by rfl) ⟨1120452, by rfl⟩ : syracuseStep 2987873 = 2240905) B2240905
theorem B1991915 : Blo 1991435 1991915 := bstep (se 1 (by rfl) ⟨1493936, by rfl⟩ : syracuseStep 1991915 = 2987873) B2987873
theorem B3028645 : Blo 1991435 3028645 := bbase (se 4 (by rfl) ⟨283935, by rfl⟩ : syracuseStep 3028645 = 567871) (by norm_num)
theorem B4038193 : Blo 1991435 4038193 := bstep (se 2 (by rfl) ⟨1514322, by rfl⟩ : syracuseStep 4038193 = 3028645) B3028645
theorem B21537029 : Blo 1991435 21537029 := bstep (se 4 (by rfl) ⟨2019096, by rfl⟩ : syracuseStep 21537029 = 4038193) B4038193
theorem B57432077 : Blo 1991435 57432077 := bstep (se 3 (by rfl) ⟨10768514, by rfl⟩ : syracuseStep 57432077 = 21537029) B21537029
theorem B38288051 : Blo 1991435 38288051 := bstep (se 1 (by rfl) ⟨28716038, by rfl⟩ : syracuseStep 38288051 = 57432077) B57432077
theorem B25525367 : Blo 1991435 25525367 := bstep (se 1 (by rfl) ⟨19144025, by rfl⟩ : syracuseStep 25525367 = 38288051) B38288051
theorem B17016911 : Blo 1991435 17016911 := bstep (se 1 (by rfl) ⟨12762683, by rfl⟩ : syracuseStep 17016911 = 25525367) B25525367
theorem B11344607 : Blo 1991435 11344607 := bstep (se 1 (by rfl) ⟨8508455, by rfl⟩ : syracuseStep 11344607 = 17016911) B17016911
theorem B7563071 : Blo 1991435 7563071 := bstep (se 1 (by rfl) ⟨5672303, by rfl⟩ : syracuseStep 7563071 = 11344607) B11344607
theorem B5042047 : Blo 1991435 5042047 := bstep (se 1 (by rfl) ⟨3781535, by rfl⟩ : syracuseStep 5042047 = 7563071) B7563071
theorem B6722729 : Blo 1991435 6722729 := bstep (se 2 (by rfl) ⟨2521023, by rfl⟩ : syracuseStep 6722729 = 5042047) B5042047
theorem B4481819 : Blo 1991435 4481819 := bstep (se 1 (by rfl) ⟨3361364, by rfl⟩ : syracuseStep 4481819 = 6722729) B6722729
theorem B2987879 : Blo 1991435 2987879 := bstep (se 1 (by rfl) ⟨2240909, by rfl⟩ : syracuseStep 2987879 = 4481819) B4481819
theorem B1991919 : Blo 1991435 1991919 := bstep (se 1 (by rfl) ⟨1493939, by rfl⟩ : syracuseStep 1991919 = 2987879) B2987879
theorem B2987885 : Blo 1991435 2987885 := bbase (se 3 (by rfl) ⟨560228, by rfl⟩ : syracuseStep 2987885 = 1120457) (by norm_num)
theorem B1991923 : Blo 1991435 1991923 := bstep (se 1 (by rfl) ⟨1493942, by rfl⟩ : syracuseStep 1991923 = 2987885) B2987885
theorem B4481837 : Blo 1991435 4481837 := bbase (se 3 (by rfl) ⟨840344, by rfl⟩ : syracuseStep 4481837 = 1680689) (by norm_num)
theorem B2987891 : Blo 1991435 2987891 := bstep (se 1 (by rfl) ⟨2240918, by rfl⟩ : syracuseStep 2987891 = 4481837) B4481837
theorem B1991927 : Blo 1991435 1991927 := bstep (se 1 (by rfl) ⟨1493945, by rfl⟩ : syracuseStep 1991927 = 2987891) B2987891
theorem B4786037 : Blo 1991435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 1991435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B8508509 : Blo 1991435 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B5672339 : Blo 1991435 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B3781559 : Blo 1991435 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B2521039 : Blo 1991435 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B3361385 : Blo 1991435 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B2240923 : Blo 1991435 2240923 := bstep (se 1 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 2240923 = 3361385) B3361385
theorem B2987897 : Blo 1991435 2987897 := bstep (se 2 (by rfl) ⟨1120461, by rfl⟩ : syracuseStep 2987897 = 2240923) B2240923
theorem B1991931 : Blo 1991435 1991931 := bstep (se 1 (by rfl) ⟨1493948, by rfl⟩ : syracuseStep 1991931 = 2987897) B2987897
theorem B12114677 : Blo 1991435 12114677 := bbase (se 5 (by rfl) ⟨567875, by rfl⟩ : syracuseStep 12114677 = 1135751) (by norm_num)
theorem B8076451 : Blo 1991435 8076451 := bstep (se 1 (by rfl) ⟨6057338, by rfl⟩ : syracuseStep 8076451 = 12114677) B12114677
theorem B10768601 : Blo 1991435 10768601 := bstep (se 2 (by rfl) ⟨4038225, by rfl⟩ : syracuseStep 10768601 = 8076451) B8076451
theorem B7179067 : Blo 1991435 7179067 := bstep (se 1 (by rfl) ⟨5384300, by rfl⟩ : syracuseStep 7179067 = 10768601) B10768601
theorem B9572089 : Blo 1991435 9572089 := bstep (se 2 (by rfl) ⟨3589533, by rfl⟩ : syracuseStep 9572089 = 7179067) B7179067
theorem B12762785 : Blo 1991435 12762785 := bstep (se 2 (by rfl) ⟨4786044, by rfl⟩ : syracuseStep 12762785 = 9572089) B9572089
theorem B34034093 : Blo 1991435 34034093 := bstep (se 3 (by rfl) ⟨6381392, by rfl⟩ : syracuseStep 34034093 = 12762785) B12762785
theorem B22689395 : Blo 1991435 22689395 := bstep (se 1 (by rfl) ⟨17017046, by rfl⟩ : syracuseStep 22689395 = 34034093) B34034093
theorem B15126263 : Blo 1991435 15126263 := bstep (se 1 (by rfl) ⟨11344697, by rfl⟩ : syracuseStep 15126263 = 22689395) B22689395
theorem B10084175 : Blo 1991435 10084175 := bstep (se 1 (by rfl) ⟨7563131, by rfl⟩ : syracuseStep 10084175 = 15126263) B15126263
theorem B6722783 : Blo 1991435 6722783 := bstep (se 1 (by rfl) ⟨5042087, by rfl⟩ : syracuseStep 6722783 = 10084175) B10084175
theorem B4481855 : Blo 1991435 4481855 := bstep (se 1 (by rfl) ⟨3361391, by rfl⟩ : syracuseStep 4481855 = 6722783) B6722783
theorem B2987903 : Blo 1991435 2987903 := bstep (se 1 (by rfl) ⟨2240927, by rfl⟩ : syracuseStep 2987903 = 4481855) B4481855
theorem B1991935 : Blo 1991435 1991935 := bstep (se 1 (by rfl) ⟨1493951, by rfl⟩ : syracuseStep 1991935 = 2987903) B2987903
theorem B2987909 : Blo 1991435 2987909 := bbase (se 4 (by rfl) ⟨280116, by rfl⟩ : syracuseStep 2987909 = 560233) (by norm_num)
theorem B1991939 : Blo 1991435 1991939 := bstep (se 1 (by rfl) ⟨1493954, by rfl⟩ : syracuseStep 1991939 = 2987909) B2987909
theorem B3361405 : Blo 1991435 3361405 := bbase (se 3 (by rfl) ⟨630263, by rfl⟩ : syracuseStep 3361405 = 1260527) (by norm_num)
theorem B4481873 : Blo 1991435 4481873 := bstep (se 2 (by rfl) ⟨1680702, by rfl⟩ : syracuseStep 4481873 = 3361405) B3361405
theorem B2987915 : Blo 1991435 2987915 := bstep (se 1 (by rfl) ⟨2240936, by rfl⟩ : syracuseStep 2987915 = 4481873) B4481873
theorem B1991943 : Blo 1991435 1991943 := bstep (se 1 (by rfl) ⟨1493957, by rfl⟩ : syracuseStep 1991943 = 2987915) B2987915
theorem B2240941 : Blo 1991435 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B2987921 : Blo 1991435 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B1991947 : Blo 1991435 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B6722837 : Blo 1991435 6722837 := bbase (se 6 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 6722837 = 315133) (by norm_num)
theorem B4481891 : Blo 1991435 4481891 := bstep (se 1 (by rfl) ⟨3361418, by rfl⟩ : syracuseStep 4481891 = 6722837) B6722837
theorem B2987927 : Blo 1991435 2987927 := bstep (se 1 (by rfl) ⟨2240945, by rfl⟩ : syracuseStep 2987927 = 4481891) B4481891
theorem B1991951 : Blo 1991435 1991951 := bstep (se 1 (by rfl) ⟨1493963, by rfl⟩ : syracuseStep 1991951 = 2987927) B2987927
theorem B2987933 : Blo 1991435 2987933 := bbase (se 3 (by rfl) ⟨560237, by rfl⟩ : syracuseStep 2987933 = 1120475) (by norm_num)
theorem B1991955 : Blo 1991435 1991955 := bstep (se 1 (by rfl) ⟨1493966, by rfl⟩ : syracuseStep 1991955 = 2987933) B2987933
theorem B4481909 : Blo 1991435 4481909 := bbase (se 5 (by rfl) ⟨210089, by rfl⟩ : syracuseStep 4481909 = 420179) (by norm_num)
theorem B2987939 : Blo 1991435 2987939 := bstep (se 1 (by rfl) ⟨2240954, by rfl⟩ : syracuseStep 2987939 = 4481909) B4481909
theorem B1991959 : Blo 1991435 1991959 := bstep (se 1 (by rfl) ⟨1493969, by rfl⟩ : syracuseStep 1991959 = 2987939) B2987939
theorem B4543069 : Blo 1991435 4543069 := bbase (se 3 (by rfl) ⟨851825, by rfl⟩ : syracuseStep 4543069 = 1703651) (by norm_num)
theorem B6057425 : Blo 1991435 6057425 := bstep (se 2 (by rfl) ⟨2271534, by rfl⟩ : syracuseStep 6057425 = 4543069) B4543069
theorem B4038283 : Blo 1991435 4038283 := bstep (se 1 (by rfl) ⟨3028712, by rfl⟩ : syracuseStep 4038283 = 6057425) B6057425
theorem B5384377 : Blo 1991435 5384377 := bstep (se 2 (by rfl) ⟨2019141, by rfl⟩ : syracuseStep 5384377 = 4038283) B4038283
theorem B28716677 : Blo 1991435 28716677 := bstep (se 4 (by rfl) ⟨2692188, by rfl⟩ : syracuseStep 28716677 = 5384377) B5384377
theorem B19144451 : Blo 1991435 19144451 := bstep (se 1 (by rfl) ⟨14358338, by rfl⟩ : syracuseStep 19144451 = 28716677) B28716677
theorem B12762967 : Blo 1991435 12762967 := bstep (se 1 (by rfl) ⟨9572225, by rfl⟩ : syracuseStep 12762967 = 19144451) B19144451
theorem B17017289 : Blo 1991435 17017289 := bstep (se 2 (by rfl) ⟨6381483, by rfl⟩ : syracuseStep 17017289 = 12762967) B12762967
theorem B11344859 : Blo 1991435 11344859 := bstep (se 1 (by rfl) ⟨8508644, by rfl⟩ : syracuseStep 11344859 = 17017289) B17017289
theorem B7563239 : Blo 1991435 7563239 := bstep (se 1 (by rfl) ⟨5672429, by rfl⟩ : syracuseStep 7563239 = 11344859) B11344859
theorem B5042159 : Blo 1991435 5042159 := bstep (se 1 (by rfl) ⟨3781619, by rfl⟩ : syracuseStep 5042159 = 7563239) B7563239
theorem B3361439 : Blo 1991435 3361439 := bstep (se 1 (by rfl) ⟨2521079, by rfl⟩ : syracuseStep 3361439 = 5042159) B5042159
theorem B2240959 : Blo 1991435 2240959 := bstep (se 1 (by rfl) ⟨1680719, by rfl⟩ : syracuseStep 2240959 = 3361439) B3361439
theorem B2987945 : Blo 1991435 2987945 := bstep (se 2 (by rfl) ⟨1120479, by rfl⟩ : syracuseStep 2987945 = 2240959) B2240959
theorem B1991963 : Blo 1991435 1991963 := bstep (se 1 (by rfl) ⟨1493972, by rfl⟩ : syracuseStep 1991963 = 2987945) B2987945
theorem B7563253 : Blo 1991435 7563253 := bbase (se 5 (by rfl) ⟨354527, by rfl⟩ : syracuseStep 7563253 = 709055) (by norm_num)
theorem B10084337 : Blo 1991435 10084337 := bstep (se 2 (by rfl) ⟨3781626, by rfl⟩ : syracuseStep 10084337 = 7563253) B7563253
theorem B6722891 : Blo 1991435 6722891 := bstep (se 1 (by rfl) ⟨5042168, by rfl⟩ : syracuseStep 6722891 = 10084337) B10084337
theorem B4481927 : Blo 1991435 4481927 := bstep (se 1 (by rfl) ⟨3361445, by rfl⟩ : syracuseStep 4481927 = 6722891) B6722891
theorem B2987951 : Blo 1991435 2987951 := bstep (se 1 (by rfl) ⟨2240963, by rfl⟩ : syracuseStep 2987951 = 4481927) B4481927
theorem B1991967 : Blo 1991435 1991967 := bstep (se 1 (by rfl) ⟨1493975, by rfl⟩ : syracuseStep 1991967 = 2987951) B2987951
theorem B2987957 : Blo 1991435 2987957 := bbase (se 5 (by rfl) ⟨140060, by rfl⟩ : syracuseStep 2987957 = 280121) (by norm_num)
theorem B1991971 : Blo 1991435 1991971 := bstep (se 1 (by rfl) ⟨1493978, by rfl⟩ : syracuseStep 1991971 = 2987957) B2987957
theorem B5042189 : Blo 1991435 5042189 := bbase (se 3 (by rfl) ⟨945410, by rfl⟩ : syracuseStep 5042189 = 1890821) (by norm_num)
theorem B3361459 : Blo 1991435 3361459 := bstep (se 1 (by rfl) ⟨2521094, by rfl⟩ : syracuseStep 3361459 = 5042189) B5042189
theorem B4481945 : Blo 1991435 4481945 := bstep (se 2 (by rfl) ⟨1680729, by rfl⟩ : syracuseStep 4481945 = 3361459) B3361459
theorem B2987963 : Blo 1991435 2987963 := bstep (se 1 (by rfl) ⟨2240972, by rfl⟩ : syracuseStep 2987963 = 4481945) B4481945
theorem B1991975 : Blo 1991435 1991975 := bstep (se 1 (by rfl) ⟨1493981, by rfl⟩ : syracuseStep 1991975 = 2987963) B2987963
theorem B2240977 : Blo 1991435 2240977 := bbase (se 2 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 2240977 = 1680733) (by norm_num)
theorem B2987969 : Blo 1991435 2987969 := bstep (se 2 (by rfl) ⟨1120488, by rfl⟩ : syracuseStep 2987969 = 2240977) B2240977
theorem B1991979 : Blo 1991435 1991979 := bstep (se 1 (by rfl) ⟨1493984, by rfl⟩ : syracuseStep 1991979 = 2987969) B2987969
theorem B4254365 : Blo 1991435 4254365 := bbase (se 3 (by rfl) ⟨797693, by rfl⟩ : syracuseStep 4254365 = 1595387) (by norm_num)
theorem B2836243 : Blo 1991435 2836243 := bstep (se 1 (by rfl) ⟨2127182, by rfl⟩ : syracuseStep 2836243 = 4254365) B4254365
theorem B3781657 : Blo 1991435 3781657 := bstep (se 2 (by rfl) ⟨1418121, by rfl⟩ : syracuseStep 3781657 = 2836243) B2836243
theorem B5042209 : Blo 1991435 5042209 := bstep (se 2 (by rfl) ⟨1890828, by rfl⟩ : syracuseStep 5042209 = 3781657) B3781657
theorem B6722945 : Blo 1991435 6722945 := bstep (se 2 (by rfl) ⟨2521104, by rfl⟩ : syracuseStep 6722945 = 5042209) B5042209
theorem B4481963 : Blo 1991435 4481963 := bstep (se 1 (by rfl) ⟨3361472, by rfl⟩ : syracuseStep 4481963 = 6722945) B6722945
theorem B2987975 : Blo 1991435 2987975 := bstep (se 1 (by rfl) ⟨2240981, by rfl⟩ : syracuseStep 2987975 = 4481963) B4481963
theorem B1991983 : Blo 1991435 1991983 := bstep (se 1 (by rfl) ⟨1493987, by rfl⟩ : syracuseStep 1991983 = 2987975) B2987975
theorem B2987981 : Blo 1991435 2987981 := bbase (se 3 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 2987981 = 1120493) (by norm_num)
theorem B1991987 : Blo 1991435 1991987 := bstep (se 1 (by rfl) ⟨1493990, by rfl⟩ : syracuseStep 1991987 = 2987981) B2987981
theorem B4481981 : Blo 1991435 4481981 := bbase (se 3 (by rfl) ⟨840371, by rfl⟩ : syracuseStep 4481981 = 1680743) (by norm_num)
theorem B2987987 : Blo 1991435 2987987 := bstep (se 1 (by rfl) ⟨2240990, by rfl⟩ : syracuseStep 2987987 = 4481981) B4481981
theorem B1991991 : Blo 1991435 1991991 := bstep (se 1 (by rfl) ⟨1493993, by rfl⟩ : syracuseStep 1991991 = 2987987) B2987987
theorem B3361493 : Blo 1991435 3361493 := bbase (se 7 (by rfl) ⟨39392, by rfl⟩ : syracuseStep 3361493 = 78785) (by norm_num)
theorem B2240995 : Blo 1991435 2240995 := bstep (se 1 (by rfl) ⟨1680746, by rfl⟩ : syracuseStep 2240995 = 3361493) B3361493
theorem B2987993 : Blo 1991435 2987993 := bstep (se 2 (by rfl) ⟨1120497, by rfl⟩ : syracuseStep 2987993 = 2240995) B2240995
theorem B1991995 : Blo 1991435 1991995 := bstep (se 1 (by rfl) ⟨1493996, by rfl⟩ : syracuseStep 1991995 = 2987993) B2987993
theorem B10768949 : Blo 1991435 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B7179299 : Blo 1991435 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B4786199 : Blo 1991435 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B3190799 : Blo 1991435 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B8508797 : Blo 1991435 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B5672531 : Blo 1991435 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B15126749 : Blo 1991435 15126749 := bstep (se 3 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 15126749 = 5672531) B5672531
theorem B10084499 : Blo 1991435 10084499 := bstep (se 1 (by rfl) ⟨7563374, by rfl⟩ : syracuseStep 10084499 = 15126749) B15126749
theorem B6722999 : Blo 1991435 6722999 := bstep (se 1 (by rfl) ⟨5042249, by rfl⟩ : syracuseStep 6722999 = 10084499) B10084499
theorem B4481999 : Blo 1991435 4481999 := bstep (se 1 (by rfl) ⟨3361499, by rfl⟩ : syracuseStep 4481999 = 6722999) B6722999
theorem B2987999 : Blo 1991435 2987999 := bstep (se 1 (by rfl) ⟨2240999, by rfl⟩ : syracuseStep 2987999 = 4481999) B4481999
theorem B1991999 : Blo 1991435 1991999 := bstep (se 1 (by rfl) ⟨1493999, by rfl⟩ : syracuseStep 1991999 = 2987999) B2987999
theorem B2988005 : Blo 1991435 2988005 := bbase (se 4 (by rfl) ⟨280125, by rfl⟩ : syracuseStep 2988005 = 560251) (by norm_num)
theorem B1992003 : Blo 1991435 1992003 := bstep (se 1 (by rfl) ⟨1494002, by rfl⟩ : syracuseStep 1992003 = 2988005) B2988005
theorem B4038373 : Blo 1991435 4038373 := bbase (se 4 (by rfl) ⟨378597, by rfl⟩ : syracuseStep 4038373 = 757195) (by norm_num)
theorem B5384497 : Blo 1991435 5384497 := bstep (se 2 (by rfl) ⟨2019186, by rfl⟩ : syracuseStep 5384497 = 4038373) B4038373
theorem B7179329 : Blo 1991435 7179329 := bstep (se 2 (by rfl) ⟨2692248, by rfl⟩ : syracuseStep 7179329 = 5384497) B5384497
theorem B4786219 : Blo 1991435 4786219 := bstep (se 1 (by rfl) ⟨3589664, by rfl⟩ : syracuseStep 4786219 = 7179329) B7179329
theorem B6381625 : Blo 1991435 6381625 := bstep (se 2 (by rfl) ⟨2393109, by rfl⟩ : syracuseStep 6381625 = 4786219) B4786219
theorem B8508833 : Blo 1991435 8508833 := bstep (se 2 (by rfl) ⟨3190812, by rfl⟩ : syracuseStep 8508833 = 6381625) B6381625
theorem B5672555 : Blo 1991435 5672555 := bstep (se 1 (by rfl) ⟨4254416, by rfl⟩ : syracuseStep 5672555 = 8508833) B8508833
theorem B3781703 : Blo 1991435 3781703 := bstep (se 1 (by rfl) ⟨2836277, by rfl⟩ : syracuseStep 3781703 = 5672555) B5672555
theorem B2521135 : Blo 1991435 2521135 := bstep (se 1 (by rfl) ⟨1890851, by rfl⟩ : syracuseStep 2521135 = 3781703) B3781703
theorem B3361513 : Blo 1991435 3361513 := bstep (se 2 (by rfl) ⟨1260567, by rfl⟩ : syracuseStep 3361513 = 2521135) B2521135
theorem B4482017 : Blo 1991435 4482017 := bstep (se 2 (by rfl) ⟨1680756, by rfl⟩ : syracuseStep 4482017 = 3361513) B3361513
theorem B2988011 : Blo 1991435 2988011 := bstep (se 1 (by rfl) ⟨2241008, by rfl⟩ : syracuseStep 2988011 = 4482017) B4482017
theorem B1992007 : Blo 1991435 1992007 := bstep (se 1 (by rfl) ⟨1494005, by rfl⟩ : syracuseStep 1992007 = 2988011) B2988011
theorem B2241013 : Blo 1991435 2241013 := bbase (se 5 (by rfl) ⟨105047, by rfl⟩ : syracuseStep 2241013 = 210095) (by norm_num)
theorem B2988017 : Blo 1991435 2988017 := bstep (se 2 (by rfl) ⟨1120506, by rfl⟩ : syracuseStep 2988017 = 2241013) B2241013
theorem B1992011 : Blo 1991435 1992011 := bstep (se 1 (by rfl) ⟨1494008, by rfl⟩ : syracuseStep 1992011 = 2988017) B2988017
theorem B2521145 : Blo 1991435 2521145 := bbase (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) (by norm_num)
theorem B6723053 : Blo 1991435 6723053 := bstep (se 3 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 6723053 = 2521145) B2521145
theorem B4482035 : Blo 1991435 4482035 := bstep (se 1 (by rfl) ⟨3361526, by rfl⟩ : syracuseStep 4482035 = 6723053) B6723053
theorem B2988023 : Blo 1991435 2988023 := bstep (se 1 (by rfl) ⟨2241017, by rfl⟩ : syracuseStep 2988023 = 4482035) B4482035
theorem B1992015 : Blo 1991435 1992015 := bstep (se 1 (by rfl) ⟨1494011, by rfl⟩ : syracuseStep 1992015 = 2988023) B2988023
theorem B2988029 : Blo 1991435 2988029 := bbase (se 3 (by rfl) ⟨560255, by rfl⟩ : syracuseStep 2988029 = 1120511) (by norm_num)
theorem B1992019 : Blo 1991435 1992019 := bstep (se 1 (by rfl) ⟨1494014, by rfl⟩ : syracuseStep 1992019 = 2988029) B2988029
theorem B4482053 : Blo 1991435 4482053 := bbase (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) (by norm_num)
theorem B2988035 : Blo 1991435 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B1992023 : Blo 1991435 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B3781741 : Blo 1991435 3781741 := bbase (se 3 (by rfl) ⟨709076, by rfl⟩ : syracuseStep 3781741 = 1418153) (by norm_num)
theorem B5042321 : Blo 1991435 5042321 := bstep (se 2 (by rfl) ⟨1890870, by rfl⟩ : syracuseStep 5042321 = 3781741) B3781741
theorem B3361547 : Blo 1991435 3361547 := bstep (se 1 (by rfl) ⟨2521160, by rfl⟩ : syracuseStep 3361547 = 5042321) B5042321
theorem B2241031 : Blo 1991435 2241031 := bstep (se 1 (by rfl) ⟨1680773, by rfl⟩ : syracuseStep 2241031 = 3361547) B3361547
theorem B2988041 : Blo 1991435 2988041 := bstep (se 2 (by rfl) ⟨1120515, by rfl⟩ : syracuseStep 2988041 = 2241031) B2241031
theorem B1992027 : Blo 1991435 1992027 := bstep (se 1 (by rfl) ⟨1494020, by rfl⟩ : syracuseStep 1992027 = 2988041) B2988041
theorem B10084661 : Blo 1991435 10084661 := bbase (se 5 (by rfl) ⟨472718, by rfl⟩ : syracuseStep 10084661 = 945437) (by norm_num)
theorem B6723107 : Blo 1991435 6723107 := bstep (se 1 (by rfl) ⟨5042330, by rfl⟩ : syracuseStep 6723107 = 10084661) B10084661
theorem B4482071 : Blo 1991435 4482071 := bstep (se 1 (by rfl) ⟨3361553, by rfl⟩ : syracuseStep 4482071 = 6723107) B6723107
theorem B2988047 : Blo 1991435 2988047 := bstep (se 1 (by rfl) ⟨2241035, by rfl⟩ : syracuseStep 2988047 = 4482071) B4482071
theorem B1992031 : Blo 1991435 1992031 := bstep (se 1 (by rfl) ⟨1494023, by rfl⟩ : syracuseStep 1992031 = 2988047) B2988047
theorem B2988053 : Blo 1991435 2988053 := bbase (se 6 (by rfl) ⟨70032, by rfl⟩ : syracuseStep 2988053 = 140065) (by norm_num)
theorem B1992035 : Blo 1991435 1992035 := bstep (se 1 (by rfl) ⟨1494026, by rfl⟩ : syracuseStep 1992035 = 2988053) B2988053
theorem B4038437 : Blo 1991435 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B10769165 : Blo 1991435 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B7179443 : Blo 1991435 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B4786295 : Blo 1991435 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B12763453 : Blo 1991435 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B17017937 : Blo 1991435 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B11345291 : Blo 1991435 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B7563527 : Blo 1991435 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B5042351 : Blo 1991435 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B3361567 : Blo 1991435 3361567 := bstep (se 1 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 3361567 = 5042351) B5042351
theorem B4482089 : Blo 1991435 4482089 := bstep (se 2 (by rfl) ⟨1680783, by rfl⟩ : syracuseStep 4482089 = 3361567) B3361567
theorem B2988059 : Blo 1991435 2988059 := bstep (se 1 (by rfl) ⟨2241044, by rfl⟩ : syracuseStep 2988059 = 4482089) B4482089
theorem B1992039 : Blo 1991435 1992039 := bstep (se 1 (by rfl) ⟨1494029, by rfl⟩ : syracuseStep 1992039 = 2988059) B2988059
theorem B2241049 : Blo 1991435 2241049 := bbase (se 2 (by rfl) ⟨840393, by rfl⟩ : syracuseStep 2241049 = 1680787) (by norm_num)
theorem B2988065 : Blo 1991435 2988065 := bstep (se 2 (by rfl) ⟨1120524, by rfl⟩ : syracuseStep 2988065 = 2241049) B2241049
theorem B1992043 : Blo 1991435 1992043 := bstep (se 1 (by rfl) ⟨1494032, by rfl⟩ : syracuseStep 1992043 = 2988065) B2988065
theorem B7563557 : Blo 1991435 7563557 := bbase (se 4 (by rfl) ⟨709083, by rfl⟩ : syracuseStep 7563557 = 1418167) (by norm_num)
theorem B5042371 : Blo 1991435 5042371 := bstep (se 1 (by rfl) ⟨3781778, by rfl⟩ : syracuseStep 5042371 = 7563557) B7563557
theorem B6723161 : Blo 1991435 6723161 := bstep (se 2 (by rfl) ⟨2521185, by rfl⟩ : syracuseStep 6723161 = 5042371) B5042371
theorem B4482107 : Blo 1991435 4482107 := bstep (se 1 (by rfl) ⟨3361580, by rfl⟩ : syracuseStep 4482107 = 6723161) B6723161
theorem B2988071 : Blo 1991435 2988071 := bstep (se 1 (by rfl) ⟨2241053, by rfl⟩ : syracuseStep 2988071 = 4482107) B4482107
theorem B1992047 : Blo 1991435 1992047 := bstep (se 1 (by rfl) ⟨1494035, by rfl⟩ : syracuseStep 1992047 = 2988071) B2988071
theorem B2988077 : Blo 1991435 2988077 := bbase (se 3 (by rfl) ⟨560264, by rfl⟩ : syracuseStep 2988077 = 1120529) (by norm_num)
theorem B1992051 : Blo 1991435 1992051 := bstep (se 1 (by rfl) ⟨1494038, by rfl⟩ : syracuseStep 1992051 = 2988077) B2988077
theorem B4482125 : Blo 1991435 4482125 := bbase (se 3 (by rfl) ⟨840398, by rfl⟩ : syracuseStep 4482125 = 1680797) (by norm_num)
theorem B2988083 : Blo 1991435 2988083 := bstep (se 1 (by rfl) ⟨2241062, by rfl⟩ : syracuseStep 2988083 = 4482125) B4482125
theorem B1992055 : Blo 1991435 1992055 := bstep (se 1 (by rfl) ⟨1494041, by rfl⟩ : syracuseStep 1992055 = 2988083) B2988083
theorem B2521201 : Blo 1991435 2521201 := bbase (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) (by norm_num)
theorem B3361601 : Blo 1991435 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B2241067 : Blo 1991435 2241067 := bstep (se 1 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 2241067 = 3361601) B3361601
theorem B2988089 : Blo 1991435 2988089 := bstep (se 2 (by rfl) ⟨1120533, by rfl⟩ : syracuseStep 2988089 = 2241067) B2241067
theorem B1992059 : Blo 1991435 1992059 := bstep (se 1 (by rfl) ⟨1494044, by rfl⟩ : syracuseStep 1992059 = 2988089) B2988089
theorem B2046793 : Blo 1991435 2046793 := bbase (se 2 (by rfl) ⟨767547, by rfl⟩ : syracuseStep 2046793 = 1535095) (by norm_num)
theorem B2729057 : Blo 1991435 2729057 := bstep (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) B2046793
theorem B29109941 : Blo 1991435 29109941 := bstep (se 5 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 29109941 = 2729057) B2729057
theorem B19406627 : Blo 1991435 19406627 := bstep (se 1 (by rfl) ⟨14554970, by rfl⟩ : syracuseStep 19406627 = 29109941) B29109941
theorem B12937751 : Blo 1991435 12937751 := bstep (se 1 (by rfl) ⟨9703313, by rfl⟩ : syracuseStep 12937751 = 19406627) B19406627
theorem B8625167 : Blo 1991435 8625167 := bstep (se 1 (by rfl) ⟨6468875, by rfl⟩ : syracuseStep 8625167 = 12937751) B12937751
theorem B5750111 : Blo 1991435 5750111 := bstep (se 1 (by rfl) ⟨4312583, by rfl⟩ : syracuseStep 5750111 = 8625167) B8625167
theorem B3833407 : Blo 1991435 3833407 := bstep (se 1 (by rfl) ⟨2875055, by rfl⟩ : syracuseStep 3833407 = 5750111) B5750111
theorem B5111209 : Blo 1991435 5111209 := bstep (se 2 (by rfl) ⟨1916703, by rfl⟩ : syracuseStep 5111209 = 3833407) B3833407
theorem B6814945 : Blo 1991435 6814945 := bstep (se 2 (by rfl) ⟨2555604, by rfl⟩ : syracuseStep 6814945 = 5111209) B5111209
theorem B9086593 : Blo 1991435 9086593 := bstep (se 2 (by rfl) ⟨3407472, by rfl⟩ : syracuseStep 9086593 = 6814945) B6814945
theorem B12115457 : Blo 1991435 12115457 := bstep (se 2 (by rfl) ⟨4543296, by rfl⟩ : syracuseStep 12115457 = 9086593) B9086593
theorem B8076971 : Blo 1991435 8076971 := bstep (se 1 (by rfl) ⟨6057728, by rfl⟩ : syracuseStep 8076971 = 12115457) B12115457
theorem B5384647 : Blo 1991435 5384647 := bstep (se 1 (by rfl) ⟨4038485, by rfl⟩ : syracuseStep 5384647 = 8076971) B8076971
theorem B7179529 : Blo 1991435 7179529 := bstep (se 2 (by rfl) ⟨2692323, by rfl⟩ : syracuseStep 7179529 = 5384647) B5384647
theorem B9572705 : Blo 1991435 9572705 := bstep (se 2 (by rfl) ⟨3589764, by rfl⟩ : syracuseStep 9572705 = 7179529) B7179529
theorem B6381803 : Blo 1991435 6381803 := bstep (se 1 (by rfl) ⟨4786352, by rfl⟩ : syracuseStep 6381803 = 9572705) B9572705
theorem B4254535 : Blo 1991435 4254535 := bstep (se 1 (by rfl) ⟨3190901, by rfl⟩ : syracuseStep 4254535 = 6381803) B6381803
theorem B22690853 : Blo 1991435 22690853 := bstep (se 4 (by rfl) ⟨2127267, by rfl⟩ : syracuseStep 22690853 = 4254535) B4254535
theorem B15127235 : Blo 1991435 15127235 := bstep (se 1 (by rfl) ⟨11345426, by rfl⟩ : syracuseStep 15127235 = 22690853) B22690853
theorem B10084823 : Blo 1991435 10084823 := bstep (se 1 (by rfl) ⟨7563617, by rfl⟩ : syracuseStep 10084823 = 15127235) B15127235
theorem B6723215 : Blo 1991435 6723215 := bstep (se 1 (by rfl) ⟨5042411, by rfl⟩ : syracuseStep 6723215 = 10084823) B10084823
theorem B4482143 : Blo 1991435 4482143 := bstep (se 1 (by rfl) ⟨3361607, by rfl⟩ : syracuseStep 4482143 = 6723215) B6723215
theorem B2988095 : Blo 1991435 2988095 := bstep (se 1 (by rfl) ⟨2241071, by rfl⟩ : syracuseStep 2988095 = 4482143) B4482143
theorem B1992063 : Blo 1991435 1992063 := bstep (se 1 (by rfl) ⟨1494047, by rfl⟩ : syracuseStep 1992063 = 2988095) B2988095
theorem B2988101 : Blo 1991435 2988101 := bbase (se 4 (by rfl) ⟨280134, by rfl⟩ : syracuseStep 2988101 = 560269) (by norm_num)
theorem B1992067 : Blo 1991435 1992067 := bstep (se 1 (by rfl) ⟨1494050, by rfl⟩ : syracuseStep 1992067 = 2988101) B2988101
theorem B3361621 : Blo 1991435 3361621 := bbase (se 9 (by rfl) ⟨9848, by rfl⟩ : syracuseStep 3361621 = 19697) (by norm_num)
theorem B4482161 : Blo 1991435 4482161 := bstep (se 2 (by rfl) ⟨1680810, by rfl⟩ : syracuseStep 4482161 = 3361621) B3361621
theorem B2988107 : Blo 1991435 2988107 := bstep (se 1 (by rfl) ⟨2241080, by rfl⟩ : syracuseStep 2988107 = 4482161) B4482161
theorem B1992071 : Blo 1991435 1992071 := bstep (se 1 (by rfl) ⟨1494053, by rfl⟩ : syracuseStep 1992071 = 2988107) B2988107
theorem B2241085 : Blo 1991435 2241085 := bbase (se 3 (by rfl) ⟨420203, by rfl⟩ : syracuseStep 2241085 = 840407) (by norm_num)
theorem B2988113 : Blo 1991435 2988113 := bstep (se 2 (by rfl) ⟨1120542, by rfl⟩ : syracuseStep 2988113 = 2241085) B2241085
theorem B1992075 : Blo 1991435 1992075 := bstep (se 1 (by rfl) ⟨1494056, by rfl⟩ : syracuseStep 1992075 = 2988113) B2988113
theorem B6723269 : Blo 1991435 6723269 := bbase (se 4 (by rfl) ⟨630306, by rfl⟩ : syracuseStep 6723269 = 1260613) (by norm_num)
theorem B4482179 : Blo 1991435 4482179 := bstep (se 1 (by rfl) ⟨3361634, by rfl⟩ : syracuseStep 4482179 = 6723269) B6723269
theorem B2988119 : Blo 1991435 2988119 := bstep (se 1 (by rfl) ⟨2241089, by rfl⟩ : syracuseStep 2988119 = 4482179) B4482179
theorem B1992079 : Blo 1991435 1992079 := bstep (se 1 (by rfl) ⟨1494059, by rfl⟩ : syracuseStep 1992079 = 2988119) B2988119
theorem B2988125 : Blo 1991435 2988125 := bbase (se 3 (by rfl) ⟨560273, by rfl⟩ : syracuseStep 2988125 = 1120547) (by norm_num)
theorem B1992083 : Blo 1991435 1992083 := bstep (se 1 (by rfl) ⟨1494062, by rfl⟩ : syracuseStep 1992083 = 2988125) B2988125
theorem B4482197 : Blo 1991435 4482197 := bbase (se 6 (by rfl) ⟨105051, by rfl⟩ : syracuseStep 4482197 = 210103) (by norm_num)
theorem B2988131 : Blo 1991435 2988131 := bstep (se 1 (by rfl) ⟨2241098, by rfl⟩ : syracuseStep 2988131 = 4482197) B4482197
theorem B1992087 : Blo 1991435 1992087 := bstep (se 1 (by rfl) ⟨1494065, by rfl⟩ : syracuseStep 1992087 = 2988131) B2988131
theorem B2836397 : Blo 1991435 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B7563725 : Blo 1991435 7563725 := bstep (se 3 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 7563725 = 2836397) B2836397
theorem B5042483 : Blo 1991435 5042483 := bstep (se 1 (by rfl) ⟨3781862, by rfl⟩ : syracuseStep 5042483 = 7563725) B7563725
theorem B3361655 : Blo 1991435 3361655 := bstep (se 1 (by rfl) ⟨2521241, by rfl⟩ : syracuseStep 3361655 = 5042483) B5042483
theorem B2241103 : Blo 1991435 2241103 := bstep (se 1 (by rfl) ⟨1680827, by rfl⟩ : syracuseStep 2241103 = 3361655) B3361655
theorem B2988137 : Blo 1991435 2988137 := bstep (se 2 (by rfl) ⟨1120551, by rfl⟩ : syracuseStep 2988137 = 2241103) B2241103
theorem B1992091 : Blo 1991435 1992091 := bstep (se 1 (by rfl) ⟨1494068, by rfl⟩ : syracuseStep 1992091 = 2988137) B2988137
theorem B19145717 : Blo 1991435 19145717 := bbase (se 5 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 19145717 = 1794911) (by norm_num)
theorem B12763811 : Blo 1991435 12763811 := bstep (se 1 (by rfl) ⟨9572858, by rfl⟩ : syracuseStep 12763811 = 19145717) B19145717
theorem B8509207 : Blo 1991435 8509207 := bstep (se 1 (by rfl) ⟨6381905, by rfl⟩ : syracuseStep 8509207 = 12763811) B12763811
theorem B11345609 : Blo 1991435 11345609 := bstep (se 2 (by rfl) ⟨4254603, by rfl⟩ : syracuseStep 11345609 = 8509207) B8509207
theorem B7563739 : Blo 1991435 7563739 := bstep (se 1 (by rfl) ⟨5672804, by rfl⟩ : syracuseStep 7563739 = 11345609) B11345609
theorem B10084985 : Blo 1991435 10084985 := bstep (se 2 (by rfl) ⟨3781869, by rfl⟩ : syracuseStep 10084985 = 7563739) B7563739
theorem B6723323 : Blo 1991435 6723323 := bstep (se 1 (by rfl) ⟨5042492, by rfl⟩ : syracuseStep 6723323 = 10084985) B10084985
theorem B4482215 : Blo 1991435 4482215 := bstep (se 1 (by rfl) ⟨3361661, by rfl⟩ : syracuseStep 4482215 = 6723323) B6723323
theorem B2988143 : Blo 1991435 2988143 := bstep (se 1 (by rfl) ⟨2241107, by rfl⟩ : syracuseStep 2988143 = 4482215) B4482215
theorem B1992095 : Blo 1991435 1992095 := bstep (se 1 (by rfl) ⟨1494071, by rfl⟩ : syracuseStep 1992095 = 2988143) B2988143
theorem B2988149 : Blo 1991435 2988149 := bbase (se 5 (by rfl) ⟨140069, by rfl⟩ : syracuseStep 2988149 = 280139) (by norm_num)
theorem B1992099 : Blo 1991435 1992099 := bstep (se 1 (by rfl) ⟨1494074, by rfl⟩ : syracuseStep 1992099 = 2988149) B2988149
theorem B3781885 : Blo 1991435 3781885 := bbase (se 3 (by rfl) ⟨709103, by rfl⟩ : syracuseStep 3781885 = 1418207) (by norm_num)
theorem B5042513 : Blo 1991435 5042513 := bstep (se 2 (by rfl) ⟨1890942, by rfl⟩ : syracuseStep 5042513 = 3781885) B3781885
theorem B3361675 : Blo 1991435 3361675 := bstep (se 1 (by rfl) ⟨2521256, by rfl⟩ : syracuseStep 3361675 = 5042513) B5042513
theorem B4482233 : Blo 1991435 4482233 := bstep (se 2 (by rfl) ⟨1680837, by rfl⟩ : syracuseStep 4482233 = 3361675) B3361675
theorem B2988155 : Blo 1991435 2988155 := bstep (se 1 (by rfl) ⟨2241116, by rfl⟩ : syracuseStep 2988155 = 4482233) B4482233
theorem B1992103 : Blo 1991435 1992103 := bstep (se 1 (by rfl) ⟨1494077, by rfl⟩ : syracuseStep 1992103 = 2988155) B2988155
theorem B2241121 : Blo 1991435 2241121 := bbase (se 2 (by rfl) ⟨840420, by rfl⟩ : syracuseStep 2241121 = 1680841) (by norm_num)
theorem B2988161 : Blo 1991435 2988161 := bstep (se 2 (by rfl) ⟨1120560, by rfl⟩ : syracuseStep 2988161 = 2241121) B2241121
theorem B1992107 : Blo 1991435 1992107 := bstep (se 1 (by rfl) ⟨1494080, by rfl⟩ : syracuseStep 1992107 = 2988161) B2988161
theorem B5042533 : Blo 1991435 5042533 := bbase (se 4 (by rfl) ⟨472737, by rfl⟩ : syracuseStep 5042533 = 945475) (by norm_num)
theorem B6723377 : Blo 1991435 6723377 := bstep (se 2 (by rfl) ⟨2521266, by rfl⟩ : syracuseStep 6723377 = 5042533) B5042533
theorem B4482251 : Blo 1991435 4482251 := bstep (se 1 (by rfl) ⟨3361688, by rfl⟩ : syracuseStep 4482251 = 6723377) B6723377
theorem B2988167 : Blo 1991435 2988167 := bstep (se 1 (by rfl) ⟨2241125, by rfl⟩ : syracuseStep 2988167 = 4482251) B4482251
theorem B1992111 : Blo 1991435 1992111 := bstep (se 1 (by rfl) ⟨1494083, by rfl⟩ : syracuseStep 1992111 = 2988167) B2988167
theorem B2988173 : Blo 1991435 2988173 := bbase (se 3 (by rfl) ⟨560282, by rfl⟩ : syracuseStep 2988173 = 1120565) (by norm_num)
theorem B1992115 : Blo 1991435 1992115 := bstep (se 1 (by rfl) ⟨1494086, by rfl⟩ : syracuseStep 1992115 = 2988173) B2988173
theorem B4482269 : Blo 1991435 4482269 := bbase (se 3 (by rfl) ⟨840425, by rfl⟩ : syracuseStep 4482269 = 1680851) (by norm_num)
theorem B2988179 : Blo 1991435 2988179 := bstep (se 1 (by rfl) ⟨2241134, by rfl⟩ : syracuseStep 2988179 = 4482269) B4482269
theorem B1992119 : Blo 1991435 1992119 := bstep (se 1 (by rfl) ⟨1494089, by rfl⟩ : syracuseStep 1992119 = 2988179) B2988179
theorem B3361709 : Blo 1991435 3361709 := bbase (se 3 (by rfl) ⟨630320, by rfl⟩ : syracuseStep 3361709 = 1260641) (by norm_num)
theorem B2241139 : Blo 1991435 2241139 := bstep (se 1 (by rfl) ⟨1680854, by rfl⟩ : syracuseStep 2241139 = 3361709) B3361709
theorem B2988185 : Blo 1991435 2988185 := bstep (se 2 (by rfl) ⟨1120569, by rfl⟩ : syracuseStep 2988185 = 2241139) B2241139
theorem B1992123 : Blo 1991435 1992123 := bstep (se 1 (by rfl) ⟨1494092, by rfl⟩ : syracuseStep 1992123 = 2988185) B2988185
theorem B3407581 : Blo 1991435 3407581 := bbase (se 3 (by rfl) ⟨638921, by rfl⟩ : syracuseStep 3407581 = 1277843) (by norm_num)
theorem B18173765 : Blo 1991435 18173765 := bstep (se 4 (by rfl) ⟨1703790, by rfl⟩ : syracuseStep 18173765 = 3407581) B3407581
theorem B48463373 : Blo 1991435 48463373 := bstep (se 3 (by rfl) ⟨9086882, by rfl⟩ : syracuseStep 48463373 = 18173765) B18173765
theorem B129235661 : Blo 1991435 129235661 := bstep (se 3 (by rfl) ⟨24231686, by rfl⟩ : syracuseStep 129235661 = 48463373) B48463373
theorem B86157107 : Blo 1991435 86157107 := bstep (se 1 (by rfl) ⟨64617830, by rfl⟩ : syracuseStep 86157107 = 129235661) B129235661
theorem B57438071 : Blo 1991435 57438071 := bstep (se 1 (by rfl) ⟨43078553, by rfl⟩ : syracuseStep 57438071 = 86157107) B86157107
theorem B38292047 : Blo 1991435 38292047 := bstep (se 1 (by rfl) ⟨28719035, by rfl⟩ : syracuseStep 38292047 = 57438071) B57438071
theorem B25528031 : Blo 1991435 25528031 := bstep (se 1 (by rfl) ⟨19146023, by rfl⟩ : syracuseStep 25528031 = 38292047) B38292047
theorem B17018687 : Blo 1991435 17018687 := bstep (se 1 (by rfl) ⟨12764015, by rfl⟩ : syracuseStep 17018687 = 25528031) B25528031
theorem B11345791 : Blo 1991435 11345791 := bstep (se 1 (by rfl) ⟨8509343, by rfl⟩ : syracuseStep 11345791 = 17018687) B17018687
theorem B15127721 : Blo 1991435 15127721 := bstep (se 2 (by rfl) ⟨5672895, by rfl⟩ : syracuseStep 15127721 = 11345791) B11345791
theorem B10085147 : Blo 1991435 10085147 := bstep (se 1 (by rfl) ⟨7563860, by rfl⟩ : syracuseStep 10085147 = 15127721) B15127721
theorem B6723431 : Blo 1991435 6723431 := bstep (se 1 (by rfl) ⟨5042573, by rfl⟩ : syracuseStep 6723431 = 10085147) B10085147
theorem B4482287 : Blo 1991435 4482287 := bstep (se 1 (by rfl) ⟨3361715, by rfl⟩ : syracuseStep 4482287 = 6723431) B6723431
theorem B2988191 : Blo 1991435 2988191 := bstep (se 1 (by rfl) ⟨2241143, by rfl⟩ : syracuseStep 2988191 = 4482287) B4482287
theorem B1992127 : Blo 1991435 1992127 := bstep (se 1 (by rfl) ⟨1494095, by rfl⟩ : syracuseStep 1992127 = 2988191) B2988191
theorem B2988197 : Blo 1991435 2988197 := bbase (se 4 (by rfl) ⟨280143, by rfl⟩ : syracuseStep 2988197 = 560287) (by norm_num)
theorem B1992131 : Blo 1991435 1992131 := bstep (se 1 (by rfl) ⟨1494098, by rfl⟩ : syracuseStep 1992131 = 2988197) B2988197
theorem B2521297 : Blo 1991435 2521297 := bbase (se 2 (by rfl) ⟨945486, by rfl⟩ : syracuseStep 2521297 = 1890973) (by norm_num)
theorem B3361729 : Blo 1991435 3361729 := bstep (se 2 (by rfl) ⟨1260648, by rfl⟩ : syracuseStep 3361729 = 2521297) B2521297
theorem B4482305 : Blo 1991435 4482305 := bstep (se 2 (by rfl) ⟨1680864, by rfl⟩ : syracuseStep 4482305 = 3361729) B3361729
theorem B2988203 : Blo 1991435 2988203 := bstep (se 1 (by rfl) ⟨2241152, by rfl⟩ : syracuseStep 2988203 = 4482305) B4482305
theorem B1992135 : Blo 1991435 1992135 := bstep (se 1 (by rfl) ⟨1494101, by rfl⟩ : syracuseStep 1992135 = 2988203) B2988203
theorem B2241157 : Blo 1991435 2241157 := bbase (se 4 (by rfl) ⟨210108, by rfl⟩ : syracuseStep 2241157 = 420217) (by norm_num)
theorem B2988209 : Blo 1991435 2988209 := bstep (se 2 (by rfl) ⟨1120578, by rfl⟩ : syracuseStep 2988209 = 2241157) B2241157
theorem B1992139 : Blo 1991435 1992139 := bstep (se 1 (by rfl) ⟨1494104, by rfl⟩ : syracuseStep 1992139 = 2988209) B2988209
theorem B2393273 : Blo 1991435 2393273 := bbase (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) (by norm_num)
theorem B6382061 : Blo 1991435 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B4254707 : Blo 1991435 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B2836471 : Blo 1991435 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B3781961 : Blo 1991435 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B2521307 : Blo 1991435 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B6723485 : Blo 1991435 6723485 := bstep (se 3 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 6723485 = 2521307) B2521307
theorem B4482323 : Blo 1991435 4482323 := bstep (se 1 (by rfl) ⟨3361742, by rfl⟩ : syracuseStep 4482323 = 6723485) B6723485
theorem B2988215 : Blo 1991435 2988215 := bstep (se 1 (by rfl) ⟨2241161, by rfl⟩ : syracuseStep 2988215 = 4482323) B4482323
theorem B1992143 : Blo 1991435 1992143 := bstep (se 1 (by rfl) ⟨1494107, by rfl⟩ : syracuseStep 1992143 = 2988215) B2988215
theorem B2988221 : Blo 1991435 2988221 := bbase (se 3 (by rfl) ⟨560291, by rfl⟩ : syracuseStep 2988221 = 1120583) (by norm_num)
theorem B1992147 : Blo 1991435 1992147 := bstep (se 1 (by rfl) ⟨1494110, by rfl⟩ : syracuseStep 1992147 = 2988221) B2988221
theorem B4482341 : Blo 1991435 4482341 := bbase (se 4 (by rfl) ⟨420219, by rfl⟩ : syracuseStep 4482341 = 840439) (by norm_num)
theorem B2988227 : Blo 1991435 2988227 := bstep (se 1 (by rfl) ⟨2241170, by rfl⟩ : syracuseStep 2988227 = 4482341) B4482341
theorem B1992151 : Blo 1991435 1992151 := bstep (se 1 (by rfl) ⟨1494113, by rfl⟩ : syracuseStep 1992151 = 2988227) B2988227
theorem B5042645 : Blo 1991435 5042645 := bbase (se 7 (by rfl) ⟨59093, by rfl⟩ : syracuseStep 5042645 = 118187) (by norm_num)
theorem B3361763 : Blo 1991435 3361763 := bstep (se 1 (by rfl) ⟨2521322, by rfl⟩ : syracuseStep 3361763 = 5042645) B5042645
theorem B2241175 : Blo 1991435 2241175 := bstep (se 1 (by rfl) ⟨1680881, by rfl⟩ : syracuseStep 2241175 = 3361763) B3361763
theorem B2988233 : Blo 1991435 2988233 := bstep (se 2 (by rfl) ⟨1120587, by rfl⟩ : syracuseStep 2988233 = 2241175) B2241175
theorem B1992155 : Blo 1991435 1992155 := bstep (se 1 (by rfl) ⟨1494116, by rfl⟩ : syracuseStep 1992155 = 2988233) B2988233
theorem B2590597 : Blo 1991435 2590597 := bbase (se 4 (by rfl) ⟨242868, by rfl⟩ : syracuseStep 2590597 = 485737) (by norm_num)
theorem B3454129 : Blo 1991435 3454129 := bstep (se 2 (by rfl) ⟨1295298, by rfl⟩ : syracuseStep 3454129 = 2590597) B2590597
theorem B4605505 : Blo 1991435 4605505 := bstep (se 2 (by rfl) ⟨1727064, by rfl⟩ : syracuseStep 4605505 = 3454129) B3454129
theorem B24562693 : Blo 1991435 24562693 := bstep (se 4 (by rfl) ⟨2302752, by rfl⟩ : syracuseStep 24562693 = 4605505) B4605505
theorem B32750257 : Blo 1991435 32750257 := bstep (se 2 (by rfl) ⟨12281346, by rfl⟩ : syracuseStep 32750257 = 24562693) B24562693
theorem B43667009 : Blo 1991435 43667009 := bstep (se 2 (by rfl) ⟨16375128, by rfl⟩ : syracuseStep 43667009 = 32750257) B32750257
theorem B29111339 : Blo 1991435 29111339 := bstep (se 1 (by rfl) ⟨21833504, by rfl⟩ : syracuseStep 29111339 = 43667009) B43667009
theorem B19407559 : Blo 1991435 19407559 := bstep (se 1 (by rfl) ⟨14555669, by rfl⟩ : syracuseStep 19407559 = 29111339) B29111339
theorem B25876745 : Blo 1991435 25876745 := bstep (se 2 (by rfl) ⟨9703779, by rfl⟩ : syracuseStep 25876745 = 19407559) B19407559
theorem B17251163 : Blo 1991435 17251163 := bstep (se 1 (by rfl) ⟨12938372, by rfl⟩ : syracuseStep 17251163 = 25876745) B25876745
theorem B11500775 : Blo 1991435 11500775 := bstep (se 1 (by rfl) ⟨8625581, by rfl⟩ : syracuseStep 11500775 = 17251163) B17251163
theorem B7667183 : Blo 1991435 7667183 := bstep (se 1 (by rfl) ⟨5750387, by rfl⟩ : syracuseStep 7667183 = 11500775) B11500775
theorem B5111455 : Blo 1991435 5111455 := bstep (se 1 (by rfl) ⟨3833591, by rfl⟩ : syracuseStep 5111455 = 7667183) B7667183
theorem B6815273 : Blo 1991435 6815273 := bstep (se 2 (by rfl) ⟨2555727, by rfl⟩ : syracuseStep 6815273 = 5111455) B5111455
theorem B18174061 : Blo 1991435 18174061 := bstep (se 3 (by rfl) ⟨3407636, by rfl⟩ : syracuseStep 18174061 = 6815273) B6815273
theorem B24232081 : Blo 1991435 24232081 := bstep (se 2 (by rfl) ⟨9087030, by rfl⟩ : syracuseStep 24232081 = 18174061) B18174061
theorem B32309441 : Blo 1991435 32309441 := bstep (se 2 (by rfl) ⟨12116040, by rfl⟩ : syracuseStep 32309441 = 24232081) B24232081
theorem B21539627 : Blo 1991435 21539627 := bstep (se 1 (by rfl) ⟨16154720, by rfl⟩ : syracuseStep 21539627 = 32309441) B32309441
theorem B14359751 : Blo 1991435 14359751 := bstep (se 1 (by rfl) ⟨10769813, by rfl⟩ : syracuseStep 14359751 = 21539627) B21539627
theorem B9573167 : Blo 1991435 9573167 := bstep (se 1 (by rfl) ⟨7179875, by rfl⟩ : syracuseStep 9573167 = 14359751) B14359751
theorem B6382111 : Blo 1991435 6382111 := bstep (se 1 (by rfl) ⟨4786583, by rfl⟩ : syracuseStep 6382111 = 9573167) B9573167
theorem B8509481 : Blo 1991435 8509481 := bstep (se 2 (by rfl) ⟨3191055, by rfl⟩ : syracuseStep 8509481 = 6382111) B6382111
theorem B5672987 : Blo 1991435 5672987 := bstep (se 1 (by rfl) ⟨4254740, by rfl⟩ : syracuseStep 5672987 = 8509481) B8509481
theorem B3781991 : Blo 1991435 3781991 := bstep (se 1 (by rfl) ⟨2836493, by rfl⟩ : syracuseStep 3781991 = 5672987) B5672987
theorem B10085309 : Blo 1991435 10085309 := bstep (se 3 (by rfl) ⟨1890995, by rfl⟩ : syracuseStep 10085309 = 3781991) B3781991
theorem B6723539 : Blo 1991435 6723539 := bstep (se 1 (by rfl) ⟨5042654, by rfl⟩ : syracuseStep 6723539 = 10085309) B10085309
theorem B4482359 : Blo 1991435 4482359 := bstep (se 1 (by rfl) ⟨3361769, by rfl⟩ : syracuseStep 4482359 = 6723539) B6723539
theorem B2988239 : Blo 1991435 2988239 := bstep (se 1 (by rfl) ⟨2241179, by rfl⟩ : syracuseStep 2988239 = 4482359) B4482359
theorem B1992159 : Blo 1991435 1992159 := bstep (se 1 (by rfl) ⟨1494119, by rfl⟩ : syracuseStep 1992159 = 2988239) B2988239
theorem B2988245 : Blo 1991435 2988245 := bbase (se 7 (by rfl) ⟨35018, by rfl⟩ : syracuseStep 2988245 = 70037) (by norm_num)
theorem B1992163 : Blo 1991435 1992163 := bstep (se 1 (by rfl) ⟨1494122, by rfl⟩ : syracuseStep 1992163 = 2988245) B2988245
theorem B3191069 : Blo 1991435 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B2127379 : Blo 1991435 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B2836505 : Blo 1991435 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B7564013 : Blo 1991435 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B5042675 : Blo 1991435 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B3361783 : Blo 1991435 3361783 := bstep (se 1 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 3361783 = 5042675) B5042675
theorem B4482377 : Blo 1991435 4482377 := bstep (se 2 (by rfl) ⟨1680891, by rfl⟩ : syracuseStep 4482377 = 3361783) B3361783
theorem B2988251 : Blo 1991435 2988251 := bstep (se 1 (by rfl) ⟨2241188, by rfl⟩ : syracuseStep 2988251 = 4482377) B4482377
theorem B1992167 : Blo 1991435 1992167 := bstep (se 1 (by rfl) ⟨1494125, by rfl⟩ : syracuseStep 1992167 = 2988251) B2988251
theorem B2241193 : Blo 1991435 2241193 := bbase (se 2 (by rfl) ⟨840447, by rfl⟩ : syracuseStep 2241193 = 1680895) (by norm_num)
theorem B2988257 : Blo 1991435 2988257 := bstep (se 2 (by rfl) ⟨1120596, by rfl⟩ : syracuseStep 2988257 = 2241193) B2241193
theorem B1992171 : Blo 1991435 1992171 := bstep (se 1 (by rfl) ⟨1494128, by rfl⟩ : syracuseStep 1992171 = 2988257) B2988257
theorem B2555749 : Blo 1991435 2555749 := bbase (se 4 (by rfl) ⟨239601, by rfl⟩ : syracuseStep 2555749 = 479203) (by norm_num)
theorem B3407665 : Blo 1991435 3407665 := bstep (se 2 (by rfl) ⟨1277874, by rfl⟩ : syracuseStep 3407665 = 2555749) B2555749
theorem B4543553 : Blo 1991435 4543553 := bstep (se 2 (by rfl) ⟨1703832, by rfl⟩ : syracuseStep 4543553 = 3407665) B3407665
theorem B12116141 : Blo 1991435 12116141 := bstep (se 3 (by rfl) ⟨2271776, by rfl⟩ : syracuseStep 12116141 = 4543553) B4543553
theorem B8077427 : Blo 1991435 8077427 := bstep (se 1 (by rfl) ⟨6058070, by rfl⟩ : syracuseStep 8077427 = 12116141) B12116141
theorem B5384951 : Blo 1991435 5384951 := bstep (se 1 (by rfl) ⟨4038713, by rfl⟩ : syracuseStep 5384951 = 8077427) B8077427
theorem B3589967 : Blo 1991435 3589967 := bstep (se 1 (by rfl) ⟨2692475, by rfl⟩ : syracuseStep 3589967 = 5384951) B5384951
theorem B2393311 : Blo 1991435 2393311 := bstep (se 1 (by rfl) ⟨1794983, by rfl⟩ : syracuseStep 2393311 = 3589967) B3589967
theorem B3191081 : Blo 1991435 3191081 := bstep (se 2 (by rfl) ⟨1196655, by rfl⟩ : syracuseStep 3191081 = 2393311) B2393311
theorem B8509549 : Blo 1991435 8509549 := bstep (se 3 (by rfl) ⟨1595540, by rfl⟩ : syracuseStep 8509549 = 3191081) B3191081
theorem B11346065 : Blo 1991435 11346065 := bstep (se 2 (by rfl) ⟨4254774, by rfl⟩ : syracuseStep 11346065 = 8509549) B8509549
theorem B7564043 : Blo 1991435 7564043 := bstep (se 1 (by rfl) ⟨5673032, by rfl⟩ : syracuseStep 7564043 = 11346065) B11346065
theorem B5042695 : Blo 1991435 5042695 := bstep (se 1 (by rfl) ⟨3782021, by rfl⟩ : syracuseStep 5042695 = 7564043) B7564043
theorem B6723593 : Blo 1991435 6723593 := bstep (se 2 (by rfl) ⟨2521347, by rfl⟩ : syracuseStep 6723593 = 5042695) B5042695
theorem B4482395 : Blo 1991435 4482395 := bstep (se 1 (by rfl) ⟨3361796, by rfl⟩ : syracuseStep 4482395 = 6723593) B6723593
theorem B2988263 : Blo 1991435 2988263 := bstep (se 1 (by rfl) ⟨2241197, by rfl⟩ : syracuseStep 2988263 = 4482395) B4482395
theorem B1992175 : Blo 1991435 1992175 := bstep (se 1 (by rfl) ⟨1494131, by rfl⟩ : syracuseStep 1992175 = 2988263) B2988263
theorem B2988269 : Blo 1991435 2988269 := bbase (se 3 (by rfl) ⟨560300, by rfl⟩ : syracuseStep 2988269 = 1120601) (by norm_num)
theorem B1992179 : Blo 1991435 1992179 := bstep (se 1 (by rfl) ⟨1494134, by rfl⟩ : syracuseStep 1992179 = 2988269) B2988269
theorem B4482413 : Blo 1991435 4482413 := bbase (se 3 (by rfl) ⟨840452, by rfl⟩ : syracuseStep 4482413 = 1680905) (by norm_num)
theorem B2988275 : Blo 1991435 2988275 := bstep (se 1 (by rfl) ⟨2241206, by rfl⟩ : syracuseStep 2988275 = 4482413) B4482413
theorem B1992183 : Blo 1991435 1992183 := bstep (se 1 (by rfl) ⟨1494137, by rfl⟩ : syracuseStep 1992183 = 2988275) B2988275
theorem B3782045 : Blo 1991435 3782045 := bbase (se 3 (by rfl) ⟨709133, by rfl⟩ : syracuseStep 3782045 = 1418267) (by norm_num)
theorem B2521363 : Blo 1991435 2521363 := bstep (se 1 (by rfl) ⟨1891022, by rfl⟩ : syracuseStep 2521363 = 3782045) B3782045
theorem B3361817 : Blo 1991435 3361817 := bstep (se 2 (by rfl) ⟨1260681, by rfl⟩ : syracuseStep 3361817 = 2521363) B2521363
theorem B2241211 : Blo 1991435 2241211 := bstep (se 1 (by rfl) ⟨1680908, by rfl⟩ : syracuseStep 2241211 = 3361817) B3361817
theorem B2988281 : Blo 1991435 2988281 := bstep (se 2 (by rfl) ⟨1120605, by rfl⟩ : syracuseStep 2988281 = 2241211) B2241211
theorem B1992187 : Blo 1991435 1992187 := bstep (se 1 (by rfl) ⟨1494140, by rfl⟩ : syracuseStep 1992187 = 2988281) B2988281
theorem B15543829 : Blo 1991435 15543829 := bbase (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) (by norm_num)
theorem B82900421 : Blo 1991435 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B55266947 : Blo 1991435 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B36844631 : Blo 1991435 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B24563087 : Blo 1991435 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B16375391 : Blo 1991435 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B10916927 : Blo 1991435 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B7277951 : Blo 1991435 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B4851967 : Blo 1991435 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B6469289 : Blo 1991435 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B4312859 : Blo 1991435 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B11500957 : Blo 1991435 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B15334609 : Blo 1991435 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B20446145 : Blo 1991435 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B13630763 : Blo 1991435 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B9087175 : Blo 1991435 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B12116233 : Blo 1991435 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B16154977 : Blo 1991435 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B21539969 : Blo 1991435 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B14359979 : Blo 1991435 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B9573319 : Blo 1991435 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B51057701 : Blo 1991435 51057701 := bstep (se 4 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 51057701 = 9573319) B9573319
theorem B34038467 : Blo 1991435 34038467 := bstep (se 1 (by rfl) ⟨25528850, by rfl⟩ : syracuseStep 34038467 = 51057701) B51057701
theorem B22692311 : Blo 1991435 22692311 := bstep (se 1 (by rfl) ⟨17019233, by rfl⟩ : syracuseStep 22692311 = 34038467) B34038467
theorem B15128207 : Blo 1991435 15128207 := bstep (se 1 (by rfl) ⟨11346155, by rfl⟩ : syracuseStep 15128207 = 22692311) B22692311
theorem B10085471 : Blo 1991435 10085471 := bstep (se 1 (by rfl) ⟨7564103, by rfl⟩ : syracuseStep 10085471 = 15128207) B15128207
theorem B6723647 : Blo 1991435 6723647 := bstep (se 1 (by rfl) ⟨5042735, by rfl⟩ : syracuseStep 6723647 = 10085471) B10085471
theorem B4482431 : Blo 1991435 4482431 := bstep (se 1 (by rfl) ⟨3361823, by rfl⟩ : syracuseStep 4482431 = 6723647) B6723647
theorem B2988287 : Blo 1991435 2988287 := bstep (se 1 (by rfl) ⟨2241215, by rfl⟩ : syracuseStep 2988287 = 4482431) B4482431
theorem B1992191 : Blo 1991435 1992191 := bstep (se 1 (by rfl) ⟨1494143, by rfl⟩ : syracuseStep 1992191 = 2988287) B2988287
theorem B2988293 : Blo 1991435 2988293 := bbase (se 4 (by rfl) ⟨280152, by rfl⟩ : syracuseStep 2988293 = 560305) (by norm_num)
theorem B1992195 : Blo 1991435 1992195 := bstep (se 1 (by rfl) ⟨1494146, by rfl⟩ : syracuseStep 1992195 = 2988293) B2988293
theorem B3361837 : Blo 1991435 3361837 := bbase (se 3 (by rfl) ⟨630344, by rfl⟩ : syracuseStep 3361837 = 1260689) (by norm_num)
theorem B4482449 : Blo 1991435 4482449 := bstep (se 2 (by rfl) ⟨1680918, by rfl⟩ : syracuseStep 4482449 = 3361837) B3361837
theorem B2988299 : Blo 1991435 2988299 := bstep (se 1 (by rfl) ⟨2241224, by rfl⟩ : syracuseStep 2988299 = 4482449) B4482449
theorem B1992199 : Blo 1991435 1992199 := bstep (se 1 (by rfl) ⟨1494149, by rfl⟩ : syracuseStep 1992199 = 2988299) B2988299
theorem B2241229 : Blo 1991435 2241229 := bbase (se 3 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 2241229 = 840461) (by norm_num)
theorem B2988305 : Blo 1991435 2988305 := bstep (se 2 (by rfl) ⟨1120614, by rfl⟩ : syracuseStep 2988305 = 2241229) B2241229
theorem B1992203 : Blo 1991435 1992203 := bstep (se 1 (by rfl) ⟨1494152, by rfl⟩ : syracuseStep 1992203 = 2988305) B2988305
theorem B6723701 : Blo 1991435 6723701 := bbase (se 5 (by rfl) ⟨315173, by rfl⟩ : syracuseStep 6723701 = 630347) (by norm_num)
theorem B4482467 : Blo 1991435 4482467 := bstep (se 1 (by rfl) ⟨3361850, by rfl⟩ : syracuseStep 4482467 = 6723701) B6723701
theorem B2988311 : Blo 1991435 2988311 := bstep (se 1 (by rfl) ⟨2241233, by rfl⟩ : syracuseStep 2988311 = 4482467) B4482467
theorem B1992207 : Blo 1991435 1992207 := bstep (se 1 (by rfl) ⟨1494155, by rfl⟩ : syracuseStep 1992207 = 2988311) B2988311
theorem B2988317 : Blo 1991435 2988317 := bbase (se 3 (by rfl) ⟨560309, by rfl⟩ : syracuseStep 2988317 = 1120619) (by norm_num)
theorem B1992211 : Blo 1991435 1992211 := bstep (se 1 (by rfl) ⟨1494158, by rfl⟩ : syracuseStep 1992211 = 2988317) B2988317
theorem B4482485 : Blo 1991435 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B2988323 : Blo 1991435 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B1992215 : Blo 1991435 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B4254869 : Blo 1991435 4254869 := bbase (se 6 (by rfl) ⟨99723, by rfl⟩ : syracuseStep 4254869 = 199447) (by norm_num)
theorem B11346317 : Blo 1991435 11346317 := bstep (se 3 (by rfl) ⟨2127434, by rfl⟩ : syracuseStep 11346317 = 4254869) B4254869
theorem B7564211 : Blo 1991435 7564211 := bstep (se 1 (by rfl) ⟨5673158, by rfl⟩ : syracuseStep 7564211 = 11346317) B11346317
theorem B5042807 : Blo 1991435 5042807 := bstep (se 1 (by rfl) ⟨3782105, by rfl⟩ : syracuseStep 5042807 = 7564211) B7564211
theorem B3361871 : Blo 1991435 3361871 := bstep (se 1 (by rfl) ⟨2521403, by rfl⟩ : syracuseStep 3361871 = 5042807) B5042807
theorem B2241247 : Blo 1991435 2241247 := bstep (se 1 (by rfl) ⟨1680935, by rfl⟩ : syracuseStep 2241247 = 3361871) B3361871
theorem B2988329 : Blo 1991435 2988329 := bstep (se 2 (by rfl) ⟨1120623, by rfl⟩ : syracuseStep 2988329 = 2241247) B2241247
theorem B1992219 : Blo 1991435 1992219 := bstep (se 1 (by rfl) ⟨1494164, by rfl⟩ : syracuseStep 1992219 = 2988329) B2988329
theorem B4254877 : Blo 1991435 4254877 := bbase (se 3 (by rfl) ⟨797789, by rfl⟩ : syracuseStep 4254877 = 1595579) (by norm_num)
theorem B5673169 : Blo 1991435 5673169 := bstep (se 2 (by rfl) ⟨2127438, by rfl⟩ : syracuseStep 5673169 = 4254877) B4254877
theorem B7564225 : Blo 1991435 7564225 := bstep (se 2 (by rfl) ⟨2836584, by rfl⟩ : syracuseStep 7564225 = 5673169) B5673169
theorem B10085633 : Blo 1991435 10085633 := bstep (se 2 (by rfl) ⟨3782112, by rfl⟩ : syracuseStep 10085633 = 7564225) B7564225
theorem B6723755 : Blo 1991435 6723755 := bstep (se 1 (by rfl) ⟨5042816, by rfl⟩ : syracuseStep 6723755 = 10085633) B10085633
theorem B4482503 : Blo 1991435 4482503 := bstep (se 1 (by rfl) ⟨3361877, by rfl⟩ : syracuseStep 4482503 = 6723755) B6723755
theorem B2988335 : Blo 1991435 2988335 := bstep (se 1 (by rfl) ⟨2241251, by rfl⟩ : syracuseStep 2988335 = 4482503) B4482503
theorem B1992223 : Blo 1991435 1992223 := bstep (se 1 (by rfl) ⟨1494167, by rfl⟩ : syracuseStep 1992223 = 2988335) B2988335
theorem B2988341 : Blo 1991435 2988341 := bbase (se 5 (by rfl) ⟨140078, by rfl⟩ : syracuseStep 2988341 = 280157) (by norm_num)
theorem B1992227 : Blo 1991435 1992227 := bstep (se 1 (by rfl) ⟨1494170, by rfl⟩ : syracuseStep 1992227 = 2988341) B2988341
theorem B5042837 : Blo 1991435 5042837 := bbase (se 6 (by rfl) ⟨118191, by rfl⟩ : syracuseStep 5042837 = 236383) (by norm_num)
theorem B3361891 : Blo 1991435 3361891 := bstep (se 1 (by rfl) ⟨2521418, by rfl⟩ : syracuseStep 3361891 = 5042837) B5042837
theorem B4482521 : Blo 1991435 4482521 := bstep (se 2 (by rfl) ⟨1680945, by rfl⟩ : syracuseStep 4482521 = 3361891) B3361891
theorem B2988347 : Blo 1991435 2988347 := bstep (se 1 (by rfl) ⟨2241260, by rfl⟩ : syracuseStep 2988347 = 4482521) B4482521
theorem B1992231 : Blo 1991435 1992231 := bstep (se 1 (by rfl) ⟨1494173, by rfl⟩ : syracuseStep 1992231 = 2988347) B2988347
theorem B2241265 : Blo 1991435 2241265 := bbase (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) (by norm_num)
theorem B2988353 : Blo 1991435 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B1992235 : Blo 1991435 1992235 := bstep (se 1 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 1992235 = 2988353) B2988353
theorem B13631093 : Blo 1991435 13631093 := bbase (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) (by norm_num)
theorem B9087395 : Blo 1991435 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B96932213 : Blo 1991435 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B64621475 : Blo 1991435 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B43080983 : Blo 1991435 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B28720655 : Blo 1991435 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B19147103 : Blo 1991435 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B12764735 : Blo 1991435 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B8509823 : Blo 1991435 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B5673215 : Blo 1991435 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B3782143 : Blo 1991435 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B5042857 : Blo 1991435 5042857 := bstep (se 2 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 5042857 = 3782143) B3782143
theorem B6723809 : Blo 1991435 6723809 := bstep (se 2 (by rfl) ⟨2521428, by rfl⟩ : syracuseStep 6723809 = 5042857) B5042857
theorem B4482539 : Blo 1991435 4482539 := bstep (se 1 (by rfl) ⟨3361904, by rfl⟩ : syracuseStep 4482539 = 6723809) B6723809
theorem B2988359 : Blo 1991435 2988359 := bstep (se 1 (by rfl) ⟨2241269, by rfl⟩ : syracuseStep 2988359 = 4482539) B4482539
theorem B1992239 : Blo 1991435 1992239 := bstep (se 1 (by rfl) ⟨1494179, by rfl⟩ : syracuseStep 1992239 = 2988359) B2988359
theorem B2988365 : Blo 1991435 2988365 := bbase (se 3 (by rfl) ⟨560318, by rfl⟩ : syracuseStep 2988365 = 1120637) (by norm_num)
theorem B1992243 : Blo 1991435 1992243 := bstep (se 1 (by rfl) ⟨1494182, by rfl⟩ : syracuseStep 1992243 = 2988365) B2988365
theorem B4482557 : Blo 1991435 4482557 := bbase (se 3 (by rfl) ⟨840479, by rfl⟩ : syracuseStep 4482557 = 1680959) (by norm_num)
theorem B2988371 : Blo 1991435 2988371 := bstep (se 1 (by rfl) ⟨2241278, by rfl⟩ : syracuseStep 2988371 = 4482557) B4482557
theorem B1992247 : Blo 1991435 1992247 := bstep (se 1 (by rfl) ⟨1494185, by rfl⟩ : syracuseStep 1992247 = 2988371) B2988371
theorem B3361925 : Blo 1991435 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B2241283 : Blo 1991435 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B2988377 : Blo 1991435 2988377 := bstep (se 2 (by rfl) ⟨1120641, by rfl⟩ : syracuseStep 2988377 = 2241283) B2241283
theorem B1992251 : Blo 1991435 1992251 := bstep (se 1 (by rfl) ⟨1494188, by rfl⟩ : syracuseStep 1992251 = 2988377) B2988377
theorem B15128693 : Blo 1991435 15128693 := bbase (se 5 (by rfl) ⟨709157, by rfl⟩ : syracuseStep 15128693 = 1418315) (by norm_num)
theorem B10085795 : Blo 1991435 10085795 := bstep (se 1 (by rfl) ⟨7564346, by rfl⟩ : syracuseStep 10085795 = 15128693) B15128693
theorem B6723863 : Blo 1991435 6723863 := bstep (se 1 (by rfl) ⟨5042897, by rfl⟩ : syracuseStep 6723863 = 10085795) B10085795
theorem B4482575 : Blo 1991435 4482575 := bstep (se 1 (by rfl) ⟨3361931, by rfl⟩ : syracuseStep 4482575 = 6723863) B6723863
theorem B2988383 : Blo 1991435 2988383 := bstep (se 1 (by rfl) ⟨2241287, by rfl⟩ : syracuseStep 2988383 = 4482575) B4482575
theorem B1992255 : Blo 1991435 1992255 := bstep (se 1 (by rfl) ⟨1494191, by rfl⟩ : syracuseStep 1992255 = 2988383) B2988383
theorem B2988389 : Blo 1991435 2988389 := bbase (se 4 (by rfl) ⟨280161, by rfl⟩ : syracuseStep 2988389 = 560323) (by norm_num)
theorem B1992259 : Blo 1991435 1992259 := bstep (se 1 (by rfl) ⟨1494194, by rfl⟩ : syracuseStep 1992259 = 2988389) B2988389
theorem B3782189 : Blo 1991435 3782189 := bbase (se 3 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 3782189 = 1418321) (by norm_num)
theorem B2521459 : Blo 1991435 2521459 := bstep (se 1 (by rfl) ⟨1891094, by rfl⟩ : syracuseStep 2521459 = 3782189) B3782189
theorem B3361945 : Blo 1991435 3361945 := bstep (se 2 (by rfl) ⟨1260729, by rfl⟩ : syracuseStep 3361945 = 2521459) B2521459
theorem B4482593 : Blo 1991435 4482593 := bstep (se 2 (by rfl) ⟨1680972, by rfl⟩ : syracuseStep 4482593 = 3361945) B3361945
theorem B2988395 : Blo 1991435 2988395 := bstep (se 1 (by rfl) ⟨2241296, by rfl⟩ : syracuseStep 2988395 = 4482593) B4482593
theorem B1992263 : Blo 1991435 1992263 := bstep (se 1 (by rfl) ⟨1494197, by rfl⟩ : syracuseStep 1992263 = 2988395) B2988395
theorem B2241301 : Blo 1991435 2241301 := bbase (se 6 (by rfl) ⟨52530, by rfl⟩ : syracuseStep 2241301 = 105061) (by norm_num)
theorem B2988401 : Blo 1991435 2988401 := bstep (se 2 (by rfl) ⟨1120650, by rfl⟩ : syracuseStep 2988401 = 2241301) B2241301
theorem B1992267 : Blo 1991435 1992267 := bstep (se 1 (by rfl) ⟨1494200, by rfl⟩ : syracuseStep 1992267 = 2988401) B2988401
theorem B2521469 : Blo 1991435 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B6723917 : Blo 1991435 6723917 := bstep (se 3 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 6723917 = 2521469) B2521469
theorem B4482611 : Blo 1991435 4482611 := bstep (se 1 (by rfl) ⟨3361958, by rfl⟩ : syracuseStep 4482611 = 6723917) B6723917
theorem B2988407 : Blo 1991435 2988407 := bstep (se 1 (by rfl) ⟨2241305, by rfl⟩ : syracuseStep 2988407 = 4482611) B4482611
theorem B1992271 : Blo 1991435 1992271 := bstep (se 1 (by rfl) ⟨1494203, by rfl⟩ : syracuseStep 1992271 = 2988407) B2988407
theorem B2988413 : Blo 1991435 2988413 := bbase (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) (by norm_num)
theorem B1992275 : Blo 1991435 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B4482629 : Blo 1991435 4482629 := bbase (se 4 (by rfl) ⟨420246, by rfl⟩ : syracuseStep 4482629 = 840493) (by norm_num)
theorem B2988419 : Blo 1991435 2988419 := bstep (se 1 (by rfl) ⟨2241314, by rfl⟩ : syracuseStep 2988419 = 4482629) B4482629
theorem B1992279 : Blo 1991435 1992279 := bstep (se 1 (by rfl) ⟨1494209, by rfl⟩ : syracuseStep 1992279 = 2988419) B2988419
theorem B7180325 : Blo 1991435 7180325 := bbase (se 4 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 7180325 = 1346311) (by norm_num)
theorem B4786883 : Blo 1991435 4786883 := bstep (se 1 (by rfl) ⟨3590162, by rfl⟩ : syracuseStep 4786883 = 7180325) B7180325
theorem B3191255 : Blo 1991435 3191255 := bstep (se 1 (by rfl) ⟨2393441, by rfl⟩ : syracuseStep 3191255 = 4786883) B4786883
theorem B2127503 : Blo 1991435 2127503 := bstep (se 1 (by rfl) ⟨1595627, by rfl⟩ : syracuseStep 2127503 = 3191255) B3191255
theorem B5673341 : Blo 1991435 5673341 := bstep (se 3 (by rfl) ⟨1063751, by rfl⟩ : syracuseStep 5673341 = 2127503) B2127503
theorem B3782227 : Blo 1991435 3782227 := bstep (se 1 (by rfl) ⟨2836670, by rfl⟩ : syracuseStep 3782227 = 5673341) B5673341
theorem B5042969 : Blo 1991435 5042969 := bstep (se 2 (by rfl) ⟨1891113, by rfl⟩ : syracuseStep 5042969 = 3782227) B3782227
theorem B3361979 : Blo 1991435 3361979 := bstep (se 1 (by rfl) ⟨2521484, by rfl⟩ : syracuseStep 3361979 = 5042969) B5042969
theorem B2241319 : Blo 1991435 2241319 := bstep (se 1 (by rfl) ⟨1680989, by rfl⟩ : syracuseStep 2241319 = 3361979) B3361979
theorem B2988425 : Blo 1991435 2988425 := bstep (se 2 (by rfl) ⟨1120659, by rfl⟩ : syracuseStep 2988425 = 2241319) B2241319
theorem B1992283 : Blo 1991435 1992283 := bstep (se 1 (by rfl) ⟨1494212, by rfl⟩ : syracuseStep 1992283 = 2988425) B2988425
theorem B10085957 : Blo 1991435 10085957 := bbase (se 4 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 10085957 = 1891117) (by norm_num)
theorem B6723971 : Blo 1991435 6723971 := bstep (se 1 (by rfl) ⟨5042978, by rfl⟩ : syracuseStep 6723971 = 10085957) B10085957
theorem B4482647 : Blo 1991435 4482647 := bstep (se 1 (by rfl) ⟨3361985, by rfl⟩ : syracuseStep 4482647 = 6723971) B6723971
theorem B2988431 : Blo 1991435 2988431 := bstep (se 1 (by rfl) ⟨2241323, by rfl⟩ : syracuseStep 2988431 = 4482647) B4482647
theorem B1992287 : Blo 1991435 1992287 := bstep (se 1 (by rfl) ⟨1494215, by rfl⟩ : syracuseStep 1992287 = 2988431) B2988431
theorem B2988437 : Blo 1991435 2988437 := bbase (se 6 (by rfl) ⟨70041, by rfl⟩ : syracuseStep 2988437 = 140083) (by norm_num)
theorem B1992291 : Blo 1991435 1992291 := bstep (se 1 (by rfl) ⟨1494218, by rfl⟩ : syracuseStep 1992291 = 2988437) B2988437
theorem B9087653 : Blo 1991435 9087653 := bbase (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) (by norm_num)
theorem B6058435 : Blo 1991435 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B8077913 : Blo 1991435 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B5385275 : Blo 1991435 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B3590183 : Blo 1991435 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B9573821 : Blo 1991435 9573821 := bstep (se 3 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 9573821 = 3590183) B3590183
theorem B6382547 : Blo 1991435 6382547 := bstep (se 1 (by rfl) ⟨4786910, by rfl⟩ : syracuseStep 6382547 = 9573821) B9573821
theorem B4255031 : Blo 1991435 4255031 := bstep (se 1 (by rfl) ⟨3191273, by rfl⟩ : syracuseStep 4255031 = 6382547) B6382547
theorem B11346749 : Blo 1991435 11346749 := bstep (se 3 (by rfl) ⟨2127515, by rfl⟩ : syracuseStep 11346749 = 4255031) B4255031
theorem B7564499 : Blo 1991435 7564499 := bstep (se 1 (by rfl) ⟨5673374, by rfl⟩ : syracuseStep 7564499 = 11346749) B11346749
theorem B5042999 : Blo 1991435 5042999 := bstep (se 1 (by rfl) ⟨3782249, by rfl⟩ : syracuseStep 5042999 = 7564499) B7564499
theorem B3361999 : Blo 1991435 3361999 := bstep (se 1 (by rfl) ⟨2521499, by rfl⟩ : syracuseStep 3361999 = 5042999) B5042999
theorem B4482665 : Blo 1991435 4482665 := bstep (se 2 (by rfl) ⟨1680999, by rfl⟩ : syracuseStep 4482665 = 3361999) B3361999
theorem B2988443 : Blo 1991435 2988443 := bstep (se 1 (by rfl) ⟨2241332, by rfl⟩ : syracuseStep 2988443 = 4482665) B4482665
theorem B1992295 : Blo 1991435 1992295 := bstep (se 1 (by rfl) ⟨1494221, by rfl⟩ : syracuseStep 1992295 = 2988443) B2988443
theorem B2241337 : Blo 1991435 2241337 := bbase (se 2 (by rfl) ⟨840501, by rfl⟩ : syracuseStep 2241337 = 1681003) (by norm_num)
theorem B2988449 : Blo 1991435 2988449 := bstep (se 2 (by rfl) ⟨1120668, by rfl⟩ : syracuseStep 2988449 = 2241337) B2241337
theorem B1992299 : Blo 1991435 1992299 := bstep (se 1 (by rfl) ⟨1494224, by rfl⟩ : syracuseStep 1992299 = 2988449) B2988449
theorem B5673397 : Blo 1991435 5673397 := bbase (se 5 (by rfl) ⟨265940, by rfl⟩ : syracuseStep 5673397 = 531881) (by norm_num)
theorem B7564529 : Blo 1991435 7564529 := bstep (se 2 (by rfl) ⟨2836698, by rfl⟩ : syracuseStep 7564529 = 5673397) B5673397
theorem B5043019 : Blo 1991435 5043019 := bstep (se 1 (by rfl) ⟨3782264, by rfl⟩ : syracuseStep 5043019 = 7564529) B7564529
theorem B6724025 : Blo 1991435 6724025 := bstep (se 2 (by rfl) ⟨2521509, by rfl⟩ : syracuseStep 6724025 = 5043019) B5043019
theorem B4482683 : Blo 1991435 4482683 := bstep (se 1 (by rfl) ⟨3362012, by rfl⟩ : syracuseStep 4482683 = 6724025) B6724025
theorem B2988455 : Blo 1991435 2988455 := bstep (se 1 (by rfl) ⟨2241341, by rfl⟩ : syracuseStep 2988455 = 4482683) B4482683
theorem B1992303 : Blo 1991435 1992303 := bstep (se 1 (by rfl) ⟨1494227, by rfl⟩ : syracuseStep 1992303 = 2988455) B2988455
theorem B2988461 : Blo 1991435 2988461 := bbase (se 3 (by rfl) ⟨560336, by rfl⟩ : syracuseStep 2988461 = 1120673) (by norm_num)
theorem B1992307 : Blo 1991435 1992307 := bstep (se 1 (by rfl) ⟨1494230, by rfl⟩ : syracuseStep 1992307 = 2988461) B2988461
theorem B4482701 : Blo 1991435 4482701 := bbase (se 3 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 4482701 = 1681013) (by norm_num)
theorem B2988467 : Blo 1991435 2988467 := bstep (se 1 (by rfl) ⟨2241350, by rfl⟩ : syracuseStep 2988467 = 4482701) B4482701
theorem B1992311 : Blo 1991435 1992311 := bstep (se 1 (by rfl) ⟨1494233, by rfl⟩ : syracuseStep 1992311 = 2988467) B2988467
theorem B2521525 : Blo 1991435 2521525 := bbase (se 5 (by rfl) ⟨118196, by rfl⟩ : syracuseStep 2521525 = 236393) (by norm_num)
theorem B3362033 : Blo 1991435 3362033 := bstep (se 2 (by rfl) ⟨1260762, by rfl⟩ : syracuseStep 3362033 = 2521525) B2521525
theorem B2241355 : Blo 1991435 2241355 := bstep (se 1 (by rfl) ⟨1681016, by rfl⟩ : syracuseStep 2241355 = 3362033) B3362033
theorem B2988473 : Blo 1991435 2988473 := bstep (se 2 (by rfl) ⟨1120677, by rfl⟩ : syracuseStep 2988473 = 2241355) B2241355
theorem B1992315 : Blo 1991435 1992315 := bstep (se 1 (by rfl) ⟨1494236, by rfl⟩ : syracuseStep 1992315 = 2988473) B2988473
theorem B7667797 : Blo 1991435 7667797 := bbase (se 8 (by rfl) ⟨44928, by rfl⟩ : syracuseStep 7667797 = 89857) (by norm_num)
theorem B10223729 : Blo 1991435 10223729 := bstep (se 2 (by rfl) ⟨3833898, by rfl⟩ : syracuseStep 10223729 = 7667797) B7667797
theorem B6815819 : Blo 1991435 6815819 := bstep (se 1 (by rfl) ⟨5111864, by rfl⟩ : syracuseStep 6815819 = 10223729) B10223729
theorem B18175517 : Blo 1991435 18175517 := bstep (se 3 (by rfl) ⟨3407909, by rfl⟩ : syracuseStep 18175517 = 6815819) B6815819
theorem B12117011 : Blo 1991435 12117011 := bstep (se 1 (by rfl) ⟨9087758, by rfl⟩ : syracuseStep 12117011 = 18175517) B18175517
theorem B32312029 : Blo 1991435 32312029 := bstep (se 3 (by rfl) ⟨6058505, by rfl⟩ : syracuseStep 32312029 = 12117011) B12117011
theorem B43082705 : Blo 1991435 43082705 := bstep (se 2 (by rfl) ⟨16156014, by rfl⟩ : syracuseStep 43082705 = 32312029) B32312029
theorem B28721803 : Blo 1991435 28721803 := bstep (se 1 (by rfl) ⟨21541352, by rfl⟩ : syracuseStep 28721803 = 43082705) B43082705
theorem B38295737 : Blo 1991435 38295737 := bstep (se 2 (by rfl) ⟨14360901, by rfl⟩ : syracuseStep 38295737 = 28721803) B28721803
theorem B25530491 : Blo 1991435 25530491 := bstep (se 1 (by rfl) ⟨19147868, by rfl⟩ : syracuseStep 25530491 = 38295737) B38295737
theorem B17020327 : Blo 1991435 17020327 := bstep (se 1 (by rfl) ⟨12765245, by rfl⟩ : syracuseStep 17020327 = 25530491) B25530491
theorem B22693769 : Blo 1991435 22693769 := bstep (se 2 (by rfl) ⟨8510163, by rfl⟩ : syracuseStep 22693769 = 17020327) B17020327
theorem B15129179 : Blo 1991435 15129179 := bstep (se 1 (by rfl) ⟨11346884, by rfl⟩ : syracuseStep 15129179 = 22693769) B22693769
theorem B10086119 : Blo 1991435 10086119 := bstep (se 1 (by rfl) ⟨7564589, by rfl⟩ : syracuseStep 10086119 = 15129179) B15129179
theorem B6724079 : Blo 1991435 6724079 := bstep (se 1 (by rfl) ⟨5043059, by rfl⟩ : syracuseStep 6724079 = 10086119) B10086119
theorem B4482719 : Blo 1991435 4482719 := bstep (se 1 (by rfl) ⟨3362039, by rfl⟩ : syracuseStep 4482719 = 6724079) B6724079
theorem B2988479 : Blo 1991435 2988479 := bstep (se 1 (by rfl) ⟨2241359, by rfl⟩ : syracuseStep 2988479 = 4482719) B4482719
theorem B1992319 : Blo 1991435 1992319 := bstep (se 1 (by rfl) ⟨1494239, by rfl⟩ : syracuseStep 1992319 = 2988479) B2988479
theorem B2988485 : Blo 1991435 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B1992323 : Blo 1991435 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B3362053 : Blo 1991435 3362053 := bbase (se 4 (by rfl) ⟨315192, by rfl⟩ : syracuseStep 3362053 = 630385) (by norm_num)
theorem B4482737 : Blo 1991435 4482737 := bstep (se 2 (by rfl) ⟨1681026, by rfl⟩ : syracuseStep 4482737 = 3362053) B3362053
theorem B2988491 : Blo 1991435 2988491 := bstep (se 1 (by rfl) ⟨2241368, by rfl⟩ : syracuseStep 2988491 = 4482737) B4482737
theorem B1992327 : Blo 1991435 1992327 := bstep (se 1 (by rfl) ⟨1494245, by rfl⟩ : syracuseStep 1992327 = 2988491) B2988491
theorem B2241373 : Blo 1991435 2241373 := bbase (se 3 (by rfl) ⟨420257, by rfl⟩ : syracuseStep 2241373 = 840515) (by norm_num)
theorem B2988497 : Blo 1991435 2988497 := bstep (se 2 (by rfl) ⟨1120686, by rfl⟩ : syracuseStep 2988497 = 2241373) B2241373
theorem B1992331 : Blo 1991435 1992331 := bstep (se 1 (by rfl) ⟨1494248, by rfl⟩ : syracuseStep 1992331 = 2988497) B2988497
theorem B6724133 : Blo 1991435 6724133 := bbase (se 4 (by rfl) ⟨630387, by rfl⟩ : syracuseStep 6724133 = 1260775) (by norm_num)
theorem B4482755 : Blo 1991435 4482755 := bstep (se 1 (by rfl) ⟨3362066, by rfl⟩ : syracuseStep 4482755 = 6724133) B6724133
theorem B2988503 : Blo 1991435 2988503 := bstep (se 1 (by rfl) ⟨2241377, by rfl⟩ : syracuseStep 2988503 = 4482755) B4482755
theorem B1992335 : Blo 1991435 1992335 := bstep (se 1 (by rfl) ⟨1494251, by rfl⟩ : syracuseStep 1992335 = 2988503) B2988503
theorem B2988509 : Blo 1991435 2988509 := bbase (se 3 (by rfl) ⟨560345, by rfl⟩ : syracuseStep 2988509 = 1120691) (by norm_num)
theorem B1992339 : Blo 1991435 1992339 := bstep (se 1 (by rfl) ⟨1494254, by rfl⟩ : syracuseStep 1992339 = 2988509) B2988509
theorem B4482773 : Blo 1991435 4482773 := bbase (se 7 (by rfl) ⟨52532, by rfl⟩ : syracuseStep 4482773 = 105065) (by norm_num)
theorem B2988515 : Blo 1991435 2988515 := bstep (se 1 (by rfl) ⟨2241386, by rfl⟩ : syracuseStep 2988515 = 4482773) B4482773
theorem B1992343 : Blo 1991435 1992343 := bstep (se 1 (by rfl) ⟨1494257, by rfl⟩ : syracuseStep 1992343 = 2988515) B2988515
theorem B3191357 : Blo 1991435 3191357 := bbase (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) (by norm_num)
theorem B8510285 : Blo 1991435 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B5673523 : Blo 1991435 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B7564697 : Blo 1991435 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B5043131 : Blo 1991435 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B3362087 : Blo 1991435 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B2241391 : Blo 1991435 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B2988521 : Blo 1991435 2988521 := bstep (se 2 (by rfl) ⟨1120695, by rfl⟩ : syracuseStep 2988521 = 2241391) B2241391
theorem B1992347 : Blo 1991435 1992347 := bstep (se 1 (by rfl) ⟨1494260, by rfl⟩ : syracuseStep 1992347 = 2988521) B2988521
theorem B4039069 : Blo 1991435 4039069 := bbase (se 3 (by rfl) ⟨757325, by rfl⟩ : syracuseStep 4039069 = 1514651) (by norm_num)
theorem B5385425 : Blo 1991435 5385425 := bstep (se 2 (by rfl) ⟨2019534, by rfl⟩ : syracuseStep 5385425 = 4039069) B4039069
theorem B14361133 : Blo 1991435 14361133 := bstep (se 3 (by rfl) ⟨2692712, by rfl⟩ : syracuseStep 14361133 = 5385425) B5385425
theorem B19148177 : Blo 1991435 19148177 := bstep (se 2 (by rfl) ⟨7180566, by rfl⟩ : syracuseStep 19148177 = 14361133) B14361133
theorem B12765451 : Blo 1991435 12765451 := bstep (se 1 (by rfl) ⟨9574088, by rfl⟩ : syracuseStep 12765451 = 19148177) B19148177
theorem B17020601 : Blo 1991435 17020601 := bstep (se 2 (by rfl) ⟨6382725, by rfl⟩ : syracuseStep 17020601 = 12765451) B12765451
theorem B11347067 : Blo 1991435 11347067 := bstep (se 1 (by rfl) ⟨8510300, by rfl⟩ : syracuseStep 11347067 = 17020601) B17020601
theorem B7564711 : Blo 1991435 7564711 := bstep (se 1 (by rfl) ⟨5673533, by rfl⟩ : syracuseStep 7564711 = 11347067) B11347067
theorem B10086281 : Blo 1991435 10086281 := bstep (se 2 (by rfl) ⟨3782355, by rfl⟩ : syracuseStep 10086281 = 7564711) B7564711
theorem B6724187 : Blo 1991435 6724187 := bstep (se 1 (by rfl) ⟨5043140, by rfl⟩ : syracuseStep 6724187 = 10086281) B10086281
theorem B4482791 : Blo 1991435 4482791 := bstep (se 1 (by rfl) ⟨3362093, by rfl⟩ : syracuseStep 4482791 = 6724187) B6724187
theorem B2988527 : Blo 1991435 2988527 := bstep (se 1 (by rfl) ⟨2241395, by rfl⟩ : syracuseStep 2988527 = 4482791) B4482791
theorem B1992351 : Blo 1991435 1992351 := bstep (se 1 (by rfl) ⟨1494263, by rfl⟩ : syracuseStep 1992351 = 2988527) B2988527
theorem B2988533 : Blo 1991435 2988533 := bbase (se 5 (by rfl) ⟨140087, by rfl⟩ : syracuseStep 2988533 = 280175) (by norm_num)
theorem B1992355 : Blo 1991435 1992355 := bstep (se 1 (by rfl) ⟨1494266, by rfl⟩ : syracuseStep 1992355 = 2988533) B2988533
theorem B5673557 : Blo 1991435 5673557 := bbase (se 8 (by rfl) ⟨33243, by rfl⟩ : syracuseStep 5673557 = 66487) (by norm_num)
theorem B3782371 : Blo 1991435 3782371 := bstep (se 1 (by rfl) ⟨2836778, by rfl⟩ : syracuseStep 3782371 = 5673557) B5673557
theorem B5043161 : Blo 1991435 5043161 := bstep (se 2 (by rfl) ⟨1891185, by rfl⟩ : syracuseStep 5043161 = 3782371) B3782371
theorem B3362107 : Blo 1991435 3362107 := bstep (se 1 (by rfl) ⟨2521580, by rfl⟩ : syracuseStep 3362107 = 5043161) B5043161
theorem B4482809 : Blo 1991435 4482809 := bstep (se 2 (by rfl) ⟨1681053, by rfl⟩ : syracuseStep 4482809 = 3362107) B3362107
theorem B2988539 : Blo 1991435 2988539 := bstep (se 1 (by rfl) ⟨2241404, by rfl⟩ : syracuseStep 2988539 = 4482809) B4482809
theorem B1992359 : Blo 1991435 1992359 := bstep (se 1 (by rfl) ⟨1494269, by rfl⟩ : syracuseStep 1992359 = 2988539) B2988539
theorem B2241409 : Blo 1991435 2241409 := bbase (se 2 (by rfl) ⟨840528, by rfl⟩ : syracuseStep 2241409 = 1681057) (by norm_num)
theorem B2988545 : Blo 1991435 2988545 := bstep (se 2 (by rfl) ⟨1120704, by rfl⟩ : syracuseStep 2988545 = 2241409) B2241409
theorem B1992363 : Blo 1991435 1992363 := bstep (se 1 (by rfl) ⟨1494272, by rfl⟩ : syracuseStep 1992363 = 2988545) B2988545
theorem B5043181 : Blo 1991435 5043181 := bbase (se 3 (by rfl) ⟨945596, by rfl⟩ : syracuseStep 5043181 = 1891193) (by norm_num)
theorem B6724241 : Blo 1991435 6724241 := bstep (se 2 (by rfl) ⟨2521590, by rfl⟩ : syracuseStep 6724241 = 5043181) B5043181
theorem B4482827 : Blo 1991435 4482827 := bstep (se 1 (by rfl) ⟨3362120, by rfl⟩ : syracuseStep 4482827 = 6724241) B6724241
theorem B2988551 : Blo 1991435 2988551 := bstep (se 1 (by rfl) ⟨2241413, by rfl⟩ : syracuseStep 2988551 = 4482827) B4482827
theorem B1992367 : Blo 1991435 1992367 := bstep (se 1 (by rfl) ⟨1494275, by rfl⟩ : syracuseStep 1992367 = 2988551) B2988551
theorem B2988557 : Blo 1991435 2988557 := bbase (se 3 (by rfl) ⟨560354, by rfl⟩ : syracuseStep 2988557 = 1120709) (by norm_num)
theorem B1992371 : Blo 1991435 1992371 := bstep (se 1 (by rfl) ⟨1494278, by rfl⟩ : syracuseStep 1992371 = 2988557) B2988557
theorem B4482845 : Blo 1991435 4482845 := bbase (se 3 (by rfl) ⟨840533, by rfl⟩ : syracuseStep 4482845 = 1681067) (by norm_num)
theorem B2988563 : Blo 1991435 2988563 := bstep (se 1 (by rfl) ⟨2241422, by rfl⟩ : syracuseStep 2988563 = 4482845) B4482845
theorem B1992375 : Blo 1991435 1992375 := bstep (se 1 (by rfl) ⟨1494281, by rfl⟩ : syracuseStep 1992375 = 2988563) B2988563
theorem B3362141 : Blo 1991435 3362141 := bbase (se 3 (by rfl) ⟨630401, by rfl⟩ : syracuseStep 3362141 = 1260803) (by norm_num)
theorem B2241427 : Blo 1991435 2241427 := bstep (se 1 (by rfl) ⟨1681070, by rfl⟩ : syracuseStep 2241427 = 3362141) B3362141
theorem B2988569 : Blo 1991435 2988569 := bstep (se 2 (by rfl) ⟨1120713, by rfl⟩ : syracuseStep 2988569 = 2241427) B2241427
theorem B1992379 : Blo 1991435 1992379 := bstep (se 1 (by rfl) ⟨1494284, by rfl⟩ : syracuseStep 1992379 = 2988569) B2988569
theorem B8510437 : Blo 1991435 8510437 := bbase (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) (by norm_num)
theorem B11347249 : Blo 1991435 11347249 := bstep (se 2 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 11347249 = 8510437) B8510437
theorem B15129665 : Blo 1991435 15129665 := bstep (se 2 (by rfl) ⟨5673624, by rfl⟩ : syracuseStep 15129665 = 11347249) B11347249
theorem B10086443 : Blo 1991435 10086443 := bstep (se 1 (by rfl) ⟨7564832, by rfl⟩ : syracuseStep 10086443 = 15129665) B15129665
theorem B6724295 : Blo 1991435 6724295 := bstep (se 1 (by rfl) ⟨5043221, by rfl⟩ : syracuseStep 6724295 = 10086443) B10086443
theorem B4482863 : Blo 1991435 4482863 := bstep (se 1 (by rfl) ⟨3362147, by rfl⟩ : syracuseStep 4482863 = 6724295) B6724295
theorem B2988575 : Blo 1991435 2988575 := bstep (se 1 (by rfl) ⟨2241431, by rfl⟩ : syracuseStep 2988575 = 4482863) B4482863
theorem B1992383 : Blo 1991435 1992383 := bstep (se 1 (by rfl) ⟨1494287, by rfl⟩ : syracuseStep 1992383 = 2988575) B2988575
theorem B2988581 : Blo 1991435 2988581 := bbase (se 4 (by rfl) ⟨280179, by rfl⟩ : syracuseStep 2988581 = 560359) (by norm_num)
theorem B1992387 : Blo 1991435 1992387 := bstep (se 1 (by rfl) ⟨1494290, by rfl⟩ : syracuseStep 1992387 = 2988581) B2988581
theorem B2521621 : Blo 1991435 2521621 := bbase (se 6 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 2521621 = 118201) (by norm_num)
theorem B3362161 : Blo 1991435 3362161 := bstep (se 2 (by rfl) ⟨1260810, by rfl⟩ : syracuseStep 3362161 = 2521621) B2521621
theorem B4482881 : Blo 1991435 4482881 := bstep (se 2 (by rfl) ⟨1681080, by rfl⟩ : syracuseStep 4482881 = 3362161) B3362161
theorem B2988587 : Blo 1991435 2988587 := bstep (se 1 (by rfl) ⟨2241440, by rfl⟩ : syracuseStep 2988587 = 4482881) B4482881
theorem B1992391 : Blo 1991435 1992391 := bstep (se 1 (by rfl) ⟨1494293, by rfl⟩ : syracuseStep 1992391 = 2988587) B2988587
theorem B2241445 : Blo 1991435 2241445 := bbase (se 4 (by rfl) ⟨210135, by rfl⟩ : syracuseStep 2241445 = 420271) (by norm_num)
theorem B2988593 : Blo 1991435 2988593 := bstep (se 2 (by rfl) ⟨1120722, by rfl⟩ : syracuseStep 2988593 = 2241445) B2241445
theorem B1992395 : Blo 1991435 1992395 := bstep (se 1 (by rfl) ⟨1494296, by rfl⟩ : syracuseStep 1992395 = 2988593) B2988593
theorem B7180741 : Blo 1991435 7180741 := bbase (se 4 (by rfl) ⟨673194, by rfl⟩ : syracuseStep 7180741 = 1346389) (by norm_num)
theorem B9574321 : Blo 1991435 9574321 := bstep (se 2 (by rfl) ⟨3590370, by rfl⟩ : syracuseStep 9574321 = 7180741) B7180741
theorem B12765761 : Blo 1991435 12765761 := bstep (se 2 (by rfl) ⟨4787160, by rfl⟩ : syracuseStep 12765761 = 9574321) B9574321
theorem B8510507 : Blo 1991435 8510507 := bstep (se 1 (by rfl) ⟨6382880, by rfl⟩ : syracuseStep 8510507 = 12765761) B12765761
theorem B5673671 : Blo 1991435 5673671 := bstep (se 1 (by rfl) ⟨4255253, by rfl⟩ : syracuseStep 5673671 = 8510507) B8510507
theorem B3782447 : Blo 1991435 3782447 := bstep (se 1 (by rfl) ⟨2836835, by rfl⟩ : syracuseStep 3782447 = 5673671) B5673671
theorem B2521631 : Blo 1991435 2521631 := bstep (se 1 (by rfl) ⟨1891223, by rfl⟩ : syracuseStep 2521631 = 3782447) B3782447
theorem B6724349 : Blo 1991435 6724349 := bstep (se 3 (by rfl) ⟨1260815, by rfl⟩ : syracuseStep 6724349 = 2521631) B2521631
theorem B4482899 : Blo 1991435 4482899 := bstep (se 1 (by rfl) ⟨3362174, by rfl⟩ : syracuseStep 4482899 = 6724349) B6724349
theorem B2988599 : Blo 1991435 2988599 := bstep (se 1 (by rfl) ⟨2241449, by rfl⟩ : syracuseStep 2988599 = 4482899) B4482899
theorem B1992399 : Blo 1991435 1992399 := bstep (se 1 (by rfl) ⟨1494299, by rfl⟩ : syracuseStep 1992399 = 2988599) B2988599
theorem B2988605 : Blo 1991435 2988605 := bbase (se 3 (by rfl) ⟨560363, by rfl⟩ : syracuseStep 2988605 = 1120727) (by norm_num)
theorem B1992403 : Blo 1991435 1992403 := bstep (se 1 (by rfl) ⟨1494302, by rfl⟩ : syracuseStep 1992403 = 2988605) B2988605
theorem B4482917 : Blo 1991435 4482917 := bbase (se 4 (by rfl) ⟨420273, by rfl⟩ : syracuseStep 4482917 = 840547) (by norm_num)
theorem B2988611 : Blo 1991435 2988611 := bstep (se 1 (by rfl) ⟨2241458, by rfl⟩ : syracuseStep 2988611 = 4482917) B4482917
theorem B1992407 : Blo 1991435 1992407 := bstep (se 1 (by rfl) ⟨1494305, by rfl⟩ : syracuseStep 1992407 = 2988611) B2988611
theorem B5043293 : Blo 1991435 5043293 := bbase (se 3 (by rfl) ⟨945617, by rfl⟩ : syracuseStep 5043293 = 1891235) (by norm_num)
theorem B3362195 : Blo 1991435 3362195 := bstep (se 1 (by rfl) ⟨2521646, by rfl⟩ : syracuseStep 3362195 = 5043293) B5043293
theorem B2241463 : Blo 1991435 2241463 := bstep (se 1 (by rfl) ⟨1681097, by rfl⟩ : syracuseStep 2241463 = 3362195) B3362195
theorem B2988617 : Blo 1991435 2988617 := bstep (se 2 (by rfl) ⟨1120731, by rfl⟩ : syracuseStep 2988617 = 2241463) B2241463
theorem B1992411 : Blo 1991435 1992411 := bstep (se 1 (by rfl) ⟨1494308, by rfl⟩ : syracuseStep 1992411 = 2988617) B2988617
theorem B3782477 : Blo 1991435 3782477 := bbase (se 3 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 3782477 = 1418429) (by norm_num)
theorem B10086605 : Blo 1991435 10086605 := bstep (se 3 (by rfl) ⟨1891238, by rfl⟩ : syracuseStep 10086605 = 3782477) B3782477
theorem B6724403 : Blo 1991435 6724403 := bstep (se 1 (by rfl) ⟨5043302, by rfl⟩ : syracuseStep 6724403 = 10086605) B10086605
theorem B4482935 : Blo 1991435 4482935 := bstep (se 1 (by rfl) ⟨3362201, by rfl⟩ : syracuseStep 4482935 = 6724403) B6724403
theorem B2988623 : Blo 1991435 2988623 := bstep (se 1 (by rfl) ⟨2241467, by rfl⟩ : syracuseStep 2988623 = 4482935) B4482935
theorem B1992415 : Blo 1991435 1992415 := bstep (se 1 (by rfl) ⟨1494311, by rfl⟩ : syracuseStep 1992415 = 2988623) B2988623
theorem B2988629 : Blo 1991435 2988629 := bbase (se 8 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 2988629 = 35023) (by norm_num)
theorem B1992419 : Blo 1991435 1992419 := bstep (se 1 (by rfl) ⟨1494314, by rfl⟩ : syracuseStep 1992419 = 2988629) B2988629
theorem B2393609 : Blo 1991435 2393609 := bbase (se 2 (by rfl) ⟨897603, by rfl⟩ : syracuseStep 2393609 = 1795207) (by norm_num)
theorem B6382957 : Blo 1991435 6382957 := bstep (se 3 (by rfl) ⟨1196804, by rfl⟩ : syracuseStep 6382957 = 2393609) B2393609
theorem B8510609 : Blo 1991435 8510609 := bstep (se 2 (by rfl) ⟨3191478, by rfl⟩ : syracuseStep 8510609 = 6382957) B6382957
theorem B5673739 : Blo 1991435 5673739 := bstep (se 1 (by rfl) ⟨4255304, by rfl⟩ : syracuseStep 5673739 = 8510609) B8510609
theorem B7564985 : Blo 1991435 7564985 := bstep (se 2 (by rfl) ⟨2836869, by rfl⟩ : syracuseStep 7564985 = 5673739) B5673739
theorem B5043323 : Blo 1991435 5043323 := bstep (se 1 (by rfl) ⟨3782492, by rfl⟩ : syracuseStep 5043323 = 7564985) B7564985
theorem B3362215 : Blo 1991435 3362215 := bstep (se 1 (by rfl) ⟨2521661, by rfl⟩ : syracuseStep 3362215 = 5043323) B5043323
theorem B4482953 : Blo 1991435 4482953 := bstep (se 2 (by rfl) ⟨1681107, by rfl⟩ : syracuseStep 4482953 = 3362215) B3362215
theorem B2988635 : Blo 1991435 2988635 := bstep (se 1 (by rfl) ⟨2241476, by rfl⟩ : syracuseStep 2988635 = 4482953) B4482953
theorem B1992423 : Blo 1991435 1992423 := bstep (se 1 (by rfl) ⟨1494317, by rfl⟩ : syracuseStep 1992423 = 2988635) B2988635
theorem B2241481 : Blo 1991435 2241481 := bbase (se 2 (by rfl) ⟨840555, by rfl⟩ : syracuseStep 2241481 = 1681111) (by norm_num)
theorem B2988641 : Blo 1991435 2988641 := bstep (se 2 (by rfl) ⟨1120740, by rfl⟩ : syracuseStep 2988641 = 2241481) B2241481
theorem B1992427 : Blo 1991435 1992427 := bstep (se 1 (by rfl) ⟨1494320, by rfl⟩ : syracuseStep 1992427 = 2988641) B2988641
theorem B4787237 : Blo 1991435 4787237 := bbase (se 4 (by rfl) ⟨448803, by rfl⟩ : syracuseStep 4787237 = 897607) (by norm_num)
theorem B3191491 : Blo 1991435 3191491 := bstep (se 1 (by rfl) ⟨2393618, by rfl⟩ : syracuseStep 3191491 = 4787237) B4787237
theorem B17021285 : Blo 1991435 17021285 := bstep (se 4 (by rfl) ⟨1595745, by rfl⟩ : syracuseStep 17021285 = 3191491) B3191491
theorem B11347523 : Blo 1991435 11347523 := bstep (se 1 (by rfl) ⟨8510642, by rfl⟩ : syracuseStep 11347523 = 17021285) B17021285
theorem B7565015 : Blo 1991435 7565015 := bstep (se 1 (by rfl) ⟨5673761, by rfl⟩ : syracuseStep 7565015 = 11347523) B11347523
theorem B5043343 : Blo 1991435 5043343 := bstep (se 1 (by rfl) ⟨3782507, by rfl⟩ : syracuseStep 5043343 = 7565015) B7565015
theorem B6724457 : Blo 1991435 6724457 := bstep (se 2 (by rfl) ⟨2521671, by rfl⟩ : syracuseStep 6724457 = 5043343) B5043343
theorem B4482971 : Blo 1991435 4482971 := bstep (se 1 (by rfl) ⟨3362228, by rfl⟩ : syracuseStep 4482971 = 6724457) B6724457
theorem B2988647 : Blo 1991435 2988647 := bstep (se 1 (by rfl) ⟨2241485, by rfl⟩ : syracuseStep 2988647 = 4482971) B4482971
theorem B1992431 : Blo 1991435 1992431 := bstep (se 1 (by rfl) ⟨1494323, by rfl⟩ : syracuseStep 1992431 = 2988647) B2988647
theorem B2988653 : Blo 1991435 2988653 := bbase (se 3 (by rfl) ⟨560372, by rfl⟩ : syracuseStep 2988653 = 1120745) (by norm_num)
theorem B1992435 : Blo 1991435 1992435 := bstep (se 1 (by rfl) ⟨1494326, by rfl⟩ : syracuseStep 1992435 = 2988653) B2988653
theorem B4482989 : Blo 1991435 4482989 := bbase (se 3 (by rfl) ⟨840560, by rfl⟩ : syracuseStep 4482989 = 1681121) (by norm_num)
theorem B2988659 : Blo 1991435 2988659 := bstep (se 1 (by rfl) ⟨2241494, by rfl⟩ : syracuseStep 2988659 = 4482989) B4482989
theorem B1992439 : Blo 1991435 1992439 := bstep (se 1 (by rfl) ⟨1494329, by rfl⟩ : syracuseStep 1992439 = 2988659) B2988659
theorem B5673797 : Blo 1991435 5673797 := bbase (se 4 (by rfl) ⟨531918, by rfl⟩ : syracuseStep 5673797 = 1063837) (by norm_num)
theorem B3782531 : Blo 1991435 3782531 := bstep (se 1 (by rfl) ⟨2836898, by rfl⟩ : syracuseStep 3782531 = 5673797) B5673797
theorem B2521687 : Blo 1991435 2521687 := bstep (se 1 (by rfl) ⟨1891265, by rfl⟩ : syracuseStep 2521687 = 3782531) B3782531
theorem B3362249 : Blo 1991435 3362249 := bstep (se 2 (by rfl) ⟨1260843, by rfl⟩ : syracuseStep 3362249 = 2521687) B2521687
theorem B2241499 : Blo 1991435 2241499 := bstep (se 1 (by rfl) ⟨1681124, by rfl⟩ : syracuseStep 2241499 = 3362249) B3362249
theorem B2988665 : Blo 1991435 2988665 := bstep (se 2 (by rfl) ⟨1120749, by rfl⟩ : syracuseStep 2988665 = 2241499) B2241499
theorem B1992443 : Blo 1991435 1992443 := bstep (se 1 (by rfl) ⟨1494332, by rfl⟩ : syracuseStep 1992443 = 2988665) B2988665
theorem B38298197 : Blo 1991435 38298197 := bbase (se 8 (by rfl) ⟨224403, by rfl⟩ : syracuseStep 38298197 = 448807) (by norm_num)
theorem B25532131 : Blo 1991435 25532131 := bstep (se 1 (by rfl) ⟨19149098, by rfl⟩ : syracuseStep 25532131 = 38298197) B38298197
theorem B34042841 : Blo 1991435 34042841 := bstep (se 2 (by rfl) ⟨12766065, by rfl⟩ : syracuseStep 34042841 = 25532131) B25532131
theorem B22695227 : Blo 1991435 22695227 := bstep (se 1 (by rfl) ⟨17021420, by rfl⟩ : syracuseStep 22695227 = 34042841) B34042841
theorem B15130151 : Blo 1991435 15130151 := bstep (se 1 (by rfl) ⟨11347613, by rfl⟩ : syracuseStep 15130151 = 22695227) B22695227
theorem B10086767 : Blo 1991435 10086767 := bstep (se 1 (by rfl) ⟨7565075, by rfl⟩ : syracuseStep 10086767 = 15130151) B15130151
theorem B6724511 : Blo 1991435 6724511 := bstep (se 1 (by rfl) ⟨5043383, by rfl⟩ : syracuseStep 6724511 = 10086767) B10086767
theorem B4483007 : Blo 1991435 4483007 := bstep (se 1 (by rfl) ⟨3362255, by rfl⟩ : syracuseStep 4483007 = 6724511) B6724511
theorem B2988671 : Blo 1991435 2988671 := bstep (se 1 (by rfl) ⟨2241503, by rfl⟩ : syracuseStep 2988671 = 4483007) B4483007
theorem B1992447 : Blo 1991435 1992447 := bstep (se 1 (by rfl) ⟨1494335, by rfl⟩ : syracuseStep 1992447 = 2988671) B2988671
theorem B2988677 : Blo 1991435 2988677 := bbase (se 4 (by rfl) ⟨280188, by rfl⟩ : syracuseStep 2988677 = 560377) (by norm_num)
theorem B1992451 : Blo 1991435 1992451 := bstep (se 1 (by rfl) ⟨1494338, by rfl⟩ : syracuseStep 1992451 = 2988677) B2988677
theorem B3362269 : Blo 1991435 3362269 := bbase (se 3 (by rfl) ⟨630425, by rfl⟩ : syracuseStep 3362269 = 1260851) (by norm_num)
theorem B4483025 : Blo 1991435 4483025 := bstep (se 2 (by rfl) ⟨1681134, by rfl⟩ : syracuseStep 4483025 = 3362269) B3362269
theorem B2988683 : Blo 1991435 2988683 := bstep (se 1 (by rfl) ⟨2241512, by rfl⟩ : syracuseStep 2988683 = 4483025) B4483025
theorem B1992455 : Blo 1991435 1992455 := bstep (se 1 (by rfl) ⟨1494341, by rfl⟩ : syracuseStep 1992455 = 2988683) B2988683
theorem B2241517 : Blo 1991435 2241517 := bbase (se 3 (by rfl) ⟨420284, by rfl⟩ : syracuseStep 2241517 = 840569) (by norm_num)
theorem B2988689 : Blo 1991435 2988689 := bstep (se 2 (by rfl) ⟨1120758, by rfl⟩ : syracuseStep 2988689 = 2241517) B2241517
theorem B1992459 : Blo 1991435 1992459 := bstep (se 1 (by rfl) ⟨1494344, by rfl⟩ : syracuseStep 1992459 = 2988689) B2988689
theorem B6724565 : Blo 1991435 6724565 := bbase (se 7 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 6724565 = 157607) (by norm_num)
theorem B4483043 : Blo 1991435 4483043 := bstep (se 1 (by rfl) ⟨3362282, by rfl⟩ : syracuseStep 4483043 = 6724565) B6724565
theorem B2988695 : Blo 1991435 2988695 := bstep (se 1 (by rfl) ⟨2241521, by rfl⟩ : syracuseStep 2988695 = 4483043) B4483043
theorem B1992463 : Blo 1991435 1992463 := bstep (se 1 (by rfl) ⟨1494347, by rfl⟩ : syracuseStep 1992463 = 2988695) B2988695
theorem B2988701 : Blo 1991435 2988701 := bbase (se 3 (by rfl) ⟨560381, by rfl⟩ : syracuseStep 2988701 = 1120763) (by norm_num)
theorem B1992467 : Blo 1991435 1992467 := bstep (se 1 (by rfl) ⟨1494350, by rfl⟩ : syracuseStep 1992467 = 2988701) B2988701
theorem B4483061 : Blo 1991435 4483061 := bbase (se 5 (by rfl) ⟨210143, by rfl⟩ : syracuseStep 4483061 = 420287) (by norm_num)
theorem B2988707 : Blo 1991435 2988707 := bstep (se 1 (by rfl) ⟨2241530, by rfl⟩ : syracuseStep 2988707 = 4483061) B4483061
theorem B1992471 : Blo 1991435 1992471 := bstep (se 1 (by rfl) ⟨1494353, by rfl⟩ : syracuseStep 1992471 = 2988707) B2988707
theorem B6058981 : Blo 1991435 6058981 := bbase (se 4 (by rfl) ⟨568029, by rfl⟩ : syracuseStep 6058981 = 1136059) (by norm_num)
theorem B32314565 : Blo 1991435 32314565 := bstep (se 4 (by rfl) ⟨3029490, by rfl⟩ : syracuseStep 32314565 = 6058981) B6058981
theorem B86172173 : Blo 1991435 86172173 := bstep (se 3 (by rfl) ⟨16157282, by rfl⟩ : syracuseStep 86172173 = 32314565) B32314565
theorem B57448115 : Blo 1991435 57448115 := bstep (se 1 (by rfl) ⟨43086086, by rfl⟩ : syracuseStep 57448115 = 86172173) B86172173
theorem B38298743 : Blo 1991435 38298743 := bstep (se 1 (by rfl) ⟨28724057, by rfl⟩ : syracuseStep 38298743 = 57448115) B57448115
theorem B25532495 : Blo 1991435 25532495 := bstep (se 1 (by rfl) ⟨19149371, by rfl⟩ : syracuseStep 25532495 = 38298743) B38298743
theorem B17021663 : Blo 1991435 17021663 := bstep (se 1 (by rfl) ⟨12766247, by rfl⟩ : syracuseStep 17021663 = 25532495) B25532495
theorem B11347775 : Blo 1991435 11347775 := bstep (se 1 (by rfl) ⟨8510831, by rfl⟩ : syracuseStep 11347775 = 17021663) B17021663
theorem B7565183 : Blo 1991435 7565183 := bstep (se 1 (by rfl) ⟨5673887, by rfl⟩ : syracuseStep 7565183 = 11347775) B11347775
theorem B5043455 : Blo 1991435 5043455 := bstep (se 1 (by rfl) ⟨3782591, by rfl⟩ : syracuseStep 5043455 = 7565183) B7565183
theorem B3362303 : Blo 1991435 3362303 := bstep (se 1 (by rfl) ⟨2521727, by rfl⟩ : syracuseStep 3362303 = 5043455) B5043455
theorem B2241535 : Blo 1991435 2241535 := bstep (se 1 (by rfl) ⟨1681151, by rfl⟩ : syracuseStep 2241535 = 3362303) B3362303
theorem B2988713 : Blo 1991435 2988713 := bstep (se 2 (by rfl) ⟨1120767, by rfl⟩ : syracuseStep 2988713 = 2241535) B2241535
theorem B1992475 : Blo 1991435 1992475 := bstep (se 1 (by rfl) ⟨1494356, by rfl⟩ : syracuseStep 1992475 = 2988713) B2988713
theorem B2836949 : Blo 1991435 2836949 := bbase (se 7 (by rfl) ⟨33245, by rfl⟩ : syracuseStep 2836949 = 66491) (by norm_num)
theorem B7565197 : Blo 1991435 7565197 := bstep (se 3 (by rfl) ⟨1418474, by rfl⟩ : syracuseStep 7565197 = 2836949) B2836949
theorem B10086929 : Blo 1991435 10086929 := bstep (se 2 (by rfl) ⟨3782598, by rfl⟩ : syracuseStep 10086929 = 7565197) B7565197
theorem B6724619 : Blo 1991435 6724619 := bstep (se 1 (by rfl) ⟨5043464, by rfl⟩ : syracuseStep 6724619 = 10086929) B10086929
theorem B4483079 : Blo 1991435 4483079 := bstep (se 1 (by rfl) ⟨3362309, by rfl⟩ : syracuseStep 4483079 = 6724619) B6724619
theorem B2988719 : Blo 1991435 2988719 := bstep (se 1 (by rfl) ⟨2241539, by rfl⟩ : syracuseStep 2988719 = 4483079) B4483079
theorem B1992479 : Blo 1991435 1992479 := bstep (se 1 (by rfl) ⟨1494359, by rfl⟩ : syracuseStep 1992479 = 2988719) B2988719
theorem B2988725 : Blo 1991435 2988725 := bbase (se 5 (by rfl) ⟨140096, by rfl⟩ : syracuseStep 2988725 = 280193) (by norm_num)
theorem B1992483 : Blo 1991435 1992483 := bstep (se 1 (by rfl) ⟨1494362, by rfl⟩ : syracuseStep 1992483 = 2988725) B2988725
theorem B5043485 : Blo 1991435 5043485 := bbase (se 3 (by rfl) ⟨945653, by rfl⟩ : syracuseStep 5043485 = 1891307) (by norm_num)
theorem B3362323 : Blo 1991435 3362323 := bstep (se 1 (by rfl) ⟨2521742, by rfl⟩ : syracuseStep 3362323 = 5043485) B5043485
theorem B4483097 : Blo 1991435 4483097 := bstep (se 2 (by rfl) ⟨1681161, by rfl⟩ : syracuseStep 4483097 = 3362323) B3362323
theorem B2988731 : Blo 1991435 2988731 := bstep (se 1 (by rfl) ⟨2241548, by rfl⟩ : syracuseStep 2988731 = 4483097) B4483097
theorem B1992487 : Blo 1991435 1992487 := bstep (se 1 (by rfl) ⟨1494365, by rfl⟩ : syracuseStep 1992487 = 2988731) B2988731
theorem B2241553 : Blo 1991435 2241553 := bbase (se 2 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 2241553 = 1681165) (by norm_num)
theorem B2988737 : Blo 1991435 2988737 := bstep (se 2 (by rfl) ⟨1120776, by rfl⟩ : syracuseStep 2988737 = 2241553) B2241553
theorem B1992491 : Blo 1991435 1992491 := bstep (se 1 (by rfl) ⟨1494368, by rfl⟩ : syracuseStep 1992491 = 2988737) B2988737
theorem B3782629 : Blo 1991435 3782629 := bbase (se 4 (by rfl) ⟨354621, by rfl⟩ : syracuseStep 3782629 = 709243) (by norm_num)
theorem B5043505 : Blo 1991435 5043505 := bstep (se 2 (by rfl) ⟨1891314, by rfl⟩ : syracuseStep 5043505 = 3782629) B3782629
theorem B6724673 : Blo 1991435 6724673 := bstep (se 2 (by rfl) ⟨2521752, by rfl⟩ : syracuseStep 6724673 = 5043505) B5043505
theorem B4483115 : Blo 1991435 4483115 := bstep (se 1 (by rfl) ⟨3362336, by rfl⟩ : syracuseStep 4483115 = 6724673) B6724673
theorem B2988743 : Blo 1991435 2988743 := bstep (se 1 (by rfl) ⟨2241557, by rfl⟩ : syracuseStep 2988743 = 4483115) B4483115
theorem B1992495 : Blo 1991435 1992495 := bstep (se 1 (by rfl) ⟨1494371, by rfl⟩ : syracuseStep 1992495 = 2988743) B2988743
theorem B2988749 : Blo 1991435 2988749 := bbase (se 3 (by rfl) ⟨560390, by rfl⟩ : syracuseStep 2988749 = 1120781) (by norm_num)
theorem B1992499 : Blo 1991435 1992499 := bstep (se 1 (by rfl) ⟨1494374, by rfl⟩ : syracuseStep 1992499 = 2988749) B2988749
theorem B4483133 : Blo 1991435 4483133 := bbase (se 3 (by rfl) ⟨840587, by rfl⟩ : syracuseStep 4483133 = 1681175) (by norm_num)
theorem B2988755 : Blo 1991435 2988755 := bstep (se 1 (by rfl) ⟨2241566, by rfl⟩ : syracuseStep 2988755 = 4483133) B4483133
theorem B1992503 : Blo 1991435 1992503 := bstep (se 1 (by rfl) ⟨1494377, by rfl⟩ : syracuseStep 1992503 = 2988755) B2988755
theorem B3362357 : Blo 1991435 3362357 := bbase (se 5 (by rfl) ⟨157610, by rfl⟩ : syracuseStep 3362357 = 315221) (by norm_num)
theorem B2241571 : Blo 1991435 2241571 := bstep (se 1 (by rfl) ⟨1681178, by rfl⟩ : syracuseStep 2241571 = 3362357) B3362357
theorem B2988761 : Blo 1991435 2988761 := bstep (se 2 (by rfl) ⟨1120785, by rfl⟩ : syracuseStep 2988761 = 2241571) B2241571
theorem B1992507 : Blo 1991435 1992507 := bstep (se 1 (by rfl) ⟨1494380, by rfl⟩ : syracuseStep 1992507 = 2988761) B2988761
theorem B5673989 : Blo 1991435 5673989 := bbase (se 4 (by rfl) ⟨531936, by rfl⟩ : syracuseStep 5673989 = 1063873) (by norm_num)
theorem B15130637 : Blo 1991435 15130637 := bstep (se 3 (by rfl) ⟨2836994, by rfl⟩ : syracuseStep 15130637 = 5673989) B5673989
theorem B10087091 : Blo 1991435 10087091 := bstep (se 1 (by rfl) ⟨7565318, by rfl⟩ : syracuseStep 10087091 = 15130637) B15130637
theorem B6724727 : Blo 1991435 6724727 := bstep (se 1 (by rfl) ⟨5043545, by rfl⟩ : syracuseStep 6724727 = 10087091) B10087091
theorem B4483151 : Blo 1991435 4483151 := bstep (se 1 (by rfl) ⟨3362363, by rfl⟩ : syracuseStep 4483151 = 6724727) B6724727
theorem B2988767 : Blo 1991435 2988767 := bstep (se 1 (by rfl) ⟨2241575, by rfl⟩ : syracuseStep 2988767 = 4483151) B4483151
theorem B1992511 : Blo 1991435 1992511 := bstep (se 1 (by rfl) ⟨1494383, by rfl⟩ : syracuseStep 1992511 = 2988767) B2988767
theorem B2988773 : Blo 1991435 2988773 := bbase (se 4 (by rfl) ⟨280197, by rfl⟩ : syracuseStep 2988773 = 560395) (by norm_num)
theorem B1992515 : Blo 1991435 1992515 := bstep (se 1 (by rfl) ⟨1494386, by rfl⟩ : syracuseStep 1992515 = 2988773) B2988773
theorem B2393725 : Blo 1991435 2393725 := bbase (se 3 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 2393725 = 897647) (by norm_num)
theorem B3191633 : Blo 1991435 3191633 := bstep (se 2 (by rfl) ⟨1196862, by rfl⟩ : syracuseStep 3191633 = 2393725) B2393725
theorem B2127755 : Blo 1991435 2127755 := bstep (se 1 (by rfl) ⟨1595816, by rfl⟩ : syracuseStep 2127755 = 3191633) B3191633
theorem B5674013 : Blo 1991435 5674013 := bstep (se 3 (by rfl) ⟨1063877, by rfl⟩ : syracuseStep 5674013 = 2127755) B2127755
theorem B3782675 : Blo 1991435 3782675 := bstep (se 1 (by rfl) ⟨2837006, by rfl⟩ : syracuseStep 3782675 = 5674013) B5674013
theorem B2521783 : Blo 1991435 2521783 := bstep (se 1 (by rfl) ⟨1891337, by rfl⟩ : syracuseStep 2521783 = 3782675) B3782675
theorem B3362377 : Blo 1991435 3362377 := bstep (se 2 (by rfl) ⟨1260891, by rfl⟩ : syracuseStep 3362377 = 2521783) B2521783
theorem B4483169 : Blo 1991435 4483169 := bstep (se 2 (by rfl) ⟨1681188, by rfl⟩ : syracuseStep 4483169 = 3362377) B3362377
theorem B2988779 : Blo 1991435 2988779 := bstep (se 1 (by rfl) ⟨2241584, by rfl⟩ : syracuseStep 2988779 = 4483169) B4483169
theorem B1992519 : Blo 1991435 1992519 := bstep (se 1 (by rfl) ⟨1494389, by rfl⟩ : syracuseStep 1992519 = 2988779) B2988779
theorem B2241589 : Blo 1991435 2241589 := bbase (se 5 (by rfl) ⟨105074, by rfl⟩ : syracuseStep 2241589 = 210149) (by norm_num)
theorem B2988785 : Blo 1991435 2988785 := bstep (se 2 (by rfl) ⟨1120794, by rfl⟩ : syracuseStep 2988785 = 2241589) B2241589
theorem B1992523 : Blo 1991435 1992523 := bstep (se 1 (by rfl) ⟨1494392, by rfl⟩ : syracuseStep 1992523 = 2988785) B2988785
theorem B2521793 : Blo 1991435 2521793 := bbase (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) (by norm_num)
theorem B6724781 : Blo 1991435 6724781 := bstep (se 3 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 6724781 = 2521793) B2521793
theorem B4483187 : Blo 1991435 4483187 := bstep (se 1 (by rfl) ⟨3362390, by rfl⟩ : syracuseStep 4483187 = 6724781) B6724781
theorem B2988791 : Blo 1991435 2988791 := bstep (se 1 (by rfl) ⟨2241593, by rfl⟩ : syracuseStep 2988791 = 4483187) B4483187
theorem B1992527 : Blo 1991435 1992527 := bstep (se 1 (by rfl) ⟨1494395, by rfl⟩ : syracuseStep 1992527 = 2988791) B2988791
theorem B2988797 : Blo 1991435 2988797 := bbase (se 3 (by rfl) ⟨560399, by rfl⟩ : syracuseStep 2988797 = 1120799) (by norm_num)
theorem B1992531 : Blo 1991435 1992531 := bstep (se 1 (by rfl) ⟨1494398, by rfl⟩ : syracuseStep 1992531 = 2988797) B2988797
theorem B4483205 : Blo 1991435 4483205 := bbase (se 4 (by rfl) ⟨420300, by rfl⟩ : syracuseStep 4483205 = 840601) (by norm_num)
theorem B2988803 : Blo 1991435 2988803 := bstep (se 1 (by rfl) ⟨2241602, by rfl⟩ : syracuseStep 2988803 = 4483205) B4483205
theorem B1992535 : Blo 1991435 1992535 := bstep (se 1 (by rfl) ⟨1494401, by rfl⟩ : syracuseStep 1992535 = 2988803) B2988803
theorem B2393749 : Blo 1991435 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B3191665 : Blo 1991435 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B4255553 : Blo 1991435 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B2837035 : Blo 1991435 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B3782713 : Blo 1991435 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B5043617 : Blo 1991435 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B3362411 : Blo 1991435 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B2241607 : Blo 1991435 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2988809 : Blo 1991435 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B1992539 : Blo 1991435 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B10087253 : Blo 1991435 10087253 := bbase (se 9 (by rfl) ⟨29552, by rfl⟩ : syracuseStep 10087253 = 59105) (by norm_num)
theorem B6724835 : Blo 1991435 6724835 := bstep (se 1 (by rfl) ⟨5043626, by rfl⟩ : syracuseStep 6724835 = 10087253) B10087253
theorem B4483223 : Blo 1991435 4483223 := bstep (se 1 (by rfl) ⟨3362417, by rfl⟩ : syracuseStep 4483223 = 6724835) B6724835
theorem B2988815 : Blo 1991435 2988815 := bstep (se 1 (by rfl) ⟨2241611, by rfl⟩ : syracuseStep 2988815 = 4483223) B4483223
theorem B1992543 : Blo 1991435 1992543 := bstep (se 1 (by rfl) ⟨1494407, by rfl⟩ : syracuseStep 1992543 = 2988815) B2988815
theorem B2988821 : Blo 1991435 2988821 := bbase (se 6 (by rfl) ⟨70050, by rfl⟩ : syracuseStep 2988821 = 140101) (by norm_num)
theorem B1992547 : Blo 1991435 1992547 := bstep (se 1 (by rfl) ⟨1494410, by rfl⟩ : syracuseStep 1992547 = 2988821) B2988821
theorem B2334629 : Blo 1991435 2334629 := bbase (se 4 (by rfl) ⟨218871, by rfl⟩ : syracuseStep 2334629 = 437743) (by norm_num)
theorem B6225677 : Blo 1991435 6225677 := bstep (se 3 (by rfl) ⟨1167314, by rfl⟩ : syracuseStep 6225677 = 2334629) B2334629
theorem B4150451 : Blo 1991435 4150451 := bstep (se 1 (by rfl) ⟨3112838, by rfl⟩ : syracuseStep 4150451 = 6225677) B6225677
theorem B2766967 : Blo 1991435 2766967 := bstep (se 1 (by rfl) ⟨2075225, by rfl⟩ : syracuseStep 2766967 = 4150451) B4150451
theorem B14757157 : Blo 1991435 14757157 := bstep (se 4 (by rfl) ⟨1383483, by rfl⟩ : syracuseStep 14757157 = 2766967) B2766967
theorem B19676209 : Blo 1991435 19676209 := bstep (se 2 (by rfl) ⟨7378578, by rfl⟩ : syracuseStep 19676209 = 14757157) B14757157
theorem B26234945 : Blo 1991435 26234945 := bstep (se 2 (by rfl) ⟨9838104, by rfl⟩ : syracuseStep 26234945 = 19676209) B19676209
theorem B17489963 : Blo 1991435 17489963 := bstep (se 1 (by rfl) ⟨13117472, by rfl⟩ : syracuseStep 17489963 = 26234945) B26234945
theorem B46639901 : Blo 1991435 46639901 := bstep (se 3 (by rfl) ⟨8744981, by rfl⟩ : syracuseStep 46639901 = 17489963) B17489963
theorem B31093267 : Blo 1991435 31093267 := bstep (se 1 (by rfl) ⟨23319950, by rfl⟩ : syracuseStep 31093267 = 46639901) B46639901
theorem B41457689 : Blo 1991435 41457689 := bstep (se 2 (by rfl) ⟨15546633, by rfl⟩ : syracuseStep 41457689 = 31093267) B31093267
theorem B27638459 : Blo 1991435 27638459 := bstep (se 1 (by rfl) ⟨20728844, by rfl⟩ : syracuseStep 27638459 = 41457689) B41457689
theorem B18425639 : Blo 1991435 18425639 := bstep (se 1 (by rfl) ⟨13819229, by rfl⟩ : syracuseStep 18425639 = 27638459) B27638459
theorem B12283759 : Blo 1991435 12283759 := bstep (se 1 (by rfl) ⟨9212819, by rfl⟩ : syracuseStep 12283759 = 18425639) B18425639
theorem B16378345 : Blo 1991435 16378345 := bstep (se 2 (by rfl) ⟨6141879, by rfl⟩ : syracuseStep 16378345 = 12283759) B12283759
theorem B87351173 : Blo 1991435 87351173 := bstep (se 4 (by rfl) ⟨8189172, by rfl⟩ : syracuseStep 87351173 = 16378345) B16378345
theorem B58234115 : Blo 1991435 58234115 := bstep (se 1 (by rfl) ⟨43675586, by rfl⟩ : syracuseStep 58234115 = 87351173) B87351173
theorem B38822743 : Blo 1991435 38822743 := bstep (se 1 (by rfl) ⟨29117057, by rfl⟩ : syracuseStep 38822743 = 58234115) B58234115
theorem B207054629 : Blo 1991435 207054629 := bstep (se 4 (by rfl) ⟨19411371, by rfl⟩ : syracuseStep 207054629 = 38822743) B38822743
theorem B138036419 : Blo 1991435 138036419 := bstep (se 1 (by rfl) ⟨103527314, by rfl⟩ : syracuseStep 138036419 = 207054629) B207054629
theorem B92024279 : Blo 1991435 92024279 := bstep (se 1 (by rfl) ⟨69018209, by rfl⟩ : syracuseStep 92024279 = 138036419) B138036419
theorem B61349519 : Blo 1991435 61349519 := bstep (se 1 (by rfl) ⟨46012139, by rfl⟩ : syracuseStep 61349519 = 92024279) B92024279
theorem B163598717 : Blo 1991435 163598717 := bstep (se 3 (by rfl) ⟨30674759, by rfl⟩ : syracuseStep 163598717 = 61349519) B61349519
theorem B109065811 : Blo 1991435 109065811 := bstep (se 1 (by rfl) ⟨81799358, by rfl⟩ : syracuseStep 109065811 = 163598717) B163598717
theorem B145421081 : Blo 1991435 145421081 := bstep (se 2 (by rfl) ⟨54532905, by rfl⟩ : syracuseStep 145421081 = 109065811) B109065811
theorem B96947387 : Blo 1991435 96947387 := bstep (se 1 (by rfl) ⟨72710540, by rfl⟩ : syracuseStep 96947387 = 145421081) B145421081
theorem B64631591 : Blo 1991435 64631591 := bstep (se 1 (by rfl) ⟨48473693, by rfl⟩ : syracuseStep 64631591 = 96947387) B96947387
theorem B43087727 : Blo 1991435 43087727 := bstep (se 1 (by rfl) ⟨32315795, by rfl⟩ : syracuseStep 43087727 = 64631591) B64631591
theorem B28725151 : Blo 1991435 28725151 := bstep (se 1 (by rfl) ⟨21543863, by rfl⟩ : syracuseStep 28725151 = 43087727) B43087727
theorem B38300201 : Blo 1991435 38300201 := bstep (se 2 (by rfl) ⟨14362575, by rfl⟩ : syracuseStep 38300201 = 28725151) B28725151
theorem B25533467 : Blo 1991435 25533467 := bstep (se 1 (by rfl) ⟨19150100, by rfl⟩ : syracuseStep 25533467 = 38300201) B38300201
theorem B17022311 : Blo 1991435 17022311 := bstep (se 1 (by rfl) ⟨12766733, by rfl⟩ : syracuseStep 17022311 = 25533467) B25533467
theorem B11348207 : Blo 1991435 11348207 := bstep (se 1 (by rfl) ⟨8511155, by rfl⟩ : syracuseStep 11348207 = 17022311) B17022311
theorem B7565471 : Blo 1991435 7565471 := bstep (se 1 (by rfl) ⟨5674103, by rfl⟩ : syracuseStep 7565471 = 11348207) B11348207
theorem B5043647 : Blo 1991435 5043647 := bstep (se 1 (by rfl) ⟨3782735, by rfl⟩ : syracuseStep 5043647 = 7565471) B7565471
theorem B3362431 : Blo 1991435 3362431 := bstep (se 1 (by rfl) ⟨2521823, by rfl⟩ : syracuseStep 3362431 = 5043647) B5043647
theorem B4483241 : Blo 1991435 4483241 := bstep (se 2 (by rfl) ⟨1681215, by rfl⟩ : syracuseStep 4483241 = 3362431) B3362431
theorem B2988827 : Blo 1991435 2988827 := bstep (se 1 (by rfl) ⟨2241620, by rfl⟩ : syracuseStep 2988827 = 4483241) B4483241
theorem B1992551 : Blo 1991435 1992551 := bstep (se 1 (by rfl) ⟨1494413, by rfl⟩ : syracuseStep 1992551 = 2988827) B2988827
theorem B2241625 : Blo 1991435 2241625 := bbase (se 2 (by rfl) ⟨840609, by rfl⟩ : syracuseStep 2241625 = 1681219) (by norm_num)
theorem B2988833 : Blo 1991435 2988833 := bstep (se 2 (by rfl) ⟨1120812, by rfl⟩ : syracuseStep 2988833 = 2241625) B2241625
theorem B1992555 : Blo 1991435 1992555 := bstep (se 1 (by rfl) ⟨1494416, by rfl⟩ : syracuseStep 1992555 = 2988833) B2988833
theorem B5385989 : Blo 1991435 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B3590659 : Blo 1991435 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B4787545 : Blo 1991435 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B6383393 : Blo 1991435 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B4255595 : Blo 1991435 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B2837063 : Blo 1991435 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B7565501 : Blo 1991435 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B5043667 : Blo 1991435 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B6724889 : Blo 1991435 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B4483259 : Blo 1991435 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B2988839 : Blo 1991435 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B1992559 : Blo 1991435 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B2988845 : Blo 1991435 2988845 := bbase (se 3 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 2988845 = 1120817) (by norm_num)
theorem B1992563 : Blo 1991435 1992563 := bstep (se 1 (by rfl) ⟨1494422, by rfl⟩ : syracuseStep 1992563 = 2988845) B2988845
theorem B4483277 : Blo 1991435 4483277 := bbase (se 3 (by rfl) ⟨840614, by rfl⟩ : syracuseStep 4483277 = 1681229) (by norm_num)
theorem B2988851 : Blo 1991435 2988851 := bstep (se 1 (by rfl) ⟨2241638, by rfl⟩ : syracuseStep 2988851 = 4483277) B4483277
theorem B1992567 : Blo 1991435 1992567 := bstep (se 1 (by rfl) ⟨1494425, by rfl⟩ : syracuseStep 1992567 = 2988851) B2988851
theorem B2521849 : Blo 1991435 2521849 := bbase (se 2 (by rfl) ⟨945693, by rfl⟩ : syracuseStep 2521849 = 1891387) (by norm_num)
theorem B3362465 : Blo 1991435 3362465 := bstep (se 2 (by rfl) ⟨1260924, by rfl⟩ : syracuseStep 3362465 = 2521849) B2521849
theorem B2241643 : Blo 1991435 2241643 := bstep (se 1 (by rfl) ⟨1681232, by rfl⟩ : syracuseStep 2241643 = 3362465) B3362465
theorem B2988857 : Blo 1991435 2988857 := bstep (se 2 (by rfl) ⟨1120821, by rfl⟩ : syracuseStep 2988857 = 2241643) B2241643
theorem B1992571 : Blo 1991435 1992571 := bstep (se 1 (by rfl) ⟨1494428, by rfl⟩ : syracuseStep 1992571 = 2988857) B2988857
theorem B10225045 : Blo 1991435 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B13633393 : Blo 1991435 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B18177857 : Blo 1991435 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B12118571 : Blo 1991435 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B8079047 : Blo 1991435 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B5386031 : Blo 1991435 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B3590687 : Blo 1991435 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B9575165 : Blo 1991435 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B6383443 : Blo 1991435 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B8511257 : Blo 1991435 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B22696685 : Blo 1991435 22696685 := bstep (se 3 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 22696685 = 8511257) B8511257
theorem B15131123 : Blo 1991435 15131123 := bstep (se 1 (by rfl) ⟨11348342, by rfl⟩ : syracuseStep 15131123 = 22696685) B22696685
theorem B10087415 : Blo 1991435 10087415 := bstep (se 1 (by rfl) ⟨7565561, by rfl⟩ : syracuseStep 10087415 = 15131123) B15131123
theorem B6724943 : Blo 1991435 6724943 := bstep (se 1 (by rfl) ⟨5043707, by rfl⟩ : syracuseStep 6724943 = 10087415) B10087415
theorem B4483295 : Blo 1991435 4483295 := bstep (se 1 (by rfl) ⟨3362471, by rfl⟩ : syracuseStep 4483295 = 6724943) B6724943
theorem B2988863 : Blo 1991435 2988863 := bstep (se 1 (by rfl) ⟨2241647, by rfl⟩ : syracuseStep 2988863 = 4483295) B4483295
theorem B1992575 : Blo 1991435 1992575 := bstep (se 1 (by rfl) ⟨1494431, by rfl⟩ : syracuseStep 1992575 = 2988863) B2988863
theorem B2988869 : Blo 1991435 2988869 := bbase (se 4 (by rfl) ⟨280206, by rfl⟩ : syracuseStep 2988869 = 560413) (by norm_num)
theorem B1992579 : Blo 1991435 1992579 := bstep (se 1 (by rfl) ⟨1494434, by rfl⟩ : syracuseStep 1992579 = 2988869) B2988869
theorem B3362485 : Blo 1991435 3362485 := bbase (se 5 (by rfl) ⟨157616, by rfl⟩ : syracuseStep 3362485 = 315233) (by norm_num)
theorem B4483313 : Blo 1991435 4483313 := bstep (se 2 (by rfl) ⟨1681242, by rfl⟩ : syracuseStep 4483313 = 3362485) B3362485
theorem B2988875 : Blo 1991435 2988875 := bstep (se 1 (by rfl) ⟨2241656, by rfl⟩ : syracuseStep 2988875 = 4483313) B4483313
theorem B1992583 : Blo 1991435 1992583 := bstep (se 1 (by rfl) ⟨1494437, by rfl⟩ : syracuseStep 1992583 = 2988875) B2988875
theorem B2241661 : Blo 1991435 2241661 := bbase (se 3 (by rfl) ⟨420311, by rfl⟩ : syracuseStep 2241661 = 840623) (by norm_num)
theorem B2988881 : Blo 1991435 2988881 := bstep (se 2 (by rfl) ⟨1120830, by rfl⟩ : syracuseStep 2988881 = 2241661) B2241661
theorem B1992587 : Blo 1991435 1992587 := bstep (se 1 (by rfl) ⟨1494440, by rfl⟩ : syracuseStep 1992587 = 2988881) B2988881
theorem B6724997 : Blo 1991435 6724997 := bbase (se 4 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 6724997 = 1260937) (by norm_num)
theorem B4483331 : Blo 1991435 4483331 := bstep (se 1 (by rfl) ⟨3362498, by rfl⟩ : syracuseStep 4483331 = 6724997) B6724997
theorem B2988887 : Blo 1991435 2988887 := bstep (se 1 (by rfl) ⟨2241665, by rfl⟩ : syracuseStep 2988887 = 4483331) B4483331
theorem B1992591 : Blo 1991435 1992591 := bstep (se 1 (by rfl) ⟨1494443, by rfl⟩ : syracuseStep 1992591 = 2988887) B2988887
theorem B2988893 : Blo 1991435 2988893 := bbase (se 3 (by rfl) ⟨560417, by rfl⟩ : syracuseStep 2988893 = 1120835) (by norm_num)
theorem B1992595 : Blo 1991435 1992595 := bstep (se 1 (by rfl) ⟨1494446, by rfl⟩ : syracuseStep 1992595 = 2988893) B2988893
theorem B4483349 : Blo 1991435 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B2988899 : Blo 1991435 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B1992599 : Blo 1991435 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B7565669 : Blo 1991435 7565669 := bbase (se 4 (by rfl) ⟨709281, by rfl⟩ : syracuseStep 7565669 = 1418563) (by norm_num)
theorem B5043779 : Blo 1991435 5043779 := bstep (se 1 (by rfl) ⟨3782834, by rfl⟩ : syracuseStep 5043779 = 7565669) B7565669
theorem B3362519 : Blo 1991435 3362519 := bstep (se 1 (by rfl) ⟨2521889, by rfl⟩ : syracuseStep 3362519 = 5043779) B5043779
theorem B2241679 : Blo 1991435 2241679 := bstep (se 1 (by rfl) ⟨1681259, by rfl⟩ : syracuseStep 2241679 = 3362519) B3362519
theorem B2988905 : Blo 1991435 2988905 := bstep (se 2 (by rfl) ⟨1120839, by rfl⟩ : syracuseStep 2988905 = 2241679) B2241679
theorem B1992603 : Blo 1991435 1992603 := bstep (se 1 (by rfl) ⟨1494452, by rfl⟩ : syracuseStep 1992603 = 2988905) B2988905
theorem B3191773 : Blo 1991435 3191773 := bbase (se 3 (by rfl) ⟨598457, by rfl⟩ : syracuseStep 3191773 = 1196915) (by norm_num)
theorem B4255697 : Blo 1991435 4255697 := bstep (se 2 (by rfl) ⟨1595886, by rfl⟩ : syracuseStep 4255697 = 3191773) B3191773
theorem B11348525 : Blo 1991435 11348525 := bstep (se 3 (by rfl) ⟨2127848, by rfl⟩ : syracuseStep 11348525 = 4255697) B4255697
theorem B7565683 : Blo 1991435 7565683 := bstep (se 1 (by rfl) ⟨5674262, by rfl⟩ : syracuseStep 7565683 = 11348525) B11348525
theorem B10087577 : Blo 1991435 10087577 := bstep (se 2 (by rfl) ⟨3782841, by rfl⟩ : syracuseStep 10087577 = 7565683) B7565683
theorem B6725051 : Blo 1991435 6725051 := bstep (se 1 (by rfl) ⟨5043788, by rfl⟩ : syracuseStep 6725051 = 10087577) B10087577
theorem B4483367 : Blo 1991435 4483367 := bstep (se 1 (by rfl) ⟨3362525, by rfl⟩ : syracuseStep 4483367 = 6725051) B6725051
theorem B2988911 : Blo 1991435 2988911 := bstep (se 1 (by rfl) ⟨2241683, by rfl⟩ : syracuseStep 2988911 = 4483367) B4483367
theorem B1992607 : Blo 1991435 1992607 := bstep (se 1 (by rfl) ⟨1494455, by rfl⟩ : syracuseStep 1992607 = 2988911) B2988911
theorem B2988917 : Blo 1991435 2988917 := bbase (se 5 (by rfl) ⟨140105, by rfl⟩ : syracuseStep 2988917 = 280211) (by norm_num)
theorem B1992611 : Blo 1991435 1992611 := bstep (se 1 (by rfl) ⟨1494458, by rfl⟩ : syracuseStep 1992611 = 2988917) B2988917
theorem B6383573 : Blo 1991435 6383573 := bbase (se 7 (by rfl) ⟨74807, by rfl⟩ : syracuseStep 6383573 = 149615) (by norm_num)
theorem B4255715 : Blo 1991435 4255715 := bstep (se 1 (by rfl) ⟨3191786, by rfl⟩ : syracuseStep 4255715 = 6383573) B6383573
theorem B2837143 : Blo 1991435 2837143 := bstep (se 1 (by rfl) ⟨2127857, by rfl⟩ : syracuseStep 2837143 = 4255715) B4255715
theorem B3782857 : Blo 1991435 3782857 := bstep (se 2 (by rfl) ⟨1418571, by rfl⟩ : syracuseStep 3782857 = 2837143) B2837143
theorem B5043809 : Blo 1991435 5043809 := bstep (se 2 (by rfl) ⟨1891428, by rfl⟩ : syracuseStep 5043809 = 3782857) B3782857
theorem B3362539 : Blo 1991435 3362539 := bstep (se 1 (by rfl) ⟨2521904, by rfl⟩ : syracuseStep 3362539 = 5043809) B5043809
theorem B4483385 : Blo 1991435 4483385 := bstep (se 2 (by rfl) ⟨1681269, by rfl⟩ : syracuseStep 4483385 = 3362539) B3362539
theorem B2988923 : Blo 1991435 2988923 := bstep (se 1 (by rfl) ⟨2241692, by rfl⟩ : syracuseStep 2988923 = 4483385) B4483385
theorem B1992615 : Blo 1991435 1992615 := bstep (se 1 (by rfl) ⟨1494461, by rfl⟩ : syracuseStep 1992615 = 2988923) B2988923
theorem B2241697 : Blo 1991435 2241697 := bbase (se 2 (by rfl) ⟨840636, by rfl⟩ : syracuseStep 2241697 = 1681273) (by norm_num)
theorem B2988929 : Blo 1991435 2988929 := bstep (se 2 (by rfl) ⟨1120848, by rfl⟩ : syracuseStep 2988929 = 2241697) B2241697
theorem B1992619 : Blo 1991435 1992619 := bstep (se 1 (by rfl) ⟨1494464, by rfl⟩ : syracuseStep 1992619 = 2988929) B2988929
theorem B5043829 : Blo 1991435 5043829 := bbase (se 5 (by rfl) ⟨236429, by rfl⟩ : syracuseStep 5043829 = 472859) (by norm_num)
theorem B6725105 : Blo 1991435 6725105 := bstep (se 2 (by rfl) ⟨2521914, by rfl⟩ : syracuseStep 6725105 = 5043829) B5043829
theorem B4483403 : Blo 1991435 4483403 := bstep (se 1 (by rfl) ⟨3362552, by rfl⟩ : syracuseStep 4483403 = 6725105) B6725105
theorem B2988935 : Blo 1991435 2988935 := bstep (se 1 (by rfl) ⟨2241701, by rfl⟩ : syracuseStep 2988935 = 4483403) B4483403
theorem B1992623 : Blo 1991435 1992623 := bstep (se 1 (by rfl) ⟨1494467, by rfl⟩ : syracuseStep 1992623 = 2988935) B2988935
theorem B2988941 : Blo 1991435 2988941 := bbase (se 3 (by rfl) ⟨560426, by rfl⟩ : syracuseStep 2988941 = 1120853) (by norm_num)
theorem B1992627 : Blo 1991435 1992627 := bstep (se 1 (by rfl) ⟨1494470, by rfl⟩ : syracuseStep 1992627 = 2988941) B2988941
theorem B4483421 : Blo 1991435 4483421 := bbase (se 3 (by rfl) ⟨840641, by rfl⟩ : syracuseStep 4483421 = 1681283) (by norm_num)
theorem B2988947 : Blo 1991435 2988947 := bstep (se 1 (by rfl) ⟨2241710, by rfl⟩ : syracuseStep 2988947 = 4483421) B4483421
theorem B1992631 : Blo 1991435 1992631 := bstep (se 1 (by rfl) ⟨1494473, by rfl⟩ : syracuseStep 1992631 = 2988947) B2988947
theorem B3362573 : Blo 1991435 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B2241715 : Blo 1991435 2241715 := bstep (se 1 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 2241715 = 3362573) B3362573
theorem B2988953 : Blo 1991435 2988953 := bstep (se 2 (by rfl) ⟨1120857, by rfl⟩ : syracuseStep 2988953 = 2241715) B2241715
theorem B1992635 : Blo 1991435 1992635 := bstep (se 1 (by rfl) ⟨1494476, by rfl⟩ : syracuseStep 1992635 = 2988953) B2988953
theorem B17023061 : Blo 1991435 17023061 := bbase (se 8 (by rfl) ⟨99744, by rfl⟩ : syracuseStep 17023061 = 199489) (by norm_num)
theorem B11348707 : Blo 1991435 11348707 := bstep (se 1 (by rfl) ⟨8511530, by rfl⟩ : syracuseStep 11348707 = 17023061) B17023061
theorem B15131609 : Blo 1991435 15131609 := bstep (se 2 (by rfl) ⟨5674353, by rfl⟩ : syracuseStep 15131609 = 11348707) B11348707
theorem B10087739 : Blo 1991435 10087739 := bstep (se 1 (by rfl) ⟨7565804, by rfl⟩ : syracuseStep 10087739 = 15131609) B15131609
theorem B6725159 : Blo 1991435 6725159 := bstep (se 1 (by rfl) ⟨5043869, by rfl⟩ : syracuseStep 6725159 = 10087739) B10087739
theorem B4483439 : Blo 1991435 4483439 := bstep (se 1 (by rfl) ⟨3362579, by rfl⟩ : syracuseStep 4483439 = 6725159) B6725159
theorem B2988959 : Blo 1991435 2988959 := bstep (se 1 (by rfl) ⟨2241719, by rfl⟩ : syracuseStep 2988959 = 4483439) B4483439
theorem B1992639 : Blo 1991435 1992639 := bstep (se 1 (by rfl) ⟨1494479, by rfl⟩ : syracuseStep 1992639 = 2988959) B2988959
theorem B2988965 : Blo 1991435 2988965 := bbase (se 4 (by rfl) ⟨280215, by rfl⟩ : syracuseStep 2988965 = 560431) (by norm_num)
theorem B1992643 : Blo 1991435 1992643 := bstep (se 1 (by rfl) ⟨1494482, by rfl⟩ : syracuseStep 1992643 = 2988965) B2988965
theorem B2521945 : Blo 1991435 2521945 := bbase (se 2 (by rfl) ⟨945729, by rfl⟩ : syracuseStep 2521945 = 1891459) (by norm_num)
theorem B3362593 : Blo 1991435 3362593 := bstep (se 2 (by rfl) ⟨1260972, by rfl⟩ : syracuseStep 3362593 = 2521945) B2521945
theorem B4483457 : Blo 1991435 4483457 := bstep (se 2 (by rfl) ⟨1681296, by rfl⟩ : syracuseStep 4483457 = 3362593) B3362593
theorem B2988971 : Blo 1991435 2988971 := bstep (se 1 (by rfl) ⟨2241728, by rfl⟩ : syracuseStep 2988971 = 4483457) B4483457
theorem B1992647 : Blo 1991435 1992647 := bstep (se 1 (by rfl) ⟨1494485, by rfl⟩ : syracuseStep 1992647 = 2988971) B2988971
theorem B2241733 : Blo 1991435 2241733 := bbase (se 4 (by rfl) ⟨210162, by rfl⟩ : syracuseStep 2241733 = 420325) (by norm_num)
theorem B2988977 : Blo 1991435 2988977 := bstep (se 2 (by rfl) ⟨1120866, by rfl⟩ : syracuseStep 2988977 = 2241733) B2241733
theorem B1992651 : Blo 1991435 1992651 := bstep (se 1 (by rfl) ⟨1494488, by rfl⟩ : syracuseStep 1992651 = 2988977) B2988977
theorem B3782933 : Blo 1991435 3782933 := bbase (se 6 (by rfl) ⟨88662, by rfl⟩ : syracuseStep 3782933 = 177325) (by norm_num)
theorem B2521955 : Blo 1991435 2521955 := bstep (se 1 (by rfl) ⟨1891466, by rfl⟩ : syracuseStep 2521955 = 3782933) B3782933
theorem B6725213 : Blo 1991435 6725213 := bstep (se 3 (by rfl) ⟨1260977, by rfl⟩ : syracuseStep 6725213 = 2521955) B2521955
theorem B4483475 : Blo 1991435 4483475 := bstep (se 1 (by rfl) ⟨3362606, by rfl⟩ : syracuseStep 4483475 = 6725213) B6725213
theorem B2988983 : Blo 1991435 2988983 := bstep (se 1 (by rfl) ⟨2241737, by rfl⟩ : syracuseStep 2988983 = 4483475) B4483475
theorem B1992655 : Blo 1991435 1992655 := bstep (se 1 (by rfl) ⟨1494491, by rfl⟩ : syracuseStep 1992655 = 2988983) B2988983
theorem B2988989 : Blo 1991435 2988989 := bbase (se 3 (by rfl) ⟨560435, by rfl⟩ : syracuseStep 2988989 = 1120871) (by norm_num)
theorem B1992659 : Blo 1991435 1992659 := bstep (se 1 (by rfl) ⟨1494494, by rfl⟩ : syracuseStep 1992659 = 2988989) B2988989
theorem B4483493 : Blo 1991435 4483493 := bbase (se 4 (by rfl) ⟨420327, by rfl⟩ : syracuseStep 4483493 = 840655) (by norm_num)
theorem B2988995 : Blo 1991435 2988995 := bstep (se 1 (by rfl) ⟨2241746, by rfl⟩ : syracuseStep 2988995 = 4483493) B4483493
theorem B1992663 : Blo 1991435 1992663 := bstep (se 1 (by rfl) ⟨1494497, by rfl⟩ : syracuseStep 1992663 = 2988995) B2988995
theorem B5043941 : Blo 1991435 5043941 := bbase (se 4 (by rfl) ⟨472869, by rfl⟩ : syracuseStep 5043941 = 945739) (by norm_num)
theorem B3362627 : Blo 1991435 3362627 := bstep (se 1 (by rfl) ⟨2521970, by rfl⟩ : syracuseStep 3362627 = 5043941) B5043941
theorem B2241751 : Blo 1991435 2241751 := bstep (se 1 (by rfl) ⟨1681313, by rfl⟩ : syracuseStep 2241751 = 3362627) B3362627
theorem B2989001 : Blo 1991435 2989001 := bstep (se 2 (by rfl) ⟨1120875, by rfl⟩ : syracuseStep 2989001 = 2241751) B2241751
theorem B1992667 : Blo 1991435 1992667 := bstep (se 1 (by rfl) ⟨1494500, by rfl⟩ : syracuseStep 1992667 = 2989001) B2989001
theorem B2127917 : Blo 1991435 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B5674445 : Blo 1991435 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B3782963 : Blo 1991435 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B10087901 : Blo 1991435 10087901 := bstep (se 3 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 10087901 = 3782963) B3782963
theorem B6725267 : Blo 1991435 6725267 := bstep (se 1 (by rfl) ⟨5043950, by rfl⟩ : syracuseStep 6725267 = 10087901) B10087901
theorem B4483511 : Blo 1991435 4483511 := bstep (se 1 (by rfl) ⟨3362633, by rfl⟩ : syracuseStep 4483511 = 6725267) B6725267
theorem B2989007 : Blo 1991435 2989007 := bstep (se 1 (by rfl) ⟨2241755, by rfl⟩ : syracuseStep 2989007 = 4483511) B4483511
theorem B1992671 : Blo 1991435 1992671 := bstep (se 1 (by rfl) ⟨1494503, by rfl⟩ : syracuseStep 1992671 = 2989007) B2989007
theorem B2989013 : Blo 1991435 2989013 := bbase (se 7 (by rfl) ⟨35027, by rfl⟩ : syracuseStep 2989013 = 70055) (by norm_num)
theorem B1992675 : Blo 1991435 1992675 := bstep (se 1 (by rfl) ⟨1494506, by rfl⟩ : syracuseStep 1992675 = 2989013) B2989013
theorem B7565957 : Blo 1991435 7565957 := bbase (se 4 (by rfl) ⟨709308, by rfl⟩ : syracuseStep 7565957 = 1418617) (by norm_num)
theorem B5043971 : Blo 1991435 5043971 := bstep (se 1 (by rfl) ⟨3782978, by rfl⟩ : syracuseStep 5043971 = 7565957) B7565957
theorem B3362647 : Blo 1991435 3362647 := bstep (se 1 (by rfl) ⟨2521985, by rfl⟩ : syracuseStep 3362647 = 5043971) B5043971
theorem B4483529 : Blo 1991435 4483529 := bstep (se 2 (by rfl) ⟨1681323, by rfl⟩ : syracuseStep 4483529 = 3362647) B3362647
theorem B2989019 : Blo 1991435 2989019 := bstep (se 1 (by rfl) ⟨2241764, by rfl⟩ : syracuseStep 2989019 = 4483529) B4483529
theorem B1992679 : Blo 1991435 1992679 := bstep (se 1 (by rfl) ⟨1494509, by rfl⟩ : syracuseStep 1992679 = 2989019) B2989019
theorem B2241769 : Blo 1991435 2241769 := bbase (se 2 (by rfl) ⟨840663, by rfl⟩ : syracuseStep 2241769 = 1681327) (by norm_num)
theorem B2989025 : Blo 1991435 2989025 := bstep (se 2 (by rfl) ⟨1120884, by rfl⟩ : syracuseStep 2989025 = 2241769) B2241769
theorem B1992683 : Blo 1991435 1992683 := bstep (se 1 (by rfl) ⟨1494512, by rfl⟩ : syracuseStep 1992683 = 2989025) B2989025
theorem B11348981 : Blo 1991435 11348981 := bbase (se 5 (by rfl) ⟨531983, by rfl⟩ : syracuseStep 11348981 = 1063967) (by norm_num)
theorem B7565987 : Blo 1991435 7565987 := bstep (se 1 (by rfl) ⟨5674490, by rfl⟩ : syracuseStep 7565987 = 11348981) B11348981
theorem B5043991 : Blo 1991435 5043991 := bstep (se 1 (by rfl) ⟨3782993, by rfl⟩ : syracuseStep 5043991 = 7565987) B7565987
theorem B6725321 : Blo 1991435 6725321 := bstep (se 2 (by rfl) ⟨2521995, by rfl⟩ : syracuseStep 6725321 = 5043991) B5043991
theorem B4483547 : Blo 1991435 4483547 := bstep (se 1 (by rfl) ⟨3362660, by rfl⟩ : syracuseStep 4483547 = 6725321) B6725321
theorem B2989031 : Blo 1991435 2989031 := bstep (se 1 (by rfl) ⟨2241773, by rfl⟩ : syracuseStep 2989031 = 4483547) B4483547
theorem B1992687 : Blo 1991435 1992687 := bstep (se 1 (by rfl) ⟨1494515, by rfl⟩ : syracuseStep 1992687 = 2989031) B2989031
theorem B2989037 : Blo 1991435 2989037 := bbase (se 3 (by rfl) ⟨560444, by rfl⟩ : syracuseStep 2989037 = 1120889) (by norm_num)
theorem B1992691 : Blo 1991435 1992691 := bstep (se 1 (by rfl) ⟨1494518, by rfl⟩ : syracuseStep 1992691 = 2989037) B2989037
theorem B4483565 : Blo 1991435 4483565 := bbase (se 3 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 4483565 = 1681337) (by norm_num)
theorem B2989043 : Blo 1991435 2989043 := bstep (se 1 (by rfl) ⟨2241782, by rfl⟩ : syracuseStep 2989043 = 4483565) B4483565
theorem B1992695 : Blo 1991435 1992695 := bstep (se 1 (by rfl) ⟨1494521, by rfl⟩ : syracuseStep 1992695 = 2989043) B2989043
theorem B9575765 : Blo 1991435 9575765 := bbase (se 11 (by rfl) ⟨7013, by rfl⟩ : syracuseStep 9575765 = 14027) (by norm_num)
theorem B6383843 : Blo 1991435 6383843 := bstep (se 1 (by rfl) ⟨4787882, by rfl⟩ : syracuseStep 6383843 = 9575765) B9575765
theorem B4255895 : Blo 1991435 4255895 := bstep (se 1 (by rfl) ⟨3191921, by rfl⟩ : syracuseStep 4255895 = 6383843) B6383843
theorem B2837263 : Blo 1991435 2837263 := bstep (se 1 (by rfl) ⟨2127947, by rfl⟩ : syracuseStep 2837263 = 4255895) B4255895
theorem B3783017 : Blo 1991435 3783017 := bstep (se 2 (by rfl) ⟨1418631, by rfl⟩ : syracuseStep 3783017 = 2837263) B2837263
theorem B2522011 : Blo 1991435 2522011 := bstep (se 1 (by rfl) ⟨1891508, by rfl⟩ : syracuseStep 2522011 = 3783017) B3783017
theorem B3362681 : Blo 1991435 3362681 := bstep (se 2 (by rfl) ⟨1261005, by rfl⟩ : syracuseStep 3362681 = 2522011) B2522011
theorem B2241787 : Blo 1991435 2241787 := bstep (se 1 (by rfl) ⟨1681340, by rfl⟩ : syracuseStep 2241787 = 3362681) B3362681
theorem B2989049 : Blo 1991435 2989049 := bstep (se 2 (by rfl) ⟨1120893, by rfl⟩ : syracuseStep 2989049 = 2241787) B2241787
theorem B1992699 : Blo 1991435 1992699 := bstep (se 1 (by rfl) ⟨1494524, by rfl⟩ : syracuseStep 1992699 = 2989049) B2989049
theorem B20730421 : Blo 1991435 20730421 := bbase (se 5 (by rfl) ⟨971738, by rfl⟩ : syracuseStep 20730421 = 1943477) (by norm_num)
theorem B27640561 : Blo 1991435 27640561 := bstep (se 2 (by rfl) ⟨10365210, by rfl⟩ : syracuseStep 27640561 = 20730421) B20730421
theorem B36854081 : Blo 1991435 36854081 := bstep (se 2 (by rfl) ⟨13820280, by rfl⟩ : syracuseStep 36854081 = 27640561) B27640561
theorem B24569387 : Blo 1991435 24569387 := bstep (se 1 (by rfl) ⟨18427040, by rfl⟩ : syracuseStep 24569387 = 36854081) B36854081
theorem B1048293845 : Blo 1991435 1048293845 := bstep (se 7 (by rfl) ⟨12284693, by rfl⟩ : syracuseStep 1048293845 = 24569387) B24569387
theorem B698862563 : Blo 1991435 698862563 := bstep (se 1 (by rfl) ⟨524146922, by rfl⟩ : syracuseStep 698862563 = 1048293845) B1048293845
theorem B465908375 : Blo 1991435 465908375 := bstep (se 1 (by rfl) ⟨349431281, by rfl⟩ : syracuseStep 465908375 = 698862563) B698862563
theorem B310605583 : Blo 1991435 310605583 := bstep (se 1 (by rfl) ⟨232954187, by rfl⟩ : syracuseStep 310605583 = 465908375) B465908375
theorem B414140777 : Blo 1991435 414140777 := bstep (se 2 (by rfl) ⟨155302791, by rfl⟩ : syracuseStep 414140777 = 310605583) B310605583
theorem B276093851 : Blo 1991435 276093851 := bstep (se 1 (by rfl) ⟨207070388, by rfl⟩ : syracuseStep 276093851 = 414140777) B414140777
theorem B736250269 : Blo 1991435 736250269 := bstep (se 3 (by rfl) ⟨138046925, by rfl⟩ : syracuseStep 736250269 = 276093851) B276093851
theorem B981667025 : Blo 1991435 981667025 := bstep (se 2 (by rfl) ⟨368125134, by rfl⟩ : syracuseStep 981667025 = 736250269) B736250269
theorem B654444683 : Blo 1991435 654444683 := bstep (se 1 (by rfl) ⟨490833512, by rfl⟩ : syracuseStep 654444683 = 981667025) B981667025
theorem B436296455 : Blo 1991435 436296455 := bstep (se 1 (by rfl) ⟨327222341, by rfl⟩ : syracuseStep 436296455 = 654444683) B654444683
theorem B290864303 : Blo 1991435 290864303 := bstep (se 1 (by rfl) ⟨218148227, by rfl⟩ : syracuseStep 290864303 = 436296455) B436296455
theorem B193909535 : Blo 1991435 193909535 := bstep (se 1 (by rfl) ⟨145432151, by rfl⟩ : syracuseStep 193909535 = 290864303) B290864303
theorem B129273023 : Blo 1991435 129273023 := bstep (se 1 (by rfl) ⟨96954767, by rfl⟩ : syracuseStep 129273023 = 193909535) B193909535
theorem B86182015 : Blo 1991435 86182015 := bstep (se 1 (by rfl) ⟨64636511, by rfl⟩ : syracuseStep 86182015 = 129273023) B129273023
theorem B114909353 : Blo 1991435 114909353 := bstep (se 2 (by rfl) ⟨43091007, by rfl⟩ : syracuseStep 114909353 = 86182015) B86182015
theorem B76606235 : Blo 1991435 76606235 := bstep (se 1 (by rfl) ⟨57454676, by rfl⟩ : syracuseStep 76606235 = 114909353) B114909353
theorem B51070823 : Blo 1991435 51070823 := bstep (se 1 (by rfl) ⟨38303117, by rfl⟩ : syracuseStep 51070823 = 76606235) B76606235
theorem B34047215 : Blo 1991435 34047215 := bstep (se 1 (by rfl) ⟨25535411, by rfl⟩ : syracuseStep 34047215 = 51070823) B51070823
theorem B22698143 : Blo 1991435 22698143 := bstep (se 1 (by rfl) ⟨17023607, by rfl⟩ : syracuseStep 22698143 = 34047215) B34047215
theorem B15132095 : Blo 1991435 15132095 := bstep (se 1 (by rfl) ⟨11349071, by rfl⟩ : syracuseStep 15132095 = 22698143) B22698143
theorem B10088063 : Blo 1991435 10088063 := bstep (se 1 (by rfl) ⟨7566047, by rfl⟩ : syracuseStep 10088063 = 15132095) B15132095
theorem B6725375 : Blo 1991435 6725375 := bstep (se 1 (by rfl) ⟨5044031, by rfl⟩ : syracuseStep 6725375 = 10088063) B10088063
theorem B4483583 : Blo 1991435 4483583 := bstep (se 1 (by rfl) ⟨3362687, by rfl⟩ : syracuseStep 4483583 = 6725375) B6725375
theorem B2989055 : Blo 1991435 2989055 := bstep (se 1 (by rfl) ⟨2241791, by rfl⟩ : syracuseStep 2989055 = 4483583) B4483583
theorem B1992703 : Blo 1991435 1992703 := bstep (se 1 (by rfl) ⟨1494527, by rfl⟩ : syracuseStep 1992703 = 2989055) B2989055
theorem B2989061 : Blo 1991435 2989061 := bbase (se 4 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 2989061 = 560449) (by norm_num)
theorem B1992707 : Blo 1991435 1992707 := bstep (se 1 (by rfl) ⟨1494530, by rfl⟩ : syracuseStep 1992707 = 2989061) B2989061
theorem B3362701 : Blo 1991435 3362701 := bbase (se 3 (by rfl) ⟨630506, by rfl⟩ : syracuseStep 3362701 = 1261013) (by norm_num)
theorem B4483601 : Blo 1991435 4483601 := bstep (se 2 (by rfl) ⟨1681350, by rfl⟩ : syracuseStep 4483601 = 3362701) B3362701
theorem B2989067 : Blo 1991435 2989067 := bstep (se 1 (by rfl) ⟨2241800, by rfl⟩ : syracuseStep 2989067 = 4483601) B4483601
theorem B1992711 : Blo 1991435 1992711 := bstep (se 1 (by rfl) ⟨1494533, by rfl⟩ : syracuseStep 1992711 = 2989067) B2989067
theorem B2241805 : Blo 1991435 2241805 := bbase (se 3 (by rfl) ⟨420338, by rfl⟩ : syracuseStep 2241805 = 840677) (by norm_num)
theorem B2989073 : Blo 1991435 2989073 := bstep (se 2 (by rfl) ⟨1120902, by rfl⟩ : syracuseStep 2989073 = 2241805) B2241805
theorem B1992715 : Blo 1991435 1992715 := bstep (se 1 (by rfl) ⟨1494536, by rfl⟩ : syracuseStep 1992715 = 2989073) B2989073
theorem B6725429 : Blo 1991435 6725429 := bbase (se 5 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 6725429 = 630509) (by norm_num)
theorem B4483619 : Blo 1991435 4483619 := bstep (se 1 (by rfl) ⟨3362714, by rfl⟩ : syracuseStep 4483619 = 6725429) B6725429
theorem B2989079 : Blo 1991435 2989079 := bstep (se 1 (by rfl) ⟨2241809, by rfl⟩ : syracuseStep 2989079 = 4483619) B4483619
theorem B1992719 : Blo 1991435 1992719 := bstep (se 1 (by rfl) ⟨1494539, by rfl⟩ : syracuseStep 1992719 = 2989079) B2989079
theorem B2989085 : Blo 1991435 2989085 := bbase (se 3 (by rfl) ⟨560453, by rfl⟩ : syracuseStep 2989085 = 1120907) (by norm_num)
theorem B1992723 : Blo 1991435 1992723 := bstep (se 1 (by rfl) ⟨1494542, by rfl⟩ : syracuseStep 1992723 = 2989085) B2989085
theorem B4483637 : Blo 1991435 4483637 := bbase (se 5 (by rfl) ⟨210170, by rfl⟩ : syracuseStep 4483637 = 420341) (by norm_num)
theorem B2989091 : Blo 1991435 2989091 := bstep (se 1 (by rfl) ⟨2241818, by rfl⟩ : syracuseStep 2989091 = 4483637) B4483637
theorem B1992727 : Blo 1991435 1992727 := bstep (se 1 (by rfl) ⟨1494545, by rfl⟩ : syracuseStep 1992727 = 2989091) B2989091
theorem B8511925 : Blo 1991435 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B11349233 : Blo 1991435 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B7566155 : Blo 1991435 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B5044103 : Blo 1991435 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B3362735 : Blo 1991435 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B2241823 : Blo 1991435 2241823 := bstep (se 1 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 2241823 = 3362735) B3362735
theorem B2989097 : Blo 1991435 2989097 := bstep (se 2 (by rfl) ⟨1120911, by rfl⟩ : syracuseStep 2989097 = 2241823) B2241823
theorem B1992731 : Blo 1991435 1992731 := bstep (se 1 (by rfl) ⟨1494548, by rfl⟩ : syracuseStep 1992731 = 2989097) B2989097
theorem B8511941 : Blo 1991435 8511941 := bbase (se 4 (by rfl) ⟨797994, by rfl⟩ : syracuseStep 8511941 = 1595989) (by norm_num)
theorem B5674627 : Blo 1991435 5674627 := bstep (se 1 (by rfl) ⟨4255970, by rfl⟩ : syracuseStep 5674627 = 8511941) B8511941
theorem B7566169 : Blo 1991435 7566169 := bstep (se 2 (by rfl) ⟨2837313, by rfl⟩ : syracuseStep 7566169 = 5674627) B5674627
theorem B10088225 : Blo 1991435 10088225 := bstep (se 2 (by rfl) ⟨3783084, by rfl⟩ : syracuseStep 10088225 = 7566169) B7566169
theorem B6725483 : Blo 1991435 6725483 := bstep (se 1 (by rfl) ⟨5044112, by rfl⟩ : syracuseStep 6725483 = 10088225) B10088225
theorem B4483655 : Blo 1991435 4483655 := bstep (se 1 (by rfl) ⟨3362741, by rfl⟩ : syracuseStep 4483655 = 6725483) B6725483
theorem B2989103 : Blo 1991435 2989103 := bstep (se 1 (by rfl) ⟨2241827, by rfl⟩ : syracuseStep 2989103 = 4483655) B4483655
theorem B1992735 : Blo 1991435 1992735 := bstep (se 1 (by rfl) ⟨1494551, by rfl⟩ : syracuseStep 1992735 = 2989103) B2989103
theorem B2989109 : Blo 1991435 2989109 := bbase (se 5 (by rfl) ⟨140114, by rfl⟩ : syracuseStep 2989109 = 280229) (by norm_num)
theorem B1992739 : Blo 1991435 1992739 := bstep (se 1 (by rfl) ⟨1494554, by rfl⟩ : syracuseStep 1992739 = 2989109) B2989109
theorem B5044133 : Blo 1991435 5044133 := bbase (se 4 (by rfl) ⟨472887, by rfl⟩ : syracuseStep 5044133 = 945775) (by norm_num)
theorem B3362755 : Blo 1991435 3362755 := bstep (se 1 (by rfl) ⟨2522066, by rfl⟩ : syracuseStep 3362755 = 5044133) B5044133
theorem B4483673 : Blo 1991435 4483673 := bstep (se 2 (by rfl) ⟨1681377, by rfl⟩ : syracuseStep 4483673 = 3362755) B3362755
theorem B2989115 : Blo 1991435 2989115 := bstep (se 1 (by rfl) ⟨2241836, by rfl⟩ : syracuseStep 2989115 = 4483673) B4483673
theorem B1992743 : Blo 1991435 1992743 := bstep (se 1 (by rfl) ⟨1494557, by rfl⟩ : syracuseStep 1992743 = 2989115) B2989115
theorem B2241841 : Blo 1991435 2241841 := bbase (se 2 (by rfl) ⟨840690, by rfl⟩ : syracuseStep 2241841 = 1681381) (by norm_num)
theorem B2989121 : Blo 1991435 2989121 := bstep (se 2 (by rfl) ⟨1120920, by rfl⟩ : syracuseStep 2989121 = 2241841) B2241841
theorem B1992747 : Blo 1991435 1992747 := bstep (se 1 (by rfl) ⟨1494560, by rfl⟩ : syracuseStep 1992747 = 2989121) B2989121
theorem B4256005 : Blo 1991435 4256005 := bbase (se 4 (by rfl) ⟨399000, by rfl⟩ : syracuseStep 4256005 = 798001) (by norm_num)
theorem B5674673 : Blo 1991435 5674673 := bstep (se 2 (by rfl) ⟨2128002, by rfl⟩ : syracuseStep 5674673 = 4256005) B4256005
theorem B3783115 : Blo 1991435 3783115 := bstep (se 1 (by rfl) ⟨2837336, by rfl⟩ : syracuseStep 3783115 = 5674673) B5674673
theorem B5044153 : Blo 1991435 5044153 := bstep (se 2 (by rfl) ⟨1891557, by rfl⟩ : syracuseStep 5044153 = 3783115) B3783115
theorem B6725537 : Blo 1991435 6725537 := bstep (se 2 (by rfl) ⟨2522076, by rfl⟩ : syracuseStep 6725537 = 5044153) B5044153
theorem B4483691 : Blo 1991435 4483691 := bstep (se 1 (by rfl) ⟨3362768, by rfl⟩ : syracuseStep 4483691 = 6725537) B6725537
theorem B2989127 : Blo 1991435 2989127 := bstep (se 1 (by rfl) ⟨2241845, by rfl⟩ : syracuseStep 2989127 = 4483691) B4483691
theorem B1992751 : Blo 1991435 1992751 := bstep (se 1 (by rfl) ⟨1494563, by rfl⟩ : syracuseStep 1992751 = 2989127) B2989127
theorem B2989133 : Blo 1991435 2989133 := bbase (se 3 (by rfl) ⟨560462, by rfl⟩ : syracuseStep 2989133 = 1120925) (by norm_num)
theorem B1992755 : Blo 1991435 1992755 := bstep (se 1 (by rfl) ⟨1494566, by rfl⟩ : syracuseStep 1992755 = 2989133) B2989133
theorem B4483709 : Blo 1991435 4483709 := bbase (se 3 (by rfl) ⟨840695, by rfl⟩ : syracuseStep 4483709 = 1681391) (by norm_num)
theorem B2989139 : Blo 1991435 2989139 := bstep (se 1 (by rfl) ⟨2241854, by rfl⟩ : syracuseStep 2989139 = 4483709) B4483709
theorem B1992759 : Blo 1991435 1992759 := bstep (se 1 (by rfl) ⟨1494569, by rfl⟩ : syracuseStep 1992759 = 2989139) B2989139
theorem B3362789 : Blo 1991435 3362789 := bbase (se 4 (by rfl) ⟨315261, by rfl⟩ : syracuseStep 3362789 = 630523) (by norm_num)
theorem B2241859 : Blo 1991435 2241859 := bstep (se 1 (by rfl) ⟨1681394, by rfl⟩ : syracuseStep 2241859 = 3362789) B3362789
theorem B2989145 : Blo 1991435 2989145 := bstep (se 2 (by rfl) ⟨1120929, by rfl⟩ : syracuseStep 2989145 = 2241859) B2241859
theorem B1992763 : Blo 1991435 1992763 := bstep (se 1 (by rfl) ⟨1494572, by rfl⟩ : syracuseStep 1992763 = 2989145) B2989145
theorem B7669525 : Blo 1991435 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B10226033 : Blo 1991435 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B6817355 : Blo 1991435 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B4544903 : Blo 1991435 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B3029935 : Blo 1991435 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B4039913 : Blo 1991435 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B10773101 : Blo 1991435 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B7182067 : Blo 1991435 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B9576089 : Blo 1991435 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B6384059 : Blo 1991435 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B4256039 : Blo 1991435 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B2837359 : Blo 1991435 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B15132581 : Blo 1991435 15132581 := bstep (se 4 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 15132581 = 2837359) B2837359
theorem B10088387 : Blo 1991435 10088387 := bstep (se 1 (by rfl) ⟨7566290, by rfl⟩ : syracuseStep 10088387 = 15132581) B15132581
theorem B6725591 : Blo 1991435 6725591 := bstep (se 1 (by rfl) ⟨5044193, by rfl⟩ : syracuseStep 6725591 = 10088387) B10088387
theorem B4483727 : Blo 1991435 4483727 := bstep (se 1 (by rfl) ⟨3362795, by rfl⟩ : syracuseStep 4483727 = 6725591) B6725591
theorem B2989151 : Blo 1991435 2989151 := bstep (se 1 (by rfl) ⟨2241863, by rfl⟩ : syracuseStep 2989151 = 4483727) B4483727
theorem B1992767 : Blo 1991435 1992767 := bstep (se 1 (by rfl) ⟨1494575, by rfl⟩ : syracuseStep 1992767 = 2989151) B2989151
theorem B2989157 : Blo 1991435 2989157 := bbase (se 4 (by rfl) ⟨280233, by rfl⟩ : syracuseStep 2989157 = 560467) (by norm_num)
theorem B1992771 : Blo 1991435 1992771 := bstep (se 1 (by rfl) ⟨1494578, by rfl⟩ : syracuseStep 1992771 = 2989157) B2989157
theorem B14560181 : Blo 1991435 14560181 := bbase (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) (by norm_num)
theorem B9706787 : Blo 1991435 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B6471191 : Blo 1991435 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B17256509 : Blo 1991435 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B11504339 : Blo 1991435 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B7669559 : Blo 1991435 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B5113039 : Blo 1991435 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B6817385 : Blo 1991435 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B4544923 : Blo 1991435 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B6059897 : Blo 1991435 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B4039931 : Blo 1991435 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B2693287 : Blo 1991435 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B3591049 : Blo 1991435 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B4788065 : Blo 1991435 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B3192043 : Blo 1991435 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B4256057 : Blo 1991435 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B2837371 : Blo 1991435 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B3783161 : Blo 1991435 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B2522107 : Blo 1991435 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B3362809 : Blo 1991435 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B4483745 : Blo 1991435 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B2989163 : Blo 1991435 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B1992775 : Blo 1991435 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B2241877 : Blo 1991435 2241877 := bbase (se 13 (by rfl) ⟨410, by rfl⟩ : syracuseStep 2241877 = 821) (by norm_num)
theorem B2989169 : Blo 1991435 2989169 := bstep (se 2 (by rfl) ⟨1120938, by rfl⟩ : syracuseStep 2989169 = 2241877) B2241877
theorem B1992779 : Blo 1991435 1992779 := bstep (se 1 (by rfl) ⟨1494584, by rfl⟩ : syracuseStep 1992779 = 2989169) B2989169
theorem B2522117 : Blo 1991435 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B6725645 : Blo 1991435 6725645 := bstep (se 3 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 6725645 = 2522117) B2522117
theorem B4483763 : Blo 1991435 4483763 := bstep (se 1 (by rfl) ⟨3362822, by rfl⟩ : syracuseStep 4483763 = 6725645) B6725645
theorem B2989175 : Blo 1991435 2989175 := bstep (se 1 (by rfl) ⟨2241881, by rfl⟩ : syracuseStep 2989175 = 4483763) B4483763
theorem B1992783 : Blo 1991435 1992783 := bstep (se 1 (by rfl) ⟨1494587, by rfl⟩ : syracuseStep 1992783 = 2989175) B2989175
theorem B2989181 : Blo 1991435 2989181 := bbase (se 3 (by rfl) ⟨560471, by rfl⟩ : syracuseStep 2989181 = 1120943) (by norm_num)
theorem B1992787 : Blo 1991435 1992787 := bstep (se 1 (by rfl) ⟨1494590, by rfl⟩ : syracuseStep 1992787 = 2989181) B2989181
theorem B4483781 : Blo 1991435 4483781 := bbase (se 4 (by rfl) ⟨420354, by rfl⟩ : syracuseStep 4483781 = 840709) (by norm_num)
theorem B2989187 : Blo 1991435 2989187 := bstep (se 1 (by rfl) ⟨2241890, by rfl⟩ : syracuseStep 2989187 = 4483781) B4483781
theorem B1992791 : Blo 1991435 1992791 := bstep (se 1 (by rfl) ⟨1494593, by rfl⟩ : syracuseStep 1992791 = 2989187) B2989187
theorem B2019985 : Blo 1991435 2019985 := bbase (se 2 (by rfl) ⟨757494, by rfl⟩ : syracuseStep 2019985 = 1514989) (by norm_num)
theorem B10773253 : Blo 1991435 10773253 := bstep (se 4 (by rfl) ⟨1009992, by rfl⟩ : syracuseStep 10773253 = 2019985) B2019985
theorem B14364337 : Blo 1991435 14364337 := bstep (se 2 (by rfl) ⟨5386626, by rfl⟩ : syracuseStep 14364337 = 10773253) B10773253
theorem B19152449 : Blo 1991435 19152449 := bstep (se 2 (by rfl) ⟨7182168, by rfl⟩ : syracuseStep 19152449 = 14364337) B14364337
theorem B12768299 : Blo 1991435 12768299 := bstep (se 1 (by rfl) ⟨9576224, by rfl⟩ : syracuseStep 12768299 = 19152449) B19152449
theorem B8512199 : Blo 1991435 8512199 := bstep (se 1 (by rfl) ⟨6384149, by rfl⟩ : syracuseStep 8512199 = 12768299) B12768299
theorem B5674799 : Blo 1991435 5674799 := bstep (se 1 (by rfl) ⟨4256099, by rfl⟩ : syracuseStep 5674799 = 8512199) B8512199
theorem B3783199 : Blo 1991435 3783199 := bstep (se 1 (by rfl) ⟨2837399, by rfl⟩ : syracuseStep 3783199 = 5674799) B5674799
theorem B5044265 : Blo 1991435 5044265 := bstep (se 2 (by rfl) ⟨1891599, by rfl⟩ : syracuseStep 5044265 = 3783199) B3783199
theorem B3362843 : Blo 1991435 3362843 := bstep (se 1 (by rfl) ⟨2522132, by rfl⟩ : syracuseStep 3362843 = 5044265) B5044265
theorem B2241895 : Blo 1991435 2241895 := bstep (se 1 (by rfl) ⟨1681421, by rfl⟩ : syracuseStep 2241895 = 3362843) B3362843
theorem B2989193 : Blo 1991435 2989193 := bstep (se 2 (by rfl) ⟨1120947, by rfl⟩ : syracuseStep 2989193 = 2241895) B2241895
theorem B1992795 : Blo 1991435 1992795 := bstep (se 1 (by rfl) ⟨1494596, by rfl⟩ : syracuseStep 1992795 = 2989193) B2989193
theorem B10088549 : Blo 1991435 10088549 := bbase (se 4 (by rfl) ⟨945801, by rfl⟩ : syracuseStep 10088549 = 1891603) (by norm_num)
theorem B6725699 : Blo 1991435 6725699 := bstep (se 1 (by rfl) ⟨5044274, by rfl⟩ : syracuseStep 6725699 = 10088549) B10088549
theorem B4483799 : Blo 1991435 4483799 := bstep (se 1 (by rfl) ⟨3362849, by rfl⟩ : syracuseStep 4483799 = 6725699) B6725699
theorem B2989199 : Blo 1991435 2989199 := bstep (se 1 (by rfl) ⟨2241899, by rfl⟩ : syracuseStep 2989199 = 4483799) B4483799
theorem B1992799 : Blo 1991435 1992799 := bstep (se 1 (by rfl) ⟨1494599, by rfl⟩ : syracuseStep 1992799 = 2989199) B2989199
theorem B2989205 : Blo 1991435 2989205 := bbase (se 6 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 2989205 = 140119) (by norm_num)
theorem B1992803 : Blo 1991435 1992803 := bstep (se 1 (by rfl) ⟨1494602, by rfl⟩ : syracuseStep 1992803 = 2989205) B2989205
theorem B2019997 : Blo 1991435 2019997 := bbase (se 3 (by rfl) ⟨378749, by rfl⟩ : syracuseStep 2019997 = 757499) (by norm_num)
theorem B10773317 : Blo 1991435 10773317 := bstep (se 4 (by rfl) ⟨1009998, by rfl⟩ : syracuseStep 10773317 = 2019997) B2019997
theorem B7182211 : Blo 1991435 7182211 := bstep (se 1 (by rfl) ⟨5386658, by rfl⟩ : syracuseStep 7182211 = 10773317) B10773317
theorem B9576281 : Blo 1991435 9576281 := bstep (se 2 (by rfl) ⟨3591105, by rfl⟩ : syracuseStep 9576281 = 7182211) B7182211
theorem B6384187 : Blo 1991435 6384187 := bstep (se 1 (by rfl) ⟨4788140, by rfl⟩ : syracuseStep 6384187 = 9576281) B9576281
theorem B8512249 : Blo 1991435 8512249 := bstep (se 2 (by rfl) ⟨3192093, by rfl⟩ : syracuseStep 8512249 = 6384187) B6384187
theorem B11349665 : Blo 1991435 11349665 := bstep (se 2 (by rfl) ⟨4256124, by rfl⟩ : syracuseStep 11349665 = 8512249) B8512249
theorem B7566443 : Blo 1991435 7566443 := bstep (se 1 (by rfl) ⟨5674832, by rfl⟩ : syracuseStep 7566443 = 11349665) B11349665
theorem B5044295 : Blo 1991435 5044295 := bstep (se 1 (by rfl) ⟨3783221, by rfl⟩ : syracuseStep 5044295 = 7566443) B7566443
theorem B3362863 : Blo 1991435 3362863 := bstep (se 1 (by rfl) ⟨2522147, by rfl⟩ : syracuseStep 3362863 = 5044295) B5044295
theorem B4483817 : Blo 1991435 4483817 := bstep (se 2 (by rfl) ⟨1681431, by rfl⟩ : syracuseStep 4483817 = 3362863) B3362863
theorem B2989211 : Blo 1991435 2989211 := bstep (se 1 (by rfl) ⟨2241908, by rfl⟩ : syracuseStep 2989211 = 4483817) B4483817
theorem B1992807 : Blo 1991435 1992807 := bstep (se 1 (by rfl) ⟨1494605, by rfl⟩ : syracuseStep 1992807 = 2989211) B2989211
theorem B2241913 : Blo 1991435 2241913 := bbase (se 2 (by rfl) ⟨840717, by rfl⟩ : syracuseStep 2241913 = 1681435) (by norm_num)
theorem B2989217 : Blo 1991435 2989217 := bstep (se 2 (by rfl) ⟨1120956, by rfl⟩ : syracuseStep 2989217 = 2241913) B2241913
theorem B1992811 : Blo 1991435 1992811 := bstep (se 1 (by rfl) ⟨1494608, by rfl⟩ : syracuseStep 1992811 = 2989217) B2989217
theorem B15339413 : Blo 1991435 15339413 := bbase (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) (by norm_num)
theorem B40905101 : Blo 1991435 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B109080269 : Blo 1991435 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B72720179 : Blo 1991435 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B48480119 : Blo 1991435 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B32320079 : Blo 1991435 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B21546719 : Blo 1991435 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B14364479 : Blo 1991435 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B9576319 : Blo 1991435 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B12768425 : Blo 1991435 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B8512283 : Blo 1991435 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B5674855 : Blo 1991435 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B7566473 : Blo 1991435 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B5044315 : Blo 1991435 5044315 := bstep (se 1 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 5044315 = 7566473) B7566473
theorem B6725753 : Blo 1991435 6725753 := bstep (se 2 (by rfl) ⟨2522157, by rfl⟩ : syracuseStep 6725753 = 5044315) B5044315
theorem B4483835 : Blo 1991435 4483835 := bstep (se 1 (by rfl) ⟨3362876, by rfl⟩ : syracuseStep 4483835 = 6725753) B6725753
theorem B2989223 : Blo 1991435 2989223 := bstep (se 1 (by rfl) ⟨2241917, by rfl⟩ : syracuseStep 2989223 = 4483835) B4483835
theorem B1992815 : Blo 1991435 1992815 := bstep (se 1 (by rfl) ⟨1494611, by rfl⟩ : syracuseStep 1992815 = 2989223) B2989223
theorem B2989229 : Blo 1991435 2989229 := bbase (se 3 (by rfl) ⟨560480, by rfl⟩ : syracuseStep 2989229 = 1120961) (by norm_num)
theorem B1992819 : Blo 1991435 1992819 := bstep (se 1 (by rfl) ⟨1494614, by rfl⟩ : syracuseStep 1992819 = 2989229) B2989229
theorem B4483853 : Blo 1991435 4483853 := bbase (se 3 (by rfl) ⟨840722, by rfl⟩ : syracuseStep 4483853 = 1681445) (by norm_num)
theorem B2989235 : Blo 1991435 2989235 := bstep (se 1 (by rfl) ⟨2241926, by rfl⟩ : syracuseStep 2989235 = 4483853) B4483853
theorem B1992823 : Blo 1991435 1992823 := bstep (se 1 (by rfl) ⟨1494617, by rfl⟩ : syracuseStep 1992823 = 2989235) B2989235
theorem B2522173 : Blo 1991435 2522173 := bbase (se 3 (by rfl) ⟨472907, by rfl⟩ : syracuseStep 2522173 = 945815) (by norm_num)
theorem B3362897 : Blo 1991435 3362897 := bstep (se 2 (by rfl) ⟨1261086, by rfl⟩ : syracuseStep 3362897 = 2522173) B2522173
theorem B2241931 : Blo 1991435 2241931 := bstep (se 1 (by rfl) ⟨1681448, by rfl⟩ : syracuseStep 2241931 = 3362897) B3362897
theorem B2989241 : Blo 1991435 2989241 := bstep (se 2 (by rfl) ⟨1120965, by rfl⟩ : syracuseStep 2989241 = 2241931) B2241931
theorem B1992827 : Blo 1991435 1992827 := bstep (se 1 (by rfl) ⟨1494620, by rfl⟩ : syracuseStep 1992827 = 2989241) B2989241
theorem B2020021 : Blo 1991435 2020021 := bbase (se 5 (by rfl) ⟨94688, by rfl⟩ : syracuseStep 2020021 = 189377) (by norm_num)
theorem B10773445 : Blo 1991435 10773445 := bstep (se 4 (by rfl) ⟨1010010, by rfl⟩ : syracuseStep 10773445 = 2020021) B2020021
theorem B14364593 : Blo 1991435 14364593 := bstep (se 2 (by rfl) ⟨5386722, by rfl⟩ : syracuseStep 14364593 = 10773445) B10773445
theorem B9576395 : Blo 1991435 9576395 := bstep (se 1 (by rfl) ⟨7182296, by rfl⟩ : syracuseStep 9576395 = 14364593) B14364593
theorem B6384263 : Blo 1991435 6384263 := bstep (se 1 (by rfl) ⟨4788197, by rfl⟩ : syracuseStep 6384263 = 9576395) B9576395
theorem B17024701 : Blo 1991435 17024701 := bstep (se 3 (by rfl) ⟨3192131, by rfl⟩ : syracuseStep 17024701 = 6384263) B6384263
theorem B22699601 : Blo 1991435 22699601 := bstep (se 2 (by rfl) ⟨8512350, by rfl⟩ : syracuseStep 22699601 = 17024701) B17024701
theorem B15133067 : Blo 1991435 15133067 := bstep (se 1 (by rfl) ⟨11349800, by rfl⟩ : syracuseStep 15133067 = 22699601) B22699601
theorem B10088711 : Blo 1991435 10088711 := bstep (se 1 (by rfl) ⟨7566533, by rfl⟩ : syracuseStep 10088711 = 15133067) B15133067
theorem B6725807 : Blo 1991435 6725807 := bstep (se 1 (by rfl) ⟨5044355, by rfl⟩ : syracuseStep 6725807 = 10088711) B10088711
theorem B4483871 : Blo 1991435 4483871 := bstep (se 1 (by rfl) ⟨3362903, by rfl⟩ : syracuseStep 4483871 = 6725807) B6725807
theorem B2989247 : Blo 1991435 2989247 := bstep (se 1 (by rfl) ⟨2241935, by rfl⟩ : syracuseStep 2989247 = 4483871) B4483871
theorem B1992831 : Blo 1991435 1992831 := bstep (se 1 (by rfl) ⟨1494623, by rfl⟩ : syracuseStep 1992831 = 2989247) B2989247
theorem B2989253 : Blo 1991435 2989253 := bbase (se 4 (by rfl) ⟨280242, by rfl⟩ : syracuseStep 2989253 = 560485) (by norm_num)
theorem B1992835 : Blo 1991435 1992835 := bstep (se 1 (by rfl) ⟨1494626, by rfl⟩ : syracuseStep 1992835 = 2989253) B2989253
theorem B3362917 : Blo 1991435 3362917 := bbase (se 4 (by rfl) ⟨315273, by rfl⟩ : syracuseStep 3362917 = 630547) (by norm_num)
theorem B4483889 : Blo 1991435 4483889 := bstep (se 2 (by rfl) ⟨1681458, by rfl⟩ : syracuseStep 4483889 = 3362917) B3362917
theorem B2989259 : Blo 1991435 2989259 := bstep (se 1 (by rfl) ⟨2241944, by rfl⟩ : syracuseStep 2989259 = 4483889) B4483889
theorem B1992839 : Blo 1991435 1992839 := bstep (se 1 (by rfl) ⟨1494629, by rfl⟩ : syracuseStep 1992839 = 2989259) B2989259
theorem B2241949 : Blo 1991435 2241949 := bbase (se 3 (by rfl) ⟨420365, by rfl⟩ : syracuseStep 2241949 = 840731) (by norm_num)
theorem B2989265 : Blo 1991435 2989265 := bstep (se 2 (by rfl) ⟨1120974, by rfl⟩ : syracuseStep 2989265 = 2241949) B2241949
theorem B1992843 : Blo 1991435 1992843 := bstep (se 1 (by rfl) ⟨1494632, by rfl⟩ : syracuseStep 1992843 = 2989265) B2989265
theorem B6725861 : Blo 1991435 6725861 := bbase (se 4 (by rfl) ⟨630549, by rfl⟩ : syracuseStep 6725861 = 1261099) (by norm_num)
theorem B4483907 : Blo 1991435 4483907 := bstep (se 1 (by rfl) ⟨3362930, by rfl⟩ : syracuseStep 4483907 = 6725861) B6725861
theorem B2989271 : Blo 1991435 2989271 := bstep (se 1 (by rfl) ⟨2241953, by rfl⟩ : syracuseStep 2989271 = 4483907) B4483907
theorem B1992847 : Blo 1991435 1992847 := bstep (se 1 (by rfl) ⟨1494635, by rfl⟩ : syracuseStep 1992847 = 2989271) B2989271
theorem B2989277 : Blo 1991435 2989277 := bbase (se 3 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 2989277 = 1120979) (by norm_num)
theorem B1992851 : Blo 1991435 1992851 := bstep (se 1 (by rfl) ⟨1494638, by rfl⟩ : syracuseStep 1992851 = 2989277) B2989277
theorem B4483925 : Blo 1991435 4483925 := bbase (se 9 (by rfl) ⟨13136, by rfl⟩ : syracuseStep 4483925 = 26273) (by norm_num)
theorem B2989283 : Blo 1991435 2989283 := bstep (se 1 (by rfl) ⟨2241962, by rfl⟩ : syracuseStep 2989283 = 4483925) B4483925
theorem B1992855 : Blo 1991435 1992855 := bstep (se 1 (by rfl) ⟨1494641, by rfl⟩ : syracuseStep 1992855 = 2989283) B2989283
theorem B5674981 : Blo 1991435 5674981 := bbase (se 4 (by rfl) ⟨532029, by rfl⟩ : syracuseStep 5674981 = 1064059) (by norm_num)
theorem B7566641 : Blo 1991435 7566641 := bstep (se 2 (by rfl) ⟨2837490, by rfl⟩ : syracuseStep 7566641 = 5674981) B5674981
theorem B5044427 : Blo 1991435 5044427 := bstep (se 1 (by rfl) ⟨3783320, by rfl⟩ : syracuseStep 5044427 = 7566641) B7566641
theorem B3362951 : Blo 1991435 3362951 := bstep (se 1 (by rfl) ⟨2522213, by rfl⟩ : syracuseStep 3362951 = 5044427) B5044427
theorem B2241967 : Blo 1991435 2241967 := bstep (se 1 (by rfl) ⟨1681475, by rfl⟩ : syracuseStep 2241967 = 3362951) B3362951
theorem B2989289 : Blo 1991435 2989289 := bstep (se 2 (by rfl) ⟨1120983, by rfl⟩ : syracuseStep 2989289 = 2241967) B2241967
theorem B1992859 : Blo 1991435 1992859 := bstep (se 1 (by rfl) ⟨1494644, by rfl⟩ : syracuseStep 1992859 = 2989289) B2989289
theorem B32320853 : Blo 1991435 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B21547235 : Blo 1991435 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B57459293 : Blo 1991435 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B38306195 : Blo 1991435 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B25537463 : Blo 1991435 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B17024975 : Blo 1991435 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B11349983 : Blo 1991435 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B7566655 : Blo 1991435 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B10088873 : Blo 1991435 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B6725915 : Blo 1991435 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B4483943 : Blo 1991435 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B2989295 : Blo 1991435 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B1992863 : Blo 1991435 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B2989301 : Blo 1991435 2989301 := bbase (se 5 (by rfl) ⟨140123, by rfl⟩ : syracuseStep 2989301 = 280247) (by norm_num)
theorem B1992867 : Blo 1991435 1992867 := bstep (se 1 (by rfl) ⟨1494650, by rfl⟩ : syracuseStep 1992867 = 2989301) B2989301
theorem B3591221 : Blo 1991435 3591221 := bbase (se 5 (by rfl) ⟨168338, by rfl⟩ : syracuseStep 3591221 = 336677) (by norm_num)
theorem B9576589 : Blo 1991435 9576589 := bstep (se 3 (by rfl) ⟨1795610, by rfl⟩ : syracuseStep 9576589 = 3591221) B3591221
theorem B12768785 : Blo 1991435 12768785 := bstep (se 2 (by rfl) ⟨4788294, by rfl⟩ : syracuseStep 12768785 = 9576589) B9576589
theorem B8512523 : Blo 1991435 8512523 := bstep (se 1 (by rfl) ⟨6384392, by rfl⟩ : syracuseStep 8512523 = 12768785) B12768785
theorem B5675015 : Blo 1991435 5675015 := bstep (se 1 (by rfl) ⟨4256261, by rfl⟩ : syracuseStep 5675015 = 8512523) B8512523
theorem B3783343 : Blo 1991435 3783343 := bstep (se 1 (by rfl) ⟨2837507, by rfl⟩ : syracuseStep 3783343 = 5675015) B5675015
theorem B5044457 : Blo 1991435 5044457 := bstep (se 2 (by rfl) ⟨1891671, by rfl⟩ : syracuseStep 5044457 = 3783343) B3783343
theorem B3362971 : Blo 1991435 3362971 := bstep (se 1 (by rfl) ⟨2522228, by rfl⟩ : syracuseStep 3362971 = 5044457) B5044457
theorem B4483961 : Blo 1991435 4483961 := bstep (se 2 (by rfl) ⟨1681485, by rfl⟩ : syracuseStep 4483961 = 3362971) B3362971
theorem B2989307 : Blo 1991435 2989307 := bstep (se 1 (by rfl) ⟨2241980, by rfl⟩ : syracuseStep 2989307 = 4483961) B4483961
theorem B1992871 : Blo 1991435 1992871 := bstep (se 1 (by rfl) ⟨1494653, by rfl⟩ : syracuseStep 1992871 = 2989307) B2989307
theorem B2241985 : Blo 1991435 2241985 := bbase (se 2 (by rfl) ⟨840744, by rfl⟩ : syracuseStep 2241985 = 1681489) (by norm_num)
theorem B2989313 : Blo 1991435 2989313 := bstep (se 2 (by rfl) ⟨1120992, by rfl⟩ : syracuseStep 2989313 = 2241985) B2241985
theorem B1992875 : Blo 1991435 1992875 := bstep (se 1 (by rfl) ⟨1494656, by rfl⟩ : syracuseStep 1992875 = 2989313) B2989313
theorem B5044477 : Blo 1991435 5044477 := bbase (se 3 (by rfl) ⟨945839, by rfl⟩ : syracuseStep 5044477 = 1891679) (by norm_num)
theorem B6725969 : Blo 1991435 6725969 := bstep (se 2 (by rfl) ⟨2522238, by rfl⟩ : syracuseStep 6725969 = 5044477) B5044477
theorem B4483979 : Blo 1991435 4483979 := bstep (se 1 (by rfl) ⟨3362984, by rfl⟩ : syracuseStep 4483979 = 6725969) B6725969
theorem B2989319 : Blo 1991435 2989319 := bstep (se 1 (by rfl) ⟨2241989, by rfl⟩ : syracuseStep 2989319 = 4483979) B4483979
theorem B1992879 : Blo 1991435 1992879 := bstep (se 1 (by rfl) ⟨1494659, by rfl⟩ : syracuseStep 1992879 = 2989319) B2989319
theorem B2989325 : Blo 1991435 2989325 := bbase (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) (by norm_num)
theorem B1992883 : Blo 1991435 1992883 := bstep (se 1 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 1992883 = 2989325) B2989325
theorem B4483997 : Blo 1991435 4483997 := bbase (se 3 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 4483997 = 1681499) (by norm_num)
theorem B2989331 : Blo 1991435 2989331 := bstep (se 1 (by rfl) ⟨2241998, by rfl⟩ : syracuseStep 2989331 = 4483997) B4483997
theorem B1992887 : Blo 1991435 1992887 := bstep (se 1 (by rfl) ⟨1494665, by rfl⟩ : syracuseStep 1992887 = 2989331) B2989331
theorem B3363005 : Blo 1991435 3363005 := bbase (se 3 (by rfl) ⟨630563, by rfl⟩ : syracuseStep 3363005 = 1261127) (by norm_num)
theorem B2242003 : Blo 1991435 2242003 := bstep (se 1 (by rfl) ⟨1681502, by rfl⟩ : syracuseStep 2242003 = 3363005) B3363005
theorem B2989337 : Blo 1991435 2989337 := bstep (se 2 (by rfl) ⟨1121001, by rfl⟩ : syracuseStep 2989337 = 2242003) B2242003
theorem B1992891 : Blo 1991435 1992891 := bstep (se 1 (by rfl) ⟨1494668, by rfl⟩ : syracuseStep 1992891 = 2989337) B2989337
theorem B11350165 : Blo 1991435 11350165 := bbase (se 6 (by rfl) ⟨266019, by rfl⟩ : syracuseStep 11350165 = 532039) (by norm_num)
theorem B15133553 : Blo 1991435 15133553 := bstep (se 2 (by rfl) ⟨5675082, by rfl⟩ : syracuseStep 15133553 = 11350165) B11350165
theorem B10089035 : Blo 1991435 10089035 := bstep (se 1 (by rfl) ⟨7566776, by rfl⟩ : syracuseStep 10089035 = 15133553) B15133553
theorem B6726023 : Blo 1991435 6726023 := bstep (se 1 (by rfl) ⟨5044517, by rfl⟩ : syracuseStep 6726023 = 10089035) B10089035
theorem B4484015 : Blo 1991435 4484015 := bstep (se 1 (by rfl) ⟨3363011, by rfl⟩ : syracuseStep 4484015 = 6726023) B6726023
theorem B2989343 : Blo 1991435 2989343 := bstep (se 1 (by rfl) ⟨2242007, by rfl⟩ : syracuseStep 2989343 = 4484015) B4484015
theorem B1992895 : Blo 1991435 1992895 := bstep (se 1 (by rfl) ⟨1494671, by rfl⟩ : syracuseStep 1992895 = 2989343) B2989343
theorem B2989349 : Blo 1991435 2989349 := bbase (se 4 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 2989349 = 560503) (by norm_num)
theorem B1992899 : Blo 1991435 1992899 := bstep (se 1 (by rfl) ⟨1494674, by rfl⟩ : syracuseStep 1992899 = 2989349) B2989349
theorem B2522269 : Blo 1991435 2522269 := bbase (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) (by norm_num)
theorem B3363025 : Blo 1991435 3363025 := bstep (se 2 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 3363025 = 2522269) B2522269
theorem B4484033 : Blo 1991435 4484033 := bstep (se 2 (by rfl) ⟨1681512, by rfl⟩ : syracuseStep 4484033 = 3363025) B3363025
theorem B2989355 : Blo 1991435 2989355 := bstep (se 1 (by rfl) ⟨2242016, by rfl⟩ : syracuseStep 2989355 = 4484033) B4484033
theorem B1992903 : Blo 1991435 1992903 := bstep (se 1 (by rfl) ⟨1494677, by rfl⟩ : syracuseStep 1992903 = 2989355) B2989355
theorem B2242021 : Blo 1991435 2242021 := bbase (se 4 (by rfl) ⟨210189, by rfl⟩ : syracuseStep 2242021 = 420379) (by norm_num)
theorem B2989361 : Blo 1991435 2989361 := bstep (se 2 (by rfl) ⟨1121010, by rfl⟩ : syracuseStep 2989361 = 2242021) B2242021
theorem B1992907 : Blo 1991435 1992907 := bstep (se 1 (by rfl) ⟨1494680, by rfl⟩ : syracuseStep 1992907 = 2989361) B2989361
theorem B3791333 : Blo 1991435 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B10110221 : Blo 1991435 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B6740147 : Blo 1991435 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B4493431 : Blo 1991435 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B5991241 : Blo 1991435 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B7988321 : Blo 1991435 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B5325547 : Blo 1991435 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B7100729 : Blo 1991435 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B4733819 : Blo 1991435 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B3155879 : Blo 1991435 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B8415677 : Blo 1991435 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B5610451 : Blo 1991435 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B7480601 : Blo 1991435 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B4987067 : Blo 1991435 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B53195381 : Blo 1991435 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B35463587 : Blo 1991435 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B378278261 : Blo 1991435 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B252185507 : Blo 1991435 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B168123671 : Blo 1991435 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B112082447 : Blo 1991435 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B74721631 : Blo 1991435 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B99628841 : Blo 1991435 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B66419227 : Blo 1991435 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B88558969 : Blo 1991435 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B118078625 : Blo 1991435 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B78719083 : Blo 1991435 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B419835109 : Blo 1991435 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B559780145 : Blo 1991435 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B373186763 : Blo 1991435 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B248791175 : Blo 1991435 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B165860783 : Blo 1991435 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B110573855 : Blo 1991435 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B73715903 : Blo 1991435 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B49143935 : Blo 1991435 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B131050493 : Blo 1991435 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B87366995 : Blo 1991435 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B58244663 : Blo 1991435 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B38829775 : Blo 1991435 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B51773033 : Blo 1991435 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B34515355 : Blo 1991435 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B46020473 : Blo 1991435 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B30680315 : Blo 1991435 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B20453543 : Blo 1991435 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B13635695 : Blo 1991435 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B9090463 : Blo 1991435 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B12120617 : Blo 1991435 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B8080411 : Blo 1991435 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B10773881 : Blo 1991435 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B7182587 : Blo 1991435 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B4788391 : Blo 1991435 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B6384521 : Blo 1991435 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B4256347 : Blo 1991435 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5675129 : Blo 1991435 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B3783419 : Blo 1991435 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B2522279 : Blo 1991435 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B6726077 : Blo 1991435 6726077 := bstep (se 3 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 6726077 = 2522279) B2522279
theorem B4484051 : Blo 1991435 4484051 := bstep (se 1 (by rfl) ⟨3363038, by rfl⟩ : syracuseStep 4484051 = 6726077) B6726077
theorem B2989367 : Blo 1991435 2989367 := bstep (se 1 (by rfl) ⟨2242025, by rfl⟩ : syracuseStep 2989367 = 4484051) B4484051
theorem B1992911 : Blo 1991435 1992911 := bstep (se 1 (by rfl) ⟨1494683, by rfl⟩ : syracuseStep 1992911 = 2989367) B2989367
theorem B2989373 : Blo 1991435 2989373 := bbase (se 3 (by rfl) ⟨560507, by rfl⟩ : syracuseStep 2989373 = 1121015) (by norm_num)
theorem B1992915 : Blo 1991435 1992915 := bstep (se 1 (by rfl) ⟨1494686, by rfl⟩ : syracuseStep 1992915 = 2989373) B2989373
theorem B4484069 : Blo 1991435 4484069 := bbase (se 4 (by rfl) ⟨420381, by rfl⟩ : syracuseStep 4484069 = 840763) (by norm_num)
theorem B2989379 : Blo 1991435 2989379 := bstep (se 1 (by rfl) ⟨2242034, by rfl⟩ : syracuseStep 2989379 = 4484069) B4484069
theorem B1992919 : Blo 1991435 1992919 := bstep (se 1 (by rfl) ⟨1494689, by rfl⟩ : syracuseStep 1992919 = 2989379) B2989379
theorem B5044589 : Blo 1991435 5044589 := bbase (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) (by norm_num)
theorem B3363059 : Blo 1991435 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B2242039 : Blo 1991435 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B2989385 : Blo 1991435 2989385 := bstep (se 2 (by rfl) ⟨1121019, by rfl⟩ : syracuseStep 2989385 = 2242039) B2242039
theorem B1992923 : Blo 1991435 1992923 := bstep (se 1 (by rfl) ⟨1494692, by rfl⟩ : syracuseStep 1992923 = 2989385) B2989385
theorem B4256381 : Blo 1991435 4256381 := bbase (se 3 (by rfl) ⟨798071, by rfl⟩ : syracuseStep 4256381 = 1596143) (by norm_num)
theorem B2837587 : Blo 1991435 2837587 := bstep (se 1 (by rfl) ⟨2128190, by rfl⟩ : syracuseStep 2837587 = 4256381) B4256381
theorem B3783449 : Blo 1991435 3783449 := bstep (se 2 (by rfl) ⟨1418793, by rfl⟩ : syracuseStep 3783449 = 2837587) B2837587
theorem B10089197 : Blo 1991435 10089197 := bstep (se 3 (by rfl) ⟨1891724, by rfl⟩ : syracuseStep 10089197 = 3783449) B3783449
theorem B6726131 : Blo 1991435 6726131 := bstep (se 1 (by rfl) ⟨5044598, by rfl⟩ : syracuseStep 6726131 = 10089197) B10089197
theorem B4484087 : Blo 1991435 4484087 := bstep (se 1 (by rfl) ⟨3363065, by rfl⟩ : syracuseStep 4484087 = 6726131) B6726131
theorem B2989391 : Blo 1991435 2989391 := bstep (se 1 (by rfl) ⟨2242043, by rfl⟩ : syracuseStep 2989391 = 4484087) B4484087
theorem B1992927 : Blo 1991435 1992927 := bstep (se 1 (by rfl) ⟨1494695, by rfl⟩ : syracuseStep 1992927 = 2989391) B2989391
theorem B2989397 : Blo 1991435 2989397 := bbase (se 11 (by rfl) ⟨2189, by rfl⟩ : syracuseStep 2989397 = 4379) (by norm_num)
theorem B1992931 : Blo 1991435 1992931 := bstep (se 1 (by rfl) ⟨1494698, by rfl⟩ : syracuseStep 1992931 = 2989397) B2989397
theorem B10921013 : Blo 1991435 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B7280675 : Blo 1991435 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B4853783 : Blo 1991435 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3235855 : Blo 1991435 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B4314473 : Blo 1991435 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B2876315 : Blo 1991435 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B30680693 : Blo 1991435 30680693 := bstep (se 5 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 30680693 = 2876315) B2876315
theorem B20453795 : Blo 1991435 20453795 := bstep (se 1 (by rfl) ⟨15340346, by rfl⟩ : syracuseStep 20453795 = 30680693) B30680693
theorem B13635863 : Blo 1991435 13635863 := bstep (se 1 (by rfl) ⟨10226897, by rfl⟩ : syracuseStep 13635863 = 20453795) B20453795
theorem B9090575 : Blo 1991435 9090575 := bstep (se 1 (by rfl) ⟨6817931, by rfl⟩ : syracuseStep 9090575 = 13635863) B13635863
theorem B6060383 : Blo 1991435 6060383 := bstep (se 1 (by rfl) ⟨4545287, by rfl⟩ : syracuseStep 6060383 = 9090575) B9090575
theorem B4040255 : Blo 1991435 4040255 := bstep (se 1 (by rfl) ⟨3030191, by rfl⟩ : syracuseStep 4040255 = 6060383) B6060383
theorem B2693503 : Blo 1991435 2693503 := bstep (se 1 (by rfl) ⟨2020127, by rfl⟩ : syracuseStep 2693503 = 4040255) B4040255
theorem B3591337 : Blo 1991435 3591337 := bstep (se 2 (by rfl) ⟨1346751, by rfl⟩ : syracuseStep 3591337 = 2693503) B2693503
theorem B4788449 : Blo 1991435 4788449 := bstep (se 2 (by rfl) ⟨1795668, by rfl⟩ : syracuseStep 4788449 = 3591337) B3591337
theorem B3192299 : Blo 1991435 3192299 := bstep (se 1 (by rfl) ⟨2394224, by rfl⟩ : syracuseStep 3192299 = 4788449) B4788449
theorem B2128199 : Blo 1991435 2128199 := bstep (se 1 (by rfl) ⟨1596149, by rfl⟩ : syracuseStep 2128199 = 3192299) B3192299
theorem B5675197 : Blo 1991435 5675197 := bstep (se 3 (by rfl) ⟨1064099, by rfl⟩ : syracuseStep 5675197 = 2128199) B2128199
theorem B7566929 : Blo 1991435 7566929 := bstep (se 2 (by rfl) ⟨2837598, by rfl⟩ : syracuseStep 7566929 = 5675197) B5675197
theorem B5044619 : Blo 1991435 5044619 := bstep (se 1 (by rfl) ⟨3783464, by rfl⟩ : syracuseStep 5044619 = 7566929) B7566929
theorem B3363079 : Blo 1991435 3363079 := bstep (se 1 (by rfl) ⟨2522309, by rfl⟩ : syracuseStep 3363079 = 5044619) B5044619
theorem B4484105 : Blo 1991435 4484105 := bstep (se 2 (by rfl) ⟨1681539, by rfl⟩ : syracuseStep 4484105 = 3363079) B3363079
theorem B2989403 : Blo 1991435 2989403 := bstep (se 1 (by rfl) ⟨2242052, by rfl⟩ : syracuseStep 2989403 = 4484105) B4484105
theorem B1992935 : Blo 1991435 1992935 := bstep (se 1 (by rfl) ⟨1494701, by rfl⟩ : syracuseStep 1992935 = 2989403) B2989403
theorem B2242057 : Blo 1991435 2242057 := bbase (se 2 (by rfl) ⟨840771, by rfl⟩ : syracuseStep 2242057 = 1681543) (by norm_num)
theorem B2989409 : Blo 1991435 2989409 := bstep (se 2 (by rfl) ⟨1121028, by rfl⟩ : syracuseStep 2989409 = 2242057) B2242057
theorem B1992939 : Blo 1991435 1992939 := bstep (se 1 (by rfl) ⟨1494704, by rfl⟩ : syracuseStep 1992939 = 2989409) B2989409
theorem B4040269 : Blo 1991435 4040269 := bbase (se 3 (by rfl) ⟨757550, by rfl⟩ : syracuseStep 4040269 = 1515101) (by norm_num)
theorem B21548101 : Blo 1991435 21548101 := bstep (se 4 (by rfl) ⟨2020134, by rfl⟩ : syracuseStep 21548101 = 4040269) B4040269
theorem B28730801 : Blo 1991435 28730801 := bstep (se 2 (by rfl) ⟨10774050, by rfl⟩ : syracuseStep 28730801 = 21548101) B21548101
theorem B19153867 : Blo 1991435 19153867 := bstep (se 1 (by rfl) ⟨14365400, by rfl⟩ : syracuseStep 19153867 = 28730801) B28730801
theorem B25538489 : Blo 1991435 25538489 := bstep (se 2 (by rfl) ⟨9576933, by rfl⟩ : syracuseStep 25538489 = 19153867) B19153867
theorem B17025659 : Blo 1991435 17025659 := bstep (se 1 (by rfl) ⟨12769244, by rfl⟩ : syracuseStep 17025659 = 25538489) B25538489
theorem B11350439 : Blo 1991435 11350439 := bstep (se 1 (by rfl) ⟨8512829, by rfl⟩ : syracuseStep 11350439 = 17025659) B17025659
theorem B7566959 : Blo 1991435 7566959 := bstep (se 1 (by rfl) ⟨5675219, by rfl⟩ : syracuseStep 7566959 = 11350439) B11350439
theorem B5044639 : Blo 1991435 5044639 := bstep (se 1 (by rfl) ⟨3783479, by rfl⟩ : syracuseStep 5044639 = 7566959) B7566959
theorem B6726185 : Blo 1991435 6726185 := bstep (se 2 (by rfl) ⟨2522319, by rfl⟩ : syracuseStep 6726185 = 5044639) B5044639
theorem B4484123 : Blo 1991435 4484123 := bstep (se 1 (by rfl) ⟨3363092, by rfl⟩ : syracuseStep 4484123 = 6726185) B6726185
theorem B2989415 : Blo 1991435 2989415 := bstep (se 1 (by rfl) ⟨2242061, by rfl⟩ : syracuseStep 2989415 = 4484123) B4484123
theorem B1992943 : Blo 1991435 1992943 := bstep (se 1 (by rfl) ⟨1494707, by rfl⟩ : syracuseStep 1992943 = 2989415) B2989415
theorem B2989421 : Blo 1991435 2989421 := bbase (se 3 (by rfl) ⟨560516, by rfl⟩ : syracuseStep 2989421 = 1121033) (by norm_num)
theorem B1992947 : Blo 1991435 1992947 := bstep (se 1 (by rfl) ⟨1494710, by rfl⟩ : syracuseStep 1992947 = 2989421) B2989421
theorem B4484141 : Blo 1991435 4484141 := bbase (se 3 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 4484141 = 1681553) (by norm_num)
theorem B2989427 : Blo 1991435 2989427 := bstep (se 1 (by rfl) ⟨2242070, by rfl⟩ : syracuseStep 2989427 = 4484141) B4484141
theorem B1992951 : Blo 1991435 1992951 := bstep (se 1 (by rfl) ⟨1494713, by rfl⟩ : syracuseStep 1992951 = 2989427) B2989427
theorem B3591373 : Blo 1991435 3591373 := bbase (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) (by norm_num)
theorem B4788497 : Blo 1991435 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B12769325 : Blo 1991435 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B8512883 : Blo 1991435 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B5675255 : Blo 1991435 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B3783503 : Blo 1991435 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B2522335 : Blo 1991435 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B3363113 : Blo 1991435 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B2242075 : Blo 1991435 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B2989433 : Blo 1991435 2989433 := bstep (se 2 (by rfl) ⟨1121037, by rfl⟩ : syracuseStep 2989433 = 2242075) B2242075
theorem B1992955 : Blo 1991435 1992955 := bstep (se 1 (by rfl) ⟨1494716, by rfl⟩ : syracuseStep 1992955 = 2989433) B2989433
theorem B4545341 : Blo 1991435 4545341 := bbase (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) (by norm_num)
theorem B3030227 : Blo 1991435 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B2020151 : Blo 1991435 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B5387069 : Blo 1991435 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B3591379 : Blo 1991435 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B4788505 : Blo 1991435 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B6384673 : Blo 1991435 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B34051589 : Blo 1991435 34051589 := bstep (se 4 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 34051589 = 6384673) B6384673
theorem B22701059 : Blo 1991435 22701059 := bstep (se 1 (by rfl) ⟨17025794, by rfl⟩ : syracuseStep 22701059 = 34051589) B34051589
theorem B15134039 : Blo 1991435 15134039 := bstep (se 1 (by rfl) ⟨11350529, by rfl⟩ : syracuseStep 15134039 = 22701059) B22701059
theorem B10089359 : Blo 1991435 10089359 := bstep (se 1 (by rfl) ⟨7567019, by rfl⟩ : syracuseStep 10089359 = 15134039) B15134039
theorem B6726239 : Blo 1991435 6726239 := bstep (se 1 (by rfl) ⟨5044679, by rfl⟩ : syracuseStep 6726239 = 10089359) B10089359
theorem B4484159 : Blo 1991435 4484159 := bstep (se 1 (by rfl) ⟨3363119, by rfl⟩ : syracuseStep 4484159 = 6726239) B6726239
theorem B2989439 : Blo 1991435 2989439 := bstep (se 1 (by rfl) ⟨2242079, by rfl⟩ : syracuseStep 2989439 = 4484159) B4484159
theorem B1992959 : Blo 1991435 1992959 := bstep (se 1 (by rfl) ⟨1494719, by rfl⟩ : syracuseStep 1992959 = 2989439) B2989439
theorem B2989445 : Blo 1991435 2989445 := bbase (se 4 (by rfl) ⟨280260, by rfl⟩ : syracuseStep 2989445 = 560521) (by norm_num)
theorem B1992963 : Blo 1991435 1992963 := bstep (se 1 (by rfl) ⟨1494722, by rfl⟩ : syracuseStep 1992963 = 2989445) B2989445
theorem B3363133 : Blo 1991435 3363133 := bbase (se 3 (by rfl) ⟨630587, by rfl⟩ : syracuseStep 3363133 = 1261175) (by norm_num)
theorem B4484177 : Blo 1991435 4484177 := bstep (se 2 (by rfl) ⟨1681566, by rfl⟩ : syracuseStep 4484177 = 3363133) B3363133
theorem B2989451 : Blo 1991435 2989451 := bstep (se 1 (by rfl) ⟨2242088, by rfl⟩ : syracuseStep 2989451 = 4484177) B4484177
theorem B1992967 : Blo 1991435 1992967 := bstep (se 1 (by rfl) ⟨1494725, by rfl⟩ : syracuseStep 1992967 = 2989451) B2989451
theorem B2242093 : Blo 1991435 2242093 := bbase (se 3 (by rfl) ⟨420392, by rfl⟩ : syracuseStep 2242093 = 840785) (by norm_num)
theorem B2989457 : Blo 1991435 2989457 := bstep (se 2 (by rfl) ⟨1121046, by rfl⟩ : syracuseStep 2989457 = 2242093) B2242093
theorem B1992971 : Blo 1991435 1992971 := bstep (se 1 (by rfl) ⟨1494728, by rfl⟩ : syracuseStep 1992971 = 2989457) B2989457
theorem B6726293 : Blo 1991435 6726293 := bbase (se 6 (by rfl) ⟨157647, by rfl⟩ : syracuseStep 6726293 = 315295) (by norm_num)
theorem B4484195 : Blo 1991435 4484195 := bstep (se 1 (by rfl) ⟨3363146, by rfl⟩ : syracuseStep 4484195 = 6726293) B6726293
theorem B2989463 : Blo 1991435 2989463 := bstep (se 1 (by rfl) ⟨2242097, by rfl⟩ : syracuseStep 2989463 = 4484195) B4484195
theorem B1992975 : Blo 1991435 1992975 := bstep (se 1 (by rfl) ⟨1494731, by rfl⟩ : syracuseStep 1992975 = 2989463) B2989463
theorem B2989469 : Blo 1991435 2989469 := bbase (se 3 (by rfl) ⟨560525, by rfl⟩ : syracuseStep 2989469 = 1121051) (by norm_num)
theorem B1992979 : Blo 1991435 1992979 := bstep (se 1 (by rfl) ⟨1494734, by rfl⟩ : syracuseStep 1992979 = 2989469) B2989469
theorem B4484213 : Blo 1991435 4484213 := bbase (se 5 (by rfl) ⟨210197, by rfl⟩ : syracuseStep 4484213 = 420395) (by norm_num)
theorem B2989475 : Blo 1991435 2989475 := bstep (se 1 (by rfl) ⟨2242106, by rfl⟩ : syracuseStep 2989475 = 4484213) B4484213
theorem B1992983 : Blo 1991435 1992983 := bstep (se 1 (by rfl) ⟨1494737, by rfl⟩ : syracuseStep 1992983 = 2989475) B2989475
theorem B17026037 : Blo 1991435 17026037 := bbase (se 5 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 17026037 = 1596191) (by norm_num)
theorem B11350691 : Blo 1991435 11350691 := bstep (se 1 (by rfl) ⟨8513018, by rfl⟩ : syracuseStep 11350691 = 17026037) B17026037
theorem B7567127 : Blo 1991435 7567127 := bstep (se 1 (by rfl) ⟨5675345, by rfl⟩ : syracuseStep 7567127 = 11350691) B11350691
theorem B5044751 : Blo 1991435 5044751 := bstep (se 1 (by rfl) ⟨3783563, by rfl⟩ : syracuseStep 5044751 = 7567127) B7567127
theorem B3363167 : Blo 1991435 3363167 := bstep (se 1 (by rfl) ⟨2522375, by rfl⟩ : syracuseStep 3363167 = 5044751) B5044751
theorem B2242111 : Blo 1991435 2242111 := bstep (se 1 (by rfl) ⟨1681583, by rfl⟩ : syracuseStep 2242111 = 3363167) B3363167
theorem B2989481 : Blo 1991435 2989481 := bstep (se 2 (by rfl) ⟨1121055, by rfl⟩ : syracuseStep 2989481 = 2242111) B2242111
theorem B1992987 : Blo 1991435 1992987 := bstep (se 1 (by rfl) ⟨1494740, by rfl⟩ : syracuseStep 1992987 = 2989481) B2989481
theorem B7567141 : Blo 1991435 7567141 := bbase (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) (by norm_num)
theorem B10089521 : Blo 1991435 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B6726347 : Blo 1991435 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B4484231 : Blo 1991435 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B2989487 : Blo 1991435 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B1992991 : Blo 1991435 1992991 := bstep (se 1 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 1992991 = 2989487) B2989487
theorem B2989493 : Blo 1991435 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1992995 : Blo 1991435 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B5044781 : Blo 1991435 5044781 := bbase (se 3 (by rfl) ⟨945896, by rfl⟩ : syracuseStep 5044781 = 1891793) (by norm_num)
theorem B3363187 : Blo 1991435 3363187 := bstep (se 1 (by rfl) ⟨2522390, by rfl⟩ : syracuseStep 3363187 = 5044781) B5044781
theorem B4484249 : Blo 1991435 4484249 := bstep (se 2 (by rfl) ⟨1681593, by rfl⟩ : syracuseStep 4484249 = 3363187) B3363187
theorem B2989499 : Blo 1991435 2989499 := bstep (se 1 (by rfl) ⟨2242124, by rfl⟩ : syracuseStep 2989499 = 4484249) B4484249
theorem B1992999 : Blo 1991435 1992999 := bstep (se 1 (by rfl) ⟨1494749, by rfl⟩ : syracuseStep 1992999 = 2989499) B2989499
theorem B2242129 : Blo 1991435 2242129 := bbase (se 2 (by rfl) ⟨840798, by rfl⟩ : syracuseStep 2242129 = 1681597) (by norm_num)
theorem B2989505 : Blo 1991435 2989505 := bstep (se 2 (by rfl) ⟨1121064, by rfl⟩ : syracuseStep 2989505 = 2242129) B2242129
theorem B1993003 : Blo 1991435 1993003 := bstep (se 1 (by rfl) ⟨1494752, by rfl⟩ : syracuseStep 1993003 = 2989505) B2989505
theorem B2837701 : Blo 1991435 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B3783601 : Blo 1991435 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B5044801 : Blo 1991435 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B6726401 : Blo 1991435 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B4484267 : Blo 1991435 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B2989511 : Blo 1991435 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B1993007 : Blo 1991435 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B2989517 : Blo 1991435 2989517 := bbase (se 3 (by rfl) ⟨560534, by rfl⟩ : syracuseStep 2989517 = 1121069) (by norm_num)
theorem B1993011 : Blo 1991435 1993011 := bstep (se 1 (by rfl) ⟨1494758, by rfl⟩ : syracuseStep 1993011 = 2989517) B2989517
theorem B4484285 : Blo 1991435 4484285 := bbase (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) (by norm_num)
theorem B2989523 : Blo 1991435 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B1993015 : Blo 1991435 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B3363221 : Blo 1991435 3363221 := bbase (se 6 (by rfl) ⟨78825, by rfl⟩ : syracuseStep 3363221 = 157651) (by norm_num)
theorem B2242147 : Blo 1991435 2242147 := bstep (se 1 (by rfl) ⟨1681610, by rfl⟩ : syracuseStep 2242147 = 3363221) B3363221
theorem B2989529 : Blo 1991435 2989529 := bstep (se 2 (by rfl) ⟨1121073, by rfl⟩ : syracuseStep 2989529 = 2242147) B2242147
theorem B1993019 : Blo 1991435 1993019 := bstep (se 1 (by rfl) ⟨1494764, by rfl⟩ : syracuseStep 1993019 = 2989529) B2989529
theorem B2693621 : Blo 1991435 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B7182989 : Blo 1991435 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B4788659 : Blo 1991435 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B12769757 : Blo 1991435 12769757 := bstep (se 3 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 12769757 = 4788659) B4788659
theorem B8513171 : Blo 1991435 8513171 := bstep (se 1 (by rfl) ⟨6384878, by rfl⟩ : syracuseStep 8513171 = 12769757) B12769757
theorem B5675447 : Blo 1991435 5675447 := bstep (se 1 (by rfl) ⟨4256585, by rfl⟩ : syracuseStep 5675447 = 8513171) B8513171
theorem B15134525 : Blo 1991435 15134525 := bstep (se 3 (by rfl) ⟨2837723, by rfl⟩ : syracuseStep 15134525 = 5675447) B5675447
theorem B10089683 : Blo 1991435 10089683 := bstep (se 1 (by rfl) ⟨7567262, by rfl⟩ : syracuseStep 10089683 = 15134525) B15134525
theorem B6726455 : Blo 1991435 6726455 := bstep (se 1 (by rfl) ⟨5044841, by rfl⟩ : syracuseStep 6726455 = 10089683) B10089683
theorem B4484303 : Blo 1991435 4484303 := bstep (se 1 (by rfl) ⟨3363227, by rfl⟩ : syracuseStep 4484303 = 6726455) B6726455
theorem B2989535 : Blo 1991435 2989535 := bstep (se 1 (by rfl) ⟨2242151, by rfl⟩ : syracuseStep 2989535 = 4484303) B4484303
theorem B1993023 : Blo 1991435 1993023 := bstep (se 1 (by rfl) ⟨1494767, by rfl⟩ : syracuseStep 1993023 = 2989535) B2989535
theorem B2989541 : Blo 1991435 2989541 := bbase (se 4 (by rfl) ⟨280269, by rfl⟩ : syracuseStep 2989541 = 560539) (by norm_num)
theorem B1993027 : Blo 1991435 1993027 := bstep (se 1 (by rfl) ⟨1494770, by rfl⟩ : syracuseStep 1993027 = 2989541) B2989541
theorem B6472021 : Blo 1991435 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B8629361 : Blo 1991435 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B5752907 : Blo 1991435 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B3835271 : Blo 1991435 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B2556847 : Blo 1991435 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B3409129 : Blo 1991435 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B4545505 : Blo 1991435 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B6060673 : Blo 1991435 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B8080897 : Blo 1991435 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B10774529 : Blo 1991435 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B7183019 : Blo 1991435 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B19154717 : Blo 1991435 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B12769811 : Blo 1991435 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B8513207 : Blo 1991435 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B5675471 : Blo 1991435 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B3783647 : Blo 1991435 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B2522431 : Blo 1991435 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B3363241 : Blo 1991435 3363241 := bstep (se 2 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 3363241 = 2522431) B2522431
theorem B4484321 : Blo 1991435 4484321 := bstep (se 2 (by rfl) ⟨1681620, by rfl⟩ : syracuseStep 4484321 = 3363241) B3363241
theorem B2989547 : Blo 1991435 2989547 := bstep (se 1 (by rfl) ⟨2242160, by rfl⟩ : syracuseStep 2989547 = 4484321) B4484321
theorem B1993031 : Blo 1991435 1993031 := bstep (se 1 (by rfl) ⟨1494773, by rfl⟩ : syracuseStep 1993031 = 2989547) B2989547
theorem B2242165 : Blo 1991435 2242165 := bbase (se 5 (by rfl) ⟨105101, by rfl⟩ : syracuseStep 2242165 = 210203) (by norm_num)
theorem B2989553 : Blo 1991435 2989553 := bstep (se 2 (by rfl) ⟨1121082, by rfl⟩ : syracuseStep 2989553 = 2242165) B2242165
theorem B1993035 : Blo 1991435 1993035 := bstep (se 1 (by rfl) ⟨1494776, by rfl⟩ : syracuseStep 1993035 = 2989553) B2989553
theorem B2522441 : Blo 1991435 2522441 := bbase (se 2 (by rfl) ⟨945915, by rfl⟩ : syracuseStep 2522441 = 1891831) (by norm_num)
theorem B6726509 : Blo 1991435 6726509 := bstep (se 3 (by rfl) ⟨1261220, by rfl⟩ : syracuseStep 6726509 = 2522441) B2522441
theorem B4484339 : Blo 1991435 4484339 := bstep (se 1 (by rfl) ⟨3363254, by rfl⟩ : syracuseStep 4484339 = 6726509) B6726509
theorem B2989559 : Blo 1991435 2989559 := bstep (se 1 (by rfl) ⟨2242169, by rfl⟩ : syracuseStep 2989559 = 4484339) B4484339
theorem B1993039 : Blo 1991435 1993039 := bstep (se 1 (by rfl) ⟨1494779, by rfl⟩ : syracuseStep 1993039 = 2989559) B2989559
theorem B2989565 : Blo 1991435 2989565 := bbase (se 3 (by rfl) ⟨560543, by rfl⟩ : syracuseStep 2989565 = 1121087) (by norm_num)
theorem B1993043 : Blo 1991435 1993043 := bstep (se 1 (by rfl) ⟨1494782, by rfl⟩ : syracuseStep 1993043 = 2989565) B2989565
theorem B4484357 : Blo 1991435 4484357 := bbase (se 4 (by rfl) ⟨420408, by rfl⟩ : syracuseStep 4484357 = 840817) (by norm_num)
theorem B2989571 : Blo 1991435 2989571 := bstep (se 1 (by rfl) ⟨2242178, by rfl⟩ : syracuseStep 2989571 = 4484357) B4484357
theorem B1993047 : Blo 1991435 1993047 := bstep (se 1 (by rfl) ⟨1494785, by rfl⟩ : syracuseStep 1993047 = 2989571) B2989571
theorem B3783685 : Blo 1991435 3783685 := bbase (se 4 (by rfl) ⟨354720, by rfl⟩ : syracuseStep 3783685 = 709441) (by norm_num)
theorem B5044913 : Blo 1991435 5044913 := bstep (se 2 (by rfl) ⟨1891842, by rfl⟩ : syracuseStep 5044913 = 3783685) B3783685
theorem B3363275 : Blo 1991435 3363275 := bstep (se 1 (by rfl) ⟨2522456, by rfl⟩ : syracuseStep 3363275 = 5044913) B5044913
theorem B2242183 : Blo 1991435 2242183 := bstep (se 1 (by rfl) ⟨1681637, by rfl⟩ : syracuseStep 2242183 = 3363275) B3363275
theorem B2989577 : Blo 1991435 2989577 := bstep (se 2 (by rfl) ⟨1121091, by rfl⟩ : syracuseStep 2989577 = 2242183) B2242183
theorem B1993051 : Blo 1991435 1993051 := bstep (se 1 (by rfl) ⟨1494788, by rfl⟩ : syracuseStep 1993051 = 2989577) B2989577
theorem B10089845 : Blo 1991435 10089845 := bbase (se 5 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 10089845 = 945923) (by norm_num)
theorem B6726563 : Blo 1991435 6726563 := bstep (se 1 (by rfl) ⟨5044922, by rfl⟩ : syracuseStep 6726563 = 10089845) B10089845
theorem B4484375 : Blo 1991435 4484375 := bstep (se 1 (by rfl) ⟨3363281, by rfl⟩ : syracuseStep 4484375 = 6726563) B6726563
theorem B2989583 : Blo 1991435 2989583 := bstep (se 1 (by rfl) ⟨2242187, by rfl⟩ : syracuseStep 2989583 = 4484375) B4484375
theorem B1993055 : Blo 1991435 1993055 := bstep (se 1 (by rfl) ⟨1494791, by rfl⟩ : syracuseStep 1993055 = 2989583) B2989583
theorem B2989589 : Blo 1991435 2989589 := bbase (se 6 (by rfl) ⟨70068, by rfl⟩ : syracuseStep 2989589 = 140137) (by norm_num)
theorem B1993059 : Blo 1991435 1993059 := bstep (se 1 (by rfl) ⟨1494794, by rfl⟩ : syracuseStep 1993059 = 2989589) B2989589
theorem B12944245 : Blo 1991435 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B17258993 : Blo 1991435 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B11505995 : Blo 1991435 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B7670663 : Blo 1991435 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B5113775 : Blo 1991435 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B3409183 : Blo 1991435 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B4545577 : Blo 1991435 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B24243077 : Blo 1991435 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B16162051 : Blo 1991435 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B21549401 : Blo 1991435 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B14366267 : Blo 1991435 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B9577511 : Blo 1991435 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B6385007 : Blo 1991435 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B17026685 : Blo 1991435 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B11351123 : Blo 1991435 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B7567415 : Blo 1991435 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B5044943 : Blo 1991435 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B3363295 : Blo 1991435 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B4484393 : Blo 1991435 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B2989595 : Blo 1991435 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B1993063 : Blo 1991435 1993063 := bstep (se 1 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 1993063 = 2989595) B2989595
theorem B2242201 : Blo 1991435 2242201 := bbase (se 2 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 2242201 = 1681651) (by norm_num)
theorem B2989601 : Blo 1991435 2989601 := bstep (se 2 (by rfl) ⟨1121100, by rfl⟩ : syracuseStep 2989601 = 2242201) B2242201
theorem B1993067 : Blo 1991435 1993067 := bstep (se 1 (by rfl) ⟨1494800, by rfl⟩ : syracuseStep 1993067 = 2989601) B2989601
theorem B7567445 : Blo 1991435 7567445 := bbase (se 8 (by rfl) ⟨44340, by rfl⟩ : syracuseStep 7567445 = 88681) (by norm_num)
theorem B5044963 : Blo 1991435 5044963 := bstep (se 1 (by rfl) ⟨3783722, by rfl⟩ : syracuseStep 5044963 = 7567445) B7567445
theorem B6726617 : Blo 1991435 6726617 := bstep (se 2 (by rfl) ⟨2522481, by rfl⟩ : syracuseStep 6726617 = 5044963) B5044963
theorem B4484411 : Blo 1991435 4484411 := bstep (se 1 (by rfl) ⟨3363308, by rfl⟩ : syracuseStep 4484411 = 6726617) B6726617
theorem B2989607 : Blo 1991435 2989607 := bstep (se 1 (by rfl) ⟨2242205, by rfl⟩ : syracuseStep 2989607 = 4484411) B4484411
theorem B1993071 : Blo 1991435 1993071 := bstep (se 1 (by rfl) ⟨1494803, by rfl⟩ : syracuseStep 1993071 = 2989607) B2989607
theorem B2989613 : Blo 1991435 2989613 := bbase (se 3 (by rfl) ⟨560552, by rfl⟩ : syracuseStep 2989613 = 1121105) (by norm_num)
theorem B1993075 : Blo 1991435 1993075 := bstep (se 1 (by rfl) ⟨1494806, by rfl⟩ : syracuseStep 1993075 = 2989613) B2989613
theorem B4484429 : Blo 1991435 4484429 := bbase (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) (by norm_num)
theorem B2989619 : Blo 1991435 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B1993079 : Blo 1991435 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B2522497 : Blo 1991435 2522497 := bbase (se 2 (by rfl) ⟨945936, by rfl⟩ : syracuseStep 2522497 = 1891873) (by norm_num)
theorem B3363329 : Blo 1991435 3363329 := bstep (se 2 (by rfl) ⟨1261248, by rfl⟩ : syracuseStep 3363329 = 2522497) B2522497
theorem B2242219 : Blo 1991435 2242219 := bstep (se 1 (by rfl) ⟨1681664, by rfl⟩ : syracuseStep 2242219 = 3363329) B3363329
theorem B2989625 : Blo 1991435 2989625 := bstep (se 2 (by rfl) ⟨1121109, by rfl⟩ : syracuseStep 2989625 = 2242219) B2242219
theorem B1993083 : Blo 1991435 1993083 := bstep (se 1 (by rfl) ⟨1494812, by rfl⟩ : syracuseStep 1993083 = 2989625) B2989625
theorem B2128361 : Blo 1991435 2128361 := bbase (se 2 (by rfl) ⟨798135, by rfl⟩ : syracuseStep 2128361 = 1596271) (by norm_num)
theorem B22702517 : Blo 1991435 22702517 := bstep (se 5 (by rfl) ⟨1064180, by rfl⟩ : syracuseStep 22702517 = 2128361) B2128361
theorem B15135011 : Blo 1991435 15135011 := bstep (se 1 (by rfl) ⟨11351258, by rfl⟩ : syracuseStep 15135011 = 22702517) B22702517
theorem B10090007 : Blo 1991435 10090007 := bstep (se 1 (by rfl) ⟨7567505, by rfl⟩ : syracuseStep 10090007 = 15135011) B15135011
theorem B6726671 : Blo 1991435 6726671 := bstep (se 1 (by rfl) ⟨5045003, by rfl⟩ : syracuseStep 6726671 = 10090007) B10090007
theorem B4484447 : Blo 1991435 4484447 := bstep (se 1 (by rfl) ⟨3363335, by rfl⟩ : syracuseStep 4484447 = 6726671) B6726671
theorem B2989631 : Blo 1991435 2989631 := bstep (se 1 (by rfl) ⟨2242223, by rfl⟩ : syracuseStep 2989631 = 4484447) B4484447
theorem B1993087 : Blo 1991435 1993087 := bstep (se 1 (by rfl) ⟨1494815, by rfl⟩ : syracuseStep 1993087 = 2989631) B2989631
theorem B2989637 : Blo 1991435 2989637 := bbase (se 4 (by rfl) ⟨280278, by rfl⟩ : syracuseStep 2989637 = 560557) (by norm_num)
theorem B1993091 : Blo 1991435 1993091 := bstep (se 1 (by rfl) ⟨1494818, by rfl⟩ : syracuseStep 1993091 = 2989637) B2989637
theorem B3363349 : Blo 1991435 3363349 := bbase (se 6 (by rfl) ⟨78828, by rfl⟩ : syracuseStep 3363349 = 157657) (by norm_num)
theorem B4484465 : Blo 1991435 4484465 := bstep (se 2 (by rfl) ⟨1681674, by rfl⟩ : syracuseStep 4484465 = 3363349) B3363349
theorem B2989643 : Blo 1991435 2989643 := bstep (se 1 (by rfl) ⟨2242232, by rfl⟩ : syracuseStep 2989643 = 4484465) B4484465
theorem B1993095 : Blo 1991435 1993095 := bstep (se 1 (by rfl) ⟨1494821, by rfl⟩ : syracuseStep 1993095 = 2989643) B2989643
theorem B2242237 : Blo 1991435 2242237 := bbase (se 3 (by rfl) ⟨420419, by rfl⟩ : syracuseStep 2242237 = 840839) (by norm_num)
theorem B2989649 : Blo 1991435 2989649 := bstep (se 2 (by rfl) ⟨1121118, by rfl⟩ : syracuseStep 2989649 = 2242237) B2242237
theorem B1993099 : Blo 1991435 1993099 := bstep (se 1 (by rfl) ⟨1494824, by rfl⟩ : syracuseStep 1993099 = 2989649) B2989649
theorem B6726725 : Blo 1991435 6726725 := bbase (se 4 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 6726725 = 1261261) (by norm_num)
theorem B4484483 : Blo 1991435 4484483 := bstep (se 1 (by rfl) ⟨3363362, by rfl⟩ : syracuseStep 4484483 = 6726725) B6726725
theorem B2989655 : Blo 1991435 2989655 := bstep (se 1 (by rfl) ⟨2242241, by rfl⟩ : syracuseStep 2989655 = 4484483) B4484483
theorem B1993103 : Blo 1991435 1993103 := bstep (se 1 (by rfl) ⟨1494827, by rfl⟩ : syracuseStep 1993103 = 2989655) B2989655
theorem B2989661 : Blo 1991435 2989661 := bbase (se 3 (by rfl) ⟨560561, by rfl⟩ : syracuseStep 2989661 = 1121123) (by norm_num)
theorem B1993107 : Blo 1991435 1993107 := bstep (se 1 (by rfl) ⟨1494830, by rfl⟩ : syracuseStep 1993107 = 2989661) B2989661
theorem B4484501 : Blo 1991435 4484501 := bbase (se 6 (by rfl) ⟨105105, by rfl⟩ : syracuseStep 4484501 = 210211) (by norm_num)
theorem B2989667 : Blo 1991435 2989667 := bstep (se 1 (by rfl) ⟨2242250, by rfl⟩ : syracuseStep 2989667 = 4484501) B4484501
theorem B1993111 : Blo 1991435 1993111 := bstep (se 1 (by rfl) ⟨1494833, by rfl⟩ : syracuseStep 1993111 = 2989667) B2989667
theorem B14366645 : Blo 1991435 14366645 := bbase (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) (by norm_num)
theorem B9577763 : Blo 1991435 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B6385175 : Blo 1991435 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B4256783 : Blo 1991435 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B2837855 : Blo 1991435 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B7567613 : Blo 1991435 7567613 := bstep (se 3 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 7567613 = 2837855) B2837855
theorem B5045075 : Blo 1991435 5045075 := bstep (se 1 (by rfl) ⟨3783806, by rfl⟩ : syracuseStep 5045075 = 7567613) B7567613
theorem B3363383 : Blo 1991435 3363383 := bstep (se 1 (by rfl) ⟨2522537, by rfl⟩ : syracuseStep 3363383 = 5045075) B5045075
theorem B2242255 : Blo 1991435 2242255 := bstep (se 1 (by rfl) ⟨1681691, by rfl⟩ : syracuseStep 2242255 = 3363383) B3363383
theorem B2989673 : Blo 1991435 2989673 := bstep (se 2 (by rfl) ⟨1121127, by rfl⟩ : syracuseStep 2989673 = 2242255) B2242255
theorem B1993115 : Blo 1991435 1993115 := bstep (se 1 (by rfl) ⟨1494836, by rfl⟩ : syracuseStep 1993115 = 2989673) B2989673
theorem B2394445 : Blo 1991435 2394445 := bbase (se 3 (by rfl) ⟨448958, by rfl⟩ : syracuseStep 2394445 = 897917) (by norm_num)
theorem B3192593 : Blo 1991435 3192593 := bstep (se 2 (by rfl) ⟨1197222, by rfl⟩ : syracuseStep 3192593 = 2394445) B2394445
theorem B8513581 : Blo 1991435 8513581 := bstep (se 3 (by rfl) ⟨1596296, by rfl⟩ : syracuseStep 8513581 = 3192593) B3192593
theorem B11351441 : Blo 1991435 11351441 := bstep (se 2 (by rfl) ⟨4256790, by rfl⟩ : syracuseStep 11351441 = 8513581) B8513581
theorem B7567627 : Blo 1991435 7567627 := bstep (se 1 (by rfl) ⟨5675720, by rfl⟩ : syracuseStep 7567627 = 11351441) B11351441
theorem B10090169 : Blo 1991435 10090169 := bstep (se 2 (by rfl) ⟨3783813, by rfl⟩ : syracuseStep 10090169 = 7567627) B7567627
theorem B6726779 : Blo 1991435 6726779 := bstep (se 1 (by rfl) ⟨5045084, by rfl⟩ : syracuseStep 6726779 = 10090169) B10090169
theorem B4484519 : Blo 1991435 4484519 := bstep (se 1 (by rfl) ⟨3363389, by rfl⟩ : syracuseStep 4484519 = 6726779) B6726779
theorem B2989679 : Blo 1991435 2989679 := bstep (se 1 (by rfl) ⟨2242259, by rfl⟩ : syracuseStep 2989679 = 4484519) B4484519
theorem B1993119 : Blo 1991435 1993119 := bstep (se 1 (by rfl) ⟨1494839, by rfl⟩ : syracuseStep 1993119 = 2989679) B2989679
theorem B2989685 : Blo 1991435 2989685 := bbase (se 5 (by rfl) ⟨140141, by rfl⟩ : syracuseStep 2989685 = 280283) (by norm_num)
theorem B1993123 : Blo 1991435 1993123 := bstep (se 1 (by rfl) ⟨1494842, by rfl⟩ : syracuseStep 1993123 = 2989685) B2989685
theorem B3783829 : Blo 1991435 3783829 := bbase (se 6 (by rfl) ⟨88683, by rfl⟩ : syracuseStep 3783829 = 177367) (by norm_num)
theorem B5045105 : Blo 1991435 5045105 := bstep (se 2 (by rfl) ⟨1891914, by rfl⟩ : syracuseStep 5045105 = 3783829) B3783829
theorem B3363403 : Blo 1991435 3363403 := bstep (se 1 (by rfl) ⟨2522552, by rfl⟩ : syracuseStep 3363403 = 5045105) B5045105
theorem B4484537 : Blo 1991435 4484537 := bstep (se 2 (by rfl) ⟨1681701, by rfl⟩ : syracuseStep 4484537 = 3363403) B3363403
theorem B2989691 : Blo 1991435 2989691 := bstep (se 1 (by rfl) ⟨2242268, by rfl⟩ : syracuseStep 2989691 = 4484537) B4484537
theorem B1993127 : Blo 1991435 1993127 := bstep (se 1 (by rfl) ⟨1494845, by rfl⟩ : syracuseStep 1993127 = 2989691) B2989691
theorem B2242273 : Blo 1991435 2242273 := bbase (se 2 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 2242273 = 1681705) (by norm_num)
theorem B2989697 : Blo 1991435 2989697 := bstep (se 2 (by rfl) ⟨1121136, by rfl⟩ : syracuseStep 2989697 = 2242273) B2242273
theorem B1993131 : Blo 1991435 1993131 := bstep (se 1 (by rfl) ⟨1494848, by rfl⟩ : syracuseStep 1993131 = 2989697) B2989697
theorem B5045125 : Blo 1991435 5045125 := bbase (se 4 (by rfl) ⟨472980, by rfl⟩ : syracuseStep 5045125 = 945961) (by norm_num)
theorem B6726833 : Blo 1991435 6726833 := bstep (se 2 (by rfl) ⟨2522562, by rfl⟩ : syracuseStep 6726833 = 5045125) B5045125
theorem B4484555 : Blo 1991435 4484555 := bstep (se 1 (by rfl) ⟨3363416, by rfl⟩ : syracuseStep 4484555 = 6726833) B6726833
theorem B2989703 : Blo 1991435 2989703 := bstep (se 1 (by rfl) ⟨2242277, by rfl⟩ : syracuseStep 2989703 = 4484555) B4484555
theorem B1993135 : Blo 1991435 1993135 := bstep (se 1 (by rfl) ⟨1494851, by rfl⟩ : syracuseStep 1993135 = 2989703) B2989703
theorem B2989709 : Blo 1991435 2989709 := bbase (se 3 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 2989709 = 1121141) (by norm_num)
theorem B1993139 : Blo 1991435 1993139 := bstep (se 1 (by rfl) ⟨1494854, by rfl⟩ : syracuseStep 1993139 = 2989709) B2989709
theorem B4484573 : Blo 1991435 4484573 := bbase (se 3 (by rfl) ⟨840857, by rfl⟩ : syracuseStep 4484573 = 1681715) (by norm_num)
theorem B2989715 : Blo 1991435 2989715 := bstep (se 1 (by rfl) ⟨2242286, by rfl⟩ : syracuseStep 2989715 = 4484573) B4484573
theorem B1993143 : Blo 1991435 1993143 := bstep (se 1 (by rfl) ⟨1494857, by rfl⟩ : syracuseStep 1993143 = 2989715) B2989715
theorem B3363437 : Blo 1991435 3363437 := bbase (se 3 (by rfl) ⟨630644, by rfl⟩ : syracuseStep 3363437 = 1261289) (by norm_num)
theorem B2242291 : Blo 1991435 2242291 := bstep (se 1 (by rfl) ⟨1681718, by rfl⟩ : syracuseStep 2242291 = 3363437) B3363437
theorem B2989721 : Blo 1991435 2989721 := bstep (se 2 (by rfl) ⟨1121145, by rfl⟩ : syracuseStep 2989721 = 2242291) B2242291
theorem B1993147 : Blo 1991435 1993147 := bstep (se 1 (by rfl) ⟨1494860, by rfl⟩ : syracuseStep 1993147 = 2989721) B2989721
theorem B8081381 : Blo 1991435 8081381 := bbase (se 4 (by rfl) ⟨757629, by rfl⟩ : syracuseStep 8081381 = 1515259) (by norm_num)
theorem B21550349 : Blo 1991435 21550349 := bstep (se 3 (by rfl) ⟨4040690, by rfl⟩ : syracuseStep 21550349 = 8081381) B8081381
theorem B14366899 : Blo 1991435 14366899 := bstep (se 1 (by rfl) ⟨10775174, by rfl⟩ : syracuseStep 14366899 = 21550349) B21550349
theorem B19155865 : Blo 1991435 19155865 := bstep (se 2 (by rfl) ⟨7183449, by rfl⟩ : syracuseStep 19155865 = 14366899) B14366899
theorem B25541153 : Blo 1991435 25541153 := bstep (se 2 (by rfl) ⟨9577932, by rfl⟩ : syracuseStep 25541153 = 19155865) B19155865
theorem B17027435 : Blo 1991435 17027435 := bstep (se 1 (by rfl) ⟨12770576, by rfl⟩ : syracuseStep 17027435 = 25541153) B25541153
theorem B11351623 : Blo 1991435 11351623 := bstep (se 1 (by rfl) ⟨8513717, by rfl⟩ : syracuseStep 11351623 = 17027435) B17027435
theorem B15135497 : Blo 1991435 15135497 := bstep (se 2 (by rfl) ⟨5675811, by rfl⟩ : syracuseStep 15135497 = 11351623) B11351623
theorem B10090331 : Blo 1991435 10090331 := bstep (se 1 (by rfl) ⟨7567748, by rfl⟩ : syracuseStep 10090331 = 15135497) B15135497
theorem B6726887 : Blo 1991435 6726887 := bstep (se 1 (by rfl) ⟨5045165, by rfl⟩ : syracuseStep 6726887 = 10090331) B10090331
theorem B4484591 : Blo 1991435 4484591 := bstep (se 1 (by rfl) ⟨3363443, by rfl⟩ : syracuseStep 4484591 = 6726887) B6726887
theorem B2989727 : Blo 1991435 2989727 := bstep (se 1 (by rfl) ⟨2242295, by rfl⟩ : syracuseStep 2989727 = 4484591) B4484591
theorem B1993151 : Blo 1991435 1993151 := bstep (se 1 (by rfl) ⟨1494863, by rfl⟩ : syracuseStep 1993151 = 2989727) B2989727
theorem B2989733 : Blo 1991435 2989733 := bbase (se 4 (by rfl) ⟨280287, by rfl⟩ : syracuseStep 2989733 = 560575) (by norm_num)
theorem B1993155 : Blo 1991435 1993155 := bstep (se 1 (by rfl) ⟨1494866, by rfl⟩ : syracuseStep 1993155 = 2989733) B2989733
theorem B2522593 : Blo 1991435 2522593 := bbase (se 2 (by rfl) ⟨945972, by rfl⟩ : syracuseStep 2522593 = 1891945) (by norm_num)
theorem B3363457 : Blo 1991435 3363457 := bstep (se 2 (by rfl) ⟨1261296, by rfl⟩ : syracuseStep 3363457 = 2522593) B2522593
theorem B4484609 : Blo 1991435 4484609 := bstep (se 2 (by rfl) ⟨1681728, by rfl⟩ : syracuseStep 4484609 = 3363457) B3363457
theorem B2989739 : Blo 1991435 2989739 := bstep (se 1 (by rfl) ⟨2242304, by rfl⟩ : syracuseStep 2989739 = 4484609) B4484609
theorem B1993159 : Blo 1991435 1993159 := bstep (se 1 (by rfl) ⟨1494869, by rfl⟩ : syracuseStep 1993159 = 2989739) B2989739
theorem B2242309 : Blo 1991435 2242309 := bbase (se 4 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 2242309 = 420433) (by norm_num)
theorem B2989745 : Blo 1991435 2989745 := bstep (se 2 (by rfl) ⟨1121154, by rfl⟩ : syracuseStep 2989745 = 2242309) B2242309
theorem B1993163 : Blo 1991435 1993163 := bstep (se 1 (by rfl) ⟨1494872, by rfl⟩ : syracuseStep 1993163 = 2989745) B2989745
theorem B16162901 : Blo 1991435 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B10775267 : Blo 1991435 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B7183511 : Blo 1991435 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B4789007 : Blo 1991435 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B3192671 : Blo 1991435 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B2128447 : Blo 1991435 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B2837929 : Blo 1991435 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B3783905 : Blo 1991435 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B2522603 : Blo 1991435 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B6726941 : Blo 1991435 6726941 := bstep (se 3 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 6726941 = 2522603) B2522603
theorem B4484627 : Blo 1991435 4484627 := bstep (se 1 (by rfl) ⟨3363470, by rfl⟩ : syracuseStep 4484627 = 6726941) B6726941
theorem B2989751 : Blo 1991435 2989751 := bstep (se 1 (by rfl) ⟨2242313, by rfl⟩ : syracuseStep 2989751 = 4484627) B4484627
theorem B1993167 : Blo 1991435 1993167 := bstep (se 1 (by rfl) ⟨1494875, by rfl⟩ : syracuseStep 1993167 = 2989751) B2989751
theorem B2989757 : Blo 1991435 2989757 := bbase (se 3 (by rfl) ⟨560579, by rfl⟩ : syracuseStep 2989757 = 1121159) (by norm_num)
theorem B1993171 : Blo 1991435 1993171 := bstep (se 1 (by rfl) ⟨1494878, by rfl⟩ : syracuseStep 1993171 = 2989757) B2989757
theorem B4484645 : Blo 1991435 4484645 := bbase (se 4 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 4484645 = 840871) (by norm_num)
theorem B2989763 : Blo 1991435 2989763 := bstep (se 1 (by rfl) ⟨2242322, by rfl⟩ : syracuseStep 2989763 = 4484645) B4484645
theorem B1993175 : Blo 1991435 1993175 := bstep (se 1 (by rfl) ⟨1494881, by rfl⟩ : syracuseStep 1993175 = 2989763) B2989763
theorem B5045237 : Blo 1991435 5045237 := bbase (se 5 (by rfl) ⟨236495, by rfl⟩ : syracuseStep 5045237 = 472991) (by norm_num)
theorem B3363491 : Blo 1991435 3363491 := bstep (se 1 (by rfl) ⟨2522618, by rfl⟩ : syracuseStep 3363491 = 5045237) B5045237
theorem B2242327 : Blo 1991435 2242327 := bstep (se 1 (by rfl) ⟨1681745, by rfl⟩ : syracuseStep 2242327 = 3363491) B3363491
theorem B2989769 : Blo 1991435 2989769 := bstep (se 2 (by rfl) ⟨1121163, by rfl⟩ : syracuseStep 2989769 = 2242327) B2242327
theorem B1993179 : Blo 1991435 1993179 := bstep (se 1 (by rfl) ⟨1494884, by rfl⟩ : syracuseStep 1993179 = 2989769) B2989769
theorem B3740813 : Blo 1991435 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2493875 : Blo 1991435 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B6650333 : Blo 1991435 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B4433555 : Blo 1991435 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2955703 : Blo 1991435 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B3940937 : Blo 1991435 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B42036661 : Blo 1991435 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B56048881 : Blo 1991435 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B74731841 : Blo 1991435 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B49821227 : Blo 1991435 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B33214151 : Blo 1991435 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B22142767 : Blo 1991435 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B29523689 : Blo 1991435 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B19682459 : Blo 1991435 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B13121639 : Blo 1991435 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B8747759 : Blo 1991435 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B5831839 : Blo 1991435 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B7775785 : Blo 1991435 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B10367713 : Blo 1991435 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B13823617 : Blo 1991435 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B18431489 : Blo 1991435 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B12287659 : Blo 1991435 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B16383545 : Blo 1991435 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B10922363 : Blo 1991435 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B7281575 : Blo 1991435 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B4854383 : Blo 1991435 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3236255 : Blo 1991435 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B34520053 : Blo 1991435 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B46026737 : Blo 1991435 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B30684491 : Blo 1991435 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B20456327 : Blo 1991435 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B54550205 : Blo 1991435 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B36366803 : Blo 1991435 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B24244535 : Blo 1991435 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B64652093 : Blo 1991435 64652093 := bstep (se 3 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 64652093 = 24244535) B24244535
theorem B43101395 : Blo 1991435 43101395 := bstep (se 1 (by rfl) ⟨32326046, by rfl⟩ : syracuseStep 43101395 = 64652093) B64652093
theorem B28734263 : Blo 1991435 28734263 := bstep (se 1 (by rfl) ⟨21550697, by rfl⟩ : syracuseStep 28734263 = 43101395) B43101395
theorem B19156175 : Blo 1991435 19156175 := bstep (se 1 (by rfl) ⟨14367131, by rfl⟩ : syracuseStep 19156175 = 28734263) B28734263
theorem B12770783 : Blo 1991435 12770783 := bstep (se 1 (by rfl) ⟨9578087, by rfl⟩ : syracuseStep 12770783 = 19156175) B19156175
theorem B8513855 : Blo 1991435 8513855 := bstep (se 1 (by rfl) ⟨6385391, by rfl⟩ : syracuseStep 8513855 = 12770783) B12770783
theorem B5675903 : Blo 1991435 5675903 := bstep (se 1 (by rfl) ⟨4256927, by rfl⟩ : syracuseStep 5675903 = 8513855) B8513855
theorem B3783935 : Blo 1991435 3783935 := bstep (se 1 (by rfl) ⟨2837951, by rfl⟩ : syracuseStep 3783935 = 5675903) B5675903
theorem B10090493 : Blo 1991435 10090493 := bstep (se 3 (by rfl) ⟨1891967, by rfl⟩ : syracuseStep 10090493 = 3783935) B3783935
theorem B6726995 : Blo 1991435 6726995 := bstep (se 1 (by rfl) ⟨5045246, by rfl⟩ : syracuseStep 6726995 = 10090493) B10090493
theorem B4484663 : Blo 1991435 4484663 := bstep (se 1 (by rfl) ⟨3363497, by rfl⟩ : syracuseStep 4484663 = 6726995) B6726995
theorem B2989775 : Blo 1991435 2989775 := bstep (se 1 (by rfl) ⟨2242331, by rfl⟩ : syracuseStep 2989775 = 4484663) B4484663
theorem B1993183 : Blo 1991435 1993183 := bstep (se 1 (by rfl) ⟨1494887, by rfl⟩ : syracuseStep 1993183 = 2989775) B2989775
theorem B2989781 : Blo 1991435 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B1993187 : Blo 1991435 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B3192709 : Blo 1991435 3192709 := bbase (se 4 (by rfl) ⟨299316, by rfl⟩ : syracuseStep 3192709 = 598633) (by norm_num)
theorem B4256945 : Blo 1991435 4256945 := bstep (se 2 (by rfl) ⟨1596354, by rfl⟩ : syracuseStep 4256945 = 3192709) B3192709
theorem B2837963 : Blo 1991435 2837963 := bstep (se 1 (by rfl) ⟨2128472, by rfl⟩ : syracuseStep 2837963 = 4256945) B4256945
theorem B7567901 : Blo 1991435 7567901 := bstep (se 3 (by rfl) ⟨1418981, by rfl⟩ : syracuseStep 7567901 = 2837963) B2837963
theorem B5045267 : Blo 1991435 5045267 := bstep (se 1 (by rfl) ⟨3783950, by rfl⟩ : syracuseStep 5045267 = 7567901) B7567901
theorem B3363511 : Blo 1991435 3363511 := bstep (se 1 (by rfl) ⟨2522633, by rfl⟩ : syracuseStep 3363511 = 5045267) B5045267
theorem B4484681 : Blo 1991435 4484681 := bstep (se 2 (by rfl) ⟨1681755, by rfl⟩ : syracuseStep 4484681 = 3363511) B3363511
theorem B2989787 : Blo 1991435 2989787 := bstep (se 1 (by rfl) ⟨2242340, by rfl⟩ : syracuseStep 2989787 = 4484681) B4484681
theorem B1993191 : Blo 1991435 1993191 := bstep (se 1 (by rfl) ⟨1494893, by rfl⟩ : syracuseStep 1993191 = 2989787) B2989787
theorem B2242345 : Blo 1991435 2242345 := bbase (se 2 (by rfl) ⟨840879, by rfl⟩ : syracuseStep 2242345 = 1681759) (by norm_num)
theorem B2989793 : Blo 1991435 2989793 := bstep (se 2 (by rfl) ⟨1121172, by rfl⟩ : syracuseStep 2989793 = 2242345) B2242345
theorem B1993195 : Blo 1991435 1993195 := bstep (se 1 (by rfl) ⟨1494896, by rfl⟩ : syracuseStep 1993195 = 2989793) B2989793
theorem B2394541 : Blo 1991435 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B12770885 : Blo 1991435 12770885 := bstep (se 4 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 12770885 = 2394541) B2394541
theorem B8513923 : Blo 1991435 8513923 := bstep (se 1 (by rfl) ⟨6385442, by rfl⟩ : syracuseStep 8513923 = 12770885) B12770885
theorem B11351897 : Blo 1991435 11351897 := bstep (se 2 (by rfl) ⟨4256961, by rfl⟩ : syracuseStep 11351897 = 8513923) B8513923
theorem B7567931 : Blo 1991435 7567931 := bstep (se 1 (by rfl) ⟨5675948, by rfl⟩ : syracuseStep 7567931 = 11351897) B11351897
theorem B5045287 : Blo 1991435 5045287 := bstep (se 1 (by rfl) ⟨3783965, by rfl⟩ : syracuseStep 5045287 = 7567931) B7567931
theorem B6727049 : Blo 1991435 6727049 := bstep (se 2 (by rfl) ⟨2522643, by rfl⟩ : syracuseStep 6727049 = 5045287) B5045287
theorem B4484699 : Blo 1991435 4484699 := bstep (se 1 (by rfl) ⟨3363524, by rfl⟩ : syracuseStep 4484699 = 6727049) B6727049
theorem B2989799 : Blo 1991435 2989799 := bstep (se 1 (by rfl) ⟨2242349, by rfl⟩ : syracuseStep 2989799 = 4484699) B4484699
theorem B1993199 : Blo 1991435 1993199 := bstep (se 1 (by rfl) ⟨1494899, by rfl⟩ : syracuseStep 1993199 = 2989799) B2989799
theorem B2989805 : Blo 1991435 2989805 := bbase (se 3 (by rfl) ⟨560588, by rfl⟩ : syracuseStep 2989805 = 1121177) (by norm_num)
theorem B1993203 : Blo 1991435 1993203 := bstep (se 1 (by rfl) ⟨1494902, by rfl⟩ : syracuseStep 1993203 = 2989805) B2989805
theorem B4484717 : Blo 1991435 4484717 := bbase (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) (by norm_num)
theorem B2989811 : Blo 1991435 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B1993207 : Blo 1991435 1993207 := bstep (se 1 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 1993207 = 2989811) B2989811
theorem B3783989 : Blo 1991435 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B2522659 : Blo 1991435 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B3363545 : Blo 1991435 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B2242363 : Blo 1991435 2242363 := bstep (se 1 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 2242363 = 3363545) B3363545
theorem B2989817 : Blo 1991435 2989817 := bstep (se 2 (by rfl) ⟨1121181, by rfl⟩ : syracuseStep 2989817 = 2242363) B2242363
theorem B1993211 : Blo 1991435 1993211 := bstep (se 1 (by rfl) ⟨1494908, by rfl⟩ : syracuseStep 1993211 = 2989817) B2989817
theorem B2221445 : Blo 1991435 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B5923853 : Blo 1991435 5923853 := bstep (se 3 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 5923853 = 2221445) B2221445
theorem B3949235 : Blo 1991435 3949235 := bstep (se 1 (by rfl) ⟨2961926, by rfl⟩ : syracuseStep 3949235 = 5923853) B5923853
theorem B42125173 : Blo 1991435 42125173 := bstep (se 5 (by rfl) ⟨1974617, by rfl⟩ : syracuseStep 42125173 = 3949235) B3949235
theorem B224667589 : Blo 1991435 224667589 := bstep (se 4 (by rfl) ⟨21062586, by rfl⟩ : syracuseStep 224667589 = 42125173) B42125173
theorem B299556785 : Blo 1991435 299556785 := bstep (se 2 (by rfl) ⟨112333794, by rfl⟩ : syracuseStep 299556785 = 224667589) B224667589
theorem B199704523 : Blo 1991435 199704523 := bstep (se 1 (by rfl) ⟨149778392, by rfl⟩ : syracuseStep 199704523 = 299556785) B299556785
theorem B266272697 : Blo 1991435 266272697 := bstep (se 2 (by rfl) ⟨99852261, by rfl⟩ : syracuseStep 266272697 = 199704523) B199704523
theorem B710060525 : Blo 1991435 710060525 := bstep (se 3 (by rfl) ⟨133136348, by rfl⟩ : syracuseStep 710060525 = 266272697) B266272697
theorem B473373683 : Blo 1991435 473373683 := bstep (se 1 (by rfl) ⟨355030262, by rfl⟩ : syracuseStep 473373683 = 710060525) B710060525
theorem B315582455 : Blo 1991435 315582455 := bstep (se 1 (by rfl) ⟨236686841, by rfl⟩ : syracuseStep 315582455 = 473373683) B473373683
theorem B210388303 : Blo 1991435 210388303 := bstep (se 1 (by rfl) ⟨157791227, by rfl⟩ : syracuseStep 210388303 = 315582455) B315582455
theorem B280517737 : Blo 1991435 280517737 := bstep (se 2 (by rfl) ⟨105194151, by rfl⟩ : syracuseStep 280517737 = 210388303) B210388303
theorem B374023649 : Blo 1991435 374023649 := bstep (se 2 (by rfl) ⟨140258868, by rfl⟩ : syracuseStep 374023649 = 280517737) B280517737
theorem B249349099 : Blo 1991435 249349099 := bstep (se 1 (by rfl) ⟨187011824, by rfl⟩ : syracuseStep 249349099 = 374023649) B374023649
theorem B332465465 : Blo 1991435 332465465 := bstep (se 2 (by rfl) ⟨124674549, by rfl⟩ : syracuseStep 332465465 = 249349099) B249349099
theorem B221643643 : Blo 1991435 221643643 := bstep (se 1 (by rfl) ⟨166232732, by rfl⟩ : syracuseStep 221643643 = 332465465) B332465465
theorem B295524857 : Blo 1991435 295524857 := bstep (se 2 (by rfl) ⟨110821821, by rfl⟩ : syracuseStep 295524857 = 221643643) B221643643
theorem B197016571 : Blo 1991435 197016571 := bstep (se 1 (by rfl) ⟨147762428, by rfl⟩ : syracuseStep 197016571 = 295524857) B295524857
theorem B262688761 : Blo 1991435 262688761 := bstep (se 2 (by rfl) ⟨98508285, by rfl⟩ : syracuseStep 262688761 = 197016571) B197016571
theorem B1401006725 : Blo 1991435 1401006725 := bstep (se 4 (by rfl) ⟨131344380, by rfl⟩ : syracuseStep 1401006725 = 262688761) B262688761
theorem B934004483 : Blo 1991435 934004483 := bstep (se 1 (by rfl) ⟨700503362, by rfl⟩ : syracuseStep 934004483 = 1401006725) B1401006725
theorem B622669655 : Blo 1991435 622669655 := bstep (se 1 (by rfl) ⟨467002241, by rfl⟩ : syracuseStep 622669655 = 934004483) B934004483
theorem B415113103 : Blo 1991435 415113103 := bstep (se 1 (by rfl) ⟨311334827, by rfl⟩ : syracuseStep 415113103 = 622669655) B622669655
theorem B2213936549 : Blo 1991435 2213936549 := bstep (se 4 (by rfl) ⟨207556551, by rfl⟩ : syracuseStep 2213936549 = 415113103) B415113103
theorem B1475957699 : Blo 1991435 1475957699 := bstep (se 1 (by rfl) ⟨1106968274, by rfl⟩ : syracuseStep 1475957699 = 2213936549) B2213936549
theorem B983971799 : Blo 1991435 983971799 := bstep (se 1 (by rfl) ⟨737978849, by rfl⟩ : syracuseStep 983971799 = 1475957699) B1475957699
theorem B655981199 : Blo 1991435 655981199 := bstep (se 1 (by rfl) ⟨491985899, by rfl⟩ : syracuseStep 655981199 = 983971799) B983971799
theorem B437320799 : Blo 1991435 437320799 := bstep (se 1 (by rfl) ⟨327990599, by rfl⟩ : syracuseStep 437320799 = 655981199) B655981199
theorem B291547199 : Blo 1991435 291547199 := bstep (se 1 (by rfl) ⟨218660399, by rfl⟩ : syracuseStep 291547199 = 437320799) B437320799
theorem B777459197 : Blo 1991435 777459197 := bstep (se 3 (by rfl) ⟨145773599, by rfl⟩ : syracuseStep 777459197 = 291547199) B291547199
theorem B518306131 : Blo 1991435 518306131 := bstep (se 1 (by rfl) ⟨388729598, by rfl⟩ : syracuseStep 518306131 = 777459197) B777459197
theorem B691074841 : Blo 1991435 691074841 := bstep (se 2 (by rfl) ⟨259153065, by rfl⟩ : syracuseStep 691074841 = 518306131) B518306131
theorem B921433121 : Blo 1991435 921433121 := bstep (se 2 (by rfl) ⟨345537420, by rfl⟩ : syracuseStep 921433121 = 691074841) B691074841
theorem B614288747 : Blo 1991435 614288747 := bstep (se 1 (by rfl) ⟨460716560, by rfl⟩ : syracuseStep 614288747 = 921433121) B921433121
theorem B409525831 : Blo 1991435 409525831 := bstep (se 1 (by rfl) ⟨307144373, by rfl⟩ : syracuseStep 409525831 = 614288747) B614288747
theorem B546034441 : Blo 1991435 546034441 := bstep (se 2 (by rfl) ⟨204762915, by rfl⟩ : syracuseStep 546034441 = 409525831) B409525831
theorem B728045921 : Blo 1991435 728045921 := bstep (se 2 (by rfl) ⟨273017220, by rfl⟩ : syracuseStep 728045921 = 546034441) B546034441
theorem B485363947 : Blo 1991435 485363947 := bstep (se 1 (by rfl) ⟨364022960, by rfl⟩ : syracuseStep 485363947 = 728045921) B728045921
theorem B647151929 : Blo 1991435 647151929 := bstep (se 2 (by rfl) ⟨242681973, by rfl⟩ : syracuseStep 647151929 = 485363947) B485363947
theorem B431434619 : Blo 1991435 431434619 := bstep (se 1 (by rfl) ⟨323575964, by rfl⟩ : syracuseStep 431434619 = 647151929) B647151929
theorem B287623079 : Blo 1991435 287623079 := bstep (se 1 (by rfl) ⟨215717309, by rfl⟩ : syracuseStep 287623079 = 431434619) B431434619
theorem B191748719 : Blo 1991435 191748719 := bstep (se 1 (by rfl) ⟨143811539, by rfl⟩ : syracuseStep 191748719 = 287623079) B287623079
theorem B511329917 : Blo 1991435 511329917 := bstep (se 3 (by rfl) ⟨95874359, by rfl⟩ : syracuseStep 511329917 = 191748719) B191748719
theorem B1363546445 : Blo 1991435 1363546445 := bstep (se 3 (by rfl) ⟨255664958, by rfl⟩ : syracuseStep 1363546445 = 511329917) B511329917
theorem B3636123853 : Blo 1991435 3636123853 := bstep (se 3 (by rfl) ⟨681773222, by rfl⟩ : syracuseStep 3636123853 = 1363546445) B1363546445
theorem B4848165137 : Blo 1991435 4848165137 := bstep (se 2 (by rfl) ⟨1818061926, by rfl⟩ : syracuseStep 4848165137 = 3636123853) B3636123853
theorem B12928440365 : Blo 1991435 12928440365 := bstep (se 3 (by rfl) ⟨2424082568, by rfl⟩ : syracuseStep 12928440365 = 4848165137) B4848165137
theorem B8618960243 : Blo 1991435 8618960243 := bstep (se 1 (by rfl) ⟨6464220182, by rfl⟩ : syracuseStep 8618960243 = 12928440365) B12928440365
theorem B22983893981 : Blo 1991435 22983893981 := bstep (se 3 (by rfl) ⟨4309480121, by rfl⟩ : syracuseStep 22983893981 = 8618960243) B8618960243
theorem B15322595987 : Blo 1991435 15322595987 := bstep (se 1 (by rfl) ⟨11491946990, by rfl⟩ : syracuseStep 15322595987 = 22983893981) B22983893981
theorem B10215063991 : Blo 1991435 10215063991 := bstep (se 1 (by rfl) ⟨7661297993, by rfl⟩ : syracuseStep 10215063991 = 15322595987) B15322595987
theorem B13620085321 : Blo 1991435 13620085321 := bstep (se 2 (by rfl) ⟨5107531995, by rfl⟩ : syracuseStep 13620085321 = 10215063991) B10215063991
theorem B18160113761 : Blo 1991435 18160113761 := bstep (se 2 (by rfl) ⟨6810042660, by rfl⟩ : syracuseStep 18160113761 = 13620085321) B13620085321
theorem B12106742507 : Blo 1991435 12106742507 := bstep (se 1 (by rfl) ⟨9080056880, by rfl⟩ : syracuseStep 12106742507 = 18160113761) B18160113761
theorem B8071161671 : Blo 1991435 8071161671 := bstep (se 1 (by rfl) ⟨6053371253, by rfl⟩ : syracuseStep 8071161671 = 12106742507) B12106742507
theorem B5380774447 : Blo 1991435 5380774447 := bstep (se 1 (by rfl) ⟨4035580835, by rfl⟩ : syracuseStep 5380774447 = 8071161671) B8071161671
theorem B7174365929 : Blo 1991435 7174365929 := bstep (se 2 (by rfl) ⟨2690387223, by rfl⟩ : syracuseStep 7174365929 = 5380774447) B5380774447
theorem B4782910619 : Blo 1991435 4782910619 := bstep (se 1 (by rfl) ⟨3587182964, by rfl⟩ : syracuseStep 4782910619 = 7174365929) B7174365929
theorem B3188607079 : Blo 1991435 3188607079 := bstep (se 1 (by rfl) ⟨2391455309, by rfl⟩ : syracuseStep 3188607079 = 4782910619) B4782910619
theorem B4251476105 : Blo 1991435 4251476105 := bstep (se 2 (by rfl) ⟨1594303539, by rfl⟩ : syracuseStep 4251476105 = 3188607079) B3188607079
theorem B2834317403 : Blo 1991435 2834317403 := bstep (se 1 (by rfl) ⟨2125738052, by rfl⟩ : syracuseStep 2834317403 = 4251476105) B4251476105
theorem B1889544935 : Blo 1991435 1889544935 := bstep (se 1 (by rfl) ⟨1417158701, by rfl⟩ : syracuseStep 1889544935 = 2834317403) B2834317403
theorem B1259696623 : Blo 1991435 1259696623 := bstep (se 1 (by rfl) ⟨944772467, by rfl⟩ : syracuseStep 1259696623 = 1889544935) B1889544935
theorem B1679595497 : Blo 1991435 1679595497 := bstep (se 2 (by rfl) ⟨629848311, by rfl⟩ : syracuseStep 1679595497 = 1259696623) B1259696623
theorem B1119730331 : Blo 1991435 1119730331 := bstep (se 1 (by rfl) ⟨839797748, by rfl⟩ : syracuseStep 1119730331 = 1679595497) B1679595497
theorem B746486887 : Blo 1991435 746486887 := bstep (se 1 (by rfl) ⟨559865165, by rfl⟩ : syracuseStep 746486887 = 1119730331) B1119730331
theorem B995315849 : Blo 1991435 995315849 := bstep (se 2 (by rfl) ⟨373243443, by rfl⟩ : syracuseStep 995315849 = 746486887) B746486887
theorem B663543899 : Blo 1991435 663543899 := bstep (se 1 (by rfl) ⟨497657924, by rfl⟩ : syracuseStep 663543899 = 995315849) B995315849
theorem B442362599 : Blo 1991435 442362599 := bstep (se 1 (by rfl) ⟨331771949, by rfl⟩ : syracuseStep 442362599 = 663543899) B663543899
theorem B294908399 : Blo 1991435 294908399 := bstep (se 1 (by rfl) ⟨221181299, by rfl⟩ : syracuseStep 294908399 = 442362599) B442362599
theorem B196605599 : Blo 1991435 196605599 := bstep (se 1 (by rfl) ⟨147454199, by rfl⟩ : syracuseStep 196605599 = 294908399) B294908399
theorem B2097126389 : Blo 1991435 2097126389 := bstep (se 5 (by rfl) ⟨98302799, by rfl⟩ : syracuseStep 2097126389 = 196605599) B196605599
theorem B5592337037 : Blo 1991435 5592337037 := bstep (se 3 (by rfl) ⟨1048563194, by rfl⟩ : syracuseStep 5592337037 = 2097126389) B2097126389
theorem B3728224691 : Blo 1991435 3728224691 := bstep (se 1 (by rfl) ⟨2796168518, by rfl⟩ : syracuseStep 3728224691 = 5592337037) B5592337037
theorem B2485483127 : Blo 1991435 2485483127 := bstep (se 1 (by rfl) ⟨1864112345, by rfl⟩ : syracuseStep 2485483127 = 3728224691) B3728224691
theorem B1656988751 : Blo 1991435 1656988751 := bstep (se 1 (by rfl) ⟨1242741563, by rfl⟩ : syracuseStep 1656988751 = 2485483127) B2485483127
theorem B1104659167 : Blo 1991435 1104659167 := bstep (se 1 (by rfl) ⟨828494375, by rfl⟩ : syracuseStep 1104659167 = 1656988751) B1656988751
theorem B1472878889 : Blo 1991435 1472878889 := bstep (se 2 (by rfl) ⟨552329583, by rfl⟩ : syracuseStep 1472878889 = 1104659167) B1104659167
theorem B981919259 : Blo 1991435 981919259 := bstep (se 1 (by rfl) ⟨736439444, by rfl⟩ : syracuseStep 981919259 = 1472878889) B1472878889
theorem B654612839 : Blo 1991435 654612839 := bstep (se 1 (by rfl) ⟨490959629, by rfl⟩ : syracuseStep 654612839 = 981919259) B981919259
theorem B436408559 : Blo 1991435 436408559 := bstep (se 1 (by rfl) ⟨327306419, by rfl⟩ : syracuseStep 436408559 = 654612839) B654612839
theorem B290939039 : Blo 1991435 290939039 := bstep (se 1 (by rfl) ⟨218204279, by rfl⟩ : syracuseStep 290939039 = 436408559) B436408559
theorem B193959359 : Blo 1991435 193959359 := bstep (se 1 (by rfl) ⟨145469519, by rfl⟩ : syracuseStep 193959359 = 290939039) B290939039
theorem B129306239 : Blo 1991435 129306239 := bstep (se 1 (by rfl) ⟨96979679, by rfl⟩ : syracuseStep 129306239 = 193959359) B193959359
theorem B86204159 : Blo 1991435 86204159 := bstep (se 1 (by rfl) ⟨64653119, by rfl⟩ : syracuseStep 86204159 = 129306239) B129306239
theorem B57469439 : Blo 1991435 57469439 := bstep (se 1 (by rfl) ⟨43102079, by rfl⟩ : syracuseStep 57469439 = 86204159) B86204159
theorem B38312959 : Blo 1991435 38312959 := bstep (se 1 (by rfl) ⟨28734719, by rfl⟩ : syracuseStep 38312959 = 57469439) B57469439
theorem B51083945 : Blo 1991435 51083945 := bstep (se 2 (by rfl) ⟨19156479, by rfl⟩ : syracuseStep 51083945 = 38312959) B38312959
theorem B34055963 : Blo 1991435 34055963 := bstep (se 1 (by rfl) ⟨25541972, by rfl⟩ : syracuseStep 34055963 = 51083945) B51083945
theorem B22703975 : Blo 1991435 22703975 := bstep (se 1 (by rfl) ⟨17027981, by rfl⟩ : syracuseStep 22703975 = 34055963) B34055963
theorem B15135983 : Blo 1991435 15135983 := bstep (se 1 (by rfl) ⟨11351987, by rfl⟩ : syracuseStep 15135983 = 22703975) B22703975
theorem B10090655 : Blo 1991435 10090655 := bstep (se 1 (by rfl) ⟨7567991, by rfl⟩ : syracuseStep 10090655 = 15135983) B15135983
theorem B6727103 : Blo 1991435 6727103 := bstep (se 1 (by rfl) ⟨5045327, by rfl⟩ : syracuseStep 6727103 = 10090655) B10090655
theorem B4484735 : Blo 1991435 4484735 := bstep (se 1 (by rfl) ⟨3363551, by rfl⟩ : syracuseStep 4484735 = 6727103) B6727103
theorem B2989823 : Blo 1991435 2989823 := bstep (se 1 (by rfl) ⟨2242367, by rfl⟩ : syracuseStep 2989823 = 4484735) B4484735
theorem B1993215 : Blo 1991435 1993215 := bstep (se 1 (by rfl) ⟨1494911, by rfl⟩ : syracuseStep 1993215 = 2989823) B2989823
theorem B2989829 : Blo 1991435 2989829 := bbase (se 4 (by rfl) ⟨280296, by rfl⟩ : syracuseStep 2989829 = 560593) (by norm_num)
theorem B1993219 : Blo 1991435 1993219 := bstep (se 1 (by rfl) ⟨1494914, by rfl⟩ : syracuseStep 1993219 = 2989829) B2989829
theorem B3363565 : Blo 1991435 3363565 := bbase (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) (by norm_num)
theorem B4484753 : Blo 1991435 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B2989835 : Blo 1991435 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B1993223 : Blo 1991435 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B2242381 : Blo 1991435 2242381 := bbase (se 3 (by rfl) ⟨420446, by rfl⟩ : syracuseStep 2242381 = 840893) (by norm_num)
theorem B2989841 : Blo 1991435 2989841 := bstep (se 2 (by rfl) ⟨1121190, by rfl⟩ : syracuseStep 2989841 = 2242381) B2242381
theorem B1993227 : Blo 1991435 1993227 := bstep (se 1 (by rfl) ⟨1494920, by rfl⟩ : syracuseStep 1993227 = 2989841) B2989841
theorem B6727157 : Blo 1991435 6727157 := bbase (se 5 (by rfl) ⟨315335, by rfl⟩ : syracuseStep 6727157 = 630671) (by norm_num)
theorem B4484771 : Blo 1991435 4484771 := bstep (se 1 (by rfl) ⟨3363578, by rfl⟩ : syracuseStep 4484771 = 6727157) B6727157
theorem B2989847 : Blo 1991435 2989847 := bstep (se 1 (by rfl) ⟨2242385, by rfl⟩ : syracuseStep 2989847 = 4484771) B4484771
theorem B1993231 : Blo 1991435 1993231 := bstep (se 1 (by rfl) ⟨1494923, by rfl⟩ : syracuseStep 1993231 = 2989847) B2989847
theorem B2989853 : Blo 1991435 2989853 := bbase (se 3 (by rfl) ⟨560597, by rfl⟩ : syracuseStep 2989853 = 1121195) (by norm_num)
theorem B1993235 : Blo 1991435 1993235 := bstep (se 1 (by rfl) ⟨1494926, by rfl⟩ : syracuseStep 1993235 = 2989853) B2989853
theorem B4484789 : Blo 1991435 4484789 := bbase (se 5 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 4484789 = 420449) (by norm_num)
theorem B2989859 : Blo 1991435 2989859 := bstep (se 1 (by rfl) ⟨2242394, by rfl⟩ : syracuseStep 2989859 = 4484789) B4484789
theorem B1993239 : Blo 1991435 1993239 := bstep (se 1 (by rfl) ⟨1494929, by rfl⟩ : syracuseStep 1993239 = 2989859) B2989859
theorem B11352149 : Blo 1991435 11352149 := bbase (se 8 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 11352149 = 133033) (by norm_num)
theorem B7568099 : Blo 1991435 7568099 := bstep (se 1 (by rfl) ⟨5676074, by rfl⟩ : syracuseStep 7568099 = 11352149) B11352149
theorem B5045399 : Blo 1991435 5045399 := bstep (se 1 (by rfl) ⟨3784049, by rfl⟩ : syracuseStep 5045399 = 7568099) B7568099
theorem B3363599 : Blo 1991435 3363599 := bstep (se 1 (by rfl) ⟨2522699, by rfl⟩ : syracuseStep 3363599 = 5045399) B5045399
theorem B2242399 : Blo 1991435 2242399 := bstep (se 1 (by rfl) ⟨1681799, by rfl⟩ : syracuseStep 2242399 = 3363599) B3363599
theorem B2989865 : Blo 1991435 2989865 := bstep (se 2 (by rfl) ⟨1121199, by rfl⟩ : syracuseStep 2989865 = 2242399) B2242399
theorem B1993243 : Blo 1991435 1993243 := bstep (se 1 (by rfl) ⟨1494932, by rfl⟩ : syracuseStep 1993243 = 2989865) B2989865
theorem B5676085 : Blo 1991435 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B7568113 : Blo 1991435 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B10090817 : Blo 1991435 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B6727211 : Blo 1991435 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B4484807 : Blo 1991435 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B2989871 : Blo 1991435 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B1993247 : Blo 1991435 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B2989877 : Blo 1991435 2989877 := bbase (se 5 (by rfl) ⟨140150, by rfl⟩ : syracuseStep 2989877 = 280301) (by norm_num)
theorem B1993251 : Blo 1991435 1993251 := bstep (se 1 (by rfl) ⟨1494938, by rfl⟩ : syracuseStep 1993251 = 2989877) B2989877
theorem B5045429 : Blo 1991435 5045429 := bbase (se 5 (by rfl) ⟨236504, by rfl⟩ : syracuseStep 5045429 = 473009) (by norm_num)
theorem B3363619 : Blo 1991435 3363619 := bstep (se 1 (by rfl) ⟨2522714, by rfl⟩ : syracuseStep 3363619 = 5045429) B5045429
theorem B4484825 : Blo 1991435 4484825 := bstep (se 2 (by rfl) ⟨1681809, by rfl⟩ : syracuseStep 4484825 = 3363619) B3363619
theorem B2989883 : Blo 1991435 2989883 := bstep (se 1 (by rfl) ⟨2242412, by rfl⟩ : syracuseStep 2989883 = 4484825) B4484825
theorem B1993255 : Blo 1991435 1993255 := bstep (se 1 (by rfl) ⟨1494941, by rfl⟩ : syracuseStep 1993255 = 2989883) B2989883
theorem B2242417 : Blo 1991435 2242417 := bbase (se 2 (by rfl) ⟨840906, by rfl⟩ : syracuseStep 2242417 = 1681813) (by norm_num)
theorem B2989889 : Blo 1991435 2989889 := bstep (se 2 (by rfl) ⟨1121208, by rfl⟩ : syracuseStep 2989889 = 2242417) B2242417
theorem B1993259 : Blo 1991435 1993259 := bstep (se 1 (by rfl) ⟨1494944, by rfl⟩ : syracuseStep 1993259 = 2989889) B2989889
theorem B8514197 : Blo 1991435 8514197 := bbase (se 6 (by rfl) ⟨199551, by rfl⟩ : syracuseStep 8514197 = 399103) (by norm_num)
theorem B5676131 : Blo 1991435 5676131 := bstep (se 1 (by rfl) ⟨4257098, by rfl⟩ : syracuseStep 5676131 = 8514197) B8514197
theorem B3784087 : Blo 1991435 3784087 := bstep (se 1 (by rfl) ⟨2838065, by rfl⟩ : syracuseStep 3784087 = 5676131) B5676131
theorem B5045449 : Blo 1991435 5045449 := bstep (se 2 (by rfl) ⟨1892043, by rfl⟩ : syracuseStep 5045449 = 3784087) B3784087
theorem B6727265 : Blo 1991435 6727265 := bstep (se 2 (by rfl) ⟨2522724, by rfl⟩ : syracuseStep 6727265 = 5045449) B5045449
theorem B4484843 : Blo 1991435 4484843 := bstep (se 1 (by rfl) ⟨3363632, by rfl⟩ : syracuseStep 4484843 = 6727265) B6727265
theorem B2989895 : Blo 1991435 2989895 := bstep (se 1 (by rfl) ⟨2242421, by rfl⟩ : syracuseStep 2989895 = 4484843) B4484843
theorem B1993263 : Blo 1991435 1993263 := bstep (se 1 (by rfl) ⟨1494947, by rfl⟩ : syracuseStep 1993263 = 2989895) B2989895
theorem B2989901 : Blo 1991435 2989901 := bbase (se 3 (by rfl) ⟨560606, by rfl⟩ : syracuseStep 2989901 = 1121213) (by norm_num)
theorem B1993267 : Blo 1991435 1993267 := bstep (se 1 (by rfl) ⟨1494950, by rfl⟩ : syracuseStep 1993267 = 2989901) B2989901
theorem B4484861 : Blo 1991435 4484861 := bbase (se 3 (by rfl) ⟨840911, by rfl⟩ : syracuseStep 4484861 = 1681823) (by norm_num)
theorem B2989907 : Blo 1991435 2989907 := bstep (se 1 (by rfl) ⟨2242430, by rfl⟩ : syracuseStep 2989907 = 4484861) B4484861
theorem B1993271 : Blo 1991435 1993271 := bstep (se 1 (by rfl) ⟨1494953, by rfl⟩ : syracuseStep 1993271 = 2989907) B2989907
theorem B3363653 : Blo 1991435 3363653 := bbase (se 4 (by rfl) ⟨315342, by rfl⟩ : syracuseStep 3363653 = 630685) (by norm_num)
theorem B2242435 : Blo 1991435 2242435 := bstep (se 1 (by rfl) ⟨1681826, by rfl⟩ : syracuseStep 2242435 = 3363653) B3363653
theorem B2989913 : Blo 1991435 2989913 := bstep (se 2 (by rfl) ⟨1121217, by rfl⟩ : syracuseStep 2989913 = 2242435) B2242435
theorem B1993275 : Blo 1991435 1993275 := bstep (se 1 (by rfl) ⟨1494956, by rfl⟩ : syracuseStep 1993275 = 2989913) B2989913
theorem B15136469 : Blo 1991435 15136469 := bbase (se 7 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 15136469 = 354761) (by norm_num)
theorem B10090979 : Blo 1991435 10090979 := bstep (se 1 (by rfl) ⟨7568234, by rfl⟩ : syracuseStep 10090979 = 15136469) B15136469
theorem B6727319 : Blo 1991435 6727319 := bstep (se 1 (by rfl) ⟨5045489, by rfl⟩ : syracuseStep 6727319 = 10090979) B10090979
theorem B4484879 : Blo 1991435 4484879 := bstep (se 1 (by rfl) ⟨3363659, by rfl⟩ : syracuseStep 4484879 = 6727319) B6727319
theorem B2989919 : Blo 1991435 2989919 := bstep (se 1 (by rfl) ⟨2242439, by rfl⟩ : syracuseStep 2989919 = 4484879) B4484879
theorem B1993279 : Blo 1991435 1993279 := bstep (se 1 (by rfl) ⟨1494959, by rfl⟩ : syracuseStep 1993279 = 2989919) B2989919
theorem B2989925 : Blo 1991435 2989925 := bbase (se 4 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 2989925 = 560611) (by norm_num)
theorem B1993283 : Blo 1991435 1993283 := bstep (se 1 (by rfl) ⟨1494962, by rfl⟩ : syracuseStep 1993283 = 2989925) B2989925
theorem B3784133 : Blo 1991435 3784133 := bbase (se 4 (by rfl) ⟨354762, by rfl⟩ : syracuseStep 3784133 = 709525) (by norm_num)
theorem B2522755 : Blo 1991435 2522755 := bstep (se 1 (by rfl) ⟨1892066, by rfl⟩ : syracuseStep 2522755 = 3784133) B3784133
theorem B3363673 : Blo 1991435 3363673 := bstep (se 2 (by rfl) ⟨1261377, by rfl⟩ : syracuseStep 3363673 = 2522755) B2522755
theorem B4484897 : Blo 1991435 4484897 := bstep (se 2 (by rfl) ⟨1681836, by rfl⟩ : syracuseStep 4484897 = 3363673) B3363673
theorem B2989931 : Blo 1991435 2989931 := bstep (se 1 (by rfl) ⟨2242448, by rfl⟩ : syracuseStep 2989931 = 4484897) B4484897
theorem B1993287 : Blo 1991435 1993287 := bstep (se 1 (by rfl) ⟨1494965, by rfl⟩ : syracuseStep 1993287 = 2989931) B2989931
theorem B2242453 : Blo 1991435 2242453 := bbase (se 6 (by rfl) ⟨52557, by rfl⟩ : syracuseStep 2242453 = 105115) (by norm_num)
theorem B2989937 : Blo 1991435 2989937 := bstep (se 2 (by rfl) ⟨1121226, by rfl⟩ : syracuseStep 2989937 = 2242453) B2242453
theorem B1993291 : Blo 1991435 1993291 := bstep (se 1 (by rfl) ⟨1494968, by rfl⟩ : syracuseStep 1993291 = 2989937) B2989937
theorem B2522765 : Blo 1991435 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B6727373 : Blo 1991435 6727373 := bstep (se 3 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 6727373 = 2522765) B2522765
theorem B4484915 : Blo 1991435 4484915 := bstep (se 1 (by rfl) ⟨3363686, by rfl⟩ : syracuseStep 4484915 = 6727373) B6727373
theorem B2989943 : Blo 1991435 2989943 := bstep (se 1 (by rfl) ⟨2242457, by rfl⟩ : syracuseStep 2989943 = 4484915) B4484915
theorem B1993295 : Blo 1991435 1993295 := bstep (se 1 (by rfl) ⟨1494971, by rfl⟩ : syracuseStep 1993295 = 2989943) B2989943
theorem B2989949 : Blo 1991435 2989949 := bbase (se 3 (by rfl) ⟨560615, by rfl⟩ : syracuseStep 2989949 = 1121231) (by norm_num)
theorem B1993299 : Blo 1991435 1993299 := bstep (se 1 (by rfl) ⟨1494974, by rfl⟩ : syracuseStep 1993299 = 2989949) B2989949
theorem B4484933 : Blo 1991435 4484933 := bbase (se 4 (by rfl) ⟨420462, by rfl⟩ : syracuseStep 4484933 = 840925) (by norm_num)
theorem B2989955 : Blo 1991435 2989955 := bstep (se 1 (by rfl) ⟨2242466, by rfl⟩ : syracuseStep 2989955 = 4484933) B4484933
theorem B1993303 : Blo 1991435 1993303 := bstep (se 1 (by rfl) ⟨1494977, by rfl⟩ : syracuseStep 1993303 = 2989955) B2989955
theorem B10228805 : Blo 1991435 10228805 := bbase (se 4 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 10228805 = 1917901) (by norm_num)
theorem B6819203 : Blo 1991435 6819203 := bstep (se 1 (by rfl) ⟨5114402, by rfl⟩ : syracuseStep 6819203 = 10228805) B10228805
theorem B4546135 : Blo 1991435 4546135 := bstep (se 1 (by rfl) ⟨3409601, by rfl⟩ : syracuseStep 4546135 = 6819203) B6819203
theorem B24246053 : Blo 1991435 24246053 := bstep (se 4 (by rfl) ⟨2273067, by rfl⟩ : syracuseStep 24246053 = 4546135) B4546135
theorem B16164035 : Blo 1991435 16164035 := bstep (se 1 (by rfl) ⟨12123026, by rfl⟩ : syracuseStep 16164035 = 24246053) B24246053
theorem B10776023 : Blo 1991435 10776023 := bstep (se 1 (by rfl) ⟨8082017, by rfl⟩ : syracuseStep 10776023 = 16164035) B16164035
theorem B7184015 : Blo 1991435 7184015 := bstep (se 1 (by rfl) ⟨5388011, by rfl⟩ : syracuseStep 7184015 = 10776023) B10776023
theorem B4789343 : Blo 1991435 4789343 := bstep (se 1 (by rfl) ⟨3592007, by rfl⟩ : syracuseStep 4789343 = 7184015) B7184015
theorem B3192895 : Blo 1991435 3192895 := bstep (se 1 (by rfl) ⟨2394671, by rfl⟩ : syracuseStep 3192895 = 4789343) B4789343
theorem B4257193 : Blo 1991435 4257193 := bstep (se 2 (by rfl) ⟨1596447, by rfl⟩ : syracuseStep 4257193 = 3192895) B3192895
theorem B5676257 : Blo 1991435 5676257 := bstep (se 2 (by rfl) ⟨2128596, by rfl⟩ : syracuseStep 5676257 = 4257193) B4257193
theorem B3784171 : Blo 1991435 3784171 := bstep (se 1 (by rfl) ⟨2838128, by rfl⟩ : syracuseStep 3784171 = 5676257) B5676257
theorem B5045561 : Blo 1991435 5045561 := bstep (se 2 (by rfl) ⟨1892085, by rfl⟩ : syracuseStep 5045561 = 3784171) B3784171
theorem B3363707 : Blo 1991435 3363707 := bstep (se 1 (by rfl) ⟨2522780, by rfl⟩ : syracuseStep 3363707 = 5045561) B5045561
theorem B2242471 : Blo 1991435 2242471 := bstep (se 1 (by rfl) ⟨1681853, by rfl⟩ : syracuseStep 2242471 = 3363707) B3363707
theorem B2989961 : Blo 1991435 2989961 := bstep (se 2 (by rfl) ⟨1121235, by rfl⟩ : syracuseStep 2989961 = 2242471) B2242471
theorem B1993307 : Blo 1991435 1993307 := bstep (se 1 (by rfl) ⟨1494980, by rfl⟩ : syracuseStep 1993307 = 2989961) B2989961
theorem B10091141 : Blo 1991435 10091141 := bbase (se 4 (by rfl) ⟨946044, by rfl⟩ : syracuseStep 10091141 = 1892089) (by norm_num)
theorem B6727427 : Blo 1991435 6727427 := bstep (se 1 (by rfl) ⟨5045570, by rfl⟩ : syracuseStep 6727427 = 10091141) B10091141
theorem B4484951 : Blo 1991435 4484951 := bstep (se 1 (by rfl) ⟨3363713, by rfl⟩ : syracuseStep 4484951 = 6727427) B6727427
theorem B2989967 : Blo 1991435 2989967 := bstep (se 1 (by rfl) ⟨2242475, by rfl⟩ : syracuseStep 2989967 = 4484951) B4484951
theorem B1993311 : Blo 1991435 1993311 := bstep (se 1 (by rfl) ⟨1494983, by rfl⟩ : syracuseStep 1993311 = 2989967) B2989967
theorem B2989973 : Blo 1991435 2989973 := bbase (se 6 (by rfl) ⟨70077, by rfl⟩ : syracuseStep 2989973 = 140155) (by norm_num)
theorem B1993315 : Blo 1991435 1993315 := bstep (se 1 (by rfl) ⟨1494986, by rfl⟩ : syracuseStep 1993315 = 2989973) B2989973
theorem B2128609 : Blo 1991435 2128609 := bbase (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) (by norm_num)
theorem B11352581 : Blo 1991435 11352581 := bstep (se 4 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 11352581 = 2128609) B2128609
theorem B7568387 : Blo 1991435 7568387 := bstep (se 1 (by rfl) ⟨5676290, by rfl⟩ : syracuseStep 7568387 = 11352581) B11352581
theorem B5045591 : Blo 1991435 5045591 := bstep (se 1 (by rfl) ⟨3784193, by rfl⟩ : syracuseStep 5045591 = 7568387) B7568387
theorem B3363727 : Blo 1991435 3363727 := bstep (se 1 (by rfl) ⟨2522795, by rfl⟩ : syracuseStep 3363727 = 5045591) B5045591
theorem B4484969 : Blo 1991435 4484969 := bstep (se 2 (by rfl) ⟨1681863, by rfl⟩ : syracuseStep 4484969 = 3363727) B3363727
theorem B2989979 : Blo 1991435 2989979 := bstep (se 1 (by rfl) ⟨2242484, by rfl⟩ : syracuseStep 2989979 = 4484969) B4484969
theorem B1993319 : Blo 1991435 1993319 := bstep (se 1 (by rfl) ⟨1494989, by rfl⟩ : syracuseStep 1993319 = 2989979) B2989979
theorem B2242489 : Blo 1991435 2242489 := bbase (se 2 (by rfl) ⟨840933, by rfl⟩ : syracuseStep 2242489 = 1681867) (by norm_num)
theorem B2989985 : Blo 1991435 2989985 := bstep (se 2 (by rfl) ⟨1121244, by rfl⟩ : syracuseStep 2989985 = 2242489) B2242489
theorem B1993323 : Blo 1991435 1993323 := bstep (se 1 (by rfl) ⟨1494992, by rfl⟩ : syracuseStep 1993323 = 2989985) B2989985
theorem B4546181 : Blo 1991435 4546181 := bbase (se 4 (by rfl) ⟨426204, by rfl⟩ : syracuseStep 4546181 = 852409) (by norm_num)
theorem B3030787 : Blo 1991435 3030787 := bstep (se 1 (by rfl) ⟨2273090, by rfl⟩ : syracuseStep 3030787 = 4546181) B4546181
theorem B4041049 : Blo 1991435 4041049 := bstep (se 2 (by rfl) ⟨1515393, by rfl⟩ : syracuseStep 4041049 = 3030787) B3030787
theorem B5388065 : Blo 1991435 5388065 := bstep (se 2 (by rfl) ⟨2020524, by rfl⟩ : syracuseStep 5388065 = 4041049) B4041049
theorem B3592043 : Blo 1991435 3592043 := bstep (se 1 (by rfl) ⟨2694032, by rfl⟩ : syracuseStep 3592043 = 5388065) B5388065
theorem B2394695 : Blo 1991435 2394695 := bstep (se 1 (by rfl) ⟨1796021, by rfl⟩ : syracuseStep 2394695 = 3592043) B3592043
theorem B6385853 : Blo 1991435 6385853 := bstep (se 3 (by rfl) ⟨1197347, by rfl⟩ : syracuseStep 6385853 = 2394695) B2394695
theorem B4257235 : Blo 1991435 4257235 := bstep (se 1 (by rfl) ⟨3192926, by rfl⟩ : syracuseStep 4257235 = 6385853) B6385853
theorem B5676313 : Blo 1991435 5676313 := bstep (se 2 (by rfl) ⟨2128617, by rfl⟩ : syracuseStep 5676313 = 4257235) B4257235
theorem B7568417 : Blo 1991435 7568417 := bstep (se 2 (by rfl) ⟨2838156, by rfl⟩ : syracuseStep 7568417 = 5676313) B5676313
theorem B5045611 : Blo 1991435 5045611 := bstep (se 1 (by rfl) ⟨3784208, by rfl⟩ : syracuseStep 5045611 = 7568417) B7568417
theorem B6727481 : Blo 1991435 6727481 := bstep (se 2 (by rfl) ⟨2522805, by rfl⟩ : syracuseStep 6727481 = 5045611) B5045611
theorem B4484987 : Blo 1991435 4484987 := bstep (se 1 (by rfl) ⟨3363740, by rfl⟩ : syracuseStep 4484987 = 6727481) B6727481
theorem B2989991 : Blo 1991435 2989991 := bstep (se 1 (by rfl) ⟨2242493, by rfl⟩ : syracuseStep 2989991 = 4484987) B4484987
theorem B1993327 : Blo 1991435 1993327 := bstep (se 1 (by rfl) ⟨1494995, by rfl⟩ : syracuseStep 1993327 = 2989991) B2989991
theorem B2989997 : Blo 1991435 2989997 := bbase (se 3 (by rfl) ⟨560624, by rfl⟩ : syracuseStep 2989997 = 1121249) (by norm_num)
theorem B1993331 : Blo 1991435 1993331 := bstep (se 1 (by rfl) ⟨1494998, by rfl⟩ : syracuseStep 1993331 = 2989997) B2989997
theorem B4485005 : Blo 1991435 4485005 := bbase (se 3 (by rfl) ⟨840938, by rfl⟩ : syracuseStep 4485005 = 1681877) (by norm_num)
theorem B2990003 : Blo 1991435 2990003 := bstep (se 1 (by rfl) ⟨2242502, by rfl⟩ : syracuseStep 2990003 = 4485005) B4485005
theorem B1993335 : Blo 1991435 1993335 := bstep (se 1 (by rfl) ⟨1495001, by rfl⟩ : syracuseStep 1993335 = 2990003) B2990003
theorem B2522821 : Blo 1991435 2522821 := bbase (se 4 (by rfl) ⟨236514, by rfl⟩ : syracuseStep 2522821 = 473029) (by norm_num)
theorem B3363761 : Blo 1991435 3363761 := bstep (se 2 (by rfl) ⟨1261410, by rfl⟩ : syracuseStep 3363761 = 2522821) B2522821
theorem B2242507 : Blo 1991435 2242507 := bstep (se 1 (by rfl) ⟨1681880, by rfl⟩ : syracuseStep 2242507 = 3363761) B3363761
theorem B2990009 : Blo 1991435 2990009 := bstep (se 2 (by rfl) ⟨1121253, by rfl⟩ : syracuseStep 2990009 = 2242507) B2242507
theorem B1993339 : Blo 1991435 1993339 := bstep (se 1 (by rfl) ⟨1495004, by rfl⟩ : syracuseStep 1993339 = 2990009) B2990009
theorem B17496917 : Blo 1991435 17496917 := bbase (se 9 (by rfl) ⟨51260, by rfl⟩ : syracuseStep 17496917 = 102521) (by norm_num)
theorem B11664611 : Blo 1991435 11664611 := bstep (se 1 (by rfl) ⟨8748458, by rfl⟩ : syracuseStep 11664611 = 17496917) B17496917
theorem B7776407 : Blo 1991435 7776407 := bstep (se 1 (by rfl) ⟨5832305, by rfl⟩ : syracuseStep 7776407 = 11664611) B11664611
theorem B5184271 : Blo 1991435 5184271 := bstep (se 1 (by rfl) ⟨3888203, by rfl⟩ : syracuseStep 5184271 = 7776407) B7776407
theorem B6912361 : Blo 1991435 6912361 := bstep (se 2 (by rfl) ⟨2592135, by rfl⟩ : syracuseStep 6912361 = 5184271) B5184271
theorem B9216481 : Blo 1991435 9216481 := bstep (se 2 (by rfl) ⟨3456180, by rfl⟩ : syracuseStep 9216481 = 6912361) B6912361
theorem B12288641 : Blo 1991435 12288641 := bstep (se 2 (by rfl) ⟨4608240, by rfl⟩ : syracuseStep 12288641 = 9216481) B9216481
theorem B131078837 : Blo 1991435 131078837 := bstep (se 5 (by rfl) ⟨6144320, by rfl⟩ : syracuseStep 131078837 = 12288641) B12288641
theorem B87385891 : Blo 1991435 87385891 := bstep (se 1 (by rfl) ⟨65539418, by rfl⟩ : syracuseStep 87385891 = 131078837) B131078837
theorem B116514521 : Blo 1991435 116514521 := bstep (se 2 (by rfl) ⟨43692945, by rfl⟩ : syracuseStep 116514521 = 87385891) B87385891
theorem B77676347 : Blo 1991435 77676347 := bstep (se 1 (by rfl) ⟨58257260, by rfl⟩ : syracuseStep 77676347 = 116514521) B116514521
theorem B51784231 : Blo 1991435 51784231 := bstep (se 1 (by rfl) ⟨38838173, by rfl⟩ : syracuseStep 51784231 = 77676347) B77676347
theorem B69045641 : Blo 1991435 69045641 := bstep (se 2 (by rfl) ⟨25892115, by rfl⟩ : syracuseStep 69045641 = 51784231) B51784231
theorem B46030427 : Blo 1991435 46030427 := bstep (se 1 (by rfl) ⟨34522820, by rfl⟩ : syracuseStep 46030427 = 69045641) B69045641
theorem B30686951 : Blo 1991435 30686951 := bstep (se 1 (by rfl) ⟨23015213, by rfl⟩ : syracuseStep 30686951 = 46030427) B46030427
theorem B81831869 : Blo 1991435 81831869 := bstep (se 3 (by rfl) ⟨15343475, by rfl⟩ : syracuseStep 81831869 = 30686951) B30686951
theorem B54554579 : Blo 1991435 54554579 := bstep (se 1 (by rfl) ⟨40915934, by rfl⟩ : syracuseStep 54554579 = 81831869) B81831869
theorem B36369719 : Blo 1991435 36369719 := bstep (se 1 (by rfl) ⟨27277289, by rfl⟩ : syracuseStep 36369719 = 54554579) B54554579
theorem B24246479 : Blo 1991435 24246479 := bstep (se 1 (by rfl) ⟨18184859, by rfl⟩ : syracuseStep 24246479 = 36369719) B36369719
theorem B16164319 : Blo 1991435 16164319 := bstep (se 1 (by rfl) ⟨12123239, by rfl⟩ : syracuseStep 16164319 = 24246479) B24246479
theorem B21552425 : Blo 1991435 21552425 := bstep (se 2 (by rfl) ⟨8082159, by rfl⟩ : syracuseStep 21552425 = 16164319) B16164319
theorem B14368283 : Blo 1991435 14368283 := bstep (se 1 (by rfl) ⟨10776212, by rfl⟩ : syracuseStep 14368283 = 21552425) B21552425
theorem B9578855 : Blo 1991435 9578855 := bstep (se 1 (by rfl) ⟨7184141, by rfl⟩ : syracuseStep 9578855 = 14368283) B14368283
theorem B25543613 : Blo 1991435 25543613 := bstep (se 3 (by rfl) ⟨4789427, by rfl⟩ : syracuseStep 25543613 = 9578855) B9578855
theorem B17029075 : Blo 1991435 17029075 := bstep (se 1 (by rfl) ⟨12771806, by rfl⟩ : syracuseStep 17029075 = 25543613) B25543613
theorem B22705433 : Blo 1991435 22705433 := bstep (se 2 (by rfl) ⟨8514537, by rfl⟩ : syracuseStep 22705433 = 17029075) B17029075
theorem B15136955 : Blo 1991435 15136955 := bstep (se 1 (by rfl) ⟨11352716, by rfl⟩ : syracuseStep 15136955 = 22705433) B22705433
theorem B10091303 : Blo 1991435 10091303 := bstep (se 1 (by rfl) ⟨7568477, by rfl⟩ : syracuseStep 10091303 = 15136955) B15136955
theorem B6727535 : Blo 1991435 6727535 := bstep (se 1 (by rfl) ⟨5045651, by rfl⟩ : syracuseStep 6727535 = 10091303) B10091303
theorem B4485023 : Blo 1991435 4485023 := bstep (se 1 (by rfl) ⟨3363767, by rfl⟩ : syracuseStep 4485023 = 6727535) B6727535
theorem B2990015 : Blo 1991435 2990015 := bstep (se 1 (by rfl) ⟨2242511, by rfl⟩ : syracuseStep 2990015 = 4485023) B4485023
theorem B1993343 : Blo 1991435 1993343 := bstep (se 1 (by rfl) ⟨1495007, by rfl⟩ : syracuseStep 1993343 = 2990015) B2990015
theorem B2990021 : Blo 1991435 2990021 := bbase (se 4 (by rfl) ⟨280314, by rfl⟩ : syracuseStep 2990021 = 560629) (by norm_num)
theorem B1993347 : Blo 1991435 1993347 := bstep (se 1 (by rfl) ⟨1495010, by rfl⟩ : syracuseStep 1993347 = 2990021) B2990021
theorem B3363781 : Blo 1991435 3363781 := bbase (se 4 (by rfl) ⟨315354, by rfl⟩ : syracuseStep 3363781 = 630709) (by norm_num)
theorem B4485041 : Blo 1991435 4485041 := bstep (se 2 (by rfl) ⟨1681890, by rfl⟩ : syracuseStep 4485041 = 3363781) B3363781
theorem B2990027 : Blo 1991435 2990027 := bstep (se 1 (by rfl) ⟨2242520, by rfl⟩ : syracuseStep 2990027 = 4485041) B4485041
theorem B1993351 : Blo 1991435 1993351 := bstep (se 1 (by rfl) ⟨1495013, by rfl⟩ : syracuseStep 1993351 = 2990027) B2990027
theorem B2242525 : Blo 1991435 2242525 := bbase (se 3 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 2242525 = 840947) (by norm_num)
theorem B2990033 : Blo 1991435 2990033 := bstep (se 2 (by rfl) ⟨1121262, by rfl⟩ : syracuseStep 2990033 = 2242525) B2242525
theorem B1993355 : Blo 1991435 1993355 := bstep (se 1 (by rfl) ⟨1495016, by rfl⟩ : syracuseStep 1993355 = 2990033) B2990033
theorem B6727589 : Blo 1991435 6727589 := bbase (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) (by norm_num)
theorem B4485059 : Blo 1991435 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B2990039 : Blo 1991435 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B1993359 : Blo 1991435 1993359 := bstep (se 1 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 1993359 = 2990039) B2990039
theorem B2990045 : Blo 1991435 2990045 := bbase (se 3 (by rfl) ⟨560633, by rfl⟩ : syracuseStep 2990045 = 1121267) (by norm_num)
theorem B1993363 : Blo 1991435 1993363 := bstep (se 1 (by rfl) ⟨1495022, by rfl⟩ : syracuseStep 1993363 = 2990045) B2990045
theorem B4485077 : Blo 1991435 4485077 := bbase (se 7 (by rfl) ⟨52559, by rfl⟩ : syracuseStep 4485077 = 105119) (by norm_num)
theorem B2990051 : Blo 1991435 2990051 := bstep (se 1 (by rfl) ⟨2242538, by rfl⟩ : syracuseStep 2990051 = 4485077) B4485077
theorem B1993367 : Blo 1991435 1993367 := bstep (se 1 (by rfl) ⟨1495025, by rfl⟩ : syracuseStep 1993367 = 2990051) B2990051
theorem B12771989 : Blo 1991435 12771989 := bbase (se 6 (by rfl) ⟨299343, by rfl⟩ : syracuseStep 12771989 = 598687) (by norm_num)
theorem B8514659 : Blo 1991435 8514659 := bstep (se 1 (by rfl) ⟨6385994, by rfl⟩ : syracuseStep 8514659 = 12771989) B12771989
theorem B5676439 : Blo 1991435 5676439 := bstep (se 1 (by rfl) ⟨4257329, by rfl⟩ : syracuseStep 5676439 = 8514659) B8514659
theorem B7568585 : Blo 1991435 7568585 := bstep (se 2 (by rfl) ⟨2838219, by rfl⟩ : syracuseStep 7568585 = 5676439) B5676439
theorem B5045723 : Blo 1991435 5045723 := bstep (se 1 (by rfl) ⟨3784292, by rfl⟩ : syracuseStep 5045723 = 7568585) B7568585
theorem B3363815 : Blo 1991435 3363815 := bstep (se 1 (by rfl) ⟨2522861, by rfl⟩ : syracuseStep 3363815 = 5045723) B5045723
theorem B2242543 : Blo 1991435 2242543 := bstep (se 1 (by rfl) ⟨1681907, by rfl⟩ : syracuseStep 2242543 = 3363815) B3363815
theorem B2990057 : Blo 1991435 2990057 := bstep (se 2 (by rfl) ⟨1121271, by rfl⟩ : syracuseStep 2990057 = 2242543) B2242543
theorem B1993371 : Blo 1991435 1993371 := bstep (se 1 (by rfl) ⟨1495028, by rfl⟩ : syracuseStep 1993371 = 2990057) B2990057
theorem B2020573 : Blo 1991435 2020573 := bbase (se 3 (by rfl) ⟨378857, by rfl⟩ : syracuseStep 2020573 = 757715) (by norm_num)
theorem B2694097 : Blo 1991435 2694097 := bstep (se 2 (by rfl) ⟨1010286, by rfl⟩ : syracuseStep 2694097 = 2020573) B2020573
theorem B3592129 : Blo 1991435 3592129 := bstep (se 2 (by rfl) ⟨1347048, by rfl⟩ : syracuseStep 3592129 = 2694097) B2694097
theorem B4789505 : Blo 1991435 4789505 := bstep (se 2 (by rfl) ⟨1796064, by rfl⟩ : syracuseStep 4789505 = 3592129) B3592129
theorem B3193003 : Blo 1991435 3193003 := bstep (se 1 (by rfl) ⟨2394752, by rfl⟩ : syracuseStep 3193003 = 4789505) B4789505
theorem B17029349 : Blo 1991435 17029349 := bstep (se 4 (by rfl) ⟨1596501, by rfl⟩ : syracuseStep 17029349 = 3193003) B3193003
theorem B11352899 : Blo 1991435 11352899 := bstep (se 1 (by rfl) ⟨8514674, by rfl⟩ : syracuseStep 11352899 = 17029349) B17029349
theorem B7568599 : Blo 1991435 7568599 := bstep (se 1 (by rfl) ⟨5676449, by rfl⟩ : syracuseStep 7568599 = 11352899) B11352899
theorem B10091465 : Blo 1991435 10091465 := bstep (se 2 (by rfl) ⟨3784299, by rfl⟩ : syracuseStep 10091465 = 7568599) B7568599
theorem B6727643 : Blo 1991435 6727643 := bstep (se 1 (by rfl) ⟨5045732, by rfl⟩ : syracuseStep 6727643 = 10091465) B10091465
theorem B4485095 : Blo 1991435 4485095 := bstep (se 1 (by rfl) ⟨3363821, by rfl⟩ : syracuseStep 4485095 = 6727643) B6727643
theorem B2990063 : Blo 1991435 2990063 := bstep (se 1 (by rfl) ⟨2242547, by rfl⟩ : syracuseStep 2990063 = 4485095) B4485095
theorem B1993375 : Blo 1991435 1993375 := bstep (se 1 (by rfl) ⟨1495031, by rfl⟩ : syracuseStep 1993375 = 2990063) B2990063
theorem B2990069 : Blo 1991435 2990069 := bbase (se 5 (by rfl) ⟨140159, by rfl⟩ : syracuseStep 2990069 = 280319) (by norm_num)
theorem B1993379 : Blo 1991435 1993379 := bstep (se 1 (by rfl) ⟨1495034, by rfl⟩ : syracuseStep 1993379 = 2990069) B2990069
theorem B4789525 : Blo 1991435 4789525 := bbase (se 6 (by rfl) ⟨112254, by rfl⟩ : syracuseStep 4789525 = 224509) (by norm_num)
theorem B6386033 : Blo 1991435 6386033 := bstep (se 2 (by rfl) ⟨2394762, by rfl⟩ : syracuseStep 6386033 = 4789525) B4789525
theorem B4257355 : Blo 1991435 4257355 := bstep (se 1 (by rfl) ⟨3193016, by rfl⟩ : syracuseStep 4257355 = 6386033) B6386033
theorem B5676473 : Blo 1991435 5676473 := bstep (se 2 (by rfl) ⟨2128677, by rfl⟩ : syracuseStep 5676473 = 4257355) B4257355
theorem B3784315 : Blo 1991435 3784315 := bstep (se 1 (by rfl) ⟨2838236, by rfl⟩ : syracuseStep 3784315 = 5676473) B5676473
theorem B5045753 : Blo 1991435 5045753 := bstep (se 2 (by rfl) ⟨1892157, by rfl⟩ : syracuseStep 5045753 = 3784315) B3784315
theorem B3363835 : Blo 1991435 3363835 := bstep (se 1 (by rfl) ⟨2522876, by rfl⟩ : syracuseStep 3363835 = 5045753) B5045753
theorem B4485113 : Blo 1991435 4485113 := bstep (se 2 (by rfl) ⟨1681917, by rfl⟩ : syracuseStep 4485113 = 3363835) B3363835
theorem B2990075 : Blo 1991435 2990075 := bstep (se 1 (by rfl) ⟨2242556, by rfl⟩ : syracuseStep 2990075 = 4485113) B4485113
theorem B1993383 : Blo 1991435 1993383 := bstep (se 1 (by rfl) ⟨1495037, by rfl⟩ : syracuseStep 1993383 = 2990075) B2990075
theorem B2242561 : Blo 1991435 2242561 := bbase (se 2 (by rfl) ⟨840960, by rfl⟩ : syracuseStep 2242561 = 1681921) (by norm_num)
theorem B2990081 : Blo 1991435 2990081 := bstep (se 2 (by rfl) ⟨1121280, by rfl⟩ : syracuseStep 2990081 = 2242561) B2242561
theorem B1993387 : Blo 1991435 1993387 := bstep (se 1 (by rfl) ⟨1495040, by rfl⟩ : syracuseStep 1993387 = 2990081) B2990081
theorem B5045773 : Blo 1991435 5045773 := bbase (se 3 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 5045773 = 1892165) (by norm_num)
theorem B6727697 : Blo 1991435 6727697 := bstep (se 2 (by rfl) ⟨2522886, by rfl⟩ : syracuseStep 6727697 = 5045773) B5045773
theorem B4485131 : Blo 1991435 4485131 := bstep (se 1 (by rfl) ⟨3363848, by rfl⟩ : syracuseStep 4485131 = 6727697) B6727697
theorem B2990087 : Blo 1991435 2990087 := bstep (se 1 (by rfl) ⟨2242565, by rfl⟩ : syracuseStep 2990087 = 4485131) B4485131
theorem B1993391 : Blo 1991435 1993391 := bstep (se 1 (by rfl) ⟨1495043, by rfl⟩ : syracuseStep 1993391 = 2990087) B2990087
theorem B2990093 : Blo 1991435 2990093 := bbase (se 3 (by rfl) ⟨560642, by rfl⟩ : syracuseStep 2990093 = 1121285) (by norm_num)
theorem B1993395 : Blo 1991435 1993395 := bstep (se 1 (by rfl) ⟨1495046, by rfl⟩ : syracuseStep 1993395 = 2990093) B2990093
theorem B4485149 : Blo 1991435 4485149 := bbase (se 3 (by rfl) ⟨840965, by rfl⟩ : syracuseStep 4485149 = 1681931) (by norm_num)
theorem B2990099 : Blo 1991435 2990099 := bstep (se 1 (by rfl) ⟨2242574, by rfl⟩ : syracuseStep 2990099 = 4485149) B4485149
theorem B1993399 : Blo 1991435 1993399 := bstep (se 1 (by rfl) ⟨1495049, by rfl⟩ : syracuseStep 1993399 = 2990099) B2990099
theorem B3363869 : Blo 1991435 3363869 := bbase (se 3 (by rfl) ⟨630725, by rfl⟩ : syracuseStep 3363869 = 1261451) (by norm_num)
theorem B2242579 : Blo 1991435 2242579 := bstep (se 1 (by rfl) ⟨1681934, by rfl⟩ : syracuseStep 2242579 = 3363869) B3363869
theorem B2990105 : Blo 1991435 2990105 := bstep (se 2 (by rfl) ⟨1121289, by rfl⟩ : syracuseStep 2990105 = 2242579) B2242579
theorem B1993403 : Blo 1991435 1993403 := bstep (se 1 (by rfl) ⟨1495052, by rfl⟩ : syracuseStep 1993403 = 2990105) B2990105
theorem B2048173 : Blo 1991435 2048173 := bbase (se 3 (by rfl) ⟨384032, by rfl⟩ : syracuseStep 2048173 = 768065) (by norm_num)
theorem B10923589 : Blo 1991435 10923589 := bstep (se 4 (by rfl) ⟨1024086, by rfl⟩ : syracuseStep 10923589 = 2048173) B2048173
theorem B14564785 : Blo 1991435 14564785 := bstep (se 2 (by rfl) ⟨5461794, by rfl⟩ : syracuseStep 14564785 = 10923589) B10923589
theorem B19419713 : Blo 1991435 19419713 := bstep (se 2 (by rfl) ⟨7282392, by rfl⟩ : syracuseStep 19419713 = 14564785) B14564785
theorem B12946475 : Blo 1991435 12946475 := bstep (se 1 (by rfl) ⟨9709856, by rfl⟩ : syracuseStep 12946475 = 19419713) B19419713
theorem B8630983 : Blo 1991435 8630983 := bstep (se 1 (by rfl) ⟨6473237, by rfl⟩ : syracuseStep 8630983 = 12946475) B12946475
theorem B11507977 : Blo 1991435 11507977 := bstep (se 2 (by rfl) ⟨4315491, by rfl⟩ : syracuseStep 11507977 = 8630983) B8630983
theorem B61375877 : Blo 1991435 61375877 := bstep (se 4 (by rfl) ⟨5753988, by rfl⟩ : syracuseStep 61375877 = 11507977) B11507977
theorem B40917251 : Blo 1991435 40917251 := bstep (se 1 (by rfl) ⟨30687938, by rfl⟩ : syracuseStep 40917251 = 61375877) B61375877
theorem B27278167 : Blo 1991435 27278167 := bstep (se 1 (by rfl) ⟨20458625, by rfl⟩ : syracuseStep 27278167 = 40917251) B40917251
theorem B36370889 : Blo 1991435 36370889 := bstep (se 2 (by rfl) ⟨13639083, by rfl⟩ : syracuseStep 36370889 = 27278167) B27278167
theorem B24247259 : Blo 1991435 24247259 := bstep (se 1 (by rfl) ⟨18185444, by rfl⟩ : syracuseStep 24247259 = 36370889) B36370889
theorem B16164839 : Blo 1991435 16164839 := bstep (se 1 (by rfl) ⟨12123629, by rfl⟩ : syracuseStep 16164839 = 24247259) B24247259
theorem B10776559 : Blo 1991435 10776559 := bstep (se 1 (by rfl) ⟨8082419, by rfl⟩ : syracuseStep 10776559 = 16164839) B16164839
theorem B14368745 : Blo 1991435 14368745 := bstep (se 2 (by rfl) ⟨5388279, by rfl⟩ : syracuseStep 14368745 = 10776559) B10776559
theorem B9579163 : Blo 1991435 9579163 := bstep (se 1 (by rfl) ⟨7184372, by rfl⟩ : syracuseStep 9579163 = 14368745) B14368745
theorem B12772217 : Blo 1991435 12772217 := bstep (se 2 (by rfl) ⟨4789581, by rfl⟩ : syracuseStep 12772217 = 9579163) B9579163
theorem B8514811 : Blo 1991435 8514811 := bstep (se 1 (by rfl) ⟨6386108, by rfl⟩ : syracuseStep 8514811 = 12772217) B12772217
theorem B11353081 : Blo 1991435 11353081 := bstep (se 2 (by rfl) ⟨4257405, by rfl⟩ : syracuseStep 11353081 = 8514811) B8514811
theorem B15137441 : Blo 1991435 15137441 := bstep (se 2 (by rfl) ⟨5676540, by rfl⟩ : syracuseStep 15137441 = 11353081) B11353081
theorem B10091627 : Blo 1991435 10091627 := bstep (se 1 (by rfl) ⟨7568720, by rfl⟩ : syracuseStep 10091627 = 15137441) B15137441
theorem B6727751 : Blo 1991435 6727751 := bstep (se 1 (by rfl) ⟨5045813, by rfl⟩ : syracuseStep 6727751 = 10091627) B10091627
theorem B4485167 : Blo 1991435 4485167 := bstep (se 1 (by rfl) ⟨3363875, by rfl⟩ : syracuseStep 4485167 = 6727751) B6727751
theorem B2990111 : Blo 1991435 2990111 := bstep (se 1 (by rfl) ⟨2242583, by rfl⟩ : syracuseStep 2990111 = 4485167) B4485167
theorem B1993407 : Blo 1991435 1993407 := bstep (se 1 (by rfl) ⟨1495055, by rfl⟩ : syracuseStep 1993407 = 2990111) B2990111
theorem B2990117 : Blo 1991435 2990117 := bbase (se 4 (by rfl) ⟨280323, by rfl⟩ : syracuseStep 2990117 = 560647) (by norm_num)
theorem B1993411 : Blo 1991435 1993411 := bstep (se 1 (by rfl) ⟨1495058, by rfl⟩ : syracuseStep 1993411 = 2990117) B2990117
theorem B2522917 : Blo 1991435 2522917 := bbase (se 4 (by rfl) ⟨236523, by rfl⟩ : syracuseStep 2522917 = 473047) (by norm_num)
theorem B3363889 : Blo 1991435 3363889 := bstep (se 2 (by rfl) ⟨1261458, by rfl⟩ : syracuseStep 3363889 = 2522917) B2522917
theorem B4485185 : Blo 1991435 4485185 := bstep (se 2 (by rfl) ⟨1681944, by rfl⟩ : syracuseStep 4485185 = 3363889) B3363889
theorem B2990123 : Blo 1991435 2990123 := bstep (se 1 (by rfl) ⟨2242592, by rfl⟩ : syracuseStep 2990123 = 4485185) B4485185
theorem B1993415 : Blo 1991435 1993415 := bstep (se 1 (by rfl) ⟨1495061, by rfl⟩ : syracuseStep 1993415 = 2990123) B2990123
theorem B2242597 : Blo 1991435 2242597 := bbase (se 4 (by rfl) ⟨210243, by rfl⟩ : syracuseStep 2242597 = 420487) (by norm_num)
theorem B2990129 : Blo 1991435 2990129 := bstep (se 2 (by rfl) ⟨1121298, by rfl⟩ : syracuseStep 2990129 = 2242597) B2242597
theorem B1993419 : Blo 1991435 1993419 := bstep (se 1 (by rfl) ⟨1495064, by rfl⟩ : syracuseStep 1993419 = 2990129) B2990129
theorem B4789621 : Blo 1991435 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B6386161 : Blo 1991435 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B8514881 : Blo 1991435 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B5676587 : Blo 1991435 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B3784391 : Blo 1991435 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B2522927 : Blo 1991435 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B6727805 : Blo 1991435 6727805 := bstep (se 3 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 6727805 = 2522927) B2522927
theorem B4485203 : Blo 1991435 4485203 := bstep (se 1 (by rfl) ⟨3363902, by rfl⟩ : syracuseStep 4485203 = 6727805) B6727805
theorem B2990135 : Blo 1991435 2990135 := bstep (se 1 (by rfl) ⟨2242601, by rfl⟩ : syracuseStep 2990135 = 4485203) B4485203
theorem B1993423 : Blo 1991435 1993423 := bstep (se 1 (by rfl) ⟨1495067, by rfl⟩ : syracuseStep 1993423 = 2990135) B2990135
theorem B2990141 : Blo 1991435 2990141 := bbase (se 3 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 2990141 = 1121303) (by norm_num)
theorem B1993427 : Blo 1991435 1993427 := bstep (se 1 (by rfl) ⟨1495070, by rfl⟩ : syracuseStep 1993427 = 2990141) B2990141
theorem B4485221 : Blo 1991435 4485221 := bbase (se 4 (by rfl) ⟨420489, by rfl⟩ : syracuseStep 4485221 = 840979) (by norm_num)
theorem B2990147 : Blo 1991435 2990147 := bstep (se 1 (by rfl) ⟨2242610, by rfl⟩ : syracuseStep 2990147 = 4485221) B4485221
theorem B1993431 : Blo 1991435 1993431 := bstep (se 1 (by rfl) ⟨1495073, by rfl⟩ : syracuseStep 1993431 = 2990147) B2990147
theorem B5045885 : Blo 1991435 5045885 := bbase (se 3 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 5045885 = 1892207) (by norm_num)
theorem B3363923 : Blo 1991435 3363923 := bstep (se 1 (by rfl) ⟨2522942, by rfl⟩ : syracuseStep 3363923 = 5045885) B5045885
theorem B2242615 : Blo 1991435 2242615 := bstep (se 1 (by rfl) ⟨1681961, by rfl⟩ : syracuseStep 2242615 = 3363923) B3363923
theorem B2990153 : Blo 1991435 2990153 := bstep (se 2 (by rfl) ⟨1121307, by rfl⟩ : syracuseStep 2990153 = 2242615) B2242615
theorem B1993435 : Blo 1991435 1993435 := bstep (se 1 (by rfl) ⟨1495076, by rfl⟩ : syracuseStep 1993435 = 2990153) B2990153
theorem C0 (j : ℕ) (h1 : 497858 ≤ j) (h2 : j ≤ 498358) : Blo 1991435 (4 * j + 3) := by
  interval_cases j
  · exact B1991435
  · exact B1991439
  · exact B1991443
  · exact B1991447
  · exact B1991451
  · exact B1991455
  · exact B1991459
  · exact B1991463
  · exact B1991467
  · exact B1991471
  · exact B1991475
  · exact B1991479
  · exact B1991483
  · exact B1991487
  · exact B1991491
  · exact B1991495
  · exact B1991499
  · exact B1991503
  · exact B1991507
  · exact B1991511
  · exact B1991515
  · exact B1991519
  · exact B1991523
  · exact B1991527
  · exact B1991531
  · exact B1991535
  · exact B1991539
  · exact B1991543
  · exact B1991547
  · exact B1991551
  · exact B1991555
  · exact B1991559
  · exact B1991563
  · exact B1991567
  · exact B1991571
  · exact B1991575
  · exact B1991579
  · exact B1991583
  · exact B1991587
  · exact B1991591
  · exact B1991595
  · exact B1991599
  · exact B1991603
  · exact B1991607
  · exact B1991611
  · exact B1991615
  · exact B1991619
  · exact B1991623
  · exact B1991627
  · exact B1991631
  · exact B1991635
  · exact B1991639
  · exact B1991643
  · exact B1991647
  · exact B1991651
  · exact B1991655
  · exact B1991659
  · exact B1991663
  · exact B1991667
  · exact B1991671
  · exact B1991675
  · exact B1991679
  · exact B1991683
  · exact B1991687
  · exact B1991691
  · exact B1991695
  · exact B1991699
  · exact B1991703
  · exact B1991707
  · exact B1991711
  · exact B1991715
  · exact B1991719
  · exact B1991723
  · exact B1991727
  · exact B1991731
  · exact B1991735
  · exact B1991739
  · exact B1991743
  · exact B1991747
  · exact B1991751
  · exact B1991755
  · exact B1991759
  · exact B1991763
  · exact B1991767
  · exact B1991771
  · exact B1991775
  · exact B1991779
  · exact B1991783
  · exact B1991787
  · exact B1991791
  · exact B1991795
  · exact B1991799
  · exact B1991803
  · exact B1991807
  · exact B1991811
  · exact B1991815
  · exact B1991819
  · exact B1991823
  · exact B1991827
  · exact B1991831
  · exact B1991835
  · exact B1991839
  · exact B1991843
  · exact B1991847
  · exact B1991851
  · exact B1991855
  · exact B1991859
  · exact B1991863
  · exact B1991867
  · exact B1991871
  · exact B1991875
  · exact B1991879
  · exact B1991883
  · exact B1991887
  · exact B1991891
  · exact B1991895
  · exact B1991899
  · exact B1991903
  · exact B1991907
  · exact B1991911
  · exact B1991915
  · exact B1991919
  · exact B1991923
  · exact B1991927
  · exact B1991931
  · exact B1991935
  · exact B1991939
  · exact B1991943
  · exact B1991947
  · exact B1991951
  · exact B1991955
  · exact B1991959
  · exact B1991963
  · exact B1991967
  · exact B1991971
  · exact B1991975
  · exact B1991979
  · exact B1991983
  · exact B1991987
  · exact B1991991
  · exact B1991995
  · exact B1991999
  · exact B1992003
  · exact B1992007
  · exact B1992011
  · exact B1992015
  · exact B1992019
  · exact B1992023
  · exact B1992027
  · exact B1992031
  · exact B1992035
  · exact B1992039
  · exact B1992043
  · exact B1992047
  · exact B1992051
  · exact B1992055
  · exact B1992059
  · exact B1992063
  · exact B1992067
  · exact B1992071
  · exact B1992075
  · exact B1992079
  · exact B1992083
  · exact B1992087
  · exact B1992091
  · exact B1992095
  · exact B1992099
  · exact B1992103
  · exact B1992107
  · exact B1992111
  · exact B1992115
  · exact B1992119
  · exact B1992123
  · exact B1992127
  · exact B1992131
  · exact B1992135
  · exact B1992139
  · exact B1992143
  · exact B1992147
  · exact B1992151
  · exact B1992155
  · exact B1992159
  · exact B1992163
  · exact B1992167
  · exact B1992171
  · exact B1992175
  · exact B1992179
  · exact B1992183
  · exact B1992187
  · exact B1992191
  · exact B1992195
  · exact B1992199
  · exact B1992203
  · exact B1992207
  · exact B1992211
  · exact B1992215
  · exact B1992219
  · exact B1992223
  · exact B1992227
  · exact B1992231
  · exact B1992235
  · exact B1992239
  · exact B1992243
  · exact B1992247
  · exact B1992251
  · exact B1992255
  · exact B1992259
  · exact B1992263
  · exact B1992267
  · exact B1992271
  · exact B1992275
  · exact B1992279
  · exact B1992283
  · exact B1992287
  · exact B1992291
  · exact B1992295
  · exact B1992299
  · exact B1992303
  · exact B1992307
  · exact B1992311
  · exact B1992315
  · exact B1992319
  · exact B1992323
  · exact B1992327
  · exact B1992331
  · exact B1992335
  · exact B1992339
  · exact B1992343
  · exact B1992347
  · exact B1992351
  · exact B1992355
  · exact B1992359
  · exact B1992363
  · exact B1992367
  · exact B1992371
  · exact B1992375
  · exact B1992379
  · exact B1992383
  · exact B1992387
  · exact B1992391
  · exact B1992395
  · exact B1992399
  · exact B1992403
  · exact B1992407
  · exact B1992411
  · exact B1992415
  · exact B1992419
  · exact B1992423
  · exact B1992427
  · exact B1992431
  · exact B1992435
  · exact B1992439
  · exact B1992443
  · exact B1992447
  · exact B1992451
  · exact B1992455
  · exact B1992459
  · exact B1992463
  · exact B1992467
  · exact B1992471
  · exact B1992475
  · exact B1992479
  · exact B1992483
  · exact B1992487
  · exact B1992491
  · exact B1992495
  · exact B1992499
  · exact B1992503
  · exact B1992507
  · exact B1992511
  · exact B1992515
  · exact B1992519
  · exact B1992523
  · exact B1992527
  · exact B1992531
  · exact B1992535
  · exact B1992539
  · exact B1992543
  · exact B1992547
  · exact B1992551
  · exact B1992555
  · exact B1992559
  · exact B1992563
  · exact B1992567
  · exact B1992571
  · exact B1992575
  · exact B1992579
  · exact B1992583
  · exact B1992587
  · exact B1992591
  · exact B1992595
  · exact B1992599
  · exact B1992603
  · exact B1992607
  · exact B1992611
  · exact B1992615
  · exact B1992619
  · exact B1992623
  · exact B1992627
  · exact B1992631
  · exact B1992635
  · exact B1992639
  · exact B1992643
  · exact B1992647
  · exact B1992651
  · exact B1992655
  · exact B1992659
  · exact B1992663
  · exact B1992667
  · exact B1992671
  · exact B1992675
  · exact B1992679
  · exact B1992683
  · exact B1992687
  · exact B1992691
  · exact B1992695
  · exact B1992699
  · exact B1992703
  · exact B1992707
  · exact B1992711
  · exact B1992715
  · exact B1992719
  · exact B1992723
  · exact B1992727
  · exact B1992731
  · exact B1992735
  · exact B1992739
  · exact B1992743
  · exact B1992747
  · exact B1992751
  · exact B1992755
  · exact B1992759
  · exact B1992763
  · exact B1992767
  · exact B1992771
  · exact B1992775
  · exact B1992779
  · exact B1992783
  · exact B1992787
  · exact B1992791
  · exact B1992795
  · exact B1992799
  · exact B1992803
  · exact B1992807
  · exact B1992811
  · exact B1992815
  · exact B1992819
  · exact B1992823
  · exact B1992827
  · exact B1992831
  · exact B1992835
  · exact B1992839
  · exact B1992843
  · exact B1992847
  · exact B1992851
  · exact B1992855
  · exact B1992859
  · exact B1992863
  · exact B1992867
  · exact B1992871
  · exact B1992875
  · exact B1992879
  · exact B1992883
  · exact B1992887
  · exact B1992891
  · exact B1992895
  · exact B1992899
  · exact B1992903
  · exact B1992907
  · exact B1992911
  · exact B1992915
  · exact B1992919
  · exact B1992923
  · exact B1992927
  · exact B1992931
  · exact B1992935
  · exact B1992939
  · exact B1992943
  · exact B1992947
  · exact B1992951
  · exact B1992955
  · exact B1992959
  · exact B1992963
  · exact B1992967
  · exact B1992971
  · exact B1992975
  · exact B1992979
  · exact B1992983
  · exact B1992987
  · exact B1992991
  · exact B1992995
  · exact B1992999
  · exact B1993003
  · exact B1993007
  · exact B1993011
  · exact B1993015
  · exact B1993019
  · exact B1993023
  · exact B1993027
  · exact B1993031
  · exact B1993035
  · exact B1993039
  · exact B1993043
  · exact B1993047
  · exact B1993051
  · exact B1993055
  · exact B1993059
  · exact B1993063
  · exact B1993067
  · exact B1993071
  · exact B1993075
  · exact B1993079
  · exact B1993083
  · exact B1993087
  · exact B1993091
  · exact B1993095
  · exact B1993099
  · exact B1993103
  · exact B1993107
  · exact B1993111
  · exact B1993115
  · exact B1993119
  · exact B1993123
  · exact B1993127
  · exact B1993131
  · exact B1993135
  · exact B1993139
  · exact B1993143
  · exact B1993147
  · exact B1993151
  · exact B1993155
  · exact B1993159
  · exact B1993163
  · exact B1993167
  · exact B1993171
  · exact B1993175
  · exact B1993179
  · exact B1993183
  · exact B1993187
  · exact B1993191
  · exact B1993195
  · exact B1993199
  · exact B1993203
  · exact B1993207
  · exact B1993211
  · exact B1993215
  · exact B1993219
  · exact B1993223
  · exact B1993227
  · exact B1993231
  · exact B1993235
  · exact B1993239
  · exact B1993243
  · exact B1993247
  · exact B1993251
  · exact B1993255
  · exact B1993259
  · exact B1993263
  · exact B1993267
  · exact B1993271
  · exact B1993275
  · exact B1993279
  · exact B1993283
  · exact B1993287
  · exact B1993291
  · exact B1993295
  · exact B1993299
  · exact B1993303
  · exact B1993307
  · exact B1993311
  · exact B1993315
  · exact B1993319
  · exact B1993323
  · exact B1993327
  · exact B1993331
  · exact B1993335
  · exact B1993339
  · exact B1993343
  · exact B1993347
  · exact B1993351
  · exact B1993355
  · exact B1993359
  · exact B1993363
  · exact B1993367
  · exact B1993371
  · exact B1993375
  · exact B1993379
  · exact B1993383
  · exact B1993387
  · exact B1993391
  · exact B1993395
  · exact B1993399
  · exact B1993403
  · exact B1993407
  · exact B1993411
  · exact B1993415
  · exact B1993419
  · exact B1993423
  · exact B1993427
  · exact B1993431
  · exact B1993435
theorem solution (m : ℕ) (hlo : 1991435 ≤ m) (hhi : m ≤ 1993435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 497858 ≤ j := by omega
    have hj2 : j ≤ 498358 := by omega
    have hb : Blo 1991435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
