-- Prove2me | solution 1 for syracuse_descends_range_1969435_1971435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:00.58699+00:00
-- url     : https://prove2.me/submissions/1bb25e96-082c-47e6-aa03-bf1183154cdc

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

theorem B9593093 : Blo 1969435 9593093 := bbase (se 4 (by rfl) ⟨899352, by rfl⟩ : syracuseStep 9593093 = 1798705) (by norm_num)
theorem B25581581 : Blo 1969435 25581581 := bstep (se 3 (by rfl) ⟨4796546, by rfl⟩ : syracuseStep 25581581 = 9593093) B9593093
theorem B17054387 : Blo 1969435 17054387 := bstep (se 1 (by rfl) ⟨12790790, by rfl⟩ : syracuseStep 17054387 = 25581581) B25581581
theorem B11369591 : Blo 1969435 11369591 := bstep (se 1 (by rfl) ⟨8527193, by rfl⟩ : syracuseStep 11369591 = 17054387) B17054387
theorem B7579727 : Blo 1969435 7579727 := bstep (se 1 (by rfl) ⟨5684795, by rfl⟩ : syracuseStep 7579727 = 11369591) B11369591
theorem B5053151 : Blo 1969435 5053151 := bstep (se 1 (by rfl) ⟨3789863, by rfl⟩ : syracuseStep 5053151 = 7579727) B7579727
theorem B13475069 : Blo 1969435 13475069 := bstep (se 3 (by rfl) ⟨2526575, by rfl⟩ : syracuseStep 13475069 = 5053151) B5053151
theorem B8983379 : Blo 1969435 8983379 := bstep (se 1 (by rfl) ⟨6737534, by rfl⟩ : syracuseStep 8983379 = 13475069) B13475069
theorem B5988919 : Blo 1969435 5988919 := bstep (se 1 (by rfl) ⟨4491689, by rfl⟩ : syracuseStep 5988919 = 8983379) B8983379
theorem B7985225 : Blo 1969435 7985225 := bstep (se 2 (by rfl) ⟨2994459, by rfl⟩ : syracuseStep 7985225 = 5988919) B5988919
theorem B5323483 : Blo 1969435 5323483 := bstep (se 1 (by rfl) ⟨3992612, by rfl⟩ : syracuseStep 5323483 = 7985225) B7985225
theorem B7097977 : Blo 1969435 7097977 := bstep (se 2 (by rfl) ⟨2661741, by rfl⟩ : syracuseStep 7097977 = 5323483) B5323483
theorem B9463969 : Blo 1969435 9463969 := bstep (se 2 (by rfl) ⟨3548988, by rfl⟩ : syracuseStep 9463969 = 7097977) B7097977
theorem B12618625 : Blo 1969435 12618625 := bstep (se 2 (by rfl) ⟨4731984, by rfl⟩ : syracuseStep 12618625 = 9463969) B9463969
theorem B16824833 : Blo 1969435 16824833 := bstep (se 2 (by rfl) ⟨6309312, by rfl⟩ : syracuseStep 16824833 = 12618625) B12618625
theorem B11216555 : Blo 1969435 11216555 := bstep (se 1 (by rfl) ⟨8412416, by rfl⟩ : syracuseStep 11216555 = 16824833) B16824833
theorem B7477703 : Blo 1969435 7477703 := bstep (se 1 (by rfl) ⟨5608277, by rfl⟩ : syracuseStep 7477703 = 11216555) B11216555
theorem B4985135 : Blo 1969435 4985135 := bstep (se 1 (by rfl) ⟨3738851, by rfl⟩ : syracuseStep 4985135 = 7477703) B7477703
theorem B3323423 : Blo 1969435 3323423 := bstep (se 1 (by rfl) ⟨2492567, by rfl⟩ : syracuseStep 3323423 = 4985135) B4985135
theorem B2215615 : Blo 1969435 2215615 := bstep (se 1 (by rfl) ⟨1661711, by rfl⟩ : syracuseStep 2215615 = 3323423) B3323423
theorem B2954153 : Blo 1969435 2954153 := bstep (se 2 (by rfl) ⟨1107807, by rfl⟩ : syracuseStep 2954153 = 2215615) B2215615
theorem B1969435 : Blo 1969435 1969435 := bstep (se 1 (by rfl) ⟨1477076, by rfl⟩ : syracuseStep 1969435 = 2954153) B2954153
theorem B7477717 : Blo 1969435 7477717 := bbase (se 7 (by rfl) ⟨87629, by rfl⟩ : syracuseStep 7477717 = 175259) (by norm_num)
theorem B9970289 : Blo 1969435 9970289 := bstep (se 2 (by rfl) ⟨3738858, by rfl⟩ : syracuseStep 9970289 = 7477717) B7477717
theorem B6646859 : Blo 1969435 6646859 := bstep (se 1 (by rfl) ⟨4985144, by rfl⟩ : syracuseStep 6646859 = 9970289) B9970289
theorem B4431239 : Blo 1969435 4431239 := bstep (se 1 (by rfl) ⟨3323429, by rfl⟩ : syracuseStep 4431239 = 6646859) B6646859
theorem B2954159 : Blo 1969435 2954159 := bstep (se 1 (by rfl) ⟨2215619, by rfl⟩ : syracuseStep 2954159 = 4431239) B4431239
theorem B1969439 : Blo 1969435 1969439 := bstep (se 1 (by rfl) ⟨1477079, by rfl⟩ : syracuseStep 1969439 = 2954159) B2954159
theorem B2954165 : Blo 1969435 2954165 := bbase (se 5 (by rfl) ⟨138476, by rfl⟩ : syracuseStep 2954165 = 276953) (by norm_num)
theorem B1969443 : Blo 1969435 1969443 := bstep (se 1 (by rfl) ⟨1477082, by rfl⟩ : syracuseStep 1969443 = 2954165) B2954165
theorem B4985165 : Blo 1969435 4985165 := bbase (se 3 (by rfl) ⟨934718, by rfl⟩ : syracuseStep 4985165 = 1869437) (by norm_num)
theorem B3323443 : Blo 1969435 3323443 := bstep (se 1 (by rfl) ⟨2492582, by rfl⟩ : syracuseStep 3323443 = 4985165) B4985165
theorem B4431257 : Blo 1969435 4431257 := bstep (se 2 (by rfl) ⟨1661721, by rfl⟩ : syracuseStep 4431257 = 3323443) B3323443
theorem B2954171 : Blo 1969435 2954171 := bstep (se 1 (by rfl) ⟨2215628, by rfl⟩ : syracuseStep 2954171 = 4431257) B4431257
theorem B1969447 : Blo 1969435 1969447 := bstep (se 1 (by rfl) ⟨1477085, by rfl⟩ : syracuseStep 1969447 = 2954171) B2954171
theorem B2215633 : Blo 1969435 2215633 := bbase (se 2 (by rfl) ⟨830862, by rfl⟩ : syracuseStep 2215633 = 1661725) (by norm_num)
theorem B2954177 : Blo 1969435 2954177 := bstep (se 2 (by rfl) ⟨1107816, by rfl⟩ : syracuseStep 2954177 = 2215633) B2215633
theorem B1969451 : Blo 1969435 1969451 := bstep (se 1 (by rfl) ⟨1477088, by rfl⟩ : syracuseStep 1969451 = 2954177) B2954177
theorem B5053205 : Blo 1969435 5053205 := bbase (se 6 (by rfl) ⟨118434, by rfl⟩ : syracuseStep 5053205 = 236869) (by norm_num)
theorem B3368803 : Blo 1969435 3368803 := bstep (se 1 (by rfl) ⟨2526602, by rfl⟩ : syracuseStep 3368803 = 5053205) B5053205
theorem B4491737 : Blo 1969435 4491737 := bstep (se 2 (by rfl) ⟨1684401, by rfl⟩ : syracuseStep 4491737 = 3368803) B3368803
theorem B2994491 : Blo 1969435 2994491 := bstep (se 1 (by rfl) ⟨2245868, by rfl⟩ : syracuseStep 2994491 = 4491737) B4491737
theorem B1996327 : Blo 1969435 1996327 := bstep (se 1 (by rfl) ⟨1497245, by rfl⟩ : syracuseStep 1996327 = 2994491) B2994491
theorem B2661769 : Blo 1969435 2661769 := bstep (se 2 (by rfl) ⟨998163, by rfl⟩ : syracuseStep 2661769 = 1996327) B1996327
theorem B3549025 : Blo 1969435 3549025 := bstep (se 2 (by rfl) ⟨1330884, by rfl⟩ : syracuseStep 3549025 = 2661769) B2661769
theorem B4732033 : Blo 1969435 4732033 := bstep (se 2 (by rfl) ⟨1774512, by rfl⟩ : syracuseStep 4732033 = 3549025) B3549025
theorem B6309377 : Blo 1969435 6309377 := bstep (se 2 (by rfl) ⟨2366016, by rfl⟩ : syracuseStep 6309377 = 4732033) B4732033
theorem B4206251 : Blo 1969435 4206251 := bstep (se 1 (by rfl) ⟨3154688, by rfl⟩ : syracuseStep 4206251 = 6309377) B6309377
theorem B2804167 : Blo 1969435 2804167 := bstep (se 1 (by rfl) ⟨2103125, by rfl⟩ : syracuseStep 2804167 = 4206251) B4206251
theorem B3738889 : Blo 1969435 3738889 := bstep (se 2 (by rfl) ⟨1402083, by rfl⟩ : syracuseStep 3738889 = 2804167) B2804167
theorem B4985185 : Blo 1969435 4985185 := bstep (se 2 (by rfl) ⟨1869444, by rfl⟩ : syracuseStep 4985185 = 3738889) B3738889
theorem B6646913 : Blo 1969435 6646913 := bstep (se 2 (by rfl) ⟨2492592, by rfl⟩ : syracuseStep 6646913 = 4985185) B4985185
theorem B4431275 : Blo 1969435 4431275 := bstep (se 1 (by rfl) ⟨3323456, by rfl⟩ : syracuseStep 4431275 = 6646913) B6646913
theorem B2954183 : Blo 1969435 2954183 := bstep (se 1 (by rfl) ⟨2215637, by rfl⟩ : syracuseStep 2954183 = 4431275) B4431275
theorem B1969455 : Blo 1969435 1969455 := bstep (se 1 (by rfl) ⟨1477091, by rfl⟩ : syracuseStep 1969455 = 2954183) B2954183
theorem B2954189 : Blo 1969435 2954189 := bbase (se 3 (by rfl) ⟨553910, by rfl⟩ : syracuseStep 2954189 = 1107821) (by norm_num)
theorem B1969459 : Blo 1969435 1969459 := bstep (se 1 (by rfl) ⟨1477094, by rfl⟩ : syracuseStep 1969459 = 2954189) B2954189
theorem B4431293 : Blo 1969435 4431293 := bbase (se 3 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 4431293 = 1661735) (by norm_num)
theorem B2954195 : Blo 1969435 2954195 := bstep (se 1 (by rfl) ⟨2215646, by rfl⟩ : syracuseStep 2954195 = 4431293) B4431293
theorem B1969463 : Blo 1969435 1969463 := bstep (se 1 (by rfl) ⟨1477097, by rfl⟩ : syracuseStep 1969463 = 2954195) B2954195
theorem B3323477 : Blo 1969435 3323477 := bbase (se 8 (by rfl) ⟨19473, by rfl⟩ : syracuseStep 3323477 = 38947) (by norm_num)
theorem B2215651 : Blo 1969435 2215651 := bstep (se 1 (by rfl) ⟨1661738, by rfl⟩ : syracuseStep 2215651 = 3323477) B3323477
theorem B2954201 : Blo 1969435 2954201 := bstep (se 2 (by rfl) ⟨1107825, by rfl⟩ : syracuseStep 2954201 = 2215651) B2215651
theorem B1969467 : Blo 1969435 1969467 := bstep (se 1 (by rfl) ⟨1477100, by rfl⟩ : syracuseStep 1969467 = 2954201) B2954201
theorem B3549053 : Blo 1969435 3549053 := bbase (se 3 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 3549053 = 1330895) (by norm_num)
theorem B9464141 : Blo 1969435 9464141 := bstep (se 3 (by rfl) ⟨1774526, by rfl⟩ : syracuseStep 9464141 = 3549053) B3549053
theorem B6309427 : Blo 1969435 6309427 := bstep (se 1 (by rfl) ⟨4732070, by rfl⟩ : syracuseStep 6309427 = 9464141) B9464141
theorem B8412569 : Blo 1969435 8412569 := bstep (se 2 (by rfl) ⟨3154713, by rfl⟩ : syracuseStep 8412569 = 6309427) B6309427
theorem B5608379 : Blo 1969435 5608379 := bstep (se 1 (by rfl) ⟨4206284, by rfl⟩ : syracuseStep 5608379 = 8412569) B8412569
theorem B14955677 : Blo 1969435 14955677 := bstep (se 3 (by rfl) ⟨2804189, by rfl⟩ : syracuseStep 14955677 = 5608379) B5608379
theorem B9970451 : Blo 1969435 9970451 := bstep (se 1 (by rfl) ⟨7477838, by rfl⟩ : syracuseStep 9970451 = 14955677) B14955677
theorem B6646967 : Blo 1969435 6646967 := bstep (se 1 (by rfl) ⟨4985225, by rfl⟩ : syracuseStep 6646967 = 9970451) B9970451
theorem B4431311 : Blo 1969435 4431311 := bstep (se 1 (by rfl) ⟨3323483, by rfl⟩ : syracuseStep 4431311 = 6646967) B6646967
theorem B2954207 : Blo 1969435 2954207 := bstep (se 1 (by rfl) ⟨2215655, by rfl⟩ : syracuseStep 2954207 = 4431311) B4431311
theorem B1969471 : Blo 1969435 1969471 := bstep (se 1 (by rfl) ⟨1477103, by rfl⟩ : syracuseStep 1969471 = 2954207) B2954207
theorem B2954213 : Blo 1969435 2954213 := bbase (se 4 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 2954213 = 553915) (by norm_num)
theorem B1969475 : Blo 1969435 1969475 := bstep (se 1 (by rfl) ⟨1477106, by rfl⟩ : syracuseStep 1969475 = 2954213) B2954213
theorem B15159797 : Blo 1969435 15159797 := bbase (se 5 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 15159797 = 1421231) (by norm_num)
theorem B10106531 : Blo 1969435 10106531 := bstep (se 1 (by rfl) ⟨7579898, by rfl⟩ : syracuseStep 10106531 = 15159797) B15159797
theorem B6737687 : Blo 1969435 6737687 := bstep (se 1 (by rfl) ⟨5053265, by rfl⟩ : syracuseStep 6737687 = 10106531) B10106531
theorem B4491791 : Blo 1969435 4491791 := bstep (se 1 (by rfl) ⟨3368843, by rfl⟩ : syracuseStep 4491791 = 6737687) B6737687
theorem B2994527 : Blo 1969435 2994527 := bstep (se 1 (by rfl) ⟨2245895, by rfl⟩ : syracuseStep 2994527 = 4491791) B4491791
theorem B7985405 : Blo 1969435 7985405 := bstep (se 3 (by rfl) ⟨1497263, by rfl⟩ : syracuseStep 7985405 = 2994527) B2994527
theorem B5323603 : Blo 1969435 5323603 := bstep (se 1 (by rfl) ⟨3992702, by rfl⟩ : syracuseStep 5323603 = 7985405) B7985405
theorem B7098137 : Blo 1969435 7098137 := bstep (se 2 (by rfl) ⟨2661801, by rfl⟩ : syracuseStep 7098137 = 5323603) B5323603
theorem B4732091 : Blo 1969435 4732091 := bstep (se 1 (by rfl) ⟨3549068, by rfl⟩ : syracuseStep 4732091 = 7098137) B7098137
theorem B3154727 : Blo 1969435 3154727 := bstep (se 1 (by rfl) ⟨2366045, by rfl⟩ : syracuseStep 3154727 = 4732091) B4732091
theorem B8412605 : Blo 1969435 8412605 := bstep (se 3 (by rfl) ⟨1577363, by rfl⟩ : syracuseStep 8412605 = 3154727) B3154727
theorem B5608403 : Blo 1969435 5608403 := bstep (se 1 (by rfl) ⟨4206302, by rfl⟩ : syracuseStep 5608403 = 8412605) B8412605
theorem B3738935 : Blo 1969435 3738935 := bstep (se 1 (by rfl) ⟨2804201, by rfl⟩ : syracuseStep 3738935 = 5608403) B5608403
theorem B2492623 : Blo 1969435 2492623 := bstep (se 1 (by rfl) ⟨1869467, by rfl⟩ : syracuseStep 2492623 = 3738935) B3738935
theorem B3323497 : Blo 1969435 3323497 := bstep (se 2 (by rfl) ⟨1246311, by rfl⟩ : syracuseStep 3323497 = 2492623) B2492623
theorem B4431329 : Blo 1969435 4431329 := bstep (se 2 (by rfl) ⟨1661748, by rfl⟩ : syracuseStep 4431329 = 3323497) B3323497
theorem B2954219 : Blo 1969435 2954219 := bstep (se 1 (by rfl) ⟨2215664, by rfl⟩ : syracuseStep 2954219 = 4431329) B4431329
theorem B1969479 : Blo 1969435 1969479 := bstep (se 1 (by rfl) ⟨1477109, by rfl⟩ : syracuseStep 1969479 = 2954219) B2954219
theorem B2215669 : Blo 1969435 2215669 := bbase (se 5 (by rfl) ⟨103859, by rfl⟩ : syracuseStep 2215669 = 207719) (by norm_num)
theorem B2954225 : Blo 1969435 2954225 := bstep (se 2 (by rfl) ⟨1107834, by rfl⟩ : syracuseStep 2954225 = 2215669) B2215669
theorem B1969483 : Blo 1969435 1969483 := bstep (se 1 (by rfl) ⟨1477112, by rfl⟩ : syracuseStep 1969483 = 2954225) B2954225
theorem B2492633 : Blo 1969435 2492633 := bbase (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) (by norm_num)
theorem B6647021 : Blo 1969435 6647021 := bstep (se 3 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 6647021 = 2492633) B2492633
theorem B4431347 : Blo 1969435 4431347 := bstep (se 1 (by rfl) ⟨3323510, by rfl⟩ : syracuseStep 4431347 = 6647021) B6647021
theorem B2954231 : Blo 1969435 2954231 := bstep (se 1 (by rfl) ⟨2215673, by rfl⟩ : syracuseStep 2954231 = 4431347) B4431347
theorem B1969487 : Blo 1969435 1969487 := bstep (se 1 (by rfl) ⟨1477115, by rfl⟩ : syracuseStep 1969487 = 2954231) B2954231
theorem B2954237 : Blo 1969435 2954237 := bbase (se 3 (by rfl) ⟨553919, by rfl⟩ : syracuseStep 2954237 = 1107839) (by norm_num)
theorem B1969491 : Blo 1969435 1969491 := bstep (se 1 (by rfl) ⟨1477118, by rfl⟩ : syracuseStep 1969491 = 2954237) B2954237
theorem B4431365 : Blo 1969435 4431365 := bbase (se 4 (by rfl) ⟨415440, by rfl⟩ : syracuseStep 4431365 = 830881) (by norm_num)
theorem B2954243 : Blo 1969435 2954243 := bstep (se 1 (by rfl) ⟨2215682, by rfl⟩ : syracuseStep 2954243 = 4431365) B4431365
theorem B1969495 : Blo 1969435 1969495 := bstep (se 1 (by rfl) ⟨1477121, by rfl⟩ : syracuseStep 1969495 = 2954243) B2954243
theorem B3738973 : Blo 1969435 3738973 := bbase (se 3 (by rfl) ⟨701057, by rfl⟩ : syracuseStep 3738973 = 1402115) (by norm_num)
theorem B4985297 : Blo 1969435 4985297 := bstep (se 2 (by rfl) ⟨1869486, by rfl⟩ : syracuseStep 4985297 = 3738973) B3738973
theorem B3323531 : Blo 1969435 3323531 := bstep (se 1 (by rfl) ⟨2492648, by rfl⟩ : syracuseStep 3323531 = 4985297) B4985297
theorem B2215687 : Blo 1969435 2215687 := bstep (se 1 (by rfl) ⟨1661765, by rfl⟩ : syracuseStep 2215687 = 3323531) B3323531
theorem B2954249 : Blo 1969435 2954249 := bstep (se 2 (by rfl) ⟨1107843, by rfl⟩ : syracuseStep 2954249 = 2215687) B2215687
theorem B1969499 : Blo 1969435 1969499 := bstep (se 1 (by rfl) ⟨1477124, by rfl⟩ : syracuseStep 1969499 = 2954249) B2954249
theorem B9970613 : Blo 1969435 9970613 := bbase (se 5 (by rfl) ⟨467372, by rfl⟩ : syracuseStep 9970613 = 934745) (by norm_num)
theorem B6647075 : Blo 1969435 6647075 := bstep (se 1 (by rfl) ⟨4985306, by rfl⟩ : syracuseStep 6647075 = 9970613) B9970613
theorem B4431383 : Blo 1969435 4431383 := bstep (se 1 (by rfl) ⟨3323537, by rfl⟩ : syracuseStep 4431383 = 6647075) B6647075
theorem B2954255 : Blo 1969435 2954255 := bstep (se 1 (by rfl) ⟨2215691, by rfl⟩ : syracuseStep 2954255 = 4431383) B4431383
theorem B1969503 : Blo 1969435 1969503 := bstep (se 1 (by rfl) ⟨1477127, by rfl⟩ : syracuseStep 1969503 = 2954255) B2954255
theorem B2954261 : Blo 1969435 2954261 := bbase (se 6 (by rfl) ⟨69240, by rfl⟩ : syracuseStep 2954261 = 138481) (by norm_num)
theorem B1969507 : Blo 1969435 1969507 := bstep (se 1 (by rfl) ⟨1477130, by rfl⟩ : syracuseStep 1969507 = 2954261) B2954261
theorem B2276573 : Blo 1969435 2276573 := bbase (se 3 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 2276573 = 853715) (by norm_num)
theorem B6070861 : Blo 1969435 6070861 := bstep (se 3 (by rfl) ⟨1138286, by rfl⟩ : syracuseStep 6070861 = 2276573) B2276573
theorem B8094481 : Blo 1969435 8094481 := bstep (se 2 (by rfl) ⟨3035430, by rfl⟩ : syracuseStep 8094481 = 6070861) B6070861
theorem B43170565 : Blo 1969435 43170565 := bstep (se 4 (by rfl) ⟨4047240, by rfl⟩ : syracuseStep 43170565 = 8094481) B8094481
theorem B57560753 : Blo 1969435 57560753 := bstep (se 2 (by rfl) ⟨21585282, by rfl⟩ : syracuseStep 57560753 = 43170565) B43170565
theorem B38373835 : Blo 1969435 38373835 := bstep (se 1 (by rfl) ⟨28780376, by rfl⟩ : syracuseStep 38373835 = 57560753) B57560753
theorem B51165113 : Blo 1969435 51165113 := bstep (se 2 (by rfl) ⟨19186917, by rfl⟩ : syracuseStep 51165113 = 38373835) B38373835
theorem B136440301 : Blo 1969435 136440301 := bstep (se 3 (by rfl) ⟨25582556, by rfl⟩ : syracuseStep 136440301 = 51165113) B51165113
theorem B181920401 : Blo 1969435 181920401 := bstep (se 2 (by rfl) ⟨68220150, by rfl⟩ : syracuseStep 181920401 = 136440301) B136440301
theorem B121280267 : Blo 1969435 121280267 := bstep (se 1 (by rfl) ⟨90960200, by rfl⟩ : syracuseStep 121280267 = 181920401) B181920401
theorem B80853511 : Blo 1969435 80853511 := bstep (se 1 (by rfl) ⟨60640133, by rfl⟩ : syracuseStep 80853511 = 121280267) B121280267
theorem B107804681 : Blo 1969435 107804681 := bstep (se 2 (by rfl) ⟨40426755, by rfl⟩ : syracuseStep 107804681 = 80853511) B80853511
theorem B71869787 : Blo 1969435 71869787 := bstep (se 1 (by rfl) ⟨53902340, by rfl⟩ : syracuseStep 71869787 = 107804681) B107804681
theorem B47913191 : Blo 1969435 47913191 := bstep (se 1 (by rfl) ⟨35934893, by rfl⟩ : syracuseStep 47913191 = 71869787) B71869787
theorem B31942127 : Blo 1969435 31942127 := bstep (se 1 (by rfl) ⟨23956595, by rfl⟩ : syracuseStep 31942127 = 47913191) B47913191
theorem B21294751 : Blo 1969435 21294751 := bstep (se 1 (by rfl) ⟨15971063, by rfl⟩ : syracuseStep 21294751 = 31942127) B31942127
theorem B28393001 : Blo 1969435 28393001 := bstep (se 2 (by rfl) ⟨10647375, by rfl⟩ : syracuseStep 28393001 = 21294751) B21294751
theorem B18928667 : Blo 1969435 18928667 := bstep (se 1 (by rfl) ⟨14196500, by rfl⟩ : syracuseStep 18928667 = 28393001) B28393001
theorem B12619111 : Blo 1969435 12619111 := bstep (se 1 (by rfl) ⟨9464333, by rfl⟩ : syracuseStep 12619111 = 18928667) B18928667
theorem B16825481 : Blo 1969435 16825481 := bstep (se 2 (by rfl) ⟨6309555, by rfl⟩ : syracuseStep 16825481 = 12619111) B12619111
theorem B11216987 : Blo 1969435 11216987 := bstep (se 1 (by rfl) ⟨8412740, by rfl⟩ : syracuseStep 11216987 = 16825481) B16825481
theorem B7477991 : Blo 1969435 7477991 := bstep (se 1 (by rfl) ⟨5608493, by rfl⟩ : syracuseStep 7477991 = 11216987) B11216987
theorem B4985327 : Blo 1969435 4985327 := bstep (se 1 (by rfl) ⟨3738995, by rfl⟩ : syracuseStep 4985327 = 7477991) B7477991
theorem B3323551 : Blo 1969435 3323551 := bstep (se 1 (by rfl) ⟨2492663, by rfl⟩ : syracuseStep 3323551 = 4985327) B4985327
theorem B4431401 : Blo 1969435 4431401 := bstep (se 2 (by rfl) ⟨1661775, by rfl⟩ : syracuseStep 4431401 = 3323551) B3323551
theorem B2954267 : Blo 1969435 2954267 := bstep (se 1 (by rfl) ⟨2215700, by rfl⟩ : syracuseStep 2954267 = 4431401) B4431401
theorem B1969511 : Blo 1969435 1969511 := bstep (se 1 (by rfl) ⟨1477133, by rfl⟩ : syracuseStep 1969511 = 2954267) B2954267
theorem B2215705 : Blo 1969435 2215705 := bbase (se 2 (by rfl) ⟨830889, by rfl⟩ : syracuseStep 2215705 = 1661779) (by norm_num)
theorem B2954273 : Blo 1969435 2954273 := bstep (se 2 (by rfl) ⟨1107852, by rfl⟩ : syracuseStep 2954273 = 2215705) B2215705
theorem B1969515 : Blo 1969435 1969515 := bstep (se 1 (by rfl) ⟨1477136, by rfl⟩ : syracuseStep 1969515 = 2954273) B2954273
theorem B7478021 : Blo 1969435 7478021 := bbase (se 4 (by rfl) ⟨701064, by rfl⟩ : syracuseStep 7478021 = 1402129) (by norm_num)
theorem B4985347 : Blo 1969435 4985347 := bstep (se 1 (by rfl) ⟨3739010, by rfl⟩ : syracuseStep 4985347 = 7478021) B7478021
theorem B6647129 : Blo 1969435 6647129 := bstep (se 2 (by rfl) ⟨2492673, by rfl⟩ : syracuseStep 6647129 = 4985347) B4985347
theorem B4431419 : Blo 1969435 4431419 := bstep (se 1 (by rfl) ⟨3323564, by rfl⟩ : syracuseStep 4431419 = 6647129) B6647129
theorem B2954279 : Blo 1969435 2954279 := bstep (se 1 (by rfl) ⟨2215709, by rfl⟩ : syracuseStep 2954279 = 4431419) B4431419
theorem B1969519 : Blo 1969435 1969519 := bstep (se 1 (by rfl) ⟨1477139, by rfl⟩ : syracuseStep 1969519 = 2954279) B2954279
theorem B2954285 : Blo 1969435 2954285 := bbase (se 3 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 2954285 = 1107857) (by norm_num)
theorem B1969523 : Blo 1969435 1969523 := bstep (se 1 (by rfl) ⟨1477142, by rfl⟩ : syracuseStep 1969523 = 2954285) B2954285
theorem B4431437 : Blo 1969435 4431437 := bbase (se 3 (by rfl) ⟨830894, by rfl⟩ : syracuseStep 4431437 = 1661789) (by norm_num)
theorem B2954291 : Blo 1969435 2954291 := bstep (se 1 (by rfl) ⟨2215718, by rfl⟩ : syracuseStep 2954291 = 4431437) B4431437
theorem B1969527 : Blo 1969435 1969527 := bstep (se 1 (by rfl) ⟨1477145, by rfl⟩ : syracuseStep 1969527 = 2954291) B2954291
theorem B2492689 : Blo 1969435 2492689 := bbase (se 2 (by rfl) ⟨934758, by rfl⟩ : syracuseStep 2492689 = 1869517) (by norm_num)
theorem B3323585 : Blo 1969435 3323585 := bstep (se 2 (by rfl) ⟨1246344, by rfl⟩ : syracuseStep 3323585 = 2492689) B2492689
theorem B2215723 : Blo 1969435 2215723 := bstep (se 1 (by rfl) ⟨1661792, by rfl⟩ : syracuseStep 2215723 = 3323585) B3323585
theorem B2954297 : Blo 1969435 2954297 := bstep (se 2 (by rfl) ⟨1107861, by rfl⟩ : syracuseStep 2954297 = 2215723) B2215723
theorem B1969531 : Blo 1969435 1969531 := bstep (se 1 (by rfl) ⟨1477148, by rfl⟩ : syracuseStep 1969531 = 2954297) B2954297
theorem B4206421 : Blo 1969435 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B22434245 : Blo 1969435 22434245 := bstep (se 4 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 22434245 = 4206421) B4206421
theorem B14956163 : Blo 1969435 14956163 := bstep (se 1 (by rfl) ⟨11217122, by rfl⟩ : syracuseStep 14956163 = 22434245) B22434245
theorem B9970775 : Blo 1969435 9970775 := bstep (se 1 (by rfl) ⟨7478081, by rfl⟩ : syracuseStep 9970775 = 14956163) B14956163
theorem B6647183 : Blo 1969435 6647183 := bstep (se 1 (by rfl) ⟨4985387, by rfl⟩ : syracuseStep 6647183 = 9970775) B9970775
theorem B4431455 : Blo 1969435 4431455 := bstep (se 1 (by rfl) ⟨3323591, by rfl⟩ : syracuseStep 4431455 = 6647183) B6647183
theorem B2954303 : Blo 1969435 2954303 := bstep (se 1 (by rfl) ⟨2215727, by rfl⟩ : syracuseStep 2954303 = 4431455) B4431455
theorem B1969535 : Blo 1969435 1969535 := bstep (se 1 (by rfl) ⟨1477151, by rfl⟩ : syracuseStep 1969535 = 2954303) B2954303
theorem B2954309 : Blo 1969435 2954309 := bbase (se 4 (by rfl) ⟨276966, by rfl⟩ : syracuseStep 2954309 = 553933) (by norm_num)
theorem B1969539 : Blo 1969435 1969539 := bstep (se 1 (by rfl) ⟨1477154, by rfl⟩ : syracuseStep 1969539 = 2954309) B2954309
theorem B3323605 : Blo 1969435 3323605 := bbase (se 7 (by rfl) ⟨38948, by rfl⟩ : syracuseStep 3323605 = 77897) (by norm_num)
theorem B4431473 : Blo 1969435 4431473 := bstep (se 2 (by rfl) ⟨1661802, by rfl⟩ : syracuseStep 4431473 = 3323605) B3323605
theorem B2954315 : Blo 1969435 2954315 := bstep (se 1 (by rfl) ⟨2215736, by rfl⟩ : syracuseStep 2954315 = 4431473) B4431473
theorem B1969543 : Blo 1969435 1969543 := bstep (se 1 (by rfl) ⟨1477157, by rfl⟩ : syracuseStep 1969543 = 2954315) B2954315
theorem B2215741 : Blo 1969435 2215741 := bbase (se 3 (by rfl) ⟨415451, by rfl⟩ : syracuseStep 2215741 = 830903) (by norm_num)
theorem B2954321 : Blo 1969435 2954321 := bstep (se 2 (by rfl) ⟨1107870, by rfl⟩ : syracuseStep 2954321 = 2215741) B2215741
theorem B1969547 : Blo 1969435 1969547 := bstep (se 1 (by rfl) ⟨1477160, by rfl⟩ : syracuseStep 1969547 = 2954321) B2954321
theorem B6647237 : Blo 1969435 6647237 := bbase (se 4 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 6647237 = 1246357) (by norm_num)
theorem B4431491 : Blo 1969435 4431491 := bstep (se 1 (by rfl) ⟨3323618, by rfl⟩ : syracuseStep 4431491 = 6647237) B6647237
theorem B2954327 : Blo 1969435 2954327 := bstep (se 1 (by rfl) ⟨2215745, by rfl⟩ : syracuseStep 2954327 = 4431491) B4431491
theorem B1969551 : Blo 1969435 1969551 := bstep (se 1 (by rfl) ⟨1477163, by rfl⟩ : syracuseStep 1969551 = 2954327) B2954327
theorem B2954333 : Blo 1969435 2954333 := bbase (se 3 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 2954333 = 1107875) (by norm_num)
theorem B1969555 : Blo 1969435 1969555 := bstep (se 1 (by rfl) ⟨1477166, by rfl⟩ : syracuseStep 1969555 = 2954333) B2954333
theorem B4431509 : Blo 1969435 4431509 := bbase (se 6 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 4431509 = 207727) (by norm_num)
theorem B2954339 : Blo 1969435 2954339 := bstep (se 1 (by rfl) ⟨2215754, by rfl⟩ : syracuseStep 2954339 = 4431509) B4431509
theorem B1969559 : Blo 1969435 1969559 := bstep (se 1 (by rfl) ⟨1477169, by rfl⟩ : syracuseStep 1969559 = 2954339) B2954339
theorem B2103241 : Blo 1969435 2103241 := bbase (se 2 (by rfl) ⟨788715, by rfl⟩ : syracuseStep 2103241 = 1577431) (by norm_num)
theorem B2804321 : Blo 1969435 2804321 := bstep (se 2 (by rfl) ⟨1051620, by rfl⟩ : syracuseStep 2804321 = 2103241) B2103241
theorem B7478189 : Blo 1969435 7478189 := bstep (se 3 (by rfl) ⟨1402160, by rfl⟩ : syracuseStep 7478189 = 2804321) B2804321
theorem B4985459 : Blo 1969435 4985459 := bstep (se 1 (by rfl) ⟨3739094, by rfl⟩ : syracuseStep 4985459 = 7478189) B7478189
theorem B3323639 : Blo 1969435 3323639 := bstep (se 1 (by rfl) ⟨2492729, by rfl⟩ : syracuseStep 3323639 = 4985459) B4985459
theorem B2215759 : Blo 1969435 2215759 := bstep (se 1 (by rfl) ⟨1661819, by rfl⟩ : syracuseStep 2215759 = 3323639) B3323639
theorem B2954345 : Blo 1969435 2954345 := bstep (se 2 (by rfl) ⟨1107879, by rfl⟩ : syracuseStep 2954345 = 2215759) B2215759
theorem B1969563 : Blo 1969435 1969563 := bstep (se 1 (by rfl) ⟨1477172, by rfl⟩ : syracuseStep 1969563 = 2954345) B2954345
theorem B4732301 : Blo 1969435 4732301 := bbase (se 3 (by rfl) ⟨887306, by rfl⟩ : syracuseStep 4732301 = 1774613) (by norm_num)
theorem B12619469 : Blo 1969435 12619469 := bstep (se 3 (by rfl) ⟨2366150, by rfl⟩ : syracuseStep 12619469 = 4732301) B4732301
theorem B8412979 : Blo 1969435 8412979 := bstep (se 1 (by rfl) ⟨6309734, by rfl⟩ : syracuseStep 8412979 = 12619469) B12619469
theorem B11217305 : Blo 1969435 11217305 := bstep (se 2 (by rfl) ⟨4206489, by rfl⟩ : syracuseStep 11217305 = 8412979) B8412979
theorem B7478203 : Blo 1969435 7478203 := bstep (se 1 (by rfl) ⟨5608652, by rfl⟩ : syracuseStep 7478203 = 11217305) B11217305
theorem B9970937 : Blo 1969435 9970937 := bstep (se 2 (by rfl) ⟨3739101, by rfl⟩ : syracuseStep 9970937 = 7478203) B7478203
theorem B6647291 : Blo 1969435 6647291 := bstep (se 1 (by rfl) ⟨4985468, by rfl⟩ : syracuseStep 6647291 = 9970937) B9970937
theorem B4431527 : Blo 1969435 4431527 := bstep (se 1 (by rfl) ⟨3323645, by rfl⟩ : syracuseStep 4431527 = 6647291) B6647291
theorem B2954351 : Blo 1969435 2954351 := bstep (se 1 (by rfl) ⟨2215763, by rfl⟩ : syracuseStep 2954351 = 4431527) B4431527
theorem B1969567 : Blo 1969435 1969567 := bstep (se 1 (by rfl) ⟨1477175, by rfl⟩ : syracuseStep 1969567 = 2954351) B2954351
theorem B2954357 : Blo 1969435 2954357 := bbase (se 5 (by rfl) ⟨138485, by rfl⟩ : syracuseStep 2954357 = 276971) (by norm_num)
theorem B1969571 : Blo 1969435 1969571 := bstep (se 1 (by rfl) ⟨1477178, by rfl⟩ : syracuseStep 1969571 = 2954357) B2954357
theorem B3739117 : Blo 1969435 3739117 := bbase (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) (by norm_num)
theorem B4985489 : Blo 1969435 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B3323659 : Blo 1969435 3323659 := bstep (se 1 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 3323659 = 4985489) B4985489
theorem B4431545 : Blo 1969435 4431545 := bstep (se 2 (by rfl) ⟨1661829, by rfl⟩ : syracuseStep 4431545 = 3323659) B3323659
theorem B2954363 : Blo 1969435 2954363 := bstep (se 1 (by rfl) ⟨2215772, by rfl⟩ : syracuseStep 2954363 = 4431545) B4431545
theorem B1969575 : Blo 1969435 1969575 := bstep (se 1 (by rfl) ⟨1477181, by rfl⟩ : syracuseStep 1969575 = 2954363) B2954363
theorem B2215777 : Blo 1969435 2215777 := bbase (se 2 (by rfl) ⟨830916, by rfl⟩ : syracuseStep 2215777 = 1661833) (by norm_num)
theorem B2954369 : Blo 1969435 2954369 := bstep (se 2 (by rfl) ⟨1107888, by rfl⟩ : syracuseStep 2954369 = 2215777) B2215777
theorem B1969579 : Blo 1969435 1969579 := bstep (se 1 (by rfl) ⟨1477184, by rfl⟩ : syracuseStep 1969579 = 2954369) B2954369
theorem B4985509 : Blo 1969435 4985509 := bbase (se 4 (by rfl) ⟨467391, by rfl⟩ : syracuseStep 4985509 = 934783) (by norm_num)
theorem B6647345 : Blo 1969435 6647345 := bstep (se 2 (by rfl) ⟨2492754, by rfl⟩ : syracuseStep 6647345 = 4985509) B4985509
theorem B4431563 : Blo 1969435 4431563 := bstep (se 1 (by rfl) ⟨3323672, by rfl⟩ : syracuseStep 4431563 = 6647345) B6647345
theorem B2954375 : Blo 1969435 2954375 := bstep (se 1 (by rfl) ⟨2215781, by rfl⟩ : syracuseStep 2954375 = 4431563) B4431563
theorem B1969583 : Blo 1969435 1969583 := bstep (se 1 (by rfl) ⟨1477187, by rfl⟩ : syracuseStep 1969583 = 2954375) B2954375
theorem B2954381 : Blo 1969435 2954381 := bbase (se 3 (by rfl) ⟨553946, by rfl⟩ : syracuseStep 2954381 = 1107893) (by norm_num)
theorem B1969587 : Blo 1969435 1969587 := bstep (se 1 (by rfl) ⟨1477190, by rfl⟩ : syracuseStep 1969587 = 2954381) B2954381
theorem B4431581 : Blo 1969435 4431581 := bbase (se 3 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 4431581 = 1661843) (by norm_num)
theorem B2954387 : Blo 1969435 2954387 := bstep (se 1 (by rfl) ⟨2215790, by rfl⟩ : syracuseStep 2954387 = 4431581) B4431581
theorem B1969591 : Blo 1969435 1969591 := bstep (se 1 (by rfl) ⟨1477193, by rfl⟩ : syracuseStep 1969591 = 2954387) B2954387
theorem B3323693 : Blo 1969435 3323693 := bbase (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) (by norm_num)
theorem B2215795 : Blo 1969435 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B2954393 : Blo 1969435 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1969595 : Blo 1969435 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B5323925 : Blo 1969435 5323925 := bbase (se 6 (by rfl) ⟨124779, by rfl⟩ : syracuseStep 5323925 = 249559) (by norm_num)
theorem B14197133 : Blo 1969435 14197133 := bstep (se 3 (by rfl) ⟨2661962, by rfl⟩ : syracuseStep 14197133 = 5323925) B5323925
theorem B37859021 : Blo 1969435 37859021 := bstep (se 3 (by rfl) ⟨7098566, by rfl⟩ : syracuseStep 37859021 = 14197133) B14197133
theorem B25239347 : Blo 1969435 25239347 := bstep (se 1 (by rfl) ⟨18929510, by rfl⟩ : syracuseStep 25239347 = 37859021) B37859021
theorem B16826231 : Blo 1969435 16826231 := bstep (se 1 (by rfl) ⟨12619673, by rfl⟩ : syracuseStep 16826231 = 25239347) B25239347
theorem B11217487 : Blo 1969435 11217487 := bstep (se 1 (by rfl) ⟨8413115, by rfl⟩ : syracuseStep 11217487 = 16826231) B16826231
theorem B14956649 : Blo 1969435 14956649 := bstep (se 2 (by rfl) ⟨5608743, by rfl⟩ : syracuseStep 14956649 = 11217487) B11217487
theorem B9971099 : Blo 1969435 9971099 := bstep (se 1 (by rfl) ⟨7478324, by rfl⟩ : syracuseStep 9971099 = 14956649) B14956649
theorem B6647399 : Blo 1969435 6647399 := bstep (se 1 (by rfl) ⟨4985549, by rfl⟩ : syracuseStep 6647399 = 9971099) B9971099
theorem B4431599 : Blo 1969435 4431599 := bstep (se 1 (by rfl) ⟨3323699, by rfl⟩ : syracuseStep 4431599 = 6647399) B6647399
theorem B2954399 : Blo 1969435 2954399 := bstep (se 1 (by rfl) ⟨2215799, by rfl⟩ : syracuseStep 2954399 = 4431599) B4431599
theorem B1969599 : Blo 1969435 1969599 := bstep (se 1 (by rfl) ⟨1477199, by rfl⟩ : syracuseStep 1969599 = 2954399) B2954399
theorem B2954405 : Blo 1969435 2954405 := bbase (se 4 (by rfl) ⟨276975, by rfl⟩ : syracuseStep 2954405 = 553951) (by norm_num)
theorem B1969603 : Blo 1969435 1969603 := bstep (se 1 (by rfl) ⟨1477202, by rfl⟩ : syracuseStep 1969603 = 2954405) B2954405
theorem B2492785 : Blo 1969435 2492785 := bbase (se 2 (by rfl) ⟨934794, by rfl⟩ : syracuseStep 2492785 = 1869589) (by norm_num)
theorem B3323713 : Blo 1969435 3323713 := bstep (se 2 (by rfl) ⟨1246392, by rfl⟩ : syracuseStep 3323713 = 2492785) B2492785
theorem B4431617 : Blo 1969435 4431617 := bstep (se 2 (by rfl) ⟨1661856, by rfl⟩ : syracuseStep 4431617 = 3323713) B3323713
theorem B2954411 : Blo 1969435 2954411 := bstep (se 1 (by rfl) ⟨2215808, by rfl⟩ : syracuseStep 2954411 = 4431617) B4431617
theorem B1969607 : Blo 1969435 1969607 := bstep (se 1 (by rfl) ⟨1477205, by rfl⟩ : syracuseStep 1969607 = 2954411) B2954411
theorem B2215813 : Blo 1969435 2215813 := bbase (se 4 (by rfl) ⟨207732, by rfl⟩ : syracuseStep 2215813 = 415465) (by norm_num)
theorem B2954417 : Blo 1969435 2954417 := bstep (se 2 (by rfl) ⟨1107906, by rfl⟩ : syracuseStep 2954417 = 2215813) B2215813
theorem B1969611 : Blo 1969435 1969611 := bstep (se 1 (by rfl) ⟨1477208, by rfl⟩ : syracuseStep 1969611 = 2954417) B2954417
theorem B2366209 : Blo 1969435 2366209 := bbase (se 2 (by rfl) ⟨887328, by rfl⟩ : syracuseStep 2366209 = 1774657) (by norm_num)
theorem B3154945 : Blo 1969435 3154945 := bstep (se 2 (by rfl) ⟨1183104, by rfl⟩ : syracuseStep 3154945 = 2366209) B2366209
theorem B4206593 : Blo 1969435 4206593 := bstep (se 2 (by rfl) ⟨1577472, by rfl⟩ : syracuseStep 4206593 = 3154945) B3154945
theorem B2804395 : Blo 1969435 2804395 := bstep (se 1 (by rfl) ⟨2103296, by rfl⟩ : syracuseStep 2804395 = 4206593) B4206593
theorem B3739193 : Blo 1969435 3739193 := bstep (se 2 (by rfl) ⟨1402197, by rfl⟩ : syracuseStep 3739193 = 2804395) B2804395
theorem B2492795 : Blo 1969435 2492795 := bstep (se 1 (by rfl) ⟨1869596, by rfl⟩ : syracuseStep 2492795 = 3739193) B3739193
theorem B6647453 : Blo 1969435 6647453 := bstep (se 3 (by rfl) ⟨1246397, by rfl⟩ : syracuseStep 6647453 = 2492795) B2492795
theorem B4431635 : Blo 1969435 4431635 := bstep (se 1 (by rfl) ⟨3323726, by rfl⟩ : syracuseStep 4431635 = 6647453) B6647453
theorem B2954423 : Blo 1969435 2954423 := bstep (se 1 (by rfl) ⟨2215817, by rfl⟩ : syracuseStep 2954423 = 4431635) B4431635
theorem B1969615 : Blo 1969435 1969615 := bstep (se 1 (by rfl) ⟨1477211, by rfl⟩ : syracuseStep 1969615 = 2954423) B2954423
theorem B2954429 : Blo 1969435 2954429 := bbase (se 3 (by rfl) ⟨553955, by rfl⟩ : syracuseStep 2954429 = 1107911) (by norm_num)
theorem B1969619 : Blo 1969435 1969619 := bstep (se 1 (by rfl) ⟨1477214, by rfl⟩ : syracuseStep 1969619 = 2954429) B2954429
theorem B4431653 : Blo 1969435 4431653 := bbase (se 4 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 4431653 = 830935) (by norm_num)
theorem B2954435 : Blo 1969435 2954435 := bstep (se 1 (by rfl) ⟨2215826, by rfl⟩ : syracuseStep 2954435 = 4431653) B4431653
theorem B1969623 : Blo 1969435 1969623 := bstep (se 1 (by rfl) ⟨1477217, by rfl⟩ : syracuseStep 1969623 = 2954435) B2954435
theorem B4985621 : Blo 1969435 4985621 := bbase (se 6 (by rfl) ⟨116850, by rfl⟩ : syracuseStep 4985621 = 233701) (by norm_num)
theorem B3323747 : Blo 1969435 3323747 := bstep (se 1 (by rfl) ⟨2492810, by rfl⟩ : syracuseStep 3323747 = 4985621) B4985621
theorem B2215831 : Blo 1969435 2215831 := bstep (se 1 (by rfl) ⟨1661873, by rfl⟩ : syracuseStep 2215831 = 3323747) B3323747
theorem B2954441 : Blo 1969435 2954441 := bstep (se 2 (by rfl) ⟨1107915, by rfl⟩ : syracuseStep 2954441 = 2215831) B2215831
theorem B1969627 : Blo 1969435 1969627 := bstep (se 1 (by rfl) ⟨1477220, by rfl⟩ : syracuseStep 1969627 = 2954441) B2954441
theorem B8413253 : Blo 1969435 8413253 := bbase (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) (by norm_num)
theorem B5608835 : Blo 1969435 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B3739223 : Blo 1969435 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B9971261 : Blo 1969435 9971261 := bstep (se 3 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 9971261 = 3739223) B3739223
theorem B6647507 : Blo 1969435 6647507 := bstep (se 1 (by rfl) ⟨4985630, by rfl⟩ : syracuseStep 6647507 = 9971261) B9971261
theorem B4431671 : Blo 1969435 4431671 := bstep (se 1 (by rfl) ⟨3323753, by rfl⟩ : syracuseStep 4431671 = 6647507) B6647507
theorem B2954447 : Blo 1969435 2954447 := bstep (se 1 (by rfl) ⟨2215835, by rfl⟩ : syracuseStep 2954447 = 4431671) B4431671
theorem B1969631 : Blo 1969435 1969631 := bstep (se 1 (by rfl) ⟨1477223, by rfl⟩ : syracuseStep 1969631 = 2954447) B2954447
theorem B2954453 : Blo 1969435 2954453 := bbase (se 7 (by rfl) ⟨34622, by rfl⟩ : syracuseStep 2954453 = 69245) (by norm_num)
theorem B1969635 : Blo 1969435 1969635 := bstep (se 1 (by rfl) ⟨1477226, by rfl⟩ : syracuseStep 1969635 = 2954453) B2954453
theorem B2804429 : Blo 1969435 2804429 := bbase (se 3 (by rfl) ⟨525830, by rfl⟩ : syracuseStep 2804429 = 1051661) (by norm_num)
theorem B7478477 : Blo 1969435 7478477 := bstep (se 3 (by rfl) ⟨1402214, by rfl⟩ : syracuseStep 7478477 = 2804429) B2804429
theorem B4985651 : Blo 1969435 4985651 := bstep (se 1 (by rfl) ⟨3739238, by rfl⟩ : syracuseStep 4985651 = 7478477) B7478477
theorem B3323767 : Blo 1969435 3323767 := bstep (se 1 (by rfl) ⟨2492825, by rfl⟩ : syracuseStep 3323767 = 4985651) B4985651
theorem B4431689 : Blo 1969435 4431689 := bstep (se 2 (by rfl) ⟨1661883, by rfl⟩ : syracuseStep 4431689 = 3323767) B3323767
theorem B2954459 : Blo 1969435 2954459 := bstep (se 1 (by rfl) ⟨2215844, by rfl⟩ : syracuseStep 2954459 = 4431689) B4431689
theorem B1969639 : Blo 1969435 1969639 := bstep (se 1 (by rfl) ⟨1477229, by rfl⟩ : syracuseStep 1969639 = 2954459) B2954459
theorem B2215849 : Blo 1969435 2215849 := bbase (se 2 (by rfl) ⟨830943, by rfl⟩ : syracuseStep 2215849 = 1661887) (by norm_num)
theorem B2954465 : Blo 1969435 2954465 := bstep (se 2 (by rfl) ⟨1107924, by rfl⟩ : syracuseStep 2954465 = 2215849) B2215849
theorem B1969643 : Blo 1969435 1969643 := bstep (se 1 (by rfl) ⟨1477232, by rfl⟩ : syracuseStep 1969643 = 2954465) B2954465
theorem B19188245 : Blo 1969435 19188245 := bbase (se 6 (by rfl) ⟨449724, by rfl⟩ : syracuseStep 19188245 = 899449) (by norm_num)
theorem B12792163 : Blo 1969435 12792163 := bstep (se 1 (by rfl) ⟨9594122, by rfl⟩ : syracuseStep 12792163 = 19188245) B19188245
theorem B17056217 : Blo 1969435 17056217 := bstep (se 2 (by rfl) ⟨6396081, by rfl⟩ : syracuseStep 17056217 = 12792163) B12792163
theorem B45483245 : Blo 1969435 45483245 := bstep (se 3 (by rfl) ⟨8528108, by rfl⟩ : syracuseStep 45483245 = 17056217) B17056217
theorem B30322163 : Blo 1969435 30322163 := bstep (se 1 (by rfl) ⟨22741622, by rfl⟩ : syracuseStep 30322163 = 45483245) B45483245
theorem B20214775 : Blo 1969435 20214775 := bstep (se 1 (by rfl) ⟨15161081, by rfl⟩ : syracuseStep 20214775 = 30322163) B30322163
theorem B26953033 : Blo 1969435 26953033 := bstep (se 2 (by rfl) ⟨10107387, by rfl⟩ : syracuseStep 26953033 = 20214775) B20214775
theorem B35937377 : Blo 1969435 35937377 := bstep (se 2 (by rfl) ⟨13476516, by rfl⟩ : syracuseStep 35937377 = 26953033) B26953033
theorem B23958251 : Blo 1969435 23958251 := bstep (se 1 (by rfl) ⟨17968688, by rfl⟩ : syracuseStep 23958251 = 35937377) B35937377
theorem B15972167 : Blo 1969435 15972167 := bstep (se 1 (by rfl) ⟨11979125, by rfl⟩ : syracuseStep 15972167 = 23958251) B23958251
theorem B10648111 : Blo 1969435 10648111 := bstep (se 1 (by rfl) ⟨7986083, by rfl⟩ : syracuseStep 10648111 = 15972167) B15972167
theorem B14197481 : Blo 1969435 14197481 := bstep (se 2 (by rfl) ⟨5324055, by rfl⟩ : syracuseStep 14197481 = 10648111) B10648111
theorem B9464987 : Blo 1969435 9464987 := bstep (se 1 (by rfl) ⟨7098740, by rfl⟩ : syracuseStep 9464987 = 14197481) B14197481
theorem B6309991 : Blo 1969435 6309991 := bstep (se 1 (by rfl) ⟨4732493, by rfl⟩ : syracuseStep 6309991 = 9464987) B9464987
theorem B8413321 : Blo 1969435 8413321 := bstep (se 2 (by rfl) ⟨3154995, by rfl⟩ : syracuseStep 8413321 = 6309991) B6309991
theorem B11217761 : Blo 1969435 11217761 := bstep (se 2 (by rfl) ⟨4206660, by rfl⟩ : syracuseStep 11217761 = 8413321) B8413321
theorem B7478507 : Blo 1969435 7478507 := bstep (se 1 (by rfl) ⟨5608880, by rfl⟩ : syracuseStep 7478507 = 11217761) B11217761
theorem B4985671 : Blo 1969435 4985671 := bstep (se 1 (by rfl) ⟨3739253, by rfl⟩ : syracuseStep 4985671 = 7478507) B7478507
theorem B6647561 : Blo 1969435 6647561 := bstep (se 2 (by rfl) ⟨2492835, by rfl⟩ : syracuseStep 6647561 = 4985671) B4985671
theorem B4431707 : Blo 1969435 4431707 := bstep (se 1 (by rfl) ⟨3323780, by rfl⟩ : syracuseStep 4431707 = 6647561) B6647561
theorem B2954471 : Blo 1969435 2954471 := bstep (se 1 (by rfl) ⟨2215853, by rfl⟩ : syracuseStep 2954471 = 4431707) B4431707
theorem B1969647 : Blo 1969435 1969647 := bstep (se 1 (by rfl) ⟨1477235, by rfl⟩ : syracuseStep 1969647 = 2954471) B2954471
theorem B2954477 : Blo 1969435 2954477 := bbase (se 3 (by rfl) ⟨553964, by rfl⟩ : syracuseStep 2954477 = 1107929) (by norm_num)
theorem B1969651 : Blo 1969435 1969651 := bstep (se 1 (by rfl) ⟨1477238, by rfl⟩ : syracuseStep 1969651 = 2954477) B2954477
theorem B4431725 : Blo 1969435 4431725 := bbase (se 3 (by rfl) ⟨830948, by rfl⟩ : syracuseStep 4431725 = 1661897) (by norm_num)
theorem B2954483 : Blo 1969435 2954483 := bstep (se 1 (by rfl) ⟨2215862, by rfl⟩ : syracuseStep 2954483 = 4431725) B4431725
theorem B1969655 : Blo 1969435 1969655 := bstep (se 1 (by rfl) ⟨1477241, by rfl⟩ : syracuseStep 1969655 = 2954483) B2954483
theorem B3739277 : Blo 1969435 3739277 := bbase (se 3 (by rfl) ⟨701114, by rfl⟩ : syracuseStep 3739277 = 1402229) (by norm_num)
theorem B2492851 : Blo 1969435 2492851 := bstep (se 1 (by rfl) ⟨1869638, by rfl⟩ : syracuseStep 2492851 = 3739277) B3739277
theorem B3323801 : Blo 1969435 3323801 := bstep (se 2 (by rfl) ⟨1246425, by rfl⟩ : syracuseStep 3323801 = 2492851) B2492851
theorem B2215867 : Blo 1969435 2215867 := bstep (se 1 (by rfl) ⟨1661900, by rfl⟩ : syracuseStep 2215867 = 3323801) B3323801
theorem B2954489 : Blo 1969435 2954489 := bstep (se 2 (by rfl) ⟨1107933, by rfl⟩ : syracuseStep 2954489 = 2215867) B2215867
theorem B1969659 : Blo 1969435 1969659 := bstep (se 1 (by rfl) ⟨1477244, by rfl⟩ : syracuseStep 1969659 = 2954489) B2954489
theorem B1996537 : Blo 1969435 1996537 := bbase (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) (by norm_num)
theorem B2662049 : Blo 1969435 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B7098797 : Blo 1969435 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B18930125 : Blo 1969435 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B50480333 : Blo 1969435 50480333 := bstep (se 3 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 50480333 = 18930125) B18930125
theorem B33653555 : Blo 1969435 33653555 := bstep (se 1 (by rfl) ⟨25240166, by rfl⟩ : syracuseStep 33653555 = 50480333) B50480333
theorem B22435703 : Blo 1969435 22435703 := bstep (se 1 (by rfl) ⟨16826777, by rfl⟩ : syracuseStep 22435703 = 33653555) B33653555
theorem B14957135 : Blo 1969435 14957135 := bstep (se 1 (by rfl) ⟨11217851, by rfl⟩ : syracuseStep 14957135 = 22435703) B22435703
theorem B9971423 : Blo 1969435 9971423 := bstep (se 1 (by rfl) ⟨7478567, by rfl⟩ : syracuseStep 9971423 = 14957135) B14957135
theorem B6647615 : Blo 1969435 6647615 := bstep (se 1 (by rfl) ⟨4985711, by rfl⟩ : syracuseStep 6647615 = 9971423) B9971423
theorem B4431743 : Blo 1969435 4431743 := bstep (se 1 (by rfl) ⟨3323807, by rfl⟩ : syracuseStep 4431743 = 6647615) B6647615
theorem B2954495 : Blo 1969435 2954495 := bstep (se 1 (by rfl) ⟨2215871, by rfl⟩ : syracuseStep 2954495 = 4431743) B4431743
theorem B1969663 : Blo 1969435 1969663 := bstep (se 1 (by rfl) ⟨1477247, by rfl⟩ : syracuseStep 1969663 = 2954495) B2954495
theorem B2954501 : Blo 1969435 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B1969667 : Blo 1969435 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B3323821 : Blo 1969435 3323821 := bbase (se 3 (by rfl) ⟨623216, by rfl⟩ : syracuseStep 3323821 = 1246433) (by norm_num)
theorem B4431761 : Blo 1969435 4431761 := bstep (se 2 (by rfl) ⟨1661910, by rfl⟩ : syracuseStep 4431761 = 3323821) B3323821
theorem B2954507 : Blo 1969435 2954507 := bstep (se 1 (by rfl) ⟨2215880, by rfl⟩ : syracuseStep 2954507 = 4431761) B4431761
theorem B1969671 : Blo 1969435 1969671 := bstep (se 1 (by rfl) ⟨1477253, by rfl⟩ : syracuseStep 1969671 = 2954507) B2954507
theorem B2215885 : Blo 1969435 2215885 := bbase (se 3 (by rfl) ⟨415478, by rfl⟩ : syracuseStep 2215885 = 830957) (by norm_num)
theorem B2954513 : Blo 1969435 2954513 := bstep (se 2 (by rfl) ⟨1107942, by rfl⟩ : syracuseStep 2954513 = 2215885) B2215885
theorem B1969675 : Blo 1969435 1969675 := bstep (se 1 (by rfl) ⟨1477256, by rfl⟩ : syracuseStep 1969675 = 2954513) B2954513
theorem B6647669 : Blo 1969435 6647669 := bbase (se 5 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 6647669 = 623219) (by norm_num)
theorem B4431779 : Blo 1969435 4431779 := bstep (se 1 (by rfl) ⟨3323834, by rfl⟩ : syracuseStep 4431779 = 6647669) B6647669
theorem B2954519 : Blo 1969435 2954519 := bstep (se 1 (by rfl) ⟨2215889, by rfl⟩ : syracuseStep 2954519 = 4431779) B4431779
theorem B1969679 : Blo 1969435 1969679 := bstep (se 1 (by rfl) ⟨1477259, by rfl⟩ : syracuseStep 1969679 = 2954519) B2954519
theorem B2954525 : Blo 1969435 2954525 := bbase (se 3 (by rfl) ⟨553973, by rfl⟩ : syracuseStep 2954525 = 1107947) (by norm_num)
theorem B1969683 : Blo 1969435 1969683 := bstep (se 1 (by rfl) ⟨1477262, by rfl⟩ : syracuseStep 1969683 = 2954525) B2954525
theorem B4431797 : Blo 1969435 4431797 := bbase (se 5 (by rfl) ⟨207740, by rfl⟩ : syracuseStep 4431797 = 415481) (by norm_num)
theorem B2954531 : Blo 1969435 2954531 := bstep (se 1 (by rfl) ⟨2215898, by rfl⟩ : syracuseStep 2954531 = 4431797) B4431797
theorem B1969687 : Blo 1969435 1969687 := bstep (se 1 (by rfl) ⟨1477265, by rfl⟩ : syracuseStep 1969687 = 2954531) B2954531
theorem B6310133 : Blo 1969435 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B4206755 : Blo 1969435 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B11218013 : Blo 1969435 11218013 := bstep (se 3 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 11218013 = 4206755) B4206755
theorem B7478675 : Blo 1969435 7478675 := bstep (se 1 (by rfl) ⟨5609006, by rfl⟩ : syracuseStep 7478675 = 11218013) B11218013
theorem B4985783 : Blo 1969435 4985783 := bstep (se 1 (by rfl) ⟨3739337, by rfl⟩ : syracuseStep 4985783 = 7478675) B7478675
theorem B3323855 : Blo 1969435 3323855 := bstep (se 1 (by rfl) ⟨2492891, by rfl⟩ : syracuseStep 3323855 = 4985783) B4985783
theorem B2215903 : Blo 1969435 2215903 := bstep (se 1 (by rfl) ⟨1661927, by rfl⟩ : syracuseStep 2215903 = 3323855) B3323855
theorem B2954537 : Blo 1969435 2954537 := bstep (se 2 (by rfl) ⟨1107951, by rfl⟩ : syracuseStep 2954537 = 2215903) B2215903
theorem B1969691 : Blo 1969435 1969691 := bstep (se 1 (by rfl) ⟨1477268, by rfl⟩ : syracuseStep 1969691 = 2954537) B2954537
theorem B2662093 : Blo 1969435 2662093 := bbase (se 3 (by rfl) ⟨499142, by rfl⟩ : syracuseStep 2662093 = 998285) (by norm_num)
theorem B3549457 : Blo 1969435 3549457 := bstep (se 2 (by rfl) ⟨1331046, by rfl⟩ : syracuseStep 3549457 = 2662093) B2662093
theorem B4732609 : Blo 1969435 4732609 := bstep (se 2 (by rfl) ⟨1774728, by rfl⟩ : syracuseStep 4732609 = 3549457) B3549457
theorem B6310145 : Blo 1969435 6310145 := bstep (se 2 (by rfl) ⟨2366304, by rfl⟩ : syracuseStep 6310145 = 4732609) B4732609
theorem B4206763 : Blo 1969435 4206763 := bstep (se 1 (by rfl) ⟨3155072, by rfl⟩ : syracuseStep 4206763 = 6310145) B6310145
theorem B5609017 : Blo 1969435 5609017 := bstep (se 2 (by rfl) ⟨2103381, by rfl⟩ : syracuseStep 5609017 = 4206763) B4206763
theorem B7478689 : Blo 1969435 7478689 := bstep (se 2 (by rfl) ⟨2804508, by rfl⟩ : syracuseStep 7478689 = 5609017) B5609017
theorem B9971585 : Blo 1969435 9971585 := bstep (se 2 (by rfl) ⟨3739344, by rfl⟩ : syracuseStep 9971585 = 7478689) B7478689
theorem B6647723 : Blo 1969435 6647723 := bstep (se 1 (by rfl) ⟨4985792, by rfl⟩ : syracuseStep 6647723 = 9971585) B9971585
theorem B4431815 : Blo 1969435 4431815 := bstep (se 1 (by rfl) ⟨3323861, by rfl⟩ : syracuseStep 4431815 = 6647723) B6647723
theorem B2954543 : Blo 1969435 2954543 := bstep (se 1 (by rfl) ⟨2215907, by rfl⟩ : syracuseStep 2954543 = 4431815) B4431815
theorem B1969695 : Blo 1969435 1969695 := bstep (se 1 (by rfl) ⟨1477271, by rfl⟩ : syracuseStep 1969695 = 2954543) B2954543
theorem B2954549 : Blo 1969435 2954549 := bbase (se 5 (by rfl) ⟨138494, by rfl⟩ : syracuseStep 2954549 = 276989) (by norm_num)
theorem B1969699 : Blo 1969435 1969699 := bstep (se 1 (by rfl) ⟨1477274, by rfl⟩ : syracuseStep 1969699 = 2954549) B2954549
theorem B4985813 : Blo 1969435 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B3323875 : Blo 1969435 3323875 := bstep (se 1 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 3323875 = 4985813) B4985813
theorem B4431833 : Blo 1969435 4431833 := bstep (se 2 (by rfl) ⟨1661937, by rfl⟩ : syracuseStep 4431833 = 3323875) B3323875
theorem B2954555 : Blo 1969435 2954555 := bstep (se 1 (by rfl) ⟨2215916, by rfl⟩ : syracuseStep 2954555 = 4431833) B4431833
theorem B1969703 : Blo 1969435 1969703 := bstep (se 1 (by rfl) ⟨1477277, by rfl⟩ : syracuseStep 1969703 = 2954555) B2954555
theorem B2215921 : Blo 1969435 2215921 := bbase (se 2 (by rfl) ⟨830970, by rfl⟩ : syracuseStep 2215921 = 1661941) (by norm_num)
theorem B2954561 : Blo 1969435 2954561 := bstep (se 2 (by rfl) ⟨1107960, by rfl⟩ : syracuseStep 2954561 = 2215921) B2215921
theorem B1969707 : Blo 1969435 1969707 := bstep (se 1 (by rfl) ⟨1477280, by rfl⟩ : syracuseStep 1969707 = 2954561) B2954561
theorem B2190673 : Blo 1969435 2190673 := bbase (se 2 (by rfl) ⟨821502, by rfl⟩ : syracuseStep 2190673 = 1643005) (by norm_num)
theorem B2920897 : Blo 1969435 2920897 := bstep (se 2 (by rfl) ⟨1095336, by rfl⟩ : syracuseStep 2920897 = 2190673) B2190673
theorem B3894529 : Blo 1969435 3894529 := bstep (se 2 (by rfl) ⟨1460448, by rfl⟩ : syracuseStep 3894529 = 2920897) B2920897
theorem B5192705 : Blo 1969435 5192705 := bstep (se 2 (by rfl) ⟨1947264, by rfl⟩ : syracuseStep 5192705 = 3894529) B3894529
theorem B13847213 : Blo 1969435 13847213 := bstep (se 3 (by rfl) ⟨2596352, by rfl⟩ : syracuseStep 13847213 = 5192705) B5192705
theorem B36925901 : Blo 1969435 36925901 := bstep (se 3 (by rfl) ⟨6923606, by rfl⟩ : syracuseStep 36925901 = 13847213) B13847213
theorem B24617267 : Blo 1969435 24617267 := bstep (se 1 (by rfl) ⟨18462950, by rfl⟩ : syracuseStep 24617267 = 36925901) B36925901
theorem B16411511 : Blo 1969435 16411511 := bstep (se 1 (by rfl) ⟨12308633, by rfl⟩ : syracuseStep 16411511 = 24617267) B24617267
theorem B10941007 : Blo 1969435 10941007 := bstep (se 1 (by rfl) ⟨8205755, by rfl⟩ : syracuseStep 10941007 = 16411511) B16411511
theorem B14588009 : Blo 1969435 14588009 := bstep (se 2 (by rfl) ⟨5470503, by rfl⟩ : syracuseStep 14588009 = 10941007) B10941007
theorem B9725339 : Blo 1969435 9725339 := bstep (se 1 (by rfl) ⟨7294004, by rfl⟩ : syracuseStep 9725339 = 14588009) B14588009
theorem B6483559 : Blo 1969435 6483559 := bstep (se 1 (by rfl) ⟨4862669, by rfl⟩ : syracuseStep 6483559 = 9725339) B9725339
theorem B8644745 : Blo 1969435 8644745 := bstep (se 2 (by rfl) ⟨3241779, by rfl⟩ : syracuseStep 8644745 = 6483559) B6483559
theorem B5763163 : Blo 1969435 5763163 := bstep (se 1 (by rfl) ⟨4322372, by rfl⟩ : syracuseStep 5763163 = 8644745) B8644745
theorem B7684217 : Blo 1969435 7684217 := bstep (se 2 (by rfl) ⟨2881581, by rfl⟩ : syracuseStep 7684217 = 5763163) B5763163
theorem B5122811 : Blo 1969435 5122811 := bstep (se 1 (by rfl) ⟨3842108, by rfl⟩ : syracuseStep 5122811 = 7684217) B7684217
theorem B3415207 : Blo 1969435 3415207 := bstep (se 1 (by rfl) ⟨2561405, by rfl⟩ : syracuseStep 3415207 = 5122811) B5122811
theorem B4553609 : Blo 1969435 4553609 := bstep (se 2 (by rfl) ⟨1707603, by rfl⟩ : syracuseStep 4553609 = 3415207) B3415207
theorem B12142957 : Blo 1969435 12142957 := bstep (se 3 (by rfl) ⟨2276804, by rfl⟩ : syracuseStep 12142957 = 4553609) B4553609
theorem B16190609 : Blo 1969435 16190609 := bstep (se 2 (by rfl) ⟨6071478, by rfl⟩ : syracuseStep 16190609 = 12142957) B12142957
theorem B43174957 : Blo 1969435 43174957 := bstep (se 3 (by rfl) ⟨8095304, by rfl⟩ : syracuseStep 43174957 = 16190609) B16190609
theorem B57566609 : Blo 1969435 57566609 := bstep (se 2 (by rfl) ⟨21587478, by rfl⟩ : syracuseStep 57566609 = 43174957) B43174957
theorem B38377739 : Blo 1969435 38377739 := bstep (se 1 (by rfl) ⟨28783304, by rfl⟩ : syracuseStep 38377739 = 57566609) B57566609
theorem B25585159 : Blo 1969435 25585159 := bstep (se 1 (by rfl) ⟨19188869, by rfl⟩ : syracuseStep 25585159 = 38377739) B38377739
theorem B34113545 : Blo 1969435 34113545 := bstep (se 2 (by rfl) ⟨12792579, by rfl⟩ : syracuseStep 34113545 = 25585159) B25585159
theorem B22742363 : Blo 1969435 22742363 := bstep (se 1 (by rfl) ⟨17056772, by rfl⟩ : syracuseStep 22742363 = 34113545) B34113545
theorem B15161575 : Blo 1969435 15161575 := bstep (se 1 (by rfl) ⟨11371181, by rfl⟩ : syracuseStep 15161575 = 22742363) B22742363
theorem B20215433 : Blo 1969435 20215433 := bstep (se 2 (by rfl) ⟨7580787, by rfl⟩ : syracuseStep 20215433 = 15161575) B15161575
theorem B13476955 : Blo 1969435 13476955 := bstep (se 1 (by rfl) ⟨10107716, by rfl⟩ : syracuseStep 13476955 = 20215433) B20215433
theorem B17969273 : Blo 1969435 17969273 := bstep (se 2 (by rfl) ⟨6738477, by rfl⟩ : syracuseStep 17969273 = 13476955) B13476955
theorem B11979515 : Blo 1969435 11979515 := bstep (se 1 (by rfl) ⟨8984636, by rfl⟩ : syracuseStep 11979515 = 17969273) B17969273
theorem B31945373 : Blo 1969435 31945373 := bstep (se 3 (by rfl) ⟨5989757, by rfl⟩ : syracuseStep 31945373 = 11979515) B11979515
theorem B21296915 : Blo 1969435 21296915 := bstep (se 1 (by rfl) ⟨15972686, by rfl⟩ : syracuseStep 21296915 = 31945373) B31945373
theorem B14197943 : Blo 1969435 14197943 := bstep (se 1 (by rfl) ⟨10648457, by rfl⟩ : syracuseStep 14197943 = 21296915) B21296915
theorem B9465295 : Blo 1969435 9465295 := bstep (se 1 (by rfl) ⟨7098971, by rfl⟩ : syracuseStep 9465295 = 14197943) B14197943
theorem B12620393 : Blo 1969435 12620393 := bstep (se 2 (by rfl) ⟨4732647, by rfl⟩ : syracuseStep 12620393 = 9465295) B9465295
theorem B8413595 : Blo 1969435 8413595 := bstep (se 1 (by rfl) ⟨6310196, by rfl⟩ : syracuseStep 8413595 = 12620393) B12620393
theorem B5609063 : Blo 1969435 5609063 := bstep (se 1 (by rfl) ⟨4206797, by rfl⟩ : syracuseStep 5609063 = 8413595) B8413595
theorem B3739375 : Blo 1969435 3739375 := bstep (se 1 (by rfl) ⟨2804531, by rfl⟩ : syracuseStep 3739375 = 5609063) B5609063
theorem B4985833 : Blo 1969435 4985833 := bstep (se 2 (by rfl) ⟨1869687, by rfl⟩ : syracuseStep 4985833 = 3739375) B3739375
theorem B6647777 : Blo 1969435 6647777 := bstep (se 2 (by rfl) ⟨2492916, by rfl⟩ : syracuseStep 6647777 = 4985833) B4985833
theorem B4431851 : Blo 1969435 4431851 := bstep (se 1 (by rfl) ⟨3323888, by rfl⟩ : syracuseStep 4431851 = 6647777) B6647777
theorem B2954567 : Blo 1969435 2954567 := bstep (se 1 (by rfl) ⟨2215925, by rfl⟩ : syracuseStep 2954567 = 4431851) B4431851
theorem B1969711 : Blo 1969435 1969711 := bstep (se 1 (by rfl) ⟨1477283, by rfl⟩ : syracuseStep 1969711 = 2954567) B2954567
theorem B2954573 : Blo 1969435 2954573 := bbase (se 3 (by rfl) ⟨553982, by rfl⟩ : syracuseStep 2954573 = 1107965) (by norm_num)
theorem B1969715 : Blo 1969435 1969715 := bstep (se 1 (by rfl) ⟨1477286, by rfl⟩ : syracuseStep 1969715 = 2954573) B2954573
theorem B4431869 : Blo 1969435 4431869 := bbase (se 3 (by rfl) ⟨830975, by rfl⟩ : syracuseStep 4431869 = 1661951) (by norm_num)
theorem B2954579 : Blo 1969435 2954579 := bstep (se 1 (by rfl) ⟨2215934, by rfl⟩ : syracuseStep 2954579 = 4431869) B4431869
theorem B1969719 : Blo 1969435 1969719 := bstep (se 1 (by rfl) ⟨1477289, by rfl⟩ : syracuseStep 1969719 = 2954579) B2954579
theorem B3323909 : Blo 1969435 3323909 := bbase (se 4 (by rfl) ⟨311616, by rfl⟩ : syracuseStep 3323909 = 623233) (by norm_num)
theorem B2215939 : Blo 1969435 2215939 := bstep (se 1 (by rfl) ⟨1661954, by rfl⟩ : syracuseStep 2215939 = 3323909) B3323909
theorem B2954585 : Blo 1969435 2954585 := bstep (se 2 (by rfl) ⟨1107969, by rfl⟩ : syracuseStep 2954585 = 2215939) B2215939
theorem B1969723 : Blo 1969435 1969723 := bstep (se 1 (by rfl) ⟨1477292, by rfl⟩ : syracuseStep 1969723 = 2954585) B2954585
theorem B14957621 : Blo 1969435 14957621 := bbase (se 5 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 14957621 = 1402277) (by norm_num)
theorem B9971747 : Blo 1969435 9971747 := bstep (se 1 (by rfl) ⟨7478810, by rfl⟩ : syracuseStep 9971747 = 14957621) B14957621
theorem B6647831 : Blo 1969435 6647831 := bstep (se 1 (by rfl) ⟨4985873, by rfl⟩ : syracuseStep 6647831 = 9971747) B9971747
theorem B4431887 : Blo 1969435 4431887 := bstep (se 1 (by rfl) ⟨3323915, by rfl⟩ : syracuseStep 4431887 = 6647831) B6647831
theorem B2954591 : Blo 1969435 2954591 := bstep (se 1 (by rfl) ⟨2215943, by rfl⟩ : syracuseStep 2954591 = 4431887) B4431887
theorem B1969727 : Blo 1969435 1969727 := bstep (se 1 (by rfl) ⟨1477295, by rfl⟩ : syracuseStep 1969727 = 2954591) B2954591
theorem B2954597 : Blo 1969435 2954597 := bbase (se 4 (by rfl) ⟨276993, by rfl⟩ : syracuseStep 2954597 = 553987) (by norm_num)
theorem B1969731 : Blo 1969435 1969731 := bstep (se 1 (by rfl) ⟨1477298, by rfl⟩ : syracuseStep 1969731 = 2954597) B2954597
theorem B3739421 : Blo 1969435 3739421 := bbase (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) (by norm_num)
theorem B2492947 : Blo 1969435 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B3323929 : Blo 1969435 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B4431905 : Blo 1969435 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B2954603 : Blo 1969435 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B1969735 : Blo 1969435 1969735 := bstep (se 1 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 1969735 = 2954603) B2954603
theorem B2215957 : Blo 1969435 2215957 := bbase (se 6 (by rfl) ⟨51936, by rfl⟩ : syracuseStep 2215957 = 103873) (by norm_num)
theorem B2954609 : Blo 1969435 2954609 := bstep (se 2 (by rfl) ⟨1107978, by rfl⟩ : syracuseStep 2954609 = 2215957) B2215957
theorem B1969739 : Blo 1969435 1969739 := bstep (se 1 (by rfl) ⟨1477304, by rfl⟩ : syracuseStep 1969739 = 2954609) B2954609
theorem B2492957 : Blo 1969435 2492957 := bbase (se 3 (by rfl) ⟨467429, by rfl⟩ : syracuseStep 2492957 = 934859) (by norm_num)
theorem B6647885 : Blo 1969435 6647885 := bstep (se 3 (by rfl) ⟨1246478, by rfl⟩ : syracuseStep 6647885 = 2492957) B2492957
theorem B4431923 : Blo 1969435 4431923 := bstep (se 1 (by rfl) ⟨3323942, by rfl⟩ : syracuseStep 4431923 = 6647885) B6647885
theorem B2954615 : Blo 1969435 2954615 := bstep (se 1 (by rfl) ⟨2215961, by rfl⟩ : syracuseStep 2954615 = 4431923) B4431923
theorem B1969743 : Blo 1969435 1969743 := bstep (se 1 (by rfl) ⟨1477307, by rfl⟩ : syracuseStep 1969743 = 2954615) B2954615
theorem B2954621 : Blo 1969435 2954621 := bbase (se 3 (by rfl) ⟨553991, by rfl⟩ : syracuseStep 2954621 = 1107983) (by norm_num)
theorem B1969747 : Blo 1969435 1969747 := bstep (se 1 (by rfl) ⟨1477310, by rfl⟩ : syracuseStep 1969747 = 2954621) B2954621
theorem B4431941 : Blo 1969435 4431941 := bbase (se 4 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 4431941 = 830989) (by norm_num)
theorem B2954627 : Blo 1969435 2954627 := bstep (se 1 (by rfl) ⟨2215970, by rfl⟩ : syracuseStep 2954627 = 4431941) B4431941
theorem B1969751 : Blo 1969435 1969751 := bstep (se 1 (by rfl) ⟨1477313, by rfl⟩ : syracuseStep 1969751 = 2954627) B2954627
theorem B5609189 : Blo 1969435 5609189 := bbase (se 4 (by rfl) ⟨525861, by rfl⟩ : syracuseStep 5609189 = 1051723) (by norm_num)
theorem B3739459 : Blo 1969435 3739459 := bstep (se 1 (by rfl) ⟨2804594, by rfl⟩ : syracuseStep 3739459 = 5609189) B5609189
theorem B4985945 : Blo 1969435 4985945 := bstep (se 2 (by rfl) ⟨1869729, by rfl⟩ : syracuseStep 4985945 = 3739459) B3739459
theorem B3323963 : Blo 1969435 3323963 := bstep (se 1 (by rfl) ⟨2492972, by rfl⟩ : syracuseStep 3323963 = 4985945) B4985945
theorem B2215975 : Blo 1969435 2215975 := bstep (se 1 (by rfl) ⟨1661981, by rfl⟩ : syracuseStep 2215975 = 3323963) B3323963
theorem B2954633 : Blo 1969435 2954633 := bstep (se 2 (by rfl) ⟨1107987, by rfl⟩ : syracuseStep 2954633 = 2215975) B2215975
theorem B1969755 : Blo 1969435 1969755 := bstep (se 1 (by rfl) ⟨1477316, by rfl⟩ : syracuseStep 1969755 = 2954633) B2954633
theorem B9971909 : Blo 1969435 9971909 := bbase (se 4 (by rfl) ⟨934866, by rfl⟩ : syracuseStep 9971909 = 1869733) (by norm_num)
theorem B6647939 : Blo 1969435 6647939 := bstep (se 1 (by rfl) ⟨4985954, by rfl⟩ : syracuseStep 6647939 = 9971909) B9971909
theorem B4431959 : Blo 1969435 4431959 := bstep (se 1 (by rfl) ⟨3323969, by rfl⟩ : syracuseStep 4431959 = 6647939) B6647939
theorem B2954639 : Blo 1969435 2954639 := bstep (se 1 (by rfl) ⟨2215979, by rfl⟩ : syracuseStep 2954639 = 4431959) B4431959
theorem B1969759 : Blo 1969435 1969759 := bstep (se 1 (by rfl) ⟨1477319, by rfl⟩ : syracuseStep 1969759 = 2954639) B2954639
theorem B2954645 : Blo 1969435 2954645 := bbase (se 6 (by rfl) ⟨69249, by rfl⟩ : syracuseStep 2954645 = 138499) (by norm_num)
theorem B1969763 : Blo 1969435 1969763 := bstep (se 1 (by rfl) ⟨1477322, by rfl⟩ : syracuseStep 1969763 = 2954645) B2954645
theorem B4206917 : Blo 1969435 4206917 := bbase (se 4 (by rfl) ⟨394398, by rfl⟩ : syracuseStep 4206917 = 788797) (by norm_num)
theorem B11218445 : Blo 1969435 11218445 := bstep (se 3 (by rfl) ⟨2103458, by rfl⟩ : syracuseStep 11218445 = 4206917) B4206917
theorem B7478963 : Blo 1969435 7478963 := bstep (se 1 (by rfl) ⟨5609222, by rfl⟩ : syracuseStep 7478963 = 11218445) B11218445
theorem B4985975 : Blo 1969435 4985975 := bstep (se 1 (by rfl) ⟨3739481, by rfl⟩ : syracuseStep 4985975 = 7478963) B7478963
theorem B3323983 : Blo 1969435 3323983 := bstep (se 1 (by rfl) ⟨2492987, by rfl⟩ : syracuseStep 3323983 = 4985975) B4985975
theorem B4431977 : Blo 1969435 4431977 := bstep (se 2 (by rfl) ⟨1661991, by rfl⟩ : syracuseStep 4431977 = 3323983) B3323983
theorem B2954651 : Blo 1969435 2954651 := bstep (se 1 (by rfl) ⟨2215988, by rfl⟩ : syracuseStep 2954651 = 4431977) B4431977
theorem B1969767 : Blo 1969435 1969767 := bstep (se 1 (by rfl) ⟨1477325, by rfl⟩ : syracuseStep 1969767 = 2954651) B2954651
theorem B2215993 : Blo 1969435 2215993 := bbase (se 2 (by rfl) ⟨830997, by rfl⟩ : syracuseStep 2215993 = 1661995) (by norm_num)
theorem B2954657 : Blo 1969435 2954657 := bstep (se 2 (by rfl) ⟨1107996, by rfl⟩ : syracuseStep 2954657 = 2215993) B2215993
theorem B1969771 : Blo 1969435 1969771 := bstep (se 1 (by rfl) ⟨1477328, by rfl⟩ : syracuseStep 1969771 = 2954657) B2954657
theorem B2366401 : Blo 1969435 2366401 := bbase (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) (by norm_num)
theorem B3155201 : Blo 1969435 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B2103467 : Blo 1969435 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B5609245 : Blo 1969435 5609245 := bstep (se 3 (by rfl) ⟨1051733, by rfl⟩ : syracuseStep 5609245 = 2103467) B2103467
theorem B7478993 : Blo 1969435 7478993 := bstep (se 2 (by rfl) ⟨2804622, by rfl⟩ : syracuseStep 7478993 = 5609245) B5609245
theorem B4985995 : Blo 1969435 4985995 := bstep (se 1 (by rfl) ⟨3739496, by rfl⟩ : syracuseStep 4985995 = 7478993) B7478993
theorem B6647993 : Blo 1969435 6647993 := bstep (se 2 (by rfl) ⟨2492997, by rfl⟩ : syracuseStep 6647993 = 4985995) B4985995
theorem B4431995 : Blo 1969435 4431995 := bstep (se 1 (by rfl) ⟨3323996, by rfl⟩ : syracuseStep 4431995 = 6647993) B6647993
theorem B2954663 : Blo 1969435 2954663 := bstep (se 1 (by rfl) ⟨2215997, by rfl⟩ : syracuseStep 2954663 = 4431995) B4431995
theorem B1969775 : Blo 1969435 1969775 := bstep (se 1 (by rfl) ⟨1477331, by rfl⟩ : syracuseStep 1969775 = 2954663) B2954663
theorem B2954669 : Blo 1969435 2954669 := bbase (se 3 (by rfl) ⟨554000, by rfl⟩ : syracuseStep 2954669 = 1108001) (by norm_num)
theorem B1969779 : Blo 1969435 1969779 := bstep (se 1 (by rfl) ⟨1477334, by rfl⟩ : syracuseStep 1969779 = 2954669) B2954669
theorem B4432013 : Blo 1969435 4432013 := bbase (se 3 (by rfl) ⟨831002, by rfl⟩ : syracuseStep 4432013 = 1662005) (by norm_num)
theorem B2954675 : Blo 1969435 2954675 := bstep (se 1 (by rfl) ⟨2216006, by rfl⟩ : syracuseStep 2954675 = 4432013) B4432013
theorem B1969783 : Blo 1969435 1969783 := bstep (se 1 (by rfl) ⟨1477337, by rfl⟩ : syracuseStep 1969783 = 2954675) B2954675
theorem B2493013 : Blo 1969435 2493013 := bbase (se 8 (by rfl) ⟨14607, by rfl⟩ : syracuseStep 2493013 = 29215) (by norm_num)
theorem B3324017 : Blo 1969435 3324017 := bstep (se 2 (by rfl) ⟨1246506, by rfl⟩ : syracuseStep 3324017 = 2493013) B2493013
theorem B2216011 : Blo 1969435 2216011 := bstep (se 1 (by rfl) ⟨1662008, by rfl⟩ : syracuseStep 2216011 = 3324017) B3324017
theorem B2954681 : Blo 1969435 2954681 := bstep (se 2 (by rfl) ⟨1108005, by rfl⟩ : syracuseStep 2954681 = 2216011) B2216011
theorem B1969787 : Blo 1969435 1969787 := bstep (se 1 (by rfl) ⟨1477340, by rfl⟩ : syracuseStep 1969787 = 2954681) B2954681
theorem B2307961 : Blo 1969435 2307961 := bbase (se 2 (by rfl) ⟨865485, by rfl⟩ : syracuseStep 2307961 = 1730971) (by norm_num)
theorem B3077281 : Blo 1969435 3077281 := bstep (se 2 (by rfl) ⟨1153980, by rfl⟩ : syracuseStep 3077281 = 2307961) B2307961
theorem B4103041 : Blo 1969435 4103041 := bstep (se 2 (by rfl) ⟨1538640, by rfl⟩ : syracuseStep 4103041 = 3077281) B3077281
theorem B5470721 : Blo 1969435 5470721 := bstep (se 2 (by rfl) ⟨2051520, by rfl⟩ : syracuseStep 5470721 = 4103041) B4103041
theorem B58354357 : Blo 1969435 58354357 := bstep (se 5 (by rfl) ⟨2735360, by rfl⟩ : syracuseStep 58354357 = 5470721) B5470721
theorem B77805809 : Blo 1969435 77805809 := bstep (se 2 (by rfl) ⟨29177178, by rfl⟩ : syracuseStep 77805809 = 58354357) B58354357
theorem B51870539 : Blo 1969435 51870539 := bstep (se 1 (by rfl) ⟨38902904, by rfl⟩ : syracuseStep 51870539 = 77805809) B77805809
theorem B138321437 : Blo 1969435 138321437 := bstep (se 3 (by rfl) ⟨25935269, by rfl⟩ : syracuseStep 138321437 = 51870539) B51870539
theorem B368857165 : Blo 1969435 368857165 := bstep (se 3 (by rfl) ⟨69160718, by rfl⟩ : syracuseStep 368857165 = 138321437) B138321437
theorem B491809553 : Blo 1969435 491809553 := bstep (se 2 (by rfl) ⟨184428582, by rfl⟩ : syracuseStep 491809553 = 368857165) B368857165
theorem B327873035 : Blo 1969435 327873035 := bstep (se 1 (by rfl) ⟨245904776, by rfl⟩ : syracuseStep 327873035 = 491809553) B491809553
theorem B218582023 : Blo 1969435 218582023 := bstep (se 1 (by rfl) ⟨163936517, by rfl⟩ : syracuseStep 218582023 = 327873035) B327873035
theorem B291442697 : Blo 1969435 291442697 := bstep (se 2 (by rfl) ⟨109291011, by rfl⟩ : syracuseStep 291442697 = 218582023) B218582023
theorem B194295131 : Blo 1969435 194295131 := bstep (se 1 (by rfl) ⟨145721348, by rfl⟩ : syracuseStep 194295131 = 291442697) B291442697
theorem B129530087 : Blo 1969435 129530087 := bstep (se 1 (by rfl) ⟨97147565, by rfl⟩ : syracuseStep 129530087 = 194295131) B194295131
theorem B86353391 : Blo 1969435 86353391 := bstep (se 1 (by rfl) ⟨64765043, by rfl⟩ : syracuseStep 86353391 = 129530087) B129530087
theorem B230275709 : Blo 1969435 230275709 := bstep (se 3 (by rfl) ⟨43176695, by rfl⟩ : syracuseStep 230275709 = 86353391) B86353391
theorem B153517139 : Blo 1969435 153517139 := bstep (se 1 (by rfl) ⟨115137854, by rfl⟩ : syracuseStep 153517139 = 230275709) B230275709
theorem B102344759 : Blo 1969435 102344759 := bstep (se 1 (by rfl) ⟨76758569, by rfl⟩ : syracuseStep 102344759 = 153517139) B153517139
theorem B68229839 : Blo 1969435 68229839 := bstep (se 1 (by rfl) ⟨51172379, by rfl⟩ : syracuseStep 68229839 = 102344759) B102344759
theorem B45486559 : Blo 1969435 45486559 := bstep (se 1 (by rfl) ⟨34114919, by rfl⟩ : syracuseStep 45486559 = 68229839) B68229839
theorem B60648745 : Blo 1969435 60648745 := bstep (se 2 (by rfl) ⟨22743279, by rfl⟩ : syracuseStep 60648745 = 45486559) B45486559
theorem B80864993 : Blo 1969435 80864993 := bstep (se 2 (by rfl) ⟨30324372, by rfl⟩ : syracuseStep 80864993 = 60648745) B60648745
theorem B53909995 : Blo 1969435 53909995 := bstep (se 1 (by rfl) ⟨40432496, by rfl⟩ : syracuseStep 53909995 = 80864993) B80864993
theorem B71879993 : Blo 1969435 71879993 := bstep (se 2 (by rfl) ⟨26954997, by rfl⟩ : syracuseStep 71879993 = 53909995) B53909995
theorem B47919995 : Blo 1969435 47919995 := bstep (se 1 (by rfl) ⟨35939996, by rfl⟩ : syracuseStep 47919995 = 71879993) B71879993
theorem B31946663 : Blo 1969435 31946663 := bstep (se 1 (by rfl) ⟨23959997, by rfl⟩ : syracuseStep 31946663 = 47919995) B47919995
theorem B85191101 : Blo 1969435 85191101 := bstep (se 3 (by rfl) ⟨15973331, by rfl⟩ : syracuseStep 85191101 = 31946663) B31946663
theorem B56794067 : Blo 1969435 56794067 := bstep (se 1 (by rfl) ⟨42595550, by rfl⟩ : syracuseStep 56794067 = 85191101) B85191101
theorem B37862711 : Blo 1969435 37862711 := bstep (se 1 (by rfl) ⟨28397033, by rfl⟩ : syracuseStep 37862711 = 56794067) B56794067
theorem B25241807 : Blo 1969435 25241807 := bstep (se 1 (by rfl) ⟨18931355, by rfl⟩ : syracuseStep 25241807 = 37862711) B37862711
theorem B16827871 : Blo 1969435 16827871 := bstep (se 1 (by rfl) ⟨12620903, by rfl⟩ : syracuseStep 16827871 = 25241807) B25241807
theorem B22437161 : Blo 1969435 22437161 := bstep (se 2 (by rfl) ⟨8413935, by rfl⟩ : syracuseStep 22437161 = 16827871) B16827871
theorem B14958107 : Blo 1969435 14958107 := bstep (se 1 (by rfl) ⟨11218580, by rfl⟩ : syracuseStep 14958107 = 22437161) B22437161
theorem B9972071 : Blo 1969435 9972071 := bstep (se 1 (by rfl) ⟨7479053, by rfl⟩ : syracuseStep 9972071 = 14958107) B14958107
theorem B6648047 : Blo 1969435 6648047 := bstep (se 1 (by rfl) ⟨4986035, by rfl⟩ : syracuseStep 6648047 = 9972071) B9972071
theorem B4432031 : Blo 1969435 4432031 := bstep (se 1 (by rfl) ⟨3324023, by rfl⟩ : syracuseStep 4432031 = 6648047) B6648047
theorem B2954687 : Blo 1969435 2954687 := bstep (se 1 (by rfl) ⟨2216015, by rfl⟩ : syracuseStep 2954687 = 4432031) B4432031
theorem B1969791 : Blo 1969435 1969791 := bstep (se 1 (by rfl) ⟨1477343, by rfl⟩ : syracuseStep 1969791 = 2954687) B2954687
theorem B2954693 : Blo 1969435 2954693 := bbase (se 4 (by rfl) ⟨277002, by rfl⟩ : syracuseStep 2954693 = 554005) (by norm_num)
theorem B1969795 : Blo 1969435 1969795 := bstep (se 1 (by rfl) ⟨1477346, by rfl⟩ : syracuseStep 1969795 = 2954693) B2954693
theorem B3324037 : Blo 1969435 3324037 := bbase (se 4 (by rfl) ⟨311628, by rfl⟩ : syracuseStep 3324037 = 623257) (by norm_num)
theorem B4432049 : Blo 1969435 4432049 := bstep (se 2 (by rfl) ⟨1662018, by rfl⟩ : syracuseStep 4432049 = 3324037) B3324037
theorem B2954699 : Blo 1969435 2954699 := bstep (se 1 (by rfl) ⟨2216024, by rfl⟩ : syracuseStep 2954699 = 4432049) B4432049
theorem B1969799 : Blo 1969435 1969799 := bstep (se 1 (by rfl) ⟨1477349, by rfl⟩ : syracuseStep 1969799 = 2954699) B2954699
theorem B2216029 : Blo 1969435 2216029 := bbase (se 3 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 2216029 = 831011) (by norm_num)
theorem B2954705 : Blo 1969435 2954705 := bstep (se 2 (by rfl) ⟨1108014, by rfl⟩ : syracuseStep 2954705 = 2216029) B2216029
theorem B1969803 : Blo 1969435 1969803 := bstep (se 1 (by rfl) ⟨1477352, by rfl⟩ : syracuseStep 1969803 = 2954705) B2954705
theorem B6648101 : Blo 1969435 6648101 := bbase (se 4 (by rfl) ⟨623259, by rfl⟩ : syracuseStep 6648101 = 1246519) (by norm_num)
theorem B4432067 : Blo 1969435 4432067 := bstep (se 1 (by rfl) ⟨3324050, by rfl⟩ : syracuseStep 4432067 = 6648101) B6648101
theorem B2954711 : Blo 1969435 2954711 := bstep (se 1 (by rfl) ⟨2216033, by rfl⟩ : syracuseStep 2954711 = 4432067) B4432067
theorem B1969807 : Blo 1969435 1969807 := bstep (se 1 (by rfl) ⟨1477355, by rfl⟩ : syracuseStep 1969807 = 2954711) B2954711
theorem B2954717 : Blo 1969435 2954717 := bbase (se 3 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 2954717 = 1108019) (by norm_num)
theorem B1969811 : Blo 1969435 1969811 := bstep (se 1 (by rfl) ⟨1477358, by rfl⟩ : syracuseStep 1969811 = 2954717) B2954717
theorem B4432085 : Blo 1969435 4432085 := bbase (se 7 (by rfl) ⟨51938, by rfl⟩ : syracuseStep 4432085 = 103877) (by norm_num)
theorem B2954723 : Blo 1969435 2954723 := bstep (se 1 (by rfl) ⟨2216042, by rfl⟩ : syracuseStep 2954723 = 4432085) B4432085
theorem B1969815 : Blo 1969435 1969815 := bstep (se 1 (by rfl) ⟨1477361, by rfl⟩ : syracuseStep 1969815 = 2954723) B2954723
theorem B7581205 : Blo 1969435 7581205 := bbase (se 6 (by rfl) ⟨177684, by rfl⟩ : syracuseStep 7581205 = 355369) (by norm_num)
theorem B10108273 : Blo 1969435 10108273 := bstep (se 2 (by rfl) ⟨3790602, by rfl⟩ : syracuseStep 10108273 = 7581205) B7581205
theorem B13477697 : Blo 1969435 13477697 := bstep (se 2 (by rfl) ⟨5054136, by rfl⟩ : syracuseStep 13477697 = 10108273) B10108273
theorem B8985131 : Blo 1969435 8985131 := bstep (se 1 (by rfl) ⟨6738848, by rfl⟩ : syracuseStep 8985131 = 13477697) B13477697
theorem B5990087 : Blo 1969435 5990087 := bstep (se 1 (by rfl) ⟨4492565, by rfl⟩ : syracuseStep 5990087 = 8985131) B8985131
theorem B3993391 : Blo 1969435 3993391 := bstep (se 1 (by rfl) ⟨2995043, by rfl⟩ : syracuseStep 3993391 = 5990087) B5990087
theorem B21298085 : Blo 1969435 21298085 := bstep (se 4 (by rfl) ⟨1996695, by rfl⟩ : syracuseStep 21298085 = 3993391) B3993391
theorem B14198723 : Blo 1969435 14198723 := bstep (se 1 (by rfl) ⟨10649042, by rfl⟩ : syracuseStep 14198723 = 21298085) B21298085
theorem B9465815 : Blo 1969435 9465815 := bstep (se 1 (by rfl) ⟨7099361, by rfl⟩ : syracuseStep 9465815 = 14198723) B14198723
theorem B6310543 : Blo 1969435 6310543 := bstep (se 1 (by rfl) ⟨4732907, by rfl⟩ : syracuseStep 6310543 = 9465815) B9465815
theorem B8414057 : Blo 1969435 8414057 := bstep (se 2 (by rfl) ⟨3155271, by rfl⟩ : syracuseStep 8414057 = 6310543) B6310543
theorem B5609371 : Blo 1969435 5609371 := bstep (se 1 (by rfl) ⟨4207028, by rfl⟩ : syracuseStep 5609371 = 8414057) B8414057
theorem B7479161 : Blo 1969435 7479161 := bstep (se 2 (by rfl) ⟨2804685, by rfl⟩ : syracuseStep 7479161 = 5609371) B5609371
theorem B4986107 : Blo 1969435 4986107 := bstep (se 1 (by rfl) ⟨3739580, by rfl⟩ : syracuseStep 4986107 = 7479161) B7479161
theorem B3324071 : Blo 1969435 3324071 := bstep (se 1 (by rfl) ⟨2493053, by rfl⟩ : syracuseStep 3324071 = 4986107) B4986107
theorem B2216047 : Blo 1969435 2216047 := bstep (se 1 (by rfl) ⟨1662035, by rfl⟩ : syracuseStep 2216047 = 3324071) B3324071
theorem B2954729 : Blo 1969435 2954729 := bstep (se 2 (by rfl) ⟨1108023, by rfl⟩ : syracuseStep 2954729 = 2216047) B2216047
theorem B1969819 : Blo 1969435 1969819 := bstep (se 1 (by rfl) ⟨1477364, by rfl⟩ : syracuseStep 1969819 = 2954729) B2954729
theorem B12621109 : Blo 1969435 12621109 := bbase (se 5 (by rfl) ⟨591614, by rfl⟩ : syracuseStep 12621109 = 1183229) (by norm_num)
theorem B16828145 : Blo 1969435 16828145 := bstep (se 2 (by rfl) ⟨6310554, by rfl⟩ : syracuseStep 16828145 = 12621109) B12621109
theorem B11218763 : Blo 1969435 11218763 := bstep (se 1 (by rfl) ⟨8414072, by rfl⟩ : syracuseStep 11218763 = 16828145) B16828145
theorem B7479175 : Blo 1969435 7479175 := bstep (se 1 (by rfl) ⟨5609381, by rfl⟩ : syracuseStep 7479175 = 11218763) B11218763
theorem B9972233 : Blo 1969435 9972233 := bstep (se 2 (by rfl) ⟨3739587, by rfl⟩ : syracuseStep 9972233 = 7479175) B7479175
theorem B6648155 : Blo 1969435 6648155 := bstep (se 1 (by rfl) ⟨4986116, by rfl⟩ : syracuseStep 6648155 = 9972233) B9972233
theorem B4432103 : Blo 1969435 4432103 := bstep (se 1 (by rfl) ⟨3324077, by rfl⟩ : syracuseStep 4432103 = 6648155) B6648155
theorem B2954735 : Blo 1969435 2954735 := bstep (se 1 (by rfl) ⟨2216051, by rfl⟩ : syracuseStep 2954735 = 4432103) B4432103
theorem B1969823 : Blo 1969435 1969823 := bstep (se 1 (by rfl) ⟨1477367, by rfl⟩ : syracuseStep 1969823 = 2954735) B2954735
theorem B2954741 : Blo 1969435 2954741 := bbase (se 5 (by rfl) ⟨138503, by rfl⟩ : syracuseStep 2954741 = 277007) (by norm_num)
theorem B1969827 : Blo 1969435 1969827 := bstep (se 1 (by rfl) ⟨1477370, by rfl⟩ : syracuseStep 1969827 = 2954741) B2954741
theorem B2246297 : Blo 1969435 2246297 := bbase (se 2 (by rfl) ⟨842361, by rfl⟩ : syracuseStep 2246297 = 1684723) (by norm_num)
theorem B5990125 : Blo 1969435 5990125 := bstep (se 3 (by rfl) ⟨1123148, by rfl⟩ : syracuseStep 5990125 = 2246297) B2246297
theorem B7986833 : Blo 1969435 7986833 := bstep (se 2 (by rfl) ⟨2995062, by rfl⟩ : syracuseStep 7986833 = 5990125) B5990125
theorem B5324555 : Blo 1969435 5324555 := bstep (se 1 (by rfl) ⟨3993416, by rfl⟩ : syracuseStep 5324555 = 7986833) B7986833
theorem B3549703 : Blo 1969435 3549703 := bstep (se 1 (by rfl) ⟨2662277, by rfl⟩ : syracuseStep 3549703 = 5324555) B5324555
theorem B4732937 : Blo 1969435 4732937 := bstep (se 2 (by rfl) ⟨1774851, by rfl⟩ : syracuseStep 4732937 = 3549703) B3549703
theorem B3155291 : Blo 1969435 3155291 := bstep (se 1 (by rfl) ⟨2366468, by rfl⟩ : syracuseStep 3155291 = 4732937) B4732937
theorem B2103527 : Blo 1969435 2103527 := bstep (se 1 (by rfl) ⟨1577645, by rfl⟩ : syracuseStep 2103527 = 3155291) B3155291
theorem B5609405 : Blo 1969435 5609405 := bstep (se 3 (by rfl) ⟨1051763, by rfl⟩ : syracuseStep 5609405 = 2103527) B2103527
theorem B3739603 : Blo 1969435 3739603 := bstep (se 1 (by rfl) ⟨2804702, by rfl⟩ : syracuseStep 3739603 = 5609405) B5609405
theorem B4986137 : Blo 1969435 4986137 := bstep (se 2 (by rfl) ⟨1869801, by rfl⟩ : syracuseStep 4986137 = 3739603) B3739603
theorem B3324091 : Blo 1969435 3324091 := bstep (se 1 (by rfl) ⟨2493068, by rfl⟩ : syracuseStep 3324091 = 4986137) B4986137
theorem B4432121 : Blo 1969435 4432121 := bstep (se 2 (by rfl) ⟨1662045, by rfl⟩ : syracuseStep 4432121 = 3324091) B3324091
theorem B2954747 : Blo 1969435 2954747 := bstep (se 1 (by rfl) ⟨2216060, by rfl⟩ : syracuseStep 2954747 = 4432121) B4432121
theorem B1969831 : Blo 1969435 1969831 := bstep (se 1 (by rfl) ⟨1477373, by rfl⟩ : syracuseStep 1969831 = 2954747) B2954747
theorem B2216065 : Blo 1969435 2216065 := bbase (se 2 (by rfl) ⟨831024, by rfl⟩ : syracuseStep 2216065 = 1662049) (by norm_num)
theorem B2954753 : Blo 1969435 2954753 := bstep (se 2 (by rfl) ⟨1108032, by rfl⟩ : syracuseStep 2954753 = 2216065) B2216065
theorem B1969835 : Blo 1969435 1969835 := bstep (se 1 (by rfl) ⟨1477376, by rfl⟩ : syracuseStep 1969835 = 2954753) B2954753
theorem B4986157 : Blo 1969435 4986157 := bbase (se 3 (by rfl) ⟨934904, by rfl⟩ : syracuseStep 4986157 = 1869809) (by norm_num)
theorem B6648209 : Blo 1969435 6648209 := bstep (se 2 (by rfl) ⟨2493078, by rfl⟩ : syracuseStep 6648209 = 4986157) B4986157
theorem B4432139 : Blo 1969435 4432139 := bstep (se 1 (by rfl) ⟨3324104, by rfl⟩ : syracuseStep 4432139 = 6648209) B6648209
theorem B2954759 : Blo 1969435 2954759 := bstep (se 1 (by rfl) ⟨2216069, by rfl⟩ : syracuseStep 2954759 = 4432139) B4432139
theorem B1969839 : Blo 1969435 1969839 := bstep (se 1 (by rfl) ⟨1477379, by rfl⟩ : syracuseStep 1969839 = 2954759) B2954759
theorem B2954765 : Blo 1969435 2954765 := bbase (se 3 (by rfl) ⟨554018, by rfl⟩ : syracuseStep 2954765 = 1108037) (by norm_num)
theorem B1969843 : Blo 1969435 1969843 := bstep (se 1 (by rfl) ⟨1477382, by rfl⟩ : syracuseStep 1969843 = 2954765) B2954765
theorem B4432157 : Blo 1969435 4432157 := bbase (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) (by norm_num)
theorem B2954771 : Blo 1969435 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B1969847 : Blo 1969435 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B3324125 : Blo 1969435 3324125 := bbase (se 3 (by rfl) ⟨623273, by rfl⟩ : syracuseStep 3324125 = 1246547) (by norm_num)
theorem B2216083 : Blo 1969435 2216083 := bstep (se 1 (by rfl) ⟨1662062, by rfl⟩ : syracuseStep 2216083 = 3324125) B3324125
theorem B2954777 : Blo 1969435 2954777 := bstep (se 2 (by rfl) ⟨1108041, by rfl⟩ : syracuseStep 2954777 = 2216083) B2216083
theorem B1969851 : Blo 1969435 1969851 := bstep (se 1 (by rfl) ⟨1477388, by rfl⟩ : syracuseStep 1969851 = 2954777) B2954777
theorem B2662309 : Blo 1969435 2662309 := bbase (se 4 (by rfl) ⟨249591, by rfl⟩ : syracuseStep 2662309 = 499183) (by norm_num)
theorem B3549745 : Blo 1969435 3549745 := bstep (se 2 (by rfl) ⟨1331154, by rfl⟩ : syracuseStep 3549745 = 2662309) B2662309
theorem B4732993 : Blo 1969435 4732993 := bstep (se 2 (by rfl) ⟨1774872, by rfl⟩ : syracuseStep 4732993 = 3549745) B3549745
theorem B6310657 : Blo 1969435 6310657 := bstep (se 2 (by rfl) ⟨2366496, by rfl⟩ : syracuseStep 6310657 = 4732993) B4732993
theorem B8414209 : Blo 1969435 8414209 := bstep (se 2 (by rfl) ⟨3155328, by rfl⟩ : syracuseStep 8414209 = 6310657) B6310657
theorem B11218945 : Blo 1969435 11218945 := bstep (se 2 (by rfl) ⟨4207104, by rfl⟩ : syracuseStep 11218945 = 8414209) B8414209
theorem B14958593 : Blo 1969435 14958593 := bstep (se 2 (by rfl) ⟨5609472, by rfl⟩ : syracuseStep 14958593 = 11218945) B11218945
theorem B9972395 : Blo 1969435 9972395 := bstep (se 1 (by rfl) ⟨7479296, by rfl⟩ : syracuseStep 9972395 = 14958593) B14958593
theorem B6648263 : Blo 1969435 6648263 := bstep (se 1 (by rfl) ⟨4986197, by rfl⟩ : syracuseStep 6648263 = 9972395) B9972395
theorem B4432175 : Blo 1969435 4432175 := bstep (se 1 (by rfl) ⟨3324131, by rfl⟩ : syracuseStep 4432175 = 6648263) B6648263
theorem B2954783 : Blo 1969435 2954783 := bstep (se 1 (by rfl) ⟨2216087, by rfl⟩ : syracuseStep 2954783 = 4432175) B4432175
theorem B1969855 : Blo 1969435 1969855 := bstep (se 1 (by rfl) ⟨1477391, by rfl⟩ : syracuseStep 1969855 = 2954783) B2954783
theorem B2954789 : Blo 1969435 2954789 := bbase (se 4 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 2954789 = 554023) (by norm_num)
theorem B1969859 : Blo 1969435 1969859 := bstep (se 1 (by rfl) ⟨1477394, by rfl⟩ : syracuseStep 1969859 = 2954789) B2954789
theorem B2493109 : Blo 1969435 2493109 := bbase (se 5 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 2493109 = 233729) (by norm_num)
theorem B3324145 : Blo 1969435 3324145 := bstep (se 2 (by rfl) ⟨1246554, by rfl⟩ : syracuseStep 3324145 = 2493109) B2493109
theorem B4432193 : Blo 1969435 4432193 := bstep (se 2 (by rfl) ⟨1662072, by rfl⟩ : syracuseStep 4432193 = 3324145) B3324145
theorem B2954795 : Blo 1969435 2954795 := bstep (se 1 (by rfl) ⟨2216096, by rfl⟩ : syracuseStep 2954795 = 4432193) B4432193
theorem B1969863 : Blo 1969435 1969863 := bstep (se 1 (by rfl) ⟨1477397, by rfl⟩ : syracuseStep 1969863 = 2954795) B2954795
theorem B2216101 : Blo 1969435 2216101 := bbase (se 4 (by rfl) ⟨207759, by rfl⟩ : syracuseStep 2216101 = 415519) (by norm_num)
theorem B2954801 : Blo 1969435 2954801 := bstep (se 2 (by rfl) ⟨1108050, by rfl⟩ : syracuseStep 2954801 = 2216101) B2216101
theorem B1969867 : Blo 1969435 1969867 := bstep (se 1 (by rfl) ⟨1477400, by rfl⟩ : syracuseStep 1969867 = 2954801) B2954801
theorem B20217077 : Blo 1969435 20217077 := bbase (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) (by norm_num)
theorem B13478051 : Blo 1969435 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B8985367 : Blo 1969435 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B11980489 : Blo 1969435 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B15973985 : Blo 1969435 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B10649323 : Blo 1969435 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B14199097 : Blo 1969435 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B18932129 : Blo 1969435 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B12621419 : Blo 1969435 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B8414279 : Blo 1969435 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B5609519 : Blo 1969435 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B3739679 : Blo 1969435 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B2493119 : Blo 1969435 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B6648317 : Blo 1969435 6648317 := bstep (se 3 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 6648317 = 2493119) B2493119
theorem B4432211 : Blo 1969435 4432211 := bstep (se 1 (by rfl) ⟨3324158, by rfl⟩ : syracuseStep 4432211 = 6648317) B6648317
theorem B2954807 : Blo 1969435 2954807 := bstep (se 1 (by rfl) ⟨2216105, by rfl⟩ : syracuseStep 2954807 = 4432211) B4432211
theorem B1969871 : Blo 1969435 1969871 := bstep (se 1 (by rfl) ⟨1477403, by rfl⟩ : syracuseStep 1969871 = 2954807) B2954807
theorem B2954813 : Blo 1969435 2954813 := bbase (se 3 (by rfl) ⟨554027, by rfl⟩ : syracuseStep 2954813 = 1108055) (by norm_num)
theorem B1969875 : Blo 1969435 1969875 := bstep (se 1 (by rfl) ⟨1477406, by rfl⟩ : syracuseStep 1969875 = 2954813) B2954813
theorem B4432229 : Blo 1969435 4432229 := bbase (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) (by norm_num)
theorem B2954819 : Blo 1969435 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B1969879 : Blo 1969435 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B4986269 : Blo 1969435 4986269 := bbase (se 3 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 4986269 = 1869851) (by norm_num)
theorem B3324179 : Blo 1969435 3324179 := bstep (se 1 (by rfl) ⟨2493134, by rfl⟩ : syracuseStep 3324179 = 4986269) B4986269
theorem B2216119 : Blo 1969435 2216119 := bstep (se 1 (by rfl) ⟨1662089, by rfl⟩ : syracuseStep 2216119 = 3324179) B3324179
theorem B2954825 : Blo 1969435 2954825 := bstep (se 2 (by rfl) ⟨1108059, by rfl⟩ : syracuseStep 2954825 = 2216119) B2216119
theorem B1969883 : Blo 1969435 1969883 := bstep (se 1 (by rfl) ⟨1477412, by rfl⟩ : syracuseStep 1969883 = 2954825) B2954825
theorem B3739709 : Blo 1969435 3739709 := bbase (se 3 (by rfl) ⟨701195, by rfl⟩ : syracuseStep 3739709 = 1402391) (by norm_num)
theorem B9972557 : Blo 1969435 9972557 := bstep (se 3 (by rfl) ⟨1869854, by rfl⟩ : syracuseStep 9972557 = 3739709) B3739709
theorem B6648371 : Blo 1969435 6648371 := bstep (se 1 (by rfl) ⟨4986278, by rfl⟩ : syracuseStep 6648371 = 9972557) B9972557
theorem B4432247 : Blo 1969435 4432247 := bstep (se 1 (by rfl) ⟨3324185, by rfl⟩ : syracuseStep 4432247 = 6648371) B6648371
theorem B2954831 : Blo 1969435 2954831 := bstep (se 1 (by rfl) ⟨2216123, by rfl⟩ : syracuseStep 2954831 = 4432247) B4432247
theorem B1969887 : Blo 1969435 1969887 := bstep (se 1 (by rfl) ⟨1477415, by rfl⟩ : syracuseStep 1969887 = 2954831) B2954831
theorem B2954837 : Blo 1969435 2954837 := bbase (se 8 (by rfl) ⟨17313, by rfl⟩ : syracuseStep 2954837 = 34627) (by norm_num)
theorem B1969891 : Blo 1969435 1969891 := bstep (se 1 (by rfl) ⟨1477418, by rfl⟩ : syracuseStep 1969891 = 2954837) B2954837
theorem B2366545 : Blo 1969435 2366545 := bbase (se 2 (by rfl) ⟨887454, by rfl⟩ : syracuseStep 2366545 = 1774909) (by norm_num)
theorem B3155393 : Blo 1969435 3155393 := bstep (se 2 (by rfl) ⟨1183272, by rfl⟩ : syracuseStep 3155393 = 2366545) B2366545
theorem B8414381 : Blo 1969435 8414381 := bstep (se 3 (by rfl) ⟨1577696, by rfl⟩ : syracuseStep 8414381 = 3155393) B3155393
theorem B5609587 : Blo 1969435 5609587 := bstep (se 1 (by rfl) ⟨4207190, by rfl⟩ : syracuseStep 5609587 = 8414381) B8414381
theorem B7479449 : Blo 1969435 7479449 := bstep (se 2 (by rfl) ⟨2804793, by rfl⟩ : syracuseStep 7479449 = 5609587) B5609587
theorem B4986299 : Blo 1969435 4986299 := bstep (se 1 (by rfl) ⟨3739724, by rfl⟩ : syracuseStep 4986299 = 7479449) B7479449
theorem B3324199 : Blo 1969435 3324199 := bstep (se 1 (by rfl) ⟨2493149, by rfl⟩ : syracuseStep 3324199 = 4986299) B4986299
theorem B4432265 : Blo 1969435 4432265 := bstep (se 2 (by rfl) ⟨1662099, by rfl⟩ : syracuseStep 4432265 = 3324199) B3324199
theorem B2954843 : Blo 1969435 2954843 := bstep (se 1 (by rfl) ⟨2216132, by rfl⟩ : syracuseStep 2954843 = 4432265) B4432265
theorem B1969895 : Blo 1969435 1969895 := bstep (se 1 (by rfl) ⟨1477421, by rfl⟩ : syracuseStep 1969895 = 2954843) B2954843
theorem B2216137 : Blo 1969435 2216137 := bbase (se 2 (by rfl) ⟨831051, by rfl⟩ : syracuseStep 2216137 = 1662103) (by norm_num)
theorem B2954849 : Blo 1969435 2954849 := bstep (se 2 (by rfl) ⟨1108068, by rfl⟩ : syracuseStep 2954849 = 2216137) B2216137
theorem B1969899 : Blo 1969435 1969899 := bstep (se 1 (by rfl) ⟨1477424, by rfl⟩ : syracuseStep 1969899 = 2954849) B2954849
theorem B23961365 : Blo 1969435 23961365 := bbase (se 6 (by rfl) ⟨561594, by rfl⟩ : syracuseStep 23961365 = 1123189) (by norm_num)
theorem B15974243 : Blo 1969435 15974243 := bstep (se 1 (by rfl) ⟨11980682, by rfl⟩ : syracuseStep 15974243 = 23961365) B23961365
theorem B10649495 : Blo 1969435 10649495 := bstep (se 1 (by rfl) ⟨7987121, by rfl⟩ : syracuseStep 10649495 = 15974243) B15974243
theorem B7099663 : Blo 1969435 7099663 := bstep (se 1 (by rfl) ⟨5324747, by rfl⟩ : syracuseStep 7099663 = 10649495) B10649495
theorem B9466217 : Blo 1969435 9466217 := bstep (se 2 (by rfl) ⟨3549831, by rfl⟩ : syracuseStep 9466217 = 7099663) B7099663
theorem B6310811 : Blo 1969435 6310811 := bstep (se 1 (by rfl) ⟨4733108, by rfl⟩ : syracuseStep 6310811 = 9466217) B9466217
theorem B16828829 : Blo 1969435 16828829 := bstep (se 3 (by rfl) ⟨3155405, by rfl⟩ : syracuseStep 16828829 = 6310811) B6310811
theorem B11219219 : Blo 1969435 11219219 := bstep (se 1 (by rfl) ⟨8414414, by rfl⟩ : syracuseStep 11219219 = 16828829) B16828829
theorem B7479479 : Blo 1969435 7479479 := bstep (se 1 (by rfl) ⟨5609609, by rfl⟩ : syracuseStep 7479479 = 11219219) B11219219
theorem B4986319 : Blo 1969435 4986319 := bstep (se 1 (by rfl) ⟨3739739, by rfl⟩ : syracuseStep 4986319 = 7479479) B7479479
theorem B6648425 : Blo 1969435 6648425 := bstep (se 2 (by rfl) ⟨2493159, by rfl⟩ : syracuseStep 6648425 = 4986319) B4986319
theorem B4432283 : Blo 1969435 4432283 := bstep (se 1 (by rfl) ⟨3324212, by rfl⟩ : syracuseStep 4432283 = 6648425) B6648425
theorem B2954855 : Blo 1969435 2954855 := bstep (se 1 (by rfl) ⟨2216141, by rfl⟩ : syracuseStep 2954855 = 4432283) B4432283
theorem B1969903 : Blo 1969435 1969903 := bstep (se 1 (by rfl) ⟨1477427, by rfl⟩ : syracuseStep 1969903 = 2954855) B2954855
theorem B2954861 : Blo 1969435 2954861 := bbase (se 3 (by rfl) ⟨554036, by rfl⟩ : syracuseStep 2954861 = 1108073) (by norm_num)
theorem B1969907 : Blo 1969435 1969907 := bstep (se 1 (by rfl) ⟨1477430, by rfl⟩ : syracuseStep 1969907 = 2954861) B2954861
theorem B4432301 : Blo 1969435 4432301 := bbase (se 3 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 4432301 = 1662113) (by norm_num)
theorem B2954867 : Blo 1969435 2954867 := bstep (se 1 (by rfl) ⟨2216150, by rfl⟩ : syracuseStep 2954867 = 4432301) B4432301
theorem B1969911 : Blo 1969435 1969911 := bstep (se 1 (by rfl) ⟨1477433, by rfl⟩ : syracuseStep 1969911 = 2954867) B2954867
theorem B2103617 : Blo 1969435 2103617 := bbase (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) (by norm_num)
theorem B5609645 : Blo 1969435 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B3739763 : Blo 1969435 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B2493175 : Blo 1969435 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B3324233 : Blo 1969435 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B2216155 : Blo 1969435 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B2954873 : Blo 1969435 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B1969915 : Blo 1969435 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B2881885 : Blo 1969435 2881885 := bbase (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) (by norm_num)
theorem B3842513 : Blo 1969435 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B2561675 : Blo 1969435 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B27324533 : Blo 1969435 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B18216355 : Blo 1969435 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B24288473 : Blo 1969435 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B16192315 : Blo 1969435 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B21589753 : Blo 1969435 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B28786337 : Blo 1969435 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B19190891 : Blo 1969435 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B51175709 : Blo 1969435 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B34117139 : Blo 1969435 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B22744759 : Blo 1969435 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B30326345 : Blo 1969435 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B20217563 : Blo 1969435 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B13478375 : Blo 1969435 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B8985583 : Blo 1969435 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B47923109 : Blo 1969435 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B31948739 : Blo 1969435 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B21299159 : Blo 1969435 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B56797757 : Blo 1969435 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B37865171 : Blo 1969435 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B25243447 : Blo 1969435 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B33657929 : Blo 1969435 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B22438619 : Blo 1969435 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B14959079 : Blo 1969435 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B9972719 : Blo 1969435 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B6648479 : Blo 1969435 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B4432319 : Blo 1969435 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B2954879 : Blo 1969435 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B1969919 : Blo 1969435 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B2954885 : Blo 1969435 2954885 := bbase (se 4 (by rfl) ⟨277020, by rfl⟩ : syracuseStep 2954885 = 554041) (by norm_num)
theorem B1969923 : Blo 1969435 1969923 := bstep (se 1 (by rfl) ⟨1477442, by rfl⟩ : syracuseStep 1969923 = 2954885) B2954885
theorem B3324253 : Blo 1969435 3324253 := bbase (se 3 (by rfl) ⟨623297, by rfl⟩ : syracuseStep 3324253 = 1246595) (by norm_num)
theorem B4432337 : Blo 1969435 4432337 := bstep (se 2 (by rfl) ⟨1662126, by rfl⟩ : syracuseStep 4432337 = 3324253) B3324253
theorem B2954891 : Blo 1969435 2954891 := bstep (se 1 (by rfl) ⟨2216168, by rfl⟩ : syracuseStep 2954891 = 4432337) B4432337
theorem B1969927 : Blo 1969435 1969927 := bstep (se 1 (by rfl) ⟨1477445, by rfl⟩ : syracuseStep 1969927 = 2954891) B2954891
theorem B2216173 : Blo 1969435 2216173 := bbase (se 3 (by rfl) ⟨415532, by rfl⟩ : syracuseStep 2216173 = 831065) (by norm_num)
theorem B2954897 : Blo 1969435 2954897 := bstep (se 2 (by rfl) ⟨1108086, by rfl⟩ : syracuseStep 2954897 = 2216173) B2216173
theorem B1969931 : Blo 1969435 1969931 := bstep (se 1 (by rfl) ⟨1477448, by rfl⟩ : syracuseStep 1969931 = 2954897) B2954897
theorem B6648533 : Blo 1969435 6648533 := bbase (se 7 (by rfl) ⟨77912, by rfl⟩ : syracuseStep 6648533 = 155825) (by norm_num)
theorem B4432355 : Blo 1969435 4432355 := bstep (se 1 (by rfl) ⟨3324266, by rfl⟩ : syracuseStep 4432355 = 6648533) B6648533
theorem B2954903 : Blo 1969435 2954903 := bstep (se 1 (by rfl) ⟨2216177, by rfl⟩ : syracuseStep 2954903 = 4432355) B4432355
theorem B1969935 : Blo 1969435 1969935 := bstep (se 1 (by rfl) ⟨1477451, by rfl⟩ : syracuseStep 1969935 = 2954903) B2954903
theorem B2954909 : Blo 1969435 2954909 := bbase (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) (by norm_num)
theorem B1969939 : Blo 1969435 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B4432373 : Blo 1969435 4432373 := bbase (se 5 (by rfl) ⟨207767, by rfl⟩ : syracuseStep 4432373 = 415535) (by norm_num)
theorem B2954915 : Blo 1969435 2954915 := bstep (se 1 (by rfl) ⟨2216186, by rfl⟩ : syracuseStep 2954915 = 4432373) B4432373
theorem B1969943 : Blo 1969435 1969943 := bstep (se 1 (by rfl) ⟨1477457, by rfl⟩ : syracuseStep 1969943 = 2954915) B2954915
theorem B7987301 : Blo 1969435 7987301 := bbase (se 4 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 7987301 = 1497619) (by norm_num)
theorem B5324867 : Blo 1969435 5324867 := bstep (se 1 (by rfl) ⟨3993650, by rfl⟩ : syracuseStep 5324867 = 7987301) B7987301
theorem B3549911 : Blo 1969435 3549911 := bstep (se 1 (by rfl) ⟨2662433, by rfl⟩ : syracuseStep 3549911 = 5324867) B5324867
theorem B37865717 : Blo 1969435 37865717 := bstep (se 5 (by rfl) ⟨1774955, by rfl⟩ : syracuseStep 37865717 = 3549911) B3549911
theorem B25243811 : Blo 1969435 25243811 := bstep (se 1 (by rfl) ⟨18932858, by rfl⟩ : syracuseStep 25243811 = 37865717) B37865717
theorem B16829207 : Blo 1969435 16829207 := bstep (se 1 (by rfl) ⟨12621905, by rfl⟩ : syracuseStep 16829207 = 25243811) B25243811
theorem B11219471 : Blo 1969435 11219471 := bstep (se 1 (by rfl) ⟨8414603, by rfl⟩ : syracuseStep 11219471 = 16829207) B16829207
theorem B7479647 : Blo 1969435 7479647 := bstep (se 1 (by rfl) ⟨5609735, by rfl⟩ : syracuseStep 7479647 = 11219471) B11219471
theorem B4986431 : Blo 1969435 4986431 := bstep (se 1 (by rfl) ⟨3739823, by rfl⟩ : syracuseStep 4986431 = 7479647) B7479647
theorem B3324287 : Blo 1969435 3324287 := bstep (se 1 (by rfl) ⟨2493215, by rfl⟩ : syracuseStep 3324287 = 4986431) B4986431
theorem B2216191 : Blo 1969435 2216191 := bstep (se 1 (by rfl) ⟨1662143, by rfl⟩ : syracuseStep 2216191 = 3324287) B3324287
theorem B2954921 : Blo 1969435 2954921 := bstep (se 2 (by rfl) ⟨1108095, by rfl⟩ : syracuseStep 2954921 = 2216191) B2216191
theorem B1969947 : Blo 1969435 1969947 := bstep (se 1 (by rfl) ⟨1477460, by rfl⟩ : syracuseStep 1969947 = 2954921) B2954921
theorem B6739301 : Blo 1969435 6739301 := bbase (se 4 (by rfl) ⟨631809, by rfl⟩ : syracuseStep 6739301 = 1263619) (by norm_num)
theorem B17971469 : Blo 1969435 17971469 := bstep (se 3 (by rfl) ⟨3369650, by rfl⟩ : syracuseStep 17971469 = 6739301) B6739301
theorem B11980979 : Blo 1969435 11980979 := bstep (se 1 (by rfl) ⟨8985734, by rfl⟩ : syracuseStep 11980979 = 17971469) B17971469
theorem B7987319 : Blo 1969435 7987319 := bstep (se 1 (by rfl) ⟨5990489, by rfl⟩ : syracuseStep 7987319 = 11980979) B11980979
theorem B5324879 : Blo 1969435 5324879 := bstep (se 1 (by rfl) ⟨3993659, by rfl⟩ : syracuseStep 5324879 = 7987319) B7987319
theorem B3549919 : Blo 1969435 3549919 := bstep (se 1 (by rfl) ⟨2662439, by rfl⟩ : syracuseStep 3549919 = 5324879) B5324879
theorem B4733225 : Blo 1969435 4733225 := bstep (se 2 (by rfl) ⟨1774959, by rfl⟩ : syracuseStep 4733225 = 3549919) B3549919
theorem B3155483 : Blo 1969435 3155483 := bstep (se 1 (by rfl) ⟨2366612, by rfl⟩ : syracuseStep 3155483 = 4733225) B4733225
theorem B2103655 : Blo 1969435 2103655 := bstep (se 1 (by rfl) ⟨1577741, by rfl⟩ : syracuseStep 2103655 = 3155483) B3155483
theorem B2804873 : Blo 1969435 2804873 := bstep (se 2 (by rfl) ⟨1051827, by rfl⟩ : syracuseStep 2804873 = 2103655) B2103655
theorem B7479661 : Blo 1969435 7479661 := bstep (se 3 (by rfl) ⟨1402436, by rfl⟩ : syracuseStep 7479661 = 2804873) B2804873
theorem B9972881 : Blo 1969435 9972881 := bstep (se 2 (by rfl) ⟨3739830, by rfl⟩ : syracuseStep 9972881 = 7479661) B7479661
theorem B6648587 : Blo 1969435 6648587 := bstep (se 1 (by rfl) ⟨4986440, by rfl⟩ : syracuseStep 6648587 = 9972881) B9972881
theorem B4432391 : Blo 1969435 4432391 := bstep (se 1 (by rfl) ⟨3324293, by rfl⟩ : syracuseStep 4432391 = 6648587) B6648587
theorem B2954927 : Blo 1969435 2954927 := bstep (se 1 (by rfl) ⟨2216195, by rfl⟩ : syracuseStep 2954927 = 4432391) B4432391
theorem B1969951 : Blo 1969435 1969951 := bstep (se 1 (by rfl) ⟨1477463, by rfl⟩ : syracuseStep 1969951 = 2954927) B2954927
theorem B2954933 : Blo 1969435 2954933 := bbase (se 5 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 2954933 = 277025) (by norm_num)
theorem B1969955 : Blo 1969435 1969955 := bstep (se 1 (by rfl) ⟨1477466, by rfl⟩ : syracuseStep 1969955 = 2954933) B2954933
theorem B4986461 : Blo 1969435 4986461 := bbase (se 3 (by rfl) ⟨934961, by rfl⟩ : syracuseStep 4986461 = 1869923) (by norm_num)
theorem B3324307 : Blo 1969435 3324307 := bstep (se 1 (by rfl) ⟨2493230, by rfl⟩ : syracuseStep 3324307 = 4986461) B4986461
theorem B4432409 : Blo 1969435 4432409 := bstep (se 2 (by rfl) ⟨1662153, by rfl⟩ : syracuseStep 4432409 = 3324307) B3324307
theorem B2954939 : Blo 1969435 2954939 := bstep (se 1 (by rfl) ⟨2216204, by rfl⟩ : syracuseStep 2954939 = 4432409) B4432409
theorem B1969959 : Blo 1969435 1969959 := bstep (se 1 (by rfl) ⟨1477469, by rfl⟩ : syracuseStep 1969959 = 2954939) B2954939
theorem B2216209 : Blo 1969435 2216209 := bbase (se 2 (by rfl) ⟨831078, by rfl⟩ : syracuseStep 2216209 = 1662157) (by norm_num)
theorem B2954945 : Blo 1969435 2954945 := bstep (se 2 (by rfl) ⟨1108104, by rfl⟩ : syracuseStep 2954945 = 2216209) B2216209
theorem B1969963 : Blo 1969435 1969963 := bstep (se 1 (by rfl) ⟨1477472, by rfl⟩ : syracuseStep 1969963 = 2954945) B2954945
theorem B3739861 : Blo 1969435 3739861 := bbase (se 7 (by rfl) ⟨43826, by rfl⟩ : syracuseStep 3739861 = 87653) (by norm_num)
theorem B4986481 : Blo 1969435 4986481 := bstep (se 2 (by rfl) ⟨1869930, by rfl⟩ : syracuseStep 4986481 = 3739861) B3739861
theorem B6648641 : Blo 1969435 6648641 := bstep (se 2 (by rfl) ⟨2493240, by rfl⟩ : syracuseStep 6648641 = 4986481) B4986481
theorem B4432427 : Blo 1969435 4432427 := bstep (se 1 (by rfl) ⟨3324320, by rfl⟩ : syracuseStep 4432427 = 6648641) B6648641
theorem B2954951 : Blo 1969435 2954951 := bstep (se 1 (by rfl) ⟨2216213, by rfl⟩ : syracuseStep 2954951 = 4432427) B4432427
theorem B1969967 : Blo 1969435 1969967 := bstep (se 1 (by rfl) ⟨1477475, by rfl⟩ : syracuseStep 1969967 = 2954951) B2954951
theorem B2954957 : Blo 1969435 2954957 := bbase (se 3 (by rfl) ⟨554054, by rfl⟩ : syracuseStep 2954957 = 1108109) (by norm_num)
theorem B1969971 : Blo 1969435 1969971 := bstep (se 1 (by rfl) ⟨1477478, by rfl⟩ : syracuseStep 1969971 = 2954957) B2954957
theorem B4432445 : Blo 1969435 4432445 := bbase (se 3 (by rfl) ⟨831083, by rfl⟩ : syracuseStep 4432445 = 1662167) (by norm_num)
theorem B2954963 : Blo 1969435 2954963 := bstep (se 1 (by rfl) ⟨2216222, by rfl⟩ : syracuseStep 2954963 = 4432445) B4432445
theorem B1969975 : Blo 1969435 1969975 := bstep (se 1 (by rfl) ⟨1477481, by rfl⟩ : syracuseStep 1969975 = 2954963) B2954963
theorem B3324341 : Blo 1969435 3324341 := bbase (se 5 (by rfl) ⟨155828, by rfl⟩ : syracuseStep 3324341 = 311657) (by norm_num)
theorem B2216227 : Blo 1969435 2216227 := bstep (se 1 (by rfl) ⟨1662170, by rfl⟩ : syracuseStep 2216227 = 3324341) B3324341
theorem B2954969 : Blo 1969435 2954969 := bstep (se 2 (by rfl) ⟨1108113, by rfl⟩ : syracuseStep 2954969 = 2216227) B2216227
theorem B1969979 : Blo 1969435 1969979 := bstep (se 1 (by rfl) ⟨1477484, by rfl⟩ : syracuseStep 1969979 = 2954969) B2954969
theorem B2103689 : Blo 1969435 2103689 := bbase (se 2 (by rfl) ⟨788883, by rfl⟩ : syracuseStep 2103689 = 1577767) (by norm_num)
theorem B5609837 : Blo 1969435 5609837 := bstep (se 3 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 5609837 = 2103689) B2103689
theorem B14959565 : Blo 1969435 14959565 := bstep (se 3 (by rfl) ⟨2804918, by rfl⟩ : syracuseStep 14959565 = 5609837) B5609837
theorem B9973043 : Blo 1969435 9973043 := bstep (se 1 (by rfl) ⟨7479782, by rfl⟩ : syracuseStep 9973043 = 14959565) B14959565
theorem B6648695 : Blo 1969435 6648695 := bstep (se 1 (by rfl) ⟨4986521, by rfl⟩ : syracuseStep 6648695 = 9973043) B9973043
theorem B4432463 : Blo 1969435 4432463 := bstep (se 1 (by rfl) ⟨3324347, by rfl⟩ : syracuseStep 4432463 = 6648695) B6648695
theorem B2954975 : Blo 1969435 2954975 := bstep (se 1 (by rfl) ⟨2216231, by rfl⟩ : syracuseStep 2954975 = 4432463) B4432463
theorem B1969983 : Blo 1969435 1969983 := bstep (se 1 (by rfl) ⟨1477487, by rfl⟩ : syracuseStep 1969983 = 2954975) B2954975
theorem B2954981 : Blo 1969435 2954981 := bbase (se 4 (by rfl) ⟨277029, by rfl⟩ : syracuseStep 2954981 = 554059) (by norm_num)
theorem B1969987 : Blo 1969435 1969987 := bstep (se 1 (by rfl) ⟨1477490, by rfl⟩ : syracuseStep 1969987 = 2954981) B2954981
theorem B5609861 : Blo 1969435 5609861 := bbase (se 4 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 5609861 = 1051849) (by norm_num)
theorem B3739907 : Blo 1969435 3739907 := bstep (se 1 (by rfl) ⟨2804930, by rfl⟩ : syracuseStep 3739907 = 5609861) B5609861
theorem B2493271 : Blo 1969435 2493271 := bstep (se 1 (by rfl) ⟨1869953, by rfl⟩ : syracuseStep 2493271 = 3739907) B3739907
theorem B3324361 : Blo 1969435 3324361 := bstep (se 2 (by rfl) ⟨1246635, by rfl⟩ : syracuseStep 3324361 = 2493271) B2493271
theorem B4432481 : Blo 1969435 4432481 := bstep (se 2 (by rfl) ⟨1662180, by rfl⟩ : syracuseStep 4432481 = 3324361) B3324361
theorem B2954987 : Blo 1969435 2954987 := bstep (se 1 (by rfl) ⟨2216240, by rfl⟩ : syracuseStep 2954987 = 4432481) B4432481
theorem B1969991 : Blo 1969435 1969991 := bstep (se 1 (by rfl) ⟨1477493, by rfl⟩ : syracuseStep 1969991 = 2954987) B2954987
theorem B2216245 : Blo 1969435 2216245 := bbase (se 5 (by rfl) ⟨103886, by rfl⟩ : syracuseStep 2216245 = 207773) (by norm_num)
theorem B2954993 : Blo 1969435 2954993 := bstep (se 2 (by rfl) ⟨1108122, by rfl⟩ : syracuseStep 2954993 = 2216245) B2216245
theorem B1969995 : Blo 1969435 1969995 := bstep (se 1 (by rfl) ⟨1477496, by rfl⟩ : syracuseStep 1969995 = 2954993) B2954993
theorem B2493281 : Blo 1969435 2493281 := bbase (se 2 (by rfl) ⟨934980, by rfl⟩ : syracuseStep 2493281 = 1869961) (by norm_num)
theorem B6648749 : Blo 1969435 6648749 := bstep (se 3 (by rfl) ⟨1246640, by rfl⟩ : syracuseStep 6648749 = 2493281) B2493281
theorem B4432499 : Blo 1969435 4432499 := bstep (se 1 (by rfl) ⟨3324374, by rfl⟩ : syracuseStep 4432499 = 6648749) B6648749
theorem B2954999 : Blo 1969435 2954999 := bstep (se 1 (by rfl) ⟨2216249, by rfl⟩ : syracuseStep 2954999 = 4432499) B4432499
theorem B1969999 : Blo 1969435 1969999 := bstep (se 1 (by rfl) ⟨1477499, by rfl⟩ : syracuseStep 1969999 = 2954999) B2954999
theorem B2955005 : Blo 1969435 2955005 := bbase (se 3 (by rfl) ⟨554063, by rfl⟩ : syracuseStep 2955005 = 1108127) (by norm_num)
theorem B1970003 : Blo 1969435 1970003 := bstep (se 1 (by rfl) ⟨1477502, by rfl⟩ : syracuseStep 1970003 = 2955005) B2955005
theorem B4432517 : Blo 1969435 4432517 := bbase (se 4 (by rfl) ⟨415548, by rfl⟩ : syracuseStep 4432517 = 831097) (by norm_num)
theorem B2955011 : Blo 1969435 2955011 := bstep (se 1 (by rfl) ⟨2216258, by rfl⟩ : syracuseStep 2955011 = 4432517) B4432517
theorem B1970007 : Blo 1969435 1970007 := bstep (se 1 (by rfl) ⟨1477505, by rfl⟩ : syracuseStep 1970007 = 2955011) B2955011
theorem B3993781 : Blo 1969435 3993781 := bbase (se 5 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 3993781 = 374417) (by norm_num)
theorem B5325041 : Blo 1969435 5325041 := bstep (se 2 (by rfl) ⟨1996890, by rfl⟩ : syracuseStep 5325041 = 3993781) B3993781
theorem B14200109 : Blo 1969435 14200109 := bstep (se 3 (by rfl) ⟨2662520, by rfl⟩ : syracuseStep 14200109 = 5325041) B5325041
theorem B9466739 : Blo 1969435 9466739 := bstep (se 1 (by rfl) ⟨7100054, by rfl⟩ : syracuseStep 9466739 = 14200109) B14200109
theorem B6311159 : Blo 1969435 6311159 := bstep (se 1 (by rfl) ⟨4733369, by rfl⟩ : syracuseStep 6311159 = 9466739) B9466739
theorem B4207439 : Blo 1969435 4207439 := bstep (se 1 (by rfl) ⟨3155579, by rfl⟩ : syracuseStep 4207439 = 6311159) B6311159
theorem B2804959 : Blo 1969435 2804959 := bstep (se 1 (by rfl) ⟨2103719, by rfl⟩ : syracuseStep 2804959 = 4207439) B4207439
theorem B3739945 : Blo 1969435 3739945 := bstep (se 2 (by rfl) ⟨1402479, by rfl⟩ : syracuseStep 3739945 = 2804959) B2804959
theorem B4986593 : Blo 1969435 4986593 := bstep (se 2 (by rfl) ⟨1869972, by rfl⟩ : syracuseStep 4986593 = 3739945) B3739945
theorem B3324395 : Blo 1969435 3324395 := bstep (se 1 (by rfl) ⟨2493296, by rfl⟩ : syracuseStep 3324395 = 4986593) B4986593
theorem B2216263 : Blo 1969435 2216263 := bstep (se 1 (by rfl) ⟨1662197, by rfl⟩ : syracuseStep 2216263 = 3324395) B3324395
theorem B2955017 : Blo 1969435 2955017 := bstep (se 2 (by rfl) ⟨1108131, by rfl⟩ : syracuseStep 2955017 = 2216263) B2216263
theorem B1970011 : Blo 1969435 1970011 := bstep (se 1 (by rfl) ⟨1477508, by rfl⟩ : syracuseStep 1970011 = 2955017) B2955017
theorem B9973205 : Blo 1969435 9973205 := bbase (se 7 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 9973205 = 233747) (by norm_num)
theorem B6648803 : Blo 1969435 6648803 := bstep (se 1 (by rfl) ⟨4986602, by rfl⟩ : syracuseStep 6648803 = 9973205) B9973205
theorem B4432535 : Blo 1969435 4432535 := bstep (se 1 (by rfl) ⟨3324401, by rfl⟩ : syracuseStep 4432535 = 6648803) B6648803
theorem B2955023 : Blo 1969435 2955023 := bstep (se 1 (by rfl) ⟨2216267, by rfl⟩ : syracuseStep 2955023 = 4432535) B4432535
theorem B1970015 : Blo 1969435 1970015 := bstep (se 1 (by rfl) ⟨1477511, by rfl⟩ : syracuseStep 1970015 = 2955023) B2955023
theorem B2955029 : Blo 1969435 2955029 := bbase (se 6 (by rfl) ⟨69258, by rfl⟩ : syracuseStep 2955029 = 138517) (by norm_num)
theorem B1970019 : Blo 1969435 1970019 := bstep (se 1 (by rfl) ⟨1477514, by rfl⟩ : syracuseStep 1970019 = 2955029) B2955029
theorem B5123621 : Blo 1969435 5123621 := bbase (se 4 (by rfl) ⟨480339, by rfl⟩ : syracuseStep 5123621 = 960679) (by norm_num)
theorem B13662989 : Blo 1969435 13662989 := bstep (se 3 (by rfl) ⟨2561810, by rfl⟩ : syracuseStep 13662989 = 5123621) B5123621
theorem B9108659 : Blo 1969435 9108659 := bstep (se 1 (by rfl) ⟨6831494, by rfl⟩ : syracuseStep 9108659 = 13662989) B13662989
theorem B24289757 : Blo 1969435 24289757 := bstep (se 3 (by rfl) ⟨4554329, by rfl⟩ : syracuseStep 24289757 = 9108659) B9108659
theorem B16193171 : Blo 1969435 16193171 := bstep (se 1 (by rfl) ⟨12144878, by rfl⟩ : syracuseStep 16193171 = 24289757) B24289757
theorem B10795447 : Blo 1969435 10795447 := bstep (se 1 (by rfl) ⟨8096585, by rfl⟩ : syracuseStep 10795447 = 16193171) B16193171
theorem B14393929 : Blo 1969435 14393929 := bstep (se 2 (by rfl) ⟨5397723, by rfl⟩ : syracuseStep 14393929 = 10795447) B10795447
theorem B19191905 : Blo 1969435 19191905 := bstep (se 2 (by rfl) ⟨7196964, by rfl⟩ : syracuseStep 19191905 = 14393929) B14393929
theorem B12794603 : Blo 1969435 12794603 := bstep (se 1 (by rfl) ⟨9595952, by rfl⟩ : syracuseStep 12794603 = 19191905) B19191905
theorem B136475765 : Blo 1969435 136475765 := bstep (se 5 (by rfl) ⟨6397301, by rfl⟩ : syracuseStep 136475765 = 12794603) B12794603
theorem B90983843 : Blo 1969435 90983843 := bstep (se 1 (by rfl) ⟨68237882, by rfl⟩ : syracuseStep 90983843 = 136475765) B136475765
theorem B60655895 : Blo 1969435 60655895 := bstep (se 1 (by rfl) ⟨45491921, by rfl⟩ : syracuseStep 60655895 = 90983843) B90983843
theorem B40437263 : Blo 1969435 40437263 := bstep (se 1 (by rfl) ⟨30327947, by rfl⟩ : syracuseStep 40437263 = 60655895) B60655895
theorem B107832701 : Blo 1969435 107832701 := bstep (se 3 (by rfl) ⟨20218631, by rfl⟩ : syracuseStep 107832701 = 40437263) B40437263
theorem B71888467 : Blo 1969435 71888467 := bstep (se 1 (by rfl) ⟨53916350, by rfl⟩ : syracuseStep 71888467 = 107832701) B107832701
theorem B95851289 : Blo 1969435 95851289 := bstep (se 2 (by rfl) ⟨35944233, by rfl⟩ : syracuseStep 95851289 = 71888467) B71888467
theorem B63900859 : Blo 1969435 63900859 := bstep (se 1 (by rfl) ⟨47925644, by rfl⟩ : syracuseStep 63900859 = 95851289) B95851289
theorem B85201145 : Blo 1969435 85201145 := bstep (se 2 (by rfl) ⟨31950429, by rfl⟩ : syracuseStep 85201145 = 63900859) B63900859
theorem B56800763 : Blo 1969435 56800763 := bstep (se 1 (by rfl) ⟨42600572, by rfl⟩ : syracuseStep 56800763 = 85201145) B85201145
theorem B37867175 : Blo 1969435 37867175 := bstep (se 1 (by rfl) ⟨28400381, by rfl⟩ : syracuseStep 37867175 = 56800763) B56800763
theorem B25244783 : Blo 1969435 25244783 := bstep (se 1 (by rfl) ⟨18933587, by rfl⟩ : syracuseStep 25244783 = 37867175) B37867175
theorem B16829855 : Blo 1969435 16829855 := bstep (se 1 (by rfl) ⟨12622391, by rfl⟩ : syracuseStep 16829855 = 25244783) B25244783
theorem B11219903 : Blo 1969435 11219903 := bstep (se 1 (by rfl) ⟨8414927, by rfl⟩ : syracuseStep 11219903 = 16829855) B16829855
theorem B7479935 : Blo 1969435 7479935 := bstep (se 1 (by rfl) ⟨5609951, by rfl⟩ : syracuseStep 7479935 = 11219903) B11219903
theorem B4986623 : Blo 1969435 4986623 := bstep (se 1 (by rfl) ⟨3739967, by rfl⟩ : syracuseStep 4986623 = 7479935) B7479935
theorem B3324415 : Blo 1969435 3324415 := bstep (se 1 (by rfl) ⟨2493311, by rfl⟩ : syracuseStep 3324415 = 4986623) B4986623
theorem B4432553 : Blo 1969435 4432553 := bstep (se 2 (by rfl) ⟨1662207, by rfl⟩ : syracuseStep 4432553 = 3324415) B3324415
theorem B2955035 : Blo 1969435 2955035 := bstep (se 1 (by rfl) ⟨2216276, by rfl⟩ : syracuseStep 2955035 = 4432553) B4432553
theorem B1970023 : Blo 1969435 1970023 := bstep (se 1 (by rfl) ⟨1477517, by rfl⟩ : syracuseStep 1970023 = 2955035) B2955035
theorem B2216281 : Blo 1969435 2216281 := bbase (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) (by norm_num)
theorem B2955041 : Blo 1969435 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B1970027 : Blo 1969435 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B5686517 : Blo 1969435 5686517 := bbase (se 5 (by rfl) ⟨266555, by rfl⟩ : syracuseStep 5686517 = 533111) (by norm_num)
theorem B3791011 : Blo 1969435 3791011 := bstep (se 1 (by rfl) ⟨2843258, by rfl⟩ : syracuseStep 3791011 = 5686517) B5686517
theorem B5054681 : Blo 1969435 5054681 := bstep (se 2 (by rfl) ⟨1895505, by rfl⟩ : syracuseStep 5054681 = 3791011) B3791011
theorem B13479149 : Blo 1969435 13479149 := bstep (se 3 (by rfl) ⟨2527340, by rfl⟩ : syracuseStep 13479149 = 5054681) B5054681
theorem B8986099 : Blo 1969435 8986099 := bstep (se 1 (by rfl) ⟨6739574, by rfl⟩ : syracuseStep 8986099 = 13479149) B13479149
theorem B11981465 : Blo 1969435 11981465 := bstep (se 2 (by rfl) ⟨4493049, by rfl⟩ : syracuseStep 11981465 = 8986099) B8986099
theorem B7987643 : Blo 1969435 7987643 := bstep (se 1 (by rfl) ⟨5990732, by rfl⟩ : syracuseStep 7987643 = 11981465) B11981465
theorem B5325095 : Blo 1969435 5325095 := bstep (se 1 (by rfl) ⟨3993821, by rfl⟩ : syracuseStep 5325095 = 7987643) B7987643
theorem B3550063 : Blo 1969435 3550063 := bstep (se 1 (by rfl) ⟨2662547, by rfl⟩ : syracuseStep 3550063 = 5325095) B5325095
theorem B4733417 : Blo 1969435 4733417 := bstep (se 2 (by rfl) ⟨1775031, by rfl⟩ : syracuseStep 4733417 = 3550063) B3550063
theorem B3155611 : Blo 1969435 3155611 := bstep (se 1 (by rfl) ⟨2366708, by rfl⟩ : syracuseStep 3155611 = 4733417) B4733417
theorem B4207481 : Blo 1969435 4207481 := bstep (se 2 (by rfl) ⟨1577805, by rfl⟩ : syracuseStep 4207481 = 3155611) B3155611
theorem B2804987 : Blo 1969435 2804987 := bstep (se 1 (by rfl) ⟨2103740, by rfl⟩ : syracuseStep 2804987 = 4207481) B4207481
theorem B7479965 : Blo 1969435 7479965 := bstep (se 3 (by rfl) ⟨1402493, by rfl⟩ : syracuseStep 7479965 = 2804987) B2804987
theorem B4986643 : Blo 1969435 4986643 := bstep (se 1 (by rfl) ⟨3739982, by rfl⟩ : syracuseStep 4986643 = 7479965) B7479965
theorem B6648857 : Blo 1969435 6648857 := bstep (se 2 (by rfl) ⟨2493321, by rfl⟩ : syracuseStep 6648857 = 4986643) B4986643
theorem B4432571 : Blo 1969435 4432571 := bstep (se 1 (by rfl) ⟨3324428, by rfl⟩ : syracuseStep 4432571 = 6648857) B6648857
theorem B2955047 : Blo 1969435 2955047 := bstep (se 1 (by rfl) ⟨2216285, by rfl⟩ : syracuseStep 2955047 = 4432571) B4432571
theorem B1970031 : Blo 1969435 1970031 := bstep (se 1 (by rfl) ⟨1477523, by rfl⟩ : syracuseStep 1970031 = 2955047) B2955047
theorem B2955053 : Blo 1969435 2955053 := bbase (se 3 (by rfl) ⟨554072, by rfl⟩ : syracuseStep 2955053 = 1108145) (by norm_num)
theorem B1970035 : Blo 1969435 1970035 := bstep (se 1 (by rfl) ⟨1477526, by rfl⟩ : syracuseStep 1970035 = 2955053) B2955053
theorem B4432589 : Blo 1969435 4432589 := bbase (se 3 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 4432589 = 1662221) (by norm_num)
theorem B2955059 : Blo 1969435 2955059 := bstep (se 1 (by rfl) ⟨2216294, by rfl⟩ : syracuseStep 2955059 = 4432589) B4432589
theorem B1970039 : Blo 1969435 1970039 := bstep (se 1 (by rfl) ⟨1477529, by rfl⟩ : syracuseStep 1970039 = 2955059) B2955059
theorem B2493337 : Blo 1969435 2493337 := bbase (se 2 (by rfl) ⟨935001, by rfl⟩ : syracuseStep 2493337 = 1870003) (by norm_num)
theorem B3324449 : Blo 1969435 3324449 := bstep (se 2 (by rfl) ⟨1246668, by rfl⟩ : syracuseStep 3324449 = 2493337) B2493337
theorem B2216299 : Blo 1969435 2216299 := bstep (se 1 (by rfl) ⟨1662224, by rfl⟩ : syracuseStep 2216299 = 3324449) B3324449
theorem B2955065 : Blo 1969435 2955065 := bstep (se 2 (by rfl) ⟨1108149, by rfl⟩ : syracuseStep 2955065 = 2216299) B2216299
theorem B1970043 : Blo 1969435 1970043 := bstep (se 1 (by rfl) ⟨1477532, by rfl⟩ : syracuseStep 1970043 = 2955065) B2955065
theorem B8415029 : Blo 1969435 8415029 := bbase (se 5 (by rfl) ⟨394454, by rfl⟩ : syracuseStep 8415029 = 788909) (by norm_num)
theorem B22440077 : Blo 1969435 22440077 := bstep (se 3 (by rfl) ⟨4207514, by rfl⟩ : syracuseStep 22440077 = 8415029) B8415029
theorem B14960051 : Blo 1969435 14960051 := bstep (se 1 (by rfl) ⟨11220038, by rfl⟩ : syracuseStep 14960051 = 22440077) B22440077
theorem B9973367 : Blo 1969435 9973367 := bstep (se 1 (by rfl) ⟨7480025, by rfl⟩ : syracuseStep 9973367 = 14960051) B14960051
theorem B6648911 : Blo 1969435 6648911 := bstep (se 1 (by rfl) ⟨4986683, by rfl⟩ : syracuseStep 6648911 = 9973367) B9973367
theorem B4432607 : Blo 1969435 4432607 := bstep (se 1 (by rfl) ⟨3324455, by rfl⟩ : syracuseStep 4432607 = 6648911) B6648911
theorem B2955071 : Blo 1969435 2955071 := bstep (se 1 (by rfl) ⟨2216303, by rfl⟩ : syracuseStep 2955071 = 4432607) B4432607
theorem B1970047 : Blo 1969435 1970047 := bstep (se 1 (by rfl) ⟨1477535, by rfl⟩ : syracuseStep 1970047 = 2955071) B2955071
theorem B2955077 : Blo 1969435 2955077 := bbase (se 4 (by rfl) ⟨277038, by rfl⟩ : syracuseStep 2955077 = 554077) (by norm_num)
theorem B1970051 : Blo 1969435 1970051 := bstep (se 1 (by rfl) ⟨1477538, by rfl⟩ : syracuseStep 1970051 = 2955077) B2955077
theorem B3324469 : Blo 1969435 3324469 := bbase (se 5 (by rfl) ⟨155834, by rfl⟩ : syracuseStep 3324469 = 311669) (by norm_num)
theorem B4432625 : Blo 1969435 4432625 := bstep (se 2 (by rfl) ⟨1662234, by rfl⟩ : syracuseStep 4432625 = 3324469) B3324469
theorem B2955083 : Blo 1969435 2955083 := bstep (se 1 (by rfl) ⟨2216312, by rfl⟩ : syracuseStep 2955083 = 4432625) B4432625
theorem B1970055 : Blo 1969435 1970055 := bstep (se 1 (by rfl) ⟨1477541, by rfl⟩ : syracuseStep 1970055 = 2955083) B2955083
theorem B2216317 : Blo 1969435 2216317 := bbase (se 3 (by rfl) ⟨415559, by rfl⟩ : syracuseStep 2216317 = 831119) (by norm_num)
theorem B2955089 : Blo 1969435 2955089 := bstep (se 2 (by rfl) ⟨1108158, by rfl⟩ : syracuseStep 2955089 = 2216317) B2216317
theorem B1970059 : Blo 1969435 1970059 := bstep (se 1 (by rfl) ⟨1477544, by rfl⟩ : syracuseStep 1970059 = 2955089) B2955089
theorem B6648965 : Blo 1969435 6648965 := bbase (se 4 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 6648965 = 1246681) (by norm_num)
theorem B4432643 : Blo 1969435 4432643 := bstep (se 1 (by rfl) ⟨3324482, by rfl⟩ : syracuseStep 4432643 = 6648965) B6648965
theorem B2955095 : Blo 1969435 2955095 := bstep (se 1 (by rfl) ⟨2216321, by rfl⟩ : syracuseStep 2955095 = 4432643) B4432643
theorem B1970063 : Blo 1969435 1970063 := bstep (se 1 (by rfl) ⟨1477547, by rfl⟩ : syracuseStep 1970063 = 2955095) B2955095
theorem B2955101 : Blo 1969435 2955101 := bbase (se 3 (by rfl) ⟨554081, by rfl⟩ : syracuseStep 2955101 = 1108163) (by norm_num)
theorem B1970067 : Blo 1969435 1970067 := bstep (se 1 (by rfl) ⟨1477550, by rfl⟩ : syracuseStep 1970067 = 2955101) B2955101
theorem B4432661 : Blo 1969435 4432661 := bbase (se 6 (by rfl) ⟨103890, by rfl⟩ : syracuseStep 4432661 = 207781) (by norm_num)
theorem B2955107 : Blo 1969435 2955107 := bstep (se 1 (by rfl) ⟨2216330, by rfl⟩ : syracuseStep 2955107 = 4432661) B4432661
theorem B1970071 : Blo 1969435 1970071 := bstep (se 1 (by rfl) ⟨1477553, by rfl⟩ : syracuseStep 1970071 = 2955107) B2955107
theorem B7480133 : Blo 1969435 7480133 := bbase (se 4 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 7480133 = 1402525) (by norm_num)
theorem B4986755 : Blo 1969435 4986755 := bstep (se 1 (by rfl) ⟨3740066, by rfl⟩ : syracuseStep 4986755 = 7480133) B7480133
theorem B3324503 : Blo 1969435 3324503 := bstep (se 1 (by rfl) ⟨2493377, by rfl⟩ : syracuseStep 3324503 = 4986755) B4986755
theorem B2216335 : Blo 1969435 2216335 := bstep (se 1 (by rfl) ⟨1662251, by rfl⟩ : syracuseStep 2216335 = 3324503) B3324503
theorem B2955113 : Blo 1969435 2955113 := bstep (se 2 (by rfl) ⟨1108167, by rfl⟩ : syracuseStep 2955113 = 2216335) B2216335
theorem B1970075 : Blo 1969435 1970075 := bstep (se 1 (by rfl) ⟨1477556, by rfl⟩ : syracuseStep 1970075 = 2955113) B2955113
theorem B10109605 : Blo 1969435 10109605 := bbase (se 4 (by rfl) ⟨947775, by rfl⟩ : syracuseStep 10109605 = 1895551) (by norm_num)
theorem B13479473 : Blo 1969435 13479473 := bstep (se 2 (by rfl) ⟨5054802, by rfl⟩ : syracuseStep 13479473 = 10109605) B10109605
theorem B8986315 : Blo 1969435 8986315 := bstep (se 1 (by rfl) ⟨6739736, by rfl⟩ : syracuseStep 8986315 = 13479473) B13479473
theorem B11981753 : Blo 1969435 11981753 := bstep (se 2 (by rfl) ⟨4493157, by rfl⟩ : syracuseStep 11981753 = 8986315) B8986315
theorem B7987835 : Blo 1969435 7987835 := bstep (se 1 (by rfl) ⟨5990876, by rfl⟩ : syracuseStep 7987835 = 11981753) B11981753
theorem B21300893 : Blo 1969435 21300893 := bstep (se 3 (by rfl) ⟨3993917, by rfl⟩ : syracuseStep 21300893 = 7987835) B7987835
theorem B14200595 : Blo 1969435 14200595 := bstep (se 1 (by rfl) ⟨10650446, by rfl⟩ : syracuseStep 14200595 = 21300893) B21300893
theorem B9467063 : Blo 1969435 9467063 := bstep (se 1 (by rfl) ⟨7100297, by rfl⟩ : syracuseStep 9467063 = 14200595) B14200595
theorem B6311375 : Blo 1969435 6311375 := bstep (se 1 (by rfl) ⟨4733531, by rfl⟩ : syracuseStep 6311375 = 9467063) B9467063
theorem B4207583 : Blo 1969435 4207583 := bstep (se 1 (by rfl) ⟨3155687, by rfl⟩ : syracuseStep 4207583 = 6311375) B6311375
theorem B11220221 : Blo 1969435 11220221 := bstep (se 3 (by rfl) ⟨2103791, by rfl⟩ : syracuseStep 11220221 = 4207583) B4207583
theorem B7480147 : Blo 1969435 7480147 := bstep (se 1 (by rfl) ⟨5610110, by rfl⟩ : syracuseStep 7480147 = 11220221) B11220221
theorem B9973529 : Blo 1969435 9973529 := bstep (se 2 (by rfl) ⟨3740073, by rfl⟩ : syracuseStep 9973529 = 7480147) B7480147
theorem B6649019 : Blo 1969435 6649019 := bstep (se 1 (by rfl) ⟨4986764, by rfl⟩ : syracuseStep 6649019 = 9973529) B9973529
theorem B4432679 : Blo 1969435 4432679 := bstep (se 1 (by rfl) ⟨3324509, by rfl⟩ : syracuseStep 4432679 = 6649019) B6649019
theorem B2955119 : Blo 1969435 2955119 := bstep (se 1 (by rfl) ⟨2216339, by rfl⟩ : syracuseStep 2955119 = 4432679) B4432679
theorem B1970079 : Blo 1969435 1970079 := bstep (se 1 (by rfl) ⟨1477559, by rfl⟩ : syracuseStep 1970079 = 2955119) B2955119
theorem B2955125 : Blo 1969435 2955125 := bbase (se 5 (by rfl) ⟨138521, by rfl⟩ : syracuseStep 2955125 = 277043) (by norm_num)
theorem B1970083 : Blo 1969435 1970083 := bstep (se 1 (by rfl) ⟨1477562, by rfl⟩ : syracuseStep 1970083 = 2955125) B2955125
theorem B3155701 : Blo 1969435 3155701 := bbase (se 5 (by rfl) ⟨147923, by rfl⟩ : syracuseStep 3155701 = 295847) (by norm_num)
theorem B4207601 : Blo 1969435 4207601 := bstep (se 2 (by rfl) ⟨1577850, by rfl⟩ : syracuseStep 4207601 = 3155701) B3155701
theorem B2805067 : Blo 1969435 2805067 := bstep (se 1 (by rfl) ⟨2103800, by rfl⟩ : syracuseStep 2805067 = 4207601) B4207601
theorem B3740089 : Blo 1969435 3740089 := bstep (se 2 (by rfl) ⟨1402533, by rfl⟩ : syracuseStep 3740089 = 2805067) B2805067
theorem B4986785 : Blo 1969435 4986785 := bstep (se 2 (by rfl) ⟨1870044, by rfl⟩ : syracuseStep 4986785 = 3740089) B3740089
theorem B3324523 : Blo 1969435 3324523 := bstep (se 1 (by rfl) ⟨2493392, by rfl⟩ : syracuseStep 3324523 = 4986785) B4986785
theorem B4432697 : Blo 1969435 4432697 := bstep (se 2 (by rfl) ⟨1662261, by rfl⟩ : syracuseStep 4432697 = 3324523) B3324523
theorem B2955131 : Blo 1969435 2955131 := bstep (se 1 (by rfl) ⟨2216348, by rfl⟩ : syracuseStep 2955131 = 4432697) B4432697
theorem B1970087 : Blo 1969435 1970087 := bstep (se 1 (by rfl) ⟨1477565, by rfl⟩ : syracuseStep 1970087 = 2955131) B2955131
theorem B2216353 : Blo 1969435 2216353 := bbase (se 2 (by rfl) ⟨831132, by rfl⟩ : syracuseStep 2216353 = 1662265) (by norm_num)
theorem B2955137 : Blo 1969435 2955137 := bstep (se 2 (by rfl) ⟨1108176, by rfl⟩ : syracuseStep 2955137 = 2216353) B2216353
theorem B1970091 : Blo 1969435 1970091 := bstep (se 1 (by rfl) ⟨1477568, by rfl⟩ : syracuseStep 1970091 = 2955137) B2955137
theorem B4986805 : Blo 1969435 4986805 := bbase (se 5 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 4986805 = 467513) (by norm_num)
theorem B6649073 : Blo 1969435 6649073 := bstep (se 2 (by rfl) ⟨2493402, by rfl⟩ : syracuseStep 6649073 = 4986805) B4986805
theorem B4432715 : Blo 1969435 4432715 := bstep (se 1 (by rfl) ⟨3324536, by rfl⟩ : syracuseStep 4432715 = 6649073) B6649073
theorem B2955143 : Blo 1969435 2955143 := bstep (se 1 (by rfl) ⟨2216357, by rfl⟩ : syracuseStep 2955143 = 4432715) B4432715
theorem B1970095 : Blo 1969435 1970095 := bstep (se 1 (by rfl) ⟨1477571, by rfl⟩ : syracuseStep 1970095 = 2955143) B2955143
theorem B2955149 : Blo 1969435 2955149 := bbase (se 3 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 2955149 = 1108181) (by norm_num)
theorem B1970099 : Blo 1969435 1970099 := bstep (se 1 (by rfl) ⟨1477574, by rfl⟩ : syracuseStep 1970099 = 2955149) B2955149
theorem B4432733 : Blo 1969435 4432733 := bbase (se 3 (by rfl) ⟨831137, by rfl⟩ : syracuseStep 4432733 = 1662275) (by norm_num)
theorem B2955155 : Blo 1969435 2955155 := bstep (se 1 (by rfl) ⟨2216366, by rfl⟩ : syracuseStep 2955155 = 4432733) B4432733
theorem B1970103 : Blo 1969435 1970103 := bstep (se 1 (by rfl) ⟨1477577, by rfl⟩ : syracuseStep 1970103 = 2955155) B2955155
theorem B3324557 : Blo 1969435 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B2216371 : Blo 1969435 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B2955161 : Blo 1969435 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B1970107 : Blo 1969435 1970107 := bstep (se 1 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 1970107 = 2955161) B2955161
theorem B6311477 : Blo 1969435 6311477 := bbase (se 5 (by rfl) ⟨295850, by rfl⟩ : syracuseStep 6311477 = 591701) (by norm_num)
theorem B16830605 : Blo 1969435 16830605 := bstep (se 3 (by rfl) ⟨3155738, by rfl⟩ : syracuseStep 16830605 = 6311477) B6311477
theorem B11220403 : Blo 1969435 11220403 := bstep (se 1 (by rfl) ⟨8415302, by rfl⟩ : syracuseStep 11220403 = 16830605) B16830605
theorem B14960537 : Blo 1969435 14960537 := bstep (se 2 (by rfl) ⟨5610201, by rfl⟩ : syracuseStep 14960537 = 11220403) B11220403
theorem B9973691 : Blo 1969435 9973691 := bstep (se 1 (by rfl) ⟨7480268, by rfl⟩ : syracuseStep 9973691 = 14960537) B14960537
theorem B6649127 : Blo 1969435 6649127 := bstep (se 1 (by rfl) ⟨4986845, by rfl⟩ : syracuseStep 6649127 = 9973691) B9973691
theorem B4432751 : Blo 1969435 4432751 := bstep (se 1 (by rfl) ⟨3324563, by rfl⟩ : syracuseStep 4432751 = 6649127) B6649127
theorem B2955167 : Blo 1969435 2955167 := bstep (se 1 (by rfl) ⟨2216375, by rfl⟩ : syracuseStep 2955167 = 4432751) B4432751
theorem B1970111 : Blo 1969435 1970111 := bstep (se 1 (by rfl) ⟨1477583, by rfl⟩ : syracuseStep 1970111 = 2955167) B2955167
theorem B2955173 : Blo 1969435 2955173 := bbase (se 4 (by rfl) ⟨277047, by rfl⟩ : syracuseStep 2955173 = 554095) (by norm_num)
theorem B1970115 : Blo 1969435 1970115 := bstep (se 1 (by rfl) ⟨1477586, by rfl⟩ : syracuseStep 1970115 = 2955173) B2955173
theorem B2493433 : Blo 1969435 2493433 := bbase (se 2 (by rfl) ⟨935037, by rfl⟩ : syracuseStep 2493433 = 1870075) (by norm_num)
theorem B3324577 : Blo 1969435 3324577 := bstep (se 2 (by rfl) ⟨1246716, by rfl⟩ : syracuseStep 3324577 = 2493433) B2493433
theorem B4432769 : Blo 1969435 4432769 := bstep (se 2 (by rfl) ⟨1662288, by rfl⟩ : syracuseStep 4432769 = 3324577) B3324577
theorem B2955179 : Blo 1969435 2955179 := bstep (se 1 (by rfl) ⟨2216384, by rfl⟩ : syracuseStep 2955179 = 4432769) B4432769
theorem B1970119 : Blo 1969435 1970119 := bstep (se 1 (by rfl) ⟨1477589, by rfl⟩ : syracuseStep 1970119 = 2955179) B2955179
theorem B2216389 : Blo 1969435 2216389 := bbase (se 4 (by rfl) ⟨207786, by rfl⟩ : syracuseStep 2216389 = 415573) (by norm_num)
theorem B2955185 : Blo 1969435 2955185 := bstep (se 2 (by rfl) ⟨1108194, by rfl⟩ : syracuseStep 2955185 = 2216389) B2216389
theorem B1970123 : Blo 1969435 1970123 := bstep (se 1 (by rfl) ⟨1477592, by rfl⟩ : syracuseStep 1970123 = 2955185) B2955185
theorem B3740165 : Blo 1969435 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B2493443 : Blo 1969435 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B6649181 : Blo 1969435 6649181 := bstep (se 3 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 6649181 = 2493443) B2493443
theorem B4432787 : Blo 1969435 4432787 := bstep (se 1 (by rfl) ⟨3324590, by rfl⟩ : syracuseStep 4432787 = 6649181) B6649181
theorem B2955191 : Blo 1969435 2955191 := bstep (se 1 (by rfl) ⟨2216393, by rfl⟩ : syracuseStep 2955191 = 4432787) B4432787
theorem B1970127 : Blo 1969435 1970127 := bstep (se 1 (by rfl) ⟨1477595, by rfl⟩ : syracuseStep 1970127 = 2955191) B2955191
theorem B2955197 : Blo 1969435 2955197 := bbase (se 3 (by rfl) ⟨554099, by rfl⟩ : syracuseStep 2955197 = 1108199) (by norm_num)
theorem B1970131 : Blo 1969435 1970131 := bstep (se 1 (by rfl) ⟨1477598, by rfl⟩ : syracuseStep 1970131 = 2955197) B2955197
theorem B4432805 : Blo 1969435 4432805 := bbase (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) (by norm_num)
theorem B2955203 : Blo 1969435 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B1970135 : Blo 1969435 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B4986917 : Blo 1969435 4986917 := bbase (se 4 (by rfl) ⟨467523, by rfl⟩ : syracuseStep 4986917 = 935047) (by norm_num)
theorem B3324611 : Blo 1969435 3324611 := bstep (se 1 (by rfl) ⟨2493458, by rfl⟩ : syracuseStep 3324611 = 4986917) B4986917
theorem B2216407 : Blo 1969435 2216407 := bstep (se 1 (by rfl) ⟨1662305, by rfl⟩ : syracuseStep 2216407 = 3324611) B3324611
theorem B2955209 : Blo 1969435 2955209 := bstep (se 2 (by rfl) ⟨1108203, by rfl⟩ : syracuseStep 2955209 = 2216407) B2216407
theorem B1970139 : Blo 1969435 1970139 := bstep (se 1 (by rfl) ⟨1477604, by rfl⟩ : syracuseStep 1970139 = 2955209) B2955209
theorem B5610293 : Blo 1969435 5610293 := bbase (se 5 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 5610293 = 525965) (by norm_num)
theorem B3740195 : Blo 1969435 3740195 := bstep (se 1 (by rfl) ⟨2805146, by rfl⟩ : syracuseStep 3740195 = 5610293) B5610293
theorem B9973853 : Blo 1969435 9973853 := bstep (se 3 (by rfl) ⟨1870097, by rfl⟩ : syracuseStep 9973853 = 3740195) B3740195
theorem B6649235 : Blo 1969435 6649235 := bstep (se 1 (by rfl) ⟨4986926, by rfl⟩ : syracuseStep 6649235 = 9973853) B9973853
theorem B4432823 : Blo 1969435 4432823 := bstep (se 1 (by rfl) ⟨3324617, by rfl⟩ : syracuseStep 4432823 = 6649235) B6649235
theorem B2955215 : Blo 1969435 2955215 := bstep (se 1 (by rfl) ⟨2216411, by rfl⟩ : syracuseStep 2955215 = 4432823) B4432823
theorem B1970143 : Blo 1969435 1970143 := bstep (se 1 (by rfl) ⟨1477607, by rfl⟩ : syracuseStep 1970143 = 2955215) B2955215
theorem B2955221 : Blo 1969435 2955221 := bbase (se 7 (by rfl) ⟨34631, by rfl⟩ : syracuseStep 2955221 = 69263) (by norm_num)
theorem B1970147 : Blo 1969435 1970147 := bstep (se 1 (by rfl) ⟨1477610, by rfl⟩ : syracuseStep 1970147 = 2955221) B2955221
theorem B7480421 : Blo 1969435 7480421 := bbase (se 4 (by rfl) ⟨701289, by rfl⟩ : syracuseStep 7480421 = 1402579) (by norm_num)
theorem B4986947 : Blo 1969435 4986947 := bstep (se 1 (by rfl) ⟨3740210, by rfl⟩ : syracuseStep 4986947 = 7480421) B7480421
theorem B3324631 : Blo 1969435 3324631 := bstep (se 1 (by rfl) ⟨2493473, by rfl⟩ : syracuseStep 3324631 = 4986947) B4986947
theorem B4432841 : Blo 1969435 4432841 := bstep (se 2 (by rfl) ⟨1662315, by rfl⟩ : syracuseStep 4432841 = 3324631) B3324631
theorem B2955227 : Blo 1969435 2955227 := bstep (se 1 (by rfl) ⟨2216420, by rfl⟩ : syracuseStep 2955227 = 4432841) B4432841
theorem B1970151 : Blo 1969435 1970151 := bstep (se 1 (by rfl) ⟨1477613, by rfl⟩ : syracuseStep 1970151 = 2955227) B2955227
theorem B2216425 : Blo 1969435 2216425 := bbase (se 2 (by rfl) ⟨831159, by rfl⟩ : syracuseStep 2216425 = 1662319) (by norm_num)
theorem B2955233 : Blo 1969435 2955233 := bstep (se 2 (by rfl) ⟨1108212, by rfl⟩ : syracuseStep 2955233 = 2216425) B2216425
theorem B1970155 : Blo 1969435 1970155 := bstep (se 1 (by rfl) ⟨1477616, by rfl⟩ : syracuseStep 1970155 = 2955233) B2955233
theorem B2103877 : Blo 1969435 2103877 := bbase (se 4 (by rfl) ⟨197238, by rfl⟩ : syracuseStep 2103877 = 394477) (by norm_num)
theorem B11220677 : Blo 1969435 11220677 := bstep (se 4 (by rfl) ⟨1051938, by rfl⟩ : syracuseStep 11220677 = 2103877) B2103877
theorem B7480451 : Blo 1969435 7480451 := bstep (se 1 (by rfl) ⟨5610338, by rfl⟩ : syracuseStep 7480451 = 11220677) B11220677
theorem B4986967 : Blo 1969435 4986967 := bstep (se 1 (by rfl) ⟨3740225, by rfl⟩ : syracuseStep 4986967 = 7480451) B7480451
theorem B6649289 : Blo 1969435 6649289 := bstep (se 2 (by rfl) ⟨2493483, by rfl⟩ : syracuseStep 6649289 = 4986967) B4986967
theorem B4432859 : Blo 1969435 4432859 := bstep (se 1 (by rfl) ⟨3324644, by rfl⟩ : syracuseStep 4432859 = 6649289) B6649289
theorem B2955239 : Blo 1969435 2955239 := bstep (se 1 (by rfl) ⟨2216429, by rfl⟩ : syracuseStep 2955239 = 4432859) B4432859
theorem B1970159 : Blo 1969435 1970159 := bstep (se 1 (by rfl) ⟨1477619, by rfl⟩ : syracuseStep 1970159 = 2955239) B2955239
theorem B2955245 : Blo 1969435 2955245 := bbase (se 3 (by rfl) ⟨554108, by rfl⟩ : syracuseStep 2955245 = 1108217) (by norm_num)
theorem B1970163 : Blo 1969435 1970163 := bstep (se 1 (by rfl) ⟨1477622, by rfl⟩ : syracuseStep 1970163 = 2955245) B2955245
theorem B4432877 : Blo 1969435 4432877 := bbase (se 3 (by rfl) ⟨831164, by rfl⟩ : syracuseStep 4432877 = 1662329) (by norm_num)
theorem B2955251 : Blo 1969435 2955251 := bstep (se 1 (by rfl) ⟨2216438, by rfl⟩ : syracuseStep 2955251 = 4432877) B4432877
theorem B1970167 : Blo 1969435 1970167 := bstep (se 1 (by rfl) ⟨1477625, by rfl⟩ : syracuseStep 1970167 = 2955251) B2955251
theorem B4207781 : Blo 1969435 4207781 := bbase (se 4 (by rfl) ⟨394479, by rfl⟩ : syracuseStep 4207781 = 788959) (by norm_num)
theorem B2805187 : Blo 1969435 2805187 := bstep (se 1 (by rfl) ⟨2103890, by rfl⟩ : syracuseStep 2805187 = 4207781) B4207781
theorem B3740249 : Blo 1969435 3740249 := bstep (se 2 (by rfl) ⟨1402593, by rfl⟩ : syracuseStep 3740249 = 2805187) B2805187
theorem B2493499 : Blo 1969435 2493499 := bstep (se 1 (by rfl) ⟨1870124, by rfl⟩ : syracuseStep 2493499 = 3740249) B3740249
theorem B3324665 : Blo 1969435 3324665 := bstep (se 2 (by rfl) ⟨1246749, by rfl⟩ : syracuseStep 3324665 = 2493499) B2493499
theorem B2216443 : Blo 1969435 2216443 := bstep (se 1 (by rfl) ⟨1662332, by rfl⟩ : syracuseStep 2216443 = 3324665) B3324665
theorem B2955257 : Blo 1969435 2955257 := bstep (se 2 (by rfl) ⟨1108221, by rfl⟩ : syracuseStep 2955257 = 2216443) B2216443
theorem B1970171 : Blo 1969435 1970171 := bstep (se 1 (by rfl) ⟨1477628, by rfl⟩ : syracuseStep 1970171 = 2955257) B2955257
theorem B9860341 : Blo 1969435 9860341 := bbase (se 5 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 9860341 = 924407) (by norm_num)
theorem B13147121 : Blo 1969435 13147121 := bstep (se 2 (by rfl) ⟨4930170, by rfl⟩ : syracuseStep 13147121 = 9860341) B9860341
theorem B35058989 : Blo 1969435 35058989 := bstep (se 3 (by rfl) ⟨6573560, by rfl⟩ : syracuseStep 35058989 = 13147121) B13147121
theorem B23372659 : Blo 1969435 23372659 := bstep (se 1 (by rfl) ⟨17529494, by rfl⟩ : syracuseStep 23372659 = 35058989) B35058989
theorem B31163545 : Blo 1969435 31163545 := bstep (se 2 (by rfl) ⟨11686329, by rfl⟩ : syracuseStep 31163545 = 23372659) B23372659
theorem B166205573 : Blo 1969435 166205573 := bstep (se 4 (by rfl) ⟨15581772, by rfl⟩ : syracuseStep 166205573 = 31163545) B31163545
theorem B110803715 : Blo 1969435 110803715 := bstep (se 1 (by rfl) ⟨83102786, by rfl⟩ : syracuseStep 110803715 = 166205573) B166205573
theorem B73869143 : Blo 1969435 73869143 := bstep (se 1 (by rfl) ⟨55401857, by rfl⟩ : syracuseStep 73869143 = 110803715) B110803715
theorem B196984381 : Blo 1969435 196984381 := bstep (se 3 (by rfl) ⟨36934571, by rfl⟩ : syracuseStep 196984381 = 73869143) B73869143
theorem B262645841 : Blo 1969435 262645841 := bstep (se 2 (by rfl) ⟨98492190, by rfl⟩ : syracuseStep 262645841 = 196984381) B196984381
theorem B175097227 : Blo 1969435 175097227 := bstep (se 1 (by rfl) ⟨131322920, by rfl⟩ : syracuseStep 175097227 = 262645841) B262645841
theorem B233462969 : Blo 1969435 233462969 := bstep (se 2 (by rfl) ⟨87548613, by rfl⟩ : syracuseStep 233462969 = 175097227) B175097227
theorem B155641979 : Blo 1969435 155641979 := bstep (se 1 (by rfl) ⟨116731484, by rfl⟩ : syracuseStep 155641979 = 233462969) B233462969
theorem B103761319 : Blo 1969435 103761319 := bstep (se 1 (by rfl) ⟨77820989, by rfl⟩ : syracuseStep 103761319 = 155641979) B155641979
theorem B138348425 : Blo 1969435 138348425 := bstep (se 2 (by rfl) ⟨51880659, by rfl⟩ : syracuseStep 138348425 = 103761319) B103761319
theorem B92232283 : Blo 1969435 92232283 := bstep (se 1 (by rfl) ⟨69174212, by rfl⟩ : syracuseStep 92232283 = 138348425) B138348425
theorem B122976377 : Blo 1969435 122976377 := bstep (se 2 (by rfl) ⟨46116141, by rfl⟩ : syracuseStep 122976377 = 92232283) B92232283
theorem B81984251 : Blo 1969435 81984251 := bstep (se 1 (by rfl) ⟨61488188, by rfl⟩ : syracuseStep 81984251 = 122976377) B122976377
theorem B54656167 : Blo 1969435 54656167 := bstep (se 1 (by rfl) ⟨40992125, by rfl⟩ : syracuseStep 54656167 = 81984251) B81984251
theorem B72874889 : Blo 1969435 72874889 := bstep (se 2 (by rfl) ⟨27328083, by rfl⟩ : syracuseStep 72874889 = 54656167) B54656167
theorem B48583259 : Blo 1969435 48583259 := bstep (se 1 (by rfl) ⟨36437444, by rfl⟩ : syracuseStep 48583259 = 72874889) B72874889
theorem B32388839 : Blo 1969435 32388839 := bstep (se 1 (by rfl) ⟨24291629, by rfl⟩ : syracuseStep 32388839 = 48583259) B48583259
theorem B21592559 : Blo 1969435 21592559 := bstep (se 1 (by rfl) ⟨16194419, by rfl⟩ : syracuseStep 21592559 = 32388839) B32388839
theorem B14395039 : Blo 1969435 14395039 := bstep (se 1 (by rfl) ⟨10796279, by rfl⟩ : syracuseStep 14395039 = 21592559) B21592559
theorem B76773541 : Blo 1969435 76773541 := bstep (se 4 (by rfl) ⟨7197519, by rfl⟩ : syracuseStep 76773541 = 14395039) B14395039
theorem B102364721 : Blo 1969435 102364721 := bstep (se 2 (by rfl) ⟨38386770, by rfl⟩ : syracuseStep 102364721 = 76773541) B76773541
theorem B68243147 : Blo 1969435 68243147 := bstep (se 1 (by rfl) ⟨51182360, by rfl⟩ : syracuseStep 68243147 = 102364721) B102364721
theorem B45495431 : Blo 1969435 45495431 := bstep (se 1 (by rfl) ⟨34121573, by rfl⟩ : syracuseStep 45495431 = 68243147) B68243147
theorem B30330287 : Blo 1969435 30330287 := bstep (se 1 (by rfl) ⟨22747715, by rfl⟩ : syracuseStep 30330287 = 45495431) B45495431
theorem B20220191 : Blo 1969435 20220191 := bstep (se 1 (by rfl) ⟨15165143, by rfl⟩ : syracuseStep 20220191 = 30330287) B30330287
theorem B13480127 : Blo 1969435 13480127 := bstep (se 1 (by rfl) ⟨10110095, by rfl⟩ : syracuseStep 13480127 = 20220191) B20220191
theorem B8986751 : Blo 1969435 8986751 := bstep (se 1 (by rfl) ⟨6740063, by rfl⟩ : syracuseStep 8986751 = 13480127) B13480127
theorem B5991167 : Blo 1969435 5991167 := bstep (se 1 (by rfl) ⟨4493375, by rfl⟩ : syracuseStep 5991167 = 8986751) B8986751
theorem B15976445 : Blo 1969435 15976445 := bstep (se 3 (by rfl) ⟨2995583, by rfl⟩ : syracuseStep 15976445 = 5991167) B5991167
theorem B170415413 : Blo 1969435 170415413 := bstep (se 5 (by rfl) ⟨7988222, by rfl⟩ : syracuseStep 170415413 = 15976445) B15976445
theorem B113610275 : Blo 1969435 113610275 := bstep (se 1 (by rfl) ⟨85207706, by rfl⟩ : syracuseStep 113610275 = 170415413) B170415413
theorem B75740183 : Blo 1969435 75740183 := bstep (se 1 (by rfl) ⟨56805137, by rfl⟩ : syracuseStep 75740183 = 113610275) B113610275
theorem B50493455 : Blo 1969435 50493455 := bstep (se 1 (by rfl) ⟨37870091, by rfl⟩ : syracuseStep 50493455 = 75740183) B75740183
theorem B33662303 : Blo 1969435 33662303 := bstep (se 1 (by rfl) ⟨25246727, by rfl⟩ : syracuseStep 33662303 = 50493455) B50493455
theorem B22441535 : Blo 1969435 22441535 := bstep (se 1 (by rfl) ⟨16831151, by rfl⟩ : syracuseStep 22441535 = 33662303) B33662303
theorem B14961023 : Blo 1969435 14961023 := bstep (se 1 (by rfl) ⟨11220767, by rfl⟩ : syracuseStep 14961023 = 22441535) B22441535
theorem B9974015 : Blo 1969435 9974015 := bstep (se 1 (by rfl) ⟨7480511, by rfl⟩ : syracuseStep 9974015 = 14961023) B14961023
theorem B6649343 : Blo 1969435 6649343 := bstep (se 1 (by rfl) ⟨4987007, by rfl⟩ : syracuseStep 6649343 = 9974015) B9974015
theorem B4432895 : Blo 1969435 4432895 := bstep (se 1 (by rfl) ⟨3324671, by rfl⟩ : syracuseStep 4432895 = 6649343) B6649343
theorem B2955263 : Blo 1969435 2955263 := bstep (se 1 (by rfl) ⟨2216447, by rfl⟩ : syracuseStep 2955263 = 4432895) B4432895
theorem B1970175 : Blo 1969435 1970175 := bstep (se 1 (by rfl) ⟨1477631, by rfl⟩ : syracuseStep 1970175 = 2955263) B2955263
theorem B2955269 : Blo 1969435 2955269 := bbase (se 4 (by rfl) ⟨277056, by rfl⟩ : syracuseStep 2955269 = 554113) (by norm_num)
theorem B1970179 : Blo 1969435 1970179 := bstep (se 1 (by rfl) ⟨1477634, by rfl⟩ : syracuseStep 1970179 = 2955269) B2955269
theorem B3324685 : Blo 1969435 3324685 := bbase (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) (by norm_num)
theorem B4432913 : Blo 1969435 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B2955275 : Blo 1969435 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B1970183 : Blo 1969435 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B2216461 : Blo 1969435 2216461 := bbase (se 3 (by rfl) ⟨415586, by rfl⟩ : syracuseStep 2216461 = 831173) (by norm_num)
theorem B2955281 : Blo 1969435 2955281 := bstep (se 2 (by rfl) ⟨1108230, by rfl⟩ : syracuseStep 2955281 = 2216461) B2216461
theorem B1970187 : Blo 1969435 1970187 := bstep (se 1 (by rfl) ⟨1477640, by rfl⟩ : syracuseStep 1970187 = 2955281) B2955281
theorem B6649397 : Blo 1969435 6649397 := bbase (se 5 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 6649397 = 623381) (by norm_num)
theorem B4432931 : Blo 1969435 4432931 := bstep (se 1 (by rfl) ⟨3324698, by rfl⟩ : syracuseStep 4432931 = 6649397) B6649397
theorem B2955287 : Blo 1969435 2955287 := bstep (se 1 (by rfl) ⟨2216465, by rfl⟩ : syracuseStep 2955287 = 4432931) B4432931
theorem B1970191 : Blo 1969435 1970191 := bstep (se 1 (by rfl) ⟨1477643, by rfl⟩ : syracuseStep 1970191 = 2955287) B2955287
theorem B2955293 : Blo 1969435 2955293 := bbase (se 3 (by rfl) ⟨554117, by rfl⟩ : syracuseStep 2955293 = 1108235) (by norm_num)
theorem B1970195 : Blo 1969435 1970195 := bstep (se 1 (by rfl) ⟨1477646, by rfl⟩ : syracuseStep 1970195 = 2955293) B2955293
theorem B4432949 : Blo 1969435 4432949 := bbase (se 5 (by rfl) ⟨207794, by rfl⟩ : syracuseStep 4432949 = 415589) (by norm_num)
theorem B2955299 : Blo 1969435 2955299 := bstep (se 1 (by rfl) ⟨2216474, by rfl⟩ : syracuseStep 2955299 = 4432949) B4432949
theorem B1970199 : Blo 1969435 1970199 := bstep (se 1 (by rfl) ⟨1477649, by rfl⟩ : syracuseStep 1970199 = 2955299) B2955299
theorem B3550373 : Blo 1969435 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B2366915 : Blo 1969435 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B6311773 : Blo 1969435 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B8415697 : Blo 1969435 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B11220929 : Blo 1969435 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B7480619 : Blo 1969435 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B4987079 : Blo 1969435 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B3324719 : Blo 1969435 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B2216479 : Blo 1969435 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B2955305 : Blo 1969435 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B1970203 : Blo 1969435 1970203 := bstep (se 1 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 1970203 = 2955305) B2955305
theorem B2246725 : Blo 1969435 2246725 := bbase (se 4 (by rfl) ⟨210630, by rfl⟩ : syracuseStep 2246725 = 421261) (by norm_num)
theorem B2995633 : Blo 1969435 2995633 := bstep (se 2 (by rfl) ⟨1123362, by rfl⟩ : syracuseStep 2995633 = 2246725) B2246725
theorem B15976709 : Blo 1969435 15976709 := bstep (se 4 (by rfl) ⟨1497816, by rfl⟩ : syracuseStep 15976709 = 2995633) B2995633
theorem B10651139 : Blo 1969435 10651139 := bstep (se 1 (by rfl) ⟨7988354, by rfl⟩ : syracuseStep 10651139 = 15976709) B15976709
theorem B7100759 : Blo 1969435 7100759 := bstep (se 1 (by rfl) ⟨5325569, by rfl⟩ : syracuseStep 7100759 = 10651139) B10651139
theorem B4733839 : Blo 1969435 4733839 := bstep (se 1 (by rfl) ⟨3550379, by rfl⟩ : syracuseStep 4733839 = 7100759) B7100759
theorem B6311785 : Blo 1969435 6311785 := bstep (se 2 (by rfl) ⟨2366919, by rfl⟩ : syracuseStep 6311785 = 4733839) B4733839
theorem B8415713 : Blo 1969435 8415713 := bstep (se 2 (by rfl) ⟨3155892, by rfl⟩ : syracuseStep 8415713 = 6311785) B6311785
theorem B5610475 : Blo 1969435 5610475 := bstep (se 1 (by rfl) ⟨4207856, by rfl⟩ : syracuseStep 5610475 = 8415713) B8415713
theorem B7480633 : Blo 1969435 7480633 := bstep (se 2 (by rfl) ⟨2805237, by rfl⟩ : syracuseStep 7480633 = 5610475) B5610475
theorem B9974177 : Blo 1969435 9974177 := bstep (se 2 (by rfl) ⟨3740316, by rfl⟩ : syracuseStep 9974177 = 7480633) B7480633
theorem B6649451 : Blo 1969435 6649451 := bstep (se 1 (by rfl) ⟨4987088, by rfl⟩ : syracuseStep 6649451 = 9974177) B9974177
theorem B4432967 : Blo 1969435 4432967 := bstep (se 1 (by rfl) ⟨3324725, by rfl⟩ : syracuseStep 4432967 = 6649451) B6649451
theorem B2955311 : Blo 1969435 2955311 := bstep (se 1 (by rfl) ⟨2216483, by rfl⟩ : syracuseStep 2955311 = 4432967) B4432967
theorem B1970207 : Blo 1969435 1970207 := bstep (se 1 (by rfl) ⟨1477655, by rfl⟩ : syracuseStep 1970207 = 2955311) B2955311
theorem B2955317 : Blo 1969435 2955317 := bbase (se 5 (by rfl) ⟨138530, by rfl⟩ : syracuseStep 2955317 = 277061) (by norm_num)
theorem B1970211 : Blo 1969435 1970211 := bstep (se 1 (by rfl) ⟨1477658, by rfl⟩ : syracuseStep 1970211 = 2955317) B2955317
theorem B4987109 : Blo 1969435 4987109 := bbase (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) (by norm_num)
theorem B3324739 : Blo 1969435 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B4432985 : Blo 1969435 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B2955323 : Blo 1969435 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B1970215 : Blo 1969435 1970215 := bstep (se 1 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 1970215 = 2955323) B2955323
theorem B2216497 : Blo 1969435 2216497 := bbase (se 2 (by rfl) ⟨831186, by rfl⟩ : syracuseStep 2216497 = 1662373) (by norm_num)
theorem B2955329 : Blo 1969435 2955329 := bstep (se 2 (by rfl) ⟨1108248, by rfl⟩ : syracuseStep 2955329 = 2216497) B2216497
theorem B1970219 : Blo 1969435 1970219 := bstep (se 1 (by rfl) ⟨1477664, by rfl⟩ : syracuseStep 1970219 = 2955329) B2955329
theorem B5991317 : Blo 1969435 5991317 := bbase (se 6 (by rfl) ⟨140421, by rfl⟩ : syracuseStep 5991317 = 280843) (by norm_num)
theorem B3994211 : Blo 1969435 3994211 := bstep (se 1 (by rfl) ⟨2995658, by rfl⟩ : syracuseStep 3994211 = 5991317) B5991317
theorem B2662807 : Blo 1969435 2662807 := bstep (se 1 (by rfl) ⟨1997105, by rfl⟩ : syracuseStep 2662807 = 3994211) B3994211
theorem B3550409 : Blo 1969435 3550409 := bstep (se 2 (by rfl) ⟨1331403, by rfl⟩ : syracuseStep 3550409 = 2662807) B2662807
theorem B2366939 : Blo 1969435 2366939 := bstep (se 1 (by rfl) ⟨1775204, by rfl⟩ : syracuseStep 2366939 = 3550409) B3550409
theorem B6311837 : Blo 1969435 6311837 := bstep (se 3 (by rfl) ⟨1183469, by rfl⟩ : syracuseStep 6311837 = 2366939) B2366939
theorem B4207891 : Blo 1969435 4207891 := bstep (se 1 (by rfl) ⟨3155918, by rfl⟩ : syracuseStep 4207891 = 6311837) B6311837
theorem B5610521 : Blo 1969435 5610521 := bstep (se 2 (by rfl) ⟨2103945, by rfl⟩ : syracuseStep 5610521 = 4207891) B4207891
theorem B3740347 : Blo 1969435 3740347 := bstep (se 1 (by rfl) ⟨2805260, by rfl⟩ : syracuseStep 3740347 = 5610521) B5610521
theorem B4987129 : Blo 1969435 4987129 := bstep (se 2 (by rfl) ⟨1870173, by rfl⟩ : syracuseStep 4987129 = 3740347) B3740347
theorem B6649505 : Blo 1969435 6649505 := bstep (se 2 (by rfl) ⟨2493564, by rfl⟩ : syracuseStep 6649505 = 4987129) B4987129
theorem B4433003 : Blo 1969435 4433003 := bstep (se 1 (by rfl) ⟨3324752, by rfl⟩ : syracuseStep 4433003 = 6649505) B6649505
theorem B2955335 : Blo 1969435 2955335 := bstep (se 1 (by rfl) ⟨2216501, by rfl⟩ : syracuseStep 2955335 = 4433003) B4433003
theorem B1970223 : Blo 1969435 1970223 := bstep (se 1 (by rfl) ⟨1477667, by rfl⟩ : syracuseStep 1970223 = 2955335) B2955335
theorem B2955341 : Blo 1969435 2955341 := bbase (se 3 (by rfl) ⟨554126, by rfl⟩ : syracuseStep 2955341 = 1108253) (by norm_num)
theorem B1970227 : Blo 1969435 1970227 := bstep (se 1 (by rfl) ⟨1477670, by rfl⟩ : syracuseStep 1970227 = 2955341) B2955341
theorem B4433021 : Blo 1969435 4433021 := bbase (se 3 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 4433021 = 1662383) (by norm_num)
theorem B2955347 : Blo 1969435 2955347 := bstep (se 1 (by rfl) ⟨2216510, by rfl⟩ : syracuseStep 2955347 = 4433021) B4433021
theorem B1970231 : Blo 1969435 1970231 := bstep (se 1 (by rfl) ⟨1477673, by rfl⟩ : syracuseStep 1970231 = 2955347) B2955347
theorem B3324773 : Blo 1969435 3324773 := bbase (se 4 (by rfl) ⟨311697, by rfl⟩ : syracuseStep 3324773 = 623395) (by norm_num)
theorem B2216515 : Blo 1969435 2216515 := bstep (se 1 (by rfl) ⟨1662386, by rfl⟩ : syracuseStep 2216515 = 3324773) B3324773
theorem B2955353 : Blo 1969435 2955353 := bstep (se 2 (by rfl) ⟨1108257, by rfl⟩ : syracuseStep 2955353 = 2216515) B2216515
theorem B1970235 : Blo 1969435 1970235 := bstep (se 1 (by rfl) ⟨1477676, by rfl⟩ : syracuseStep 1970235 = 2955353) B2955353
theorem B4207925 : Blo 1969435 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B2805283 : Blo 1969435 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B14961509 : Blo 1969435 14961509 := bstep (se 4 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 14961509 = 2805283) B2805283
theorem B9974339 : Blo 1969435 9974339 := bstep (se 1 (by rfl) ⟨7480754, by rfl⟩ : syracuseStep 9974339 = 14961509) B14961509
theorem B6649559 : Blo 1969435 6649559 := bstep (se 1 (by rfl) ⟨4987169, by rfl⟩ : syracuseStep 6649559 = 9974339) B9974339
theorem B4433039 : Blo 1969435 4433039 := bstep (se 1 (by rfl) ⟨3324779, by rfl⟩ : syracuseStep 4433039 = 6649559) B6649559
theorem B2955359 : Blo 1969435 2955359 := bstep (se 1 (by rfl) ⟨2216519, by rfl⟩ : syracuseStep 2955359 = 4433039) B4433039
theorem B1970239 : Blo 1969435 1970239 := bstep (se 1 (by rfl) ⟨1477679, by rfl⟩ : syracuseStep 1970239 = 2955359) B2955359
theorem B2955365 : Blo 1969435 2955365 := bbase (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) (by norm_num)
theorem B1970243 : Blo 1969435 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B7582853 : Blo 1969435 7582853 := bbase (se 4 (by rfl) ⟨710892, by rfl⟩ : syracuseStep 7582853 = 1421785) (by norm_num)
theorem B20220941 : Blo 1969435 20220941 := bstep (se 3 (by rfl) ⟨3791426, by rfl⟩ : syracuseStep 20220941 = 7582853) B7582853
theorem B13480627 : Blo 1969435 13480627 := bstep (se 1 (by rfl) ⟨10110470, by rfl⟩ : syracuseStep 13480627 = 20220941) B20220941
theorem B17974169 : Blo 1969435 17974169 := bstep (se 2 (by rfl) ⟨6740313, by rfl⟩ : syracuseStep 17974169 = 13480627) B13480627
theorem B11982779 : Blo 1969435 11982779 := bstep (se 1 (by rfl) ⟨8987084, by rfl⟩ : syracuseStep 11982779 = 17974169) B17974169
theorem B7988519 : Blo 1969435 7988519 := bstep (se 1 (by rfl) ⟨5991389, by rfl⟩ : syracuseStep 7988519 = 11982779) B11982779
theorem B5325679 : Blo 1969435 5325679 := bstep (se 1 (by rfl) ⟨3994259, by rfl⟩ : syracuseStep 5325679 = 7988519) B7988519
theorem B7100905 : Blo 1969435 7100905 := bstep (se 2 (by rfl) ⟨2662839, by rfl⟩ : syracuseStep 7100905 = 5325679) B5325679
theorem B9467873 : Blo 1969435 9467873 := bstep (se 2 (by rfl) ⟨3550452, by rfl⟩ : syracuseStep 9467873 = 7100905) B7100905
theorem B6311915 : Blo 1969435 6311915 := bstep (se 1 (by rfl) ⟨4733936, by rfl⟩ : syracuseStep 6311915 = 9467873) B9467873
theorem B4207943 : Blo 1969435 4207943 := bstep (se 1 (by rfl) ⟨3155957, by rfl⟩ : syracuseStep 4207943 = 6311915) B6311915
theorem B2805295 : Blo 1969435 2805295 := bstep (se 1 (by rfl) ⟨2103971, by rfl⟩ : syracuseStep 2805295 = 4207943) B4207943
theorem B3740393 : Blo 1969435 3740393 := bstep (se 2 (by rfl) ⟨1402647, by rfl⟩ : syracuseStep 3740393 = 2805295) B2805295
theorem B2493595 : Blo 1969435 2493595 := bstep (se 1 (by rfl) ⟨1870196, by rfl⟩ : syracuseStep 2493595 = 3740393) B3740393
theorem B3324793 : Blo 1969435 3324793 := bstep (se 2 (by rfl) ⟨1246797, by rfl⟩ : syracuseStep 3324793 = 2493595) B2493595
theorem B4433057 : Blo 1969435 4433057 := bstep (se 2 (by rfl) ⟨1662396, by rfl⟩ : syracuseStep 4433057 = 3324793) B3324793
theorem B2955371 : Blo 1969435 2955371 := bstep (se 1 (by rfl) ⟨2216528, by rfl⟩ : syracuseStep 2955371 = 4433057) B4433057
theorem B1970247 : Blo 1969435 1970247 := bstep (se 1 (by rfl) ⟨1477685, by rfl⟩ : syracuseStep 1970247 = 2955371) B2955371
theorem B2216533 : Blo 1969435 2216533 := bbase (se 8 (by rfl) ⟨12987, by rfl⟩ : syracuseStep 2216533 = 25975) (by norm_num)
theorem B2955377 : Blo 1969435 2955377 := bstep (se 2 (by rfl) ⟨1108266, by rfl⟩ : syracuseStep 2955377 = 2216533) B2216533
theorem B1970251 : Blo 1969435 1970251 := bstep (se 1 (by rfl) ⟨1477688, by rfl⟩ : syracuseStep 1970251 = 2955377) B2955377
theorem B2493605 : Blo 1969435 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B6649613 : Blo 1969435 6649613 := bstep (se 3 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 6649613 = 2493605) B2493605
theorem B4433075 : Blo 1969435 4433075 := bstep (se 1 (by rfl) ⟨3324806, by rfl⟩ : syracuseStep 4433075 = 6649613) B6649613
theorem B2955383 : Blo 1969435 2955383 := bstep (se 1 (by rfl) ⟨2216537, by rfl⟩ : syracuseStep 2955383 = 4433075) B4433075
theorem B1970255 : Blo 1969435 1970255 := bstep (se 1 (by rfl) ⟨1477691, by rfl⟩ : syracuseStep 1970255 = 2955383) B2955383
theorem B2955389 : Blo 1969435 2955389 := bbase (se 3 (by rfl) ⟨554135, by rfl⟩ : syracuseStep 2955389 = 1108271) (by norm_num)
theorem B1970259 : Blo 1969435 1970259 := bstep (se 1 (by rfl) ⟨1477694, by rfl⟩ : syracuseStep 1970259 = 2955389) B2955389
theorem B4433093 : Blo 1969435 4433093 := bbase (se 4 (by rfl) ⟨415602, by rfl⟩ : syracuseStep 4433093 = 831205) (by norm_num)
theorem B2955395 : Blo 1969435 2955395 := bstep (se 1 (by rfl) ⟨2216546, by rfl⟩ : syracuseStep 2955395 = 4433093) B4433093
theorem B1970263 : Blo 1969435 1970263 := bstep (se 1 (by rfl) ⟨1477697, by rfl⟩ : syracuseStep 1970263 = 2955395) B2955395
theorem B12623957 : Blo 1969435 12623957 := bbase (se 8 (by rfl) ⟨73968, by rfl⟩ : syracuseStep 12623957 = 147937) (by norm_num)
theorem B8415971 : Blo 1969435 8415971 := bstep (se 1 (by rfl) ⟨6311978, by rfl⟩ : syracuseStep 8415971 = 12623957) B12623957
theorem B5610647 : Blo 1969435 5610647 := bstep (se 1 (by rfl) ⟨4207985, by rfl⟩ : syracuseStep 5610647 = 8415971) B8415971
theorem B3740431 : Blo 1969435 3740431 := bstep (se 1 (by rfl) ⟨2805323, by rfl⟩ : syracuseStep 3740431 = 5610647) B5610647
theorem B4987241 : Blo 1969435 4987241 := bstep (se 2 (by rfl) ⟨1870215, by rfl⟩ : syracuseStep 4987241 = 3740431) B3740431
theorem B3324827 : Blo 1969435 3324827 := bstep (se 1 (by rfl) ⟨2493620, by rfl⟩ : syracuseStep 3324827 = 4987241) B4987241
theorem B2216551 : Blo 1969435 2216551 := bstep (se 1 (by rfl) ⟨1662413, by rfl⟩ : syracuseStep 2216551 = 3324827) B3324827
theorem B2955401 : Blo 1969435 2955401 := bstep (se 2 (by rfl) ⟨1108275, by rfl⟩ : syracuseStep 2955401 = 2216551) B2216551
theorem B1970267 : Blo 1969435 1970267 := bstep (se 1 (by rfl) ⟨1477700, by rfl⟩ : syracuseStep 1970267 = 2955401) B2955401
theorem B9974501 : Blo 1969435 9974501 := bbase (se 4 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 9974501 = 1870219) (by norm_num)
theorem B6649667 : Blo 1969435 6649667 := bstep (se 1 (by rfl) ⟨4987250, by rfl⟩ : syracuseStep 6649667 = 9974501) B9974501
theorem B4433111 : Blo 1969435 4433111 := bstep (se 1 (by rfl) ⟨3324833, by rfl⟩ : syracuseStep 4433111 = 6649667) B6649667
theorem B2955407 : Blo 1969435 2955407 := bstep (se 1 (by rfl) ⟨2216555, by rfl⟩ : syracuseStep 2955407 = 4433111) B4433111
theorem B1970271 : Blo 1969435 1970271 := bstep (se 1 (by rfl) ⟨1477703, by rfl⟩ : syracuseStep 1970271 = 2955407) B2955407
theorem B2955413 : Blo 1969435 2955413 := bbase (se 6 (by rfl) ⟨69267, by rfl⟩ : syracuseStep 2955413 = 138535) (by norm_num)
theorem B1970275 : Blo 1969435 1970275 := bstep (se 1 (by rfl) ⟨1477706, by rfl⟩ : syracuseStep 1970275 = 2955413) B2955413
theorem B8416021 : Blo 1969435 8416021 := bbase (se 6 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 8416021 = 394501) (by norm_num)
theorem B11221361 : Blo 1969435 11221361 := bstep (se 2 (by rfl) ⟨4208010, by rfl⟩ : syracuseStep 11221361 = 8416021) B8416021
theorem B7480907 : Blo 1969435 7480907 := bstep (se 1 (by rfl) ⟨5610680, by rfl⟩ : syracuseStep 7480907 = 11221361) B11221361
theorem B4987271 : Blo 1969435 4987271 := bstep (se 1 (by rfl) ⟨3740453, by rfl⟩ : syracuseStep 4987271 = 7480907) B7480907
theorem B3324847 : Blo 1969435 3324847 := bstep (se 1 (by rfl) ⟨2493635, by rfl⟩ : syracuseStep 3324847 = 4987271) B4987271
theorem B4433129 : Blo 1969435 4433129 := bstep (se 2 (by rfl) ⟨1662423, by rfl⟩ : syracuseStep 4433129 = 3324847) B3324847
theorem B2955419 : Blo 1969435 2955419 := bstep (se 1 (by rfl) ⟨2216564, by rfl⟩ : syracuseStep 2955419 = 4433129) B4433129
theorem B1970279 : Blo 1969435 1970279 := bstep (se 1 (by rfl) ⟨1477709, by rfl⟩ : syracuseStep 1970279 = 2955419) B2955419
theorem B2216569 : Blo 1969435 2216569 := bbase (se 2 (by rfl) ⟨831213, by rfl⟩ : syracuseStep 2216569 = 1662427) (by norm_num)
theorem B2955425 : Blo 1969435 2955425 := bstep (se 2 (by rfl) ⟨1108284, by rfl⟩ : syracuseStep 2955425 = 2216569) B2216569
theorem B1970283 : Blo 1969435 1970283 := bstep (se 1 (by rfl) ⟨1477712, by rfl⟩ : syracuseStep 1970283 = 2955425) B2955425
theorem B5991509 : Blo 1969435 5991509 := bbase (se 8 (by rfl) ⟨35106, by rfl⟩ : syracuseStep 5991509 = 70213) (by norm_num)
theorem B15977357 : Blo 1969435 15977357 := bstep (se 3 (by rfl) ⟨2995754, by rfl⟩ : syracuseStep 15977357 = 5991509) B5991509
theorem B10651571 : Blo 1969435 10651571 := bstep (se 1 (by rfl) ⟨7988678, by rfl⟩ : syracuseStep 10651571 = 15977357) B15977357
theorem B7101047 : Blo 1969435 7101047 := bstep (se 1 (by rfl) ⟨5325785, by rfl⟩ : syracuseStep 7101047 = 10651571) B10651571
theorem B18936125 : Blo 1969435 18936125 := bstep (se 3 (by rfl) ⟨3550523, by rfl⟩ : syracuseStep 18936125 = 7101047) B7101047
theorem B12624083 : Blo 1969435 12624083 := bstep (se 1 (by rfl) ⟨9468062, by rfl⟩ : syracuseStep 12624083 = 18936125) B18936125
theorem B8416055 : Blo 1969435 8416055 := bstep (se 1 (by rfl) ⟨6312041, by rfl⟩ : syracuseStep 8416055 = 12624083) B12624083
theorem B5610703 : Blo 1969435 5610703 := bstep (se 1 (by rfl) ⟨4208027, by rfl⟩ : syracuseStep 5610703 = 8416055) B8416055
theorem B7480937 : Blo 1969435 7480937 := bstep (se 2 (by rfl) ⟨2805351, by rfl⟩ : syracuseStep 7480937 = 5610703) B5610703
theorem B4987291 : Blo 1969435 4987291 := bstep (se 1 (by rfl) ⟨3740468, by rfl⟩ : syracuseStep 4987291 = 7480937) B7480937
theorem B6649721 : Blo 1969435 6649721 := bstep (se 2 (by rfl) ⟨2493645, by rfl⟩ : syracuseStep 6649721 = 4987291) B4987291
theorem B4433147 : Blo 1969435 4433147 := bstep (se 1 (by rfl) ⟨3324860, by rfl⟩ : syracuseStep 4433147 = 6649721) B6649721
theorem B2955431 : Blo 1969435 2955431 := bstep (se 1 (by rfl) ⟨2216573, by rfl⟩ : syracuseStep 2955431 = 4433147) B4433147
theorem B1970287 : Blo 1969435 1970287 := bstep (se 1 (by rfl) ⟨1477715, by rfl⟩ : syracuseStep 1970287 = 2955431) B2955431
theorem B2955437 : Blo 1969435 2955437 := bbase (se 3 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 2955437 = 1108289) (by norm_num)
theorem B1970291 : Blo 1969435 1970291 := bstep (se 1 (by rfl) ⟨1477718, by rfl⟩ : syracuseStep 1970291 = 2955437) B2955437
theorem B4433165 : Blo 1969435 4433165 := bbase (se 3 (by rfl) ⟨831218, by rfl⟩ : syracuseStep 4433165 = 1662437) (by norm_num)
theorem B2955443 : Blo 1969435 2955443 := bstep (se 1 (by rfl) ⟨2216582, by rfl⟩ : syracuseStep 2955443 = 4433165) B4433165
theorem B1970295 : Blo 1969435 1970295 := bstep (se 1 (by rfl) ⟨1477721, by rfl⟩ : syracuseStep 1970295 = 2955443) B2955443
theorem B2493661 : Blo 1969435 2493661 := bbase (se 3 (by rfl) ⟨467561, by rfl⟩ : syracuseStep 2493661 = 935123) (by norm_num)
theorem B3324881 : Blo 1969435 3324881 := bstep (se 2 (by rfl) ⟨1246830, by rfl⟩ : syracuseStep 3324881 = 2493661) B2493661
theorem B2216587 : Blo 1969435 2216587 := bstep (se 1 (by rfl) ⟨1662440, by rfl⟩ : syracuseStep 2216587 = 3324881) B3324881
theorem B2955449 : Blo 1969435 2955449 := bstep (se 2 (by rfl) ⟨1108293, by rfl⟩ : syracuseStep 2955449 = 2216587) B2216587
theorem B1970299 : Blo 1969435 1970299 := bstep (se 1 (by rfl) ⟨1477724, by rfl⟩ : syracuseStep 1970299 = 2955449) B2955449
theorem B16832245 : Blo 1969435 16832245 := bbase (se 5 (by rfl) ⟨789011, by rfl⟩ : syracuseStep 16832245 = 1578023) (by norm_num)
theorem B22442993 : Blo 1969435 22442993 := bstep (se 2 (by rfl) ⟨8416122, by rfl⟩ : syracuseStep 22442993 = 16832245) B16832245
theorem B14961995 : Blo 1969435 14961995 := bstep (se 1 (by rfl) ⟨11221496, by rfl⟩ : syracuseStep 14961995 = 22442993) B22442993
theorem B9974663 : Blo 1969435 9974663 := bstep (se 1 (by rfl) ⟨7480997, by rfl⟩ : syracuseStep 9974663 = 14961995) B14961995
theorem B6649775 : Blo 1969435 6649775 := bstep (se 1 (by rfl) ⟨4987331, by rfl⟩ : syracuseStep 6649775 = 9974663) B9974663
theorem B4433183 : Blo 1969435 4433183 := bstep (se 1 (by rfl) ⟨3324887, by rfl⟩ : syracuseStep 4433183 = 6649775) B6649775
theorem B2955455 : Blo 1969435 2955455 := bstep (se 1 (by rfl) ⟨2216591, by rfl⟩ : syracuseStep 2955455 = 4433183) B4433183
theorem B1970303 : Blo 1969435 1970303 := bstep (se 1 (by rfl) ⟨1477727, by rfl⟩ : syracuseStep 1970303 = 2955455) B2955455
theorem B2955461 : Blo 1969435 2955461 := bbase (se 4 (by rfl) ⟨277074, by rfl⟩ : syracuseStep 2955461 = 554149) (by norm_num)
theorem B1970307 : Blo 1969435 1970307 := bstep (se 1 (by rfl) ⟨1477730, by rfl⟩ : syracuseStep 1970307 = 2955461) B2955461
theorem B3324901 : Blo 1969435 3324901 := bbase (se 4 (by rfl) ⟨311709, by rfl⟩ : syracuseStep 3324901 = 623419) (by norm_num)
theorem B4433201 : Blo 1969435 4433201 := bstep (se 2 (by rfl) ⟨1662450, by rfl⟩ : syracuseStep 4433201 = 3324901) B3324901
theorem B2955467 : Blo 1969435 2955467 := bstep (se 1 (by rfl) ⟨2216600, by rfl⟩ : syracuseStep 2955467 = 4433201) B4433201
theorem B1970311 : Blo 1969435 1970311 := bstep (se 1 (by rfl) ⟨1477733, by rfl⟩ : syracuseStep 1970311 = 2955467) B2955467
theorem B2216605 : Blo 1969435 2216605 := bbase (se 3 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 2216605 = 831227) (by norm_num)
theorem B2955473 : Blo 1969435 2955473 := bstep (se 2 (by rfl) ⟨1108302, by rfl⟩ : syracuseStep 2955473 = 2216605) B2216605
theorem B1970315 : Blo 1969435 1970315 := bstep (se 1 (by rfl) ⟨1477736, by rfl⟩ : syracuseStep 1970315 = 2955473) B2955473
theorem B6649829 : Blo 1969435 6649829 := bbase (se 4 (by rfl) ⟨623421, by rfl⟩ : syracuseStep 6649829 = 1246843) (by norm_num)
theorem B4433219 : Blo 1969435 4433219 := bstep (se 1 (by rfl) ⟨3324914, by rfl⟩ : syracuseStep 4433219 = 6649829) B6649829
theorem B2955479 : Blo 1969435 2955479 := bstep (se 1 (by rfl) ⟨2216609, by rfl⟩ : syracuseStep 2955479 = 4433219) B4433219
theorem B1970319 : Blo 1969435 1970319 := bstep (se 1 (by rfl) ⟨1477739, by rfl⟩ : syracuseStep 1970319 = 2955479) B2955479
theorem B2955485 : Blo 1969435 2955485 := bbase (se 3 (by rfl) ⟨554153, by rfl⟩ : syracuseStep 2955485 = 1108307) (by norm_num)
theorem B1970323 : Blo 1969435 1970323 := bstep (se 1 (by rfl) ⟨1477742, by rfl⟩ : syracuseStep 1970323 = 2955485) B2955485
theorem B4433237 : Blo 1969435 4433237 := bbase (se 12 (by rfl) ⟨1623, by rfl⟩ : syracuseStep 4433237 = 3247) (by norm_num)
theorem B2955491 : Blo 1969435 2955491 := bstep (se 1 (by rfl) ⟨2216618, by rfl⟩ : syracuseStep 2955491 = 4433237) B4433237
theorem B1970327 : Blo 1969435 1970327 := bstep (se 1 (by rfl) ⟨1477745, by rfl⟩ : syracuseStep 1970327 = 2955491) B2955491
theorem B2104061 : Blo 1969435 2104061 := bbase (se 3 (by rfl) ⟨394511, by rfl⟩ : syracuseStep 2104061 = 789023) (by norm_num)
theorem B5610829 : Blo 1969435 5610829 := bstep (se 3 (by rfl) ⟨1052030, by rfl⟩ : syracuseStep 5610829 = 2104061) B2104061
theorem B7481105 : Blo 1969435 7481105 := bstep (se 2 (by rfl) ⟨2805414, by rfl⟩ : syracuseStep 7481105 = 5610829) B5610829
theorem B4987403 : Blo 1969435 4987403 := bstep (se 1 (by rfl) ⟨3740552, by rfl⟩ : syracuseStep 4987403 = 7481105) B7481105
theorem B3324935 : Blo 1969435 3324935 := bstep (se 1 (by rfl) ⟨2493701, by rfl⟩ : syracuseStep 3324935 = 4987403) B4987403
theorem B2216623 : Blo 1969435 2216623 := bstep (se 1 (by rfl) ⟨1662467, by rfl⟩ : syracuseStep 2216623 = 3324935) B3324935
theorem B2955497 : Blo 1969435 2955497 := bstep (se 2 (by rfl) ⟨1108311, by rfl⟩ : syracuseStep 2955497 = 2216623) B2216623
theorem B1970331 : Blo 1969435 1970331 := bstep (se 1 (by rfl) ⟨1477748, by rfl⟩ : syracuseStep 1970331 = 2955497) B2955497
theorem B10651829 : Blo 1969435 10651829 := bbase (se 5 (by rfl) ⟨499304, by rfl⟩ : syracuseStep 10651829 = 998609) (by norm_num)
theorem B28404877 : Blo 1969435 28404877 := bstep (se 3 (by rfl) ⟨5325914, by rfl⟩ : syracuseStep 28404877 = 10651829) B10651829
theorem B37873169 : Blo 1969435 37873169 := bstep (se 2 (by rfl) ⟨14202438, by rfl⟩ : syracuseStep 37873169 = 28404877) B28404877
theorem B25248779 : Blo 1969435 25248779 := bstep (se 1 (by rfl) ⟨18936584, by rfl⟩ : syracuseStep 25248779 = 37873169) B37873169
theorem B16832519 : Blo 1969435 16832519 := bstep (se 1 (by rfl) ⟨12624389, by rfl⟩ : syracuseStep 16832519 = 25248779) B25248779
theorem B11221679 : Blo 1969435 11221679 := bstep (se 1 (by rfl) ⟨8416259, by rfl⟩ : syracuseStep 11221679 = 16832519) B16832519
theorem B7481119 : Blo 1969435 7481119 := bstep (se 1 (by rfl) ⟨5610839, by rfl⟩ : syracuseStep 7481119 = 11221679) B11221679
theorem B9974825 : Blo 1969435 9974825 := bstep (se 2 (by rfl) ⟨3740559, by rfl⟩ : syracuseStep 9974825 = 7481119) B7481119
theorem B6649883 : Blo 1969435 6649883 := bstep (se 1 (by rfl) ⟨4987412, by rfl⟩ : syracuseStep 6649883 = 9974825) B9974825
theorem B4433255 : Blo 1969435 4433255 := bstep (se 1 (by rfl) ⟨3324941, by rfl⟩ : syracuseStep 4433255 = 6649883) B6649883
theorem B2955503 : Blo 1969435 2955503 := bstep (se 1 (by rfl) ⟨2216627, by rfl⟩ : syracuseStep 2955503 = 4433255) B4433255
theorem B1970335 : Blo 1969435 1970335 := bstep (se 1 (by rfl) ⟨1477751, by rfl⟩ : syracuseStep 1970335 = 2955503) B2955503
theorem B2955509 : Blo 1969435 2955509 := bbase (se 5 (by rfl) ⟨138539, by rfl⟩ : syracuseStep 2955509 = 277079) (by norm_num)
theorem B1970339 : Blo 1969435 1970339 := bstep (se 1 (by rfl) ⟨1477754, by rfl⟩ : syracuseStep 1970339 = 2955509) B2955509
theorem B3994453 : Blo 1969435 3994453 := bbase (se 9 (by rfl) ⟨11702, by rfl⟩ : syracuseStep 3994453 = 23405) (by norm_num)
theorem B21303749 : Blo 1969435 21303749 := bstep (se 4 (by rfl) ⟨1997226, by rfl⟩ : syracuseStep 21303749 = 3994453) B3994453
theorem B14202499 : Blo 1969435 14202499 := bstep (se 1 (by rfl) ⟨10651874, by rfl⟩ : syracuseStep 14202499 = 21303749) B21303749
theorem B18936665 : Blo 1969435 18936665 := bstep (se 2 (by rfl) ⟨7101249, by rfl⟩ : syracuseStep 18936665 = 14202499) B14202499
theorem B12624443 : Blo 1969435 12624443 := bstep (se 1 (by rfl) ⟨9468332, by rfl⟩ : syracuseStep 12624443 = 18936665) B18936665
theorem B8416295 : Blo 1969435 8416295 := bstep (se 1 (by rfl) ⟨6312221, by rfl⟩ : syracuseStep 8416295 = 12624443) B12624443
theorem B5610863 : Blo 1969435 5610863 := bstep (se 1 (by rfl) ⟨4208147, by rfl⟩ : syracuseStep 5610863 = 8416295) B8416295
theorem B3740575 : Blo 1969435 3740575 := bstep (se 1 (by rfl) ⟨2805431, by rfl⟩ : syracuseStep 3740575 = 5610863) B5610863
theorem B4987433 : Blo 1969435 4987433 := bstep (se 2 (by rfl) ⟨1870287, by rfl⟩ : syracuseStep 4987433 = 3740575) B3740575
theorem B3324955 : Blo 1969435 3324955 := bstep (se 1 (by rfl) ⟨2493716, by rfl⟩ : syracuseStep 3324955 = 4987433) B4987433
theorem B4433273 : Blo 1969435 4433273 := bstep (se 2 (by rfl) ⟨1662477, by rfl⟩ : syracuseStep 4433273 = 3324955) B3324955
theorem B2955515 : Blo 1969435 2955515 := bstep (se 1 (by rfl) ⟨2216636, by rfl⟩ : syracuseStep 2955515 = 4433273) B4433273
theorem B1970343 : Blo 1969435 1970343 := bstep (se 1 (by rfl) ⟨1477757, by rfl⟩ : syracuseStep 1970343 = 2955515) B2955515
theorem B2216641 : Blo 1969435 2216641 := bbase (se 2 (by rfl) ⟨831240, by rfl⟩ : syracuseStep 2216641 = 1662481) (by norm_num)
theorem B2955521 : Blo 1969435 2955521 := bstep (se 2 (by rfl) ⟨1108320, by rfl⟩ : syracuseStep 2955521 = 2216641) B2216641
theorem B1970347 : Blo 1969435 1970347 := bstep (se 1 (by rfl) ⟨1477760, by rfl⟩ : syracuseStep 1970347 = 2955521) B2955521
theorem B4987453 : Blo 1969435 4987453 := bbase (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) (by norm_num)
theorem B6649937 : Blo 1969435 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B4433291 : Blo 1969435 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B2955527 : Blo 1969435 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B1970351 : Blo 1969435 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B2955533 : Blo 1969435 2955533 := bbase (se 3 (by rfl) ⟨554162, by rfl⟩ : syracuseStep 2955533 = 1108325) (by norm_num)
theorem B1970355 : Blo 1969435 1970355 := bstep (se 1 (by rfl) ⟨1477766, by rfl⟩ : syracuseStep 1970355 = 2955533) B2955533
theorem B4433309 : Blo 1969435 4433309 := bbase (se 3 (by rfl) ⟨831245, by rfl⟩ : syracuseStep 4433309 = 1662491) (by norm_num)
theorem B2955539 : Blo 1969435 2955539 := bstep (se 1 (by rfl) ⟨2216654, by rfl⟩ : syracuseStep 2955539 = 4433309) B4433309
theorem B1970359 : Blo 1969435 1970359 := bstep (se 1 (by rfl) ⟨1477769, by rfl⟩ : syracuseStep 1970359 = 2955539) B2955539
theorem B3324989 : Blo 1969435 3324989 := bbase (se 3 (by rfl) ⟨623435, by rfl⟩ : syracuseStep 3324989 = 1246871) (by norm_num)
theorem B2216659 : Blo 1969435 2216659 := bstep (se 1 (by rfl) ⟨1662494, by rfl⟩ : syracuseStep 2216659 = 3324989) B3324989
theorem B2955545 : Blo 1969435 2955545 := bstep (se 2 (by rfl) ⟨1108329, by rfl⟩ : syracuseStep 2955545 = 2216659) B2216659
theorem B1970363 : Blo 1969435 1970363 := bstep (se 1 (by rfl) ⟨1477772, by rfl⟩ : syracuseStep 1970363 = 2955545) B2955545
theorem B3156149 : Blo 1969435 3156149 := bbase (se 5 (by rfl) ⟨147944, by rfl⟩ : syracuseStep 3156149 = 295889) (by norm_num)
theorem B2104099 : Blo 1969435 2104099 := bstep (se 1 (by rfl) ⟨1578074, by rfl⟩ : syracuseStep 2104099 = 3156149) B3156149
theorem B11221861 : Blo 1969435 11221861 := bstep (se 4 (by rfl) ⟨1052049, by rfl⟩ : syracuseStep 11221861 = 2104099) B2104099
theorem B14962481 : Blo 1969435 14962481 := bstep (se 2 (by rfl) ⟨5610930, by rfl⟩ : syracuseStep 14962481 = 11221861) B11221861
theorem B9974987 : Blo 1969435 9974987 := bstep (se 1 (by rfl) ⟨7481240, by rfl⟩ : syracuseStep 9974987 = 14962481) B14962481
theorem B6649991 : Blo 1969435 6649991 := bstep (se 1 (by rfl) ⟨4987493, by rfl⟩ : syracuseStep 6649991 = 9974987) B9974987
theorem B4433327 : Blo 1969435 4433327 := bstep (se 1 (by rfl) ⟨3324995, by rfl⟩ : syracuseStep 4433327 = 6649991) B6649991
theorem B2955551 : Blo 1969435 2955551 := bstep (se 1 (by rfl) ⟨2216663, by rfl⟩ : syracuseStep 2955551 = 4433327) B4433327
theorem B1970367 : Blo 1969435 1970367 := bstep (se 1 (by rfl) ⟨1477775, by rfl⟩ : syracuseStep 1970367 = 2955551) B2955551
theorem B2955557 : Blo 1969435 2955557 := bbase (se 4 (by rfl) ⟨277083, by rfl⟩ : syracuseStep 2955557 = 554167) (by norm_num)
theorem B1970371 : Blo 1969435 1970371 := bstep (se 1 (by rfl) ⟨1477778, by rfl⟩ : syracuseStep 1970371 = 2955557) B2955557
theorem B2493757 : Blo 1969435 2493757 := bbase (se 3 (by rfl) ⟨467579, by rfl⟩ : syracuseStep 2493757 = 935159) (by norm_num)
theorem B3325009 : Blo 1969435 3325009 := bstep (se 2 (by rfl) ⟨1246878, by rfl⟩ : syracuseStep 3325009 = 2493757) B2493757
theorem B4433345 : Blo 1969435 4433345 := bstep (se 2 (by rfl) ⟨1662504, by rfl⟩ : syracuseStep 4433345 = 3325009) B3325009
theorem B2955563 : Blo 1969435 2955563 := bstep (se 1 (by rfl) ⟨2216672, by rfl⟩ : syracuseStep 2955563 = 4433345) B4433345
theorem B1970375 : Blo 1969435 1970375 := bstep (se 1 (by rfl) ⟨1477781, by rfl⟩ : syracuseStep 1970375 = 2955563) B2955563
theorem B2216677 : Blo 1969435 2216677 := bbase (se 4 (by rfl) ⟨207813, by rfl⟩ : syracuseStep 2216677 = 415627) (by norm_num)
theorem B2955569 : Blo 1969435 2955569 := bstep (se 2 (by rfl) ⟨1108338, by rfl⟩ : syracuseStep 2955569 = 2216677) B2216677
theorem B1970379 : Blo 1969435 1970379 := bstep (se 1 (by rfl) ⟨1477784, by rfl⟩ : syracuseStep 1970379 = 2955569) B2955569
theorem B2132825 : Blo 1969435 2132825 := bbase (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) (by norm_num)
theorem B5687533 : Blo 1969435 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B7583377 : Blo 1969435 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B10111169 : Blo 1969435 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B6740779 : Blo 1969435 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B8987705 : Blo 1969435 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B5991803 : Blo 1969435 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B3994535 : Blo 1969435 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B10652093 : Blo 1969435 10652093 := bstep (se 3 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 10652093 = 3994535) B3994535
theorem B7101395 : Blo 1969435 7101395 := bstep (se 1 (by rfl) ⟨5326046, by rfl⟩ : syracuseStep 7101395 = 10652093) B10652093
theorem B4734263 : Blo 1969435 4734263 := bstep (se 1 (by rfl) ⟨3550697, by rfl⟩ : syracuseStep 4734263 = 7101395) B7101395
theorem B3156175 : Blo 1969435 3156175 := bstep (se 1 (by rfl) ⟨2367131, by rfl⟩ : syracuseStep 3156175 = 4734263) B4734263
theorem B4208233 : Blo 1969435 4208233 := bstep (se 2 (by rfl) ⟨1578087, by rfl⟩ : syracuseStep 4208233 = 3156175) B3156175
theorem B5610977 : Blo 1969435 5610977 := bstep (se 2 (by rfl) ⟨2104116, by rfl⟩ : syracuseStep 5610977 = 4208233) B4208233
theorem B3740651 : Blo 1969435 3740651 := bstep (se 1 (by rfl) ⟨2805488, by rfl⟩ : syracuseStep 3740651 = 5610977) B5610977
theorem B2493767 : Blo 1969435 2493767 := bstep (se 1 (by rfl) ⟨1870325, by rfl⟩ : syracuseStep 2493767 = 3740651) B3740651
theorem B6650045 : Blo 1969435 6650045 := bstep (se 3 (by rfl) ⟨1246883, by rfl⟩ : syracuseStep 6650045 = 2493767) B2493767
theorem B4433363 : Blo 1969435 4433363 := bstep (se 1 (by rfl) ⟨3325022, by rfl⟩ : syracuseStep 4433363 = 6650045) B6650045
theorem B2955575 : Blo 1969435 2955575 := bstep (se 1 (by rfl) ⟨2216681, by rfl⟩ : syracuseStep 2955575 = 4433363) B4433363
theorem B1970383 : Blo 1969435 1970383 := bstep (se 1 (by rfl) ⟨1477787, by rfl⟩ : syracuseStep 1970383 = 2955575) B2955575
theorem B2955581 : Blo 1969435 2955581 := bbase (se 3 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 2955581 = 1108343) (by norm_num)
theorem B1970387 : Blo 1969435 1970387 := bstep (se 1 (by rfl) ⟨1477790, by rfl⟩ : syracuseStep 1970387 = 2955581) B2955581
theorem B4433381 : Blo 1969435 4433381 := bbase (se 4 (by rfl) ⟨415629, by rfl⟩ : syracuseStep 4433381 = 831259) (by norm_num)
theorem B2955587 : Blo 1969435 2955587 := bstep (se 1 (by rfl) ⟨2216690, by rfl⟩ : syracuseStep 2955587 = 4433381) B4433381
theorem B1970391 : Blo 1969435 1970391 := bstep (se 1 (by rfl) ⟨1477793, by rfl⟩ : syracuseStep 1970391 = 2955587) B2955587
theorem B4987565 : Blo 1969435 4987565 := bbase (se 3 (by rfl) ⟨935168, by rfl⟩ : syracuseStep 4987565 = 1870337) (by norm_num)
theorem B3325043 : Blo 1969435 3325043 := bstep (se 1 (by rfl) ⟨2493782, by rfl⟩ : syracuseStep 3325043 = 4987565) B4987565
theorem B2216695 : Blo 1969435 2216695 := bstep (se 1 (by rfl) ⟨1662521, by rfl⟩ : syracuseStep 2216695 = 3325043) B3325043
theorem B2955593 : Blo 1969435 2955593 := bstep (se 2 (by rfl) ⟨1108347, by rfl⟩ : syracuseStep 2955593 = 2216695) B2216695
theorem B1970395 : Blo 1969435 1970395 := bstep (se 1 (by rfl) ⟨1477796, by rfl⟩ : syracuseStep 1970395 = 2955593) B2955593
theorem B4734301 : Blo 1969435 4734301 := bbase (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) (by norm_num)
theorem B6312401 : Blo 1969435 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B4208267 : Blo 1969435 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B2805511 : Blo 1969435 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B3740681 : Blo 1969435 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B9975149 : Blo 1969435 9975149 := bstep (se 3 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 9975149 = 3740681) B3740681
theorem B6650099 : Blo 1969435 6650099 := bstep (se 1 (by rfl) ⟨4987574, by rfl⟩ : syracuseStep 6650099 = 9975149) B9975149
theorem B4433399 : Blo 1969435 4433399 := bstep (se 1 (by rfl) ⟨3325049, by rfl⟩ : syracuseStep 4433399 = 6650099) B6650099
theorem B2955599 : Blo 1969435 2955599 := bstep (se 1 (by rfl) ⟨2216699, by rfl⟩ : syracuseStep 2955599 = 4433399) B4433399
theorem B1970399 : Blo 1969435 1970399 := bstep (se 1 (by rfl) ⟨1477799, by rfl⟩ : syracuseStep 1970399 = 2955599) B2955599
theorem B2955605 : Blo 1969435 2955605 := bbase (se 10 (by rfl) ⟨4329, by rfl⟩ : syracuseStep 2955605 = 8659) (by norm_num)
theorem B1970403 : Blo 1969435 1970403 := bstep (se 1 (by rfl) ⟨1477802, by rfl⟩ : syracuseStep 1970403 = 2955605) B2955605
theorem B5611045 : Blo 1969435 5611045 := bbase (se 4 (by rfl) ⟨526035, by rfl⟩ : syracuseStep 5611045 = 1052071) (by norm_num)
theorem B7481393 : Blo 1969435 7481393 := bstep (se 2 (by rfl) ⟨2805522, by rfl⟩ : syracuseStep 7481393 = 5611045) B5611045
theorem B4987595 : Blo 1969435 4987595 := bstep (se 1 (by rfl) ⟨3740696, by rfl⟩ : syracuseStep 4987595 = 7481393) B7481393
theorem B3325063 : Blo 1969435 3325063 := bstep (se 1 (by rfl) ⟨2493797, by rfl⟩ : syracuseStep 3325063 = 4987595) B4987595
theorem B4433417 : Blo 1969435 4433417 := bstep (se 2 (by rfl) ⟨1662531, by rfl⟩ : syracuseStep 4433417 = 3325063) B3325063
theorem B2955611 : Blo 1969435 2955611 := bstep (se 1 (by rfl) ⟨2216708, by rfl⟩ : syracuseStep 2955611 = 4433417) B4433417
theorem B1970407 : Blo 1969435 1970407 := bstep (se 1 (by rfl) ⟨1477805, by rfl⟩ : syracuseStep 1970407 = 2955611) B2955611
theorem B2216713 : Blo 1969435 2216713 := bbase (se 2 (by rfl) ⟨831267, by rfl⟩ : syracuseStep 2216713 = 1662535) (by norm_num)
theorem B2955617 : Blo 1969435 2955617 := bstep (se 2 (by rfl) ⟨1108356, by rfl⟩ : syracuseStep 2955617 = 2216713) B2216713
theorem B1970411 : Blo 1969435 1970411 := bstep (se 1 (by rfl) ⟨1477808, by rfl⟩ : syracuseStep 1970411 = 2955617) B2955617
theorem B9468677 : Blo 1969435 9468677 := bbase (se 4 (by rfl) ⟨887688, by rfl⟩ : syracuseStep 9468677 = 1775377) (by norm_num)
theorem B25249805 : Blo 1969435 25249805 := bstep (se 3 (by rfl) ⟨4734338, by rfl⟩ : syracuseStep 25249805 = 9468677) B9468677
theorem B16833203 : Blo 1969435 16833203 := bstep (se 1 (by rfl) ⟨12624902, by rfl⟩ : syracuseStep 16833203 = 25249805) B25249805
theorem B11222135 : Blo 1969435 11222135 := bstep (se 1 (by rfl) ⟨8416601, by rfl⟩ : syracuseStep 11222135 = 16833203) B16833203
theorem B7481423 : Blo 1969435 7481423 := bstep (se 1 (by rfl) ⟨5611067, by rfl⟩ : syracuseStep 7481423 = 11222135) B11222135
theorem B4987615 : Blo 1969435 4987615 := bstep (se 1 (by rfl) ⟨3740711, by rfl⟩ : syracuseStep 4987615 = 7481423) B7481423
theorem B6650153 : Blo 1969435 6650153 := bstep (se 2 (by rfl) ⟨2493807, by rfl⟩ : syracuseStep 6650153 = 4987615) B4987615
theorem B4433435 : Blo 1969435 4433435 := bstep (se 1 (by rfl) ⟨3325076, by rfl⟩ : syracuseStep 4433435 = 6650153) B6650153
theorem B2955623 : Blo 1969435 2955623 := bstep (se 1 (by rfl) ⟨2216717, by rfl⟩ : syracuseStep 2955623 = 4433435) B4433435
theorem B1970415 : Blo 1969435 1970415 := bstep (se 1 (by rfl) ⟨1477811, by rfl⟩ : syracuseStep 1970415 = 2955623) B2955623
theorem B2955629 : Blo 1969435 2955629 := bbase (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) (by norm_num)
theorem B1970419 : Blo 1969435 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B4433453 : Blo 1969435 4433453 := bbase (se 3 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 4433453 = 1662545) (by norm_num)
theorem B2955635 : Blo 1969435 2955635 := bstep (se 1 (by rfl) ⟨2216726, by rfl⟩ : syracuseStep 2955635 = 4433453) B4433453
theorem B1970423 : Blo 1969435 1970423 := bstep (se 1 (by rfl) ⟨1477817, by rfl⟩ : syracuseStep 1970423 = 2955635) B2955635
theorem B5326165 : Blo 1969435 5326165 := bbase (se 12 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 5326165 = 3901) (by norm_num)
theorem B28406213 : Blo 1969435 28406213 := bstep (se 4 (by rfl) ⟨2663082, by rfl⟩ : syracuseStep 28406213 = 5326165) B5326165
theorem B18937475 : Blo 1969435 18937475 := bstep (se 1 (by rfl) ⟨14203106, by rfl⟩ : syracuseStep 18937475 = 28406213) B28406213
theorem B12624983 : Blo 1969435 12624983 := bstep (se 1 (by rfl) ⟨9468737, by rfl⟩ : syracuseStep 12624983 = 18937475) B18937475
theorem B8416655 : Blo 1969435 8416655 := bstep (se 1 (by rfl) ⟨6312491, by rfl⟩ : syracuseStep 8416655 = 12624983) B12624983
theorem B5611103 : Blo 1969435 5611103 := bstep (se 1 (by rfl) ⟨4208327, by rfl⟩ : syracuseStep 5611103 = 8416655) B8416655
theorem B3740735 : Blo 1969435 3740735 := bstep (se 1 (by rfl) ⟨2805551, by rfl⟩ : syracuseStep 3740735 = 5611103) B5611103
theorem B2493823 : Blo 1969435 2493823 := bstep (se 1 (by rfl) ⟨1870367, by rfl⟩ : syracuseStep 2493823 = 3740735) B3740735
theorem B3325097 : Blo 1969435 3325097 := bstep (se 2 (by rfl) ⟨1246911, by rfl⟩ : syracuseStep 3325097 = 2493823) B2493823
theorem B2216731 : Blo 1969435 2216731 := bstep (se 1 (by rfl) ⟨1662548, by rfl⟩ : syracuseStep 2216731 = 3325097) B3325097
theorem B2955641 : Blo 1969435 2955641 := bstep (se 2 (by rfl) ⟨1108365, by rfl⟩ : syracuseStep 2955641 = 2216731) B2216731
theorem B1970427 : Blo 1969435 1970427 := bstep (se 1 (by rfl) ⟨1477820, by rfl⟩ : syracuseStep 1970427 = 2955641) B2955641
theorem B2527853 : Blo 1969435 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B26963765 : Blo 1969435 26963765 := bstep (se 5 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 26963765 = 2527853) B2527853
theorem B17975843 : Blo 1969435 17975843 := bstep (se 1 (by rfl) ⟨13481882, by rfl⟩ : syracuseStep 17975843 = 26963765) B26963765
theorem B11983895 : Blo 1969435 11983895 := bstep (se 1 (by rfl) ⟨8987921, by rfl⟩ : syracuseStep 11983895 = 17975843) B17975843
theorem B7989263 : Blo 1969435 7989263 := bstep (se 1 (by rfl) ⟨5991947, by rfl⟩ : syracuseStep 7989263 = 11983895) B11983895
theorem B5326175 : Blo 1969435 5326175 := bstep (se 1 (by rfl) ⟨3994631, by rfl⟩ : syracuseStep 5326175 = 7989263) B7989263
theorem B3550783 : Blo 1969435 3550783 := bstep (se 1 (by rfl) ⟨2663087, by rfl⟩ : syracuseStep 3550783 = 5326175) B5326175
theorem B4734377 : Blo 1969435 4734377 := bstep (se 2 (by rfl) ⟨1775391, by rfl⟩ : syracuseStep 4734377 = 3550783) B3550783
theorem B3156251 : Blo 1969435 3156251 := bstep (se 1 (by rfl) ⟨2367188, by rfl⟩ : syracuseStep 3156251 = 4734377) B4734377
theorem B33666677 : Blo 1969435 33666677 := bstep (se 5 (by rfl) ⟨1578125, by rfl⟩ : syracuseStep 33666677 = 3156251) B3156251
theorem B22444451 : Blo 1969435 22444451 := bstep (se 1 (by rfl) ⟨16833338, by rfl⟩ : syracuseStep 22444451 = 33666677) B33666677
theorem B14962967 : Blo 1969435 14962967 := bstep (se 1 (by rfl) ⟨11222225, by rfl⟩ : syracuseStep 14962967 = 22444451) B22444451
theorem B9975311 : Blo 1969435 9975311 := bstep (se 1 (by rfl) ⟨7481483, by rfl⟩ : syracuseStep 9975311 = 14962967) B14962967
theorem B6650207 : Blo 1969435 6650207 := bstep (se 1 (by rfl) ⟨4987655, by rfl⟩ : syracuseStep 6650207 = 9975311) B9975311
theorem B4433471 : Blo 1969435 4433471 := bstep (se 1 (by rfl) ⟨3325103, by rfl⟩ : syracuseStep 4433471 = 6650207) B6650207
theorem B2955647 : Blo 1969435 2955647 := bstep (se 1 (by rfl) ⟨2216735, by rfl⟩ : syracuseStep 2955647 = 4433471) B4433471
theorem B1970431 : Blo 1969435 1970431 := bstep (se 1 (by rfl) ⟨1477823, by rfl⟩ : syracuseStep 1970431 = 2955647) B2955647
theorem B2955653 : Blo 1969435 2955653 := bbase (se 4 (by rfl) ⟨277092, by rfl⟩ : syracuseStep 2955653 = 554185) (by norm_num)
theorem B1970435 : Blo 1969435 1970435 := bstep (se 1 (by rfl) ⟨1477826, by rfl⟩ : syracuseStep 1970435 = 2955653) B2955653
theorem B3325117 : Blo 1969435 3325117 := bbase (se 3 (by rfl) ⟨623459, by rfl⟩ : syracuseStep 3325117 = 1246919) (by norm_num)
theorem B4433489 : Blo 1969435 4433489 := bstep (se 2 (by rfl) ⟨1662558, by rfl⟩ : syracuseStep 4433489 = 3325117) B3325117
theorem B2955659 : Blo 1969435 2955659 := bstep (se 1 (by rfl) ⟨2216744, by rfl⟩ : syracuseStep 2955659 = 4433489) B4433489
theorem B1970439 : Blo 1969435 1970439 := bstep (se 1 (by rfl) ⟨1477829, by rfl⟩ : syracuseStep 1970439 = 2955659) B2955659
theorem B2216749 : Blo 1969435 2216749 := bbase (se 3 (by rfl) ⟨415640, by rfl⟩ : syracuseStep 2216749 = 831281) (by norm_num)
theorem B2955665 : Blo 1969435 2955665 := bstep (se 2 (by rfl) ⟨1108374, by rfl⟩ : syracuseStep 2955665 = 2216749) B2216749
theorem B1970443 : Blo 1969435 1970443 := bstep (se 1 (by rfl) ⟨1477832, by rfl⟩ : syracuseStep 1970443 = 2955665) B2955665
theorem B6650261 : Blo 1969435 6650261 := bbase (se 6 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 6650261 = 311731) (by norm_num)
theorem B4433507 : Blo 1969435 4433507 := bstep (se 1 (by rfl) ⟨3325130, by rfl⟩ : syracuseStep 4433507 = 6650261) B6650261
theorem B2955671 : Blo 1969435 2955671 := bstep (se 1 (by rfl) ⟨2216753, by rfl⟩ : syracuseStep 2955671 = 4433507) B4433507
theorem B1970447 : Blo 1969435 1970447 := bstep (se 1 (by rfl) ⟨1477835, by rfl⟩ : syracuseStep 1970447 = 2955671) B2955671
theorem B2955677 : Blo 1969435 2955677 := bbase (se 3 (by rfl) ⟨554189, by rfl⟩ : syracuseStep 2955677 = 1108379) (by norm_num)
theorem B1970451 : Blo 1969435 1970451 := bstep (se 1 (by rfl) ⟨1477838, by rfl⟩ : syracuseStep 1970451 = 2955677) B2955677
theorem B4433525 : Blo 1969435 4433525 := bbase (se 5 (by rfl) ⟨207821, by rfl⟩ : syracuseStep 4433525 = 415643) (by norm_num)
theorem B2955683 : Blo 1969435 2955683 := bstep (se 1 (by rfl) ⟨2216762, by rfl⟩ : syracuseStep 2955683 = 4433525) B4433525
theorem B1970455 : Blo 1969435 1970455 := bstep (se 1 (by rfl) ⟨1477841, by rfl⟩ : syracuseStep 1970455 = 2955683) B2955683
theorem B4734445 : Blo 1969435 4734445 := bbase (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) (by norm_num)
theorem B6312593 : Blo 1969435 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B16833581 : Blo 1969435 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B11222387 : Blo 1969435 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B7481591 : Blo 1969435 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B4987727 : Blo 1969435 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B3325151 : Blo 1969435 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B2216767 : Blo 1969435 2216767 := bstep (se 1 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 2216767 = 3325151) B3325151
theorem B2955689 : Blo 1969435 2955689 := bstep (se 2 (by rfl) ⟨1108383, by rfl⟩ : syracuseStep 2955689 = 2216767) B2216767
theorem B1970459 : Blo 1969435 1970459 := bstep (se 1 (by rfl) ⟨1477844, by rfl⟩ : syracuseStep 1970459 = 2955689) B2955689
theorem B7481605 : Blo 1969435 7481605 := bbase (se 4 (by rfl) ⟨701400, by rfl⟩ : syracuseStep 7481605 = 1402801) (by norm_num)
theorem B9975473 : Blo 1969435 9975473 := bstep (se 2 (by rfl) ⟨3740802, by rfl⟩ : syracuseStep 9975473 = 7481605) B7481605
theorem B6650315 : Blo 1969435 6650315 := bstep (se 1 (by rfl) ⟨4987736, by rfl⟩ : syracuseStep 6650315 = 9975473) B9975473
theorem B4433543 : Blo 1969435 4433543 := bstep (se 1 (by rfl) ⟨3325157, by rfl⟩ : syracuseStep 4433543 = 6650315) B6650315
theorem B2955695 : Blo 1969435 2955695 := bstep (se 1 (by rfl) ⟨2216771, by rfl⟩ : syracuseStep 2955695 = 4433543) B4433543
theorem B1970463 : Blo 1969435 1970463 := bstep (se 1 (by rfl) ⟨1477847, by rfl⟩ : syracuseStep 1970463 = 2955695) B2955695
theorem B2955701 : Blo 1969435 2955701 := bbase (se 5 (by rfl) ⟨138548, by rfl⟩ : syracuseStep 2955701 = 277097) (by norm_num)
theorem B1970467 : Blo 1969435 1970467 := bstep (se 1 (by rfl) ⟨1477850, by rfl⟩ : syracuseStep 1970467 = 2955701) B2955701
theorem B4987757 : Blo 1969435 4987757 := bbase (se 3 (by rfl) ⟨935204, by rfl⟩ : syracuseStep 4987757 = 1870409) (by norm_num)
theorem B3325171 : Blo 1969435 3325171 := bstep (se 1 (by rfl) ⟨2493878, by rfl⟩ : syracuseStep 3325171 = 4987757) B4987757
theorem B4433561 : Blo 1969435 4433561 := bstep (se 2 (by rfl) ⟨1662585, by rfl⟩ : syracuseStep 4433561 = 3325171) B3325171
theorem B2955707 : Blo 1969435 2955707 := bstep (se 1 (by rfl) ⟨2216780, by rfl⟩ : syracuseStep 2955707 = 4433561) B4433561
theorem B1970471 : Blo 1969435 1970471 := bstep (se 1 (by rfl) ⟨1477853, by rfl⟩ : syracuseStep 1970471 = 2955707) B2955707
theorem B2216785 : Blo 1969435 2216785 := bbase (se 2 (by rfl) ⟨831294, by rfl⟩ : syracuseStep 2216785 = 1662589) (by norm_num)
theorem B2955713 : Blo 1969435 2955713 := bstep (se 2 (by rfl) ⟨1108392, by rfl⟩ : syracuseStep 2955713 = 2216785) B2216785
theorem B1970475 : Blo 1969435 1970475 := bstep (se 1 (by rfl) ⟨1477856, by rfl⟩ : syracuseStep 1970475 = 2955713) B2955713
theorem B7989461 : Blo 1969435 7989461 := bbase (se 7 (by rfl) ⟨93626, by rfl⟩ : syracuseStep 7989461 = 187253) (by norm_num)
theorem B5326307 : Blo 1969435 5326307 := bstep (se 1 (by rfl) ⟨3994730, by rfl⟩ : syracuseStep 5326307 = 7989461) B7989461
theorem B3550871 : Blo 1969435 3550871 := bstep (se 1 (by rfl) ⟨2663153, by rfl⟩ : syracuseStep 3550871 = 5326307) B5326307
theorem B2367247 : Blo 1969435 2367247 := bstep (se 1 (by rfl) ⟨1775435, by rfl⟩ : syracuseStep 2367247 = 3550871) B3550871
theorem B3156329 : Blo 1969435 3156329 := bstep (se 2 (by rfl) ⟨1183623, by rfl⟩ : syracuseStep 3156329 = 2367247) B2367247
theorem B2104219 : Blo 1969435 2104219 := bstep (se 1 (by rfl) ⟨1578164, by rfl⟩ : syracuseStep 2104219 = 3156329) B3156329
theorem B2805625 : Blo 1969435 2805625 := bstep (se 2 (by rfl) ⟨1052109, by rfl⟩ : syracuseStep 2805625 = 2104219) B2104219
theorem B3740833 : Blo 1969435 3740833 := bstep (se 2 (by rfl) ⟨1402812, by rfl⟩ : syracuseStep 3740833 = 2805625) B2805625
theorem B4987777 : Blo 1969435 4987777 := bstep (se 2 (by rfl) ⟨1870416, by rfl⟩ : syracuseStep 4987777 = 3740833) B3740833
theorem B6650369 : Blo 1969435 6650369 := bstep (se 2 (by rfl) ⟨2493888, by rfl⟩ : syracuseStep 6650369 = 4987777) B4987777
theorem B4433579 : Blo 1969435 4433579 := bstep (se 1 (by rfl) ⟨3325184, by rfl⟩ : syracuseStep 4433579 = 6650369) B6650369
theorem B2955719 : Blo 1969435 2955719 := bstep (se 1 (by rfl) ⟨2216789, by rfl⟩ : syracuseStep 2955719 = 4433579) B4433579
theorem B1970479 : Blo 1969435 1970479 := bstep (se 1 (by rfl) ⟨1477859, by rfl⟩ : syracuseStep 1970479 = 2955719) B2955719
theorem B2955725 : Blo 1969435 2955725 := bbase (se 3 (by rfl) ⟨554198, by rfl⟩ : syracuseStep 2955725 = 1108397) (by norm_num)
theorem B1970483 : Blo 1969435 1970483 := bstep (se 1 (by rfl) ⟨1477862, by rfl⟩ : syracuseStep 1970483 = 2955725) B2955725
theorem B4433597 : Blo 1969435 4433597 := bbase (se 3 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 4433597 = 1662599) (by norm_num)
theorem B2955731 : Blo 1969435 2955731 := bstep (se 1 (by rfl) ⟨2216798, by rfl⟩ : syracuseStep 2955731 = 4433597) B4433597
theorem B1970487 : Blo 1969435 1970487 := bstep (se 1 (by rfl) ⟨1477865, by rfl⟩ : syracuseStep 1970487 = 2955731) B2955731
theorem B3325205 : Blo 1969435 3325205 := bbase (se 6 (by rfl) ⟨77934, by rfl⟩ : syracuseStep 3325205 = 155869) (by norm_num)
theorem B2216803 : Blo 1969435 2216803 := bstep (se 1 (by rfl) ⟨1662602, by rfl⟩ : syracuseStep 2216803 = 3325205) B3325205
theorem B2955737 : Blo 1969435 2955737 := bstep (se 2 (by rfl) ⟨1108401, by rfl⟩ : syracuseStep 2955737 = 2216803) B2216803
theorem B1970491 : Blo 1969435 1970491 := bstep (se 1 (by rfl) ⟨1477868, by rfl⟩ : syracuseStep 1970491 = 2955737) B2955737
theorem B2247053 : Blo 1969435 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B5992141 : Blo 1969435 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B7989521 : Blo 1969435 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B21305389 : Blo 1969435 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B28407185 : Blo 1969435 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B18938123 : Blo 1969435 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B12625415 : Blo 1969435 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B8416943 : Blo 1969435 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B5611295 : Blo 1969435 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B14963453 : Blo 1969435 14963453 := bstep (se 3 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 14963453 = 5611295) B5611295
theorem B9975635 : Blo 1969435 9975635 := bstep (se 1 (by rfl) ⟨7481726, by rfl⟩ : syracuseStep 9975635 = 14963453) B14963453
theorem B6650423 : Blo 1969435 6650423 := bstep (se 1 (by rfl) ⟨4987817, by rfl⟩ : syracuseStep 6650423 = 9975635) B9975635
theorem B4433615 : Blo 1969435 4433615 := bstep (se 1 (by rfl) ⟨3325211, by rfl⟩ : syracuseStep 4433615 = 6650423) B6650423
theorem B2955743 : Blo 1969435 2955743 := bstep (se 1 (by rfl) ⟨2216807, by rfl⟩ : syracuseStep 2955743 = 4433615) B4433615
theorem B1970495 : Blo 1969435 1970495 := bstep (se 1 (by rfl) ⟨1477871, by rfl⟩ : syracuseStep 1970495 = 2955743) B2955743
theorem B2955749 : Blo 1969435 2955749 := bbase (se 4 (by rfl) ⟨277101, by rfl⟩ : syracuseStep 2955749 = 554203) (by norm_num)
theorem B1970499 : Blo 1969435 1970499 := bstep (se 1 (by rfl) ⟨1477874, by rfl⟩ : syracuseStep 1970499 = 2955749) B2955749
theorem B1997389 : Blo 1969435 1997389 := bbase (se 3 (by rfl) ⟨374510, by rfl⟩ : syracuseStep 1997389 = 749021) (by norm_num)
theorem B10652741 : Blo 1969435 10652741 := bstep (se 4 (by rfl) ⟨998694, by rfl⟩ : syracuseStep 10652741 = 1997389) B1997389
theorem B7101827 : Blo 1969435 7101827 := bstep (se 1 (by rfl) ⟨5326370, by rfl⟩ : syracuseStep 7101827 = 10652741) B10652741
theorem B4734551 : Blo 1969435 4734551 := bstep (se 1 (by rfl) ⟨3550913, by rfl⟩ : syracuseStep 4734551 = 7101827) B7101827
theorem B12625469 : Blo 1969435 12625469 := bstep (se 3 (by rfl) ⟨2367275, by rfl⟩ : syracuseStep 12625469 = 4734551) B4734551
theorem B8416979 : Blo 1969435 8416979 := bstep (se 1 (by rfl) ⟨6312734, by rfl⟩ : syracuseStep 8416979 = 12625469) B12625469
theorem B5611319 : Blo 1969435 5611319 := bstep (se 1 (by rfl) ⟨4208489, by rfl⟩ : syracuseStep 5611319 = 8416979) B8416979
theorem B3740879 : Blo 1969435 3740879 := bstep (se 1 (by rfl) ⟨2805659, by rfl⟩ : syracuseStep 3740879 = 5611319) B5611319
theorem B2493919 : Blo 1969435 2493919 := bstep (se 1 (by rfl) ⟨1870439, by rfl⟩ : syracuseStep 2493919 = 3740879) B3740879
theorem B3325225 : Blo 1969435 3325225 := bstep (se 2 (by rfl) ⟨1246959, by rfl⟩ : syracuseStep 3325225 = 2493919) B2493919
theorem B4433633 : Blo 1969435 4433633 := bstep (se 2 (by rfl) ⟨1662612, by rfl⟩ : syracuseStep 4433633 = 3325225) B3325225
theorem B2955755 : Blo 1969435 2955755 := bstep (se 1 (by rfl) ⟨2216816, by rfl⟩ : syracuseStep 2955755 = 4433633) B4433633
theorem B1970503 : Blo 1969435 1970503 := bstep (se 1 (by rfl) ⟨1477877, by rfl⟩ : syracuseStep 1970503 = 2955755) B2955755
theorem B2216821 : Blo 1969435 2216821 := bbase (se 5 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 2216821 = 207827) (by norm_num)
theorem B2955761 : Blo 1969435 2955761 := bstep (se 2 (by rfl) ⟨1108410, by rfl⟩ : syracuseStep 2955761 = 2216821) B2216821
theorem B1970507 : Blo 1969435 1970507 := bstep (se 1 (by rfl) ⟨1477880, by rfl⟩ : syracuseStep 1970507 = 2955761) B2955761
theorem B2493929 : Blo 1969435 2493929 := bbase (se 2 (by rfl) ⟨935223, by rfl⟩ : syracuseStep 2493929 = 1870447) (by norm_num)
theorem B6650477 : Blo 1969435 6650477 := bstep (se 3 (by rfl) ⟨1246964, by rfl⟩ : syracuseStep 6650477 = 2493929) B2493929
theorem B4433651 : Blo 1969435 4433651 := bstep (se 1 (by rfl) ⟨3325238, by rfl⟩ : syracuseStep 4433651 = 6650477) B6650477
theorem B2955767 : Blo 1969435 2955767 := bstep (se 1 (by rfl) ⟨2216825, by rfl⟩ : syracuseStep 2955767 = 4433651) B4433651
theorem B1970511 : Blo 1969435 1970511 := bstep (se 1 (by rfl) ⟨1477883, by rfl⟩ : syracuseStep 1970511 = 2955767) B2955767
theorem B2955773 : Blo 1969435 2955773 := bbase (se 3 (by rfl) ⟨554207, by rfl⟩ : syracuseStep 2955773 = 1108415) (by norm_num)
theorem B1970515 : Blo 1969435 1970515 := bstep (se 1 (by rfl) ⟨1477886, by rfl⟩ : syracuseStep 1970515 = 2955773) B2955773
theorem B4433669 : Blo 1969435 4433669 := bbase (se 4 (by rfl) ⟨415656, by rfl⟩ : syracuseStep 4433669 = 831313) (by norm_num)
theorem B2955779 : Blo 1969435 2955779 := bstep (se 1 (by rfl) ⟨2216834, by rfl⟩ : syracuseStep 2955779 = 4433669) B4433669
theorem B1970519 : Blo 1969435 1970519 := bstep (se 1 (by rfl) ⟨1477889, by rfl⟩ : syracuseStep 1970519 = 2955779) B2955779
theorem B3740917 : Blo 1969435 3740917 := bbase (se 5 (by rfl) ⟨175355, by rfl⟩ : syracuseStep 3740917 = 350711) (by norm_num)
theorem B4987889 : Blo 1969435 4987889 := bstep (se 2 (by rfl) ⟨1870458, by rfl⟩ : syracuseStep 4987889 = 3740917) B3740917
theorem B3325259 : Blo 1969435 3325259 := bstep (se 1 (by rfl) ⟨2493944, by rfl⟩ : syracuseStep 3325259 = 4987889) B4987889
theorem B2216839 : Blo 1969435 2216839 := bstep (se 1 (by rfl) ⟨1662629, by rfl⟩ : syracuseStep 2216839 = 3325259) B3325259
theorem B2955785 : Blo 1969435 2955785 := bstep (se 2 (by rfl) ⟨1108419, by rfl⟩ : syracuseStep 2955785 = 2216839) B2216839
theorem B1970523 : Blo 1969435 1970523 := bstep (se 1 (by rfl) ⟨1477892, by rfl⟩ : syracuseStep 1970523 = 2955785) B2955785
theorem B9975797 : Blo 1969435 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B6650531 : Blo 1969435 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B4433687 : Blo 1969435 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B2955791 : Blo 1969435 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B1970527 : Blo 1969435 1970527 := bstep (se 1 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 1970527 = 2955791) B2955791
theorem B2955797 : Blo 1969435 2955797 := bbase (se 6 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 2955797 = 138553) (by norm_num)
theorem B1970531 : Blo 1969435 1970531 := bstep (se 1 (by rfl) ⟨1477898, by rfl⟩ : syracuseStep 1970531 = 2955797) B2955797
theorem B16834229 : Blo 1969435 16834229 := bbase (se 5 (by rfl) ⟨789104, by rfl⟩ : syracuseStep 16834229 = 1578209) (by norm_num)
theorem B11222819 : Blo 1969435 11222819 := bstep (se 1 (by rfl) ⟨8417114, by rfl⟩ : syracuseStep 11222819 = 16834229) B16834229
theorem B7481879 : Blo 1969435 7481879 := bstep (se 1 (by rfl) ⟨5611409, by rfl⟩ : syracuseStep 7481879 = 11222819) B11222819
theorem B4987919 : Blo 1969435 4987919 := bstep (se 1 (by rfl) ⟨3740939, by rfl⟩ : syracuseStep 4987919 = 7481879) B7481879
theorem B3325279 : Blo 1969435 3325279 := bstep (se 1 (by rfl) ⟨2493959, by rfl⟩ : syracuseStep 3325279 = 4987919) B4987919
theorem B4433705 : Blo 1969435 4433705 := bstep (se 2 (by rfl) ⟨1662639, by rfl⟩ : syracuseStep 4433705 = 3325279) B3325279
theorem B2955803 : Blo 1969435 2955803 := bstep (se 1 (by rfl) ⟨2216852, by rfl⟩ : syracuseStep 2955803 = 4433705) B4433705
theorem B1970535 : Blo 1969435 1970535 := bstep (se 1 (by rfl) ⟨1477901, by rfl⟩ : syracuseStep 1970535 = 2955803) B2955803
theorem B2216857 : Blo 1969435 2216857 := bbase (se 2 (by rfl) ⟨831321, by rfl⟩ : syracuseStep 2216857 = 1662643) (by norm_num)
theorem B2955809 : Blo 1969435 2955809 := bstep (se 2 (by rfl) ⟨1108428, by rfl⟩ : syracuseStep 2955809 = 2216857) B2216857
theorem B1970539 : Blo 1969435 1970539 := bstep (se 1 (by rfl) ⟨1477904, by rfl⟩ : syracuseStep 1970539 = 2955809) B2955809
theorem B7481909 : Blo 1969435 7481909 := bbase (se 5 (by rfl) ⟨350714, by rfl⟩ : syracuseStep 7481909 = 701429) (by norm_num)
theorem B4987939 : Blo 1969435 4987939 := bstep (se 1 (by rfl) ⟨3740954, by rfl⟩ : syracuseStep 4987939 = 7481909) B7481909
theorem B6650585 : Blo 1969435 6650585 := bstep (se 2 (by rfl) ⟨2493969, by rfl⟩ : syracuseStep 6650585 = 4987939) B4987939
theorem B4433723 : Blo 1969435 4433723 := bstep (se 1 (by rfl) ⟨3325292, by rfl⟩ : syracuseStep 4433723 = 6650585) B6650585
theorem B2955815 : Blo 1969435 2955815 := bstep (se 1 (by rfl) ⟨2216861, by rfl⟩ : syracuseStep 2955815 = 4433723) B4433723
theorem B1970543 : Blo 1969435 1970543 := bstep (se 1 (by rfl) ⟨1477907, by rfl⟩ : syracuseStep 1970543 = 2955815) B2955815
theorem B2955821 : Blo 1969435 2955821 := bbase (se 3 (by rfl) ⟨554216, by rfl⟩ : syracuseStep 2955821 = 1108433) (by norm_num)
theorem B1970547 : Blo 1969435 1970547 := bstep (se 1 (by rfl) ⟨1477910, by rfl⟩ : syracuseStep 1970547 = 2955821) B2955821
theorem B4433741 : Blo 1969435 4433741 := bbase (se 3 (by rfl) ⟨831326, by rfl⟩ : syracuseStep 4433741 = 1662653) (by norm_num)
theorem B2955827 : Blo 1969435 2955827 := bstep (se 1 (by rfl) ⟨2216870, by rfl⟩ : syracuseStep 2955827 = 4433741) B4433741
theorem B1970551 : Blo 1969435 1970551 := bstep (se 1 (by rfl) ⟨1477913, by rfl⟩ : syracuseStep 1970551 = 2955827) B2955827
theorem B2493985 : Blo 1969435 2493985 := bbase (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) (by norm_num)
theorem B3325313 : Blo 1969435 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2216875 : Blo 1969435 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B2955833 : Blo 1969435 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B1970555 : Blo 1969435 1970555 := bstep (se 1 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 1970555 = 2955833) B2955833
theorem B22445909 : Blo 1969435 22445909 := bbase (se 9 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 22445909 = 131519) (by norm_num)
theorem B14963939 : Blo 1969435 14963939 := bstep (se 1 (by rfl) ⟨11222954, by rfl⟩ : syracuseStep 14963939 = 22445909) B22445909
theorem B9975959 : Blo 1969435 9975959 := bstep (se 1 (by rfl) ⟨7481969, by rfl⟩ : syracuseStep 9975959 = 14963939) B14963939
theorem B6650639 : Blo 1969435 6650639 := bstep (se 1 (by rfl) ⟨4987979, by rfl⟩ : syracuseStep 6650639 = 9975959) B9975959
theorem B4433759 : Blo 1969435 4433759 := bstep (se 1 (by rfl) ⟨3325319, by rfl⟩ : syracuseStep 4433759 = 6650639) B6650639
theorem B2955839 : Blo 1969435 2955839 := bstep (se 1 (by rfl) ⟨2216879, by rfl⟩ : syracuseStep 2955839 = 4433759) B4433759
theorem B1970559 : Blo 1969435 1970559 := bstep (se 1 (by rfl) ⟨1477919, by rfl⟩ : syracuseStep 1970559 = 2955839) B2955839
theorem B2955845 : Blo 1969435 2955845 := bbase (se 4 (by rfl) ⟨277110, by rfl⟩ : syracuseStep 2955845 = 554221) (by norm_num)
theorem B1970563 : Blo 1969435 1970563 := bstep (se 1 (by rfl) ⟨1477922, by rfl⟩ : syracuseStep 1970563 = 2955845) B2955845
theorem B3325333 : Blo 1969435 3325333 := bbase (se 6 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 3325333 = 155875) (by norm_num)
theorem B4433777 : Blo 1969435 4433777 := bstep (se 2 (by rfl) ⟨1662666, by rfl⟩ : syracuseStep 4433777 = 3325333) B3325333
theorem B2955851 : Blo 1969435 2955851 := bstep (se 1 (by rfl) ⟨2216888, by rfl⟩ : syracuseStep 2955851 = 4433777) B4433777
theorem B1970567 : Blo 1969435 1970567 := bstep (se 1 (by rfl) ⟨1477925, by rfl⟩ : syracuseStep 1970567 = 2955851) B2955851
theorem B2216893 : Blo 1969435 2216893 := bbase (se 3 (by rfl) ⟨415667, by rfl⟩ : syracuseStep 2216893 = 831335) (by norm_num)
theorem B2955857 : Blo 1969435 2955857 := bstep (se 2 (by rfl) ⟨1108446, by rfl⟩ : syracuseStep 2955857 = 2216893) B2216893
theorem B1970571 : Blo 1969435 1970571 := bstep (se 1 (by rfl) ⟨1477928, by rfl⟩ : syracuseStep 1970571 = 2955857) B2955857
theorem B6650693 : Blo 1969435 6650693 := bbase (se 4 (by rfl) ⟨623502, by rfl⟩ : syracuseStep 6650693 = 1247005) (by norm_num)
theorem B4433795 : Blo 1969435 4433795 := bstep (se 1 (by rfl) ⟨3325346, by rfl⟩ : syracuseStep 4433795 = 6650693) B6650693
theorem B2955863 : Blo 1969435 2955863 := bstep (se 1 (by rfl) ⟨2216897, by rfl⟩ : syracuseStep 2955863 = 4433795) B4433795
theorem B1970575 : Blo 1969435 1970575 := bstep (se 1 (by rfl) ⟨1477931, by rfl⟩ : syracuseStep 1970575 = 2955863) B2955863
theorem B2955869 : Blo 1969435 2955869 := bbase (se 3 (by rfl) ⟨554225, by rfl⟩ : syracuseStep 2955869 = 1108451) (by norm_num)
theorem B1970579 : Blo 1969435 1970579 := bstep (se 1 (by rfl) ⟨1477934, by rfl⟩ : syracuseStep 1970579 = 2955869) B2955869
theorem B4433813 : Blo 1969435 4433813 := bbase (se 6 (by rfl) ⟨103917, by rfl⟩ : syracuseStep 4433813 = 207835) (by norm_num)
theorem B2955875 : Blo 1969435 2955875 := bstep (se 1 (by rfl) ⟨2216906, by rfl⟩ : syracuseStep 2955875 = 4433813) B4433813
theorem B1970583 : Blo 1969435 1970583 := bstep (se 1 (by rfl) ⟨1477937, by rfl⟩ : syracuseStep 1970583 = 2955875) B2955875
theorem B4208669 : Blo 1969435 4208669 := bbase (se 3 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 4208669 = 1578251) (by norm_num)
theorem B2805779 : Blo 1969435 2805779 := bstep (se 1 (by rfl) ⟨2104334, by rfl⟩ : syracuseStep 2805779 = 4208669) B4208669
theorem B7482077 : Blo 1969435 7482077 := bstep (se 3 (by rfl) ⟨1402889, by rfl⟩ : syracuseStep 7482077 = 2805779) B2805779
theorem B4988051 : Blo 1969435 4988051 := bstep (se 1 (by rfl) ⟨3741038, by rfl⟩ : syracuseStep 4988051 = 7482077) B7482077
theorem B3325367 : Blo 1969435 3325367 := bstep (se 1 (by rfl) ⟨2494025, by rfl⟩ : syracuseStep 3325367 = 4988051) B4988051
theorem B2216911 : Blo 1969435 2216911 := bstep (se 1 (by rfl) ⟨1662683, by rfl⟩ : syracuseStep 2216911 = 3325367) B3325367
theorem B2955881 : Blo 1969435 2955881 := bstep (se 2 (by rfl) ⟨1108455, by rfl⟩ : syracuseStep 2955881 = 2216911) B2216911
theorem B1970587 : Blo 1969435 1970587 := bstep (se 1 (by rfl) ⟨1477940, by rfl⟩ : syracuseStep 1970587 = 2955881) B2955881
theorem B17977301 : Blo 1969435 17977301 := bbase (se 7 (by rfl) ⟨210671, by rfl⟩ : syracuseStep 17977301 = 421343) (by norm_num)
theorem B11984867 : Blo 1969435 11984867 := bstep (se 1 (by rfl) ⟨8988650, by rfl⟩ : syracuseStep 11984867 = 17977301) B17977301
theorem B7989911 : Blo 1969435 7989911 := bstep (se 1 (by rfl) ⟨5992433, by rfl⟩ : syracuseStep 7989911 = 11984867) B11984867
theorem B5326607 : Blo 1969435 5326607 := bstep (se 1 (by rfl) ⟨3994955, by rfl⟩ : syracuseStep 5326607 = 7989911) B7989911
theorem B14204285 : Blo 1969435 14204285 := bstep (se 3 (by rfl) ⟨2663303, by rfl⟩ : syracuseStep 14204285 = 5326607) B5326607
theorem B9469523 : Blo 1969435 9469523 := bstep (se 1 (by rfl) ⟨7102142, by rfl⟩ : syracuseStep 9469523 = 14204285) B14204285
theorem B6313015 : Blo 1969435 6313015 := bstep (se 1 (by rfl) ⟨4734761, by rfl⟩ : syracuseStep 6313015 = 9469523) B9469523
theorem B8417353 : Blo 1969435 8417353 := bstep (se 2 (by rfl) ⟨3156507, by rfl⟩ : syracuseStep 8417353 = 6313015) B6313015
theorem B11223137 : Blo 1969435 11223137 := bstep (se 2 (by rfl) ⟨4208676, by rfl⟩ : syracuseStep 11223137 = 8417353) B8417353
theorem B7482091 : Blo 1969435 7482091 := bstep (se 1 (by rfl) ⟨5611568, by rfl⟩ : syracuseStep 7482091 = 11223137) B11223137
theorem B9976121 : Blo 1969435 9976121 := bstep (se 2 (by rfl) ⟨3741045, by rfl⟩ : syracuseStep 9976121 = 7482091) B7482091
theorem B6650747 : Blo 1969435 6650747 := bstep (se 1 (by rfl) ⟨4988060, by rfl⟩ : syracuseStep 6650747 = 9976121) B9976121
theorem B4433831 : Blo 1969435 4433831 := bstep (se 1 (by rfl) ⟨3325373, by rfl⟩ : syracuseStep 4433831 = 6650747) B6650747
theorem B2955887 : Blo 1969435 2955887 := bstep (se 1 (by rfl) ⟨2216915, by rfl⟩ : syracuseStep 2955887 = 4433831) B4433831
theorem B1970591 : Blo 1969435 1970591 := bstep (se 1 (by rfl) ⟨1477943, by rfl⟩ : syracuseStep 1970591 = 2955887) B2955887
theorem B2955893 : Blo 1969435 2955893 := bbase (se 5 (by rfl) ⟨138557, by rfl⟩ : syracuseStep 2955893 = 277115) (by norm_num)
theorem B1970595 : Blo 1969435 1970595 := bstep (se 1 (by rfl) ⟨1477946, by rfl⟩ : syracuseStep 1970595 = 2955893) B2955893
theorem B3741061 : Blo 1969435 3741061 := bbase (se 4 (by rfl) ⟨350724, by rfl⟩ : syracuseStep 3741061 = 701449) (by norm_num)
theorem B4988081 : Blo 1969435 4988081 := bstep (se 2 (by rfl) ⟨1870530, by rfl⟩ : syracuseStep 4988081 = 3741061) B3741061
theorem B3325387 : Blo 1969435 3325387 := bstep (se 1 (by rfl) ⟨2494040, by rfl⟩ : syracuseStep 3325387 = 4988081) B4988081
theorem B4433849 : Blo 1969435 4433849 := bstep (se 2 (by rfl) ⟨1662693, by rfl⟩ : syracuseStep 4433849 = 3325387) B3325387
theorem B2955899 : Blo 1969435 2955899 := bstep (se 1 (by rfl) ⟨2216924, by rfl⟩ : syracuseStep 2955899 = 4433849) B4433849
theorem B1970599 : Blo 1969435 1970599 := bstep (se 1 (by rfl) ⟨1477949, by rfl⟩ : syracuseStep 1970599 = 2955899) B2955899
theorem B2216929 : Blo 1969435 2216929 := bbase (se 2 (by rfl) ⟨831348, by rfl⟩ : syracuseStep 2216929 = 1662697) (by norm_num)
theorem B2955905 : Blo 1969435 2955905 := bstep (se 2 (by rfl) ⟨1108464, by rfl⟩ : syracuseStep 2955905 = 2216929) B2216929
theorem B1970603 : Blo 1969435 1970603 := bstep (se 1 (by rfl) ⟨1477952, by rfl⟩ : syracuseStep 1970603 = 2955905) B2955905
theorem B4988101 : Blo 1969435 4988101 := bbase (se 4 (by rfl) ⟨467634, by rfl⟩ : syracuseStep 4988101 = 935269) (by norm_num)
theorem B6650801 : Blo 1969435 6650801 := bstep (se 2 (by rfl) ⟨2494050, by rfl⟩ : syracuseStep 6650801 = 4988101) B4988101
theorem B4433867 : Blo 1969435 4433867 := bstep (se 1 (by rfl) ⟨3325400, by rfl⟩ : syracuseStep 4433867 = 6650801) B6650801
theorem B2955911 : Blo 1969435 2955911 := bstep (se 1 (by rfl) ⟨2216933, by rfl⟩ : syracuseStep 2955911 = 4433867) B4433867
theorem B1970607 : Blo 1969435 1970607 := bstep (se 1 (by rfl) ⟨1477955, by rfl⟩ : syracuseStep 1970607 = 2955911) B2955911
theorem B2955917 : Blo 1969435 2955917 := bbase (se 3 (by rfl) ⟨554234, by rfl⟩ : syracuseStep 2955917 = 1108469) (by norm_num)
theorem B1970611 : Blo 1969435 1970611 := bstep (se 1 (by rfl) ⟨1477958, by rfl⟩ : syracuseStep 1970611 = 2955917) B2955917
theorem B4433885 : Blo 1969435 4433885 := bbase (se 3 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 4433885 = 1662707) (by norm_num)
theorem B2955923 : Blo 1969435 2955923 := bstep (se 1 (by rfl) ⟨2216942, by rfl⟩ : syracuseStep 2955923 = 4433885) B4433885
theorem B1970615 : Blo 1969435 1970615 := bstep (se 1 (by rfl) ⟨1477961, by rfl⟩ : syracuseStep 1970615 = 2955923) B2955923
theorem B3325421 : Blo 1969435 3325421 := bbase (se 3 (by rfl) ⟨623516, by rfl⟩ : syracuseStep 3325421 = 1247033) (by norm_num)
theorem B2216947 : Blo 1969435 2216947 := bstep (se 1 (by rfl) ⟨1662710, by rfl⟩ : syracuseStep 2216947 = 3325421) B3325421
theorem B2955929 : Blo 1969435 2955929 := bstep (se 2 (by rfl) ⟨1108473, by rfl⟩ : syracuseStep 2955929 = 2216947) B2216947
theorem B1970619 : Blo 1969435 1970619 := bstep (se 1 (by rfl) ⟨1477964, by rfl⟩ : syracuseStep 1970619 = 2955929) B2955929
theorem B3995021 : Blo 1969435 3995021 := bbase (se 3 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 3995021 = 1498133) (by norm_num)
theorem B2663347 : Blo 1969435 2663347 := bstep (se 1 (by rfl) ⟨1997510, by rfl⟩ : syracuseStep 2663347 = 3995021) B3995021
theorem B3551129 : Blo 1969435 3551129 := bstep (se 2 (by rfl) ⟨1331673, by rfl⟩ : syracuseStep 3551129 = 2663347) B2663347
theorem B2367419 : Blo 1969435 2367419 := bstep (se 1 (by rfl) ⟨1775564, by rfl⟩ : syracuseStep 2367419 = 3551129) B3551129
theorem B25252469 : Blo 1969435 25252469 := bstep (se 5 (by rfl) ⟨1183709, by rfl⟩ : syracuseStep 25252469 = 2367419) B2367419
theorem B16834979 : Blo 1969435 16834979 := bstep (se 1 (by rfl) ⟨12626234, by rfl⟩ : syracuseStep 16834979 = 25252469) B25252469
theorem B11223319 : Blo 1969435 11223319 := bstep (se 1 (by rfl) ⟨8417489, by rfl⟩ : syracuseStep 11223319 = 16834979) B16834979
theorem B14964425 : Blo 1969435 14964425 := bstep (se 2 (by rfl) ⟨5611659, by rfl⟩ : syracuseStep 14964425 = 11223319) B11223319
theorem B9976283 : Blo 1969435 9976283 := bstep (se 1 (by rfl) ⟨7482212, by rfl⟩ : syracuseStep 9976283 = 14964425) B14964425
theorem B6650855 : Blo 1969435 6650855 := bstep (se 1 (by rfl) ⟨4988141, by rfl⟩ : syracuseStep 6650855 = 9976283) B9976283
theorem B4433903 : Blo 1969435 4433903 := bstep (se 1 (by rfl) ⟨3325427, by rfl⟩ : syracuseStep 4433903 = 6650855) B6650855
theorem B2955935 : Blo 1969435 2955935 := bstep (se 1 (by rfl) ⟨2216951, by rfl⟩ : syracuseStep 2955935 = 4433903) B4433903
theorem B1970623 : Blo 1969435 1970623 := bstep (se 1 (by rfl) ⟨1477967, by rfl⟩ : syracuseStep 1970623 = 2955935) B2955935
theorem B2955941 : Blo 1969435 2955941 := bbase (se 4 (by rfl) ⟨277119, by rfl⟩ : syracuseStep 2955941 = 554239) (by norm_num)
theorem B1970627 : Blo 1969435 1970627 := bstep (se 1 (by rfl) ⟨1477970, by rfl⟩ : syracuseStep 1970627 = 2955941) B2955941
theorem B2494081 : Blo 1969435 2494081 := bbase (se 2 (by rfl) ⟨935280, by rfl⟩ : syracuseStep 2494081 = 1870561) (by norm_num)
theorem B3325441 : Blo 1969435 3325441 := bstep (se 2 (by rfl) ⟨1247040, by rfl⟩ : syracuseStep 3325441 = 2494081) B2494081
theorem B4433921 : Blo 1969435 4433921 := bstep (se 2 (by rfl) ⟨1662720, by rfl⟩ : syracuseStep 4433921 = 3325441) B3325441
theorem B2955947 : Blo 1969435 2955947 := bstep (se 1 (by rfl) ⟨2216960, by rfl⟩ : syracuseStep 2955947 = 4433921) B4433921
theorem B1970631 : Blo 1969435 1970631 := bstep (se 1 (by rfl) ⟨1477973, by rfl⟩ : syracuseStep 1970631 = 2955947) B2955947
theorem B2216965 : Blo 1969435 2216965 := bbase (se 4 (by rfl) ⟨207840, by rfl⟩ : syracuseStep 2216965 = 415681) (by norm_num)
theorem B2955953 : Blo 1969435 2955953 := bstep (se 2 (by rfl) ⟨1108482, by rfl⟩ : syracuseStep 2955953 = 2216965) B2216965
theorem B1970635 : Blo 1969435 1970635 := bstep (se 1 (by rfl) ⟨1477976, by rfl⟩ : syracuseStep 1970635 = 2955953) B2955953
theorem B2805853 : Blo 1969435 2805853 := bbase (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) (by norm_num)
theorem B3741137 : Blo 1969435 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B2494091 : Blo 1969435 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B6650909 : Blo 1969435 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B4433939 : Blo 1969435 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B2955959 : Blo 1969435 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B1970639 : Blo 1969435 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B2955965 : Blo 1969435 2955965 := bbase (se 3 (by rfl) ⟨554243, by rfl⟩ : syracuseStep 2955965 = 1108487) (by norm_num)
theorem B1970643 : Blo 1969435 1970643 := bstep (se 1 (by rfl) ⟨1477982, by rfl⟩ : syracuseStep 1970643 = 2955965) B2955965
theorem B4433957 : Blo 1969435 4433957 := bbase (se 4 (by rfl) ⟨415683, by rfl⟩ : syracuseStep 4433957 = 831367) (by norm_num)
theorem B2955971 : Blo 1969435 2955971 := bstep (se 1 (by rfl) ⟨2216978, by rfl⟩ : syracuseStep 2955971 = 4433957) B4433957
theorem B1970647 : Blo 1969435 1970647 := bstep (se 1 (by rfl) ⟨1477985, by rfl⟩ : syracuseStep 1970647 = 2955971) B2955971
theorem B4988213 : Blo 1969435 4988213 := bbase (se 5 (by rfl) ⟨233822, by rfl⟩ : syracuseStep 4988213 = 467645) (by norm_num)
theorem B3325475 : Blo 1969435 3325475 := bstep (se 1 (by rfl) ⟨2494106, by rfl⟩ : syracuseStep 3325475 = 4988213) B4988213
theorem B2216983 : Blo 1969435 2216983 := bstep (se 1 (by rfl) ⟨1662737, by rfl⟩ : syracuseStep 2216983 = 3325475) B3325475
theorem B2955977 : Blo 1969435 2955977 := bstep (se 2 (by rfl) ⟨1108491, by rfl⟩ : syracuseStep 2955977 = 2216983) B2216983
theorem B1970651 : Blo 1969435 1970651 := bstep (se 1 (by rfl) ⟨1477988, by rfl⟩ : syracuseStep 1970651 = 2955977) B2955977
theorem B15980341 : Blo 1969435 15980341 := bbase (se 5 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 15980341 = 1498157) (by norm_num)
theorem B21307121 : Blo 1969435 21307121 := bstep (se 2 (by rfl) ⟨7990170, by rfl⟩ : syracuseStep 21307121 = 15980341) B15980341
theorem B14204747 : Blo 1969435 14204747 := bstep (se 1 (by rfl) ⟨10653560, by rfl⟩ : syracuseStep 14204747 = 21307121) B21307121
theorem B9469831 : Blo 1969435 9469831 := bstep (se 1 (by rfl) ⟨7102373, by rfl⟩ : syracuseStep 9469831 = 14204747) B14204747
theorem B12626441 : Blo 1969435 12626441 := bstep (se 2 (by rfl) ⟨4734915, by rfl⟩ : syracuseStep 12626441 = 9469831) B9469831
theorem B8417627 : Blo 1969435 8417627 := bstep (se 1 (by rfl) ⟨6313220, by rfl⟩ : syracuseStep 8417627 = 12626441) B12626441
theorem B5611751 : Blo 1969435 5611751 := bstep (se 1 (by rfl) ⟨4208813, by rfl⟩ : syracuseStep 5611751 = 8417627) B8417627
theorem B3741167 : Blo 1969435 3741167 := bstep (se 1 (by rfl) ⟨2805875, by rfl⟩ : syracuseStep 3741167 = 5611751) B5611751
theorem B9976445 : Blo 1969435 9976445 := bstep (se 3 (by rfl) ⟨1870583, by rfl⟩ : syracuseStep 9976445 = 3741167) B3741167
theorem B6650963 : Blo 1969435 6650963 := bstep (se 1 (by rfl) ⟨4988222, by rfl⟩ : syracuseStep 6650963 = 9976445) B9976445
theorem B4433975 : Blo 1969435 4433975 := bstep (se 1 (by rfl) ⟨3325481, by rfl⟩ : syracuseStep 4433975 = 6650963) B6650963
theorem B2955983 : Blo 1969435 2955983 := bstep (se 1 (by rfl) ⟨2216987, by rfl⟩ : syracuseStep 2955983 = 4433975) B4433975
theorem B1970655 : Blo 1969435 1970655 := bstep (se 1 (by rfl) ⟨1477991, by rfl⟩ : syracuseStep 1970655 = 2955983) B2955983
theorem B2955989 : Blo 1969435 2955989 := bbase (se 7 (by rfl) ⟨34640, by rfl⟩ : syracuseStep 2955989 = 69281) (by norm_num)
theorem B1970659 : Blo 1969435 1970659 := bstep (se 1 (by rfl) ⟨1477994, by rfl⟩ : syracuseStep 1970659 = 2955989) B2955989
theorem B2247245 : Blo 1969435 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B23970613 : Blo 1969435 23970613 := bstep (se 5 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 23970613 = 2247245) B2247245
theorem B31960817 : Blo 1969435 31960817 := bstep (se 2 (by rfl) ⟨11985306, by rfl⟩ : syracuseStep 31960817 = 23970613) B23970613
theorem B21307211 : Blo 1969435 21307211 := bstep (se 1 (by rfl) ⟨15980408, by rfl⟩ : syracuseStep 21307211 = 31960817) B31960817
theorem B14204807 : Blo 1969435 14204807 := bstep (se 1 (by rfl) ⟨10653605, by rfl⟩ : syracuseStep 14204807 = 21307211) B21307211
theorem B9469871 : Blo 1969435 9469871 := bstep (se 1 (by rfl) ⟨7102403, by rfl⟩ : syracuseStep 9469871 = 14204807) B14204807
theorem B6313247 : Blo 1969435 6313247 := bstep (se 1 (by rfl) ⟨4734935, by rfl⟩ : syracuseStep 6313247 = 9469871) B9469871
theorem B4208831 : Blo 1969435 4208831 := bstep (se 1 (by rfl) ⟨3156623, by rfl⟩ : syracuseStep 4208831 = 6313247) B6313247
theorem B2805887 : Blo 1969435 2805887 := bstep (se 1 (by rfl) ⟨2104415, by rfl⟩ : syracuseStep 2805887 = 4208831) B4208831
theorem B7482365 : Blo 1969435 7482365 := bstep (se 3 (by rfl) ⟨1402943, by rfl⟩ : syracuseStep 7482365 = 2805887) B2805887
theorem B4988243 : Blo 1969435 4988243 := bstep (se 1 (by rfl) ⟨3741182, by rfl⟩ : syracuseStep 4988243 = 7482365) B7482365
theorem B3325495 : Blo 1969435 3325495 := bstep (se 1 (by rfl) ⟨2494121, by rfl⟩ : syracuseStep 3325495 = 4988243) B4988243
theorem B4433993 : Blo 1969435 4433993 := bstep (se 2 (by rfl) ⟨1662747, by rfl⟩ : syracuseStep 4433993 = 3325495) B3325495
theorem B2955995 : Blo 1969435 2955995 := bstep (se 1 (by rfl) ⟨2216996, by rfl⟩ : syracuseStep 2955995 = 4433993) B4433993
theorem B1970663 : Blo 1969435 1970663 := bstep (se 1 (by rfl) ⟨1477997, by rfl⟩ : syracuseStep 1970663 = 2955995) B2955995
theorem B2217001 : Blo 1969435 2217001 := bbase (se 2 (by rfl) ⟨831375, by rfl⟩ : syracuseStep 2217001 = 1662751) (by norm_num)
theorem B2956001 : Blo 1969435 2956001 := bstep (se 2 (by rfl) ⟨1108500, by rfl⟩ : syracuseStep 2956001 = 2217001) B2217001
theorem B1970667 : Blo 1969435 1970667 := bstep (se 1 (by rfl) ⟨1478000, by rfl⟩ : syracuseStep 1970667 = 2956001) B2956001
theorem B4555829 : Blo 1969435 4555829 := bbase (se 5 (by rfl) ⟨213554, by rfl⟩ : syracuseStep 4555829 = 427109) (by norm_num)
theorem B3037219 : Blo 1969435 3037219 := bstep (se 1 (by rfl) ⟨2277914, by rfl⟩ : syracuseStep 3037219 = 4555829) B4555829
theorem B16198501 : Blo 1969435 16198501 := bstep (se 4 (by rfl) ⟨1518609, by rfl⟩ : syracuseStep 16198501 = 3037219) B3037219
theorem B21598001 : Blo 1969435 21598001 := bstep (se 2 (by rfl) ⟨8099250, by rfl⟩ : syracuseStep 21598001 = 16198501) B16198501
theorem B14398667 : Blo 1969435 14398667 := bstep (se 1 (by rfl) ⟨10799000, by rfl⟩ : syracuseStep 14398667 = 21598001) B21598001
theorem B9599111 : Blo 1969435 9599111 := bstep (se 1 (by rfl) ⟨7199333, by rfl⟩ : syracuseStep 9599111 = 14398667) B14398667
theorem B6399407 : Blo 1969435 6399407 := bstep (se 1 (by rfl) ⟨4799555, by rfl⟩ : syracuseStep 6399407 = 9599111) B9599111
theorem B4266271 : Blo 1969435 4266271 := bstep (se 1 (by rfl) ⟨3199703, by rfl⟩ : syracuseStep 4266271 = 6399407) B6399407
theorem B5688361 : Blo 1969435 5688361 := bstep (se 2 (by rfl) ⟨2133135, by rfl⟩ : syracuseStep 5688361 = 4266271) B4266271
theorem B7584481 : Blo 1969435 7584481 := bstep (se 2 (by rfl) ⟨2844180, by rfl⟩ : syracuseStep 7584481 = 5688361) B5688361
theorem B40450565 : Blo 1969435 40450565 := bstep (se 4 (by rfl) ⟨3792240, by rfl⟩ : syracuseStep 40450565 = 7584481) B7584481
theorem B26967043 : Blo 1969435 26967043 := bstep (se 1 (by rfl) ⟨20225282, by rfl⟩ : syracuseStep 26967043 = 40450565) B40450565
theorem B35956057 : Blo 1969435 35956057 := bstep (se 2 (by rfl) ⟨13483521, by rfl⟩ : syracuseStep 35956057 = 26967043) B26967043
theorem B47941409 : Blo 1969435 47941409 := bstep (se 2 (by rfl) ⟨17978028, by rfl⟩ : syracuseStep 47941409 = 35956057) B35956057
theorem B31960939 : Blo 1969435 31960939 := bstep (se 1 (by rfl) ⟨23970704, by rfl⟩ : syracuseStep 31960939 = 47941409) B47941409
theorem B42614585 : Blo 1969435 42614585 := bstep (se 2 (by rfl) ⟨15980469, by rfl⟩ : syracuseStep 42614585 = 31960939) B31960939
theorem B28409723 : Blo 1969435 28409723 := bstep (se 1 (by rfl) ⟨21307292, by rfl⟩ : syracuseStep 28409723 = 42614585) B42614585
theorem B18939815 : Blo 1969435 18939815 := bstep (se 1 (by rfl) ⟨14204861, by rfl⟩ : syracuseStep 18939815 = 28409723) B28409723
theorem B12626543 : Blo 1969435 12626543 := bstep (se 1 (by rfl) ⟨9469907, by rfl⟩ : syracuseStep 12626543 = 18939815) B18939815
theorem B8417695 : Blo 1969435 8417695 := bstep (se 1 (by rfl) ⟨6313271, by rfl⟩ : syracuseStep 8417695 = 12626543) B12626543
theorem B11223593 : Blo 1969435 11223593 := bstep (se 2 (by rfl) ⟨4208847, by rfl⟩ : syracuseStep 11223593 = 8417695) B8417695
theorem B7482395 : Blo 1969435 7482395 := bstep (se 1 (by rfl) ⟨5611796, by rfl⟩ : syracuseStep 7482395 = 11223593) B11223593
theorem B4988263 : Blo 1969435 4988263 := bstep (se 1 (by rfl) ⟨3741197, by rfl⟩ : syracuseStep 4988263 = 7482395) B7482395
theorem B6651017 : Blo 1969435 6651017 := bstep (se 2 (by rfl) ⟨2494131, by rfl⟩ : syracuseStep 6651017 = 4988263) B4988263
theorem B4434011 : Blo 1969435 4434011 := bstep (se 1 (by rfl) ⟨3325508, by rfl⟩ : syracuseStep 4434011 = 6651017) B6651017
theorem B2956007 : Blo 1969435 2956007 := bstep (se 1 (by rfl) ⟨2217005, by rfl⟩ : syracuseStep 2956007 = 4434011) B4434011
theorem B1970671 : Blo 1969435 1970671 := bstep (se 1 (by rfl) ⟨1478003, by rfl⟩ : syracuseStep 1970671 = 2956007) B2956007
theorem B2956013 : Blo 1969435 2956013 := bbase (se 3 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 2956013 = 1108505) (by norm_num)
theorem B1970675 : Blo 1969435 1970675 := bstep (se 1 (by rfl) ⟨1478006, by rfl⟩ : syracuseStep 1970675 = 2956013) B2956013
theorem B4434029 : Blo 1969435 4434029 := bbase (se 3 (by rfl) ⟨831380, by rfl⟩ : syracuseStep 4434029 = 1662761) (by norm_num)
theorem B2956019 : Blo 1969435 2956019 := bstep (se 1 (by rfl) ⟨2217014, by rfl⟩ : syracuseStep 2956019 = 4434029) B4434029
theorem B1970679 : Blo 1969435 1970679 := bstep (se 1 (by rfl) ⟨1478009, by rfl⟩ : syracuseStep 1970679 = 2956019) B2956019
theorem B3741221 : Blo 1969435 3741221 := bbase (se 4 (by rfl) ⟨350739, by rfl⟩ : syracuseStep 3741221 = 701479) (by norm_num)
theorem B2494147 : Blo 1969435 2494147 := bstep (se 1 (by rfl) ⟨1870610, by rfl⟩ : syracuseStep 2494147 = 3741221) B3741221
theorem B3325529 : Blo 1969435 3325529 := bstep (se 2 (by rfl) ⟨1247073, by rfl⟩ : syracuseStep 3325529 = 2494147) B2494147
theorem B2217019 : Blo 1969435 2217019 := bstep (se 1 (by rfl) ⟨1662764, by rfl⟩ : syracuseStep 2217019 = 3325529) B3325529
theorem B2956025 : Blo 1969435 2956025 := bstep (se 2 (by rfl) ⟨1108509, by rfl⟩ : syracuseStep 2956025 = 2217019) B2217019
theorem B1970683 : Blo 1969435 1970683 := bstep (se 1 (by rfl) ⟨1478012, by rfl⟩ : syracuseStep 1970683 = 2956025) B2956025
theorem B5125349 : Blo 1969435 5125349 := bbase (se 4 (by rfl) ⟨480501, by rfl⟩ : syracuseStep 5125349 = 961003) (by norm_num)
theorem B3416899 : Blo 1969435 3416899 := bstep (se 1 (by rfl) ⟨2562674, by rfl⟩ : syracuseStep 3416899 = 5125349) B5125349
theorem B4555865 : Blo 1969435 4555865 := bstep (se 2 (by rfl) ⟨1708449, by rfl⟩ : syracuseStep 4555865 = 3416899) B3416899
theorem B12148973 : Blo 1969435 12148973 := bstep (se 3 (by rfl) ⟨2277932, by rfl⟩ : syracuseStep 12148973 = 4555865) B4555865
theorem B8099315 : Blo 1969435 8099315 := bstep (se 1 (by rfl) ⟨6074486, by rfl⟩ : syracuseStep 8099315 = 12148973) B12148973
theorem B5399543 : Blo 1969435 5399543 := bstep (se 1 (by rfl) ⟨4049657, by rfl⟩ : syracuseStep 5399543 = 8099315) B8099315
theorem B3599695 : Blo 1969435 3599695 := bstep (se 1 (by rfl) ⟨2699771, by rfl⟩ : syracuseStep 3599695 = 5399543) B5399543
theorem B4799593 : Blo 1969435 4799593 := bstep (se 2 (by rfl) ⟨1799847, by rfl⟩ : syracuseStep 4799593 = 3599695) B3599695
theorem B25597829 : Blo 1969435 25597829 := bstep (se 4 (by rfl) ⟨2399796, by rfl⟩ : syracuseStep 25597829 = 4799593) B4799593
theorem B68260877 : Blo 1969435 68260877 := bstep (se 3 (by rfl) ⟨12798914, by rfl⟩ : syracuseStep 68260877 = 25597829) B25597829
theorem B45507251 : Blo 1969435 45507251 := bstep (se 1 (by rfl) ⟨34130438, by rfl⟩ : syracuseStep 45507251 = 68260877) B68260877
theorem B30338167 : Blo 1969435 30338167 := bstep (se 1 (by rfl) ⟨22753625, by rfl⟩ : syracuseStep 30338167 = 45507251) B45507251
theorem B40450889 : Blo 1969435 40450889 := bstep (se 2 (by rfl) ⟨15169083, by rfl⟩ : syracuseStep 40450889 = 30338167) B30338167
theorem B26967259 : Blo 1969435 26967259 := bstep (se 1 (by rfl) ⟨20225444, by rfl⟩ : syracuseStep 26967259 = 40450889) B40450889
theorem B35956345 : Blo 1969435 35956345 := bstep (se 2 (by rfl) ⟨13483629, by rfl⟩ : syracuseStep 35956345 = 26967259) B26967259
theorem B47941793 : Blo 1969435 47941793 := bstep (se 2 (by rfl) ⟨17978172, by rfl⟩ : syracuseStep 47941793 = 35956345) B35956345
theorem B31961195 : Blo 1969435 31961195 := bstep (se 1 (by rfl) ⟨23970896, by rfl⟩ : syracuseStep 31961195 = 47941793) B47941793
theorem B21307463 : Blo 1969435 21307463 := bstep (se 1 (by rfl) ⟨15980597, by rfl⟩ : syracuseStep 21307463 = 31961195) B31961195
theorem B14204975 : Blo 1969435 14204975 := bstep (se 1 (by rfl) ⟨10653731, by rfl⟩ : syracuseStep 14204975 = 21307463) B21307463
theorem B37879933 : Blo 1969435 37879933 := bstep (se 3 (by rfl) ⟨7102487, by rfl⟩ : syracuseStep 37879933 = 14204975) B14204975
theorem B50506577 : Blo 1969435 50506577 := bstep (se 2 (by rfl) ⟨18939966, by rfl⟩ : syracuseStep 50506577 = 37879933) B37879933
theorem B33671051 : Blo 1969435 33671051 := bstep (se 1 (by rfl) ⟨25253288, by rfl⟩ : syracuseStep 33671051 = 50506577) B50506577
theorem B22447367 : Blo 1969435 22447367 := bstep (se 1 (by rfl) ⟨16835525, by rfl⟩ : syracuseStep 22447367 = 33671051) B33671051
theorem B14964911 : Blo 1969435 14964911 := bstep (se 1 (by rfl) ⟨11223683, by rfl⟩ : syracuseStep 14964911 = 22447367) B22447367
theorem B9976607 : Blo 1969435 9976607 := bstep (se 1 (by rfl) ⟨7482455, by rfl⟩ : syracuseStep 9976607 = 14964911) B14964911
theorem B6651071 : Blo 1969435 6651071 := bstep (se 1 (by rfl) ⟨4988303, by rfl⟩ : syracuseStep 6651071 = 9976607) B9976607
theorem B4434047 : Blo 1969435 4434047 := bstep (se 1 (by rfl) ⟨3325535, by rfl⟩ : syracuseStep 4434047 = 6651071) B6651071
theorem B2956031 : Blo 1969435 2956031 := bstep (se 1 (by rfl) ⟨2217023, by rfl⟩ : syracuseStep 2956031 = 4434047) B4434047
theorem B1970687 : Blo 1969435 1970687 := bstep (se 1 (by rfl) ⟨1478015, by rfl⟩ : syracuseStep 1970687 = 2956031) B2956031
theorem B2956037 : Blo 1969435 2956037 := bbase (se 4 (by rfl) ⟨277128, by rfl⟩ : syracuseStep 2956037 = 554257) (by norm_num)
theorem B1970691 : Blo 1969435 1970691 := bstep (se 1 (by rfl) ⟨1478018, by rfl⟩ : syracuseStep 1970691 = 2956037) B2956037
theorem B3325549 : Blo 1969435 3325549 := bbase (se 3 (by rfl) ⟨623540, by rfl⟩ : syracuseStep 3325549 = 1247081) (by norm_num)
theorem B4434065 : Blo 1969435 4434065 := bstep (se 2 (by rfl) ⟨1662774, by rfl⟩ : syracuseStep 4434065 = 3325549) B3325549
theorem B2956043 : Blo 1969435 2956043 := bstep (se 1 (by rfl) ⟨2217032, by rfl⟩ : syracuseStep 2956043 = 4434065) B4434065
theorem B1970695 : Blo 1969435 1970695 := bstep (se 1 (by rfl) ⟨1478021, by rfl⟩ : syracuseStep 1970695 = 2956043) B2956043
theorem B2217037 : Blo 1969435 2217037 := bbase (se 3 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 2217037 = 831389) (by norm_num)
theorem B2956049 : Blo 1969435 2956049 := bstep (se 2 (by rfl) ⟨1108518, by rfl⟩ : syracuseStep 2956049 = 2217037) B2217037
theorem B1970699 : Blo 1969435 1970699 := bstep (se 1 (by rfl) ⟨1478024, by rfl⟩ : syracuseStep 1970699 = 2956049) B2956049
theorem B6651125 : Blo 1969435 6651125 := bbase (se 5 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 6651125 = 623543) (by norm_num)
theorem B4434083 : Blo 1969435 4434083 := bstep (se 1 (by rfl) ⟨3325562, by rfl⟩ : syracuseStep 4434083 = 6651125) B6651125
theorem B2956055 : Blo 1969435 2956055 := bstep (se 1 (by rfl) ⟨2217041, by rfl⟩ : syracuseStep 2956055 = 4434083) B4434083
theorem B1970703 : Blo 1969435 1970703 := bstep (se 1 (by rfl) ⟨1478027, by rfl⟩ : syracuseStep 1970703 = 2956055) B2956055
theorem B2956061 : Blo 1969435 2956061 := bbase (se 3 (by rfl) ⟨554261, by rfl⟩ : syracuseStep 2956061 = 1108523) (by norm_num)
theorem B1970707 : Blo 1969435 1970707 := bstep (se 1 (by rfl) ⟨1478030, by rfl⟩ : syracuseStep 1970707 = 2956061) B2956061
theorem B4434101 : Blo 1969435 4434101 := bbase (se 5 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 4434101 = 415697) (by norm_num)
theorem B2956067 : Blo 1969435 2956067 := bstep (se 1 (by rfl) ⟨2217050, by rfl⟩ : syracuseStep 2956067 = 4434101) B4434101
theorem B1970711 : Blo 1969435 1970711 := bstep (se 1 (by rfl) ⟨1478033, by rfl⟩ : syracuseStep 1970711 = 2956067) B2956067
theorem B4735061 : Blo 1969435 4735061 := bbase (se 8 (by rfl) ⟨27744, by rfl⟩ : syracuseStep 4735061 = 55489) (by norm_num)
theorem B3156707 : Blo 1969435 3156707 := bstep (se 1 (by rfl) ⟨2367530, by rfl⟩ : syracuseStep 3156707 = 4735061) B4735061
theorem B2104471 : Blo 1969435 2104471 := bstep (se 1 (by rfl) ⟨1578353, by rfl⟩ : syracuseStep 2104471 = 3156707) B3156707
theorem B11223845 : Blo 1969435 11223845 := bstep (se 4 (by rfl) ⟨1052235, by rfl⟩ : syracuseStep 11223845 = 2104471) B2104471
theorem B7482563 : Blo 1969435 7482563 := bstep (se 1 (by rfl) ⟨5611922, by rfl⟩ : syracuseStep 7482563 = 11223845) B11223845
theorem B4988375 : Blo 1969435 4988375 := bstep (se 1 (by rfl) ⟨3741281, by rfl⟩ : syracuseStep 4988375 = 7482563) B7482563
theorem B3325583 : Blo 1969435 3325583 := bstep (se 1 (by rfl) ⟨2494187, by rfl⟩ : syracuseStep 3325583 = 4988375) B4988375
theorem B2217055 : Blo 1969435 2217055 := bstep (se 1 (by rfl) ⟨1662791, by rfl⟩ : syracuseStep 2217055 = 3325583) B3325583
theorem B2956073 : Blo 1969435 2956073 := bstep (se 2 (by rfl) ⟨1108527, by rfl⟩ : syracuseStep 2956073 = 2217055) B2217055
theorem B1970715 : Blo 1969435 1970715 := bstep (se 1 (by rfl) ⟨1478036, by rfl⟩ : syracuseStep 1970715 = 2956073) B2956073
theorem B3332549 : Blo 1969435 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B8886797 : Blo 1969435 8886797 := bstep (se 3 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 8886797 = 3332549) B3332549
theorem B5924531 : Blo 1969435 5924531 := bstep (se 1 (by rfl) ⟨4443398, by rfl⟩ : syracuseStep 5924531 = 8886797) B8886797
theorem B3949687 : Blo 1969435 3949687 := bstep (se 1 (by rfl) ⟨2962265, by rfl⟩ : syracuseStep 3949687 = 5924531) B5924531
theorem B21064997 : Blo 1969435 21064997 := bstep (se 4 (by rfl) ⟨1974843, by rfl⟩ : syracuseStep 21064997 = 3949687) B3949687
theorem B14043331 : Blo 1969435 14043331 := bstep (se 1 (by rfl) ⟨10532498, by rfl⟩ : syracuseStep 14043331 = 21064997) B21064997
theorem B18724441 : Blo 1969435 18724441 := bstep (se 2 (by rfl) ⟨7021665, by rfl⟩ : syracuseStep 18724441 = 14043331) B14043331
theorem B24965921 : Blo 1969435 24965921 := bstep (se 2 (by rfl) ⟨9362220, by rfl⟩ : syracuseStep 24965921 = 18724441) B18724441
theorem B66575789 : Blo 1969435 66575789 := bstep (se 3 (by rfl) ⟨12482960, by rfl⟩ : syracuseStep 66575789 = 24965921) B24965921
theorem B44383859 : Blo 1969435 44383859 := bstep (se 1 (by rfl) ⟨33287894, by rfl⟩ : syracuseStep 44383859 = 66575789) B66575789
theorem B29589239 : Blo 1969435 29589239 := bstep (se 1 (by rfl) ⟨22191929, by rfl⟩ : syracuseStep 29589239 = 44383859) B44383859
theorem B78904637 : Blo 1969435 78904637 := bstep (se 3 (by rfl) ⟨14794619, by rfl⟩ : syracuseStep 78904637 = 29589239) B29589239
theorem B52603091 : Blo 1969435 52603091 := bstep (se 1 (by rfl) ⟨39452318, by rfl⟩ : syracuseStep 52603091 = 78904637) B78904637
theorem B35068727 : Blo 1969435 35068727 := bstep (se 1 (by rfl) ⟨26301545, by rfl⟩ : syracuseStep 35068727 = 52603091) B52603091
theorem B23379151 : Blo 1969435 23379151 := bstep (se 1 (by rfl) ⟨17534363, by rfl⟩ : syracuseStep 23379151 = 35068727) B35068727
theorem B31172201 : Blo 1969435 31172201 := bstep (se 2 (by rfl) ⟨11689575, by rfl⟩ : syracuseStep 31172201 = 23379151) B23379151
theorem B20781467 : Blo 1969435 20781467 := bstep (se 1 (by rfl) ⟨15586100, by rfl⟩ : syracuseStep 20781467 = 31172201) B31172201
theorem B13854311 : Blo 1969435 13854311 := bstep (se 1 (by rfl) ⟨10390733, by rfl⟩ : syracuseStep 13854311 = 20781467) B20781467
theorem B9236207 : Blo 1969435 9236207 := bstep (se 1 (by rfl) ⟨6927155, by rfl⟩ : syracuseStep 9236207 = 13854311) B13854311
theorem B6157471 : Blo 1969435 6157471 := bstep (se 1 (by rfl) ⟨4618103, by rfl⟩ : syracuseStep 6157471 = 9236207) B9236207
theorem B8209961 : Blo 1969435 8209961 := bstep (se 2 (by rfl) ⟨3078735, by rfl⟩ : syracuseStep 8209961 = 6157471) B6157471
theorem B5473307 : Blo 1969435 5473307 := bstep (se 1 (by rfl) ⟨4104980, by rfl⟩ : syracuseStep 5473307 = 8209961) B8209961
theorem B3648871 : Blo 1969435 3648871 := bstep (se 1 (by rfl) ⟨2736653, by rfl⟩ : syracuseStep 3648871 = 5473307) B5473307
theorem B19460645 : Blo 1969435 19460645 := bstep (se 4 (by rfl) ⟨1824435, by rfl⟩ : syracuseStep 19460645 = 3648871) B3648871
theorem B12973763 : Blo 1969435 12973763 := bstep (se 1 (by rfl) ⟨9730322, by rfl⟩ : syracuseStep 12973763 = 19460645) B19460645
theorem B8649175 : Blo 1969435 8649175 := bstep (se 1 (by rfl) ⟨6486881, by rfl⟩ : syracuseStep 8649175 = 12973763) B12973763
theorem B11532233 : Blo 1969435 11532233 := bstep (se 2 (by rfl) ⟨4324587, by rfl⟩ : syracuseStep 11532233 = 8649175) B8649175
theorem B7688155 : Blo 1969435 7688155 := bstep (se 1 (by rfl) ⟨5766116, by rfl⟩ : syracuseStep 7688155 = 11532233) B11532233
theorem B10250873 : Blo 1969435 10250873 := bstep (se 2 (by rfl) ⟨3844077, by rfl⟩ : syracuseStep 10250873 = 7688155) B7688155
theorem B6833915 : Blo 1969435 6833915 := bstep (se 1 (by rfl) ⟨5125436, by rfl⟩ : syracuseStep 6833915 = 10250873) B10250873
theorem B4555943 : Blo 1969435 4555943 := bstep (se 1 (by rfl) ⟨3416957, by rfl⟩ : syracuseStep 4555943 = 6833915) B6833915
theorem B3037295 : Blo 1969435 3037295 := bstep (se 1 (by rfl) ⟨2277971, by rfl⟩ : syracuseStep 3037295 = 4555943) B4555943
theorem B2024863 : Blo 1969435 2024863 := bstep (se 1 (by rfl) ⟨1518647, by rfl⟩ : syracuseStep 2024863 = 3037295) B3037295
theorem B43197077 : Blo 1969435 43197077 := bstep (se 6 (by rfl) ⟨1012431, by rfl⟩ : syracuseStep 43197077 = 2024863) B2024863
theorem B28798051 : Blo 1969435 28798051 := bstep (se 1 (by rfl) ⟨21598538, by rfl⟩ : syracuseStep 28798051 = 43197077) B43197077
theorem B38397401 : Blo 1969435 38397401 := bstep (se 2 (by rfl) ⟨14399025, by rfl⟩ : syracuseStep 38397401 = 28798051) B28798051
theorem B25598267 : Blo 1969435 25598267 := bstep (se 1 (by rfl) ⟨19198700, by rfl⟩ : syracuseStep 25598267 = 38397401) B38397401
theorem B17065511 : Blo 1969435 17065511 := bstep (se 1 (by rfl) ⟨12799133, by rfl⟩ : syracuseStep 17065511 = 25598267) B25598267
theorem B11377007 : Blo 1969435 11377007 := bstep (se 1 (by rfl) ⟨8532755, by rfl⟩ : syracuseStep 11377007 = 17065511) B17065511
theorem B7584671 : Blo 1969435 7584671 := bstep (se 1 (by rfl) ⟨5688503, by rfl⟩ : syracuseStep 7584671 = 11377007) B11377007
theorem B5056447 : Blo 1969435 5056447 := bstep (se 1 (by rfl) ⟨3792335, by rfl⟩ : syracuseStep 5056447 = 7584671) B7584671
theorem B6741929 : Blo 1969435 6741929 := bstep (se 2 (by rfl) ⟨2528223, by rfl⟩ : syracuseStep 6741929 = 5056447) B5056447
theorem B4494619 : Blo 1969435 4494619 := bstep (se 1 (by rfl) ⟨3370964, by rfl⟩ : syracuseStep 4494619 = 6741929) B6741929
theorem B5992825 : Blo 1969435 5992825 := bstep (se 2 (by rfl) ⟨2247309, by rfl⟩ : syracuseStep 5992825 = 4494619) B4494619
theorem B7990433 : Blo 1969435 7990433 := bstep (se 2 (by rfl) ⟨2996412, by rfl⟩ : syracuseStep 7990433 = 5992825) B5992825
theorem B5326955 : Blo 1969435 5326955 := bstep (se 1 (by rfl) ⟨3995216, by rfl⟩ : syracuseStep 5326955 = 7990433) B7990433
theorem B3551303 : Blo 1969435 3551303 := bstep (se 1 (by rfl) ⟨2663477, by rfl⟩ : syracuseStep 3551303 = 5326955) B5326955
theorem B2367535 : Blo 1969435 2367535 := bstep (se 1 (by rfl) ⟨1775651, by rfl⟩ : syracuseStep 2367535 = 3551303) B3551303
theorem B3156713 : Blo 1969435 3156713 := bstep (se 2 (by rfl) ⟨1183767, by rfl⟩ : syracuseStep 3156713 = 2367535) B2367535
theorem B2104475 : Blo 1969435 2104475 := bstep (se 1 (by rfl) ⟨1578356, by rfl⟩ : syracuseStep 2104475 = 3156713) B3156713
theorem B5611933 : Blo 1969435 5611933 := bstep (se 3 (by rfl) ⟨1052237, by rfl⟩ : syracuseStep 5611933 = 2104475) B2104475
theorem B7482577 : Blo 1969435 7482577 := bstep (se 2 (by rfl) ⟨2805966, by rfl⟩ : syracuseStep 7482577 = 5611933) B5611933
theorem B9976769 : Blo 1969435 9976769 := bstep (se 2 (by rfl) ⟨3741288, by rfl⟩ : syracuseStep 9976769 = 7482577) B7482577
theorem B6651179 : Blo 1969435 6651179 := bstep (se 1 (by rfl) ⟨4988384, by rfl⟩ : syracuseStep 6651179 = 9976769) B9976769
theorem B4434119 : Blo 1969435 4434119 := bstep (se 1 (by rfl) ⟨3325589, by rfl⟩ : syracuseStep 4434119 = 6651179) B6651179
theorem B2956079 : Blo 1969435 2956079 := bstep (se 1 (by rfl) ⟨2217059, by rfl⟩ : syracuseStep 2956079 = 4434119) B4434119
theorem B1970719 : Blo 1969435 1970719 := bstep (se 1 (by rfl) ⟨1478039, by rfl⟩ : syracuseStep 1970719 = 2956079) B2956079
theorem B2956085 : Blo 1969435 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B1970723 : Blo 1969435 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B4988405 : Blo 1969435 4988405 := bbase (se 5 (by rfl) ⟨233831, by rfl⟩ : syracuseStep 4988405 = 467663) (by norm_num)
theorem B3325603 : Blo 1969435 3325603 := bstep (se 1 (by rfl) ⟨2494202, by rfl⟩ : syracuseStep 3325603 = 4988405) B4988405
theorem B4434137 : Blo 1969435 4434137 := bstep (se 2 (by rfl) ⟨1662801, by rfl⟩ : syracuseStep 4434137 = 3325603) B3325603
theorem B2956091 : Blo 1969435 2956091 := bstep (se 1 (by rfl) ⟨2217068, by rfl⟩ : syracuseStep 2956091 = 4434137) B4434137
theorem B1970727 : Blo 1969435 1970727 := bstep (se 1 (by rfl) ⟨1478045, by rfl⟩ : syracuseStep 1970727 = 2956091) B2956091
theorem B2217073 : Blo 1969435 2217073 := bbase (se 2 (by rfl) ⟨831402, by rfl⟩ : syracuseStep 2217073 = 1662805) (by norm_num)
theorem B2956097 : Blo 1969435 2956097 := bstep (se 2 (by rfl) ⟨1108536, by rfl⟩ : syracuseStep 2956097 = 2217073) B2217073
theorem B1970731 : Blo 1969435 1970731 := bstep (se 1 (by rfl) ⟨1478048, by rfl⟩ : syracuseStep 1970731 = 2956097) B2956097
theorem B6313477 : Blo 1969435 6313477 := bbase (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) (by norm_num)
theorem B8417969 : Blo 1969435 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B5611979 : Blo 1969435 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B3741319 : Blo 1969435 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B4988425 : Blo 1969435 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B6651233 : Blo 1969435 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B4434155 : Blo 1969435 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B2956103 : Blo 1969435 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B1970735 : Blo 1969435 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B2956109 : Blo 1969435 2956109 := bbase (se 3 (by rfl) ⟨554270, by rfl⟩ : syracuseStep 2956109 = 1108541) (by norm_num)
theorem B1970739 : Blo 1969435 1970739 := bstep (se 1 (by rfl) ⟨1478054, by rfl⟩ : syracuseStep 1970739 = 2956109) B2956109
theorem B4434173 : Blo 1969435 4434173 := bbase (se 3 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 4434173 = 1662815) (by norm_num)
theorem B2956115 : Blo 1969435 2956115 := bstep (se 1 (by rfl) ⟨2217086, by rfl⟩ : syracuseStep 2956115 = 4434173) B4434173
theorem B1970743 : Blo 1969435 1970743 := bstep (se 1 (by rfl) ⟨1478057, by rfl⟩ : syracuseStep 1970743 = 2956115) B2956115
theorem B3325637 : Blo 1969435 3325637 := bbase (se 4 (by rfl) ⟨311778, by rfl⟩ : syracuseStep 3325637 = 623557) (by norm_num)
theorem B2217091 : Blo 1969435 2217091 := bstep (se 1 (by rfl) ⟨1662818, by rfl⟩ : syracuseStep 2217091 = 3325637) B3325637
theorem B2956121 : Blo 1969435 2956121 := bstep (se 2 (by rfl) ⟨1108545, by rfl⟩ : syracuseStep 2956121 = 2217091) B2217091
theorem B1970747 : Blo 1969435 1970747 := bstep (se 1 (by rfl) ⟨1478060, by rfl⟩ : syracuseStep 1970747 = 2956121) B2956121
theorem B14965397 : Blo 1969435 14965397 := bbase (se 6 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 14965397 = 701503) (by norm_num)
theorem B9976931 : Blo 1969435 9976931 := bstep (se 1 (by rfl) ⟨7482698, by rfl⟩ : syracuseStep 9976931 = 14965397) B14965397
theorem B6651287 : Blo 1969435 6651287 := bstep (se 1 (by rfl) ⟨4988465, by rfl⟩ : syracuseStep 6651287 = 9976931) B9976931
theorem B4434191 : Blo 1969435 4434191 := bstep (se 1 (by rfl) ⟨3325643, by rfl⟩ : syracuseStep 4434191 = 6651287) B6651287
theorem B2956127 : Blo 1969435 2956127 := bstep (se 1 (by rfl) ⟨2217095, by rfl⟩ : syracuseStep 2956127 = 4434191) B4434191
theorem B1970751 : Blo 1969435 1970751 := bstep (se 1 (by rfl) ⟨1478063, by rfl⟩ : syracuseStep 1970751 = 2956127) B2956127
theorem B2956133 : Blo 1969435 2956133 := bbase (se 4 (by rfl) ⟨277137, by rfl⟩ : syracuseStep 2956133 = 554275) (by norm_num)
theorem B1970755 : Blo 1969435 1970755 := bstep (se 1 (by rfl) ⟨1478066, by rfl⟩ : syracuseStep 1970755 = 2956133) B2956133
theorem B3741365 : Blo 1969435 3741365 := bbase (se 5 (by rfl) ⟨175376, by rfl⟩ : syracuseStep 3741365 = 350753) (by norm_num)
theorem B2494243 : Blo 1969435 2494243 := bstep (se 1 (by rfl) ⟨1870682, by rfl⟩ : syracuseStep 2494243 = 3741365) B3741365
theorem B3325657 : Blo 1969435 3325657 := bstep (se 2 (by rfl) ⟨1247121, by rfl⟩ : syracuseStep 3325657 = 2494243) B2494243
theorem B4434209 : Blo 1969435 4434209 := bstep (se 2 (by rfl) ⟨1662828, by rfl⟩ : syracuseStep 4434209 = 3325657) B3325657
theorem B2956139 : Blo 1969435 2956139 := bstep (se 1 (by rfl) ⟨2217104, by rfl⟩ : syracuseStep 2956139 = 4434209) B4434209
theorem B1970759 : Blo 1969435 1970759 := bstep (se 1 (by rfl) ⟨1478069, by rfl⟩ : syracuseStep 1970759 = 2956139) B2956139
theorem B2217109 : Blo 1969435 2217109 := bbase (se 6 (by rfl) ⟨51963, by rfl⟩ : syracuseStep 2217109 = 103927) (by norm_num)
theorem B2956145 : Blo 1969435 2956145 := bstep (se 2 (by rfl) ⟨1108554, by rfl⟩ : syracuseStep 2956145 = 2217109) B2217109
theorem B1970763 : Blo 1969435 1970763 := bstep (se 1 (by rfl) ⟨1478072, by rfl⟩ : syracuseStep 1970763 = 2956145) B2956145
theorem B2494253 : Blo 1969435 2494253 := bbase (se 3 (by rfl) ⟨467672, by rfl⟩ : syracuseStep 2494253 = 935345) (by norm_num)
theorem B6651341 : Blo 1969435 6651341 := bstep (se 3 (by rfl) ⟨1247126, by rfl⟩ : syracuseStep 6651341 = 2494253) B2494253
theorem B4434227 : Blo 1969435 4434227 := bstep (se 1 (by rfl) ⟨3325670, by rfl⟩ : syracuseStep 4434227 = 6651341) B6651341
theorem B2956151 : Blo 1969435 2956151 := bstep (se 1 (by rfl) ⟨2217113, by rfl⟩ : syracuseStep 2956151 = 4434227) B4434227
theorem B1970767 : Blo 1969435 1970767 := bstep (se 1 (by rfl) ⟨1478075, by rfl⟩ : syracuseStep 1970767 = 2956151) B2956151
theorem B2956157 : Blo 1969435 2956157 := bbase (se 3 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 2956157 = 1108559) (by norm_num)
theorem B1970771 : Blo 1969435 1970771 := bstep (se 1 (by rfl) ⟨1478078, by rfl⟩ : syracuseStep 1970771 = 2956157) B2956157
theorem B4434245 : Blo 1969435 4434245 := bbase (se 4 (by rfl) ⟨415710, by rfl⟩ : syracuseStep 4434245 = 831421) (by norm_num)
theorem B2956163 : Blo 1969435 2956163 := bstep (se 1 (by rfl) ⟨2217122, by rfl⟩ : syracuseStep 2956163 = 4434245) B4434245
theorem B1970775 : Blo 1969435 1970775 := bstep (se 1 (by rfl) ⟨1478081, by rfl⟩ : syracuseStep 1970775 = 2956163) B2956163
theorem B1997669 : Blo 1969435 1997669 := bbase (se 4 (by rfl) ⟨187281, by rfl⟩ : syracuseStep 1997669 = 374563) (by norm_num)
theorem B5327117 : Blo 1969435 5327117 := bstep (se 3 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 5327117 = 1997669) B1997669
theorem B3551411 : Blo 1969435 3551411 := bstep (se 1 (by rfl) ⟨2663558, by rfl⟩ : syracuseStep 3551411 = 5327117) B5327117
theorem B9470429 : Blo 1969435 9470429 := bstep (se 3 (by rfl) ⟨1775705, by rfl⟩ : syracuseStep 9470429 = 3551411) B3551411
theorem B6313619 : Blo 1969435 6313619 := bstep (se 1 (by rfl) ⟨4735214, by rfl⟩ : syracuseStep 6313619 = 9470429) B9470429
theorem B4209079 : Blo 1969435 4209079 := bstep (se 1 (by rfl) ⟨3156809, by rfl⟩ : syracuseStep 4209079 = 6313619) B6313619
theorem B5612105 : Blo 1969435 5612105 := bstep (se 2 (by rfl) ⟨2104539, by rfl⟩ : syracuseStep 5612105 = 4209079) B4209079
theorem B3741403 : Blo 1969435 3741403 := bstep (se 1 (by rfl) ⟨2806052, by rfl⟩ : syracuseStep 3741403 = 5612105) B5612105
theorem B4988537 : Blo 1969435 4988537 := bstep (se 2 (by rfl) ⟨1870701, by rfl⟩ : syracuseStep 4988537 = 3741403) B3741403
theorem B3325691 : Blo 1969435 3325691 := bstep (se 1 (by rfl) ⟨2494268, by rfl⟩ : syracuseStep 3325691 = 4988537) B4988537
theorem B2217127 : Blo 1969435 2217127 := bstep (se 1 (by rfl) ⟨1662845, by rfl⟩ : syracuseStep 2217127 = 3325691) B3325691
theorem B2956169 : Blo 1969435 2956169 := bstep (se 2 (by rfl) ⟨1108563, by rfl⟩ : syracuseStep 2956169 = 2217127) B2217127
theorem B1970779 : Blo 1969435 1970779 := bstep (se 1 (by rfl) ⟨1478084, by rfl⟩ : syracuseStep 1970779 = 2956169) B2956169
theorem B9977093 : Blo 1969435 9977093 := bbase (se 4 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 9977093 = 1870705) (by norm_num)
theorem B6651395 : Blo 1969435 6651395 := bstep (se 1 (by rfl) ⟨4988546, by rfl⟩ : syracuseStep 6651395 = 9977093) B9977093
theorem B4434263 : Blo 1969435 4434263 := bstep (se 1 (by rfl) ⟨3325697, by rfl⟩ : syracuseStep 4434263 = 6651395) B6651395
theorem B2956175 : Blo 1969435 2956175 := bstep (se 1 (by rfl) ⟨2217131, by rfl⟩ : syracuseStep 2956175 = 4434263) B4434263
theorem B1970783 : Blo 1969435 1970783 := bstep (se 1 (by rfl) ⟨1478087, by rfl⟩ : syracuseStep 1970783 = 2956175) B2956175
theorem B2956181 : Blo 1969435 2956181 := bbase (se 6 (by rfl) ⟨69285, by rfl⟩ : syracuseStep 2956181 = 138571) (by norm_num)
theorem B1970787 : Blo 1969435 1970787 := bstep (se 1 (by rfl) ⟨1478090, by rfl⟩ : syracuseStep 1970787 = 2956181) B2956181
theorem B11224277 : Blo 1969435 11224277 := bbase (se 7 (by rfl) ⟨131534, by rfl⟩ : syracuseStep 11224277 = 263069) (by norm_num)
theorem B7482851 : Blo 1969435 7482851 := bstep (se 1 (by rfl) ⟨5612138, by rfl⟩ : syracuseStep 7482851 = 11224277) B11224277
theorem B4988567 : Blo 1969435 4988567 := bstep (se 1 (by rfl) ⟨3741425, by rfl⟩ : syracuseStep 4988567 = 7482851) B7482851
theorem B3325711 : Blo 1969435 3325711 := bstep (se 1 (by rfl) ⟨2494283, by rfl⟩ : syracuseStep 3325711 = 4988567) B4988567
theorem B4434281 : Blo 1969435 4434281 := bstep (se 2 (by rfl) ⟨1662855, by rfl⟩ : syracuseStep 4434281 = 3325711) B3325711
theorem B2956187 : Blo 1969435 2956187 := bstep (se 1 (by rfl) ⟨2217140, by rfl⟩ : syracuseStep 2956187 = 4434281) B4434281
theorem B1970791 : Blo 1969435 1970791 := bstep (se 1 (by rfl) ⟨1478093, by rfl⟩ : syracuseStep 1970791 = 2956187) B2956187
theorem B2217145 : Blo 1969435 2217145 := bbase (se 2 (by rfl) ⟨831429, by rfl⟩ : syracuseStep 2217145 = 1662859) (by norm_num)
theorem B2956193 : Blo 1969435 2956193 := bstep (se 2 (by rfl) ⟨1108572, by rfl⟩ : syracuseStep 2956193 = 2217145) B2217145
theorem B1970795 : Blo 1969435 1970795 := bstep (se 1 (by rfl) ⟨1478096, by rfl⟩ : syracuseStep 1970795 = 2956193) B2956193
theorem B7990757 : Blo 1969435 7990757 := bbase (se 4 (by rfl) ⟨749133, by rfl⟩ : syracuseStep 7990757 = 1498267) (by norm_num)
theorem B5327171 : Blo 1969435 5327171 := bstep (se 1 (by rfl) ⟨3995378, by rfl⟩ : syracuseStep 5327171 = 7990757) B7990757
theorem B3551447 : Blo 1969435 3551447 := bstep (se 1 (by rfl) ⟨2663585, by rfl⟩ : syracuseStep 3551447 = 5327171) B5327171
theorem B2367631 : Blo 1969435 2367631 := bstep (se 1 (by rfl) ⟨1775723, by rfl⟩ : syracuseStep 2367631 = 3551447) B3551447
theorem B3156841 : Blo 1969435 3156841 := bstep (se 2 (by rfl) ⟨1183815, by rfl⟩ : syracuseStep 3156841 = 2367631) B2367631
theorem B4209121 : Blo 1969435 4209121 := bstep (se 2 (by rfl) ⟨1578420, by rfl⟩ : syracuseStep 4209121 = 3156841) B3156841
theorem B5612161 : Blo 1969435 5612161 := bstep (se 2 (by rfl) ⟨2104560, by rfl⟩ : syracuseStep 5612161 = 4209121) B4209121
theorem B7482881 : Blo 1969435 7482881 := bstep (se 2 (by rfl) ⟨2806080, by rfl⟩ : syracuseStep 7482881 = 5612161) B5612161
theorem B4988587 : Blo 1969435 4988587 := bstep (se 1 (by rfl) ⟨3741440, by rfl⟩ : syracuseStep 4988587 = 7482881) B7482881
theorem B6651449 : Blo 1969435 6651449 := bstep (se 2 (by rfl) ⟨2494293, by rfl⟩ : syracuseStep 6651449 = 4988587) B4988587
theorem B4434299 : Blo 1969435 4434299 := bstep (se 1 (by rfl) ⟨3325724, by rfl⟩ : syracuseStep 4434299 = 6651449) B6651449
theorem B2956199 : Blo 1969435 2956199 := bstep (se 1 (by rfl) ⟨2217149, by rfl⟩ : syracuseStep 2956199 = 4434299) B4434299
theorem B1970799 : Blo 1969435 1970799 := bstep (se 1 (by rfl) ⟨1478099, by rfl⟩ : syracuseStep 1970799 = 2956199) B2956199
theorem B2956205 : Blo 1969435 2956205 := bbase (se 3 (by rfl) ⟨554288, by rfl⟩ : syracuseStep 2956205 = 1108577) (by norm_num)
theorem B1970803 : Blo 1969435 1970803 := bstep (se 1 (by rfl) ⟨1478102, by rfl⟩ : syracuseStep 1970803 = 2956205) B2956205
theorem B4434317 : Blo 1969435 4434317 := bbase (se 3 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 4434317 = 1662869) (by norm_num)
theorem B2956211 : Blo 1969435 2956211 := bstep (se 1 (by rfl) ⟨2217158, by rfl⟩ : syracuseStep 2956211 = 4434317) B4434317
theorem B1970807 : Blo 1969435 1970807 := bstep (se 1 (by rfl) ⟨1478105, by rfl⟩ : syracuseStep 1970807 = 2956211) B2956211
theorem B2494309 : Blo 1969435 2494309 := bbase (se 4 (by rfl) ⟨233841, by rfl⟩ : syracuseStep 2494309 = 467683) (by norm_num)
theorem B3325745 : Blo 1969435 3325745 := bstep (se 2 (by rfl) ⟨1247154, by rfl⟩ : syracuseStep 3325745 = 2494309) B2494309
theorem B2217163 : Blo 1969435 2217163 := bstep (se 1 (by rfl) ⟨1662872, by rfl⟩ : syracuseStep 2217163 = 3325745) B3325745
theorem B2956217 : Blo 1969435 2956217 := bstep (se 2 (by rfl) ⟨1108581, by rfl⟩ : syracuseStep 2956217 = 2217163) B2217163
theorem B1970811 : Blo 1969435 1970811 := bstep (se 1 (by rfl) ⟨1478108, by rfl⟩ : syracuseStep 1970811 = 2956217) B2956217
theorem B7102949 : Blo 1969435 7102949 := bbase (se 4 (by rfl) ⟨665901, by rfl⟩ : syracuseStep 7102949 = 1331803) (by norm_num)
theorem B18941197 : Blo 1969435 18941197 := bstep (se 3 (by rfl) ⟨3551474, by rfl⟩ : syracuseStep 18941197 = 7102949) B7102949
theorem B25254929 : Blo 1969435 25254929 := bstep (se 2 (by rfl) ⟨9470598, by rfl⟩ : syracuseStep 25254929 = 18941197) B18941197
theorem B16836619 : Blo 1969435 16836619 := bstep (se 1 (by rfl) ⟨12627464, by rfl⟩ : syracuseStep 16836619 = 25254929) B25254929
theorem B22448825 : Blo 1969435 22448825 := bstep (se 2 (by rfl) ⟨8418309, by rfl⟩ : syracuseStep 22448825 = 16836619) B16836619
theorem B14965883 : Blo 1969435 14965883 := bstep (se 1 (by rfl) ⟨11224412, by rfl⟩ : syracuseStep 14965883 = 22448825) B22448825
theorem B9977255 : Blo 1969435 9977255 := bstep (se 1 (by rfl) ⟨7482941, by rfl⟩ : syracuseStep 9977255 = 14965883) B14965883
theorem B6651503 : Blo 1969435 6651503 := bstep (se 1 (by rfl) ⟨4988627, by rfl⟩ : syracuseStep 6651503 = 9977255) B9977255
theorem B4434335 : Blo 1969435 4434335 := bstep (se 1 (by rfl) ⟨3325751, by rfl⟩ : syracuseStep 4434335 = 6651503) B6651503
theorem B2956223 : Blo 1969435 2956223 := bstep (se 1 (by rfl) ⟨2217167, by rfl⟩ : syracuseStep 2956223 = 4434335) B4434335
theorem B1970815 : Blo 1969435 1970815 := bstep (se 1 (by rfl) ⟨1478111, by rfl⟩ : syracuseStep 1970815 = 2956223) B2956223
theorem B2956229 : Blo 1969435 2956229 := bbase (se 4 (by rfl) ⟨277146, by rfl⟩ : syracuseStep 2956229 = 554293) (by norm_num)
theorem B1970819 : Blo 1969435 1970819 := bstep (se 1 (by rfl) ⟨1478114, by rfl⟩ : syracuseStep 1970819 = 2956229) B2956229
theorem B3325765 : Blo 1969435 3325765 := bbase (se 4 (by rfl) ⟨311790, by rfl⟩ : syracuseStep 3325765 = 623581) (by norm_num)
theorem B4434353 : Blo 1969435 4434353 := bstep (se 2 (by rfl) ⟨1662882, by rfl⟩ : syracuseStep 4434353 = 3325765) B3325765
theorem B2956235 : Blo 1969435 2956235 := bstep (se 1 (by rfl) ⟨2217176, by rfl⟩ : syracuseStep 2956235 = 4434353) B4434353
theorem B1970823 : Blo 1969435 1970823 := bstep (se 1 (by rfl) ⟨1478117, by rfl⟩ : syracuseStep 1970823 = 2956235) B2956235
theorem B2217181 : Blo 1969435 2217181 := bbase (se 3 (by rfl) ⟨415721, by rfl⟩ : syracuseStep 2217181 = 831443) (by norm_num)
theorem B2956241 : Blo 1969435 2956241 := bstep (se 2 (by rfl) ⟨1108590, by rfl⟩ : syracuseStep 2956241 = 2217181) B2217181
theorem B1970827 : Blo 1969435 1970827 := bstep (se 1 (by rfl) ⟨1478120, by rfl⟩ : syracuseStep 1970827 = 2956241) B2956241
theorem B6651557 : Blo 1969435 6651557 := bbase (se 4 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 6651557 = 1247167) (by norm_num)
theorem B4434371 : Blo 1969435 4434371 := bstep (se 1 (by rfl) ⟨3325778, by rfl⟩ : syracuseStep 4434371 = 6651557) B6651557
theorem B2956247 : Blo 1969435 2956247 := bstep (se 1 (by rfl) ⟨2217185, by rfl⟩ : syracuseStep 2956247 = 4434371) B4434371
theorem B1970831 : Blo 1969435 1970831 := bstep (se 1 (by rfl) ⟨1478123, by rfl⟩ : syracuseStep 1970831 = 2956247) B2956247
theorem B2956253 : Blo 1969435 2956253 := bbase (se 3 (by rfl) ⟨554297, by rfl⟩ : syracuseStep 2956253 = 1108595) (by norm_num)
theorem B1970835 : Blo 1969435 1970835 := bstep (se 1 (by rfl) ⟨1478126, by rfl⟩ : syracuseStep 1970835 = 2956253) B2956253
theorem B4434389 : Blo 1969435 4434389 := bbase (se 7 (by rfl) ⟨51965, by rfl⟩ : syracuseStep 4434389 = 103931) (by norm_num)
theorem B2956259 : Blo 1969435 2956259 := bstep (se 1 (by rfl) ⟨2217194, by rfl⟩ : syracuseStep 2956259 = 4434389) B4434389
theorem B1970839 : Blo 1969435 1970839 := bstep (se 1 (by rfl) ⟨1478129, by rfl⟩ : syracuseStep 1970839 = 2956259) B2956259
theorem B40454101 : Blo 1969435 40454101 := bbase (se 7 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 40454101 = 948143) (by norm_num)
theorem B53938801 : Blo 1969435 53938801 := bstep (se 2 (by rfl) ⟨20227050, by rfl⟩ : syracuseStep 53938801 = 40454101) B40454101
theorem B71918401 : Blo 1969435 71918401 := bstep (se 2 (by rfl) ⟨26969400, by rfl⟩ : syracuseStep 71918401 = 53938801) B53938801
theorem B95891201 : Blo 1969435 95891201 := bstep (se 2 (by rfl) ⟨35959200, by rfl⟩ : syracuseStep 95891201 = 71918401) B71918401
theorem B63927467 : Blo 1969435 63927467 := bstep (se 1 (by rfl) ⟨47945600, by rfl⟩ : syracuseStep 63927467 = 95891201) B95891201
theorem B42618311 : Blo 1969435 42618311 := bstep (se 1 (by rfl) ⟨31963733, by rfl⟩ : syracuseStep 42618311 = 63927467) B63927467
theorem B28412207 : Blo 1969435 28412207 := bstep (se 1 (by rfl) ⟨21309155, by rfl⟩ : syracuseStep 28412207 = 42618311) B42618311
theorem B18941471 : Blo 1969435 18941471 := bstep (se 1 (by rfl) ⟨14206103, by rfl⟩ : syracuseStep 18941471 = 28412207) B28412207
theorem B12627647 : Blo 1969435 12627647 := bstep (se 1 (by rfl) ⟨9470735, by rfl⟩ : syracuseStep 12627647 = 18941471) B18941471
theorem B8418431 : Blo 1969435 8418431 := bstep (se 1 (by rfl) ⟨6313823, by rfl⟩ : syracuseStep 8418431 = 12627647) B12627647
theorem B5612287 : Blo 1969435 5612287 := bstep (se 1 (by rfl) ⟨4209215, by rfl⟩ : syracuseStep 5612287 = 8418431) B8418431
theorem B7483049 : Blo 1969435 7483049 := bstep (se 2 (by rfl) ⟨2806143, by rfl⟩ : syracuseStep 7483049 = 5612287) B5612287
theorem B4988699 : Blo 1969435 4988699 := bstep (se 1 (by rfl) ⟨3741524, by rfl⟩ : syracuseStep 4988699 = 7483049) B7483049
theorem B3325799 : Blo 1969435 3325799 := bstep (se 1 (by rfl) ⟨2494349, by rfl⟩ : syracuseStep 3325799 = 4988699) B4988699
theorem B2217199 : Blo 1969435 2217199 := bstep (se 1 (by rfl) ⟨1662899, by rfl⟩ : syracuseStep 2217199 = 3325799) B3325799
theorem B2956265 : Blo 1969435 2956265 := bstep (se 2 (by rfl) ⟨1108599, by rfl⟩ : syracuseStep 2956265 = 2217199) B2217199
theorem B1970843 : Blo 1969435 1970843 := bstep (se 1 (by rfl) ⟨1478132, by rfl⟩ : syracuseStep 1970843 = 2956265) B2956265
theorem B7990949 : Blo 1969435 7990949 := bbase (se 4 (by rfl) ⟨749151, by rfl⟩ : syracuseStep 7990949 = 1498303) (by norm_num)
theorem B5327299 : Blo 1969435 5327299 := bstep (se 1 (by rfl) ⟨3995474, by rfl⟩ : syracuseStep 5327299 = 7990949) B7990949
theorem B7103065 : Blo 1969435 7103065 := bstep (se 2 (by rfl) ⟨2663649, by rfl⟩ : syracuseStep 7103065 = 5327299) B5327299
theorem B9470753 : Blo 1969435 9470753 := bstep (se 2 (by rfl) ⟨3551532, by rfl⟩ : syracuseStep 9470753 = 7103065) B7103065
theorem B6313835 : Blo 1969435 6313835 := bstep (se 1 (by rfl) ⟨4735376, by rfl⟩ : syracuseStep 6313835 = 9470753) B9470753
theorem B16836893 : Blo 1969435 16836893 := bstep (se 3 (by rfl) ⟨3156917, by rfl⟩ : syracuseStep 16836893 = 6313835) B6313835
theorem B11224595 : Blo 1969435 11224595 := bstep (se 1 (by rfl) ⟨8418446, by rfl⟩ : syracuseStep 11224595 = 16836893) B16836893
theorem B7483063 : Blo 1969435 7483063 := bstep (se 1 (by rfl) ⟨5612297, by rfl⟩ : syracuseStep 7483063 = 11224595) B11224595
theorem B9977417 : Blo 1969435 9977417 := bstep (se 2 (by rfl) ⟨3741531, by rfl⟩ : syracuseStep 9977417 = 7483063) B7483063
theorem B6651611 : Blo 1969435 6651611 := bstep (se 1 (by rfl) ⟨4988708, by rfl⟩ : syracuseStep 6651611 = 9977417) B9977417
theorem B4434407 : Blo 1969435 4434407 := bstep (se 1 (by rfl) ⟨3325805, by rfl⟩ : syracuseStep 4434407 = 6651611) B6651611
theorem B2956271 : Blo 1969435 2956271 := bstep (se 1 (by rfl) ⟨2217203, by rfl⟩ : syracuseStep 2956271 = 4434407) B4434407
theorem B1970847 : Blo 1969435 1970847 := bstep (se 1 (by rfl) ⟨1478135, by rfl⟩ : syracuseStep 1970847 = 2956271) B2956271
theorem B2956277 : Blo 1969435 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B1970851 : Blo 1969435 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B4735397 : Blo 1969435 4735397 := bbase (se 4 (by rfl) ⟨443943, by rfl⟩ : syracuseStep 4735397 = 887887) (by norm_num)
theorem B3156931 : Blo 1969435 3156931 := bstep (se 1 (by rfl) ⟨2367698, by rfl⟩ : syracuseStep 3156931 = 4735397) B4735397
theorem B4209241 : Blo 1969435 4209241 := bstep (se 2 (by rfl) ⟨1578465, by rfl⟩ : syracuseStep 4209241 = 3156931) B3156931
theorem B5612321 : Blo 1969435 5612321 := bstep (se 2 (by rfl) ⟨2104620, by rfl⟩ : syracuseStep 5612321 = 4209241) B4209241
theorem B3741547 : Blo 1969435 3741547 := bstep (se 1 (by rfl) ⟨2806160, by rfl⟩ : syracuseStep 3741547 = 5612321) B5612321
theorem B4988729 : Blo 1969435 4988729 := bstep (se 2 (by rfl) ⟨1870773, by rfl⟩ : syracuseStep 4988729 = 3741547) B3741547
theorem B3325819 : Blo 1969435 3325819 := bstep (se 1 (by rfl) ⟨2494364, by rfl⟩ : syracuseStep 3325819 = 4988729) B4988729
theorem B4434425 : Blo 1969435 4434425 := bstep (se 2 (by rfl) ⟨1662909, by rfl⟩ : syracuseStep 4434425 = 3325819) B3325819
theorem B2956283 : Blo 1969435 2956283 := bstep (se 1 (by rfl) ⟨2217212, by rfl⟩ : syracuseStep 2956283 = 4434425) B4434425
theorem B1970855 : Blo 1969435 1970855 := bstep (se 1 (by rfl) ⟨1478141, by rfl⟩ : syracuseStep 1970855 = 2956283) B2956283
theorem B2217217 : Blo 1969435 2217217 := bbase (se 2 (by rfl) ⟨831456, by rfl⟩ : syracuseStep 2217217 = 1662913) (by norm_num)
theorem B2956289 : Blo 1969435 2956289 := bstep (se 2 (by rfl) ⟨1108608, by rfl⟩ : syracuseStep 2956289 = 2217217) B2217217
theorem B1970859 : Blo 1969435 1970859 := bstep (se 1 (by rfl) ⟨1478144, by rfl⟩ : syracuseStep 1970859 = 2956289) B2956289
theorem B4988749 : Blo 1969435 4988749 := bbase (se 3 (by rfl) ⟨935390, by rfl⟩ : syracuseStep 4988749 = 1870781) (by norm_num)
theorem B6651665 : Blo 1969435 6651665 := bstep (se 2 (by rfl) ⟨2494374, by rfl⟩ : syracuseStep 6651665 = 4988749) B4988749
theorem B4434443 : Blo 1969435 4434443 := bstep (se 1 (by rfl) ⟨3325832, by rfl⟩ : syracuseStep 4434443 = 6651665) B6651665
theorem B2956295 : Blo 1969435 2956295 := bstep (se 1 (by rfl) ⟨2217221, by rfl⟩ : syracuseStep 2956295 = 4434443) B4434443
theorem B1970863 : Blo 1969435 1970863 := bstep (se 1 (by rfl) ⟨1478147, by rfl⟩ : syracuseStep 1970863 = 2956295) B2956295
theorem B2956301 : Blo 1969435 2956301 := bbase (se 3 (by rfl) ⟨554306, by rfl⟩ : syracuseStep 2956301 = 1108613) (by norm_num)
theorem B1970867 : Blo 1969435 1970867 := bstep (se 1 (by rfl) ⟨1478150, by rfl⟩ : syracuseStep 1970867 = 2956301) B2956301
theorem B4434461 : Blo 1969435 4434461 := bbase (se 3 (by rfl) ⟨831461, by rfl⟩ : syracuseStep 4434461 = 1662923) (by norm_num)
theorem B2956307 : Blo 1969435 2956307 := bstep (se 1 (by rfl) ⟨2217230, by rfl⟩ : syracuseStep 2956307 = 4434461) B4434461
theorem B1970871 : Blo 1969435 1970871 := bstep (se 1 (by rfl) ⟨1478153, by rfl⟩ : syracuseStep 1970871 = 2956307) B2956307
theorem B3325853 : Blo 1969435 3325853 := bbase (se 3 (by rfl) ⟨623597, by rfl⟩ : syracuseStep 3325853 = 1247195) (by norm_num)
theorem B2217235 : Blo 1969435 2217235 := bstep (se 1 (by rfl) ⟨1662926, by rfl⟩ : syracuseStep 2217235 = 3325853) B3325853
theorem B2956313 : Blo 1969435 2956313 := bstep (se 2 (by rfl) ⟨1108617, by rfl⟩ : syracuseStep 2956313 = 2217235) B2217235
theorem B1970875 : Blo 1969435 1970875 := bstep (se 1 (by rfl) ⟨1478156, by rfl⟩ : syracuseStep 1970875 = 2956313) B2956313
theorem B18941813 : Blo 1969435 18941813 := bbase (se 5 (by rfl) ⟨887897, by rfl⟩ : syracuseStep 18941813 = 1775795) (by norm_num)
theorem B12627875 : Blo 1969435 12627875 := bstep (se 1 (by rfl) ⟨9470906, by rfl⟩ : syracuseStep 12627875 = 18941813) B18941813
theorem B8418583 : Blo 1969435 8418583 := bstep (se 1 (by rfl) ⟨6313937, by rfl⟩ : syracuseStep 8418583 = 12627875) B12627875
theorem B11224777 : Blo 1969435 11224777 := bstep (se 2 (by rfl) ⟨4209291, by rfl⟩ : syracuseStep 11224777 = 8418583) B8418583
theorem B14966369 : Blo 1969435 14966369 := bstep (se 2 (by rfl) ⟨5612388, by rfl⟩ : syracuseStep 14966369 = 11224777) B11224777
theorem B9977579 : Blo 1969435 9977579 := bstep (se 1 (by rfl) ⟨7483184, by rfl⟩ : syracuseStep 9977579 = 14966369) B14966369
theorem B6651719 : Blo 1969435 6651719 := bstep (se 1 (by rfl) ⟨4988789, by rfl⟩ : syracuseStep 6651719 = 9977579) B9977579
theorem B4434479 : Blo 1969435 4434479 := bstep (se 1 (by rfl) ⟨3325859, by rfl⟩ : syracuseStep 4434479 = 6651719) B6651719
theorem B2956319 : Blo 1969435 2956319 := bstep (se 1 (by rfl) ⟨2217239, by rfl⟩ : syracuseStep 2956319 = 4434479) B4434479
theorem B1970879 : Blo 1969435 1970879 := bstep (se 1 (by rfl) ⟨1478159, by rfl⟩ : syracuseStep 1970879 = 2956319) B2956319
theorem B2956325 : Blo 1969435 2956325 := bbase (se 4 (by rfl) ⟨277155, by rfl⟩ : syracuseStep 2956325 = 554311) (by norm_num)
theorem B1970883 : Blo 1969435 1970883 := bstep (se 1 (by rfl) ⟨1478162, by rfl⟩ : syracuseStep 1970883 = 2956325) B2956325
theorem B2494405 : Blo 1969435 2494405 := bbase (se 4 (by rfl) ⟨233850, by rfl⟩ : syracuseStep 2494405 = 467701) (by norm_num)
theorem B3325873 : Blo 1969435 3325873 := bstep (se 2 (by rfl) ⟨1247202, by rfl⟩ : syracuseStep 3325873 = 2494405) B2494405
theorem B4434497 : Blo 1969435 4434497 := bstep (se 2 (by rfl) ⟨1662936, by rfl⟩ : syracuseStep 4434497 = 3325873) B3325873
theorem B2956331 : Blo 1969435 2956331 := bstep (se 1 (by rfl) ⟨2217248, by rfl⟩ : syracuseStep 2956331 = 4434497) B4434497
theorem B1970887 : Blo 1969435 1970887 := bstep (se 1 (by rfl) ⟨1478165, by rfl⟩ : syracuseStep 1970887 = 2956331) B2956331
theorem B2217253 : Blo 1969435 2217253 := bbase (se 4 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 2217253 = 415735) (by norm_num)
theorem B2956337 : Blo 1969435 2956337 := bstep (se 2 (by rfl) ⟨1108626, by rfl⟩ : syracuseStep 2956337 = 2217253) B2217253
theorem B1970891 : Blo 1969435 1970891 := bstep (se 1 (by rfl) ⟨1478168, by rfl⟩ : syracuseStep 1970891 = 2956337) B2956337
theorem B4735493 : Blo 1969435 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B3156995 : Blo 1969435 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B8418653 : Blo 1969435 8418653 := bstep (se 3 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 8418653 = 3156995) B3156995
theorem B5612435 : Blo 1969435 5612435 := bstep (se 1 (by rfl) ⟨4209326, by rfl⟩ : syracuseStep 5612435 = 8418653) B8418653
theorem B3741623 : Blo 1969435 3741623 := bstep (se 1 (by rfl) ⟨2806217, by rfl⟩ : syracuseStep 3741623 = 5612435) B5612435
theorem B2494415 : Blo 1969435 2494415 := bstep (se 1 (by rfl) ⟨1870811, by rfl⟩ : syracuseStep 2494415 = 3741623) B3741623
theorem B6651773 : Blo 1969435 6651773 := bstep (se 3 (by rfl) ⟨1247207, by rfl⟩ : syracuseStep 6651773 = 2494415) B2494415
theorem B4434515 : Blo 1969435 4434515 := bstep (se 1 (by rfl) ⟨3325886, by rfl⟩ : syracuseStep 4434515 = 6651773) B6651773
theorem B2956343 : Blo 1969435 2956343 := bstep (se 1 (by rfl) ⟨2217257, by rfl⟩ : syracuseStep 2956343 = 4434515) B4434515
theorem B1970895 : Blo 1969435 1970895 := bstep (se 1 (by rfl) ⟨1478171, by rfl⟩ : syracuseStep 1970895 = 2956343) B2956343
theorem B2956349 : Blo 1969435 2956349 := bbase (se 3 (by rfl) ⟨554315, by rfl⟩ : syracuseStep 2956349 = 1108631) (by norm_num)
theorem B1970899 : Blo 1969435 1970899 := bstep (se 1 (by rfl) ⟨1478174, by rfl⟩ : syracuseStep 1970899 = 2956349) B2956349
theorem B4434533 : Blo 1969435 4434533 := bbase (se 4 (by rfl) ⟨415737, by rfl⟩ : syracuseStep 4434533 = 831475) (by norm_num)
theorem B2956355 : Blo 1969435 2956355 := bstep (se 1 (by rfl) ⟨2217266, by rfl⟩ : syracuseStep 2956355 = 4434533) B4434533
theorem B1970903 : Blo 1969435 1970903 := bstep (se 1 (by rfl) ⟨1478177, by rfl⟩ : syracuseStep 1970903 = 2956355) B2956355
theorem B4988861 : Blo 1969435 4988861 := bbase (se 3 (by rfl) ⟨935411, by rfl⟩ : syracuseStep 4988861 = 1870823) (by norm_num)
theorem B3325907 : Blo 1969435 3325907 := bstep (se 1 (by rfl) ⟨2494430, by rfl⟩ : syracuseStep 3325907 = 4988861) B4988861
theorem B2217271 : Blo 1969435 2217271 := bstep (se 1 (by rfl) ⟨1662953, by rfl⟩ : syracuseStep 2217271 = 3325907) B3325907
theorem B2956361 : Blo 1969435 2956361 := bstep (se 2 (by rfl) ⟨1108635, by rfl⟩ : syracuseStep 2956361 = 2217271) B2217271
theorem B1970907 : Blo 1969435 1970907 := bstep (se 1 (by rfl) ⟨1478180, by rfl⟩ : syracuseStep 1970907 = 2956361) B2956361
theorem B3741653 : Blo 1969435 3741653 := bbase (se 7 (by rfl) ⟨43847, by rfl⟩ : syracuseStep 3741653 = 87695) (by norm_num)
theorem B9977741 : Blo 1969435 9977741 := bstep (se 3 (by rfl) ⟨1870826, by rfl⟩ : syracuseStep 9977741 = 3741653) B3741653
theorem B6651827 : Blo 1969435 6651827 := bstep (se 1 (by rfl) ⟨4988870, by rfl⟩ : syracuseStep 6651827 = 9977741) B9977741
theorem B4434551 : Blo 1969435 4434551 := bstep (se 1 (by rfl) ⟨3325913, by rfl⟩ : syracuseStep 4434551 = 6651827) B6651827
theorem B2956367 : Blo 1969435 2956367 := bstep (se 1 (by rfl) ⟨2217275, by rfl⟩ : syracuseStep 2956367 = 4434551) B4434551
theorem B1970911 : Blo 1969435 1970911 := bstep (se 1 (by rfl) ⟨1478183, by rfl⟩ : syracuseStep 1970911 = 2956367) B2956367
theorem B2956373 : Blo 1969435 2956373 := bbase (se 8 (by rfl) ⟨17322, by rfl⟩ : syracuseStep 2956373 = 34645) (by norm_num)
theorem B1970915 : Blo 1969435 1970915 := bstep (se 1 (by rfl) ⟨1478186, by rfl⟩ : syracuseStep 1970915 = 2956373) B2956373
theorem B8990149 : Blo 1969435 8990149 := bbase (se 4 (by rfl) ⟨842826, by rfl⟩ : syracuseStep 8990149 = 1685653) (by norm_num)
theorem B11986865 : Blo 1969435 11986865 := bstep (se 2 (by rfl) ⟨4495074, by rfl⟩ : syracuseStep 11986865 = 8990149) B8990149
theorem B7991243 : Blo 1969435 7991243 := bstep (se 1 (by rfl) ⟨5993432, by rfl⟩ : syracuseStep 7991243 = 11986865) B11986865
theorem B5327495 : Blo 1969435 5327495 := bstep (se 1 (by rfl) ⟨3995621, by rfl⟩ : syracuseStep 5327495 = 7991243) B7991243
theorem B3551663 : Blo 1969435 3551663 := bstep (se 1 (by rfl) ⟨2663747, by rfl⟩ : syracuseStep 3551663 = 5327495) B5327495
theorem B2367775 : Blo 1969435 2367775 := bstep (se 1 (by rfl) ⟨1775831, by rfl⟩ : syracuseStep 2367775 = 3551663) B3551663
theorem B12628133 : Blo 1969435 12628133 := bstep (se 4 (by rfl) ⟨1183887, by rfl⟩ : syracuseStep 12628133 = 2367775) B2367775
theorem B8418755 : Blo 1969435 8418755 := bstep (se 1 (by rfl) ⟨6314066, by rfl⟩ : syracuseStep 8418755 = 12628133) B12628133
theorem B5612503 : Blo 1969435 5612503 := bstep (se 1 (by rfl) ⟨4209377, by rfl⟩ : syracuseStep 5612503 = 8418755) B8418755
theorem B7483337 : Blo 1969435 7483337 := bstep (se 2 (by rfl) ⟨2806251, by rfl⟩ : syracuseStep 7483337 = 5612503) B5612503
theorem B4988891 : Blo 1969435 4988891 := bstep (se 1 (by rfl) ⟨3741668, by rfl⟩ : syracuseStep 4988891 = 7483337) B7483337
theorem B3325927 : Blo 1969435 3325927 := bstep (se 1 (by rfl) ⟨2494445, by rfl⟩ : syracuseStep 3325927 = 4988891) B4988891
theorem B4434569 : Blo 1969435 4434569 := bstep (se 2 (by rfl) ⟨1662963, by rfl⟩ : syracuseStep 4434569 = 3325927) B3325927
theorem B2956379 : Blo 1969435 2956379 := bstep (se 1 (by rfl) ⟨2217284, by rfl⟩ : syracuseStep 2956379 = 4434569) B4434569
theorem B1970919 : Blo 1969435 1970919 := bstep (se 1 (by rfl) ⟨1478189, by rfl⟩ : syracuseStep 1970919 = 2956379) B2956379
theorem B2217289 : Blo 1969435 2217289 := bbase (se 2 (by rfl) ⟨831483, by rfl⟩ : syracuseStep 2217289 = 1662967) (by norm_num)
theorem B2956385 : Blo 1969435 2956385 := bstep (se 2 (by rfl) ⟨1108644, by rfl⟩ : syracuseStep 2956385 = 2217289) B2217289
theorem B1970923 : Blo 1969435 1970923 := bstep (se 1 (by rfl) ⟨1478192, by rfl⟩ : syracuseStep 1970923 = 2956385) B2956385
theorem B2700101 : Blo 1969435 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B7200269 : Blo 1969435 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B4800179 : Blo 1969435 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B12800477 : Blo 1969435 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B34134605 : Blo 1969435 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B22756403 : Blo 1969435 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B15170935 : Blo 1969435 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B20227913 : Blo 1969435 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B13485275 : Blo 1969435 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B8990183 : Blo 1969435 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B5993455 : Blo 1969435 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B7991273 : Blo 1969435 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B5327515 : Blo 1969435 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B28413413 : Blo 1969435 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B18942275 : Blo 1969435 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B12628183 : Blo 1969435 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B16837577 : Blo 1969435 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B11225051 : Blo 1969435 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B7483367 : Blo 1969435 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B4988911 : Blo 1969435 4988911 := bstep (se 1 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 4988911 = 7483367) B7483367
theorem B6651881 : Blo 1969435 6651881 := bstep (se 2 (by rfl) ⟨2494455, by rfl⟩ : syracuseStep 6651881 = 4988911) B4988911
theorem B4434587 : Blo 1969435 4434587 := bstep (se 1 (by rfl) ⟨3325940, by rfl⟩ : syracuseStep 4434587 = 6651881) B6651881
theorem B2956391 : Blo 1969435 2956391 := bstep (se 1 (by rfl) ⟨2217293, by rfl⟩ : syracuseStep 2956391 = 4434587) B4434587
theorem B1970927 : Blo 1969435 1970927 := bstep (se 1 (by rfl) ⟨1478195, by rfl⟩ : syracuseStep 1970927 = 2956391) B2956391
theorem B2956397 : Blo 1969435 2956397 := bbase (se 3 (by rfl) ⟨554324, by rfl⟩ : syracuseStep 2956397 = 1108649) (by norm_num)
theorem B1970931 : Blo 1969435 1970931 := bstep (se 1 (by rfl) ⟨1478198, by rfl⟩ : syracuseStep 1970931 = 2956397) B2956397
theorem B4434605 : Blo 1969435 4434605 := bbase (se 3 (by rfl) ⟨831488, by rfl⟩ : syracuseStep 4434605 = 1662977) (by norm_num)
theorem B2956403 : Blo 1969435 2956403 := bstep (se 1 (by rfl) ⟨2217302, by rfl⟩ : syracuseStep 2956403 = 4434605) B4434605
theorem B1970935 : Blo 1969435 1970935 := bstep (se 1 (by rfl) ⟨1478201, by rfl⟩ : syracuseStep 1970935 = 2956403) B2956403
theorem B4209421 : Blo 1969435 4209421 := bbase (se 3 (by rfl) ⟨789266, by rfl⟩ : syracuseStep 4209421 = 1578533) (by norm_num)
theorem B5612561 : Blo 1969435 5612561 := bstep (se 2 (by rfl) ⟨2104710, by rfl⟩ : syracuseStep 5612561 = 4209421) B4209421
theorem B3741707 : Blo 1969435 3741707 := bstep (se 1 (by rfl) ⟨2806280, by rfl⟩ : syracuseStep 3741707 = 5612561) B5612561
theorem B2494471 : Blo 1969435 2494471 := bstep (se 1 (by rfl) ⟨1870853, by rfl⟩ : syracuseStep 2494471 = 3741707) B3741707
theorem B3325961 : Blo 1969435 3325961 := bstep (se 2 (by rfl) ⟨1247235, by rfl⟩ : syracuseStep 3325961 = 2494471) B2494471
theorem B2217307 : Blo 1969435 2217307 := bstep (se 1 (by rfl) ⟨1662980, by rfl⟩ : syracuseStep 2217307 = 3325961) B3325961
theorem B2956409 : Blo 1969435 2956409 := bstep (se 2 (by rfl) ⟨1108653, by rfl⟩ : syracuseStep 2956409 = 2217307) B2217307
theorem B1970939 : Blo 1969435 1970939 := bstep (se 1 (by rfl) ⟨1478204, by rfl⟩ : syracuseStep 1970939 = 2956409) B2956409
theorem B10114037 : Blo 1969435 10114037 := bbase (se 5 (by rfl) ⟨474095, by rfl⟩ : syracuseStep 10114037 = 948191) (by norm_num)
theorem B6742691 : Blo 1969435 6742691 := bstep (se 1 (by rfl) ⟨5057018, by rfl⟩ : syracuseStep 6742691 = 10114037) B10114037
theorem B4495127 : Blo 1969435 4495127 := bstep (se 1 (by rfl) ⟨3371345, by rfl⟩ : syracuseStep 4495127 = 6742691) B6742691
theorem B47948021 : Blo 1969435 47948021 := bstep (se 5 (by rfl) ⟨2247563, by rfl⟩ : syracuseStep 47948021 = 4495127) B4495127
theorem B31965347 : Blo 1969435 31965347 := bstep (se 1 (by rfl) ⟨23974010, by rfl⟩ : syracuseStep 31965347 = 47948021) B47948021
theorem B21310231 : Blo 1969435 21310231 := bstep (se 1 (by rfl) ⟨15982673, by rfl⟩ : syracuseStep 21310231 = 31965347) B31965347
theorem B28413641 : Blo 1969435 28413641 := bstep (se 2 (by rfl) ⟨10655115, by rfl⟩ : syracuseStep 28413641 = 21310231) B21310231
theorem B18942427 : Blo 1969435 18942427 := bstep (se 1 (by rfl) ⟨14206820, by rfl⟩ : syracuseStep 18942427 = 28413641) B28413641
theorem B25256569 : Blo 1969435 25256569 := bstep (se 2 (by rfl) ⟨9471213, by rfl⟩ : syracuseStep 25256569 = 18942427) B18942427
theorem B33675425 : Blo 1969435 33675425 := bstep (se 2 (by rfl) ⟨12628284, by rfl⟩ : syracuseStep 33675425 = 25256569) B25256569
theorem B22450283 : Blo 1969435 22450283 := bstep (se 1 (by rfl) ⟨16837712, by rfl⟩ : syracuseStep 22450283 = 33675425) B33675425
theorem B14966855 : Blo 1969435 14966855 := bstep (se 1 (by rfl) ⟨11225141, by rfl⟩ : syracuseStep 14966855 = 22450283) B22450283
theorem B9977903 : Blo 1969435 9977903 := bstep (se 1 (by rfl) ⟨7483427, by rfl⟩ : syracuseStep 9977903 = 14966855) B14966855
theorem B6651935 : Blo 1969435 6651935 := bstep (se 1 (by rfl) ⟨4988951, by rfl⟩ : syracuseStep 6651935 = 9977903) B9977903
theorem B4434623 : Blo 1969435 4434623 := bstep (se 1 (by rfl) ⟨3325967, by rfl⟩ : syracuseStep 4434623 = 6651935) B6651935
theorem B2956415 : Blo 1969435 2956415 := bstep (se 1 (by rfl) ⟨2217311, by rfl⟩ : syracuseStep 2956415 = 4434623) B4434623
theorem B1970943 : Blo 1969435 1970943 := bstep (se 1 (by rfl) ⟨1478207, by rfl⟩ : syracuseStep 1970943 = 2956415) B2956415
theorem B2956421 : Blo 1969435 2956421 := bbase (se 4 (by rfl) ⟨277164, by rfl⟩ : syracuseStep 2956421 = 554329) (by norm_num)
theorem B1970947 : Blo 1969435 1970947 := bstep (se 1 (by rfl) ⟨1478210, by rfl⟩ : syracuseStep 1970947 = 2956421) B2956421
theorem B3325981 : Blo 1969435 3325981 := bbase (se 3 (by rfl) ⟨623621, by rfl⟩ : syracuseStep 3325981 = 1247243) (by norm_num)
theorem B4434641 : Blo 1969435 4434641 := bstep (se 2 (by rfl) ⟨1662990, by rfl⟩ : syracuseStep 4434641 = 3325981) B3325981
theorem B2956427 : Blo 1969435 2956427 := bstep (se 1 (by rfl) ⟨2217320, by rfl⟩ : syracuseStep 2956427 = 4434641) B4434641
theorem B1970951 : Blo 1969435 1970951 := bstep (se 1 (by rfl) ⟨1478213, by rfl⟩ : syracuseStep 1970951 = 2956427) B2956427
theorem B2217325 : Blo 1969435 2217325 := bbase (se 3 (by rfl) ⟨415748, by rfl⟩ : syracuseStep 2217325 = 831497) (by norm_num)
theorem B2956433 : Blo 1969435 2956433 := bstep (se 2 (by rfl) ⟨1108662, by rfl⟩ : syracuseStep 2956433 = 2217325) B2217325
theorem B1970955 : Blo 1969435 1970955 := bstep (se 1 (by rfl) ⟨1478216, by rfl⟩ : syracuseStep 1970955 = 2956433) B2956433
theorem B6651989 : Blo 1969435 6651989 := bbase (se 8 (by rfl) ⟨38976, by rfl⟩ : syracuseStep 6651989 = 77953) (by norm_num)
theorem B4434659 : Blo 1969435 4434659 := bstep (se 1 (by rfl) ⟨3325994, by rfl⟩ : syracuseStep 4434659 = 6651989) B6651989
theorem B2956439 : Blo 1969435 2956439 := bstep (se 1 (by rfl) ⟨2217329, by rfl⟩ : syracuseStep 2956439 = 4434659) B4434659
theorem B1970959 : Blo 1969435 1970959 := bstep (se 1 (by rfl) ⟨1478219, by rfl⟩ : syracuseStep 1970959 = 2956439) B2956439
theorem B2956445 : Blo 1969435 2956445 := bbase (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) (by norm_num)
theorem B1970963 : Blo 1969435 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B4434677 : Blo 1969435 4434677 := bbase (se 5 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 4434677 = 415751) (by norm_num)
theorem B2956451 : Blo 1969435 2956451 := bstep (se 1 (by rfl) ⟨2217338, by rfl⟩ : syracuseStep 2956451 = 4434677) B4434677
theorem B1970967 : Blo 1969435 1970967 := bstep (se 1 (by rfl) ⟨1478225, by rfl⟩ : syracuseStep 1970967 = 2956451) B2956451
theorem B5057093 : Blo 1969435 5057093 := bbase (se 4 (by rfl) ⟨474102, by rfl⟩ : syracuseStep 5057093 = 948205) (by norm_num)
theorem B3371395 : Blo 1969435 3371395 := bstep (se 1 (by rfl) ⟨2528546, by rfl⟩ : syracuseStep 3371395 = 5057093) B5057093
theorem B4495193 : Blo 1969435 4495193 := bstep (se 2 (by rfl) ⟨1685697, by rfl⟩ : syracuseStep 4495193 = 3371395) B3371395
theorem B2996795 : Blo 1969435 2996795 := bstep (se 1 (by rfl) ⟨2247596, by rfl⟩ : syracuseStep 2996795 = 4495193) B4495193
theorem B7991453 : Blo 1969435 7991453 := bstep (se 3 (by rfl) ⟨1498397, by rfl⟩ : syracuseStep 7991453 = 2996795) B2996795
theorem B5327635 : Blo 1969435 5327635 := bstep (se 1 (by rfl) ⟨3995726, by rfl⟩ : syracuseStep 5327635 = 7991453) B7991453
theorem B7103513 : Blo 1969435 7103513 := bstep (se 2 (by rfl) ⟨2663817, by rfl⟩ : syracuseStep 7103513 = 5327635) B5327635
theorem B4735675 : Blo 1969435 4735675 := bstep (se 1 (by rfl) ⟨3551756, by rfl⟩ : syracuseStep 4735675 = 7103513) B7103513
theorem B25256933 : Blo 1969435 25256933 := bstep (se 4 (by rfl) ⟨2367837, by rfl⟩ : syracuseStep 25256933 = 4735675) B4735675
theorem B16837955 : Blo 1969435 16837955 := bstep (se 1 (by rfl) ⟨12628466, by rfl⟩ : syracuseStep 16837955 = 25256933) B25256933
theorem B11225303 : Blo 1969435 11225303 := bstep (se 1 (by rfl) ⟨8418977, by rfl⟩ : syracuseStep 11225303 = 16837955) B16837955
theorem B7483535 : Blo 1969435 7483535 := bstep (se 1 (by rfl) ⟨5612651, by rfl⟩ : syracuseStep 7483535 = 11225303) B11225303
theorem B4989023 : Blo 1969435 4989023 := bstep (se 1 (by rfl) ⟨3741767, by rfl⟩ : syracuseStep 4989023 = 7483535) B7483535
theorem B3326015 : Blo 1969435 3326015 := bstep (se 1 (by rfl) ⟨2494511, by rfl⟩ : syracuseStep 3326015 = 4989023) B4989023
theorem B2217343 : Blo 1969435 2217343 := bstep (se 1 (by rfl) ⟨1663007, by rfl⟩ : syracuseStep 2217343 = 3326015) B3326015
theorem B2956457 : Blo 1969435 2956457 := bstep (se 2 (by rfl) ⟨1108671, by rfl⟩ : syracuseStep 2956457 = 2217343) B2217343
theorem B1970971 : Blo 1969435 1970971 := bstep (se 1 (by rfl) ⟨1478228, by rfl⟩ : syracuseStep 1970971 = 2956457) B2956457
theorem B4735685 : Blo 1969435 4735685 := bbase (se 4 (by rfl) ⟨443970, by rfl⟩ : syracuseStep 4735685 = 887941) (by norm_num)
theorem B3157123 : Blo 1969435 3157123 := bstep (se 1 (by rfl) ⟨2367842, by rfl⟩ : syracuseStep 3157123 = 4735685) B4735685
theorem B4209497 : Blo 1969435 4209497 := bstep (se 2 (by rfl) ⟨1578561, by rfl⟩ : syracuseStep 4209497 = 3157123) B3157123
theorem B2806331 : Blo 1969435 2806331 := bstep (se 1 (by rfl) ⟨2104748, by rfl⟩ : syracuseStep 2806331 = 4209497) B4209497
theorem B7483549 : Blo 1969435 7483549 := bstep (se 3 (by rfl) ⟨1403165, by rfl⟩ : syracuseStep 7483549 = 2806331) B2806331
theorem B9978065 : Blo 1969435 9978065 := bstep (se 2 (by rfl) ⟨3741774, by rfl⟩ : syracuseStep 9978065 = 7483549) B7483549
theorem B6652043 : Blo 1969435 6652043 := bstep (se 1 (by rfl) ⟨4989032, by rfl⟩ : syracuseStep 6652043 = 9978065) B9978065
theorem B4434695 : Blo 1969435 4434695 := bstep (se 1 (by rfl) ⟨3326021, by rfl⟩ : syracuseStep 4434695 = 6652043) B6652043
theorem B2956463 : Blo 1969435 2956463 := bstep (se 1 (by rfl) ⟨2217347, by rfl⟩ : syracuseStep 2956463 = 4434695) B4434695
theorem B1970975 : Blo 1969435 1970975 := bstep (se 1 (by rfl) ⟨1478231, by rfl⟩ : syracuseStep 1970975 = 2956463) B2956463
theorem B2956469 : Blo 1969435 2956469 := bbase (se 5 (by rfl) ⟨138584, by rfl⟩ : syracuseStep 2956469 = 277169) (by norm_num)
theorem B1970979 : Blo 1969435 1970979 := bstep (se 1 (by rfl) ⟨1478234, by rfl⟩ : syracuseStep 1970979 = 2956469) B2956469
theorem B4989053 : Blo 1969435 4989053 := bbase (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) (by norm_num)
theorem B3326035 : Blo 1969435 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B4434713 : Blo 1969435 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B2956475 : Blo 1969435 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1970983 : Blo 1969435 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B2217361 : Blo 1969435 2217361 := bbase (se 2 (by rfl) ⟨831510, by rfl⟩ : syracuseStep 2217361 = 1663021) (by norm_num)
theorem B2956481 : Blo 1969435 2956481 := bstep (se 2 (by rfl) ⟨1108680, by rfl⟩ : syracuseStep 2956481 = 2217361) B2217361
theorem B1970987 : Blo 1969435 1970987 := bstep (se 1 (by rfl) ⟨1478240, by rfl⟩ : syracuseStep 1970987 = 2956481) B2956481
theorem B3741805 : Blo 1969435 3741805 := bbase (se 3 (by rfl) ⟨701588, by rfl⟩ : syracuseStep 3741805 = 1403177) (by norm_num)
theorem B4989073 : Blo 1969435 4989073 := bstep (se 2 (by rfl) ⟨1870902, by rfl⟩ : syracuseStep 4989073 = 3741805) B3741805
theorem B6652097 : Blo 1969435 6652097 := bstep (se 2 (by rfl) ⟨2494536, by rfl⟩ : syracuseStep 6652097 = 4989073) B4989073
theorem B4434731 : Blo 1969435 4434731 := bstep (se 1 (by rfl) ⟨3326048, by rfl⟩ : syracuseStep 4434731 = 6652097) B6652097
theorem B2956487 : Blo 1969435 2956487 := bstep (se 1 (by rfl) ⟨2217365, by rfl⟩ : syracuseStep 2956487 = 4434731) B4434731
theorem B1970991 : Blo 1969435 1970991 := bstep (se 1 (by rfl) ⟨1478243, by rfl⟩ : syracuseStep 1970991 = 2956487) B2956487
theorem B2956493 : Blo 1969435 2956493 := bbase (se 3 (by rfl) ⟨554342, by rfl⟩ : syracuseStep 2956493 = 1108685) (by norm_num)
theorem B1970995 : Blo 1969435 1970995 := bstep (se 1 (by rfl) ⟨1478246, by rfl⟩ : syracuseStep 1970995 = 2956493) B2956493
theorem B4434749 : Blo 1969435 4434749 := bbase (se 3 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 4434749 = 1663031) (by norm_num)
theorem B2956499 : Blo 1969435 2956499 := bstep (se 1 (by rfl) ⟨2217374, by rfl⟩ : syracuseStep 2956499 = 4434749) B4434749
theorem B1970999 : Blo 1969435 1970999 := bstep (se 1 (by rfl) ⟨1478249, by rfl⟩ : syracuseStep 1970999 = 2956499) B2956499
theorem B3326069 : Blo 1969435 3326069 := bbase (se 5 (by rfl) ⟨155909, by rfl⟩ : syracuseStep 3326069 = 311819) (by norm_num)
theorem B2217379 : Blo 1969435 2217379 := bstep (se 1 (by rfl) ⟨1663034, by rfl⟩ : syracuseStep 2217379 = 3326069) B3326069
theorem B2956505 : Blo 1969435 2956505 := bstep (se 2 (by rfl) ⟨1108689, by rfl⟩ : syracuseStep 2956505 = 2217379) B2217379
theorem B1971003 : Blo 1969435 1971003 := bstep (se 1 (by rfl) ⟨1478252, by rfl⟩ : syracuseStep 1971003 = 2956505) B2956505
theorem B4209565 : Blo 1969435 4209565 := bbase (se 3 (by rfl) ⟨789293, by rfl⟩ : syracuseStep 4209565 = 1578587) (by norm_num)
theorem B5612753 : Blo 1969435 5612753 := bstep (se 2 (by rfl) ⟨2104782, by rfl⟩ : syracuseStep 5612753 = 4209565) B4209565
theorem B14967341 : Blo 1969435 14967341 := bstep (se 3 (by rfl) ⟨2806376, by rfl⟩ : syracuseStep 14967341 = 5612753) B5612753
theorem B9978227 : Blo 1969435 9978227 := bstep (se 1 (by rfl) ⟨7483670, by rfl⟩ : syracuseStep 9978227 = 14967341) B14967341
theorem B6652151 : Blo 1969435 6652151 := bstep (se 1 (by rfl) ⟨4989113, by rfl⟩ : syracuseStep 6652151 = 9978227) B9978227
theorem B4434767 : Blo 1969435 4434767 := bstep (se 1 (by rfl) ⟨3326075, by rfl⟩ : syracuseStep 4434767 = 6652151) B6652151
theorem B2956511 : Blo 1969435 2956511 := bstep (se 1 (by rfl) ⟨2217383, by rfl⟩ : syracuseStep 2956511 = 4434767) B4434767
theorem B1971007 : Blo 1969435 1971007 := bstep (se 1 (by rfl) ⟨1478255, by rfl⟩ : syracuseStep 1971007 = 2956511) B2956511
theorem B2956517 : Blo 1969435 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B1971011 : Blo 1969435 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B10655509 : Blo 1969435 10655509 := bbase (se 6 (by rfl) ⟨249738, by rfl⟩ : syracuseStep 10655509 = 499477) (by norm_num)
theorem B14207345 : Blo 1969435 14207345 := bstep (se 2 (by rfl) ⟨5327754, by rfl⟩ : syracuseStep 14207345 = 10655509) B10655509
theorem B9471563 : Blo 1969435 9471563 := bstep (se 1 (by rfl) ⟨7103672, by rfl⟩ : syracuseStep 9471563 = 14207345) B14207345
theorem B6314375 : Blo 1969435 6314375 := bstep (se 1 (by rfl) ⟨4735781, by rfl⟩ : syracuseStep 6314375 = 9471563) B9471563
theorem B4209583 : Blo 1969435 4209583 := bstep (se 1 (by rfl) ⟨3157187, by rfl⟩ : syracuseStep 4209583 = 6314375) B6314375
theorem B5612777 : Blo 1969435 5612777 := bstep (se 2 (by rfl) ⟨2104791, by rfl⟩ : syracuseStep 5612777 = 4209583) B4209583
theorem B3741851 : Blo 1969435 3741851 := bstep (se 1 (by rfl) ⟨2806388, by rfl⟩ : syracuseStep 3741851 = 5612777) B5612777
theorem B2494567 : Blo 1969435 2494567 := bstep (se 1 (by rfl) ⟨1870925, by rfl⟩ : syracuseStep 2494567 = 3741851) B3741851
theorem B3326089 : Blo 1969435 3326089 := bstep (se 2 (by rfl) ⟨1247283, by rfl⟩ : syracuseStep 3326089 = 2494567) B2494567
theorem B4434785 : Blo 1969435 4434785 := bstep (se 2 (by rfl) ⟨1663044, by rfl⟩ : syracuseStep 4434785 = 3326089) B3326089
theorem B2956523 : Blo 1969435 2956523 := bstep (se 1 (by rfl) ⟨2217392, by rfl⟩ : syracuseStep 2956523 = 4434785) B4434785
theorem B1971015 : Blo 1969435 1971015 := bstep (se 1 (by rfl) ⟨1478261, by rfl⟩ : syracuseStep 1971015 = 2956523) B2956523
theorem B2217397 : Blo 1969435 2217397 := bbase (se 5 (by rfl) ⟨103940, by rfl⟩ : syracuseStep 2217397 = 207881) (by norm_num)
theorem B2956529 : Blo 1969435 2956529 := bstep (se 2 (by rfl) ⟨1108698, by rfl⟩ : syracuseStep 2956529 = 2217397) B2217397
theorem B1971019 : Blo 1969435 1971019 := bstep (se 1 (by rfl) ⟨1478264, by rfl⟩ : syracuseStep 1971019 = 2956529) B2956529
theorem B2494577 : Blo 1969435 2494577 := bbase (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) (by norm_num)
theorem B6652205 : Blo 1969435 6652205 := bstep (se 3 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 6652205 = 2494577) B2494577
theorem B4434803 : Blo 1969435 4434803 := bstep (se 1 (by rfl) ⟨3326102, by rfl⟩ : syracuseStep 4434803 = 6652205) B6652205
theorem B2956535 : Blo 1969435 2956535 := bstep (se 1 (by rfl) ⟨2217401, by rfl⟩ : syracuseStep 2956535 = 4434803) B4434803
theorem B1971023 : Blo 1969435 1971023 := bstep (se 1 (by rfl) ⟨1478267, by rfl⟩ : syracuseStep 1971023 = 2956535) B2956535
theorem B2956541 : Blo 1969435 2956541 := bbase (se 3 (by rfl) ⟨554351, by rfl⟩ : syracuseStep 2956541 = 1108703) (by norm_num)
theorem B1971027 : Blo 1969435 1971027 := bstep (se 1 (by rfl) ⟨1478270, by rfl⟩ : syracuseStep 1971027 = 2956541) B2956541
theorem B4434821 : Blo 1969435 4434821 := bbase (se 4 (by rfl) ⟨415764, by rfl⟩ : syracuseStep 4434821 = 831529) (by norm_num)
theorem B2956547 : Blo 1969435 2956547 := bstep (se 1 (by rfl) ⟨2217410, by rfl⟩ : syracuseStep 2956547 = 4434821) B4434821
theorem B1971031 : Blo 1969435 1971031 := bstep (se 1 (by rfl) ⟨1478273, by rfl⟩ : syracuseStep 1971031 = 2956547) B2956547
theorem B2104813 : Blo 1969435 2104813 := bbase (se 3 (by rfl) ⟨394652, by rfl⟩ : syracuseStep 2104813 = 789305) (by norm_num)
theorem B2806417 : Blo 1969435 2806417 := bstep (se 2 (by rfl) ⟨1052406, by rfl⟩ : syracuseStep 2806417 = 2104813) B2104813
theorem B3741889 : Blo 1969435 3741889 := bstep (se 2 (by rfl) ⟨1403208, by rfl⟩ : syracuseStep 3741889 = 2806417) B2806417
theorem B4989185 : Blo 1969435 4989185 := bstep (se 2 (by rfl) ⟨1870944, by rfl⟩ : syracuseStep 4989185 = 3741889) B3741889
theorem B3326123 : Blo 1969435 3326123 := bstep (se 1 (by rfl) ⟨2494592, by rfl⟩ : syracuseStep 3326123 = 4989185) B4989185
theorem B2217415 : Blo 1969435 2217415 := bstep (se 1 (by rfl) ⟨1663061, by rfl⟩ : syracuseStep 2217415 = 3326123) B3326123
theorem B2956553 : Blo 1969435 2956553 := bstep (se 2 (by rfl) ⟨1108707, by rfl⟩ : syracuseStep 2956553 = 2217415) B2217415
theorem B1971035 : Blo 1969435 1971035 := bstep (se 1 (by rfl) ⟨1478276, by rfl⟩ : syracuseStep 1971035 = 2956553) B2956553
theorem B9978389 : Blo 1969435 9978389 := bbase (se 6 (by rfl) ⟨233868, by rfl⟩ : syracuseStep 9978389 = 467737) (by norm_num)
theorem B6652259 : Blo 1969435 6652259 := bstep (se 1 (by rfl) ⟨4989194, by rfl⟩ : syracuseStep 6652259 = 9978389) B9978389
theorem B4434839 : Blo 1969435 4434839 := bstep (se 1 (by rfl) ⟨3326129, by rfl⟩ : syracuseStep 4434839 = 6652259) B6652259
theorem B2956559 : Blo 1969435 2956559 := bstep (se 1 (by rfl) ⟨2217419, by rfl⟩ : syracuseStep 2956559 = 4434839) B4434839
theorem B1971039 : Blo 1969435 1971039 := bstep (se 1 (by rfl) ⟨1478279, by rfl⟩ : syracuseStep 1971039 = 2956559) B2956559
theorem B2956565 : Blo 1969435 2956565 := bbase (se 6 (by rfl) ⟨69294, by rfl⟩ : syracuseStep 2956565 = 138589) (by norm_num)
theorem B1971043 : Blo 1969435 1971043 := bstep (se 1 (by rfl) ⟨1478282, by rfl⟩ : syracuseStep 1971043 = 2956565) B2956565
theorem B3551893 : Blo 1969435 3551893 := bbase (se 6 (by rfl) ⟨83247, by rfl⟩ : syracuseStep 3551893 = 166495) (by norm_num)
theorem B18943429 : Blo 1969435 18943429 := bstep (se 4 (by rfl) ⟨1775946, by rfl⟩ : syracuseStep 18943429 = 3551893) B3551893
theorem B25257905 : Blo 1969435 25257905 := bstep (se 2 (by rfl) ⟨9471714, by rfl⟩ : syracuseStep 25257905 = 18943429) B18943429
theorem B16838603 : Blo 1969435 16838603 := bstep (se 1 (by rfl) ⟨12628952, by rfl⟩ : syracuseStep 16838603 = 25257905) B25257905
theorem B11225735 : Blo 1969435 11225735 := bstep (se 1 (by rfl) ⟨8419301, by rfl⟩ : syracuseStep 11225735 = 16838603) B16838603
theorem B7483823 : Blo 1969435 7483823 := bstep (se 1 (by rfl) ⟨5612867, by rfl⟩ : syracuseStep 7483823 = 11225735) B11225735
theorem B4989215 : Blo 1969435 4989215 := bstep (se 1 (by rfl) ⟨3741911, by rfl⟩ : syracuseStep 4989215 = 7483823) B7483823
theorem B3326143 : Blo 1969435 3326143 := bstep (se 1 (by rfl) ⟨2494607, by rfl⟩ : syracuseStep 3326143 = 4989215) B4989215
theorem B4434857 : Blo 1969435 4434857 := bstep (se 2 (by rfl) ⟨1663071, by rfl⟩ : syracuseStep 4434857 = 3326143) B3326143
theorem B2956571 : Blo 1969435 2956571 := bstep (se 1 (by rfl) ⟨2217428, by rfl⟩ : syracuseStep 2956571 = 4434857) B4434857
theorem B1971047 : Blo 1969435 1971047 := bstep (se 1 (by rfl) ⟨1478285, by rfl⟩ : syracuseStep 1971047 = 2956571) B2956571
theorem B2217433 : Blo 1969435 2217433 := bbase (se 2 (by rfl) ⟨831537, by rfl⟩ : syracuseStep 2217433 = 1663075) (by norm_num)
theorem B2956577 : Blo 1969435 2956577 := bstep (se 2 (by rfl) ⟨1108716, by rfl⟩ : syracuseStep 2956577 = 2217433) B2217433
theorem B1971051 : Blo 1969435 1971051 := bstep (se 1 (by rfl) ⟨1478288, by rfl⟩ : syracuseStep 1971051 = 2956577) B2956577
theorem B2806445 : Blo 1969435 2806445 := bbase (se 3 (by rfl) ⟨526208, by rfl⟩ : syracuseStep 2806445 = 1052417) (by norm_num)
theorem B7483853 : Blo 1969435 7483853 := bstep (se 3 (by rfl) ⟨1403222, by rfl⟩ : syracuseStep 7483853 = 2806445) B2806445
theorem B4989235 : Blo 1969435 4989235 := bstep (se 1 (by rfl) ⟨3741926, by rfl⟩ : syracuseStep 4989235 = 7483853) B7483853
theorem B6652313 : Blo 1969435 6652313 := bstep (se 2 (by rfl) ⟨2494617, by rfl⟩ : syracuseStep 6652313 = 4989235) B4989235
theorem B4434875 : Blo 1969435 4434875 := bstep (se 1 (by rfl) ⟨3326156, by rfl⟩ : syracuseStep 4434875 = 6652313) B6652313
theorem B2956583 : Blo 1969435 2956583 := bstep (se 1 (by rfl) ⟨2217437, by rfl⟩ : syracuseStep 2956583 = 4434875) B4434875
theorem B1971055 : Blo 1969435 1971055 := bstep (se 1 (by rfl) ⟨1478291, by rfl⟩ : syracuseStep 1971055 = 2956583) B2956583
theorem B2956589 : Blo 1969435 2956589 := bbase (se 3 (by rfl) ⟨554360, by rfl⟩ : syracuseStep 2956589 = 1108721) (by norm_num)
theorem B1971059 : Blo 1969435 1971059 := bstep (se 1 (by rfl) ⟨1478294, by rfl⟩ : syracuseStep 1971059 = 2956589) B2956589
theorem B4434893 : Blo 1969435 4434893 := bbase (se 3 (by rfl) ⟨831542, by rfl⟩ : syracuseStep 4434893 = 1663085) (by norm_num)
theorem B2956595 : Blo 1969435 2956595 := bstep (se 1 (by rfl) ⟨2217446, by rfl⟩ : syracuseStep 2956595 = 4434893) B4434893
theorem B1971063 : Blo 1969435 1971063 := bstep (se 1 (by rfl) ⟨1478297, by rfl⟩ : syracuseStep 1971063 = 2956595) B2956595
theorem B2494633 : Blo 1969435 2494633 := bbase (se 2 (by rfl) ⟨935487, by rfl⟩ : syracuseStep 2494633 = 1870975) (by norm_num)
theorem B3326177 : Blo 1969435 3326177 := bstep (se 2 (by rfl) ⟨1247316, by rfl⟩ : syracuseStep 3326177 = 2494633) B2494633
theorem B2217451 : Blo 1969435 2217451 := bstep (se 1 (by rfl) ⟨1663088, by rfl⟩ : syracuseStep 2217451 = 3326177) B3326177
theorem B2956601 : Blo 1969435 2956601 := bstep (se 2 (by rfl) ⟨1108725, by rfl⟩ : syracuseStep 2956601 = 2217451) B2217451
theorem B1971067 : Blo 1969435 1971067 := bstep (se 1 (by rfl) ⟨1478300, by rfl⟩ : syracuseStep 1971067 = 2956601) B2956601
theorem B9471829 : Blo 1969435 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B12629105 : Blo 1969435 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B8419403 : Blo 1969435 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B22451741 : Blo 1969435 22451741 := bstep (se 3 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 22451741 = 8419403) B8419403
theorem B14967827 : Blo 1969435 14967827 := bstep (se 1 (by rfl) ⟨11225870, by rfl⟩ : syracuseStep 14967827 = 22451741) B22451741
theorem B9978551 : Blo 1969435 9978551 := bstep (se 1 (by rfl) ⟨7483913, by rfl⟩ : syracuseStep 9978551 = 14967827) B14967827
theorem B6652367 : Blo 1969435 6652367 := bstep (se 1 (by rfl) ⟨4989275, by rfl⟩ : syracuseStep 6652367 = 9978551) B9978551
theorem B4434911 : Blo 1969435 4434911 := bstep (se 1 (by rfl) ⟨3326183, by rfl⟩ : syracuseStep 4434911 = 6652367) B6652367
theorem B2956607 : Blo 1969435 2956607 := bstep (se 1 (by rfl) ⟨2217455, by rfl⟩ : syracuseStep 2956607 = 4434911) B4434911
theorem B1971071 : Blo 1969435 1971071 := bstep (se 1 (by rfl) ⟨1478303, by rfl⟩ : syracuseStep 1971071 = 2956607) B2956607
theorem B2956613 : Blo 1969435 2956613 := bbase (se 4 (by rfl) ⟨277182, by rfl⟩ : syracuseStep 2956613 = 554365) (by norm_num)
theorem B1971075 : Blo 1969435 1971075 := bstep (se 1 (by rfl) ⟨1478306, by rfl⟩ : syracuseStep 1971075 = 2956613) B2956613
theorem B3326197 : Blo 1969435 3326197 := bbase (se 5 (by rfl) ⟨155915, by rfl⟩ : syracuseStep 3326197 = 311831) (by norm_num)
theorem B4434929 : Blo 1969435 4434929 := bstep (se 2 (by rfl) ⟨1663098, by rfl⟩ : syracuseStep 4434929 = 3326197) B3326197
theorem B2956619 : Blo 1969435 2956619 := bstep (se 1 (by rfl) ⟨2217464, by rfl⟩ : syracuseStep 2956619 = 4434929) B4434929
theorem B1971079 : Blo 1969435 1971079 := bstep (se 1 (by rfl) ⟨1478309, by rfl⟩ : syracuseStep 1971079 = 2956619) B2956619
theorem B2217469 : Blo 1969435 2217469 := bbase (se 3 (by rfl) ⟨415775, by rfl⟩ : syracuseStep 2217469 = 831551) (by norm_num)
theorem B2956625 : Blo 1969435 2956625 := bstep (se 2 (by rfl) ⟨1108734, by rfl⟩ : syracuseStep 2956625 = 2217469) B2217469
theorem B1971083 : Blo 1969435 1971083 := bstep (se 1 (by rfl) ⟨1478312, by rfl⟩ : syracuseStep 1971083 = 2956625) B2956625
theorem B6652421 : Blo 1969435 6652421 := bbase (se 4 (by rfl) ⟨623664, by rfl⟩ : syracuseStep 6652421 = 1247329) (by norm_num)
theorem B4434947 : Blo 1969435 4434947 := bstep (se 1 (by rfl) ⟨3326210, by rfl⟩ : syracuseStep 4434947 = 6652421) B6652421
theorem B2956631 : Blo 1969435 2956631 := bstep (se 1 (by rfl) ⟨2217473, by rfl⟩ : syracuseStep 2956631 = 4434947) B4434947
theorem B1971087 : Blo 1969435 1971087 := bstep (se 1 (by rfl) ⟨1478315, by rfl⟩ : syracuseStep 1971087 = 2956631) B2956631
theorem B2956637 : Blo 1969435 2956637 := bbase (se 3 (by rfl) ⟨554369, by rfl⟩ : syracuseStep 2956637 = 1108739) (by norm_num)
theorem B1971091 : Blo 1969435 1971091 := bstep (se 1 (by rfl) ⟨1478318, by rfl⟩ : syracuseStep 1971091 = 2956637) B2956637
theorem B4434965 : Blo 1969435 4434965 := bbase (se 6 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 4434965 = 207889) (by norm_num)
theorem B2956643 : Blo 1969435 2956643 := bstep (se 1 (by rfl) ⟨2217482, by rfl⟩ : syracuseStep 2956643 = 4434965) B4434965
theorem B1971095 : Blo 1969435 1971095 := bstep (se 1 (by rfl) ⟨1478321, by rfl⟩ : syracuseStep 1971095 = 2956643) B2956643
theorem B7484021 : Blo 1969435 7484021 := bbase (se 5 (by rfl) ⟨350813, by rfl⟩ : syracuseStep 7484021 = 701627) (by norm_num)
theorem B4989347 : Blo 1969435 4989347 := bstep (se 1 (by rfl) ⟨3742010, by rfl⟩ : syracuseStep 4989347 = 7484021) B7484021
theorem B3326231 : Blo 1969435 3326231 := bstep (se 1 (by rfl) ⟨2494673, by rfl⟩ : syracuseStep 3326231 = 4989347) B4989347
theorem B2217487 : Blo 1969435 2217487 := bstep (se 1 (by rfl) ⟨1663115, by rfl⟩ : syracuseStep 2217487 = 3326231) B3326231
theorem B2956649 : Blo 1969435 2956649 := bstep (se 2 (by rfl) ⟨1108743, by rfl⟩ : syracuseStep 2956649 = 2217487) B2217487
theorem B1971099 : Blo 1969435 1971099 := bstep (se 1 (by rfl) ⟨1478324, by rfl⟩ : syracuseStep 1971099 = 2956649) B2956649
theorem B2104885 : Blo 1969435 2104885 := bbase (se 5 (by rfl) ⟨98666, by rfl⟩ : syracuseStep 2104885 = 197333) (by norm_num)
theorem B11226053 : Blo 1969435 11226053 := bstep (se 4 (by rfl) ⟨1052442, by rfl⟩ : syracuseStep 11226053 = 2104885) B2104885
theorem B7484035 : Blo 1969435 7484035 := bstep (se 1 (by rfl) ⟨5613026, by rfl⟩ : syracuseStep 7484035 = 11226053) B11226053
theorem B9978713 : Blo 1969435 9978713 := bstep (se 2 (by rfl) ⟨3742017, by rfl⟩ : syracuseStep 9978713 = 7484035) B7484035
theorem B6652475 : Blo 1969435 6652475 := bstep (se 1 (by rfl) ⟨4989356, by rfl⟩ : syracuseStep 6652475 = 9978713) B9978713
theorem B4434983 : Blo 1969435 4434983 := bstep (se 1 (by rfl) ⟨3326237, by rfl⟩ : syracuseStep 4434983 = 6652475) B6652475
theorem B2956655 : Blo 1969435 2956655 := bstep (se 1 (by rfl) ⟨2217491, by rfl⟩ : syracuseStep 2956655 = 4434983) B4434983
theorem B1971103 : Blo 1969435 1971103 := bstep (se 1 (by rfl) ⟨1478327, by rfl⟩ : syracuseStep 1971103 = 2956655) B2956655
theorem B2956661 : Blo 1969435 2956661 := bbase (se 5 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 2956661 = 277187) (by norm_num)
theorem B1971107 : Blo 1969435 1971107 := bstep (se 1 (by rfl) ⟨1478330, by rfl⟩ : syracuseStep 1971107 = 2956661) B2956661
theorem B2806525 : Blo 1969435 2806525 := bbase (se 3 (by rfl) ⟨526223, by rfl⟩ : syracuseStep 2806525 = 1052447) (by norm_num)
theorem B3742033 : Blo 1969435 3742033 := bstep (se 2 (by rfl) ⟨1403262, by rfl⟩ : syracuseStep 3742033 = 2806525) B2806525
theorem B4989377 : Blo 1969435 4989377 := bstep (se 2 (by rfl) ⟨1871016, by rfl⟩ : syracuseStep 4989377 = 3742033) B3742033
theorem B3326251 : Blo 1969435 3326251 := bstep (se 1 (by rfl) ⟨2494688, by rfl⟩ : syracuseStep 3326251 = 4989377) B4989377
theorem B4435001 : Blo 1969435 4435001 := bstep (se 2 (by rfl) ⟨1663125, by rfl⟩ : syracuseStep 4435001 = 3326251) B3326251
theorem B2956667 : Blo 1969435 2956667 := bstep (se 1 (by rfl) ⟨2217500, by rfl⟩ : syracuseStep 2956667 = 4435001) B4435001
theorem B1971111 : Blo 1969435 1971111 := bstep (se 1 (by rfl) ⟨1478333, by rfl⟩ : syracuseStep 1971111 = 2956667) B2956667
theorem B2217505 : Blo 1969435 2217505 := bbase (se 2 (by rfl) ⟨831564, by rfl⟩ : syracuseStep 2217505 = 1663129) (by norm_num)
theorem B2956673 : Blo 1969435 2956673 := bstep (se 2 (by rfl) ⟨1108752, by rfl⟩ : syracuseStep 2956673 = 2217505) B2217505
theorem B1971115 : Blo 1969435 1971115 := bstep (se 1 (by rfl) ⟨1478336, by rfl⟩ : syracuseStep 1971115 = 2956673) B2956673
theorem B4989397 : Blo 1969435 4989397 := bbase (se 7 (by rfl) ⟨58469, by rfl⟩ : syracuseStep 4989397 = 116939) (by norm_num)
theorem B6652529 : Blo 1969435 6652529 := bstep (se 2 (by rfl) ⟨2494698, by rfl⟩ : syracuseStep 6652529 = 4989397) B4989397
theorem B4435019 : Blo 1969435 4435019 := bstep (se 1 (by rfl) ⟨3326264, by rfl⟩ : syracuseStep 4435019 = 6652529) B6652529
theorem B2956679 : Blo 1969435 2956679 := bstep (se 1 (by rfl) ⟨2217509, by rfl⟩ : syracuseStep 2956679 = 4435019) B4435019
theorem B1971119 : Blo 1969435 1971119 := bstep (se 1 (by rfl) ⟨1478339, by rfl⟩ : syracuseStep 1971119 = 2956679) B2956679
theorem B2956685 : Blo 1969435 2956685 := bbase (se 3 (by rfl) ⟨554378, by rfl⟩ : syracuseStep 2956685 = 1108757) (by norm_num)
theorem B1971123 : Blo 1969435 1971123 := bstep (se 1 (by rfl) ⟨1478342, by rfl⟩ : syracuseStep 1971123 = 2956685) B2956685
theorem B4435037 : Blo 1969435 4435037 := bbase (se 3 (by rfl) ⟨831569, by rfl⟩ : syracuseStep 4435037 = 1663139) (by norm_num)
theorem B2956691 : Blo 1969435 2956691 := bstep (se 1 (by rfl) ⟨2217518, by rfl⟩ : syracuseStep 2956691 = 4435037) B4435037
theorem B1971127 : Blo 1969435 1971127 := bstep (se 1 (by rfl) ⟨1478345, by rfl⟩ : syracuseStep 1971127 = 2956691) B2956691
theorem B3326285 : Blo 1969435 3326285 := bbase (se 3 (by rfl) ⟨623678, by rfl⟩ : syracuseStep 3326285 = 1247357) (by norm_num)
theorem B2217523 : Blo 1969435 2217523 := bstep (se 1 (by rfl) ⟨1663142, by rfl⟩ : syracuseStep 2217523 = 3326285) B3326285
theorem B2956697 : Blo 1969435 2956697 := bstep (se 2 (by rfl) ⟨1108761, by rfl⟩ : syracuseStep 2956697 = 2217523) B2217523
theorem B1971131 : Blo 1969435 1971131 := bstep (se 1 (by rfl) ⟨1478348, by rfl⟩ : syracuseStep 1971131 = 2956697) B2956697
theorem B1998029 : Blo 1969435 1998029 := bbase (se 3 (by rfl) ⟨374630, by rfl⟩ : syracuseStep 1998029 = 749261) (by norm_num)
theorem B5328077 : Blo 1969435 5328077 := bstep (se 3 (by rfl) ⟨999014, by rfl⟩ : syracuseStep 5328077 = 1998029) B1998029
theorem B14208205 : Blo 1969435 14208205 := bstep (se 3 (by rfl) ⟨2664038, by rfl⟩ : syracuseStep 14208205 = 5328077) B5328077
theorem B18944273 : Blo 1969435 18944273 := bstep (se 2 (by rfl) ⟨7104102, by rfl⟩ : syracuseStep 18944273 = 14208205) B14208205
theorem B12629515 : Blo 1969435 12629515 := bstep (se 1 (by rfl) ⟨9472136, by rfl⟩ : syracuseStep 12629515 = 18944273) B18944273
theorem B16839353 : Blo 1969435 16839353 := bstep (se 2 (by rfl) ⟨6314757, by rfl⟩ : syracuseStep 16839353 = 12629515) B12629515
theorem B11226235 : Blo 1969435 11226235 := bstep (se 1 (by rfl) ⟨8419676, by rfl⟩ : syracuseStep 11226235 = 16839353) B16839353
theorem B14968313 : Blo 1969435 14968313 := bstep (se 2 (by rfl) ⟨5613117, by rfl⟩ : syracuseStep 14968313 = 11226235) B11226235
theorem B9978875 : Blo 1969435 9978875 := bstep (se 1 (by rfl) ⟨7484156, by rfl⟩ : syracuseStep 9978875 = 14968313) B14968313
theorem B6652583 : Blo 1969435 6652583 := bstep (se 1 (by rfl) ⟨4989437, by rfl⟩ : syracuseStep 6652583 = 9978875) B9978875
theorem B4435055 : Blo 1969435 4435055 := bstep (se 1 (by rfl) ⟨3326291, by rfl⟩ : syracuseStep 4435055 = 6652583) B6652583
theorem B2956703 : Blo 1969435 2956703 := bstep (se 1 (by rfl) ⟨2217527, by rfl⟩ : syracuseStep 2956703 = 4435055) B4435055
theorem B1971135 : Blo 1969435 1971135 := bstep (se 1 (by rfl) ⟨1478351, by rfl⟩ : syracuseStep 1971135 = 2956703) B2956703
theorem B2956709 : Blo 1969435 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B1971139 : Blo 1969435 1971139 := bstep (se 1 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 1971139 = 2956709) B2956709
theorem B2494729 : Blo 1969435 2494729 := bbase (se 2 (by rfl) ⟨935523, by rfl⟩ : syracuseStep 2494729 = 1871047) (by norm_num)
theorem B3326305 : Blo 1969435 3326305 := bstep (se 2 (by rfl) ⟨1247364, by rfl⟩ : syracuseStep 3326305 = 2494729) B2494729
theorem B4435073 : Blo 1969435 4435073 := bstep (se 2 (by rfl) ⟨1663152, by rfl⟩ : syracuseStep 4435073 = 3326305) B3326305
theorem B2956715 : Blo 1969435 2956715 := bstep (se 1 (by rfl) ⟨2217536, by rfl⟩ : syracuseStep 2956715 = 4435073) B4435073
theorem B1971143 : Blo 1969435 1971143 := bstep (se 1 (by rfl) ⟨1478357, by rfl⟩ : syracuseStep 1971143 = 2956715) B2956715
theorem B2217541 : Blo 1969435 2217541 := bbase (se 4 (by rfl) ⟨207894, by rfl⟩ : syracuseStep 2217541 = 415789) (by norm_num)
theorem B2956721 : Blo 1969435 2956721 := bstep (se 2 (by rfl) ⟨1108770, by rfl⟩ : syracuseStep 2956721 = 2217541) B2217541
theorem B1971147 : Blo 1969435 1971147 := bstep (se 1 (by rfl) ⟨1478360, by rfl⟩ : syracuseStep 1971147 = 2956721) B2956721
theorem B3742109 : Blo 1969435 3742109 := bbase (se 3 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 3742109 = 1403291) (by norm_num)
theorem B2494739 : Blo 1969435 2494739 := bstep (se 1 (by rfl) ⟨1871054, by rfl⟩ : syracuseStep 2494739 = 3742109) B3742109
theorem B6652637 : Blo 1969435 6652637 := bstep (se 3 (by rfl) ⟨1247369, by rfl⟩ : syracuseStep 6652637 = 2494739) B2494739
theorem B4435091 : Blo 1969435 4435091 := bstep (se 1 (by rfl) ⟨3326318, by rfl⟩ : syracuseStep 4435091 = 6652637) B6652637
theorem B2956727 : Blo 1969435 2956727 := bstep (se 1 (by rfl) ⟨2217545, by rfl⟩ : syracuseStep 2956727 = 4435091) B4435091
theorem B1971151 : Blo 1969435 1971151 := bstep (se 1 (by rfl) ⟨1478363, by rfl⟩ : syracuseStep 1971151 = 2956727) B2956727
theorem B2956733 : Blo 1969435 2956733 := bbase (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) (by norm_num)
theorem B1971155 : Blo 1969435 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B4435109 : Blo 1969435 4435109 := bbase (se 4 (by rfl) ⟨415791, by rfl⟩ : syracuseStep 4435109 = 831583) (by norm_num)
theorem B2956739 : Blo 1969435 2956739 := bstep (se 1 (by rfl) ⟨2217554, by rfl⟩ : syracuseStep 2956739 = 4435109) B4435109
theorem B1971159 : Blo 1969435 1971159 := bstep (se 1 (by rfl) ⟨1478369, by rfl⟩ : syracuseStep 1971159 = 2956739) B2956739
theorem B4989509 : Blo 1969435 4989509 := bbase (se 4 (by rfl) ⟨467766, by rfl⟩ : syracuseStep 4989509 = 935533) (by norm_num)
theorem B3326339 : Blo 1969435 3326339 := bstep (se 1 (by rfl) ⟨2494754, by rfl⟩ : syracuseStep 3326339 = 4989509) B4989509
theorem B2217559 : Blo 1969435 2217559 := bstep (se 1 (by rfl) ⟨1663169, by rfl⟩ : syracuseStep 2217559 = 3326339) B3326339
theorem B2956745 : Blo 1969435 2956745 := bstep (se 2 (by rfl) ⟨1108779, by rfl⟩ : syracuseStep 2956745 = 2217559) B2217559
theorem B1971163 : Blo 1969435 1971163 := bstep (se 1 (by rfl) ⟨1478372, by rfl⟩ : syracuseStep 1971163 = 2956745) B2956745
theorem B2368073 : Blo 1969435 2368073 := bbase (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) (by norm_num)
theorem B6314861 : Blo 1969435 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B4209907 : Blo 1969435 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B5613209 : Blo 1969435 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B3742139 : Blo 1969435 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B9979037 : Blo 1969435 9979037 := bstep (se 3 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 9979037 = 3742139) B3742139
theorem B6652691 : Blo 1969435 6652691 := bstep (se 1 (by rfl) ⟨4989518, by rfl⟩ : syracuseStep 6652691 = 9979037) B9979037
theorem B4435127 : Blo 1969435 4435127 := bstep (se 1 (by rfl) ⟨3326345, by rfl⟩ : syracuseStep 4435127 = 6652691) B6652691
theorem B2956751 : Blo 1969435 2956751 := bstep (se 1 (by rfl) ⟨2217563, by rfl⟩ : syracuseStep 2956751 = 4435127) B4435127
theorem B1971167 : Blo 1969435 1971167 := bstep (se 1 (by rfl) ⟨1478375, by rfl⟩ : syracuseStep 1971167 = 2956751) B2956751
theorem B2956757 : Blo 1969435 2956757 := bbase (se 7 (by rfl) ⟨34649, by rfl⟩ : syracuseStep 2956757 = 69299) (by norm_num)
theorem B1971171 : Blo 1969435 1971171 := bstep (se 1 (by rfl) ⟨1478378, by rfl⟩ : syracuseStep 1971171 = 2956757) B2956757
theorem B7484309 : Blo 1969435 7484309 := bbase (se 6 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 7484309 = 350827) (by norm_num)
theorem B4989539 : Blo 1969435 4989539 := bstep (se 1 (by rfl) ⟨3742154, by rfl⟩ : syracuseStep 4989539 = 7484309) B7484309
theorem B3326359 : Blo 1969435 3326359 := bstep (se 1 (by rfl) ⟨2494769, by rfl⟩ : syracuseStep 3326359 = 4989539) B4989539
theorem B4435145 : Blo 1969435 4435145 := bstep (se 2 (by rfl) ⟨1663179, by rfl⟩ : syracuseStep 4435145 = 3326359) B3326359
theorem B2956763 : Blo 1969435 2956763 := bstep (se 1 (by rfl) ⟨2217572, by rfl⟩ : syracuseStep 2956763 = 4435145) B4435145
theorem B1971175 : Blo 1969435 1971175 := bstep (se 1 (by rfl) ⟨1478381, by rfl⟩ : syracuseStep 1971175 = 2956763) B2956763
theorem B2217577 : Blo 1969435 2217577 := bbase (se 2 (by rfl) ⟨831591, by rfl⟩ : syracuseStep 2217577 = 1663183) (by norm_num)
theorem B2956769 : Blo 1969435 2956769 := bstep (se 2 (by rfl) ⟨1108788, by rfl⟩ : syracuseStep 2956769 = 2217577) B2217577
theorem B1971179 : Blo 1969435 1971179 := bstep (se 1 (by rfl) ⟨1478384, by rfl⟩ : syracuseStep 1971179 = 2956769) B2956769
theorem B4209941 : Blo 1969435 4209941 := bbase (se 6 (by rfl) ⟨98670, by rfl⟩ : syracuseStep 4209941 = 197341) (by norm_num)
theorem B11226509 : Blo 1969435 11226509 := bstep (se 3 (by rfl) ⟨2104970, by rfl⟩ : syracuseStep 11226509 = 4209941) B4209941
theorem B7484339 : Blo 1969435 7484339 := bstep (se 1 (by rfl) ⟨5613254, by rfl⟩ : syracuseStep 7484339 = 11226509) B11226509
theorem B4989559 : Blo 1969435 4989559 := bstep (se 1 (by rfl) ⟨3742169, by rfl⟩ : syracuseStep 4989559 = 7484339) B7484339
theorem B6652745 : Blo 1969435 6652745 := bstep (se 2 (by rfl) ⟨2494779, by rfl⟩ : syracuseStep 6652745 = 4989559) B4989559
theorem B4435163 : Blo 1969435 4435163 := bstep (se 1 (by rfl) ⟨3326372, by rfl⟩ : syracuseStep 4435163 = 6652745) B6652745
theorem B2956775 : Blo 1969435 2956775 := bstep (se 1 (by rfl) ⟨2217581, by rfl⟩ : syracuseStep 2956775 = 4435163) B4435163
theorem B1971183 : Blo 1969435 1971183 := bstep (se 1 (by rfl) ⟨1478387, by rfl⟩ : syracuseStep 1971183 = 2956775) B2956775
theorem B2956781 : Blo 1969435 2956781 := bbase (se 3 (by rfl) ⟨554396, by rfl⟩ : syracuseStep 2956781 = 1108793) (by norm_num)
theorem B1971187 : Blo 1969435 1971187 := bstep (se 1 (by rfl) ⟨1478390, by rfl⟩ : syracuseStep 1971187 = 2956781) B2956781
theorem B4435181 : Blo 1969435 4435181 := bbase (se 3 (by rfl) ⟨831596, by rfl⟩ : syracuseStep 4435181 = 1663193) (by norm_num)
theorem B2956787 : Blo 1969435 2956787 := bstep (se 1 (by rfl) ⟨2217590, by rfl⟩ : syracuseStep 2956787 = 4435181) B4435181
theorem B1971191 : Blo 1969435 1971191 := bstep (se 1 (by rfl) ⟨1478393, by rfl⟩ : syracuseStep 1971191 = 2956787) B2956787
theorem B2806645 : Blo 1969435 2806645 := bbase (se 5 (by rfl) ⟨131561, by rfl⟩ : syracuseStep 2806645 = 263123) (by norm_num)
theorem B3742193 : Blo 1969435 3742193 := bstep (se 2 (by rfl) ⟨1403322, by rfl⟩ : syracuseStep 3742193 = 2806645) B2806645
theorem B2494795 : Blo 1969435 2494795 := bstep (se 1 (by rfl) ⟨1871096, by rfl⟩ : syracuseStep 2494795 = 3742193) B3742193
theorem B3326393 : Blo 1969435 3326393 := bstep (se 2 (by rfl) ⟨1247397, by rfl⟩ : syracuseStep 3326393 = 2494795) B2494795
theorem B2217595 : Blo 1969435 2217595 := bstep (se 1 (by rfl) ⟨1663196, by rfl⟩ : syracuseStep 2217595 = 3326393) B3326393
theorem B2956793 : Blo 1969435 2956793 := bstep (se 2 (by rfl) ⟨1108797, by rfl⟩ : syracuseStep 2956793 = 2217595) B2217595
theorem B1971195 : Blo 1969435 1971195 := bstep (se 1 (by rfl) ⟨1478396, by rfl⟩ : syracuseStep 1971195 = 2956793) B2956793
theorem B2400421 : Blo 1969435 2400421 := bbase (se 4 (by rfl) ⟨225039, by rfl⟩ : syracuseStep 2400421 = 450079) (by norm_num)
theorem B3200561 : Blo 1969435 3200561 := bstep (se 2 (by rfl) ⟨1200210, by rfl⟩ : syracuseStep 3200561 = 2400421) B2400421
theorem B2133707 : Blo 1969435 2133707 := bstep (se 1 (by rfl) ⟨1600280, by rfl⟩ : syracuseStep 2133707 = 3200561) B3200561
theorem B22759541 : Blo 1969435 22759541 := bstep (se 5 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 22759541 = 2133707) B2133707
theorem B15173027 : Blo 1969435 15173027 := bstep (se 1 (by rfl) ⟨11379770, by rfl⟩ : syracuseStep 15173027 = 22759541) B22759541
theorem B10115351 : Blo 1969435 10115351 := bstep (se 1 (by rfl) ⟨7586513, by rfl⟩ : syracuseStep 10115351 = 15173027) B15173027
theorem B6743567 : Blo 1969435 6743567 := bstep (se 1 (by rfl) ⟨5057675, by rfl⟩ : syracuseStep 6743567 = 10115351) B10115351
theorem B4495711 : Blo 1969435 4495711 := bstep (se 1 (by rfl) ⟨3371783, by rfl⟩ : syracuseStep 4495711 = 6743567) B6743567
theorem B5994281 : Blo 1969435 5994281 := bstep (se 2 (by rfl) ⟨2247855, by rfl⟩ : syracuseStep 5994281 = 4495711) B4495711
theorem B15984749 : Blo 1969435 15984749 := bstep (se 3 (by rfl) ⟨2997140, by rfl⟩ : syracuseStep 15984749 = 5994281) B5994281
theorem B42625997 : Blo 1969435 42625997 := bstep (se 3 (by rfl) ⟨7992374, by rfl⟩ : syracuseStep 42625997 = 15984749) B15984749
theorem B28417331 : Blo 1969435 28417331 := bstep (se 1 (by rfl) ⟨21312998, by rfl⟩ : syracuseStep 28417331 = 42625997) B42625997
theorem B75779549 : Blo 1969435 75779549 := bstep (se 3 (by rfl) ⟨14208665, by rfl⟩ : syracuseStep 75779549 = 28417331) B28417331
theorem B50519699 : Blo 1969435 50519699 := bstep (se 1 (by rfl) ⟨37889774, by rfl⟩ : syracuseStep 50519699 = 75779549) B75779549
theorem B33679799 : Blo 1969435 33679799 := bstep (se 1 (by rfl) ⟨25259849, by rfl⟩ : syracuseStep 33679799 = 50519699) B50519699
theorem B22453199 : Blo 1969435 22453199 := bstep (se 1 (by rfl) ⟨16839899, by rfl⟩ : syracuseStep 22453199 = 33679799) B33679799
theorem B14968799 : Blo 1969435 14968799 := bstep (se 1 (by rfl) ⟨11226599, by rfl⟩ : syracuseStep 14968799 = 22453199) B22453199
theorem B9979199 : Blo 1969435 9979199 := bstep (se 1 (by rfl) ⟨7484399, by rfl⟩ : syracuseStep 9979199 = 14968799) B14968799
theorem B6652799 : Blo 1969435 6652799 := bstep (se 1 (by rfl) ⟨4989599, by rfl⟩ : syracuseStep 6652799 = 9979199) B9979199
theorem B4435199 : Blo 1969435 4435199 := bstep (se 1 (by rfl) ⟨3326399, by rfl⟩ : syracuseStep 4435199 = 6652799) B6652799
theorem B2956799 : Blo 1969435 2956799 := bstep (se 1 (by rfl) ⟨2217599, by rfl⟩ : syracuseStep 2956799 = 4435199) B4435199
theorem B1971199 : Blo 1969435 1971199 := bstep (se 1 (by rfl) ⟨1478399, by rfl⟩ : syracuseStep 1971199 = 2956799) B2956799
theorem B2956805 : Blo 1969435 2956805 := bbase (se 4 (by rfl) ⟨277200, by rfl⟩ : syracuseStep 2956805 = 554401) (by norm_num)
theorem B1971203 : Blo 1969435 1971203 := bstep (se 1 (by rfl) ⟨1478402, by rfl⟩ : syracuseStep 1971203 = 2956805) B2956805
theorem B3326413 : Blo 1969435 3326413 := bbase (se 3 (by rfl) ⟨623702, by rfl⟩ : syracuseStep 3326413 = 1247405) (by norm_num)
theorem B4435217 : Blo 1969435 4435217 := bstep (se 2 (by rfl) ⟨1663206, by rfl⟩ : syracuseStep 4435217 = 3326413) B3326413
theorem B2956811 : Blo 1969435 2956811 := bstep (se 1 (by rfl) ⟨2217608, by rfl⟩ : syracuseStep 2956811 = 4435217) B4435217
theorem B1971207 : Blo 1969435 1971207 := bstep (se 1 (by rfl) ⟨1478405, by rfl⟩ : syracuseStep 1971207 = 2956811) B2956811
theorem B2217613 : Blo 1969435 2217613 := bbase (se 3 (by rfl) ⟨415802, by rfl⟩ : syracuseStep 2217613 = 831605) (by norm_num)
theorem B2956817 : Blo 1969435 2956817 := bstep (se 2 (by rfl) ⟨1108806, by rfl⟩ : syracuseStep 2956817 = 2217613) B2217613
theorem B1971211 : Blo 1969435 1971211 := bstep (se 1 (by rfl) ⟨1478408, by rfl⟩ : syracuseStep 1971211 = 2956817) B2956817
theorem B6652853 : Blo 1969435 6652853 := bbase (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) (by norm_num)
theorem B4435235 : Blo 1969435 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B2956823 : Blo 1969435 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B1971215 : Blo 1969435 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B2956829 : Blo 1969435 2956829 := bbase (se 3 (by rfl) ⟨554405, by rfl⟩ : syracuseStep 2956829 = 1108811) (by norm_num)
theorem B1971219 : Blo 1969435 1971219 := bstep (se 1 (by rfl) ⟨1478414, by rfl⟩ : syracuseStep 1971219 = 2956829) B2956829
theorem B4435253 : Blo 1969435 4435253 := bbase (se 5 (by rfl) ⟨207902, by rfl⟩ : syracuseStep 4435253 = 415805) (by norm_num)
theorem B2956835 : Blo 1969435 2956835 := bstep (se 1 (by rfl) ⟨2217626, by rfl⟩ : syracuseStep 2956835 = 4435253) B4435253
theorem B1971223 : Blo 1969435 1971223 := bstep (se 1 (by rfl) ⟨1478417, by rfl⟩ : syracuseStep 1971223 = 2956835) B2956835
theorem B2433205 : Blo 1969435 2433205 := bbase (se 5 (by rfl) ⟨114056, by rfl⟩ : syracuseStep 2433205 = 228113) (by norm_num)
theorem B12977093 : Blo 1969435 12977093 := bstep (se 4 (by rfl) ⟨1216602, by rfl⟩ : syracuseStep 12977093 = 2433205) B2433205
theorem B8651395 : Blo 1969435 8651395 := bstep (se 1 (by rfl) ⟨6488546, by rfl⟩ : syracuseStep 8651395 = 12977093) B12977093
theorem B11535193 : Blo 1969435 11535193 := bstep (se 2 (by rfl) ⟨4325697, by rfl⟩ : syracuseStep 11535193 = 8651395) B8651395
theorem B15380257 : Blo 1969435 15380257 := bstep (se 2 (by rfl) ⟨5767596, by rfl⟩ : syracuseStep 15380257 = 11535193) B11535193
theorem B20507009 : Blo 1969435 20507009 := bstep (se 2 (by rfl) ⟨7690128, by rfl⟩ : syracuseStep 20507009 = 15380257) B15380257
theorem B54685357 : Blo 1969435 54685357 := bstep (se 3 (by rfl) ⟨10253504, by rfl⟩ : syracuseStep 54685357 = 20507009) B20507009
theorem B291655237 : Blo 1969435 291655237 := bstep (se 4 (by rfl) ⟨27342678, by rfl⟩ : syracuseStep 291655237 = 54685357) B54685357
theorem B388873649 : Blo 1969435 388873649 := bstep (se 2 (by rfl) ⟨145827618, by rfl⟩ : syracuseStep 388873649 = 291655237) B291655237
theorem B259249099 : Blo 1969435 259249099 := bstep (se 1 (by rfl) ⟨194436824, by rfl⟩ : syracuseStep 259249099 = 388873649) B388873649
theorem B345665465 : Blo 1969435 345665465 := bstep (se 2 (by rfl) ⟨129624549, by rfl⟩ : syracuseStep 345665465 = 259249099) B259249099
theorem B230443643 : Blo 1969435 230443643 := bstep (se 1 (by rfl) ⟨172832732, by rfl⟩ : syracuseStep 230443643 = 345665465) B345665465
theorem B614516381 : Blo 1969435 614516381 := bstep (se 3 (by rfl) ⟨115221821, by rfl⟩ : syracuseStep 614516381 = 230443643) B230443643
theorem B409677587 : Blo 1969435 409677587 := bstep (se 1 (by rfl) ⟨307258190, by rfl⟩ : syracuseStep 409677587 = 614516381) B614516381
theorem B273118391 : Blo 1969435 273118391 := bstep (se 1 (by rfl) ⟨204838793, by rfl⟩ : syracuseStep 273118391 = 409677587) B409677587
theorem B182078927 : Blo 1969435 182078927 := bstep (se 1 (by rfl) ⟨136559195, by rfl⟩ : syracuseStep 182078927 = 273118391) B273118391
theorem B121385951 : Blo 1969435 121385951 := bstep (se 1 (by rfl) ⟨91039463, by rfl⟩ : syracuseStep 121385951 = 182078927) B182078927
theorem B80923967 : Blo 1969435 80923967 := bstep (se 1 (by rfl) ⟨60692975, by rfl⟩ : syracuseStep 80923967 = 121385951) B121385951
theorem B53949311 : Blo 1969435 53949311 := bstep (se 1 (by rfl) ⟨40461983, by rfl⟩ : syracuseStep 53949311 = 80923967) B80923967
theorem B35966207 : Blo 1969435 35966207 := bstep (se 1 (by rfl) ⟨26974655, by rfl⟩ : syracuseStep 35966207 = 53949311) B53949311
theorem B23977471 : Blo 1969435 23977471 := bstep (se 1 (by rfl) ⟨17983103, by rfl⟩ : syracuseStep 23977471 = 35966207) B35966207
theorem B31969961 : Blo 1969435 31969961 := bstep (se 2 (by rfl) ⟨11988735, by rfl⟩ : syracuseStep 31969961 = 23977471) B23977471
theorem B21313307 : Blo 1969435 21313307 := bstep (se 1 (by rfl) ⟨15984980, by rfl⟩ : syracuseStep 21313307 = 31969961) B31969961
theorem B14208871 : Blo 1969435 14208871 := bstep (se 1 (by rfl) ⟨10656653, by rfl⟩ : syracuseStep 14208871 = 21313307) B21313307
theorem B18945161 : Blo 1969435 18945161 := bstep (se 2 (by rfl) ⟨7104435, by rfl⟩ : syracuseStep 18945161 = 14208871) B14208871
theorem B12630107 : Blo 1969435 12630107 := bstep (se 1 (by rfl) ⟨9472580, by rfl⟩ : syracuseStep 12630107 = 18945161) B18945161
theorem B8420071 : Blo 1969435 8420071 := bstep (se 1 (by rfl) ⟨6315053, by rfl⟩ : syracuseStep 8420071 = 12630107) B12630107
theorem B11226761 : Blo 1969435 11226761 := bstep (se 2 (by rfl) ⟨4210035, by rfl⟩ : syracuseStep 11226761 = 8420071) B8420071
theorem B7484507 : Blo 1969435 7484507 := bstep (se 1 (by rfl) ⟨5613380, by rfl⟩ : syracuseStep 7484507 = 11226761) B11226761
theorem B4989671 : Blo 1969435 4989671 := bstep (se 1 (by rfl) ⟨3742253, by rfl⟩ : syracuseStep 4989671 = 7484507) B7484507
theorem B3326447 : Blo 1969435 3326447 := bstep (se 1 (by rfl) ⟨2494835, by rfl⟩ : syracuseStep 3326447 = 4989671) B4989671
theorem B2217631 : Blo 1969435 2217631 := bstep (se 1 (by rfl) ⟨1663223, by rfl⟩ : syracuseStep 2217631 = 3326447) B3326447
theorem B2956841 : Blo 1969435 2956841 := bstep (se 2 (by rfl) ⟨1108815, by rfl⟩ : syracuseStep 2956841 = 2217631) B2217631
theorem B1971227 : Blo 1969435 1971227 := bstep (se 1 (by rfl) ⟨1478420, by rfl⟩ : syracuseStep 1971227 = 2956841) B2956841
theorem B3996253 : Blo 1969435 3996253 := bbase (se 3 (by rfl) ⟨749297, by rfl⟩ : syracuseStep 3996253 = 1498595) (by norm_num)
theorem B5328337 : Blo 1969435 5328337 := bstep (se 2 (by rfl) ⟨1998126, by rfl⟩ : syracuseStep 5328337 = 3996253) B3996253
theorem B7104449 : Blo 1969435 7104449 := bstep (se 2 (by rfl) ⟨2664168, by rfl⟩ : syracuseStep 7104449 = 5328337) B5328337
theorem B18945197 : Blo 1969435 18945197 := bstep (se 3 (by rfl) ⟨3552224, by rfl⟩ : syracuseStep 18945197 = 7104449) B7104449
theorem B12630131 : Blo 1969435 12630131 := bstep (se 1 (by rfl) ⟨9472598, by rfl⟩ : syracuseStep 12630131 = 18945197) B18945197
theorem B8420087 : Blo 1969435 8420087 := bstep (se 1 (by rfl) ⟨6315065, by rfl⟩ : syracuseStep 8420087 = 12630131) B12630131
theorem B5613391 : Blo 1969435 5613391 := bstep (se 1 (by rfl) ⟨4210043, by rfl⟩ : syracuseStep 5613391 = 8420087) B8420087
theorem B7484521 : Blo 1969435 7484521 := bstep (se 2 (by rfl) ⟨2806695, by rfl⟩ : syracuseStep 7484521 = 5613391) B5613391
theorem B9979361 : Blo 1969435 9979361 := bstep (se 2 (by rfl) ⟨3742260, by rfl⟩ : syracuseStep 9979361 = 7484521) B7484521
theorem B6652907 : Blo 1969435 6652907 := bstep (se 1 (by rfl) ⟨4989680, by rfl⟩ : syracuseStep 6652907 = 9979361) B9979361
theorem B4435271 : Blo 1969435 4435271 := bstep (se 1 (by rfl) ⟨3326453, by rfl⟩ : syracuseStep 4435271 = 6652907) B6652907
theorem B2956847 : Blo 1969435 2956847 := bstep (se 1 (by rfl) ⟨2217635, by rfl⟩ : syracuseStep 2956847 = 4435271) B4435271
theorem B1971231 : Blo 1969435 1971231 := bstep (se 1 (by rfl) ⟨1478423, by rfl⟩ : syracuseStep 1971231 = 2956847) B2956847
theorem B2956853 : Blo 1969435 2956853 := bbase (se 5 (by rfl) ⟨138602, by rfl⟩ : syracuseStep 2956853 = 277205) (by norm_num)
theorem B1971235 : Blo 1969435 1971235 := bstep (se 1 (by rfl) ⟨1478426, by rfl⟩ : syracuseStep 1971235 = 2956853) B2956853
theorem B4989701 : Blo 1969435 4989701 := bbase (se 4 (by rfl) ⟨467784, by rfl⟩ : syracuseStep 4989701 = 935569) (by norm_num)
theorem B3326467 : Blo 1969435 3326467 := bstep (se 1 (by rfl) ⟨2494850, by rfl⟩ : syracuseStep 3326467 = 4989701) B4989701
theorem B4435289 : Blo 1969435 4435289 := bstep (se 2 (by rfl) ⟨1663233, by rfl⟩ : syracuseStep 4435289 = 3326467) B3326467
theorem B2956859 : Blo 1969435 2956859 := bstep (se 1 (by rfl) ⟨2217644, by rfl⟩ : syracuseStep 2956859 = 4435289) B4435289
theorem B1971239 : Blo 1969435 1971239 := bstep (se 1 (by rfl) ⟨1478429, by rfl⟩ : syracuseStep 1971239 = 2956859) B2956859
theorem B2217649 : Blo 1969435 2217649 := bbase (se 2 (by rfl) ⟨831618, by rfl⟩ : syracuseStep 2217649 = 1663237) (by norm_num)
theorem B2956865 : Blo 1969435 2956865 := bstep (se 2 (by rfl) ⟨1108824, by rfl⟩ : syracuseStep 2956865 = 2217649) B2217649
theorem B1971243 : Blo 1969435 1971243 := bstep (se 1 (by rfl) ⟨1478432, by rfl⟩ : syracuseStep 1971243 = 2956865) B2956865
theorem B2162873 : Blo 1969435 2162873 := bbase (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) (by norm_num)
theorem B5767661 : Blo 1969435 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B3845107 : Blo 1969435 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B5126809 : Blo 1969435 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B6835745 : Blo 1969435 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B4557163 : Blo 1969435 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B6076217 : Blo 1969435 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B4050811 : Blo 1969435 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B5401081 : Blo 1969435 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B7201441 : Blo 1969435 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B9601921 : Blo 1969435 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B51210245 : Blo 1969435 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B34140163 : Blo 1969435 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B45520217 : Blo 1969435 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B30346811 : Blo 1969435 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B20231207 : Blo 1969435 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B13487471 : Blo 1969435 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B8991647 : Blo 1969435 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B5994431 : Blo 1969435 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B3996287 : Blo 1969435 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B2664191 : Blo 1969435 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B7104509 : Blo 1969435 7104509 := bstep (se 3 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 7104509 = 2664191) B2664191
theorem B4736339 : Blo 1969435 4736339 := bstep (se 1 (by rfl) ⟨3552254, by rfl⟩ : syracuseStep 4736339 = 7104509) B7104509
theorem B3157559 : Blo 1969435 3157559 := bstep (se 1 (by rfl) ⟨2368169, by rfl⟩ : syracuseStep 3157559 = 4736339) B4736339
theorem B2105039 : Blo 1969435 2105039 := bstep (se 1 (by rfl) ⟨1578779, by rfl⟩ : syracuseStep 2105039 = 3157559) B3157559
theorem B5613437 : Blo 1969435 5613437 := bstep (se 3 (by rfl) ⟨1052519, by rfl⟩ : syracuseStep 5613437 = 2105039) B2105039
theorem B3742291 : Blo 1969435 3742291 := bstep (se 1 (by rfl) ⟨2806718, by rfl⟩ : syracuseStep 3742291 = 5613437) B5613437
theorem B4989721 : Blo 1969435 4989721 := bstep (se 2 (by rfl) ⟨1871145, by rfl⟩ : syracuseStep 4989721 = 3742291) B3742291
theorem B6652961 : Blo 1969435 6652961 := bstep (se 2 (by rfl) ⟨2494860, by rfl⟩ : syracuseStep 6652961 = 4989721) B4989721
theorem B4435307 : Blo 1969435 4435307 := bstep (se 1 (by rfl) ⟨3326480, by rfl⟩ : syracuseStep 4435307 = 6652961) B6652961
theorem B2956871 : Blo 1969435 2956871 := bstep (se 1 (by rfl) ⟨2217653, by rfl⟩ : syracuseStep 2956871 = 4435307) B4435307
theorem B1971247 : Blo 1969435 1971247 := bstep (se 1 (by rfl) ⟨1478435, by rfl⟩ : syracuseStep 1971247 = 2956871) B2956871
theorem B2956877 : Blo 1969435 2956877 := bbase (se 3 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 2956877 = 1108829) (by norm_num)
theorem B1971251 : Blo 1969435 1971251 := bstep (se 1 (by rfl) ⟨1478438, by rfl⟩ : syracuseStep 1971251 = 2956877) B2956877
theorem B4435325 : Blo 1969435 4435325 := bbase (se 3 (by rfl) ⟨831623, by rfl⟩ : syracuseStep 4435325 = 1663247) (by norm_num)
theorem B2956883 : Blo 1969435 2956883 := bstep (se 1 (by rfl) ⟨2217662, by rfl⟩ : syracuseStep 2956883 = 4435325) B4435325
theorem B1971255 : Blo 1969435 1971255 := bstep (se 1 (by rfl) ⟨1478441, by rfl⟩ : syracuseStep 1971255 = 2956883) B2956883
theorem B3326501 : Blo 1969435 3326501 := bbase (se 4 (by rfl) ⟨311859, by rfl⟩ : syracuseStep 3326501 = 623719) (by norm_num)
theorem B2217667 : Blo 1969435 2217667 := bstep (se 1 (by rfl) ⟨1663250, by rfl⟩ : syracuseStep 2217667 = 3326501) B3326501
theorem B2956889 : Blo 1969435 2956889 := bstep (se 2 (by rfl) ⟨1108833, by rfl⟩ : syracuseStep 2956889 = 2217667) B2217667
theorem B1971259 : Blo 1969435 1971259 := bstep (se 1 (by rfl) ⟨1478444, by rfl⟩ : syracuseStep 1971259 = 2956889) B2956889
theorem B2806741 : Blo 1969435 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B14969285 : Blo 1969435 14969285 := bstep (se 4 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 14969285 = 2806741) B2806741
theorem B9979523 : Blo 1969435 9979523 := bstep (se 1 (by rfl) ⟨7484642, by rfl⟩ : syracuseStep 9979523 = 14969285) B14969285
theorem B6653015 : Blo 1969435 6653015 := bstep (se 1 (by rfl) ⟨4989761, by rfl⟩ : syracuseStep 6653015 = 9979523) B9979523
theorem B4435343 : Blo 1969435 4435343 := bstep (se 1 (by rfl) ⟨3326507, by rfl⟩ : syracuseStep 4435343 = 6653015) B6653015
theorem B2956895 : Blo 1969435 2956895 := bstep (se 1 (by rfl) ⟨2217671, by rfl⟩ : syracuseStep 2956895 = 4435343) B4435343
theorem B1971263 : Blo 1969435 1971263 := bstep (se 1 (by rfl) ⟨1478447, by rfl⟩ : syracuseStep 1971263 = 2956895) B2956895
theorem B2956901 : Blo 1969435 2956901 := bbase (se 4 (by rfl) ⟨277209, by rfl⟩ : syracuseStep 2956901 = 554419) (by norm_num)
theorem B1971267 : Blo 1969435 1971267 := bstep (se 1 (by rfl) ⟨1478450, by rfl⟩ : syracuseStep 1971267 = 2956901) B2956901
theorem B2105065 : Blo 1969435 2105065 := bbase (se 2 (by rfl) ⟨789399, by rfl⟩ : syracuseStep 2105065 = 1578799) (by norm_num)
theorem B2806753 : Blo 1969435 2806753 := bstep (se 2 (by rfl) ⟨1052532, by rfl⟩ : syracuseStep 2806753 = 2105065) B2105065
theorem B3742337 : Blo 1969435 3742337 := bstep (se 2 (by rfl) ⟨1403376, by rfl⟩ : syracuseStep 3742337 = 2806753) B2806753
theorem B2494891 : Blo 1969435 2494891 := bstep (se 1 (by rfl) ⟨1871168, by rfl⟩ : syracuseStep 2494891 = 3742337) B3742337
theorem B3326521 : Blo 1969435 3326521 := bstep (se 2 (by rfl) ⟨1247445, by rfl⟩ : syracuseStep 3326521 = 2494891) B2494891
theorem B4435361 : Blo 1969435 4435361 := bstep (se 2 (by rfl) ⟨1663260, by rfl⟩ : syracuseStep 4435361 = 3326521) B3326521
theorem B2956907 : Blo 1969435 2956907 := bstep (se 1 (by rfl) ⟨2217680, by rfl⟩ : syracuseStep 2956907 = 4435361) B4435361
theorem B1971271 : Blo 1969435 1971271 := bstep (se 1 (by rfl) ⟨1478453, by rfl⟩ : syracuseStep 1971271 = 2956907) B2956907
theorem B2217685 : Blo 1969435 2217685 := bbase (se 7 (by rfl) ⟨25988, by rfl⟩ : syracuseStep 2217685 = 51977) (by norm_num)
theorem B2956913 : Blo 1969435 2956913 := bstep (se 2 (by rfl) ⟨1108842, by rfl⟩ : syracuseStep 2956913 = 2217685) B2217685
theorem B1971275 : Blo 1969435 1971275 := bstep (se 1 (by rfl) ⟨1478456, by rfl⟩ : syracuseStep 1971275 = 2956913) B2956913
theorem B2494901 : Blo 1969435 2494901 := bbase (se 5 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 2494901 = 233897) (by norm_num)
theorem B6653069 : Blo 1969435 6653069 := bstep (se 3 (by rfl) ⟨1247450, by rfl⟩ : syracuseStep 6653069 = 2494901) B2494901
theorem B4435379 : Blo 1969435 4435379 := bstep (se 1 (by rfl) ⟨3326534, by rfl⟩ : syracuseStep 4435379 = 6653069) B6653069
theorem B2956919 : Blo 1969435 2956919 := bstep (se 1 (by rfl) ⟨2217689, by rfl⟩ : syracuseStep 2956919 = 4435379) B4435379
theorem B1971279 : Blo 1969435 1971279 := bstep (se 1 (by rfl) ⟨1478459, by rfl⟩ : syracuseStep 1971279 = 2956919) B2956919
theorem B2956925 : Blo 1969435 2956925 := bbase (se 3 (by rfl) ⟨554423, by rfl⟩ : syracuseStep 2956925 = 1108847) (by norm_num)
theorem B1971283 : Blo 1969435 1971283 := bstep (se 1 (by rfl) ⟨1478462, by rfl⟩ : syracuseStep 1971283 = 2956925) B2956925
theorem B4435397 : Blo 1969435 4435397 := bbase (se 4 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 4435397 = 831637) (by norm_num)
theorem B2956931 : Blo 1969435 2956931 := bstep (se 1 (by rfl) ⟨2217698, by rfl⟩ : syracuseStep 2956931 = 4435397) B4435397
theorem B1971287 : Blo 1969435 1971287 := bstep (se 1 (by rfl) ⟨1478465, by rfl⟩ : syracuseStep 1971287 = 2956931) B2956931
theorem B4050901 : Blo 1969435 4050901 := bbase (se 7 (by rfl) ⟨47471, by rfl⟩ : syracuseStep 4050901 = 94943) (by norm_num)
theorem B21604805 : Blo 1969435 21604805 := bstep (se 4 (by rfl) ⟨2025450, by rfl⟩ : syracuseStep 21604805 = 4050901) B4050901
theorem B14403203 : Blo 1969435 14403203 := bstep (se 1 (by rfl) ⟨10802402, by rfl⟩ : syracuseStep 14403203 = 21604805) B21604805
theorem B9602135 : Blo 1969435 9602135 := bstep (se 1 (by rfl) ⟨7201601, by rfl⟩ : syracuseStep 9602135 = 14403203) B14403203
theorem B6401423 : Blo 1969435 6401423 := bstep (se 1 (by rfl) ⟨4801067, by rfl⟩ : syracuseStep 6401423 = 9602135) B9602135
theorem B4267615 : Blo 1969435 4267615 := bstep (se 1 (by rfl) ⟨3200711, by rfl⟩ : syracuseStep 4267615 = 6401423) B6401423
theorem B5690153 : Blo 1969435 5690153 := bstep (se 2 (by rfl) ⟨2133807, by rfl⟩ : syracuseStep 5690153 = 4267615) B4267615
theorem B3793435 : Blo 1969435 3793435 := bstep (se 1 (by rfl) ⟨2845076, by rfl⟩ : syracuseStep 3793435 = 5690153) B5690153
theorem B20231653 : Blo 1969435 20231653 := bstep (se 4 (by rfl) ⟨1896717, by rfl⟩ : syracuseStep 20231653 = 3793435) B3793435
theorem B26975537 : Blo 1969435 26975537 := bstep (se 2 (by rfl) ⟨10115826, by rfl⟩ : syracuseStep 26975537 = 20231653) B20231653
theorem B17983691 : Blo 1969435 17983691 := bstep (se 1 (by rfl) ⟨13487768, by rfl⟩ : syracuseStep 17983691 = 26975537) B26975537
theorem B11989127 : Blo 1969435 11989127 := bstep (se 1 (by rfl) ⟨8991845, by rfl⟩ : syracuseStep 11989127 = 17983691) B17983691
theorem B7992751 : Blo 1969435 7992751 := bstep (se 1 (by rfl) ⟨5994563, by rfl⟩ : syracuseStep 7992751 = 11989127) B11989127
theorem B10657001 : Blo 1969435 10657001 := bstep (se 2 (by rfl) ⟨3996375, by rfl⟩ : syracuseStep 10657001 = 7992751) B7992751
theorem B7104667 : Blo 1969435 7104667 := bstep (se 1 (by rfl) ⟨5328500, by rfl⟩ : syracuseStep 7104667 = 10657001) B10657001
theorem B9472889 : Blo 1969435 9472889 := bstep (se 2 (by rfl) ⟨3552333, by rfl⟩ : syracuseStep 9472889 = 7104667) B7104667
theorem B6315259 : Blo 1969435 6315259 := bstep (se 1 (by rfl) ⟨4736444, by rfl⟩ : syracuseStep 6315259 = 9472889) B9472889
theorem B8420345 : Blo 1969435 8420345 := bstep (se 2 (by rfl) ⟨3157629, by rfl⟩ : syracuseStep 8420345 = 6315259) B6315259
theorem B5613563 : Blo 1969435 5613563 := bstep (se 1 (by rfl) ⟨4210172, by rfl⟩ : syracuseStep 5613563 = 8420345) B8420345
theorem B3742375 : Blo 1969435 3742375 := bstep (se 1 (by rfl) ⟨2806781, by rfl⟩ : syracuseStep 3742375 = 5613563) B5613563
theorem B4989833 : Blo 1969435 4989833 := bstep (se 2 (by rfl) ⟨1871187, by rfl⟩ : syracuseStep 4989833 = 3742375) B3742375
theorem B3326555 : Blo 1969435 3326555 := bstep (se 1 (by rfl) ⟨2494916, by rfl⟩ : syracuseStep 3326555 = 4989833) B4989833
theorem B2217703 : Blo 1969435 2217703 := bstep (se 1 (by rfl) ⟨1663277, by rfl⟩ : syracuseStep 2217703 = 3326555) B3326555
theorem B2956937 : Blo 1969435 2956937 := bstep (se 2 (by rfl) ⟨1108851, by rfl⟩ : syracuseStep 2956937 = 2217703) B2217703
theorem B1971291 : Blo 1969435 1971291 := bstep (se 1 (by rfl) ⟨1478468, by rfl⟩ : syracuseStep 1971291 = 2956937) B2956937
theorem B9979685 : Blo 1969435 9979685 := bbase (se 4 (by rfl) ⟨935595, by rfl⟩ : syracuseStep 9979685 = 1871191) (by norm_num)
theorem B6653123 : Blo 1969435 6653123 := bstep (se 1 (by rfl) ⟨4989842, by rfl⟩ : syracuseStep 6653123 = 9979685) B9979685
theorem B4435415 : Blo 1969435 4435415 := bstep (se 1 (by rfl) ⟨3326561, by rfl⟩ : syracuseStep 4435415 = 6653123) B6653123
theorem B2956943 : Blo 1969435 2956943 := bstep (se 1 (by rfl) ⟨2217707, by rfl⟩ : syracuseStep 2956943 = 4435415) B4435415
theorem B1971295 : Blo 1969435 1971295 := bstep (se 1 (by rfl) ⟨1478471, by rfl⟩ : syracuseStep 1971295 = 2956943) B2956943
theorem B2956949 : Blo 1969435 2956949 := bbase (se 6 (by rfl) ⟨69303, by rfl⟩ : syracuseStep 2956949 = 138607) (by norm_num)
theorem B1971299 : Blo 1969435 1971299 := bstep (se 1 (by rfl) ⟨1478474, by rfl⟩ : syracuseStep 1971299 = 2956949) B2956949
theorem B7104709 : Blo 1969435 7104709 := bbase (se 4 (by rfl) ⟨666066, by rfl⟩ : syracuseStep 7104709 = 1332133) (by norm_num)
theorem B9472945 : Blo 1969435 9472945 := bstep (se 2 (by rfl) ⟨3552354, by rfl⟩ : syracuseStep 9472945 = 7104709) B7104709
theorem B12630593 : Blo 1969435 12630593 := bstep (se 2 (by rfl) ⟨4736472, by rfl⟩ : syracuseStep 12630593 = 9472945) B9472945
theorem B8420395 : Blo 1969435 8420395 := bstep (se 1 (by rfl) ⟨6315296, by rfl⟩ : syracuseStep 8420395 = 12630593) B12630593
theorem B11227193 : Blo 1969435 11227193 := bstep (se 2 (by rfl) ⟨4210197, by rfl⟩ : syracuseStep 11227193 = 8420395) B8420395
theorem B7484795 : Blo 1969435 7484795 := bstep (se 1 (by rfl) ⟨5613596, by rfl⟩ : syracuseStep 7484795 = 11227193) B11227193
theorem B4989863 : Blo 1969435 4989863 := bstep (se 1 (by rfl) ⟨3742397, by rfl⟩ : syracuseStep 4989863 = 7484795) B7484795
theorem B3326575 : Blo 1969435 3326575 := bstep (se 1 (by rfl) ⟨2494931, by rfl⟩ : syracuseStep 3326575 = 4989863) B4989863
theorem B4435433 : Blo 1969435 4435433 := bstep (se 2 (by rfl) ⟨1663287, by rfl⟩ : syracuseStep 4435433 = 3326575) B3326575
theorem B2956955 : Blo 1969435 2956955 := bstep (se 1 (by rfl) ⟨2217716, by rfl⟩ : syracuseStep 2956955 = 4435433) B4435433
theorem B1971303 : Blo 1969435 1971303 := bstep (se 1 (by rfl) ⟨1478477, by rfl⟩ : syracuseStep 1971303 = 2956955) B2956955
theorem B2217721 : Blo 1969435 2217721 := bbase (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) (by norm_num)
theorem B2956961 : Blo 1969435 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B1971307 : Blo 1969435 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B3157661 : Blo 1969435 3157661 := bbase (se 3 (by rfl) ⟨592061, by rfl⟩ : syracuseStep 3157661 = 1184123) (by norm_num)
theorem B8420429 : Blo 1969435 8420429 := bstep (se 3 (by rfl) ⟨1578830, by rfl⟩ : syracuseStep 8420429 = 3157661) B3157661
theorem B5613619 : Blo 1969435 5613619 := bstep (se 1 (by rfl) ⟨4210214, by rfl⟩ : syracuseStep 5613619 = 8420429) B8420429
theorem B7484825 : Blo 1969435 7484825 := bstep (se 2 (by rfl) ⟨2806809, by rfl⟩ : syracuseStep 7484825 = 5613619) B5613619
theorem B4989883 : Blo 1969435 4989883 := bstep (se 1 (by rfl) ⟨3742412, by rfl⟩ : syracuseStep 4989883 = 7484825) B7484825
theorem B6653177 : Blo 1969435 6653177 := bstep (se 2 (by rfl) ⟨2494941, by rfl⟩ : syracuseStep 6653177 = 4989883) B4989883
theorem B4435451 : Blo 1969435 4435451 := bstep (se 1 (by rfl) ⟨3326588, by rfl⟩ : syracuseStep 4435451 = 6653177) B6653177
theorem B2956967 : Blo 1969435 2956967 := bstep (se 1 (by rfl) ⟨2217725, by rfl⟩ : syracuseStep 2956967 = 4435451) B4435451
theorem B1971311 : Blo 1969435 1971311 := bstep (se 1 (by rfl) ⟨1478483, by rfl⟩ : syracuseStep 1971311 = 2956967) B2956967
theorem B2956973 : Blo 1969435 2956973 := bbase (se 3 (by rfl) ⟨554432, by rfl⟩ : syracuseStep 2956973 = 1108865) (by norm_num)
theorem B1971315 : Blo 1969435 1971315 := bstep (se 1 (by rfl) ⟨1478486, by rfl⟩ : syracuseStep 1971315 = 2956973) B2956973
theorem B4435469 : Blo 1969435 4435469 := bbase (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) (by norm_num)
theorem B2956979 : Blo 1969435 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1971319 : Blo 1969435 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B2494957 : Blo 1969435 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B3326609 : Blo 1969435 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2217739 : Blo 1969435 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B2956985 : Blo 1969435 2956985 := bstep (se 2 (by rfl) ⟨1108869, by rfl⟩ : syracuseStep 2956985 = 2217739) B2217739
theorem B1971323 : Blo 1969435 1971323 := bstep (se 1 (by rfl) ⟨1478492, by rfl⟩ : syracuseStep 1971323 = 2956985) B2956985
theorem B14209589 : Blo 1969435 14209589 := bbase (se 5 (by rfl) ⟨666074, by rfl⟩ : syracuseStep 14209589 = 1332149) (by norm_num)
theorem B9473059 : Blo 1969435 9473059 := bstep (se 1 (by rfl) ⟨7104794, by rfl⟩ : syracuseStep 9473059 = 14209589) B14209589
theorem B12630745 : Blo 1969435 12630745 := bstep (se 2 (by rfl) ⟨4736529, by rfl⟩ : syracuseStep 12630745 = 9473059) B9473059
theorem B16840993 : Blo 1969435 16840993 := bstep (se 2 (by rfl) ⟨6315372, by rfl⟩ : syracuseStep 16840993 = 12630745) B12630745
theorem B22454657 : Blo 1969435 22454657 := bstep (se 2 (by rfl) ⟨8420496, by rfl⟩ : syracuseStep 22454657 = 16840993) B16840993
theorem B14969771 : Blo 1969435 14969771 := bstep (se 1 (by rfl) ⟨11227328, by rfl⟩ : syracuseStep 14969771 = 22454657) B22454657
theorem B9979847 : Blo 1969435 9979847 := bstep (se 1 (by rfl) ⟨7484885, by rfl⟩ : syracuseStep 9979847 = 14969771) B14969771
theorem B6653231 : Blo 1969435 6653231 := bstep (se 1 (by rfl) ⟨4989923, by rfl⟩ : syracuseStep 6653231 = 9979847) B9979847
theorem B4435487 : Blo 1969435 4435487 := bstep (se 1 (by rfl) ⟨3326615, by rfl⟩ : syracuseStep 4435487 = 6653231) B6653231
theorem B2956991 : Blo 1969435 2956991 := bstep (se 1 (by rfl) ⟨2217743, by rfl⟩ : syracuseStep 2956991 = 4435487) B4435487
theorem B1971327 : Blo 1969435 1971327 := bstep (se 1 (by rfl) ⟨1478495, by rfl⟩ : syracuseStep 1971327 = 2956991) B2956991
theorem B2956997 : Blo 1969435 2956997 := bbase (se 4 (by rfl) ⟨277218, by rfl⟩ : syracuseStep 2956997 = 554437) (by norm_num)
theorem B1971331 : Blo 1969435 1971331 := bstep (se 1 (by rfl) ⟨1478498, by rfl⟩ : syracuseStep 1971331 = 2956997) B2956997
theorem B3326629 : Blo 1969435 3326629 := bbase (se 4 (by rfl) ⟨311871, by rfl⟩ : syracuseStep 3326629 = 623743) (by norm_num)
theorem B4435505 : Blo 1969435 4435505 := bstep (se 2 (by rfl) ⟨1663314, by rfl⟩ : syracuseStep 4435505 = 3326629) B3326629
theorem B2957003 : Blo 1969435 2957003 := bstep (se 1 (by rfl) ⟨2217752, by rfl⟩ : syracuseStep 2957003 = 4435505) B4435505
theorem B1971335 : Blo 1969435 1971335 := bstep (se 1 (by rfl) ⟨1478501, by rfl⟩ : syracuseStep 1971335 = 2957003) B2957003
theorem B2217757 : Blo 1969435 2217757 := bbase (se 3 (by rfl) ⟨415829, by rfl⟩ : syracuseStep 2217757 = 831659) (by norm_num)
theorem B2957009 : Blo 1969435 2957009 := bstep (se 2 (by rfl) ⟨1108878, by rfl⟩ : syracuseStep 2957009 = 2217757) B2217757
theorem B1971339 : Blo 1969435 1971339 := bstep (se 1 (by rfl) ⟨1478504, by rfl⟩ : syracuseStep 1971339 = 2957009) B2957009
theorem B6653285 : Blo 1969435 6653285 := bbase (se 4 (by rfl) ⟨623745, by rfl⟩ : syracuseStep 6653285 = 1247491) (by norm_num)
theorem B4435523 : Blo 1969435 4435523 := bstep (se 1 (by rfl) ⟨3326642, by rfl⟩ : syracuseStep 4435523 = 6653285) B6653285
theorem B2957015 : Blo 1969435 2957015 := bstep (se 1 (by rfl) ⟨2217761, by rfl⟩ : syracuseStep 2957015 = 4435523) B4435523
theorem B1971343 : Blo 1969435 1971343 := bstep (se 1 (by rfl) ⟨1478507, by rfl⟩ : syracuseStep 1971343 = 2957015) B2957015
theorem B2957021 : Blo 1969435 2957021 := bbase (se 3 (by rfl) ⟨554441, by rfl⟩ : syracuseStep 2957021 = 1108883) (by norm_num)
theorem B1971347 : Blo 1969435 1971347 := bstep (se 1 (by rfl) ⟨1478510, by rfl⟩ : syracuseStep 1971347 = 2957021) B2957021
theorem B4435541 : Blo 1969435 4435541 := bbase (se 8 (by rfl) ⟨25989, by rfl⟩ : syracuseStep 4435541 = 51979) (by norm_num)
theorem B2957027 : Blo 1969435 2957027 := bstep (se 1 (by rfl) ⟨2217770, by rfl⟩ : syracuseStep 2957027 = 4435541) B4435541
theorem B1971351 : Blo 1969435 1971351 := bstep (se 1 (by rfl) ⟨1478513, by rfl⟩ : syracuseStep 1971351 = 2957027) B2957027
theorem B4210309 : Blo 1969435 4210309 := bbase (se 4 (by rfl) ⟨394716, by rfl⟩ : syracuseStep 4210309 = 789433) (by norm_num)
theorem B5613745 : Blo 1969435 5613745 := bstep (se 2 (by rfl) ⟨2105154, by rfl⟩ : syracuseStep 5613745 = 4210309) B4210309
theorem B7484993 : Blo 1969435 7484993 := bstep (se 2 (by rfl) ⟨2806872, by rfl⟩ : syracuseStep 7484993 = 5613745) B5613745
theorem B4989995 : Blo 1969435 4989995 := bstep (se 1 (by rfl) ⟨3742496, by rfl⟩ : syracuseStep 4989995 = 7484993) B7484993
theorem B3326663 : Blo 1969435 3326663 := bstep (se 1 (by rfl) ⟨2494997, by rfl⟩ : syracuseStep 3326663 = 4989995) B4989995
theorem B2217775 : Blo 1969435 2217775 := bstep (se 1 (by rfl) ⟨1663331, by rfl⟩ : syracuseStep 2217775 = 3326663) B3326663
theorem B2957033 : Blo 1969435 2957033 := bstep (se 2 (by rfl) ⟨1108887, by rfl⟩ : syracuseStep 2957033 = 2217775) B2217775
theorem B1971355 : Blo 1969435 1971355 := bstep (se 1 (by rfl) ⟨1478516, by rfl⟩ : syracuseStep 1971355 = 2957033) B2957033
theorem B4496077 : Blo 1969435 4496077 := bbase (se 3 (by rfl) ⟨843014, by rfl⟩ : syracuseStep 4496077 = 1686029) (by norm_num)
theorem B5994769 : Blo 1969435 5994769 := bstep (se 2 (by rfl) ⟨2248038, by rfl⟩ : syracuseStep 5994769 = 4496077) B4496077
theorem B7993025 : Blo 1969435 7993025 := bstep (se 2 (by rfl) ⟨2997384, by rfl⟩ : syracuseStep 7993025 = 5994769) B5994769
theorem B5328683 : Blo 1969435 5328683 := bstep (se 1 (by rfl) ⟨3996512, by rfl⟩ : syracuseStep 5328683 = 7993025) B7993025
theorem B3552455 : Blo 1969435 3552455 := bstep (se 1 (by rfl) ⟨2664341, by rfl⟩ : syracuseStep 3552455 = 5328683) B5328683
theorem B9473213 : Blo 1969435 9473213 := bstep (se 3 (by rfl) ⟨1776227, by rfl⟩ : syracuseStep 9473213 = 3552455) B3552455
theorem B25261901 : Blo 1969435 25261901 := bstep (se 3 (by rfl) ⟨4736606, by rfl⟩ : syracuseStep 25261901 = 9473213) B9473213
theorem B16841267 : Blo 1969435 16841267 := bstep (se 1 (by rfl) ⟨12630950, by rfl⟩ : syracuseStep 16841267 = 25261901) B25261901
theorem B11227511 : Blo 1969435 11227511 := bstep (se 1 (by rfl) ⟨8420633, by rfl⟩ : syracuseStep 11227511 = 16841267) B16841267
theorem B7485007 : Blo 1969435 7485007 := bstep (se 1 (by rfl) ⟨5613755, by rfl⟩ : syracuseStep 7485007 = 11227511) B11227511
theorem B9980009 : Blo 1969435 9980009 := bstep (se 2 (by rfl) ⟨3742503, by rfl⟩ : syracuseStep 9980009 = 7485007) B7485007
theorem B6653339 : Blo 1969435 6653339 := bstep (se 1 (by rfl) ⟨4990004, by rfl⟩ : syracuseStep 6653339 = 9980009) B9980009
theorem B4435559 : Blo 1969435 4435559 := bstep (se 1 (by rfl) ⟨3326669, by rfl⟩ : syracuseStep 4435559 = 6653339) B6653339
theorem B2957039 : Blo 1969435 2957039 := bstep (se 1 (by rfl) ⟨2217779, by rfl⟩ : syracuseStep 2957039 = 4435559) B4435559
theorem B1971359 : Blo 1969435 1971359 := bstep (se 1 (by rfl) ⟨1478519, by rfl⟩ : syracuseStep 1971359 = 2957039) B2957039
theorem B2957045 : Blo 1969435 2957045 := bbase (se 5 (by rfl) ⟨138611, by rfl⟩ : syracuseStep 2957045 = 277223) (by norm_num)
theorem B1971363 : Blo 1969435 1971363 := bstep (se 1 (by rfl) ⟨1478522, by rfl⟩ : syracuseStep 1971363 = 2957045) B2957045
theorem B1998265 : Blo 1969435 1998265 := bbase (se 2 (by rfl) ⟨749349, by rfl⟩ : syracuseStep 1998265 = 1498699) (by norm_num)
theorem B2664353 : Blo 1969435 2664353 := bstep (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) B1998265
theorem B7104941 : Blo 1969435 7104941 := bstep (se 3 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 7104941 = 2664353) B2664353
theorem B4736627 : Blo 1969435 4736627 := bstep (se 1 (by rfl) ⟨3552470, by rfl⟩ : syracuseStep 4736627 = 7104941) B7104941
theorem B3157751 : Blo 1969435 3157751 := bstep (se 1 (by rfl) ⟨2368313, by rfl⟩ : syracuseStep 3157751 = 4736627) B4736627
theorem B8420669 : Blo 1969435 8420669 := bstep (se 3 (by rfl) ⟨1578875, by rfl⟩ : syracuseStep 8420669 = 3157751) B3157751
theorem B5613779 : Blo 1969435 5613779 := bstep (se 1 (by rfl) ⟨4210334, by rfl⟩ : syracuseStep 5613779 = 8420669) B8420669
theorem B3742519 : Blo 1969435 3742519 := bstep (se 1 (by rfl) ⟨2806889, by rfl⟩ : syracuseStep 3742519 = 5613779) B5613779
theorem B4990025 : Blo 1969435 4990025 := bstep (se 2 (by rfl) ⟨1871259, by rfl⟩ : syracuseStep 4990025 = 3742519) B3742519
theorem B3326683 : Blo 1969435 3326683 := bstep (se 1 (by rfl) ⟨2495012, by rfl⟩ : syracuseStep 3326683 = 4990025) B4990025
theorem B4435577 : Blo 1969435 4435577 := bstep (se 2 (by rfl) ⟨1663341, by rfl⟩ : syracuseStep 4435577 = 3326683) B3326683
theorem B2957051 : Blo 1969435 2957051 := bstep (se 1 (by rfl) ⟨2217788, by rfl⟩ : syracuseStep 2957051 = 4435577) B4435577
theorem B1971367 : Blo 1969435 1971367 := bstep (se 1 (by rfl) ⟨1478525, by rfl⟩ : syracuseStep 1971367 = 2957051) B2957051
theorem B2217793 : Blo 1969435 2217793 := bbase (se 2 (by rfl) ⟨831672, by rfl⟩ : syracuseStep 2217793 = 1663345) (by norm_num)
theorem B2957057 : Blo 1969435 2957057 := bstep (se 2 (by rfl) ⟨1108896, by rfl⟩ : syracuseStep 2957057 = 2217793) B2217793
theorem B1971371 : Blo 1969435 1971371 := bstep (se 1 (by rfl) ⟨1478528, by rfl⟩ : syracuseStep 1971371 = 2957057) B2957057
theorem B4990045 : Blo 1969435 4990045 := bbase (se 3 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 4990045 = 1871267) (by norm_num)
theorem B6653393 : Blo 1969435 6653393 := bstep (se 2 (by rfl) ⟨2495022, by rfl⟩ : syracuseStep 6653393 = 4990045) B4990045
theorem B4435595 : Blo 1969435 4435595 := bstep (se 1 (by rfl) ⟨3326696, by rfl⟩ : syracuseStep 4435595 = 6653393) B6653393
theorem B2957063 : Blo 1969435 2957063 := bstep (se 1 (by rfl) ⟨2217797, by rfl⟩ : syracuseStep 2957063 = 4435595) B4435595
theorem B1971375 : Blo 1969435 1971375 := bstep (se 1 (by rfl) ⟨1478531, by rfl⟩ : syracuseStep 1971375 = 2957063) B2957063
theorem B2957069 : Blo 1969435 2957069 := bbase (se 3 (by rfl) ⟨554450, by rfl⟩ : syracuseStep 2957069 = 1108901) (by norm_num)
theorem B1971379 : Blo 1969435 1971379 := bstep (se 1 (by rfl) ⟨1478534, by rfl⟩ : syracuseStep 1971379 = 2957069) B2957069
theorem B4435613 : Blo 1969435 4435613 := bbase (se 3 (by rfl) ⟨831677, by rfl⟩ : syracuseStep 4435613 = 1663355) (by norm_num)
theorem B2957075 : Blo 1969435 2957075 := bstep (se 1 (by rfl) ⟨2217806, by rfl⟩ : syracuseStep 2957075 = 4435613) B4435613
theorem B1971383 : Blo 1969435 1971383 := bstep (se 1 (by rfl) ⟨1478537, by rfl⟩ : syracuseStep 1971383 = 2957075) B2957075
theorem B3326717 : Blo 1969435 3326717 := bbase (se 3 (by rfl) ⟨623759, by rfl⟩ : syracuseStep 3326717 = 1247519) (by norm_num)
theorem B2217811 : Blo 1969435 2217811 := bstep (se 1 (by rfl) ⟨1663358, by rfl⟩ : syracuseStep 2217811 = 3326717) B3326717
theorem B2957081 : Blo 1969435 2957081 := bstep (se 2 (by rfl) ⟨1108905, by rfl⟩ : syracuseStep 2957081 = 2217811) B2217811
theorem B1971387 : Blo 1969435 1971387 := bstep (se 1 (by rfl) ⟨1478540, by rfl⟩ : syracuseStep 1971387 = 2957081) B2957081
theorem B3157789 : Blo 1969435 3157789 := bbase (se 3 (by rfl) ⟨592085, by rfl⟩ : syracuseStep 3157789 = 1184171) (by norm_num)
theorem B4210385 : Blo 1969435 4210385 := bstep (se 2 (by rfl) ⟨1578894, by rfl⟩ : syracuseStep 4210385 = 3157789) B3157789
theorem B11227693 : Blo 1969435 11227693 := bstep (se 3 (by rfl) ⟨2105192, by rfl⟩ : syracuseStep 11227693 = 4210385) B4210385
theorem B14970257 : Blo 1969435 14970257 := bstep (se 2 (by rfl) ⟨5613846, by rfl⟩ : syracuseStep 14970257 = 11227693) B11227693
theorem B9980171 : Blo 1969435 9980171 := bstep (se 1 (by rfl) ⟨7485128, by rfl⟩ : syracuseStep 9980171 = 14970257) B14970257
theorem B6653447 : Blo 1969435 6653447 := bstep (se 1 (by rfl) ⟨4990085, by rfl⟩ : syracuseStep 6653447 = 9980171) B9980171
theorem B4435631 : Blo 1969435 4435631 := bstep (se 1 (by rfl) ⟨3326723, by rfl⟩ : syracuseStep 4435631 = 6653447) B6653447
theorem B2957087 : Blo 1969435 2957087 := bstep (se 1 (by rfl) ⟨2217815, by rfl⟩ : syracuseStep 2957087 = 4435631) B4435631
theorem B1971391 : Blo 1969435 1971391 := bstep (se 1 (by rfl) ⟨1478543, by rfl⟩ : syracuseStep 1971391 = 2957087) B2957087
theorem B2957093 : Blo 1969435 2957093 := bbase (se 4 (by rfl) ⟨277227, by rfl⟩ : syracuseStep 2957093 = 554455) (by norm_num)
theorem B1971395 : Blo 1969435 1971395 := bstep (se 1 (by rfl) ⟨1478546, by rfl⟩ : syracuseStep 1971395 = 2957093) B2957093
theorem B2495053 : Blo 1969435 2495053 := bbase (se 3 (by rfl) ⟨467822, by rfl⟩ : syracuseStep 2495053 = 935645) (by norm_num)
theorem B3326737 : Blo 1969435 3326737 := bstep (se 2 (by rfl) ⟨1247526, by rfl⟩ : syracuseStep 3326737 = 2495053) B2495053
theorem B4435649 : Blo 1969435 4435649 := bstep (se 2 (by rfl) ⟨1663368, by rfl⟩ : syracuseStep 4435649 = 3326737) B3326737
theorem B2957099 : Blo 1969435 2957099 := bstep (se 1 (by rfl) ⟨2217824, by rfl⟩ : syracuseStep 2957099 = 4435649) B4435649
theorem B1971399 : Blo 1969435 1971399 := bstep (se 1 (by rfl) ⟨1478549, by rfl⟩ : syracuseStep 1971399 = 2957099) B2957099
theorem B2217829 : Blo 1969435 2217829 := bbase (se 4 (by rfl) ⟨207921, by rfl⟩ : syracuseStep 2217829 = 415843) (by norm_num)
theorem B2957105 : Blo 1969435 2957105 := bstep (se 2 (by rfl) ⟨1108914, by rfl⟩ : syracuseStep 2957105 = 2217829) B2217829
theorem B1971403 : Blo 1969435 1971403 := bstep (se 1 (by rfl) ⟨1478552, by rfl⟩ : syracuseStep 1971403 = 2957105) B2957105
theorem B5613893 : Blo 1969435 5613893 := bbase (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) (by norm_num)
theorem B3742595 : Blo 1969435 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B2495063 : Blo 1969435 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B6653501 : Blo 1969435 6653501 := bstep (se 3 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 6653501 = 2495063) B2495063
theorem B4435667 : Blo 1969435 4435667 := bstep (se 1 (by rfl) ⟨3326750, by rfl⟩ : syracuseStep 4435667 = 6653501) B6653501
theorem B2957111 : Blo 1969435 2957111 := bstep (se 1 (by rfl) ⟨2217833, by rfl⟩ : syracuseStep 2957111 = 4435667) B4435667
theorem B1971407 : Blo 1969435 1971407 := bstep (se 1 (by rfl) ⟨1478555, by rfl⟩ : syracuseStep 1971407 = 2957111) B2957111
theorem B2957117 : Blo 1969435 2957117 := bbase (se 3 (by rfl) ⟨554459, by rfl⟩ : syracuseStep 2957117 = 1108919) (by norm_num)
theorem B1971411 : Blo 1969435 1971411 := bstep (se 1 (by rfl) ⟨1478558, by rfl⟩ : syracuseStep 1971411 = 2957117) B2957117
theorem B4435685 : Blo 1969435 4435685 := bbase (se 4 (by rfl) ⟨415845, by rfl⟩ : syracuseStep 4435685 = 831691) (by norm_num)
theorem B2957123 : Blo 1969435 2957123 := bstep (se 1 (by rfl) ⟨2217842, by rfl⟩ : syracuseStep 2957123 = 4435685) B4435685
theorem B1971415 : Blo 1969435 1971415 := bstep (se 1 (by rfl) ⟨1478561, by rfl⟩ : syracuseStep 1971415 = 2957123) B2957123
theorem B4990157 : Blo 1969435 4990157 := bbase (se 3 (by rfl) ⟨935654, by rfl⟩ : syracuseStep 4990157 = 1871309) (by norm_num)
theorem B3326771 : Blo 1969435 3326771 := bstep (se 1 (by rfl) ⟨2495078, by rfl⟩ : syracuseStep 3326771 = 4990157) B4990157
theorem B2217847 : Blo 1969435 2217847 := bstep (se 1 (by rfl) ⟨1663385, by rfl⟩ : syracuseStep 2217847 = 3326771) B3326771
theorem B2957129 : Blo 1969435 2957129 := bstep (se 2 (by rfl) ⟨1108923, by rfl⟩ : syracuseStep 2957129 = 2217847) B2217847
theorem B1971419 : Blo 1969435 1971419 := bstep (se 1 (by rfl) ⟨1478564, by rfl⟩ : syracuseStep 1971419 = 2957129) B2957129
theorem B2368381 : Blo 1969435 2368381 := bbase (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) (by norm_num)
theorem B3157841 : Blo 1969435 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B2105227 : Blo 1969435 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B2806969 : Blo 1969435 2806969 := bstep (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) B2105227
theorem B3742625 : Blo 1969435 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B9980333 : Blo 1969435 9980333 := bstep (se 3 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 9980333 = 3742625) B3742625
theorem B6653555 : Blo 1969435 6653555 := bstep (se 1 (by rfl) ⟨4990166, by rfl⟩ : syracuseStep 6653555 = 9980333) B9980333
theorem B4435703 : Blo 1969435 4435703 := bstep (se 1 (by rfl) ⟨3326777, by rfl⟩ : syracuseStep 4435703 = 6653555) B6653555
theorem B2957135 : Blo 1969435 2957135 := bstep (se 1 (by rfl) ⟨2217851, by rfl⟩ : syracuseStep 2957135 = 4435703) B4435703
theorem B1971423 : Blo 1969435 1971423 := bstep (se 1 (by rfl) ⟨1478567, by rfl⟩ : syracuseStep 1971423 = 2957135) B2957135
theorem B2957141 : Blo 1969435 2957141 := bbase (se 9 (by rfl) ⟨8663, by rfl⟩ : syracuseStep 2957141 = 17327) (by norm_num)
theorem B1971427 : Blo 1969435 1971427 := bstep (se 1 (by rfl) ⟨1478570, by rfl⟩ : syracuseStep 1971427 = 2957141) B2957141
theorem B2248121 : Blo 1969435 2248121 := bbase (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) (by norm_num)
theorem B5994989 : Blo 1969435 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B3996659 : Blo 1969435 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B10657757 : Blo 1969435 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B7105171 : Blo 1969435 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B9473561 : Blo 1969435 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B6315707 : Blo 1969435 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B4210471 : Blo 1969435 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B5613961 : Blo 1969435 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B7485281 : Blo 1969435 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B4990187 : Blo 1969435 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B3326791 : Blo 1969435 3326791 := bstep (se 1 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 3326791 = 4990187) B4990187
theorem B4435721 : Blo 1969435 4435721 := bstep (se 2 (by rfl) ⟨1663395, by rfl⟩ : syracuseStep 4435721 = 3326791) B3326791
theorem B2957147 : Blo 1969435 2957147 := bstep (se 1 (by rfl) ⟨2217860, by rfl⟩ : syracuseStep 2957147 = 4435721) B4435721
theorem B1971431 : Blo 1969435 1971431 := bstep (se 1 (by rfl) ⟨1478573, by rfl⟩ : syracuseStep 1971431 = 2957147) B2957147
theorem B2217865 : Blo 1969435 2217865 := bbase (se 2 (by rfl) ⟨831699, by rfl⟩ : syracuseStep 2217865 = 1663399) (by norm_num)
theorem B2957153 : Blo 1969435 2957153 := bstep (se 2 (by rfl) ⟨1108932, by rfl⟩ : syracuseStep 2957153 = 2217865) B2217865
theorem B1971435 : Blo 1969435 1971435 := bstep (se 1 (by rfl) ⟨1478576, by rfl⟩ : syracuseStep 1971435 = 2957153) B2957153
theorem C0 (j : ℕ) (h1 : 492358 ≤ j) (h2 : j ≤ 492858) : Blo 1969435 (4 * j + 3) := by
  interval_cases j
  · exact B1969435
  · exact B1969439
  · exact B1969443
  · exact B1969447
  · exact B1969451
  · exact B1969455
  · exact B1969459
  · exact B1969463
  · exact B1969467
  · exact B1969471
  · exact B1969475
  · exact B1969479
  · exact B1969483
  · exact B1969487
  · exact B1969491
  · exact B1969495
  · exact B1969499
  · exact B1969503
  · exact B1969507
  · exact B1969511
  · exact B1969515
  · exact B1969519
  · exact B1969523
  · exact B1969527
  · exact B1969531
  · exact B1969535
  · exact B1969539
  · exact B1969543
  · exact B1969547
  · exact B1969551
  · exact B1969555
  · exact B1969559
  · exact B1969563
  · exact B1969567
  · exact B1969571
  · exact B1969575
  · exact B1969579
  · exact B1969583
  · exact B1969587
  · exact B1969591
  · exact B1969595
  · exact B1969599
  · exact B1969603
  · exact B1969607
  · exact B1969611
  · exact B1969615
  · exact B1969619
  · exact B1969623
  · exact B1969627
  · exact B1969631
  · exact B1969635
  · exact B1969639
  · exact B1969643
  · exact B1969647
  · exact B1969651
  · exact B1969655
  · exact B1969659
  · exact B1969663
  · exact B1969667
  · exact B1969671
  · exact B1969675
  · exact B1969679
  · exact B1969683
  · exact B1969687
  · exact B1969691
  · exact B1969695
  · exact B1969699
  · exact B1969703
  · exact B1969707
  · exact B1969711
  · exact B1969715
  · exact B1969719
  · exact B1969723
  · exact B1969727
  · exact B1969731
  · exact B1969735
  · exact B1969739
  · exact B1969743
  · exact B1969747
  · exact B1969751
  · exact B1969755
  · exact B1969759
  · exact B1969763
  · exact B1969767
  · exact B1969771
  · exact B1969775
  · exact B1969779
  · exact B1969783
  · exact B1969787
  · exact B1969791
  · exact B1969795
  · exact B1969799
  · exact B1969803
  · exact B1969807
  · exact B1969811
  · exact B1969815
  · exact B1969819
  · exact B1969823
  · exact B1969827
  · exact B1969831
  · exact B1969835
  · exact B1969839
  · exact B1969843
  · exact B1969847
  · exact B1969851
  · exact B1969855
  · exact B1969859
  · exact B1969863
  · exact B1969867
  · exact B1969871
  · exact B1969875
  · exact B1969879
  · exact B1969883
  · exact B1969887
  · exact B1969891
  · exact B1969895
  · exact B1969899
  · exact B1969903
  · exact B1969907
  · exact B1969911
  · exact B1969915
  · exact B1969919
  · exact B1969923
  · exact B1969927
  · exact B1969931
  · exact B1969935
  · exact B1969939
  · exact B1969943
  · exact B1969947
  · exact B1969951
  · exact B1969955
  · exact B1969959
  · exact B1969963
  · exact B1969967
  · exact B1969971
  · exact B1969975
  · exact B1969979
  · exact B1969983
  · exact B1969987
  · exact B1969991
  · exact B1969995
  · exact B1969999
  · exact B1970003
  · exact B1970007
  · exact B1970011
  · exact B1970015
  · exact B1970019
  · exact B1970023
  · exact B1970027
  · exact B1970031
  · exact B1970035
  · exact B1970039
  · exact B1970043
  · exact B1970047
  · exact B1970051
  · exact B1970055
  · exact B1970059
  · exact B1970063
  · exact B1970067
  · exact B1970071
  · exact B1970075
  · exact B1970079
  · exact B1970083
  · exact B1970087
  · exact B1970091
  · exact B1970095
  · exact B1970099
  · exact B1970103
  · exact B1970107
  · exact B1970111
  · exact B1970115
  · exact B1970119
  · exact B1970123
  · exact B1970127
  · exact B1970131
  · exact B1970135
  · exact B1970139
  · exact B1970143
  · exact B1970147
  · exact B1970151
  · exact B1970155
  · exact B1970159
  · exact B1970163
  · exact B1970167
  · exact B1970171
  · exact B1970175
  · exact B1970179
  · exact B1970183
  · exact B1970187
  · exact B1970191
  · exact B1970195
  · exact B1970199
  · exact B1970203
  · exact B1970207
  · exact B1970211
  · exact B1970215
  · exact B1970219
  · exact B1970223
  · exact B1970227
  · exact B1970231
  · exact B1970235
  · exact B1970239
  · exact B1970243
  · exact B1970247
  · exact B1970251
  · exact B1970255
  · exact B1970259
  · exact B1970263
  · exact B1970267
  · exact B1970271
  · exact B1970275
  · exact B1970279
  · exact B1970283
  · exact B1970287
  · exact B1970291
  · exact B1970295
  · exact B1970299
  · exact B1970303
  · exact B1970307
  · exact B1970311
  · exact B1970315
  · exact B1970319
  · exact B1970323
  · exact B1970327
  · exact B1970331
  · exact B1970335
  · exact B1970339
  · exact B1970343
  · exact B1970347
  · exact B1970351
  · exact B1970355
  · exact B1970359
  · exact B1970363
  · exact B1970367
  · exact B1970371
  · exact B1970375
  · exact B1970379
  · exact B1970383
  · exact B1970387
  · exact B1970391
  · exact B1970395
  · exact B1970399
  · exact B1970403
  · exact B1970407
  · exact B1970411
  · exact B1970415
  · exact B1970419
  · exact B1970423
  · exact B1970427
  · exact B1970431
  · exact B1970435
  · exact B1970439
  · exact B1970443
  · exact B1970447
  · exact B1970451
  · exact B1970455
  · exact B1970459
  · exact B1970463
  · exact B1970467
  · exact B1970471
  · exact B1970475
  · exact B1970479
  · exact B1970483
  · exact B1970487
  · exact B1970491
  · exact B1970495
  · exact B1970499
  · exact B1970503
  · exact B1970507
  · exact B1970511
  · exact B1970515
  · exact B1970519
  · exact B1970523
  · exact B1970527
  · exact B1970531
  · exact B1970535
  · exact B1970539
  · exact B1970543
  · exact B1970547
  · exact B1970551
  · exact B1970555
  · exact B1970559
  · exact B1970563
  · exact B1970567
  · exact B1970571
  · exact B1970575
  · exact B1970579
  · exact B1970583
  · exact B1970587
  · exact B1970591
  · exact B1970595
  · exact B1970599
  · exact B1970603
  · exact B1970607
  · exact B1970611
  · exact B1970615
  · exact B1970619
  · exact B1970623
  · exact B1970627
  · exact B1970631
  · exact B1970635
  · exact B1970639
  · exact B1970643
  · exact B1970647
  · exact B1970651
  · exact B1970655
  · exact B1970659
  · exact B1970663
  · exact B1970667
  · exact B1970671
  · exact B1970675
  · exact B1970679
  · exact B1970683
  · exact B1970687
  · exact B1970691
  · exact B1970695
  · exact B1970699
  · exact B1970703
  · exact B1970707
  · exact B1970711
  · exact B1970715
  · exact B1970719
  · exact B1970723
  · exact B1970727
  · exact B1970731
  · exact B1970735
  · exact B1970739
  · exact B1970743
  · exact B1970747
  · exact B1970751
  · exact B1970755
  · exact B1970759
  · exact B1970763
  · exact B1970767
  · exact B1970771
  · exact B1970775
  · exact B1970779
  · exact B1970783
  · exact B1970787
  · exact B1970791
  · exact B1970795
  · exact B1970799
  · exact B1970803
  · exact B1970807
  · exact B1970811
  · exact B1970815
  · exact B1970819
  · exact B1970823
  · exact B1970827
  · exact B1970831
  · exact B1970835
  · exact B1970839
  · exact B1970843
  · exact B1970847
  · exact B1970851
  · exact B1970855
  · exact B1970859
  · exact B1970863
  · exact B1970867
  · exact B1970871
  · exact B1970875
  · exact B1970879
  · exact B1970883
  · exact B1970887
  · exact B1970891
  · exact B1970895
  · exact B1970899
  · exact B1970903
  · exact B1970907
  · exact B1970911
  · exact B1970915
  · exact B1970919
  · exact B1970923
  · exact B1970927
  · exact B1970931
  · exact B1970935
  · exact B1970939
  · exact B1970943
  · exact B1970947
  · exact B1970951
  · exact B1970955
  · exact B1970959
  · exact B1970963
  · exact B1970967
  · exact B1970971
  · exact B1970975
  · exact B1970979
  · exact B1970983
  · exact B1970987
  · exact B1970991
  · exact B1970995
  · exact B1970999
  · exact B1971003
  · exact B1971007
  · exact B1971011
  · exact B1971015
  · exact B1971019
  · exact B1971023
  · exact B1971027
  · exact B1971031
  · exact B1971035
  · exact B1971039
  · exact B1971043
  · exact B1971047
  · exact B1971051
  · exact B1971055
  · exact B1971059
  · exact B1971063
  · exact B1971067
  · exact B1971071
  · exact B1971075
  · exact B1971079
  · exact B1971083
  · exact B1971087
  · exact B1971091
  · exact B1971095
  · exact B1971099
  · exact B1971103
  · exact B1971107
  · exact B1971111
  · exact B1971115
  · exact B1971119
  · exact B1971123
  · exact B1971127
  · exact B1971131
  · exact B1971135
  · exact B1971139
  · exact B1971143
  · exact B1971147
  · exact B1971151
  · exact B1971155
  · exact B1971159
  · exact B1971163
  · exact B1971167
  · exact B1971171
  · exact B1971175
  · exact B1971179
  · exact B1971183
  · exact B1971187
  · exact B1971191
  · exact B1971195
  · exact B1971199
  · exact B1971203
  · exact B1971207
  · exact B1971211
  · exact B1971215
  · exact B1971219
  · exact B1971223
  · exact B1971227
  · exact B1971231
  · exact B1971235
  · exact B1971239
  · exact B1971243
  · exact B1971247
  · exact B1971251
  · exact B1971255
  · exact B1971259
  · exact B1971263
  · exact B1971267
  · exact B1971271
  · exact B1971275
  · exact B1971279
  · exact B1971283
  · exact B1971287
  · exact B1971291
  · exact B1971295
  · exact B1971299
  · exact B1971303
  · exact B1971307
  · exact B1971311
  · exact B1971315
  · exact B1971319
  · exact B1971323
  · exact B1971327
  · exact B1971331
  · exact B1971335
  · exact B1971339
  · exact B1971343
  · exact B1971347
  · exact B1971351
  · exact B1971355
  · exact B1971359
  · exact B1971363
  · exact B1971367
  · exact B1971371
  · exact B1971375
  · exact B1971379
  · exact B1971383
  · exact B1971387
  · exact B1971391
  · exact B1971395
  · exact B1971399
  · exact B1971403
  · exact B1971407
  · exact B1971411
  · exact B1971415
  · exact B1971419
  · exact B1971423
  · exact B1971427
  · exact B1971431
  · exact B1971435
theorem solution (m : ℕ) (hlo : 1969435 ≤ m) (hhi : m ≤ 1971435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 492358 ≤ j := by omega
    have hj2 : j ≤ 492858 := by omega
    have hb : Blo 1969435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
