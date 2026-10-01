-- Prove2me | solution 1 for syracuse_descends_range_1993435_1995435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:26.526858+00:00
-- url     : https://prove2.me/submissions/de06a9bb-de87-44be-8154-d714074909bb

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

theorem B5045885 : Blo 1993435 5045885 := bbase (se 3 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 5045885 = 1892207) (by norm_num)
theorem B3363923 : Blo 1993435 3363923 := bstep (se 1 (by rfl) ⟨2522942, by rfl⟩ : syracuseStep 3363923 = 5045885) B5045885
theorem B2242615 : Blo 1993435 2242615 := bstep (se 1 (by rfl) ⟨1681961, by rfl⟩ : syracuseStep 2242615 = 3363923) B3363923
theorem B2990153 : Blo 1993435 2990153 := bstep (se 2 (by rfl) ⟨1121307, by rfl⟩ : syracuseStep 2990153 = 2242615) B2242615
theorem B1993435 : Blo 1993435 1993435 := bstep (se 1 (by rfl) ⟨1495076, by rfl⟩ : syracuseStep 1993435 = 2990153) B2990153
theorem B3784421 : Blo 1993435 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B10091789 : Blo 1993435 10091789 := bstep (se 3 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 10091789 = 3784421) B3784421
theorem B6727859 : Blo 1993435 6727859 := bstep (se 1 (by rfl) ⟨5045894, by rfl⟩ : syracuseStep 6727859 = 10091789) B10091789
theorem B4485239 : Blo 1993435 4485239 := bstep (se 1 (by rfl) ⟨3363929, by rfl⟩ : syracuseStep 4485239 = 6727859) B6727859
theorem B2990159 : Blo 1993435 2990159 := bstep (se 1 (by rfl) ⟨2242619, by rfl⟩ : syracuseStep 2990159 = 4485239) B4485239
theorem B1993439 : Blo 1993435 1993439 := bstep (se 1 (by rfl) ⟨1495079, by rfl⟩ : syracuseStep 1993439 = 2990159) B2990159
theorem B2990165 : Blo 1993435 2990165 := bbase (se 8 (by rfl) ⟨17520, by rfl⟩ : syracuseStep 2990165 = 35041) (by norm_num)
theorem B1993443 : Blo 1993435 1993443 := bstep (se 1 (by rfl) ⟨1495082, by rfl⟩ : syracuseStep 1993443 = 2990165) B2990165
theorem B4546453 : Blo 1993435 4546453 := bbase (se 6 (by rfl) ⟨106557, by rfl⟩ : syracuseStep 4546453 = 213115) (by norm_num)
theorem B6061937 : Blo 1993435 6061937 := bstep (se 2 (by rfl) ⟨2273226, by rfl⟩ : syracuseStep 6061937 = 4546453) B4546453
theorem B16165165 : Blo 1993435 16165165 := bstep (se 3 (by rfl) ⟨3030968, by rfl⟩ : syracuseStep 16165165 = 6061937) B6061937
theorem B21553553 : Blo 1993435 21553553 := bstep (se 2 (by rfl) ⟨8082582, by rfl⟩ : syracuseStep 21553553 = 16165165) B16165165
theorem B14369035 : Blo 1993435 14369035 := bstep (se 1 (by rfl) ⟨10776776, by rfl⟩ : syracuseStep 14369035 = 21553553) B21553553
theorem B19158713 : Blo 1993435 19158713 := bstep (se 2 (by rfl) ⟨7184517, by rfl⟩ : syracuseStep 19158713 = 14369035) B14369035
theorem B12772475 : Blo 1993435 12772475 := bstep (se 1 (by rfl) ⟨9579356, by rfl⟩ : syracuseStep 12772475 = 19158713) B19158713
theorem B8514983 : Blo 1993435 8514983 := bstep (se 1 (by rfl) ⟨6386237, by rfl⟩ : syracuseStep 8514983 = 12772475) B12772475
theorem B5676655 : Blo 1993435 5676655 := bstep (se 1 (by rfl) ⟨4257491, by rfl⟩ : syracuseStep 5676655 = 8514983) B8514983
theorem B7568873 : Blo 1993435 7568873 := bstep (se 2 (by rfl) ⟨2838327, by rfl⟩ : syracuseStep 7568873 = 5676655) B5676655
theorem B5045915 : Blo 1993435 5045915 := bstep (se 1 (by rfl) ⟨3784436, by rfl⟩ : syracuseStep 5045915 = 7568873) B7568873
theorem B3363943 : Blo 1993435 3363943 := bstep (se 1 (by rfl) ⟨2522957, by rfl⟩ : syracuseStep 3363943 = 5045915) B5045915
theorem B4485257 : Blo 1993435 4485257 := bstep (se 2 (by rfl) ⟨1681971, by rfl⟩ : syracuseStep 4485257 = 3363943) B3363943
theorem B2990171 : Blo 1993435 2990171 := bstep (se 1 (by rfl) ⟨2242628, by rfl⟩ : syracuseStep 2990171 = 4485257) B4485257
theorem B1993447 : Blo 1993435 1993447 := bstep (se 1 (by rfl) ⟨1495085, by rfl⟩ : syracuseStep 1993447 = 2990171) B2990171
theorem B2242633 : Blo 1993435 2242633 := bbase (se 2 (by rfl) ⟨840987, by rfl⟩ : syracuseStep 2242633 = 1681975) (by norm_num)
theorem B2990177 : Blo 1993435 2990177 := bstep (se 2 (by rfl) ⟨1121316, by rfl⟩ : syracuseStep 2990177 = 2242633) B2242633
theorem B1993451 : Blo 1993435 1993451 := bstep (se 1 (by rfl) ⟨1495088, by rfl⟩ : syracuseStep 1993451 = 2990177) B2990177
theorem B2694205 : Blo 1993435 2694205 := bbase (se 3 (by rfl) ⟨505163, by rfl⟩ : syracuseStep 2694205 = 1010327) (by norm_num)
theorem B3592273 : Blo 1993435 3592273 := bstep (se 2 (by rfl) ⟨1347102, by rfl⟩ : syracuseStep 3592273 = 2694205) B2694205
theorem B4789697 : Blo 1993435 4789697 := bstep (se 2 (by rfl) ⟨1796136, by rfl⟩ : syracuseStep 4789697 = 3592273) B3592273
theorem B12772525 : Blo 1993435 12772525 := bstep (se 3 (by rfl) ⟨2394848, by rfl⟩ : syracuseStep 12772525 = 4789697) B4789697
theorem B17030033 : Blo 1993435 17030033 := bstep (se 2 (by rfl) ⟨6386262, by rfl⟩ : syracuseStep 17030033 = 12772525) B12772525
theorem B11353355 : Blo 1993435 11353355 := bstep (se 1 (by rfl) ⟨8515016, by rfl⟩ : syracuseStep 11353355 = 17030033) B17030033
theorem B7568903 : Blo 1993435 7568903 := bstep (se 1 (by rfl) ⟨5676677, by rfl⟩ : syracuseStep 7568903 = 11353355) B11353355
theorem B5045935 : Blo 1993435 5045935 := bstep (se 1 (by rfl) ⟨3784451, by rfl⟩ : syracuseStep 5045935 = 7568903) B7568903
theorem B6727913 : Blo 1993435 6727913 := bstep (se 2 (by rfl) ⟨2522967, by rfl⟩ : syracuseStep 6727913 = 5045935) B5045935
theorem B4485275 : Blo 1993435 4485275 := bstep (se 1 (by rfl) ⟨3363956, by rfl⟩ : syracuseStep 4485275 = 6727913) B6727913
theorem B2990183 : Blo 1993435 2990183 := bstep (se 1 (by rfl) ⟨2242637, by rfl⟩ : syracuseStep 2990183 = 4485275) B4485275
theorem B1993455 : Blo 1993435 1993455 := bstep (se 1 (by rfl) ⟨1495091, by rfl⟩ : syracuseStep 1993455 = 2990183) B2990183
theorem B2990189 : Blo 1993435 2990189 := bbase (se 3 (by rfl) ⟨560660, by rfl⟩ : syracuseStep 2990189 = 1121321) (by norm_num)
theorem B1993459 : Blo 1993435 1993459 := bstep (se 1 (by rfl) ⟨1495094, by rfl⟩ : syracuseStep 1993459 = 2990189) B2990189
theorem B4485293 : Blo 1993435 4485293 := bbase (se 3 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 4485293 = 1681985) (by norm_num)
theorem B2990195 : Blo 1993435 2990195 := bstep (se 1 (by rfl) ⟨2242646, by rfl⟩ : syracuseStep 2990195 = 4485293) B4485293
theorem B1993463 : Blo 1993435 1993463 := bstep (se 1 (by rfl) ⟨1495097, by rfl⟩ : syracuseStep 1993463 = 2990195) B2990195
theorem B3456397 : Blo 1993435 3456397 := bbase (se 3 (by rfl) ⟨648074, by rfl⟩ : syracuseStep 3456397 = 1296149) (by norm_num)
theorem B18434117 : Blo 1993435 18434117 := bstep (se 4 (by rfl) ⟨1728198, by rfl⟩ : syracuseStep 18434117 = 3456397) B3456397
theorem B12289411 : Blo 1993435 12289411 := bstep (se 1 (by rfl) ⟨9217058, by rfl⟩ : syracuseStep 12289411 = 18434117) B18434117
theorem B65543525 : Blo 1993435 65543525 := bstep (se 4 (by rfl) ⟨6144705, by rfl⟩ : syracuseStep 65543525 = 12289411) B12289411
theorem B43695683 : Blo 1993435 43695683 := bstep (se 1 (by rfl) ⟨32771762, by rfl⟩ : syracuseStep 43695683 = 65543525) B65543525
theorem B29130455 : Blo 1993435 29130455 := bstep (se 1 (by rfl) ⟨21847841, by rfl⟩ : syracuseStep 29130455 = 43695683) B43695683
theorem B19420303 : Blo 1993435 19420303 := bstep (se 1 (by rfl) ⟨14565227, by rfl⟩ : syracuseStep 19420303 = 29130455) B29130455
theorem B25893737 : Blo 1993435 25893737 := bstep (se 2 (by rfl) ⟨9710151, by rfl⟩ : syracuseStep 25893737 = 19420303) B19420303
theorem B17262491 : Blo 1993435 17262491 := bstep (se 1 (by rfl) ⟨12946868, by rfl⟩ : syracuseStep 17262491 = 25893737) B25893737
theorem B46033309 : Blo 1993435 46033309 := bstep (se 3 (by rfl) ⟨8631245, by rfl⟩ : syracuseStep 46033309 = 17262491) B17262491
theorem B61377745 : Blo 1993435 61377745 := bstep (se 2 (by rfl) ⟨23016654, by rfl⟩ : syracuseStep 61377745 = 46033309) B46033309
theorem B81836993 : Blo 1993435 81836993 := bstep (se 2 (by rfl) ⟨30688872, by rfl⟩ : syracuseStep 81836993 = 61377745) B61377745
theorem B54557995 : Blo 1993435 54557995 := bstep (se 1 (by rfl) ⟨40918496, by rfl⟩ : syracuseStep 54557995 = 81836993) B81836993
theorem B72743993 : Blo 1993435 72743993 := bstep (se 2 (by rfl) ⟨27278997, by rfl⟩ : syracuseStep 72743993 = 54557995) B54557995
theorem B48495995 : Blo 1993435 48495995 := bstep (se 1 (by rfl) ⟨36371996, by rfl⟩ : syracuseStep 48495995 = 72743993) B72743993
theorem B32330663 : Blo 1993435 32330663 := bstep (se 1 (by rfl) ⟨24247997, by rfl⟩ : syracuseStep 32330663 = 48495995) B48495995
theorem B21553775 : Blo 1993435 21553775 := bstep (se 1 (by rfl) ⟨16165331, by rfl⟩ : syracuseStep 21553775 = 32330663) B32330663
theorem B14369183 : Blo 1993435 14369183 := bstep (se 1 (by rfl) ⟨10776887, by rfl⟩ : syracuseStep 14369183 = 21553775) B21553775
theorem B9579455 : Blo 1993435 9579455 := bstep (se 1 (by rfl) ⟨7184591, by rfl⟩ : syracuseStep 9579455 = 14369183) B14369183
theorem B6386303 : Blo 1993435 6386303 := bstep (se 1 (by rfl) ⟨4789727, by rfl⟩ : syracuseStep 6386303 = 9579455) B9579455
theorem B4257535 : Blo 1993435 4257535 := bstep (se 1 (by rfl) ⟨3193151, by rfl⟩ : syracuseStep 4257535 = 6386303) B6386303
theorem B5676713 : Blo 1993435 5676713 := bstep (se 2 (by rfl) ⟨2128767, by rfl⟩ : syracuseStep 5676713 = 4257535) B4257535
theorem B3784475 : Blo 1993435 3784475 := bstep (se 1 (by rfl) ⟨2838356, by rfl⟩ : syracuseStep 3784475 = 5676713) B5676713
theorem B2522983 : Blo 1993435 2522983 := bstep (se 1 (by rfl) ⟨1892237, by rfl⟩ : syracuseStep 2522983 = 3784475) B3784475
theorem B3363977 : Blo 1993435 3363977 := bstep (se 2 (by rfl) ⟨1261491, by rfl⟩ : syracuseStep 3363977 = 2522983) B2522983
theorem B2242651 : Blo 1993435 2242651 := bstep (se 1 (by rfl) ⟨1681988, by rfl⟩ : syracuseStep 2242651 = 3363977) B3363977
theorem B2990201 : Blo 1993435 2990201 := bstep (se 2 (by rfl) ⟨1121325, by rfl⟩ : syracuseStep 2990201 = 2242651) B2242651
theorem B1993467 : Blo 1993435 1993467 := bstep (se 1 (by rfl) ⟨1495100, by rfl⟩ : syracuseStep 1993467 = 2990201) B2990201
theorem B5114821 : Blo 1993435 5114821 := bbase (se 4 (by rfl) ⟨479514, by rfl⟩ : syracuseStep 5114821 = 959029) (by norm_num)
theorem B6819761 : Blo 1993435 6819761 := bstep (se 2 (by rfl) ⟨2557410, by rfl⟩ : syracuseStep 6819761 = 5114821) B5114821
theorem B18186029 : Blo 1993435 18186029 := bstep (se 3 (by rfl) ⟨3409880, by rfl⟩ : syracuseStep 18186029 = 6819761) B6819761
theorem B12124019 : Blo 1993435 12124019 := bstep (se 1 (by rfl) ⟨9093014, by rfl⟩ : syracuseStep 12124019 = 18186029) B18186029
theorem B8082679 : Blo 1993435 8082679 := bstep (se 1 (by rfl) ⟨6062009, by rfl⟩ : syracuseStep 8082679 = 12124019) B12124019
theorem B10776905 : Blo 1993435 10776905 := bstep (se 2 (by rfl) ⟨4041339, by rfl⟩ : syracuseStep 10776905 = 8082679) B8082679
theorem B7184603 : Blo 1993435 7184603 := bstep (se 1 (by rfl) ⟨5388452, by rfl⟩ : syracuseStep 7184603 = 10776905) B10776905
theorem B4789735 : Blo 1993435 4789735 := bstep (se 1 (by rfl) ⟨3592301, by rfl⟩ : syracuseStep 4789735 = 7184603) B7184603
theorem B25545253 : Blo 1993435 25545253 := bstep (se 4 (by rfl) ⟨2394867, by rfl⟩ : syracuseStep 25545253 = 4789735) B4789735
theorem B34060337 : Blo 1993435 34060337 := bstep (se 2 (by rfl) ⟨12772626, by rfl⟩ : syracuseStep 34060337 = 25545253) B25545253
theorem B22706891 : Blo 1993435 22706891 := bstep (se 1 (by rfl) ⟨17030168, by rfl⟩ : syracuseStep 22706891 = 34060337) B34060337
theorem B15137927 : Blo 1993435 15137927 := bstep (se 1 (by rfl) ⟨11353445, by rfl⟩ : syracuseStep 15137927 = 22706891) B22706891
theorem B10091951 : Blo 1993435 10091951 := bstep (se 1 (by rfl) ⟨7568963, by rfl⟩ : syracuseStep 10091951 = 15137927) B15137927
theorem B6727967 : Blo 1993435 6727967 := bstep (se 1 (by rfl) ⟨5045975, by rfl⟩ : syracuseStep 6727967 = 10091951) B10091951
theorem B4485311 : Blo 1993435 4485311 := bstep (se 1 (by rfl) ⟨3363983, by rfl⟩ : syracuseStep 4485311 = 6727967) B6727967
theorem B2990207 : Blo 1993435 2990207 := bstep (se 1 (by rfl) ⟨2242655, by rfl⟩ : syracuseStep 2990207 = 4485311) B4485311
theorem B1993471 : Blo 1993435 1993471 := bstep (se 1 (by rfl) ⟨1495103, by rfl⟩ : syracuseStep 1993471 = 2990207) B2990207
theorem B2990213 : Blo 1993435 2990213 := bbase (se 4 (by rfl) ⟨280332, by rfl⟩ : syracuseStep 2990213 = 560665) (by norm_num)
theorem B1993475 : Blo 1993435 1993475 := bstep (se 1 (by rfl) ⟨1495106, by rfl⟩ : syracuseStep 1993475 = 2990213) B2990213
theorem B3363997 : Blo 1993435 3363997 := bbase (se 3 (by rfl) ⟨630749, by rfl⟩ : syracuseStep 3363997 = 1261499) (by norm_num)
theorem B4485329 : Blo 1993435 4485329 := bstep (se 2 (by rfl) ⟨1681998, by rfl⟩ : syracuseStep 4485329 = 3363997) B3363997
theorem B2990219 : Blo 1993435 2990219 := bstep (se 1 (by rfl) ⟨2242664, by rfl⟩ : syracuseStep 2990219 = 4485329) B4485329
theorem B1993479 : Blo 1993435 1993479 := bstep (se 1 (by rfl) ⟨1495109, by rfl⟩ : syracuseStep 1993479 = 2990219) B2990219
theorem B2242669 : Blo 1993435 2242669 := bbase (se 3 (by rfl) ⟨420500, by rfl⟩ : syracuseStep 2242669 = 841001) (by norm_num)
theorem B2990225 : Blo 1993435 2990225 := bstep (se 2 (by rfl) ⟨1121334, by rfl⟩ : syracuseStep 2990225 = 2242669) B2242669
theorem B1993483 : Blo 1993435 1993483 := bstep (se 1 (by rfl) ⟨1495112, by rfl⟩ : syracuseStep 1993483 = 2990225) B2990225
theorem B6728021 : Blo 1993435 6728021 := bbase (se 10 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 6728021 = 19711) (by norm_num)
theorem B4485347 : Blo 1993435 4485347 := bstep (se 1 (by rfl) ⟨3364010, by rfl⟩ : syracuseStep 4485347 = 6728021) B6728021
theorem B2990231 : Blo 1993435 2990231 := bstep (se 1 (by rfl) ⟨2242673, by rfl⟩ : syracuseStep 2990231 = 4485347) B4485347
theorem B1993487 : Blo 1993435 1993487 := bstep (se 1 (by rfl) ⟨1495115, by rfl⟩ : syracuseStep 1993487 = 2990231) B2990231
theorem B2990237 : Blo 1993435 2990237 := bbase (se 3 (by rfl) ⟨560669, by rfl⟩ : syracuseStep 2990237 = 1121339) (by norm_num)
theorem B1993491 : Blo 1993435 1993491 := bstep (se 1 (by rfl) ⟨1495118, by rfl⟩ : syracuseStep 1993491 = 2990237) B2990237
theorem B4485365 : Blo 1993435 4485365 := bbase (se 5 (by rfl) ⟨210251, by rfl⟩ : syracuseStep 4485365 = 420503) (by norm_num)
theorem B2990243 : Blo 1993435 2990243 := bstep (se 1 (by rfl) ⟨2242682, by rfl⟩ : syracuseStep 2990243 = 4485365) B4485365
theorem B1993495 : Blo 1993435 1993495 := bstep (se 1 (by rfl) ⟨1495121, by rfl⟩ : syracuseStep 1993495 = 2990243) B2990243
theorem B4041397 : Blo 1993435 4041397 := bbase (se 5 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 4041397 = 378881) (by norm_num)
theorem B5388529 : Blo 1993435 5388529 := bstep (se 2 (by rfl) ⟨2020698, by rfl⟩ : syracuseStep 5388529 = 4041397) B4041397
theorem B7184705 : Blo 1993435 7184705 := bstep (se 2 (by rfl) ⟨2694264, by rfl⟩ : syracuseStep 7184705 = 5388529) B5388529
theorem B19159213 : Blo 1993435 19159213 := bstep (se 3 (by rfl) ⟨3592352, by rfl⟩ : syracuseStep 19159213 = 7184705) B7184705
theorem B25545617 : Blo 1993435 25545617 := bstep (se 2 (by rfl) ⟨9579606, by rfl⟩ : syracuseStep 25545617 = 19159213) B19159213
theorem B17030411 : Blo 1993435 17030411 := bstep (se 1 (by rfl) ⟨12772808, by rfl⟩ : syracuseStep 17030411 = 25545617) B25545617
theorem B11353607 : Blo 1993435 11353607 := bstep (se 1 (by rfl) ⟨8515205, by rfl⟩ : syracuseStep 11353607 = 17030411) B17030411
theorem B7569071 : Blo 1993435 7569071 := bstep (se 1 (by rfl) ⟨5676803, by rfl⟩ : syracuseStep 7569071 = 11353607) B11353607
theorem B5046047 : Blo 1993435 5046047 := bstep (se 1 (by rfl) ⟨3784535, by rfl⟩ : syracuseStep 5046047 = 7569071) B7569071
theorem B3364031 : Blo 1993435 3364031 := bstep (se 1 (by rfl) ⟨2523023, by rfl⟩ : syracuseStep 3364031 = 5046047) B5046047
theorem B2242687 : Blo 1993435 2242687 := bstep (se 1 (by rfl) ⟨1682015, by rfl⟩ : syracuseStep 2242687 = 3364031) B3364031
theorem B2990249 : Blo 1993435 2990249 := bstep (se 2 (by rfl) ⟨1121343, by rfl⟩ : syracuseStep 2990249 = 2242687) B2242687
theorem B1993499 : Blo 1993435 1993499 := bstep (se 1 (by rfl) ⟨1495124, by rfl⟩ : syracuseStep 1993499 = 2990249) B2990249
theorem B4789813 : Blo 1993435 4789813 := bbase (se 5 (by rfl) ⟨224522, by rfl⟩ : syracuseStep 4789813 = 449045) (by norm_num)
theorem B6386417 : Blo 1993435 6386417 := bstep (se 2 (by rfl) ⟨2394906, by rfl⟩ : syracuseStep 6386417 = 4789813) B4789813
theorem B4257611 : Blo 1993435 4257611 := bstep (se 1 (by rfl) ⟨3193208, by rfl⟩ : syracuseStep 4257611 = 6386417) B6386417
theorem B2838407 : Blo 1993435 2838407 := bstep (se 1 (by rfl) ⟨2128805, by rfl⟩ : syracuseStep 2838407 = 4257611) B4257611
theorem B7569085 : Blo 1993435 7569085 := bstep (se 3 (by rfl) ⟨1419203, by rfl⟩ : syracuseStep 7569085 = 2838407) B2838407
theorem B10092113 : Blo 1993435 10092113 := bstep (se 2 (by rfl) ⟨3784542, by rfl⟩ : syracuseStep 10092113 = 7569085) B7569085
theorem B6728075 : Blo 1993435 6728075 := bstep (se 1 (by rfl) ⟨5046056, by rfl⟩ : syracuseStep 6728075 = 10092113) B10092113
theorem B4485383 : Blo 1993435 4485383 := bstep (se 1 (by rfl) ⟨3364037, by rfl⟩ : syracuseStep 4485383 = 6728075) B6728075
theorem B2990255 : Blo 1993435 2990255 := bstep (se 1 (by rfl) ⟨2242691, by rfl⟩ : syracuseStep 2990255 = 4485383) B4485383
theorem B1993503 : Blo 1993435 1993503 := bstep (se 1 (by rfl) ⟨1495127, by rfl⟩ : syracuseStep 1993503 = 2990255) B2990255
theorem B2990261 : Blo 1993435 2990261 := bbase (se 5 (by rfl) ⟨140168, by rfl⟩ : syracuseStep 2990261 = 280337) (by norm_num)
theorem B1993507 : Blo 1993435 1993507 := bstep (se 1 (by rfl) ⟨1495130, by rfl⟩ : syracuseStep 1993507 = 2990261) B2990261
theorem B5046077 : Blo 1993435 5046077 := bbase (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) (by norm_num)
theorem B3364051 : Blo 1993435 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B4485401 : Blo 1993435 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B2990267 : Blo 1993435 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B1993511 : Blo 1993435 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B2242705 : Blo 1993435 2242705 := bbase (se 2 (by rfl) ⟨841014, by rfl⟩ : syracuseStep 2242705 = 1682029) (by norm_num)
theorem B2990273 : Blo 1993435 2990273 := bstep (se 2 (by rfl) ⟨1121352, by rfl⟩ : syracuseStep 2990273 = 2242705) B2242705
theorem B1993515 : Blo 1993435 1993515 := bstep (se 1 (by rfl) ⟨1495136, by rfl⟩ : syracuseStep 1993515 = 2990273) B2990273
theorem B3784573 : Blo 1993435 3784573 := bbase (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) (by norm_num)
theorem B5046097 : Blo 1993435 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B6728129 : Blo 1993435 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B4485419 : Blo 1993435 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B2990279 : Blo 1993435 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B1993519 : Blo 1993435 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B2990285 : Blo 1993435 2990285 := bbase (se 3 (by rfl) ⟨560678, by rfl⟩ : syracuseStep 2990285 = 1121357) (by norm_num)
theorem B1993523 : Blo 1993435 1993523 := bstep (se 1 (by rfl) ⟨1495142, by rfl⟩ : syracuseStep 1993523 = 2990285) B2990285
theorem B4485437 : Blo 1993435 4485437 := bbase (se 3 (by rfl) ⟨841019, by rfl⟩ : syracuseStep 4485437 = 1682039) (by norm_num)
theorem B2990291 : Blo 1993435 2990291 := bstep (se 1 (by rfl) ⟨2242718, by rfl⟩ : syracuseStep 2990291 = 4485437) B4485437
theorem B1993527 : Blo 1993435 1993527 := bstep (se 1 (by rfl) ⟨1495145, by rfl⟩ : syracuseStep 1993527 = 2990291) B2990291
theorem B3364085 : Blo 1993435 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B2242723 : Blo 1993435 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B2990297 : Blo 1993435 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B1993531 : Blo 1993435 1993531 := bstep (se 1 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 1993531 = 2990297) B2990297
theorem B5462149 : Blo 1993435 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B7282865 : Blo 1993435 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B4855243 : Blo 1993435 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B6473657 : Blo 1993435 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B4315771 : Blo 1993435 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B23017445 : Blo 1993435 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B15344963 : Blo 1993435 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B10229975 : Blo 1993435 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B6819983 : Blo 1993435 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B4546655 : Blo 1993435 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B3031103 : Blo 1993435 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B2020735 : Blo 1993435 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B2694313 : Blo 1993435 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B14369669 : Blo 1993435 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B9579779 : Blo 1993435 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B6386519 : Blo 1993435 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B4257679 : Blo 1993435 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B5676905 : Blo 1993435 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B15138413 : Blo 1993435 15138413 := bstep (se 3 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 15138413 = 5676905) B5676905
theorem B10092275 : Blo 1993435 10092275 := bstep (se 1 (by rfl) ⟨7569206, by rfl⟩ : syracuseStep 10092275 = 15138413) B15138413
theorem B6728183 : Blo 1993435 6728183 := bstep (se 1 (by rfl) ⟨5046137, by rfl⟩ : syracuseStep 6728183 = 10092275) B10092275
theorem B4485455 : Blo 1993435 4485455 := bstep (se 1 (by rfl) ⟨3364091, by rfl⟩ : syracuseStep 4485455 = 6728183) B6728183
theorem B2990303 : Blo 1993435 2990303 := bstep (se 1 (by rfl) ⟨2242727, by rfl⟩ : syracuseStep 2990303 = 4485455) B4485455
theorem B1993535 : Blo 1993435 1993535 := bstep (se 1 (by rfl) ⟨1495151, by rfl⟩ : syracuseStep 1993535 = 2990303) B2990303
theorem B2990309 : Blo 1993435 2990309 := bbase (se 4 (by rfl) ⟨280341, by rfl⟩ : syracuseStep 2990309 = 560683) (by norm_num)
theorem B1993539 : Blo 1993435 1993539 := bstep (se 1 (by rfl) ⟨1495154, by rfl⟩ : syracuseStep 1993539 = 2990309) B2990309
theorem B2694325 : Blo 1993435 2694325 := bbase (se 5 (by rfl) ⟨126296, by rfl⟩ : syracuseStep 2694325 = 252593) (by norm_num)
theorem B3592433 : Blo 1993435 3592433 := bstep (se 2 (by rfl) ⟨1347162, by rfl⟩ : syracuseStep 3592433 = 2694325) B2694325
theorem B2394955 : Blo 1993435 2394955 := bstep (se 1 (by rfl) ⟨1796216, by rfl⟩ : syracuseStep 2394955 = 3592433) B3592433
theorem B3193273 : Blo 1993435 3193273 := bstep (se 2 (by rfl) ⟨1197477, by rfl⟩ : syracuseStep 3193273 = 2394955) B2394955
theorem B4257697 : Blo 1993435 4257697 := bstep (se 2 (by rfl) ⟨1596636, by rfl⟩ : syracuseStep 4257697 = 3193273) B3193273
theorem B5676929 : Blo 1993435 5676929 := bstep (se 2 (by rfl) ⟨2128848, by rfl⟩ : syracuseStep 5676929 = 4257697) B4257697
theorem B3784619 : Blo 1993435 3784619 := bstep (se 1 (by rfl) ⟨2838464, by rfl⟩ : syracuseStep 3784619 = 5676929) B5676929
theorem B2523079 : Blo 1993435 2523079 := bstep (se 1 (by rfl) ⟨1892309, by rfl⟩ : syracuseStep 2523079 = 3784619) B3784619
theorem B3364105 : Blo 1993435 3364105 := bstep (se 2 (by rfl) ⟨1261539, by rfl⟩ : syracuseStep 3364105 = 2523079) B2523079
theorem B4485473 : Blo 1993435 4485473 := bstep (se 2 (by rfl) ⟨1682052, by rfl⟩ : syracuseStep 4485473 = 3364105) B3364105
theorem B2990315 : Blo 1993435 2990315 := bstep (se 1 (by rfl) ⟨2242736, by rfl⟩ : syracuseStep 2990315 = 4485473) B4485473
theorem B1993543 : Blo 1993435 1993543 := bstep (se 1 (by rfl) ⟨1495157, by rfl⟩ : syracuseStep 1993543 = 2990315) B2990315
theorem B2242741 : Blo 1993435 2242741 := bbase (se 5 (by rfl) ⟨105128, by rfl⟩ : syracuseStep 2242741 = 210257) (by norm_num)
theorem B2990321 : Blo 1993435 2990321 := bstep (se 2 (by rfl) ⟨1121370, by rfl⟩ : syracuseStep 2990321 = 2242741) B2242741
theorem B1993547 : Blo 1993435 1993547 := bstep (se 1 (by rfl) ⟨1495160, by rfl⟩ : syracuseStep 1993547 = 2990321) B2990321
theorem B2523089 : Blo 1993435 2523089 := bbase (se 2 (by rfl) ⟨946158, by rfl⟩ : syracuseStep 2523089 = 1892317) (by norm_num)
theorem B6728237 : Blo 1993435 6728237 := bstep (se 3 (by rfl) ⟨1261544, by rfl⟩ : syracuseStep 6728237 = 2523089) B2523089
theorem B4485491 : Blo 1993435 4485491 := bstep (se 1 (by rfl) ⟨3364118, by rfl⟩ : syracuseStep 4485491 = 6728237) B6728237
theorem B2990327 : Blo 1993435 2990327 := bstep (se 1 (by rfl) ⟨2242745, by rfl⟩ : syracuseStep 2990327 = 4485491) B4485491
theorem B1993551 : Blo 1993435 1993551 := bstep (se 1 (by rfl) ⟨1495163, by rfl⟩ : syracuseStep 1993551 = 2990327) B2990327
theorem B2990333 : Blo 1993435 2990333 := bbase (se 3 (by rfl) ⟨560687, by rfl⟩ : syracuseStep 2990333 = 1121375) (by norm_num)
theorem B1993555 : Blo 1993435 1993555 := bstep (se 1 (by rfl) ⟨1495166, by rfl⟩ : syracuseStep 1993555 = 2990333) B2990333
theorem B4485509 : Blo 1993435 4485509 := bbase (se 4 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 4485509 = 841033) (by norm_num)
theorem B2990339 : Blo 1993435 2990339 := bstep (se 1 (by rfl) ⟨2242754, by rfl⟩ : syracuseStep 2990339 = 4485509) B4485509
theorem B1993559 : Blo 1993435 1993559 := bstep (se 1 (by rfl) ⟨1495169, by rfl⟩ : syracuseStep 1993559 = 2990339) B2990339
theorem B2838493 : Blo 1993435 2838493 := bbase (se 3 (by rfl) ⟨532217, by rfl⟩ : syracuseStep 2838493 = 1064435) (by norm_num)
theorem B3784657 : Blo 1993435 3784657 := bstep (se 2 (by rfl) ⟨1419246, by rfl⟩ : syracuseStep 3784657 = 2838493) B2838493
theorem B5046209 : Blo 1993435 5046209 := bstep (se 2 (by rfl) ⟨1892328, by rfl⟩ : syracuseStep 5046209 = 3784657) B3784657
theorem B3364139 : Blo 1993435 3364139 := bstep (se 1 (by rfl) ⟨2523104, by rfl⟩ : syracuseStep 3364139 = 5046209) B5046209
theorem B2242759 : Blo 1993435 2242759 := bstep (se 1 (by rfl) ⟨1682069, by rfl⟩ : syracuseStep 2242759 = 3364139) B3364139
theorem B2990345 : Blo 1993435 2990345 := bstep (se 2 (by rfl) ⟨1121379, by rfl⟩ : syracuseStep 2990345 = 2242759) B2242759
theorem B1993563 : Blo 1993435 1993563 := bstep (se 1 (by rfl) ⟨1495172, by rfl⟩ : syracuseStep 1993563 = 2990345) B2990345
theorem B10092437 : Blo 1993435 10092437 := bbase (se 6 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 10092437 = 473083) (by norm_num)
theorem B6728291 : Blo 1993435 6728291 := bstep (se 1 (by rfl) ⟨5046218, by rfl⟩ : syracuseStep 6728291 = 10092437) B10092437
theorem B4485527 : Blo 1993435 4485527 := bstep (se 1 (by rfl) ⟨3364145, by rfl⟩ : syracuseStep 4485527 = 6728291) B6728291
theorem B2990351 : Blo 1993435 2990351 := bstep (se 1 (by rfl) ⟨2242763, by rfl⟩ : syracuseStep 2990351 = 4485527) B4485527
theorem B1993567 : Blo 1993435 1993567 := bstep (se 1 (by rfl) ⟨1495175, by rfl⟩ : syracuseStep 1993567 = 2990351) B2990351
theorem B2990357 : Blo 1993435 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B1993571 : Blo 1993435 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B3836317 : Blo 1993435 3836317 := bbase (se 3 (by rfl) ⟨719309, by rfl⟩ : syracuseStep 3836317 = 1438619) (by norm_num)
theorem B5115089 : Blo 1993435 5115089 := bstep (se 2 (by rfl) ⟨1918158, by rfl⟩ : syracuseStep 5115089 = 3836317) B3836317
theorem B13640237 : Blo 1993435 13640237 := bstep (se 3 (by rfl) ⟨2557544, by rfl⟩ : syracuseStep 13640237 = 5115089) B5115089
theorem B9093491 : Blo 1993435 9093491 := bstep (se 1 (by rfl) ⟨6820118, by rfl⟩ : syracuseStep 9093491 = 13640237) B13640237
theorem B6062327 : Blo 1993435 6062327 := bstep (se 1 (by rfl) ⟨4546745, by rfl⟩ : syracuseStep 6062327 = 9093491) B9093491
theorem B4041551 : Blo 1993435 4041551 := bstep (se 1 (by rfl) ⟨3031163, by rfl⟩ : syracuseStep 4041551 = 6062327) B6062327
theorem B2694367 : Blo 1993435 2694367 := bstep (se 1 (by rfl) ⟨2020775, by rfl⟩ : syracuseStep 2694367 = 4041551) B4041551
theorem B14369957 : Blo 1993435 14369957 := bstep (se 4 (by rfl) ⟨1347183, by rfl⟩ : syracuseStep 14369957 = 2694367) B2694367
theorem B9579971 : Blo 1993435 9579971 := bstep (se 1 (by rfl) ⟨7184978, by rfl⟩ : syracuseStep 9579971 = 14369957) B14369957
theorem B25546589 : Blo 1993435 25546589 := bstep (se 3 (by rfl) ⟨4789985, by rfl⟩ : syracuseStep 25546589 = 9579971) B9579971
theorem B17031059 : Blo 1993435 17031059 := bstep (se 1 (by rfl) ⟨12773294, by rfl⟩ : syracuseStep 17031059 = 25546589) B25546589
theorem B11354039 : Blo 1993435 11354039 := bstep (se 1 (by rfl) ⟨8515529, by rfl⟩ : syracuseStep 11354039 = 17031059) B17031059
theorem B7569359 : Blo 1993435 7569359 := bstep (se 1 (by rfl) ⟨5677019, by rfl⟩ : syracuseStep 7569359 = 11354039) B11354039
theorem B5046239 : Blo 1993435 5046239 := bstep (se 1 (by rfl) ⟨3784679, by rfl⟩ : syracuseStep 5046239 = 7569359) B7569359
theorem B3364159 : Blo 1993435 3364159 := bstep (se 1 (by rfl) ⟨2523119, by rfl⟩ : syracuseStep 3364159 = 5046239) B5046239
theorem B4485545 : Blo 1993435 4485545 := bstep (se 2 (by rfl) ⟨1682079, by rfl⟩ : syracuseStep 4485545 = 3364159) B3364159
theorem B2990363 : Blo 1993435 2990363 := bstep (se 1 (by rfl) ⟨2242772, by rfl⟩ : syracuseStep 2990363 = 4485545) B4485545
theorem B1993575 : Blo 1993435 1993575 := bstep (se 1 (by rfl) ⟨1495181, by rfl⟩ : syracuseStep 1993575 = 2990363) B2990363
theorem B2242777 : Blo 1993435 2242777 := bbase (se 2 (by rfl) ⟨841041, by rfl⟩ : syracuseStep 2242777 = 1682083) (by norm_num)
theorem B2990369 : Blo 1993435 2990369 := bstep (se 2 (by rfl) ⟨1121388, by rfl⟩ : syracuseStep 2990369 = 2242777) B2242777
theorem B1993579 : Blo 1993435 1993579 := bstep (se 1 (by rfl) ⟨1495184, by rfl⟩ : syracuseStep 1993579 = 2990369) B2990369
theorem B9710725 : Blo 1993435 9710725 := bbase (se 4 (by rfl) ⟨910380, by rfl⟩ : syracuseStep 9710725 = 1820761) (by norm_num)
theorem B12947633 : Blo 1993435 12947633 := bstep (se 2 (by rfl) ⟨4855362, by rfl⟩ : syracuseStep 12947633 = 9710725) B9710725
theorem B8631755 : Blo 1993435 8631755 := bstep (se 1 (by rfl) ⟨6473816, by rfl⟩ : syracuseStep 8631755 = 12947633) B12947633
theorem B5754503 : Blo 1993435 5754503 := bstep (se 1 (by rfl) ⟨4315877, by rfl⟩ : syracuseStep 5754503 = 8631755) B8631755
theorem B3836335 : Blo 1993435 3836335 := bstep (se 1 (by rfl) ⟨2877251, by rfl⟩ : syracuseStep 3836335 = 5754503) B5754503
theorem B5115113 : Blo 1993435 5115113 := bstep (se 2 (by rfl) ⟨1918167, by rfl⟩ : syracuseStep 5115113 = 3836335) B3836335
theorem B3410075 : Blo 1993435 3410075 := bstep (se 1 (by rfl) ⟨2557556, by rfl⟩ : syracuseStep 3410075 = 5115113) B5115113
theorem B2273383 : Blo 1993435 2273383 := bstep (se 1 (by rfl) ⟨1705037, by rfl⟩ : syracuseStep 2273383 = 3410075) B3410075
theorem B3031177 : Blo 1993435 3031177 := bstep (se 2 (by rfl) ⟨1136691, by rfl⟩ : syracuseStep 3031177 = 2273383) B2273383
theorem B4041569 : Blo 1993435 4041569 := bstep (se 2 (by rfl) ⟨1515588, by rfl⟩ : syracuseStep 4041569 = 3031177) B3031177
theorem B2694379 : Blo 1993435 2694379 := bstep (se 1 (by rfl) ⟨2020784, by rfl⟩ : syracuseStep 2694379 = 4041569) B4041569
theorem B3592505 : Blo 1993435 3592505 := bstep (se 2 (by rfl) ⟨1347189, by rfl⟩ : syracuseStep 3592505 = 2694379) B2694379
theorem B2395003 : Blo 1993435 2395003 := bstep (se 1 (by rfl) ⟨1796252, by rfl⟩ : syracuseStep 2395003 = 3592505) B3592505
theorem B3193337 : Blo 1993435 3193337 := bstep (se 2 (by rfl) ⟨1197501, by rfl⟩ : syracuseStep 3193337 = 2395003) B2395003
theorem B2128891 : Blo 1993435 2128891 := bstep (se 1 (by rfl) ⟨1596668, by rfl⟩ : syracuseStep 2128891 = 3193337) B3193337
theorem B2838521 : Blo 1993435 2838521 := bstep (se 2 (by rfl) ⟨1064445, by rfl⟩ : syracuseStep 2838521 = 2128891) B2128891
theorem B7569389 : Blo 1993435 7569389 := bstep (se 3 (by rfl) ⟨1419260, by rfl⟩ : syracuseStep 7569389 = 2838521) B2838521
theorem B5046259 : Blo 1993435 5046259 := bstep (se 1 (by rfl) ⟨3784694, by rfl⟩ : syracuseStep 5046259 = 7569389) B7569389
theorem B6728345 : Blo 1993435 6728345 := bstep (se 2 (by rfl) ⟨2523129, by rfl⟩ : syracuseStep 6728345 = 5046259) B5046259
theorem B4485563 : Blo 1993435 4485563 := bstep (se 1 (by rfl) ⟨3364172, by rfl⟩ : syracuseStep 4485563 = 6728345) B6728345
theorem B2990375 : Blo 1993435 2990375 := bstep (se 1 (by rfl) ⟨2242781, by rfl⟩ : syracuseStep 2990375 = 4485563) B4485563
theorem B1993583 : Blo 1993435 1993583 := bstep (se 1 (by rfl) ⟨1495187, by rfl⟩ : syracuseStep 1993583 = 2990375) B2990375
theorem B2990381 : Blo 1993435 2990381 := bbase (se 3 (by rfl) ⟨560696, by rfl⟩ : syracuseStep 2990381 = 1121393) (by norm_num)
theorem B1993587 : Blo 1993435 1993587 := bstep (se 1 (by rfl) ⟨1495190, by rfl⟩ : syracuseStep 1993587 = 2990381) B2990381
theorem B4485581 : Blo 1993435 4485581 := bbase (se 3 (by rfl) ⟨841046, by rfl⟩ : syracuseStep 4485581 = 1682093) (by norm_num)
theorem B2990387 : Blo 1993435 2990387 := bstep (se 1 (by rfl) ⟨2242790, by rfl⟩ : syracuseStep 2990387 = 4485581) B4485581
theorem B1993591 : Blo 1993435 1993591 := bstep (se 1 (by rfl) ⟨1495193, by rfl⟩ : syracuseStep 1993591 = 2990387) B2990387
theorem B2523145 : Blo 1993435 2523145 := bbase (se 2 (by rfl) ⟨946179, by rfl⟩ : syracuseStep 2523145 = 1892359) (by norm_num)
theorem B3364193 : Blo 1993435 3364193 := bstep (se 2 (by rfl) ⟨1261572, by rfl⟩ : syracuseStep 3364193 = 2523145) B2523145
theorem B2242795 : Blo 1993435 2242795 := bstep (se 1 (by rfl) ⟨1682096, by rfl⟩ : syracuseStep 2242795 = 3364193) B3364193
theorem B2990393 : Blo 1993435 2990393 := bstep (se 2 (by rfl) ⟨1121397, by rfl⟩ : syracuseStep 2990393 = 2242795) B2242795
theorem B1993595 : Blo 1993435 1993595 := bstep (se 1 (by rfl) ⟨1495196, by rfl⟩ : syracuseStep 1993595 = 2990393) B2990393
theorem B6473861 : Blo 1993435 6473861 := bbase (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) (by norm_num)
theorem B4315907 : Blo 1993435 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B11509085 : Blo 1993435 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B30690893 : Blo 1993435 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B20460595 : Blo 1993435 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B27280793 : Blo 1993435 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B18187195 : Blo 1993435 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B24249593 : Blo 1993435 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B16166395 : Blo 1993435 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B21555193 : Blo 1993435 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B28740257 : Blo 1993435 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B19160171 : Blo 1993435 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B12773447 : Blo 1993435 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B8515631 : Blo 1993435 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B22708349 : Blo 1993435 22708349 := bstep (se 3 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 22708349 = 8515631) B8515631
theorem B15138899 : Blo 1993435 15138899 := bstep (se 1 (by rfl) ⟨11354174, by rfl⟩ : syracuseStep 15138899 = 22708349) B22708349
theorem B10092599 : Blo 1993435 10092599 := bstep (se 1 (by rfl) ⟨7569449, by rfl⟩ : syracuseStep 10092599 = 15138899) B15138899
theorem B6728399 : Blo 1993435 6728399 := bstep (se 1 (by rfl) ⟨5046299, by rfl⟩ : syracuseStep 6728399 = 10092599) B10092599
theorem B4485599 : Blo 1993435 4485599 := bstep (se 1 (by rfl) ⟨3364199, by rfl⟩ : syracuseStep 4485599 = 6728399) B6728399
theorem B2990399 : Blo 1993435 2990399 := bstep (se 1 (by rfl) ⟨2242799, by rfl⟩ : syracuseStep 2990399 = 4485599) B4485599
theorem B1993599 : Blo 1993435 1993599 := bstep (se 1 (by rfl) ⟨1495199, by rfl⟩ : syracuseStep 1993599 = 2990399) B2990399
theorem B2990405 : Blo 1993435 2990405 := bbase (se 4 (by rfl) ⟨280350, by rfl⟩ : syracuseStep 2990405 = 560701) (by norm_num)
theorem B1993603 : Blo 1993435 1993603 := bstep (se 1 (by rfl) ⟨1495202, by rfl⟩ : syracuseStep 1993603 = 2990405) B2990405
theorem B3364213 : Blo 1993435 3364213 := bbase (se 5 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 3364213 = 315395) (by norm_num)
theorem B4485617 : Blo 1993435 4485617 := bstep (se 2 (by rfl) ⟨1682106, by rfl⟩ : syracuseStep 4485617 = 3364213) B3364213
theorem B2990411 : Blo 1993435 2990411 := bstep (se 1 (by rfl) ⟨2242808, by rfl⟩ : syracuseStep 2990411 = 4485617) B4485617
theorem B1993607 : Blo 1993435 1993607 := bstep (se 1 (by rfl) ⟨1495205, by rfl⟩ : syracuseStep 1993607 = 2990411) B2990411
theorem B2242813 : Blo 1993435 2242813 := bbase (se 3 (by rfl) ⟨420527, by rfl⟩ : syracuseStep 2242813 = 841055) (by norm_num)
theorem B2990417 : Blo 1993435 2990417 := bstep (se 2 (by rfl) ⟨1121406, by rfl⟩ : syracuseStep 2990417 = 2242813) B2242813
theorem B1993611 : Blo 1993435 1993611 := bstep (se 1 (by rfl) ⟨1495208, by rfl⟩ : syracuseStep 1993611 = 2990417) B2990417
theorem B6728453 : Blo 1993435 6728453 := bbase (se 4 (by rfl) ⟨630792, by rfl⟩ : syracuseStep 6728453 = 1261585) (by norm_num)
theorem B4485635 : Blo 1993435 4485635 := bstep (se 1 (by rfl) ⟨3364226, by rfl⟩ : syracuseStep 4485635 = 6728453) B6728453
theorem B2990423 : Blo 1993435 2990423 := bstep (se 1 (by rfl) ⟨2242817, by rfl⟩ : syracuseStep 2990423 = 4485635) B4485635
theorem B1993615 : Blo 1993435 1993615 := bstep (se 1 (by rfl) ⟨1495211, by rfl⟩ : syracuseStep 1993615 = 2990423) B2990423
theorem B2990429 : Blo 1993435 2990429 := bbase (se 3 (by rfl) ⟨560705, by rfl⟩ : syracuseStep 2990429 = 1121411) (by norm_num)
theorem B1993619 : Blo 1993435 1993619 := bstep (se 1 (by rfl) ⟨1495214, by rfl⟩ : syracuseStep 1993619 = 2990429) B2990429
theorem B4485653 : Blo 1993435 4485653 := bbase (se 6 (by rfl) ⟨105132, by rfl⟩ : syracuseStep 4485653 = 210265) (by norm_num)
theorem B2990435 : Blo 1993435 2990435 := bstep (se 1 (by rfl) ⟨2242826, by rfl⟩ : syracuseStep 2990435 = 4485653) B4485653
theorem B1993623 : Blo 1993435 1993623 := bstep (se 1 (by rfl) ⟨1495217, by rfl⟩ : syracuseStep 1993623 = 2990435) B2990435
theorem B7569557 : Blo 1993435 7569557 := bbase (se 6 (by rfl) ⟨177411, by rfl⟩ : syracuseStep 7569557 = 354823) (by norm_num)
theorem B5046371 : Blo 1993435 5046371 := bstep (se 1 (by rfl) ⟨3784778, by rfl⟩ : syracuseStep 5046371 = 7569557) B7569557
theorem B3364247 : Blo 1993435 3364247 := bstep (se 1 (by rfl) ⟨2523185, by rfl⟩ : syracuseStep 3364247 = 5046371) B5046371
theorem B2242831 : Blo 1993435 2242831 := bstep (se 1 (by rfl) ⟨1682123, by rfl⟩ : syracuseStep 2242831 = 3364247) B3364247
theorem B2990441 : Blo 1993435 2990441 := bstep (se 2 (by rfl) ⟨1121415, by rfl⟩ : syracuseStep 2990441 = 2242831) B2242831
theorem B1993627 : Blo 1993435 1993627 := bstep (se 1 (by rfl) ⟨1495220, by rfl⟩ : syracuseStep 1993627 = 2990441) B2990441
theorem B11354357 : Blo 1993435 11354357 := bbase (se 5 (by rfl) ⟨532235, by rfl⟩ : syracuseStep 11354357 = 1064471) (by norm_num)
theorem B7569571 : Blo 1993435 7569571 := bstep (se 1 (by rfl) ⟨5677178, by rfl⟩ : syracuseStep 7569571 = 11354357) B11354357
theorem B10092761 : Blo 1993435 10092761 := bstep (se 2 (by rfl) ⟨3784785, by rfl⟩ : syracuseStep 10092761 = 7569571) B7569571
theorem B6728507 : Blo 1993435 6728507 := bstep (se 1 (by rfl) ⟨5046380, by rfl⟩ : syracuseStep 6728507 = 10092761) B10092761
theorem B4485671 : Blo 1993435 4485671 := bstep (se 1 (by rfl) ⟨3364253, by rfl⟩ : syracuseStep 4485671 = 6728507) B6728507
theorem B2990447 : Blo 1993435 2990447 := bstep (se 1 (by rfl) ⟨2242835, by rfl⟩ : syracuseStep 2990447 = 4485671) B4485671
theorem B1993631 : Blo 1993435 1993631 := bstep (se 1 (by rfl) ⟨1495223, by rfl⟩ : syracuseStep 1993631 = 2990447) B2990447
theorem B2990453 : Blo 1993435 2990453 := bbase (se 5 (by rfl) ⟨140177, by rfl⟩ : syracuseStep 2990453 = 280355) (by norm_num)
theorem B1993635 : Blo 1993435 1993635 := bstep (se 1 (by rfl) ⟨1495226, by rfl⟩ : syracuseStep 1993635 = 2990453) B2990453
theorem B4790141 : Blo 1993435 4790141 := bbase (se 3 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 4790141 = 1796303) (by norm_num)
theorem B3193427 : Blo 1993435 3193427 := bstep (se 1 (by rfl) ⟨2395070, by rfl⟩ : syracuseStep 3193427 = 4790141) B4790141
theorem B2128951 : Blo 1993435 2128951 := bstep (se 1 (by rfl) ⟨1596713, by rfl⟩ : syracuseStep 2128951 = 3193427) B3193427
theorem B2838601 : Blo 1993435 2838601 := bstep (se 2 (by rfl) ⟨1064475, by rfl⟩ : syracuseStep 2838601 = 2128951) B2128951
theorem B3784801 : Blo 1993435 3784801 := bstep (se 2 (by rfl) ⟨1419300, by rfl⟩ : syracuseStep 3784801 = 2838601) B2838601
theorem B5046401 : Blo 1993435 5046401 := bstep (se 2 (by rfl) ⟨1892400, by rfl⟩ : syracuseStep 5046401 = 3784801) B3784801
theorem B3364267 : Blo 1993435 3364267 := bstep (se 1 (by rfl) ⟨2523200, by rfl⟩ : syracuseStep 3364267 = 5046401) B5046401
theorem B4485689 : Blo 1993435 4485689 := bstep (se 2 (by rfl) ⟨1682133, by rfl⟩ : syracuseStep 4485689 = 3364267) B3364267
theorem B2990459 : Blo 1993435 2990459 := bstep (se 1 (by rfl) ⟨2242844, by rfl⟩ : syracuseStep 2990459 = 4485689) B4485689
theorem B1993639 : Blo 1993435 1993639 := bstep (se 1 (by rfl) ⟨1495229, by rfl⟩ : syracuseStep 1993639 = 2990459) B2990459
theorem B2242849 : Blo 1993435 2242849 := bbase (se 2 (by rfl) ⟨841068, by rfl⟩ : syracuseStep 2242849 = 1682137) (by norm_num)
theorem B2990465 : Blo 1993435 2990465 := bstep (se 2 (by rfl) ⟨1121424, by rfl⟩ : syracuseStep 2990465 = 2242849) B2242849
theorem B1993643 : Blo 1993435 1993643 := bstep (se 1 (by rfl) ⟨1495232, by rfl⟩ : syracuseStep 1993643 = 2990465) B2990465
theorem B5046421 : Blo 1993435 5046421 := bbase (se 6 (by rfl) ⟨118275, by rfl⟩ : syracuseStep 5046421 = 236551) (by norm_num)
theorem B6728561 : Blo 1993435 6728561 := bstep (se 2 (by rfl) ⟨2523210, by rfl⟩ : syracuseStep 6728561 = 5046421) B5046421
theorem B4485707 : Blo 1993435 4485707 := bstep (se 1 (by rfl) ⟨3364280, by rfl⟩ : syracuseStep 4485707 = 6728561) B6728561
theorem B2990471 : Blo 1993435 2990471 := bstep (se 1 (by rfl) ⟨2242853, by rfl⟩ : syracuseStep 2990471 = 4485707) B4485707
theorem B1993647 : Blo 1993435 1993647 := bstep (se 1 (by rfl) ⟨1495235, by rfl⟩ : syracuseStep 1993647 = 2990471) B2990471
theorem B2990477 : Blo 1993435 2990477 := bbase (se 3 (by rfl) ⟨560714, by rfl⟩ : syracuseStep 2990477 = 1121429) (by norm_num)
theorem B1993651 : Blo 1993435 1993651 := bstep (se 1 (by rfl) ⟨1495238, by rfl⟩ : syracuseStep 1993651 = 2990477) B2990477
theorem B4485725 : Blo 1993435 4485725 := bbase (se 3 (by rfl) ⟨841073, by rfl⟩ : syracuseStep 4485725 = 1682147) (by norm_num)
theorem B2990483 : Blo 1993435 2990483 := bstep (se 1 (by rfl) ⟨2242862, by rfl⟩ : syracuseStep 2990483 = 4485725) B4485725
theorem B1993655 : Blo 1993435 1993655 := bstep (se 1 (by rfl) ⟨1495241, by rfl⟩ : syracuseStep 1993655 = 2990483) B2990483
theorem B3364301 : Blo 1993435 3364301 := bbase (se 3 (by rfl) ⟨630806, by rfl⟩ : syracuseStep 3364301 = 1261613) (by norm_num)
theorem B2242867 : Blo 1993435 2242867 := bstep (se 1 (by rfl) ⟨1682150, by rfl⟩ : syracuseStep 2242867 = 3364301) B3364301
theorem B2990489 : Blo 1993435 2990489 := bstep (se 2 (by rfl) ⟨1121433, by rfl⟩ : syracuseStep 2990489 = 2242867) B2242867
theorem B1993659 : Blo 1993435 1993659 := bstep (se 1 (by rfl) ⟨1495244, by rfl⟩ : syracuseStep 1993659 = 2990489) B2990489
theorem B2557657 : Blo 1993435 2557657 := bbase (se 2 (by rfl) ⟨959121, by rfl⟩ : syracuseStep 2557657 = 1918243) (by norm_num)
theorem B3410209 : Blo 1993435 3410209 := bstep (se 2 (by rfl) ⟨1278828, by rfl⟩ : syracuseStep 3410209 = 2557657) B2557657
theorem B4546945 : Blo 1993435 4546945 := bstep (se 2 (by rfl) ⟨1705104, by rfl⟩ : syracuseStep 4546945 = 3410209) B3410209
theorem B24250373 : Blo 1993435 24250373 := bstep (se 4 (by rfl) ⟨2273472, by rfl⟩ : syracuseStep 24250373 = 4546945) B4546945
theorem B16166915 : Blo 1993435 16166915 := bstep (se 1 (by rfl) ⟨12125186, by rfl⟩ : syracuseStep 16166915 = 24250373) B24250373
theorem B10777943 : Blo 1993435 10777943 := bstep (se 1 (by rfl) ⟨8083457, by rfl⟩ : syracuseStep 10777943 = 16166915) B16166915
theorem B7185295 : Blo 1993435 7185295 := bstep (se 1 (by rfl) ⟨5388971, by rfl⟩ : syracuseStep 7185295 = 10777943) B10777943
theorem B9580393 : Blo 1993435 9580393 := bstep (se 2 (by rfl) ⟨3592647, by rfl⟩ : syracuseStep 9580393 = 7185295) B7185295
theorem B12773857 : Blo 1993435 12773857 := bstep (se 2 (by rfl) ⟨4790196, by rfl⟩ : syracuseStep 12773857 = 9580393) B9580393
theorem B17031809 : Blo 1993435 17031809 := bstep (se 2 (by rfl) ⟨6386928, by rfl⟩ : syracuseStep 17031809 = 12773857) B12773857
theorem B11354539 : Blo 1993435 11354539 := bstep (se 1 (by rfl) ⟨8515904, by rfl⟩ : syracuseStep 11354539 = 17031809) B17031809
theorem B15139385 : Blo 1993435 15139385 := bstep (se 2 (by rfl) ⟨5677269, by rfl⟩ : syracuseStep 15139385 = 11354539) B11354539
theorem B10092923 : Blo 1993435 10092923 := bstep (se 1 (by rfl) ⟨7569692, by rfl⟩ : syracuseStep 10092923 = 15139385) B15139385
theorem B6728615 : Blo 1993435 6728615 := bstep (se 1 (by rfl) ⟨5046461, by rfl⟩ : syracuseStep 6728615 = 10092923) B10092923
theorem B4485743 : Blo 1993435 4485743 := bstep (se 1 (by rfl) ⟨3364307, by rfl⟩ : syracuseStep 4485743 = 6728615) B6728615
theorem B2990495 : Blo 1993435 2990495 := bstep (se 1 (by rfl) ⟨2242871, by rfl⟩ : syracuseStep 2990495 = 4485743) B4485743
theorem B1993663 : Blo 1993435 1993663 := bstep (se 1 (by rfl) ⟨1495247, by rfl⟩ : syracuseStep 1993663 = 2990495) B2990495
theorem B2990501 : Blo 1993435 2990501 := bbase (se 4 (by rfl) ⟨280359, by rfl⟩ : syracuseStep 2990501 = 560719) (by norm_num)
theorem B1993667 : Blo 1993435 1993667 := bstep (se 1 (by rfl) ⟨1495250, by rfl⟩ : syracuseStep 1993667 = 2990501) B2990501
theorem B2523241 : Blo 1993435 2523241 := bbase (se 2 (by rfl) ⟨946215, by rfl⟩ : syracuseStep 2523241 = 1892431) (by norm_num)
theorem B3364321 : Blo 1993435 3364321 := bstep (se 2 (by rfl) ⟨1261620, by rfl⟩ : syracuseStep 3364321 = 2523241) B2523241
theorem B4485761 : Blo 1993435 4485761 := bstep (se 2 (by rfl) ⟨1682160, by rfl⟩ : syracuseStep 4485761 = 3364321) B3364321
theorem B2990507 : Blo 1993435 2990507 := bstep (se 1 (by rfl) ⟨2242880, by rfl⟩ : syracuseStep 2990507 = 4485761) B4485761
theorem B1993671 : Blo 1993435 1993671 := bstep (se 1 (by rfl) ⟨1495253, by rfl⟩ : syracuseStep 1993671 = 2990507) B2990507
theorem B2242885 : Blo 1993435 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B2990513 : Blo 1993435 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B1993675 : Blo 1993435 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B3784877 : Blo 1993435 3784877 := bbase (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) (by norm_num)
theorem B2523251 : Blo 1993435 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B6728669 : Blo 1993435 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B4485779 : Blo 1993435 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B2990519 : Blo 1993435 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B1993679 : Blo 1993435 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B2990525 : Blo 1993435 2990525 := bbase (se 3 (by rfl) ⟨560723, by rfl⟩ : syracuseStep 2990525 = 1121447) (by norm_num)
theorem B1993683 : Blo 1993435 1993683 := bstep (se 1 (by rfl) ⟨1495262, by rfl⟩ : syracuseStep 1993683 = 2990525) B2990525
theorem B4485797 : Blo 1993435 4485797 := bbase (se 4 (by rfl) ⟨420543, by rfl⟩ : syracuseStep 4485797 = 841087) (by norm_num)
theorem B2990531 : Blo 1993435 2990531 := bstep (se 1 (by rfl) ⟨2242898, by rfl⟩ : syracuseStep 2990531 = 4485797) B4485797
theorem B1993687 : Blo 1993435 1993687 := bstep (se 1 (by rfl) ⟨1495265, by rfl⟩ : syracuseStep 1993687 = 2990531) B2990531
theorem B5046533 : Blo 1993435 5046533 := bbase (se 4 (by rfl) ⟨473112, by rfl⟩ : syracuseStep 5046533 = 946225) (by norm_num)
theorem B3364355 : Blo 1993435 3364355 := bstep (se 1 (by rfl) ⟨2523266, by rfl⟩ : syracuseStep 3364355 = 5046533) B5046533
theorem B2242903 : Blo 1993435 2242903 := bstep (se 1 (by rfl) ⟨1682177, by rfl⟩ : syracuseStep 2242903 = 3364355) B3364355
theorem B2990537 : Blo 1993435 2990537 := bstep (se 2 (by rfl) ⟨1121451, by rfl⟩ : syracuseStep 2990537 = 2242903) B2242903
theorem B1993691 : Blo 1993435 1993691 := bstep (se 1 (by rfl) ⟨1495268, by rfl⟩ : syracuseStep 1993691 = 2990537) B2990537
theorem B4258021 : Blo 1993435 4258021 := bbase (se 4 (by rfl) ⟨399189, by rfl⟩ : syracuseStep 4258021 = 798379) (by norm_num)
theorem B5677361 : Blo 1993435 5677361 := bstep (se 2 (by rfl) ⟨2129010, by rfl⟩ : syracuseStep 5677361 = 4258021) B4258021
theorem B3784907 : Blo 1993435 3784907 := bstep (se 1 (by rfl) ⟨2838680, by rfl⟩ : syracuseStep 3784907 = 5677361) B5677361
theorem B10093085 : Blo 1993435 10093085 := bstep (se 3 (by rfl) ⟨1892453, by rfl⟩ : syracuseStep 10093085 = 3784907) B3784907
theorem B6728723 : Blo 1993435 6728723 := bstep (se 1 (by rfl) ⟨5046542, by rfl⟩ : syracuseStep 6728723 = 10093085) B10093085
theorem B4485815 : Blo 1993435 4485815 := bstep (se 1 (by rfl) ⟨3364361, by rfl⟩ : syracuseStep 4485815 = 6728723) B6728723
theorem B2990543 : Blo 1993435 2990543 := bstep (se 1 (by rfl) ⟨2242907, by rfl⟩ : syracuseStep 2990543 = 4485815) B4485815
theorem B1993695 : Blo 1993435 1993695 := bstep (se 1 (by rfl) ⟨1495271, by rfl⟩ : syracuseStep 1993695 = 2990543) B2990543
theorem B2990549 : Blo 1993435 2990549 := bbase (se 7 (by rfl) ⟨35045, by rfl⟩ : syracuseStep 2990549 = 70091) (by norm_num)
theorem B1993699 : Blo 1993435 1993699 := bstep (se 1 (by rfl) ⟨1495274, by rfl⟩ : syracuseStep 1993699 = 2990549) B2990549
theorem B7569845 : Blo 1993435 7569845 := bbase (se 5 (by rfl) ⟨354836, by rfl⟩ : syracuseStep 7569845 = 709673) (by norm_num)
theorem B5046563 : Blo 1993435 5046563 := bstep (se 1 (by rfl) ⟨3784922, by rfl⟩ : syracuseStep 5046563 = 7569845) B7569845
theorem B3364375 : Blo 1993435 3364375 := bstep (se 1 (by rfl) ⟨2523281, by rfl⟩ : syracuseStep 3364375 = 5046563) B5046563
theorem B4485833 : Blo 1993435 4485833 := bstep (se 2 (by rfl) ⟨1682187, by rfl⟩ : syracuseStep 4485833 = 3364375) B3364375
theorem B2990555 : Blo 1993435 2990555 := bstep (se 1 (by rfl) ⟨2242916, by rfl⟩ : syracuseStep 2990555 = 4485833) B4485833
theorem B1993703 : Blo 1993435 1993703 := bstep (se 1 (by rfl) ⟨1495277, by rfl⟩ : syracuseStep 1993703 = 2990555) B2990555
theorem B2242921 : Blo 1993435 2242921 := bbase (se 2 (by rfl) ⟨841095, by rfl⟩ : syracuseStep 2242921 = 1682191) (by norm_num)
theorem B2990561 : Blo 1993435 2990561 := bstep (se 2 (by rfl) ⟨1121460, by rfl⟩ : syracuseStep 2990561 = 2242921) B2242921
theorem B1993707 : Blo 1993435 1993707 := bstep (se 1 (by rfl) ⟨1495280, by rfl⟩ : syracuseStep 1993707 = 2990561) B2990561
theorem B6062741 : Blo 1993435 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B4041827 : Blo 1993435 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B2694551 : Blo 1993435 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B7185469 : Blo 1993435 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B9580625 : Blo 1993435 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B6387083 : Blo 1993435 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B4258055 : Blo 1993435 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B11354813 : Blo 1993435 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B7569875 : Blo 1993435 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B5046583 : Blo 1993435 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B6728777 : Blo 1993435 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B4485851 : Blo 1993435 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B2990567 : Blo 1993435 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B1993711 : Blo 1993435 1993711 := bstep (se 1 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 1993711 = 2990567) B2990567
theorem B2990573 : Blo 1993435 2990573 := bbase (se 3 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 2990573 = 1121465) (by norm_num)
theorem B1993715 : Blo 1993435 1993715 := bstep (se 1 (by rfl) ⟨1495286, by rfl⟩ : syracuseStep 1993715 = 2990573) B2990573
theorem B4485869 : Blo 1993435 4485869 := bbase (se 3 (by rfl) ⟨841100, by rfl⟩ : syracuseStep 4485869 = 1682201) (by norm_num)
theorem B2990579 : Blo 1993435 2990579 := bstep (se 1 (by rfl) ⟨2242934, by rfl⟩ : syracuseStep 2990579 = 4485869) B4485869
theorem B1993719 : Blo 1993435 1993719 := bstep (se 1 (by rfl) ⟨1495289, by rfl⟩ : syracuseStep 1993719 = 2990579) B2990579
theorem B2129041 : Blo 1993435 2129041 := bbase (se 2 (by rfl) ⟨798390, by rfl⟩ : syracuseStep 2129041 = 1596781) (by norm_num)
theorem B2838721 : Blo 1993435 2838721 := bstep (se 2 (by rfl) ⟨1064520, by rfl⟩ : syracuseStep 2838721 = 2129041) B2129041
theorem B3784961 : Blo 1993435 3784961 := bstep (se 2 (by rfl) ⟨1419360, by rfl⟩ : syracuseStep 3784961 = 2838721) B2838721
theorem B2523307 : Blo 1993435 2523307 := bstep (se 1 (by rfl) ⟨1892480, by rfl⟩ : syracuseStep 2523307 = 3784961) B3784961
theorem B3364409 : Blo 1993435 3364409 := bstep (se 2 (by rfl) ⟨1261653, by rfl⟩ : syracuseStep 3364409 = 2523307) B2523307
theorem B2242939 : Blo 1993435 2242939 := bstep (se 1 (by rfl) ⟨1682204, by rfl⟩ : syracuseStep 2242939 = 3364409) B3364409
theorem B2990585 : Blo 1993435 2990585 := bstep (se 2 (by rfl) ⟨1121469, by rfl⟩ : syracuseStep 2990585 = 2242939) B2242939
theorem B1993723 : Blo 1993435 1993723 := bstep (se 1 (by rfl) ⟨1495292, by rfl⟩ : syracuseStep 1993723 = 2990585) B2990585
theorem B9711413 : Blo 1993435 9711413 := bbase (se 5 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 9711413 = 910445) (by norm_num)
theorem B6474275 : Blo 1993435 6474275 := bstep (se 1 (by rfl) ⟨4855706, by rfl⟩ : syracuseStep 6474275 = 9711413) B9711413
theorem B276235733 : Blo 1993435 276235733 := bstep (se 7 (by rfl) ⟨3237137, by rfl⟩ : syracuseStep 276235733 = 6474275) B6474275
theorem B184157155 : Blo 1993435 184157155 := bstep (se 1 (by rfl) ⟨138117866, by rfl⟩ : syracuseStep 184157155 = 276235733) B276235733
theorem B245542873 : Blo 1993435 245542873 := bstep (se 2 (by rfl) ⟨92078577, by rfl⟩ : syracuseStep 245542873 = 184157155) B184157155
theorem B327390497 : Blo 1993435 327390497 := bstep (se 2 (by rfl) ⟨122771436, by rfl⟩ : syracuseStep 327390497 = 245542873) B245542873
theorem B218260331 : Blo 1993435 218260331 := bstep (se 1 (by rfl) ⟨163695248, by rfl⟩ : syracuseStep 218260331 = 327390497) B327390497
theorem B145506887 : Blo 1993435 145506887 := bstep (se 1 (by rfl) ⟨109130165, by rfl⟩ : syracuseStep 145506887 = 218260331) B218260331
theorem B97004591 : Blo 1993435 97004591 := bstep (se 1 (by rfl) ⟨72753443, by rfl⟩ : syracuseStep 97004591 = 145506887) B145506887
theorem B64669727 : Blo 1993435 64669727 := bstep (se 1 (by rfl) ⟨48502295, by rfl⟩ : syracuseStep 64669727 = 97004591) B97004591
theorem B43113151 : Blo 1993435 43113151 := bstep (se 1 (by rfl) ⟨32334863, by rfl⟩ : syracuseStep 43113151 = 64669727) B64669727
theorem B57484201 : Blo 1993435 57484201 := bstep (se 2 (by rfl) ⟨21556575, by rfl⟩ : syracuseStep 57484201 = 43113151) B43113151
theorem B76645601 : Blo 1993435 76645601 := bstep (se 2 (by rfl) ⟨28742100, by rfl⟩ : syracuseStep 76645601 = 57484201) B57484201
theorem B51097067 : Blo 1993435 51097067 := bstep (se 1 (by rfl) ⟨38322800, by rfl⟩ : syracuseStep 51097067 = 76645601) B76645601
theorem B34064711 : Blo 1993435 34064711 := bstep (se 1 (by rfl) ⟨25548533, by rfl⟩ : syracuseStep 34064711 = 51097067) B51097067
theorem B22709807 : Blo 1993435 22709807 := bstep (se 1 (by rfl) ⟨17032355, by rfl⟩ : syracuseStep 22709807 = 34064711) B34064711
theorem B15139871 : Blo 1993435 15139871 := bstep (se 1 (by rfl) ⟨11354903, by rfl⟩ : syracuseStep 15139871 = 22709807) B22709807
theorem B10093247 : Blo 1993435 10093247 := bstep (se 1 (by rfl) ⟨7569935, by rfl⟩ : syracuseStep 10093247 = 15139871) B15139871
theorem B6728831 : Blo 1993435 6728831 := bstep (se 1 (by rfl) ⟨5046623, by rfl⟩ : syracuseStep 6728831 = 10093247) B10093247
theorem B4485887 : Blo 1993435 4485887 := bstep (se 1 (by rfl) ⟨3364415, by rfl⟩ : syracuseStep 4485887 = 6728831) B6728831
theorem B2990591 : Blo 1993435 2990591 := bstep (se 1 (by rfl) ⟨2242943, by rfl⟩ : syracuseStep 2990591 = 4485887) B4485887
theorem B1993727 : Blo 1993435 1993727 := bstep (se 1 (by rfl) ⟨1495295, by rfl⟩ : syracuseStep 1993727 = 2990591) B2990591
theorem B2990597 : Blo 1993435 2990597 := bbase (se 4 (by rfl) ⟨280368, by rfl⟩ : syracuseStep 2990597 = 560737) (by norm_num)
theorem B1993731 : Blo 1993435 1993731 := bstep (se 1 (by rfl) ⟨1495298, by rfl⟩ : syracuseStep 1993731 = 2990597) B2990597
theorem B3364429 : Blo 1993435 3364429 := bbase (se 3 (by rfl) ⟨630830, by rfl⟩ : syracuseStep 3364429 = 1261661) (by norm_num)
theorem B4485905 : Blo 1993435 4485905 := bstep (se 2 (by rfl) ⟨1682214, by rfl⟩ : syracuseStep 4485905 = 3364429) B3364429
theorem B2990603 : Blo 1993435 2990603 := bstep (se 1 (by rfl) ⟨2242952, by rfl⟩ : syracuseStep 2990603 = 4485905) B4485905
theorem B1993735 : Blo 1993435 1993735 := bstep (se 1 (by rfl) ⟨1495301, by rfl⟩ : syracuseStep 1993735 = 2990603) B2990603
theorem B2242957 : Blo 1993435 2242957 := bbase (se 3 (by rfl) ⟨420554, by rfl⟩ : syracuseStep 2242957 = 841109) (by norm_num)
theorem B2990609 : Blo 1993435 2990609 := bstep (se 2 (by rfl) ⟨1121478, by rfl⟩ : syracuseStep 2990609 = 2242957) B2242957
theorem B1993739 : Blo 1993435 1993739 := bstep (se 1 (by rfl) ⟨1495304, by rfl⟩ : syracuseStep 1993739 = 2990609) B2990609
theorem B6728885 : Blo 1993435 6728885 := bbase (se 5 (by rfl) ⟨315416, by rfl⟩ : syracuseStep 6728885 = 630833) (by norm_num)
theorem B4485923 : Blo 1993435 4485923 := bstep (se 1 (by rfl) ⟨3364442, by rfl⟩ : syracuseStep 4485923 = 6728885) B6728885
theorem B2990615 : Blo 1993435 2990615 := bstep (se 1 (by rfl) ⟨2242961, by rfl⟩ : syracuseStep 2990615 = 4485923) B4485923
theorem B1993743 : Blo 1993435 1993743 := bstep (se 1 (by rfl) ⟨1495307, by rfl⟩ : syracuseStep 1993743 = 2990615) B2990615
theorem B2990621 : Blo 1993435 2990621 := bbase (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) (by norm_num)
theorem B1993747 : Blo 1993435 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B4485941 : Blo 1993435 4485941 := bbase (se 5 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 4485941 = 420557) (by norm_num)
theorem B2990627 : Blo 1993435 2990627 := bstep (se 1 (by rfl) ⟨2242970, by rfl⟩ : syracuseStep 2990627 = 4485941) B4485941
theorem B1993751 : Blo 1993435 1993751 := bstep (se 1 (by rfl) ⟨1495313, by rfl⟩ : syracuseStep 1993751 = 2990627) B2990627
theorem B9580837 : Blo 1993435 9580837 := bbase (se 4 (by rfl) ⟨898203, by rfl⟩ : syracuseStep 9580837 = 1796407) (by norm_num)
theorem B12774449 : Blo 1993435 12774449 := bstep (se 2 (by rfl) ⟨4790418, by rfl⟩ : syracuseStep 12774449 = 9580837) B9580837
theorem B8516299 : Blo 1993435 8516299 := bstep (se 1 (by rfl) ⟨6387224, by rfl⟩ : syracuseStep 8516299 = 12774449) B12774449
theorem B11355065 : Blo 1993435 11355065 := bstep (se 2 (by rfl) ⟨4258149, by rfl⟩ : syracuseStep 11355065 = 8516299) B8516299
theorem B7570043 : Blo 1993435 7570043 := bstep (se 1 (by rfl) ⟨5677532, by rfl⟩ : syracuseStep 7570043 = 11355065) B11355065
theorem B5046695 : Blo 1993435 5046695 := bstep (se 1 (by rfl) ⟨3785021, by rfl⟩ : syracuseStep 5046695 = 7570043) B7570043
theorem B3364463 : Blo 1993435 3364463 := bstep (se 1 (by rfl) ⟨2523347, by rfl⟩ : syracuseStep 3364463 = 5046695) B5046695
theorem B2242975 : Blo 1993435 2242975 := bstep (se 1 (by rfl) ⟨1682231, by rfl⟩ : syracuseStep 2242975 = 3364463) B3364463
theorem B2990633 : Blo 1993435 2990633 := bstep (se 2 (by rfl) ⟨1121487, by rfl⟩ : syracuseStep 2990633 = 2242975) B2242975
theorem B1993755 : Blo 1993435 1993755 := bstep (se 1 (by rfl) ⟨1495316, by rfl⟩ : syracuseStep 1993755 = 2990633) B2990633
theorem B13641493 : Blo 1993435 13641493 := bbase (se 6 (by rfl) ⟨319722, by rfl⟩ : syracuseStep 13641493 = 639445) (by norm_num)
theorem B18188657 : Blo 1993435 18188657 := bstep (se 2 (by rfl) ⟨6820746, by rfl⟩ : syracuseStep 18188657 = 13641493) B13641493
theorem B12125771 : Blo 1993435 12125771 := bstep (se 1 (by rfl) ⟨9094328, by rfl⟩ : syracuseStep 12125771 = 18188657) B18188657
theorem B8083847 : Blo 1993435 8083847 := bstep (se 1 (by rfl) ⟨6062885, by rfl⟩ : syracuseStep 8083847 = 12125771) B12125771
theorem B21556925 : Blo 1993435 21556925 := bstep (se 3 (by rfl) ⟨4041923, by rfl⟩ : syracuseStep 21556925 = 8083847) B8083847
theorem B14371283 : Blo 1993435 14371283 := bstep (se 1 (by rfl) ⟨10778462, by rfl⟩ : syracuseStep 14371283 = 21556925) B21556925
theorem B9580855 : Blo 1993435 9580855 := bstep (se 1 (by rfl) ⟨7185641, by rfl⟩ : syracuseStep 9580855 = 14371283) B14371283
theorem B12774473 : Blo 1993435 12774473 := bstep (se 2 (by rfl) ⟨4790427, by rfl⟩ : syracuseStep 12774473 = 9580855) B9580855
theorem B8516315 : Blo 1993435 8516315 := bstep (se 1 (by rfl) ⟨6387236, by rfl⟩ : syracuseStep 8516315 = 12774473) B12774473
theorem B5677543 : Blo 1993435 5677543 := bstep (se 1 (by rfl) ⟨4258157, by rfl⟩ : syracuseStep 5677543 = 8516315) B8516315
theorem B7570057 : Blo 1993435 7570057 := bstep (se 2 (by rfl) ⟨2838771, by rfl⟩ : syracuseStep 7570057 = 5677543) B5677543
theorem B10093409 : Blo 1993435 10093409 := bstep (se 2 (by rfl) ⟨3785028, by rfl⟩ : syracuseStep 10093409 = 7570057) B7570057
theorem B6728939 : Blo 1993435 6728939 := bstep (se 1 (by rfl) ⟨5046704, by rfl⟩ : syracuseStep 6728939 = 10093409) B10093409
theorem B4485959 : Blo 1993435 4485959 := bstep (se 1 (by rfl) ⟨3364469, by rfl⟩ : syracuseStep 4485959 = 6728939) B6728939
theorem B2990639 : Blo 1993435 2990639 := bstep (se 1 (by rfl) ⟨2242979, by rfl⟩ : syracuseStep 2990639 = 4485959) B4485959
theorem B1993759 : Blo 1993435 1993759 := bstep (se 1 (by rfl) ⟨1495319, by rfl⟩ : syracuseStep 1993759 = 2990639) B2990639
theorem B2990645 : Blo 1993435 2990645 := bbase (se 5 (by rfl) ⟨140186, by rfl⟩ : syracuseStep 2990645 = 280373) (by norm_num)
theorem B1993763 : Blo 1993435 1993763 := bstep (se 1 (by rfl) ⟨1495322, by rfl⟩ : syracuseStep 1993763 = 2990645) B2990645
theorem B5046725 : Blo 1993435 5046725 := bbase (se 4 (by rfl) ⟨473130, by rfl⟩ : syracuseStep 5046725 = 946261) (by norm_num)
theorem B3364483 : Blo 1993435 3364483 := bstep (se 1 (by rfl) ⟨2523362, by rfl⟩ : syracuseStep 3364483 = 5046725) B5046725
theorem B4485977 : Blo 1993435 4485977 := bstep (se 2 (by rfl) ⟨1682241, by rfl⟩ : syracuseStep 4485977 = 3364483) B3364483
theorem B2990651 : Blo 1993435 2990651 := bstep (se 1 (by rfl) ⟨2242988, by rfl⟩ : syracuseStep 2990651 = 4485977) B4485977
theorem B1993767 : Blo 1993435 1993767 := bstep (se 1 (by rfl) ⟨1495325, by rfl⟩ : syracuseStep 1993767 = 2990651) B2990651
theorem B2242993 : Blo 1993435 2242993 := bbase (se 2 (by rfl) ⟨841122, by rfl⟩ : syracuseStep 2242993 = 1682245) (by norm_num)
theorem B2990657 : Blo 1993435 2990657 := bstep (se 2 (by rfl) ⟨1121496, by rfl⟩ : syracuseStep 2990657 = 2242993) B2242993
theorem B1993771 : Blo 1993435 1993771 := bstep (se 1 (by rfl) ⟨1495328, by rfl⟩ : syracuseStep 1993771 = 2990657) B2990657
theorem B5677589 : Blo 1993435 5677589 := bbase (se 6 (by rfl) ⟨133068, by rfl⟩ : syracuseStep 5677589 = 266137) (by norm_num)
theorem B3785059 : Blo 1993435 3785059 := bstep (se 1 (by rfl) ⟨2838794, by rfl⟩ : syracuseStep 3785059 = 5677589) B5677589
theorem B5046745 : Blo 1993435 5046745 := bstep (se 2 (by rfl) ⟨1892529, by rfl⟩ : syracuseStep 5046745 = 3785059) B3785059
theorem B6728993 : Blo 1993435 6728993 := bstep (se 2 (by rfl) ⟨2523372, by rfl⟩ : syracuseStep 6728993 = 5046745) B5046745
theorem B4485995 : Blo 1993435 4485995 := bstep (se 1 (by rfl) ⟨3364496, by rfl⟩ : syracuseStep 4485995 = 6728993) B6728993
theorem B2990663 : Blo 1993435 2990663 := bstep (se 1 (by rfl) ⟨2242997, by rfl⟩ : syracuseStep 2990663 = 4485995) B4485995
theorem B1993775 : Blo 1993435 1993775 := bstep (se 1 (by rfl) ⟨1495331, by rfl⟩ : syracuseStep 1993775 = 2990663) B2990663
theorem B2990669 : Blo 1993435 2990669 := bbase (se 3 (by rfl) ⟨560750, by rfl⟩ : syracuseStep 2990669 = 1121501) (by norm_num)
theorem B1993779 : Blo 1993435 1993779 := bstep (se 1 (by rfl) ⟨1495334, by rfl⟩ : syracuseStep 1993779 = 2990669) B2990669
theorem B4486013 : Blo 1993435 4486013 := bbase (se 3 (by rfl) ⟨841127, by rfl⟩ : syracuseStep 4486013 = 1682255) (by norm_num)
theorem B2990675 : Blo 1993435 2990675 := bstep (se 1 (by rfl) ⟨2243006, by rfl⟩ : syracuseStep 2990675 = 4486013) B4486013
theorem B1993783 : Blo 1993435 1993783 := bstep (se 1 (by rfl) ⟨1495337, by rfl⟩ : syracuseStep 1993783 = 2990675) B2990675
theorem B3364517 : Blo 1993435 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B2243011 : Blo 1993435 2243011 := bstep (se 1 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 2243011 = 3364517) B3364517
theorem B2990681 : Blo 1993435 2990681 := bstep (se 2 (by rfl) ⟨1121505, by rfl⟩ : syracuseStep 2990681 = 2243011) B2243011
theorem B1993787 : Blo 1993435 1993787 := bstep (se 1 (by rfl) ⟨1495340, by rfl⟩ : syracuseStep 1993787 = 2990681) B2990681
theorem B2129113 : Blo 1993435 2129113 := bbase (se 2 (by rfl) ⟨798417, by rfl⟩ : syracuseStep 2129113 = 1596835) (by norm_num)
theorem B2838817 : Blo 1993435 2838817 := bstep (se 2 (by rfl) ⟨1064556, by rfl⟩ : syracuseStep 2838817 = 2129113) B2129113
theorem B15140357 : Blo 1993435 15140357 := bstep (se 4 (by rfl) ⟨1419408, by rfl⟩ : syracuseStep 15140357 = 2838817) B2838817
theorem B10093571 : Blo 1993435 10093571 := bstep (se 1 (by rfl) ⟨7570178, by rfl⟩ : syracuseStep 10093571 = 15140357) B15140357
theorem B6729047 : Blo 1993435 6729047 := bstep (se 1 (by rfl) ⟨5046785, by rfl⟩ : syracuseStep 6729047 = 10093571) B10093571
theorem B4486031 : Blo 1993435 4486031 := bstep (se 1 (by rfl) ⟨3364523, by rfl⟩ : syracuseStep 4486031 = 6729047) B6729047
theorem B2990687 : Blo 1993435 2990687 := bstep (se 1 (by rfl) ⟨2243015, by rfl⟩ : syracuseStep 2990687 = 4486031) B4486031
theorem B1993791 : Blo 1993435 1993791 := bstep (se 1 (by rfl) ⟨1495343, by rfl⟩ : syracuseStep 1993791 = 2990687) B2990687
theorem B2990693 : Blo 1993435 2990693 := bbase (se 4 (by rfl) ⟨280377, by rfl⟩ : syracuseStep 2990693 = 560755) (by norm_num)
theorem B1993795 : Blo 1993435 1993795 := bstep (se 1 (by rfl) ⟨1495346, by rfl⟩ : syracuseStep 1993795 = 2990693) B2990693
theorem B2838829 : Blo 1993435 2838829 := bbase (se 3 (by rfl) ⟨532280, by rfl⟩ : syracuseStep 2838829 = 1064561) (by norm_num)
theorem B3785105 : Blo 1993435 3785105 := bstep (se 2 (by rfl) ⟨1419414, by rfl⟩ : syracuseStep 3785105 = 2838829) B2838829
theorem B2523403 : Blo 1993435 2523403 := bstep (se 1 (by rfl) ⟨1892552, by rfl⟩ : syracuseStep 2523403 = 3785105) B3785105
theorem B3364537 : Blo 1993435 3364537 := bstep (se 2 (by rfl) ⟨1261701, by rfl⟩ : syracuseStep 3364537 = 2523403) B2523403
theorem B4486049 : Blo 1993435 4486049 := bstep (se 2 (by rfl) ⟨1682268, by rfl⟩ : syracuseStep 4486049 = 3364537) B3364537
theorem B2990699 : Blo 1993435 2990699 := bstep (se 1 (by rfl) ⟨2243024, by rfl⟩ : syracuseStep 2990699 = 4486049) B4486049
theorem B1993799 : Blo 1993435 1993799 := bstep (se 1 (by rfl) ⟨1495349, by rfl⟩ : syracuseStep 1993799 = 2990699) B2990699
theorem B2243029 : Blo 1993435 2243029 := bbase (se 7 (by rfl) ⟨26285, by rfl⟩ : syracuseStep 2243029 = 52571) (by norm_num)
theorem B2990705 : Blo 1993435 2990705 := bstep (se 2 (by rfl) ⟨1121514, by rfl⟩ : syracuseStep 2990705 = 2243029) B2243029
theorem B1993803 : Blo 1993435 1993803 := bstep (se 1 (by rfl) ⟨1495352, by rfl⟩ : syracuseStep 1993803 = 2990705) B2990705
theorem B2523413 : Blo 1993435 2523413 := bbase (se 6 (by rfl) ⟨59142, by rfl⟩ : syracuseStep 2523413 = 118285) (by norm_num)
theorem B6729101 : Blo 1993435 6729101 := bstep (se 3 (by rfl) ⟨1261706, by rfl⟩ : syracuseStep 6729101 = 2523413) B2523413
theorem B4486067 : Blo 1993435 4486067 := bstep (se 1 (by rfl) ⟨3364550, by rfl⟩ : syracuseStep 4486067 = 6729101) B6729101
theorem B2990711 : Blo 1993435 2990711 := bstep (se 1 (by rfl) ⟨2243033, by rfl⟩ : syracuseStep 2990711 = 4486067) B4486067
theorem B1993807 : Blo 1993435 1993807 := bstep (se 1 (by rfl) ⟨1495355, by rfl⟩ : syracuseStep 1993807 = 2990711) B2990711
theorem B2990717 : Blo 1993435 2990717 := bbase (se 3 (by rfl) ⟨560759, by rfl⟩ : syracuseStep 2990717 = 1121519) (by norm_num)
theorem B1993811 : Blo 1993435 1993811 := bstep (se 1 (by rfl) ⟨1495358, by rfl⟩ : syracuseStep 1993811 = 2990717) B2990717
theorem B4486085 : Blo 1993435 4486085 := bbase (se 4 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 4486085 = 841141) (by norm_num)
theorem B2990723 : Blo 1993435 2990723 := bstep (se 1 (by rfl) ⟨2243042, by rfl⟩ : syracuseStep 2990723 = 4486085) B4486085
theorem B1993815 : Blo 1993435 1993815 := bstep (se 1 (by rfl) ⟨1495361, by rfl⟩ : syracuseStep 1993815 = 2990723) B2990723
theorem B4790573 : Blo 1993435 4790573 := bbase (se 3 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 4790573 = 1796465) (by norm_num)
theorem B3193715 : Blo 1993435 3193715 := bstep (se 1 (by rfl) ⟨2395286, by rfl⟩ : syracuseStep 3193715 = 4790573) B4790573
theorem B8516573 : Blo 1993435 8516573 := bstep (se 3 (by rfl) ⟨1596857, by rfl⟩ : syracuseStep 8516573 = 3193715) B3193715
theorem B5677715 : Blo 1993435 5677715 := bstep (se 1 (by rfl) ⟨4258286, by rfl⟩ : syracuseStep 5677715 = 8516573) B8516573
theorem B3785143 : Blo 1993435 3785143 := bstep (se 1 (by rfl) ⟨2838857, by rfl⟩ : syracuseStep 3785143 = 5677715) B5677715
theorem B5046857 : Blo 1993435 5046857 := bstep (se 2 (by rfl) ⟨1892571, by rfl⟩ : syracuseStep 5046857 = 3785143) B3785143
theorem B3364571 : Blo 1993435 3364571 := bstep (se 1 (by rfl) ⟨2523428, by rfl⟩ : syracuseStep 3364571 = 5046857) B5046857
theorem B2243047 : Blo 1993435 2243047 := bstep (se 1 (by rfl) ⟨1682285, by rfl⟩ : syracuseStep 2243047 = 3364571) B3364571
theorem B2990729 : Blo 1993435 2990729 := bstep (se 2 (by rfl) ⟨1121523, by rfl⟩ : syracuseStep 2990729 = 2243047) B2243047
theorem B1993819 : Blo 1993435 1993819 := bstep (se 1 (by rfl) ⟨1495364, by rfl⟩ : syracuseStep 1993819 = 2990729) B2990729
theorem B10093733 : Blo 1993435 10093733 := bbase (se 4 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 10093733 = 1892575) (by norm_num)
theorem B6729155 : Blo 1993435 6729155 := bstep (se 1 (by rfl) ⟨5046866, by rfl⟩ : syracuseStep 6729155 = 10093733) B10093733
theorem B4486103 : Blo 1993435 4486103 := bstep (se 1 (by rfl) ⟨3364577, by rfl⟩ : syracuseStep 4486103 = 6729155) B6729155
theorem B2990735 : Blo 1993435 2990735 := bstep (se 1 (by rfl) ⟨2243051, by rfl⟩ : syracuseStep 2990735 = 4486103) B4486103
theorem B1993823 : Blo 1993435 1993823 := bstep (se 1 (by rfl) ⟨1495367, by rfl⟩ : syracuseStep 1993823 = 2990735) B2990735
theorem B2990741 : Blo 1993435 2990741 := bbase (se 6 (by rfl) ⟨70095, by rfl⟩ : syracuseStep 2990741 = 140191) (by norm_num)
theorem B1993827 : Blo 1993435 1993827 := bstep (se 1 (by rfl) ⟨1495370, by rfl⟩ : syracuseStep 1993827 = 2990741) B2990741
theorem B2273665 : Blo 1993435 2273665 := bbase (se 2 (by rfl) ⟨852624, by rfl⟩ : syracuseStep 2273665 = 1705249) (by norm_num)
theorem B3031553 : Blo 1993435 3031553 := bstep (se 2 (by rfl) ⟨1136832, by rfl⟩ : syracuseStep 3031553 = 2273665) B2273665
theorem B2021035 : Blo 1993435 2021035 := bstep (se 1 (by rfl) ⟨1515776, by rfl⟩ : syracuseStep 2021035 = 3031553) B3031553
theorem B2694713 : Blo 1993435 2694713 := bstep (se 2 (by rfl) ⟨1010517, by rfl⟩ : syracuseStep 2694713 = 2021035) B2021035
theorem B28743605 : Blo 1993435 28743605 := bstep (se 5 (by rfl) ⟨1347356, by rfl⟩ : syracuseStep 28743605 = 2694713) B2694713
theorem B19162403 : Blo 1993435 19162403 := bstep (se 1 (by rfl) ⟨14371802, by rfl⟩ : syracuseStep 19162403 = 28743605) B28743605
theorem B12774935 : Blo 1993435 12774935 := bstep (se 1 (by rfl) ⟨9581201, by rfl⟩ : syracuseStep 12774935 = 19162403) B19162403
theorem B8516623 : Blo 1993435 8516623 := bstep (se 1 (by rfl) ⟨6387467, by rfl⟩ : syracuseStep 8516623 = 12774935) B12774935
theorem B11355497 : Blo 1993435 11355497 := bstep (se 2 (by rfl) ⟨4258311, by rfl⟩ : syracuseStep 11355497 = 8516623) B8516623
theorem B7570331 : Blo 1993435 7570331 := bstep (se 1 (by rfl) ⟨5677748, by rfl⟩ : syracuseStep 7570331 = 11355497) B11355497
theorem B5046887 : Blo 1993435 5046887 := bstep (se 1 (by rfl) ⟨3785165, by rfl⟩ : syracuseStep 5046887 = 7570331) B7570331
theorem B3364591 : Blo 1993435 3364591 := bstep (se 1 (by rfl) ⟨2523443, by rfl⟩ : syracuseStep 3364591 = 5046887) B5046887
theorem B4486121 : Blo 1993435 4486121 := bstep (se 2 (by rfl) ⟨1682295, by rfl⟩ : syracuseStep 4486121 = 3364591) B3364591
theorem B2990747 : Blo 1993435 2990747 := bstep (se 1 (by rfl) ⟨2243060, by rfl⟩ : syracuseStep 2990747 = 4486121) B4486121
theorem B1993831 : Blo 1993435 1993831 := bstep (se 1 (by rfl) ⟨1495373, by rfl⟩ : syracuseStep 1993831 = 2990747) B2990747
theorem B2243065 : Blo 1993435 2243065 := bbase (se 2 (by rfl) ⟨841149, by rfl⟩ : syracuseStep 2243065 = 1682299) (by norm_num)
theorem B2990753 : Blo 1993435 2990753 := bstep (se 2 (by rfl) ⟨1121532, by rfl⟩ : syracuseStep 2990753 = 2243065) B2243065
theorem B1993835 : Blo 1993435 1993835 := bstep (se 1 (by rfl) ⟨1495376, by rfl⟩ : syracuseStep 1993835 = 2990753) B2990753
theorem B6387493 : Blo 1993435 6387493 := bbase (se 4 (by rfl) ⟨598827, by rfl⟩ : syracuseStep 6387493 = 1197655) (by norm_num)
theorem B8516657 : Blo 1993435 8516657 := bstep (se 2 (by rfl) ⟨3193746, by rfl⟩ : syracuseStep 8516657 = 6387493) B6387493
theorem B5677771 : Blo 1993435 5677771 := bstep (se 1 (by rfl) ⟨4258328, by rfl⟩ : syracuseStep 5677771 = 8516657) B8516657
theorem B7570361 : Blo 1993435 7570361 := bstep (se 2 (by rfl) ⟨2838885, by rfl⟩ : syracuseStep 7570361 = 5677771) B5677771
theorem B5046907 : Blo 1993435 5046907 := bstep (se 1 (by rfl) ⟨3785180, by rfl⟩ : syracuseStep 5046907 = 7570361) B7570361
theorem B6729209 : Blo 1993435 6729209 := bstep (se 2 (by rfl) ⟨2523453, by rfl⟩ : syracuseStep 6729209 = 5046907) B5046907
theorem B4486139 : Blo 1993435 4486139 := bstep (se 1 (by rfl) ⟨3364604, by rfl⟩ : syracuseStep 4486139 = 6729209) B6729209
theorem B2990759 : Blo 1993435 2990759 := bstep (se 1 (by rfl) ⟨2243069, by rfl⟩ : syracuseStep 2990759 = 4486139) B4486139
theorem B1993839 : Blo 1993435 1993839 := bstep (se 1 (by rfl) ⟨1495379, by rfl⟩ : syracuseStep 1993839 = 2990759) B2990759
theorem B2990765 : Blo 1993435 2990765 := bbase (se 3 (by rfl) ⟨560768, by rfl⟩ : syracuseStep 2990765 = 1121537) (by norm_num)
theorem B1993843 : Blo 1993435 1993843 := bstep (se 1 (by rfl) ⟨1495382, by rfl⟩ : syracuseStep 1993843 = 2990765) B2990765
theorem B4486157 : Blo 1993435 4486157 := bbase (se 3 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 4486157 = 1682309) (by norm_num)
theorem B2990771 : Blo 1993435 2990771 := bstep (se 1 (by rfl) ⟨2243078, by rfl⟩ : syracuseStep 2990771 = 4486157) B4486157
theorem B1993847 : Blo 1993435 1993847 := bstep (se 1 (by rfl) ⟨1495385, by rfl⟩ : syracuseStep 1993847 = 2990771) B2990771
theorem B2523469 : Blo 1993435 2523469 := bbase (se 3 (by rfl) ⟨473150, by rfl⟩ : syracuseStep 2523469 = 946301) (by norm_num)
theorem B3364625 : Blo 1993435 3364625 := bstep (se 2 (by rfl) ⟨1261734, by rfl⟩ : syracuseStep 3364625 = 2523469) B2523469
theorem B2243083 : Blo 1993435 2243083 := bstep (se 1 (by rfl) ⟨1682312, by rfl⟩ : syracuseStep 2243083 = 3364625) B3364625
theorem B2990777 : Blo 1993435 2990777 := bstep (se 2 (by rfl) ⟨1121541, by rfl⟩ : syracuseStep 2990777 = 2243083) B2243083
theorem B1993851 : Blo 1993435 1993851 := bstep (se 1 (by rfl) ⟨1495388, by rfl⟩ : syracuseStep 1993851 = 2990777) B2990777
theorem B4856021 : Blo 1993435 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3237347 : Blo 1993435 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B8632925 : Blo 1993435 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B5755283 : Blo 1993435 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B3836855 : Blo 1993435 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B2557903 : Blo 1993435 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B3410537 : Blo 1993435 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B9094765 : Blo 1993435 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B12126353 : Blo 1993435 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B32336941 : Blo 1993435 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B43115921 : Blo 1993435 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B28743947 : Blo 1993435 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B19162631 : Blo 1993435 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B12775087 : Blo 1993435 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B17033449 : Blo 1993435 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B22711265 : Blo 1993435 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B15140843 : Blo 1993435 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B10093895 : Blo 1993435 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B6729263 : Blo 1993435 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B4486175 : Blo 1993435 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B2990783 : Blo 1993435 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B1993855 : Blo 1993435 1993855 := bstep (se 1 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 1993855 = 2990783) B2990783
theorem B2990789 : Blo 1993435 2990789 := bbase (se 4 (by rfl) ⟨280386, by rfl⟩ : syracuseStep 2990789 = 560773) (by norm_num)
theorem B1993859 : Blo 1993435 1993859 := bstep (se 1 (by rfl) ⟨1495394, by rfl⟩ : syracuseStep 1993859 = 2990789) B2990789
theorem B3364645 : Blo 1993435 3364645 := bbase (se 4 (by rfl) ⟨315435, by rfl⟩ : syracuseStep 3364645 = 630871) (by norm_num)
theorem B4486193 : Blo 1993435 4486193 := bstep (se 2 (by rfl) ⟨1682322, by rfl⟩ : syracuseStep 4486193 = 3364645) B3364645
theorem B2990795 : Blo 1993435 2990795 := bstep (se 1 (by rfl) ⟨2243096, by rfl⟩ : syracuseStep 2990795 = 4486193) B4486193
theorem B1993863 : Blo 1993435 1993863 := bstep (se 1 (by rfl) ⟨1495397, by rfl⟩ : syracuseStep 1993863 = 2990795) B2990795
theorem B2243101 : Blo 1993435 2243101 := bbase (se 3 (by rfl) ⟨420581, by rfl⟩ : syracuseStep 2243101 = 841163) (by norm_num)
theorem B2990801 : Blo 1993435 2990801 := bstep (se 2 (by rfl) ⟨1121550, by rfl⟩ : syracuseStep 2990801 = 2243101) B2243101
theorem B1993867 : Blo 1993435 1993867 := bstep (se 1 (by rfl) ⟨1495400, by rfl⟩ : syracuseStep 1993867 = 2990801) B2990801
theorem B6729317 : Blo 1993435 6729317 := bbase (se 4 (by rfl) ⟨630873, by rfl⟩ : syracuseStep 6729317 = 1261747) (by norm_num)
theorem B4486211 : Blo 1993435 4486211 := bstep (se 1 (by rfl) ⟨3364658, by rfl⟩ : syracuseStep 4486211 = 6729317) B6729317
theorem B2990807 : Blo 1993435 2990807 := bstep (se 1 (by rfl) ⟨2243105, by rfl⟩ : syracuseStep 2990807 = 4486211) B4486211
theorem B1993871 : Blo 1993435 1993871 := bstep (se 1 (by rfl) ⟨1495403, by rfl⟩ : syracuseStep 1993871 = 2990807) B2990807
theorem B2990813 : Blo 1993435 2990813 := bbase (se 3 (by rfl) ⟨560777, by rfl⟩ : syracuseStep 2990813 = 1121555) (by norm_num)
theorem B1993875 : Blo 1993435 1993875 := bstep (se 1 (by rfl) ⟨1495406, by rfl⟩ : syracuseStep 1993875 = 2990813) B2990813
theorem B4486229 : Blo 1993435 4486229 := bbase (se 8 (by rfl) ⟨26286, by rfl⟩ : syracuseStep 4486229 = 52573) (by norm_num)
theorem B2990819 : Blo 1993435 2990819 := bstep (se 1 (by rfl) ⟨2243114, by rfl⟩ : syracuseStep 2990819 = 4486229) B4486229
theorem B1993879 : Blo 1993435 1993879 := bstep (se 1 (by rfl) ⟨1495409, by rfl⟩ : syracuseStep 1993879 = 2990819) B2990819
theorem B3593045 : Blo 1993435 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B9581453 : Blo 1993435 9581453 := bstep (se 3 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 9581453 = 3593045) B3593045
theorem B6387635 : Blo 1993435 6387635 := bstep (se 1 (by rfl) ⟨4790726, by rfl⟩ : syracuseStep 6387635 = 9581453) B9581453
theorem B4258423 : Blo 1993435 4258423 := bstep (se 1 (by rfl) ⟨3193817, by rfl⟩ : syracuseStep 4258423 = 6387635) B6387635
theorem B5677897 : Blo 1993435 5677897 := bstep (se 2 (by rfl) ⟨2129211, by rfl⟩ : syracuseStep 5677897 = 4258423) B4258423
theorem B7570529 : Blo 1993435 7570529 := bstep (se 2 (by rfl) ⟨2838948, by rfl⟩ : syracuseStep 7570529 = 5677897) B5677897
theorem B5047019 : Blo 1993435 5047019 := bstep (se 1 (by rfl) ⟨3785264, by rfl⟩ : syracuseStep 5047019 = 7570529) B7570529
theorem B3364679 : Blo 1993435 3364679 := bstep (se 1 (by rfl) ⟨2523509, by rfl⟩ : syracuseStep 3364679 = 5047019) B5047019
theorem B2243119 : Blo 1993435 2243119 := bstep (se 1 (by rfl) ⟨1682339, by rfl⟩ : syracuseStep 2243119 = 3364679) B3364679
theorem B2990825 : Blo 1993435 2990825 := bstep (se 2 (by rfl) ⟨1121559, by rfl⟩ : syracuseStep 2990825 = 2243119) B2243119
theorem B1993883 : Blo 1993435 1993883 := bstep (se 1 (by rfl) ⟨1495412, by rfl⟩ : syracuseStep 1993883 = 2990825) B2990825
theorem B3031637 : Blo 1993435 3031637 := bbase (se 8 (by rfl) ⟨17763, by rfl⟩ : syracuseStep 3031637 = 35527) (by norm_num)
theorem B32337461 : Blo 1993435 32337461 := bstep (se 5 (by rfl) ⟨1515818, by rfl⟩ : syracuseStep 32337461 = 3031637) B3031637
theorem B21558307 : Blo 1993435 21558307 := bstep (se 1 (by rfl) ⟨16168730, by rfl⟩ : syracuseStep 21558307 = 32337461) B32337461
theorem B28744409 : Blo 1993435 28744409 := bstep (se 2 (by rfl) ⟨10779153, by rfl⟩ : syracuseStep 28744409 = 21558307) B21558307
theorem B19162939 : Blo 1993435 19162939 := bstep (se 1 (by rfl) ⟨14372204, by rfl⟩ : syracuseStep 19162939 = 28744409) B28744409
theorem B25550585 : Blo 1993435 25550585 := bstep (se 2 (by rfl) ⟨9581469, by rfl⟩ : syracuseStep 25550585 = 19162939) B19162939
theorem B17033723 : Blo 1993435 17033723 := bstep (se 1 (by rfl) ⟨12775292, by rfl⟩ : syracuseStep 17033723 = 25550585) B25550585
theorem B11355815 : Blo 1993435 11355815 := bstep (se 1 (by rfl) ⟨8516861, by rfl⟩ : syracuseStep 11355815 = 17033723) B17033723
theorem B7570543 : Blo 1993435 7570543 := bstep (se 1 (by rfl) ⟨5677907, by rfl⟩ : syracuseStep 7570543 = 11355815) B11355815
theorem B10094057 : Blo 1993435 10094057 := bstep (se 2 (by rfl) ⟨3785271, by rfl⟩ : syracuseStep 10094057 = 7570543) B7570543
theorem B6729371 : Blo 1993435 6729371 := bstep (se 1 (by rfl) ⟨5047028, by rfl⟩ : syracuseStep 6729371 = 10094057) B10094057
theorem B4486247 : Blo 1993435 4486247 := bstep (se 1 (by rfl) ⟨3364685, by rfl⟩ : syracuseStep 4486247 = 6729371) B6729371
theorem B2990831 : Blo 1993435 2990831 := bstep (se 1 (by rfl) ⟨2243123, by rfl⟩ : syracuseStep 2990831 = 4486247) B4486247
theorem B1993887 : Blo 1993435 1993887 := bstep (se 1 (by rfl) ⟨1495415, by rfl⟩ : syracuseStep 1993887 = 2990831) B2990831
theorem B2990837 : Blo 1993435 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B1993891 : Blo 1993435 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B7186133 : Blo 1993435 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B4790755 : Blo 1993435 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B6387673 : Blo 1993435 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B8516897 : Blo 1993435 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B5677931 : Blo 1993435 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B3785287 : Blo 1993435 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B5047049 : Blo 1993435 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B3364699 : Blo 1993435 3364699 := bstep (se 1 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 3364699 = 5047049) B5047049
theorem B4486265 : Blo 1993435 4486265 := bstep (se 2 (by rfl) ⟨1682349, by rfl⟩ : syracuseStep 4486265 = 3364699) B3364699
theorem B2990843 : Blo 1993435 2990843 := bstep (se 1 (by rfl) ⟨2243132, by rfl⟩ : syracuseStep 2990843 = 4486265) B4486265
theorem B1993895 : Blo 1993435 1993895 := bstep (se 1 (by rfl) ⟨1495421, by rfl⟩ : syracuseStep 1993895 = 2990843) B2990843
theorem B2243137 : Blo 1993435 2243137 := bbase (se 2 (by rfl) ⟨841176, by rfl⟩ : syracuseStep 2243137 = 1682353) (by norm_num)
theorem B2990849 : Blo 1993435 2990849 := bstep (se 2 (by rfl) ⟨1121568, by rfl⟩ : syracuseStep 2990849 = 2243137) B2243137
theorem B1993899 : Blo 1993435 1993899 := bstep (se 1 (by rfl) ⟨1495424, by rfl⟩ : syracuseStep 1993899 = 2990849) B2990849
theorem B5047069 : Blo 1993435 5047069 := bbase (se 3 (by rfl) ⟨946325, by rfl⟩ : syracuseStep 5047069 = 1892651) (by norm_num)
theorem B6729425 : Blo 1993435 6729425 := bstep (se 2 (by rfl) ⟨2523534, by rfl⟩ : syracuseStep 6729425 = 5047069) B5047069
theorem B4486283 : Blo 1993435 4486283 := bstep (se 1 (by rfl) ⟨3364712, by rfl⟩ : syracuseStep 4486283 = 6729425) B6729425
theorem B2990855 : Blo 1993435 2990855 := bstep (se 1 (by rfl) ⟨2243141, by rfl⟩ : syracuseStep 2990855 = 4486283) B4486283
theorem B1993903 : Blo 1993435 1993903 := bstep (se 1 (by rfl) ⟨1495427, by rfl⟩ : syracuseStep 1993903 = 2990855) B2990855
theorem B2990861 : Blo 1993435 2990861 := bbase (se 3 (by rfl) ⟨560786, by rfl⟩ : syracuseStep 2990861 = 1121573) (by norm_num)
theorem B1993907 : Blo 1993435 1993907 := bstep (se 1 (by rfl) ⟨1495430, by rfl⟩ : syracuseStep 1993907 = 2990861) B2990861
theorem B4486301 : Blo 1993435 4486301 := bbase (se 3 (by rfl) ⟨841181, by rfl⟩ : syracuseStep 4486301 = 1682363) (by norm_num)
theorem B2990867 : Blo 1993435 2990867 := bstep (se 1 (by rfl) ⟨2243150, by rfl⟩ : syracuseStep 2990867 = 4486301) B4486301
theorem B1993911 : Blo 1993435 1993911 := bstep (se 1 (by rfl) ⟨1495433, by rfl⟩ : syracuseStep 1993911 = 2990867) B2990867
theorem B3364733 : Blo 1993435 3364733 := bbase (se 3 (by rfl) ⟨630887, by rfl⟩ : syracuseStep 3364733 = 1261775) (by norm_num)
theorem B2243155 : Blo 1993435 2243155 := bstep (se 1 (by rfl) ⟨1682366, by rfl⟩ : syracuseStep 2243155 = 3364733) B3364733
theorem B2990873 : Blo 1993435 2990873 := bstep (se 2 (by rfl) ⟨1121577, by rfl⟩ : syracuseStep 2990873 = 2243155) B2243155
theorem B1993915 : Blo 1993435 1993915 := bstep (se 1 (by rfl) ⟨1495436, by rfl⟩ : syracuseStep 1993915 = 2990873) B2990873
theorem B6387749 : Blo 1993435 6387749 := bbase (se 4 (by rfl) ⟨598851, by rfl⟩ : syracuseStep 6387749 = 1197703) (by norm_num)
theorem B4258499 : Blo 1993435 4258499 := bstep (se 1 (by rfl) ⟨3193874, by rfl⟩ : syracuseStep 4258499 = 6387749) B6387749
theorem B11355997 : Blo 1993435 11355997 := bstep (se 3 (by rfl) ⟨2129249, by rfl⟩ : syracuseStep 11355997 = 4258499) B4258499
theorem B15141329 : Blo 1993435 15141329 := bstep (se 2 (by rfl) ⟨5677998, by rfl⟩ : syracuseStep 15141329 = 11355997) B11355997
theorem B10094219 : Blo 1993435 10094219 := bstep (se 1 (by rfl) ⟨7570664, by rfl⟩ : syracuseStep 10094219 = 15141329) B15141329
theorem B6729479 : Blo 1993435 6729479 := bstep (se 1 (by rfl) ⟨5047109, by rfl⟩ : syracuseStep 6729479 = 10094219) B10094219
theorem B4486319 : Blo 1993435 4486319 := bstep (se 1 (by rfl) ⟨3364739, by rfl⟩ : syracuseStep 4486319 = 6729479) B6729479
theorem B2990879 : Blo 1993435 2990879 := bstep (se 1 (by rfl) ⟨2243159, by rfl⟩ : syracuseStep 2990879 = 4486319) B4486319
theorem B1993919 : Blo 1993435 1993919 := bstep (se 1 (by rfl) ⟨1495439, by rfl⟩ : syracuseStep 1993919 = 2990879) B2990879
theorem B2990885 : Blo 1993435 2990885 := bbase (se 4 (by rfl) ⟨280395, by rfl⟩ : syracuseStep 2990885 = 560791) (by norm_num)
theorem B1993923 : Blo 1993435 1993923 := bstep (se 1 (by rfl) ⟨1495442, by rfl⟩ : syracuseStep 1993923 = 2990885) B2990885
theorem B2523565 : Blo 1993435 2523565 := bbase (se 3 (by rfl) ⟨473168, by rfl⟩ : syracuseStep 2523565 = 946337) (by norm_num)
theorem B3364753 : Blo 1993435 3364753 := bstep (se 2 (by rfl) ⟨1261782, by rfl⟩ : syracuseStep 3364753 = 2523565) B2523565
theorem B4486337 : Blo 1993435 4486337 := bstep (se 2 (by rfl) ⟨1682376, by rfl⟩ : syracuseStep 4486337 = 3364753) B3364753
theorem B2990891 : Blo 1993435 2990891 := bstep (se 1 (by rfl) ⟨2243168, by rfl⟩ : syracuseStep 2990891 = 4486337) B4486337
theorem B1993927 : Blo 1993435 1993927 := bstep (se 1 (by rfl) ⟨1495445, by rfl⟩ : syracuseStep 1993927 = 2990891) B2990891
theorem B2243173 : Blo 1993435 2243173 := bbase (se 4 (by rfl) ⟨210297, by rfl⟩ : syracuseStep 2243173 = 420595) (by norm_num)
theorem B2990897 : Blo 1993435 2990897 := bstep (se 2 (by rfl) ⟨1121586, by rfl⟩ : syracuseStep 2990897 = 2243173) B2243173
theorem B1993931 : Blo 1993435 1993931 := bstep (se 1 (by rfl) ⟨1495448, by rfl⟩ : syracuseStep 1993931 = 2990897) B2990897
theorem B3193901 : Blo 1993435 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B2129267 : Blo 1993435 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B5678045 : Blo 1993435 5678045 := bstep (se 3 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 5678045 = 2129267) B2129267
theorem B3785363 : Blo 1993435 3785363 := bstep (se 1 (by rfl) ⟨2839022, by rfl⟩ : syracuseStep 3785363 = 5678045) B5678045
theorem B2523575 : Blo 1993435 2523575 := bstep (se 1 (by rfl) ⟨1892681, by rfl⟩ : syracuseStep 2523575 = 3785363) B3785363
theorem B6729533 : Blo 1993435 6729533 := bstep (se 3 (by rfl) ⟨1261787, by rfl⟩ : syracuseStep 6729533 = 2523575) B2523575
theorem B4486355 : Blo 1993435 4486355 := bstep (se 1 (by rfl) ⟨3364766, by rfl⟩ : syracuseStep 4486355 = 6729533) B6729533
theorem B2990903 : Blo 1993435 2990903 := bstep (se 1 (by rfl) ⟨2243177, by rfl⟩ : syracuseStep 2990903 = 4486355) B4486355
theorem B1993935 : Blo 1993435 1993935 := bstep (se 1 (by rfl) ⟨1495451, by rfl⟩ : syracuseStep 1993935 = 2990903) B2990903
theorem B2990909 : Blo 1993435 2990909 := bbase (se 3 (by rfl) ⟨560795, by rfl⟩ : syracuseStep 2990909 = 1121591) (by norm_num)
theorem B1993939 : Blo 1993435 1993939 := bstep (se 1 (by rfl) ⟨1495454, by rfl⟩ : syracuseStep 1993939 = 2990909) B2990909
theorem B4486373 : Blo 1993435 4486373 := bbase (se 4 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 4486373 = 841195) (by norm_num)
theorem B2990915 : Blo 1993435 2990915 := bstep (se 1 (by rfl) ⟨2243186, by rfl⟩ : syracuseStep 2990915 = 4486373) B4486373
theorem B1993943 : Blo 1993435 1993943 := bstep (se 1 (by rfl) ⟨1495457, by rfl⟩ : syracuseStep 1993943 = 2990915) B2990915
theorem B5047181 : Blo 1993435 5047181 := bbase (se 3 (by rfl) ⟨946346, by rfl⟩ : syracuseStep 5047181 = 1892693) (by norm_num)
theorem B3364787 : Blo 1993435 3364787 := bstep (se 1 (by rfl) ⟨2523590, by rfl⟩ : syracuseStep 3364787 = 5047181) B5047181
theorem B2243191 : Blo 1993435 2243191 := bstep (se 1 (by rfl) ⟨1682393, by rfl⟩ : syracuseStep 2243191 = 3364787) B3364787
theorem B2990921 : Blo 1993435 2990921 := bstep (se 2 (by rfl) ⟨1121595, by rfl⟩ : syracuseStep 2990921 = 2243191) B2243191
theorem B1993947 : Blo 1993435 1993947 := bstep (se 1 (by rfl) ⟨1495460, by rfl⟩ : syracuseStep 1993947 = 2990921) B2990921
theorem B2839045 : Blo 1993435 2839045 := bbase (se 4 (by rfl) ⟨266160, by rfl⟩ : syracuseStep 2839045 = 532321) (by norm_num)
theorem B3785393 : Blo 1993435 3785393 := bstep (se 2 (by rfl) ⟨1419522, by rfl⟩ : syracuseStep 3785393 = 2839045) B2839045
theorem B10094381 : Blo 1993435 10094381 := bstep (se 3 (by rfl) ⟨1892696, by rfl⟩ : syracuseStep 10094381 = 3785393) B3785393
theorem B6729587 : Blo 1993435 6729587 := bstep (se 1 (by rfl) ⟨5047190, by rfl⟩ : syracuseStep 6729587 = 10094381) B10094381
theorem B4486391 : Blo 1993435 4486391 := bstep (se 1 (by rfl) ⟨3364793, by rfl⟩ : syracuseStep 4486391 = 6729587) B6729587
theorem B2990927 : Blo 1993435 2990927 := bstep (se 1 (by rfl) ⟨2243195, by rfl⟩ : syracuseStep 2990927 = 4486391) B4486391
theorem B1993951 : Blo 1993435 1993951 := bstep (se 1 (by rfl) ⟨1495463, by rfl⟩ : syracuseStep 1993951 = 2990927) B2990927
theorem B2990933 : Blo 1993435 2990933 := bbase (se 9 (by rfl) ⟨8762, by rfl⟩ : syracuseStep 2990933 = 17525) (by norm_num)
theorem B1993955 : Blo 1993435 1993955 := bstep (se 1 (by rfl) ⟨1495466, by rfl⟩ : syracuseStep 1993955 = 2990933) B2990933
theorem B4790909 : Blo 1993435 4790909 := bbase (se 3 (by rfl) ⟨898295, by rfl⟩ : syracuseStep 4790909 = 1796591) (by norm_num)
theorem B3193939 : Blo 1993435 3193939 := bstep (se 1 (by rfl) ⟨2395454, by rfl⟩ : syracuseStep 3193939 = 4790909) B4790909
theorem B4258585 : Blo 1993435 4258585 := bstep (se 2 (by rfl) ⟨1596969, by rfl⟩ : syracuseStep 4258585 = 3193939) B3193939
theorem B5678113 : Blo 1993435 5678113 := bstep (se 2 (by rfl) ⟨2129292, by rfl⟩ : syracuseStep 5678113 = 4258585) B4258585
theorem B7570817 : Blo 1993435 7570817 := bstep (se 2 (by rfl) ⟨2839056, by rfl⟩ : syracuseStep 7570817 = 5678113) B5678113
theorem B5047211 : Blo 1993435 5047211 := bstep (se 1 (by rfl) ⟨3785408, by rfl⟩ : syracuseStep 5047211 = 7570817) B7570817
theorem B3364807 : Blo 1993435 3364807 := bstep (se 1 (by rfl) ⟨2523605, by rfl⟩ : syracuseStep 3364807 = 5047211) B5047211
theorem B4486409 : Blo 1993435 4486409 := bstep (se 2 (by rfl) ⟨1682403, by rfl⟩ : syracuseStep 4486409 = 3364807) B3364807
theorem B2990939 : Blo 1993435 2990939 := bstep (se 1 (by rfl) ⟨2243204, by rfl⟩ : syracuseStep 2990939 = 4486409) B4486409
theorem B1993959 : Blo 1993435 1993959 := bstep (se 1 (by rfl) ⟨1495469, by rfl⟩ : syracuseStep 1993959 = 2990939) B2990939
theorem B2243209 : Blo 1993435 2243209 := bbase (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) (by norm_num)
theorem B2990945 : Blo 1993435 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B1993963 : Blo 1993435 1993963 := bstep (se 1 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 1993963 = 2990945) B2990945
theorem B2768933 : Blo 1993435 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B7383821 : Blo 1993435 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B19690189 : Blo 1993435 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B105014341 : Blo 1993435 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B140019121 : Blo 1993435 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B746768645 : Blo 1993435 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B497845763 : Blo 1993435 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B331897175 : Blo 1993435 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B221264783 : Blo 1993435 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B147509855 : Blo 1993435 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B98339903 : Blo 1993435 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B65559935 : Blo 1993435 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B43706623 : Blo 1993435 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B58275497 : Blo 1993435 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B155401325 : Blo 1993435 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B103600883 : Blo 1993435 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B69067255 : Blo 1993435 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B92089673 : Blo 1993435 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B61393115 : Blo 1993435 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B40928743 : Blo 1993435 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B54571657 : Blo 1993435 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B72762209 : Blo 1993435 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B48508139 : Blo 1993435 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B32338759 : Blo 1993435 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B43118345 : Blo 1993435 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B28745563 : Blo 1993435 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B38327417 : Blo 1993435 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B25551611 : Blo 1993435 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B17034407 : Blo 1993435 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B11356271 : Blo 1993435 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B7570847 : Blo 1993435 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B5047231 : Blo 1993435 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B6729641 : Blo 1993435 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B4486427 : Blo 1993435 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B2990951 : Blo 1993435 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B1993967 : Blo 1993435 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B2990957 : Blo 1993435 2990957 := bbase (se 3 (by rfl) ⟨560804, by rfl⟩ : syracuseStep 2990957 = 1121609) (by norm_num)
theorem B1993971 : Blo 1993435 1993971 := bstep (se 1 (by rfl) ⟨1495478, by rfl⟩ : syracuseStep 1993971 = 2990957) B2990957
theorem B4486445 : Blo 1993435 4486445 := bbase (se 3 (by rfl) ⟨841208, by rfl⟩ : syracuseStep 4486445 = 1682417) (by norm_num)
theorem B2990963 : Blo 1993435 2990963 := bstep (se 1 (by rfl) ⟨2243222, by rfl⟩ : syracuseStep 2990963 = 4486445) B4486445
theorem B1993975 : Blo 1993435 1993975 := bstep (se 1 (by rfl) ⟨1495481, by rfl⟩ : syracuseStep 1993975 = 2990963) B2990963
theorem B2592965 : Blo 1993435 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B6914573 : Blo 1993435 6914573 := bstep (se 3 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 6914573 = 2592965) B2592965
theorem B4609715 : Blo 1993435 4609715 := bstep (se 1 (by rfl) ⟨3457286, by rfl⟩ : syracuseStep 4609715 = 6914573) B6914573
theorem B12292573 : Blo 1993435 12292573 := bstep (se 3 (by rfl) ⟨2304857, by rfl⟩ : syracuseStep 12292573 = 4609715) B4609715
theorem B16390097 : Blo 1993435 16390097 := bstep (se 2 (by rfl) ⟨6146286, by rfl⟩ : syracuseStep 16390097 = 12292573) B12292573
theorem B10926731 : Blo 1993435 10926731 := bstep (se 1 (by rfl) ⟨8195048, by rfl⟩ : syracuseStep 10926731 = 16390097) B16390097
theorem B7284487 : Blo 1993435 7284487 := bstep (se 1 (by rfl) ⟨5463365, by rfl⟩ : syracuseStep 7284487 = 10926731) B10926731
theorem B9712649 : Blo 1993435 9712649 := bstep (se 2 (by rfl) ⟨3642243, by rfl⟩ : syracuseStep 9712649 = 7284487) B7284487
theorem B6475099 : Blo 1993435 6475099 := bstep (se 1 (by rfl) ⟨4856324, by rfl⟩ : syracuseStep 6475099 = 9712649) B9712649
theorem B8633465 : Blo 1993435 8633465 := bstep (se 2 (by rfl) ⟨3237549, by rfl⟩ : syracuseStep 8633465 = 6475099) B6475099
theorem B5755643 : Blo 1993435 5755643 := bstep (se 1 (by rfl) ⟨4316732, by rfl⟩ : syracuseStep 5755643 = 8633465) B8633465
theorem B3837095 : Blo 1993435 3837095 := bstep (se 1 (by rfl) ⟨2877821, by rfl⟩ : syracuseStep 3837095 = 5755643) B5755643
theorem B2558063 : Blo 1993435 2558063 := bstep (se 1 (by rfl) ⟨1918547, by rfl⟩ : syracuseStep 2558063 = 3837095) B3837095
theorem B6821501 : Blo 1993435 6821501 := bstep (se 3 (by rfl) ⟨1279031, by rfl⟩ : syracuseStep 6821501 = 2558063) B2558063
theorem B18190669 : Blo 1993435 18190669 := bstep (se 3 (by rfl) ⟨3410750, by rfl⟩ : syracuseStep 18190669 = 6821501) B6821501
theorem B24254225 : Blo 1993435 24254225 := bstep (se 2 (by rfl) ⟨9095334, by rfl⟩ : syracuseStep 24254225 = 18190669) B18190669
theorem B16169483 : Blo 1993435 16169483 := bstep (se 1 (by rfl) ⟨12127112, by rfl⟩ : syracuseStep 16169483 = 24254225) B24254225
theorem B10779655 : Blo 1993435 10779655 := bstep (se 1 (by rfl) ⟨8084741, by rfl⟩ : syracuseStep 10779655 = 16169483) B16169483
theorem B14372873 : Blo 1993435 14372873 := bstep (se 2 (by rfl) ⟨5389827, by rfl⟩ : syracuseStep 14372873 = 10779655) B10779655
theorem B9581915 : Blo 1993435 9581915 := bstep (se 1 (by rfl) ⟨7186436, by rfl⟩ : syracuseStep 9581915 = 14372873) B14372873
theorem B6387943 : Blo 1993435 6387943 := bstep (se 1 (by rfl) ⟨4790957, by rfl⟩ : syracuseStep 6387943 = 9581915) B9581915
theorem B8517257 : Blo 1993435 8517257 := bstep (se 2 (by rfl) ⟨3193971, by rfl⟩ : syracuseStep 8517257 = 6387943) B6387943
theorem B5678171 : Blo 1993435 5678171 := bstep (se 1 (by rfl) ⟨4258628, by rfl⟩ : syracuseStep 5678171 = 8517257) B8517257
theorem B3785447 : Blo 1993435 3785447 := bstep (se 1 (by rfl) ⟨2839085, by rfl⟩ : syracuseStep 3785447 = 5678171) B5678171
theorem B2523631 : Blo 1993435 2523631 := bstep (se 1 (by rfl) ⟨1892723, by rfl⟩ : syracuseStep 2523631 = 3785447) B3785447
theorem B3364841 : Blo 1993435 3364841 := bstep (se 2 (by rfl) ⟨1261815, by rfl⟩ : syracuseStep 3364841 = 2523631) B2523631
theorem B2243227 : Blo 1993435 2243227 := bstep (se 1 (by rfl) ⟨1682420, by rfl⟩ : syracuseStep 2243227 = 3364841) B3364841
theorem B2990969 : Blo 1993435 2990969 := bstep (se 2 (by rfl) ⟨1121613, by rfl⟩ : syracuseStep 2990969 = 2243227) B2243227
theorem B1993979 : Blo 1993435 1993979 := bstep (se 1 (by rfl) ⟨1495484, by rfl⟩ : syracuseStep 1993979 = 2990969) B2990969
theorem B19163861 : Blo 1993435 19163861 := bbase (se 7 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 19163861 = 449153) (by norm_num)
theorem B12775907 : Blo 1993435 12775907 := bstep (se 1 (by rfl) ⟨9581930, by rfl⟩ : syracuseStep 12775907 = 19163861) B19163861
theorem B34069085 : Blo 1993435 34069085 := bstep (se 3 (by rfl) ⟨6387953, by rfl⟩ : syracuseStep 34069085 = 12775907) B12775907
theorem B22712723 : Blo 1993435 22712723 := bstep (se 1 (by rfl) ⟨17034542, by rfl⟩ : syracuseStep 22712723 = 34069085) B34069085
theorem B15141815 : Blo 1993435 15141815 := bstep (se 1 (by rfl) ⟨11356361, by rfl⟩ : syracuseStep 15141815 = 22712723) B22712723
theorem B10094543 : Blo 1993435 10094543 := bstep (se 1 (by rfl) ⟨7570907, by rfl⟩ : syracuseStep 10094543 = 15141815) B15141815
theorem B6729695 : Blo 1993435 6729695 := bstep (se 1 (by rfl) ⟨5047271, by rfl⟩ : syracuseStep 6729695 = 10094543) B10094543
theorem B4486463 : Blo 1993435 4486463 := bstep (se 1 (by rfl) ⟨3364847, by rfl⟩ : syracuseStep 4486463 = 6729695) B6729695
theorem B2990975 : Blo 1993435 2990975 := bstep (se 1 (by rfl) ⟨2243231, by rfl⟩ : syracuseStep 2990975 = 4486463) B4486463
theorem B1993983 : Blo 1993435 1993983 := bstep (se 1 (by rfl) ⟨1495487, by rfl⟩ : syracuseStep 1993983 = 2990975) B2990975
theorem B2990981 : Blo 1993435 2990981 := bbase (se 4 (by rfl) ⟨280404, by rfl⟩ : syracuseStep 2990981 = 560809) (by norm_num)
theorem B1993987 : Blo 1993435 1993987 := bstep (se 1 (by rfl) ⟨1495490, by rfl⟩ : syracuseStep 1993987 = 2990981) B2990981
theorem B3364861 : Blo 1993435 3364861 := bbase (se 3 (by rfl) ⟨630911, by rfl⟩ : syracuseStep 3364861 = 1261823) (by norm_num)
theorem B4486481 : Blo 1993435 4486481 := bstep (se 2 (by rfl) ⟨1682430, by rfl⟩ : syracuseStep 4486481 = 3364861) B3364861
theorem B2990987 : Blo 1993435 2990987 := bstep (se 1 (by rfl) ⟨2243240, by rfl⟩ : syracuseStep 2990987 = 4486481) B4486481
theorem B1993991 : Blo 1993435 1993991 := bstep (se 1 (by rfl) ⟨1495493, by rfl⟩ : syracuseStep 1993991 = 2990987) B2990987
theorem B2243245 : Blo 1993435 2243245 := bbase (se 3 (by rfl) ⟨420608, by rfl⟩ : syracuseStep 2243245 = 841217) (by norm_num)
theorem B2990993 : Blo 1993435 2990993 := bstep (se 2 (by rfl) ⟨1121622, by rfl⟩ : syracuseStep 2990993 = 2243245) B2243245
theorem B1993995 : Blo 1993435 1993995 := bstep (se 1 (by rfl) ⟨1495496, by rfl⟩ : syracuseStep 1993995 = 2990993) B2990993
theorem B6729749 : Blo 1993435 6729749 := bbase (se 6 (by rfl) ⟨157728, by rfl⟩ : syracuseStep 6729749 = 315457) (by norm_num)
theorem B4486499 : Blo 1993435 4486499 := bstep (se 1 (by rfl) ⟨3364874, by rfl⟩ : syracuseStep 4486499 = 6729749) B6729749
theorem B2990999 : Blo 1993435 2990999 := bstep (se 1 (by rfl) ⟨2243249, by rfl⟩ : syracuseStep 2990999 = 4486499) B4486499
theorem B1993999 : Blo 1993435 1993999 := bstep (se 1 (by rfl) ⟨1495499, by rfl⟩ : syracuseStep 1993999 = 2990999) B2990999
theorem B2991005 : Blo 1993435 2991005 := bbase (se 3 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 2991005 = 1121627) (by norm_num)
theorem B1994003 : Blo 1993435 1994003 := bstep (se 1 (by rfl) ⟨1495502, by rfl⟩ : syracuseStep 1994003 = 2991005) B2991005
theorem B4486517 : Blo 1993435 4486517 := bbase (se 5 (by rfl) ⟨210305, by rfl⟩ : syracuseStep 4486517 = 420611) (by norm_num)
theorem B2991011 : Blo 1993435 2991011 := bstep (se 1 (by rfl) ⟨2243258, by rfl⟩ : syracuseStep 2991011 = 4486517) B4486517
theorem B1994007 : Blo 1993435 1994007 := bstep (se 1 (by rfl) ⟨1495505, by rfl⟩ : syracuseStep 1994007 = 2991011) B2991011
theorem B6063653 : Blo 1993435 6063653 := bbase (se 4 (by rfl) ⟨568467, by rfl⟩ : syracuseStep 6063653 = 1136935) (by norm_num)
theorem B4042435 : Blo 1993435 4042435 := bstep (se 1 (by rfl) ⟨3031826, by rfl⟩ : syracuseStep 4042435 = 6063653) B6063653
theorem B5389913 : Blo 1993435 5389913 := bstep (se 2 (by rfl) ⟨2021217, by rfl⟩ : syracuseStep 5389913 = 4042435) B4042435
theorem B14373101 : Blo 1993435 14373101 := bstep (se 3 (by rfl) ⟨2694956, by rfl⟩ : syracuseStep 14373101 = 5389913) B5389913
theorem B9582067 : Blo 1993435 9582067 := bstep (se 1 (by rfl) ⟨7186550, by rfl⟩ : syracuseStep 9582067 = 14373101) B14373101
theorem B12776089 : Blo 1993435 12776089 := bstep (se 2 (by rfl) ⟨4791033, by rfl⟩ : syracuseStep 12776089 = 9582067) B9582067
theorem B17034785 : Blo 1993435 17034785 := bstep (se 2 (by rfl) ⟨6388044, by rfl⟩ : syracuseStep 17034785 = 12776089) B12776089
theorem B11356523 : Blo 1993435 11356523 := bstep (se 1 (by rfl) ⟨8517392, by rfl⟩ : syracuseStep 11356523 = 17034785) B17034785
theorem B7571015 : Blo 1993435 7571015 := bstep (se 1 (by rfl) ⟨5678261, by rfl⟩ : syracuseStep 7571015 = 11356523) B11356523
theorem B5047343 : Blo 1993435 5047343 := bstep (se 1 (by rfl) ⟨3785507, by rfl⟩ : syracuseStep 5047343 = 7571015) B7571015
theorem B3364895 : Blo 1993435 3364895 := bstep (se 1 (by rfl) ⟨2523671, by rfl⟩ : syracuseStep 3364895 = 5047343) B5047343
theorem B2243263 : Blo 1993435 2243263 := bstep (se 1 (by rfl) ⟨1682447, by rfl⟩ : syracuseStep 2243263 = 3364895) B3364895
theorem B2991017 : Blo 1993435 2991017 := bstep (se 2 (by rfl) ⟨1121631, by rfl⟩ : syracuseStep 2991017 = 2243263) B2243263
theorem B1994011 : Blo 1993435 1994011 := bstep (se 1 (by rfl) ⟨1495508, by rfl⟩ : syracuseStep 1994011 = 2991017) B2991017
theorem B7571029 : Blo 1993435 7571029 := bbase (se 8 (by rfl) ⟨44361, by rfl⟩ : syracuseStep 7571029 = 88723) (by norm_num)
theorem B10094705 : Blo 1993435 10094705 := bstep (se 2 (by rfl) ⟨3785514, by rfl⟩ : syracuseStep 10094705 = 7571029) B7571029
theorem B6729803 : Blo 1993435 6729803 := bstep (se 1 (by rfl) ⟨5047352, by rfl⟩ : syracuseStep 6729803 = 10094705) B10094705
theorem B4486535 : Blo 1993435 4486535 := bstep (se 1 (by rfl) ⟨3364901, by rfl⟩ : syracuseStep 4486535 = 6729803) B6729803
theorem B2991023 : Blo 1993435 2991023 := bstep (se 1 (by rfl) ⟨2243267, by rfl⟩ : syracuseStep 2991023 = 4486535) B4486535
theorem B1994015 : Blo 1993435 1994015 := bstep (se 1 (by rfl) ⟨1495511, by rfl⟩ : syracuseStep 1994015 = 2991023) B2991023
theorem B2991029 : Blo 1993435 2991029 := bbase (se 5 (by rfl) ⟨140204, by rfl⟩ : syracuseStep 2991029 = 280409) (by norm_num)
theorem B1994019 : Blo 1993435 1994019 := bstep (se 1 (by rfl) ⟨1495514, by rfl⟩ : syracuseStep 1994019 = 2991029) B2991029
theorem B5047373 : Blo 1993435 5047373 := bbase (se 3 (by rfl) ⟨946382, by rfl⟩ : syracuseStep 5047373 = 1892765) (by norm_num)
theorem B3364915 : Blo 1993435 3364915 := bstep (se 1 (by rfl) ⟨2523686, by rfl⟩ : syracuseStep 3364915 = 5047373) B5047373
theorem B4486553 : Blo 1993435 4486553 := bstep (se 2 (by rfl) ⟨1682457, by rfl⟩ : syracuseStep 4486553 = 3364915) B3364915
theorem B2991035 : Blo 1993435 2991035 := bstep (se 1 (by rfl) ⟨2243276, by rfl⟩ : syracuseStep 2991035 = 4486553) B4486553
theorem B1994023 : Blo 1993435 1994023 := bstep (se 1 (by rfl) ⟨1495517, by rfl⟩ : syracuseStep 1994023 = 2991035) B2991035
theorem B2243281 : Blo 1993435 2243281 := bbase (se 2 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 2243281 = 1682461) (by norm_num)
theorem B2991041 : Blo 1993435 2991041 := bstep (se 2 (by rfl) ⟨1121640, by rfl⟩ : syracuseStep 2991041 = 2243281) B2243281
theorem B1994027 : Blo 1993435 1994027 := bstep (se 1 (by rfl) ⟨1495520, by rfl⟩ : syracuseStep 1994027 = 2991041) B2991041
theorem B2395541 : Blo 1993435 2395541 := bbase (se 6 (by rfl) ⟨56145, by rfl⟩ : syracuseStep 2395541 = 112291) (by norm_num)
theorem B6388109 : Blo 1993435 6388109 := bstep (se 3 (by rfl) ⟨1197770, by rfl⟩ : syracuseStep 6388109 = 2395541) B2395541
theorem B4258739 : Blo 1993435 4258739 := bstep (se 1 (by rfl) ⟨3194054, by rfl⟩ : syracuseStep 4258739 = 6388109) B6388109
theorem B2839159 : Blo 1993435 2839159 := bstep (se 1 (by rfl) ⟨2129369, by rfl⟩ : syracuseStep 2839159 = 4258739) B4258739
theorem B3785545 : Blo 1993435 3785545 := bstep (se 2 (by rfl) ⟨1419579, by rfl⟩ : syracuseStep 3785545 = 2839159) B2839159
theorem B5047393 : Blo 1993435 5047393 := bstep (se 2 (by rfl) ⟨1892772, by rfl⟩ : syracuseStep 5047393 = 3785545) B3785545
theorem B6729857 : Blo 1993435 6729857 := bstep (se 2 (by rfl) ⟨2523696, by rfl⟩ : syracuseStep 6729857 = 5047393) B5047393
theorem B4486571 : Blo 1993435 4486571 := bstep (se 1 (by rfl) ⟨3364928, by rfl⟩ : syracuseStep 4486571 = 6729857) B6729857
theorem B2991047 : Blo 1993435 2991047 := bstep (se 1 (by rfl) ⟨2243285, by rfl⟩ : syracuseStep 2991047 = 4486571) B4486571
theorem B1994031 : Blo 1993435 1994031 := bstep (se 1 (by rfl) ⟨1495523, by rfl⟩ : syracuseStep 1994031 = 2991047) B2991047
theorem B2991053 : Blo 1993435 2991053 := bbase (se 3 (by rfl) ⟨560822, by rfl⟩ : syracuseStep 2991053 = 1121645) (by norm_num)
theorem B1994035 : Blo 1993435 1994035 := bstep (se 1 (by rfl) ⟨1495526, by rfl⟩ : syracuseStep 1994035 = 2991053) B2991053
theorem B4486589 : Blo 1993435 4486589 := bbase (se 3 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 4486589 = 1682471) (by norm_num)
theorem B2991059 : Blo 1993435 2991059 := bstep (se 1 (by rfl) ⟨2243294, by rfl⟩ : syracuseStep 2991059 = 4486589) B4486589
theorem B1994039 : Blo 1993435 1994039 := bstep (se 1 (by rfl) ⟨1495529, by rfl⟩ : syracuseStep 1994039 = 2991059) B2991059
theorem B3364949 : Blo 1993435 3364949 := bbase (se 8 (by rfl) ⟨19716, by rfl⟩ : syracuseStep 3364949 = 39433) (by norm_num)
theorem B2243299 : Blo 1993435 2243299 := bstep (se 1 (by rfl) ⟨1682474, by rfl⟩ : syracuseStep 2243299 = 3364949) B3364949
theorem B2991065 : Blo 1993435 2991065 := bstep (se 2 (by rfl) ⟨1121649, by rfl⟩ : syracuseStep 2991065 = 2243299) B2243299
theorem B1994043 : Blo 1993435 1994043 := bstep (se 1 (by rfl) ⟨1495532, by rfl⟩ : syracuseStep 1994043 = 2991065) B2991065
theorem B4210237 : Blo 1993435 4210237 := bbase (se 3 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 4210237 = 1578839) (by norm_num)
theorem B22454597 : Blo 1993435 22454597 := bstep (se 4 (by rfl) ⟨2105118, by rfl⟩ : syracuseStep 22454597 = 4210237) B4210237
theorem B14969731 : Blo 1993435 14969731 := bstep (se 1 (by rfl) ⟨11227298, by rfl⟩ : syracuseStep 14969731 = 22454597) B22454597
theorem B19959641 : Blo 1993435 19959641 := bstep (se 2 (by rfl) ⟨7484865, by rfl⟩ : syracuseStep 19959641 = 14969731) B14969731
theorem B13306427 : Blo 1993435 13306427 := bstep (se 1 (by rfl) ⟨9979820, by rfl⟩ : syracuseStep 13306427 = 19959641) B19959641
theorem B8870951 : Blo 1993435 8870951 := bstep (se 1 (by rfl) ⟨6653213, by rfl⟩ : syracuseStep 8870951 = 13306427) B13306427
theorem B5913967 : Blo 1993435 5913967 := bstep (se 1 (by rfl) ⟨4435475, by rfl⟩ : syracuseStep 5913967 = 8870951) B8870951
theorem B7885289 : Blo 1993435 7885289 := bstep (se 2 (by rfl) ⟨2956983, by rfl⟩ : syracuseStep 7885289 = 5913967) B5913967
theorem B21027437 : Blo 1993435 21027437 := bstep (se 3 (by rfl) ⟨3942644, by rfl⟩ : syracuseStep 21027437 = 7885289) B7885289
theorem B14018291 : Blo 1993435 14018291 := bstep (se 1 (by rfl) ⟨10513718, by rfl⟩ : syracuseStep 14018291 = 21027437) B21027437
theorem B9345527 : Blo 1993435 9345527 := bstep (se 1 (by rfl) ⟨7009145, by rfl⟩ : syracuseStep 9345527 = 14018291) B14018291
theorem B6230351 : Blo 1993435 6230351 := bstep (se 1 (by rfl) ⟨4672763, by rfl⟩ : syracuseStep 6230351 = 9345527) B9345527
theorem B4153567 : Blo 1993435 4153567 := bstep (se 1 (by rfl) ⟨3115175, by rfl⟩ : syracuseStep 4153567 = 6230351) B6230351
theorem B5538089 : Blo 1993435 5538089 := bstep (se 2 (by rfl) ⟨2076783, by rfl⟩ : syracuseStep 5538089 = 4153567) B4153567
theorem B14768237 : Blo 1993435 14768237 := bstep (se 3 (by rfl) ⟨2769044, by rfl⟩ : syracuseStep 14768237 = 5538089) B5538089
theorem B9845491 : Blo 1993435 9845491 := bstep (se 1 (by rfl) ⟨7384118, by rfl⟩ : syracuseStep 9845491 = 14768237) B14768237
theorem B13127321 : Blo 1993435 13127321 := bstep (se 2 (by rfl) ⟨4922745, by rfl⟩ : syracuseStep 13127321 = 9845491) B9845491
theorem B8751547 : Blo 1993435 8751547 := bstep (se 1 (by rfl) ⟨6563660, by rfl⟩ : syracuseStep 8751547 = 13127321) B13127321
theorem B46674917 : Blo 1993435 46674917 := bstep (se 4 (by rfl) ⟨4375773, by rfl⟩ : syracuseStep 46674917 = 8751547) B8751547
theorem B31116611 : Blo 1993435 31116611 := bstep (se 1 (by rfl) ⟨23337458, by rfl⟩ : syracuseStep 31116611 = 46674917) B46674917
theorem B20744407 : Blo 1993435 20744407 := bstep (se 1 (by rfl) ⟨15558305, by rfl⟩ : syracuseStep 20744407 = 31116611) B31116611
theorem B27659209 : Blo 1993435 27659209 := bstep (se 2 (by rfl) ⟨10372203, by rfl⟩ : syracuseStep 27659209 = 20744407) B20744407
theorem B590063125 : Blo 1993435 590063125 := bstep (se 6 (by rfl) ⟨13829604, by rfl⟩ : syracuseStep 590063125 = 27659209) B27659209
theorem B786750833 : Blo 1993435 786750833 := bstep (se 2 (by rfl) ⟨295031562, by rfl⟩ : syracuseStep 786750833 = 590063125) B590063125
theorem B524500555 : Blo 1993435 524500555 := bstep (se 1 (by rfl) ⟨393375416, by rfl⟩ : syracuseStep 524500555 = 786750833) B786750833
theorem B699334073 : Blo 1993435 699334073 := bstep (se 2 (by rfl) ⟨262250277, by rfl⟩ : syracuseStep 699334073 = 524500555) B524500555
theorem B466222715 : Blo 1993435 466222715 := bstep (se 1 (by rfl) ⟨349667036, by rfl⟩ : syracuseStep 466222715 = 699334073) B699334073
theorem B310815143 : Blo 1993435 310815143 := bstep (se 1 (by rfl) ⟨233111357, by rfl⟩ : syracuseStep 310815143 = 466222715) B466222715
theorem B207210095 : Blo 1993435 207210095 := bstep (se 1 (by rfl) ⟨155407571, by rfl⟩ : syracuseStep 207210095 = 310815143) B310815143
theorem B138140063 : Blo 1993435 138140063 := bstep (se 1 (by rfl) ⟨103605047, by rfl⟩ : syracuseStep 138140063 = 207210095) B207210095
theorem B92093375 : Blo 1993435 92093375 := bstep (se 1 (by rfl) ⟨69070031, by rfl⟩ : syracuseStep 92093375 = 138140063) B138140063
theorem B61395583 : Blo 1993435 61395583 := bstep (se 1 (by rfl) ⟨46046687, by rfl⟩ : syracuseStep 61395583 = 92093375) B92093375
theorem B81860777 : Blo 1993435 81860777 := bstep (se 2 (by rfl) ⟨30697791, by rfl⟩ : syracuseStep 81860777 = 61395583) B61395583
theorem B54573851 : Blo 1993435 54573851 := bstep (se 1 (by rfl) ⟨40930388, by rfl⟩ : syracuseStep 54573851 = 81860777) B81860777
theorem B36382567 : Blo 1993435 36382567 := bstep (se 1 (by rfl) ⟨27286925, by rfl⟩ : syracuseStep 36382567 = 54573851) B54573851
theorem B48510089 : Blo 1993435 48510089 := bstep (se 2 (by rfl) ⟨18191283, by rfl⟩ : syracuseStep 48510089 = 36382567) B36382567
theorem B32340059 : Blo 1993435 32340059 := bstep (se 1 (by rfl) ⟨24255044, by rfl⟩ : syracuseStep 32340059 = 48510089) B48510089
theorem B21560039 : Blo 1993435 21560039 := bstep (se 1 (by rfl) ⟨16170029, by rfl⟩ : syracuseStep 21560039 = 32340059) B32340059
theorem B14373359 : Blo 1993435 14373359 := bstep (se 1 (by rfl) ⟨10780019, by rfl⟩ : syracuseStep 14373359 = 21560039) B21560039
theorem B9582239 : Blo 1993435 9582239 := bstep (se 1 (by rfl) ⟨7186679, by rfl⟩ : syracuseStep 9582239 = 14373359) B14373359
theorem B6388159 : Blo 1993435 6388159 := bstep (se 1 (by rfl) ⟨4791119, by rfl⟩ : syracuseStep 6388159 = 9582239) B9582239
theorem B8517545 : Blo 1993435 8517545 := bstep (se 2 (by rfl) ⟨3194079, by rfl⟩ : syracuseStep 8517545 = 6388159) B6388159
theorem B5678363 : Blo 1993435 5678363 := bstep (se 1 (by rfl) ⟨4258772, by rfl⟩ : syracuseStep 5678363 = 8517545) B8517545
theorem B15142301 : Blo 1993435 15142301 := bstep (se 3 (by rfl) ⟨2839181, by rfl⟩ : syracuseStep 15142301 = 5678363) B5678363
theorem B10094867 : Blo 1993435 10094867 := bstep (se 1 (by rfl) ⟨7571150, by rfl⟩ : syracuseStep 10094867 = 15142301) B15142301
theorem B6729911 : Blo 1993435 6729911 := bstep (se 1 (by rfl) ⟨5047433, by rfl⟩ : syracuseStep 6729911 = 10094867) B10094867
theorem B4486607 : Blo 1993435 4486607 := bstep (se 1 (by rfl) ⟨3364955, by rfl⟩ : syracuseStep 4486607 = 6729911) B6729911
theorem B2991071 : Blo 1993435 2991071 := bstep (se 1 (by rfl) ⟨2243303, by rfl⟩ : syracuseStep 2991071 = 4486607) B4486607
theorem B1994047 : Blo 1993435 1994047 := bstep (se 1 (by rfl) ⟨1495535, by rfl⟩ : syracuseStep 1994047 = 2991071) B2991071
theorem B2991077 : Blo 1993435 2991077 := bbase (se 4 (by rfl) ⟨280413, by rfl⟩ : syracuseStep 2991077 = 560827) (by norm_num)
theorem B1994051 : Blo 1993435 1994051 := bstep (se 1 (by rfl) ⟨1495538, by rfl⟩ : syracuseStep 1994051 = 2991077) B2991077
theorem B3194093 : Blo 1993435 3194093 := bbase (se 3 (by rfl) ⟨598892, by rfl⟩ : syracuseStep 3194093 = 1197785) (by norm_num)
theorem B8517581 : Blo 1993435 8517581 := bstep (se 3 (by rfl) ⟨1597046, by rfl⟩ : syracuseStep 8517581 = 3194093) B3194093
theorem B5678387 : Blo 1993435 5678387 := bstep (se 1 (by rfl) ⟨4258790, by rfl⟩ : syracuseStep 5678387 = 8517581) B8517581
theorem B3785591 : Blo 1993435 3785591 := bstep (se 1 (by rfl) ⟨2839193, by rfl⟩ : syracuseStep 3785591 = 5678387) B5678387
theorem B2523727 : Blo 1993435 2523727 := bstep (se 1 (by rfl) ⟨1892795, by rfl⟩ : syracuseStep 2523727 = 3785591) B3785591
theorem B3364969 : Blo 1993435 3364969 := bstep (se 2 (by rfl) ⟨1261863, by rfl⟩ : syracuseStep 3364969 = 2523727) B2523727
theorem B4486625 : Blo 1993435 4486625 := bstep (se 2 (by rfl) ⟨1682484, by rfl⟩ : syracuseStep 4486625 = 3364969) B3364969
theorem B2991083 : Blo 1993435 2991083 := bstep (se 1 (by rfl) ⟨2243312, by rfl⟩ : syracuseStep 2991083 = 4486625) B4486625
theorem B1994055 : Blo 1993435 1994055 := bstep (se 1 (by rfl) ⟨1495541, by rfl⟩ : syracuseStep 1994055 = 2991083) B2991083
theorem B2243317 : Blo 1993435 2243317 := bbase (se 5 (by rfl) ⟨105155, by rfl⟩ : syracuseStep 2243317 = 210311) (by norm_num)
theorem B2991089 : Blo 1993435 2991089 := bstep (se 2 (by rfl) ⟨1121658, by rfl⟩ : syracuseStep 2991089 = 2243317) B2243317
theorem B1994059 : Blo 1993435 1994059 := bstep (se 1 (by rfl) ⟨1495544, by rfl⟩ : syracuseStep 1994059 = 2991089) B2991089
theorem B2523737 : Blo 1993435 2523737 := bbase (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) (by norm_num)
theorem B6729965 : Blo 1993435 6729965 := bstep (se 3 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 6729965 = 2523737) B2523737
theorem B4486643 : Blo 1993435 4486643 := bstep (se 1 (by rfl) ⟨3364982, by rfl⟩ : syracuseStep 4486643 = 6729965) B6729965
theorem B2991095 : Blo 1993435 2991095 := bstep (se 1 (by rfl) ⟨2243321, by rfl⟩ : syracuseStep 2991095 = 4486643) B4486643
theorem B1994063 : Blo 1993435 1994063 := bstep (se 1 (by rfl) ⟨1495547, by rfl⟩ : syracuseStep 1994063 = 2991095) B2991095
theorem B2991101 : Blo 1993435 2991101 := bbase (se 3 (by rfl) ⟨560831, by rfl⟩ : syracuseStep 2991101 = 1121663) (by norm_num)
theorem B1994067 : Blo 1993435 1994067 := bstep (se 1 (by rfl) ⟨1495550, by rfl⟩ : syracuseStep 1994067 = 2991101) B2991101
theorem B4486661 : Blo 1993435 4486661 := bbase (se 4 (by rfl) ⟨420624, by rfl⟩ : syracuseStep 4486661 = 841249) (by norm_num)
theorem B2991107 : Blo 1993435 2991107 := bstep (se 1 (by rfl) ⟨2243330, by rfl⟩ : syracuseStep 2991107 = 4486661) B4486661
theorem B1994071 : Blo 1993435 1994071 := bstep (se 1 (by rfl) ⟨1495553, by rfl⟩ : syracuseStep 1994071 = 2991107) B2991107
theorem B3785629 : Blo 1993435 3785629 := bbase (se 3 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 3785629 = 1419611) (by norm_num)
theorem B5047505 : Blo 1993435 5047505 := bstep (se 2 (by rfl) ⟨1892814, by rfl⟩ : syracuseStep 5047505 = 3785629) B3785629
theorem B3365003 : Blo 1993435 3365003 := bstep (se 1 (by rfl) ⟨2523752, by rfl⟩ : syracuseStep 3365003 = 5047505) B5047505
theorem B2243335 : Blo 1993435 2243335 := bstep (se 1 (by rfl) ⟨1682501, by rfl⟩ : syracuseStep 2243335 = 3365003) B3365003
theorem B2991113 : Blo 1993435 2991113 := bstep (se 2 (by rfl) ⟨1121667, by rfl⟩ : syracuseStep 2991113 = 2243335) B2243335
theorem B1994075 : Blo 1993435 1994075 := bstep (se 1 (by rfl) ⟨1495556, by rfl⟩ : syracuseStep 1994075 = 2991113) B2991113
theorem B10095029 : Blo 1993435 10095029 := bbase (se 5 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 10095029 = 946409) (by norm_num)
theorem B6730019 : Blo 1993435 6730019 := bstep (se 1 (by rfl) ⟨5047514, by rfl⟩ : syracuseStep 6730019 = 10095029) B10095029
theorem B4486679 : Blo 1993435 4486679 := bstep (se 1 (by rfl) ⟨3365009, by rfl⟩ : syracuseStep 4486679 = 6730019) B6730019
theorem B2991119 : Blo 1993435 2991119 := bstep (se 1 (by rfl) ⟨2243339, by rfl⟩ : syracuseStep 2991119 = 4486679) B4486679
theorem B1994079 : Blo 1993435 1994079 := bstep (se 1 (by rfl) ⟨1495559, by rfl⟩ : syracuseStep 1994079 = 2991119) B2991119
theorem B2991125 : Blo 1993435 2991125 := bbase (se 6 (by rfl) ⟨70104, by rfl⟩ : syracuseStep 2991125 = 140209) (by norm_num)
theorem B1994083 : Blo 1993435 1994083 := bstep (se 1 (by rfl) ⟨1495562, by rfl⟩ : syracuseStep 1994083 = 2991125) B2991125
theorem B2336429 : Blo 1993435 2336429 := bbase (se 3 (by rfl) ⟨438080, by rfl⟩ : syracuseStep 2336429 = 876161) (by norm_num)
theorem B6230477 : Blo 1993435 6230477 := bstep (se 3 (by rfl) ⟨1168214, by rfl⟩ : syracuseStep 6230477 = 2336429) B2336429
theorem B16614605 : Blo 1993435 16614605 := bstep (se 3 (by rfl) ⟨3115238, by rfl⟩ : syracuseStep 16614605 = 6230477) B6230477
theorem B44305613 : Blo 1993435 44305613 := bstep (se 3 (by rfl) ⟨8307302, by rfl⟩ : syracuseStep 44305613 = 16614605) B16614605
theorem B29537075 : Blo 1993435 29537075 := bstep (se 1 (by rfl) ⟨22152806, by rfl⟩ : syracuseStep 29537075 = 44305613) B44305613
theorem B19691383 : Blo 1993435 19691383 := bstep (se 1 (by rfl) ⟨14768537, by rfl⟩ : syracuseStep 19691383 = 29537075) B29537075
theorem B26255177 : Blo 1993435 26255177 := bstep (se 2 (by rfl) ⟨9845691, by rfl⟩ : syracuseStep 26255177 = 19691383) B19691383
theorem B17503451 : Blo 1993435 17503451 := bstep (se 1 (by rfl) ⟨13127588, by rfl⟩ : syracuseStep 17503451 = 26255177) B26255177
theorem B11668967 : Blo 1993435 11668967 := bstep (se 1 (by rfl) ⟨8751725, by rfl⟩ : syracuseStep 11668967 = 17503451) B17503451
theorem B7779311 : Blo 1993435 7779311 := bstep (se 1 (by rfl) ⟨5834483, by rfl⟩ : syracuseStep 7779311 = 11668967) B11668967
theorem B5186207 : Blo 1993435 5186207 := bstep (se 1 (by rfl) ⟨3889655, by rfl⟩ : syracuseStep 5186207 = 7779311) B7779311
theorem B13829885 : Blo 1993435 13829885 := bstep (se 3 (by rfl) ⟨2593103, by rfl⟩ : syracuseStep 13829885 = 5186207) B5186207
theorem B9219923 : Blo 1993435 9219923 := bstep (se 1 (by rfl) ⟨6914942, by rfl⟩ : syracuseStep 9219923 = 13829885) B13829885
theorem B6146615 : Blo 1993435 6146615 := bstep (se 1 (by rfl) ⟨4609961, by rfl⟩ : syracuseStep 6146615 = 9219923) B9219923
theorem B16390973 : Blo 1993435 16390973 := bstep (se 3 (by rfl) ⟨3073307, by rfl⟩ : syracuseStep 16390973 = 6146615) B6146615
theorem B10927315 : Blo 1993435 10927315 := bstep (se 1 (by rfl) ⟨8195486, by rfl⟩ : syracuseStep 10927315 = 16390973) B16390973
theorem B14569753 : Blo 1993435 14569753 := bstep (se 2 (by rfl) ⟨5463657, by rfl⟩ : syracuseStep 14569753 = 10927315) B10927315
theorem B19426337 : Blo 1993435 19426337 := bstep (se 2 (by rfl) ⟨7284876, by rfl⟩ : syracuseStep 19426337 = 14569753) B14569753
theorem B12950891 : Blo 1993435 12950891 := bstep (se 1 (by rfl) ⟨9713168, by rfl⟩ : syracuseStep 12950891 = 19426337) B19426337
theorem B8633927 : Blo 1993435 8633927 := bstep (se 1 (by rfl) ⟨6475445, by rfl⟩ : syracuseStep 8633927 = 12950891) B12950891
theorem B23023805 : Blo 1993435 23023805 := bstep (se 3 (by rfl) ⟨4316963, by rfl⟩ : syracuseStep 23023805 = 8633927) B8633927
theorem B61396813 : Blo 1993435 61396813 := bstep (se 3 (by rfl) ⟨11511902, by rfl⟩ : syracuseStep 61396813 = 23023805) B23023805
theorem B81862417 : Blo 1993435 81862417 := bstep (se 2 (by rfl) ⟨30698406, by rfl⟩ : syracuseStep 81862417 = 61396813) B61396813
theorem B109149889 : Blo 1993435 109149889 := bstep (se 2 (by rfl) ⟨40931208, by rfl⟩ : syracuseStep 109149889 = 81862417) B81862417
theorem B145533185 : Blo 1993435 145533185 := bstep (se 2 (by rfl) ⟨54574944, by rfl⟩ : syracuseStep 145533185 = 109149889) B109149889
theorem B97022123 : Blo 1993435 97022123 := bstep (se 1 (by rfl) ⟨72766592, by rfl⟩ : syracuseStep 97022123 = 145533185) B145533185
theorem B64681415 : Blo 1993435 64681415 := bstep (se 1 (by rfl) ⟨48511061, by rfl⟩ : syracuseStep 64681415 = 97022123) B97022123
theorem B43120943 : Blo 1993435 43120943 := bstep (se 1 (by rfl) ⟨32340707, by rfl⟩ : syracuseStep 43120943 = 64681415) B64681415
theorem B28747295 : Blo 1993435 28747295 := bstep (se 1 (by rfl) ⟨21560471, by rfl⟩ : syracuseStep 28747295 = 43120943) B43120943
theorem B19164863 : Blo 1993435 19164863 := bstep (se 1 (by rfl) ⟨14373647, by rfl⟩ : syracuseStep 19164863 = 28747295) B28747295
theorem B12776575 : Blo 1993435 12776575 := bstep (se 1 (by rfl) ⟨9582431, by rfl⟩ : syracuseStep 12776575 = 19164863) B19164863
theorem B17035433 : Blo 1993435 17035433 := bstep (se 2 (by rfl) ⟨6388287, by rfl⟩ : syracuseStep 17035433 = 12776575) B12776575
theorem B11356955 : Blo 1993435 11356955 := bstep (se 1 (by rfl) ⟨8517716, by rfl⟩ : syracuseStep 11356955 = 17035433) B17035433
theorem B7571303 : Blo 1993435 7571303 := bstep (se 1 (by rfl) ⟨5678477, by rfl⟩ : syracuseStep 7571303 = 11356955) B11356955
theorem B5047535 : Blo 1993435 5047535 := bstep (se 1 (by rfl) ⟨3785651, by rfl⟩ : syracuseStep 5047535 = 7571303) B7571303
theorem B3365023 : Blo 1993435 3365023 := bstep (se 1 (by rfl) ⟨2523767, by rfl⟩ : syracuseStep 3365023 = 5047535) B5047535
theorem B4486697 : Blo 1993435 4486697 := bstep (se 2 (by rfl) ⟨1682511, by rfl⟩ : syracuseStep 4486697 = 3365023) B3365023
theorem B2991131 : Blo 1993435 2991131 := bstep (se 1 (by rfl) ⟨2243348, by rfl⟩ : syracuseStep 2991131 = 4486697) B4486697
theorem B1994087 : Blo 1993435 1994087 := bstep (se 1 (by rfl) ⟨1495565, by rfl⟩ : syracuseStep 1994087 = 2991131) B2991131
theorem B2243353 : Blo 1993435 2243353 := bbase (se 2 (by rfl) ⟨841257, by rfl⟩ : syracuseStep 2243353 = 1682515) (by norm_num)
theorem B2991137 : Blo 1993435 2991137 := bstep (se 2 (by rfl) ⟨1121676, by rfl⟩ : syracuseStep 2991137 = 2243353) B2243353
theorem B1994091 : Blo 1993435 1994091 := bstep (se 1 (by rfl) ⟨1495568, by rfl⟩ : syracuseStep 1994091 = 2991137) B2991137
theorem B7571333 : Blo 1993435 7571333 := bbase (se 4 (by rfl) ⟨709812, by rfl⟩ : syracuseStep 7571333 = 1419625) (by norm_num)
theorem B5047555 : Blo 1993435 5047555 := bstep (se 1 (by rfl) ⟨3785666, by rfl⟩ : syracuseStep 5047555 = 7571333) B7571333
theorem B6730073 : Blo 1993435 6730073 := bstep (se 2 (by rfl) ⟨2523777, by rfl⟩ : syracuseStep 6730073 = 5047555) B5047555
theorem B4486715 : Blo 1993435 4486715 := bstep (se 1 (by rfl) ⟨3365036, by rfl⟩ : syracuseStep 4486715 = 6730073) B6730073
theorem B2991143 : Blo 1993435 2991143 := bstep (se 1 (by rfl) ⟨2243357, by rfl⟩ : syracuseStep 2991143 = 4486715) B4486715
theorem B1994095 : Blo 1993435 1994095 := bstep (se 1 (by rfl) ⟨1495571, by rfl⟩ : syracuseStep 1994095 = 2991143) B2991143
theorem B2991149 : Blo 1993435 2991149 := bbase (se 3 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 2991149 = 1121681) (by norm_num)
theorem B1994099 : Blo 1993435 1994099 := bstep (se 1 (by rfl) ⟨1495574, by rfl⟩ : syracuseStep 1994099 = 2991149) B2991149
theorem B4486733 : Blo 1993435 4486733 := bbase (se 3 (by rfl) ⟨841262, by rfl⟩ : syracuseStep 4486733 = 1682525) (by norm_num)
theorem B2991155 : Blo 1993435 2991155 := bstep (se 1 (by rfl) ⟨2243366, by rfl⟩ : syracuseStep 2991155 = 4486733) B4486733
theorem B1994103 : Blo 1993435 1994103 := bstep (se 1 (by rfl) ⟨1495577, by rfl⟩ : syracuseStep 1994103 = 2991155) B2991155
theorem B2523793 : Blo 1993435 2523793 := bbase (se 2 (by rfl) ⟨946422, by rfl⟩ : syracuseStep 2523793 = 1892845) (by norm_num)
theorem B3365057 : Blo 1993435 3365057 := bstep (se 2 (by rfl) ⟨1261896, by rfl⟩ : syracuseStep 3365057 = 2523793) B2523793
theorem B2243371 : Blo 1993435 2243371 := bstep (se 1 (by rfl) ⟨1682528, by rfl⟩ : syracuseStep 2243371 = 3365057) B3365057
theorem B2991161 : Blo 1993435 2991161 := bstep (se 2 (by rfl) ⟨1121685, by rfl⟩ : syracuseStep 2991161 = 2243371) B2243371
theorem B1994107 : Blo 1993435 1994107 := bstep (se 1 (by rfl) ⟨1495580, by rfl⟩ : syracuseStep 1994107 = 2991161) B2991161
theorem B4258909 : Blo 1993435 4258909 := bbase (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) (by norm_num)
theorem B22714181 : Blo 1993435 22714181 := bstep (se 4 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 22714181 = 4258909) B4258909
theorem B15142787 : Blo 1993435 15142787 := bstep (se 1 (by rfl) ⟨11357090, by rfl⟩ : syracuseStep 15142787 = 22714181) B22714181
theorem B10095191 : Blo 1993435 10095191 := bstep (se 1 (by rfl) ⟨7571393, by rfl⟩ : syracuseStep 10095191 = 15142787) B15142787
theorem B6730127 : Blo 1993435 6730127 := bstep (se 1 (by rfl) ⟨5047595, by rfl⟩ : syracuseStep 6730127 = 10095191) B10095191
theorem B4486751 : Blo 1993435 4486751 := bstep (se 1 (by rfl) ⟨3365063, by rfl⟩ : syracuseStep 4486751 = 6730127) B6730127
theorem B2991167 : Blo 1993435 2991167 := bstep (se 1 (by rfl) ⟨2243375, by rfl⟩ : syracuseStep 2991167 = 4486751) B4486751
theorem B1994111 : Blo 1993435 1994111 := bstep (se 1 (by rfl) ⟨1495583, by rfl⟩ : syracuseStep 1994111 = 2991167) B2991167
theorem B2991173 : Blo 1993435 2991173 := bbase (se 4 (by rfl) ⟨280422, by rfl⟩ : syracuseStep 2991173 = 560845) (by norm_num)
theorem B1994115 : Blo 1993435 1994115 := bstep (se 1 (by rfl) ⟨1495586, by rfl⟩ : syracuseStep 1994115 = 2991173) B2991173
theorem B3365077 : Blo 1993435 3365077 := bbase (se 7 (by rfl) ⟨39434, by rfl⟩ : syracuseStep 3365077 = 78869) (by norm_num)
theorem B4486769 : Blo 1993435 4486769 := bstep (se 2 (by rfl) ⟨1682538, by rfl⟩ : syracuseStep 4486769 = 3365077) B3365077
theorem B2991179 : Blo 1993435 2991179 := bstep (se 1 (by rfl) ⟨2243384, by rfl⟩ : syracuseStep 2991179 = 4486769) B4486769
theorem B1994119 : Blo 1993435 1994119 := bstep (se 1 (by rfl) ⟨1495589, by rfl⟩ : syracuseStep 1994119 = 2991179) B2991179
theorem B2243389 : Blo 1993435 2243389 := bbase (se 3 (by rfl) ⟨420635, by rfl⟩ : syracuseStep 2243389 = 841271) (by norm_num)
theorem B2991185 : Blo 1993435 2991185 := bstep (se 2 (by rfl) ⟨1121694, by rfl⟩ : syracuseStep 2991185 = 2243389) B2243389
theorem B1994123 : Blo 1993435 1994123 := bstep (se 1 (by rfl) ⟨1495592, by rfl⟩ : syracuseStep 1994123 = 2991185) B2991185
theorem B6730181 : Blo 1993435 6730181 := bbase (se 4 (by rfl) ⟨630954, by rfl⟩ : syracuseStep 6730181 = 1261909) (by norm_num)
theorem B4486787 : Blo 1993435 4486787 := bstep (se 1 (by rfl) ⟨3365090, by rfl⟩ : syracuseStep 4486787 = 6730181) B6730181
theorem B2991191 : Blo 1993435 2991191 := bstep (se 1 (by rfl) ⟨2243393, by rfl⟩ : syracuseStep 2991191 = 4486787) B4486787
theorem B1994127 : Blo 1993435 1994127 := bstep (se 1 (by rfl) ⟨1495595, by rfl⟩ : syracuseStep 1994127 = 2991191) B2991191
theorem B2991197 : Blo 1993435 2991197 := bbase (se 3 (by rfl) ⟨560849, by rfl⟩ : syracuseStep 2991197 = 1121699) (by norm_num)
theorem B1994131 : Blo 1993435 1994131 := bstep (se 1 (by rfl) ⟨1495598, by rfl⟩ : syracuseStep 1994131 = 2991197) B2991197
theorem B4486805 : Blo 1993435 4486805 := bbase (se 6 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 4486805 = 210319) (by norm_num)
theorem B2991203 : Blo 1993435 2991203 := bstep (se 1 (by rfl) ⟨2243402, by rfl⟩ : syracuseStep 2991203 = 4486805) B4486805
theorem B1994135 : Blo 1993435 1994135 := bstep (se 1 (by rfl) ⟨1495601, by rfl⟩ : syracuseStep 1994135 = 2991203) B2991203
theorem B2129485 : Blo 1993435 2129485 := bbase (se 3 (by rfl) ⟨399278, by rfl⟩ : syracuseStep 2129485 = 798557) (by norm_num)
theorem B2839313 : Blo 1993435 2839313 := bstep (se 2 (by rfl) ⟨1064742, by rfl⟩ : syracuseStep 2839313 = 2129485) B2129485
theorem B7571501 : Blo 1993435 7571501 := bstep (se 3 (by rfl) ⟨1419656, by rfl⟩ : syracuseStep 7571501 = 2839313) B2839313
theorem B5047667 : Blo 1993435 5047667 := bstep (se 1 (by rfl) ⟨3785750, by rfl⟩ : syracuseStep 5047667 = 7571501) B7571501
theorem B3365111 : Blo 1993435 3365111 := bstep (se 1 (by rfl) ⟨2523833, by rfl⟩ : syracuseStep 3365111 = 5047667) B5047667
theorem B2243407 : Blo 1993435 2243407 := bstep (se 1 (by rfl) ⟨1682555, by rfl⟩ : syracuseStep 2243407 = 3365111) B3365111
theorem B2991209 : Blo 1993435 2991209 := bstep (se 2 (by rfl) ⟨1121703, by rfl⟩ : syracuseStep 2991209 = 2243407) B2243407
theorem B1994139 : Blo 1993435 1994139 := bstep (se 1 (by rfl) ⟨1495604, by rfl⟩ : syracuseStep 1994139 = 2991209) B2991209
theorem B7674821 : Blo 1993435 7674821 := bbase (se 4 (by rfl) ⟨719514, by rfl⟩ : syracuseStep 7674821 = 1439029) (by norm_num)
theorem B5116547 : Blo 1993435 5116547 := bstep (se 1 (by rfl) ⟨3837410, by rfl⟩ : syracuseStep 5116547 = 7674821) B7674821
theorem B13644125 : Blo 1993435 13644125 := bstep (se 3 (by rfl) ⟨2558273, by rfl⟩ : syracuseStep 13644125 = 5116547) B5116547
theorem B9096083 : Blo 1993435 9096083 := bstep (se 1 (by rfl) ⟨6822062, by rfl⟩ : syracuseStep 9096083 = 13644125) B13644125
theorem B6064055 : Blo 1993435 6064055 := bstep (se 1 (by rfl) ⟨4548041, by rfl⟩ : syracuseStep 6064055 = 9096083) B9096083
theorem B4042703 : Blo 1993435 4042703 := bstep (se 1 (by rfl) ⟨3032027, by rfl⟩ : syracuseStep 4042703 = 6064055) B6064055
theorem B2695135 : Blo 1993435 2695135 := bstep (se 1 (by rfl) ⟨2021351, by rfl⟩ : syracuseStep 2695135 = 4042703) B4042703
theorem B3593513 : Blo 1993435 3593513 := bstep (se 2 (by rfl) ⟨1347567, by rfl⟩ : syracuseStep 3593513 = 2695135) B2695135
theorem B2395675 : Blo 1993435 2395675 := bstep (se 1 (by rfl) ⟨1796756, by rfl⟩ : syracuseStep 2395675 = 3593513) B3593513
theorem B12776933 : Blo 1993435 12776933 := bstep (se 4 (by rfl) ⟨1197837, by rfl⟩ : syracuseStep 12776933 = 2395675) B2395675
theorem B8517955 : Blo 1993435 8517955 := bstep (se 1 (by rfl) ⟨6388466, by rfl⟩ : syracuseStep 8517955 = 12776933) B12776933
theorem B11357273 : Blo 1993435 11357273 := bstep (se 2 (by rfl) ⟨4258977, by rfl⟩ : syracuseStep 11357273 = 8517955) B8517955
theorem B7571515 : Blo 1993435 7571515 := bstep (se 1 (by rfl) ⟨5678636, by rfl⟩ : syracuseStep 7571515 = 11357273) B11357273
theorem B10095353 : Blo 1993435 10095353 := bstep (se 2 (by rfl) ⟨3785757, by rfl⟩ : syracuseStep 10095353 = 7571515) B7571515
theorem B6730235 : Blo 1993435 6730235 := bstep (se 1 (by rfl) ⟨5047676, by rfl⟩ : syracuseStep 6730235 = 10095353) B10095353
theorem B4486823 : Blo 1993435 4486823 := bstep (se 1 (by rfl) ⟨3365117, by rfl⟩ : syracuseStep 4486823 = 6730235) B6730235
theorem B2991215 : Blo 1993435 2991215 := bstep (se 1 (by rfl) ⟨2243411, by rfl⟩ : syracuseStep 2991215 = 4486823) B4486823
theorem B1994143 : Blo 1993435 1994143 := bstep (se 1 (by rfl) ⟨1495607, by rfl⟩ : syracuseStep 1994143 = 2991215) B2991215
theorem B2991221 : Blo 1993435 2991221 := bbase (se 5 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 2991221 = 280427) (by norm_num)
theorem B1994147 : Blo 1993435 1994147 := bstep (se 1 (by rfl) ⟨1495610, by rfl⟩ : syracuseStep 1994147 = 2991221) B2991221
theorem B3785773 : Blo 1993435 3785773 := bbase (se 3 (by rfl) ⟨709832, by rfl⟩ : syracuseStep 3785773 = 1419665) (by norm_num)
theorem B5047697 : Blo 1993435 5047697 := bstep (se 2 (by rfl) ⟨1892886, by rfl⟩ : syracuseStep 5047697 = 3785773) B3785773
theorem B3365131 : Blo 1993435 3365131 := bstep (se 1 (by rfl) ⟨2523848, by rfl⟩ : syracuseStep 3365131 = 5047697) B5047697
theorem B4486841 : Blo 1993435 4486841 := bstep (se 2 (by rfl) ⟨1682565, by rfl⟩ : syracuseStep 4486841 = 3365131) B3365131
theorem B2991227 : Blo 1993435 2991227 := bstep (se 1 (by rfl) ⟨2243420, by rfl⟩ : syracuseStep 2991227 = 4486841) B4486841
theorem B1994151 : Blo 1993435 1994151 := bstep (se 1 (by rfl) ⟨1495613, by rfl⟩ : syracuseStep 1994151 = 2991227) B2991227
theorem B2243425 : Blo 1993435 2243425 := bbase (se 2 (by rfl) ⟨841284, by rfl⟩ : syracuseStep 2243425 = 1682569) (by norm_num)
theorem B2991233 : Blo 1993435 2991233 := bstep (se 2 (by rfl) ⟨1121712, by rfl⟩ : syracuseStep 2991233 = 2243425) B2243425
theorem B1994155 : Blo 1993435 1994155 := bstep (se 1 (by rfl) ⟨1495616, by rfl⟩ : syracuseStep 1994155 = 2991233) B2991233
theorem B5047717 : Blo 1993435 5047717 := bbase (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) (by norm_num)
theorem B6730289 : Blo 1993435 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B4486859 : Blo 1993435 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B2991239 : Blo 1993435 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B1994159 : Blo 1993435 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B2991245 : Blo 1993435 2991245 := bbase (se 3 (by rfl) ⟨560858, by rfl⟩ : syracuseStep 2991245 = 1121717) (by norm_num)
theorem B1994163 : Blo 1993435 1994163 := bstep (se 1 (by rfl) ⟨1495622, by rfl⟩ : syracuseStep 1994163 = 2991245) B2991245
theorem B4486877 : Blo 1993435 4486877 := bbase (se 3 (by rfl) ⟨841289, by rfl⟩ : syracuseStep 4486877 = 1682579) (by norm_num)
theorem B2991251 : Blo 1993435 2991251 := bstep (se 1 (by rfl) ⟨2243438, by rfl⟩ : syracuseStep 2991251 = 4486877) B4486877
theorem B1994167 : Blo 1993435 1994167 := bstep (se 1 (by rfl) ⟨1495625, by rfl⟩ : syracuseStep 1994167 = 2991251) B2991251
theorem B3365165 : Blo 1993435 3365165 := bbase (se 3 (by rfl) ⟨630968, by rfl⟩ : syracuseStep 3365165 = 1261937) (by norm_num)
theorem B2243443 : Blo 1993435 2243443 := bstep (se 1 (by rfl) ⟨1682582, by rfl⟩ : syracuseStep 2243443 = 3365165) B3365165
theorem B2991257 : Blo 1993435 2991257 := bstep (se 2 (by rfl) ⟨1121721, by rfl⟩ : syracuseStep 2991257 = 2243443) B2243443
theorem B1994171 : Blo 1993435 1994171 := bstep (se 1 (by rfl) ⟨1495628, by rfl⟩ : syracuseStep 1994171 = 2991257) B2991257
theorem B38331413 : Blo 1993435 38331413 := bbase (se 6 (by rfl) ⟨898392, by rfl⟩ : syracuseStep 38331413 = 1796785) (by norm_num)
theorem B25554275 : Blo 1993435 25554275 := bstep (se 1 (by rfl) ⟨19165706, by rfl⟩ : syracuseStep 25554275 = 38331413) B38331413
theorem B17036183 : Blo 1993435 17036183 := bstep (se 1 (by rfl) ⟨12777137, by rfl⟩ : syracuseStep 17036183 = 25554275) B25554275
theorem B11357455 : Blo 1993435 11357455 := bstep (se 1 (by rfl) ⟨8518091, by rfl⟩ : syracuseStep 11357455 = 17036183) B17036183
theorem B15143273 : Blo 1993435 15143273 := bstep (se 2 (by rfl) ⟨5678727, by rfl⟩ : syracuseStep 15143273 = 11357455) B11357455
theorem B10095515 : Blo 1993435 10095515 := bstep (se 1 (by rfl) ⟨7571636, by rfl⟩ : syracuseStep 10095515 = 15143273) B15143273
theorem B6730343 : Blo 1993435 6730343 := bstep (se 1 (by rfl) ⟨5047757, by rfl⟩ : syracuseStep 6730343 = 10095515) B10095515
theorem B4486895 : Blo 1993435 4486895 := bstep (se 1 (by rfl) ⟨3365171, by rfl⟩ : syracuseStep 4486895 = 6730343) B6730343
theorem B2991263 : Blo 1993435 2991263 := bstep (se 1 (by rfl) ⟨2243447, by rfl⟩ : syracuseStep 2991263 = 4486895) B4486895
theorem B1994175 : Blo 1993435 1994175 := bstep (se 1 (by rfl) ⟨1495631, by rfl⟩ : syracuseStep 1994175 = 2991263) B2991263
theorem B2991269 : Blo 1993435 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B1994179 : Blo 1993435 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B2523889 : Blo 1993435 2523889 := bbase (se 2 (by rfl) ⟨946458, by rfl⟩ : syracuseStep 2523889 = 1892917) (by norm_num)
theorem B3365185 : Blo 1993435 3365185 := bstep (se 2 (by rfl) ⟨1261944, by rfl⟩ : syracuseStep 3365185 = 2523889) B2523889
theorem B4486913 : Blo 1993435 4486913 := bstep (se 2 (by rfl) ⟨1682592, by rfl⟩ : syracuseStep 4486913 = 3365185) B3365185
theorem B2991275 : Blo 1993435 2991275 := bstep (se 1 (by rfl) ⟨2243456, by rfl⟩ : syracuseStep 2991275 = 4486913) B4486913
theorem B1994183 : Blo 1993435 1994183 := bstep (se 1 (by rfl) ⟨1495637, by rfl⟩ : syracuseStep 1994183 = 2991275) B2991275
theorem B2243461 : Blo 1993435 2243461 := bbase (se 4 (by rfl) ⟨210324, by rfl⟩ : syracuseStep 2243461 = 420649) (by norm_num)
theorem B2991281 : Blo 1993435 2991281 := bstep (se 2 (by rfl) ⟨1121730, by rfl⟩ : syracuseStep 2991281 = 2243461) B2243461
theorem B1994187 : Blo 1993435 1994187 := bstep (se 1 (by rfl) ⟨1495640, by rfl⟩ : syracuseStep 1994187 = 2991281) B2991281
theorem B3032101 : Blo 1993435 3032101 := bbase (se 4 (by rfl) ⟨284259, by rfl⟩ : syracuseStep 3032101 = 568519) (by norm_num)
theorem B4042801 : Blo 1993435 4042801 := bstep (se 2 (by rfl) ⟨1516050, by rfl⟩ : syracuseStep 4042801 = 3032101) B3032101
theorem B5390401 : Blo 1993435 5390401 := bstep (se 2 (by rfl) ⟨2021400, by rfl⟩ : syracuseStep 5390401 = 4042801) B4042801
theorem B7187201 : Blo 1993435 7187201 := bstep (se 2 (by rfl) ⟨2695200, by rfl⟩ : syracuseStep 7187201 = 5390401) B5390401
theorem B4791467 : Blo 1993435 4791467 := bstep (se 1 (by rfl) ⟨3593600, by rfl⟩ : syracuseStep 4791467 = 7187201) B7187201
theorem B3194311 : Blo 1993435 3194311 := bstep (se 1 (by rfl) ⟨2395733, by rfl⟩ : syracuseStep 3194311 = 4791467) B4791467
theorem B4259081 : Blo 1993435 4259081 := bstep (se 2 (by rfl) ⟨1597155, by rfl⟩ : syracuseStep 4259081 = 3194311) B3194311
theorem B2839387 : Blo 1993435 2839387 := bstep (se 1 (by rfl) ⟨2129540, by rfl⟩ : syracuseStep 2839387 = 4259081) B4259081
theorem B3785849 : Blo 1993435 3785849 := bstep (se 2 (by rfl) ⟨1419693, by rfl⟩ : syracuseStep 3785849 = 2839387) B2839387
theorem B2523899 : Blo 1993435 2523899 := bstep (se 1 (by rfl) ⟨1892924, by rfl⟩ : syracuseStep 2523899 = 3785849) B3785849
theorem B6730397 : Blo 1993435 6730397 := bstep (se 3 (by rfl) ⟨1261949, by rfl⟩ : syracuseStep 6730397 = 2523899) B2523899
theorem B4486931 : Blo 1993435 4486931 := bstep (se 1 (by rfl) ⟨3365198, by rfl⟩ : syracuseStep 4486931 = 6730397) B6730397
theorem B2991287 : Blo 1993435 2991287 := bstep (se 1 (by rfl) ⟨2243465, by rfl⟩ : syracuseStep 2991287 = 4486931) B4486931
theorem B1994191 : Blo 1993435 1994191 := bstep (se 1 (by rfl) ⟨1495643, by rfl⟩ : syracuseStep 1994191 = 2991287) B2991287
theorem B2991293 : Blo 1993435 2991293 := bbase (se 3 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 2991293 = 1121735) (by norm_num)
theorem B1994195 : Blo 1993435 1994195 := bstep (se 1 (by rfl) ⟨1495646, by rfl⟩ : syracuseStep 1994195 = 2991293) B2991293
theorem B4486949 : Blo 1993435 4486949 := bbase (se 4 (by rfl) ⟨420651, by rfl⟩ : syracuseStep 4486949 = 841303) (by norm_num)
theorem B2991299 : Blo 1993435 2991299 := bstep (se 1 (by rfl) ⟨2243474, by rfl⟩ : syracuseStep 2991299 = 4486949) B4486949
theorem B1994199 : Blo 1993435 1994199 := bstep (se 1 (by rfl) ⟨1495649, by rfl⟩ : syracuseStep 1994199 = 2991299) B2991299
theorem B5047829 : Blo 1993435 5047829 := bbase (se 6 (by rfl) ⟨118308, by rfl⟩ : syracuseStep 5047829 = 236617) (by norm_num)
theorem B3365219 : Blo 1993435 3365219 := bstep (se 1 (by rfl) ⟨2523914, by rfl⟩ : syracuseStep 3365219 = 5047829) B5047829
theorem B2243479 : Blo 1993435 2243479 := bstep (se 1 (by rfl) ⟨1682609, by rfl⟩ : syracuseStep 2243479 = 3365219) B3365219
theorem B2991305 : Blo 1993435 2991305 := bstep (se 2 (by rfl) ⟨1121739, by rfl⟩ : syracuseStep 2991305 = 2243479) B2243479
theorem B1994203 : Blo 1993435 1994203 := bstep (se 1 (by rfl) ⟨1495652, by rfl⟩ : syracuseStep 1994203 = 2991305) B2991305
theorem B8518229 : Blo 1993435 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B5678819 : Blo 1993435 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B3785879 : Blo 1993435 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B10095677 : Blo 1993435 10095677 := bstep (se 3 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 10095677 = 3785879) B3785879
theorem B6730451 : Blo 1993435 6730451 := bstep (se 1 (by rfl) ⟨5047838, by rfl⟩ : syracuseStep 6730451 = 10095677) B10095677
theorem B4486967 : Blo 1993435 4486967 := bstep (se 1 (by rfl) ⟨3365225, by rfl⟩ : syracuseStep 4486967 = 6730451) B6730451
theorem B2991311 : Blo 1993435 2991311 := bstep (se 1 (by rfl) ⟨2243483, by rfl⟩ : syracuseStep 2991311 = 4486967) B4486967
theorem B1994207 : Blo 1993435 1994207 := bstep (se 1 (by rfl) ⟨1495655, by rfl⟩ : syracuseStep 1994207 = 2991311) B2991311
theorem B2991317 : Blo 1993435 2991317 := bbase (se 7 (by rfl) ⟨35054, by rfl⟩ : syracuseStep 2991317 = 70109) (by norm_num)
theorem B1994211 : Blo 1993435 1994211 := bstep (se 1 (by rfl) ⟨1495658, by rfl⟩ : syracuseStep 1994211 = 2991317) B2991317
theorem B2839421 : Blo 1993435 2839421 := bbase (se 3 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 2839421 = 1064783) (by norm_num)
theorem B7571789 : Blo 1993435 7571789 := bstep (se 3 (by rfl) ⟨1419710, by rfl⟩ : syracuseStep 7571789 = 2839421) B2839421
theorem B5047859 : Blo 1993435 5047859 := bstep (se 1 (by rfl) ⟨3785894, by rfl⟩ : syracuseStep 5047859 = 7571789) B7571789
theorem B3365239 : Blo 1993435 3365239 := bstep (se 1 (by rfl) ⟨2523929, by rfl⟩ : syracuseStep 3365239 = 5047859) B5047859
theorem B4486985 : Blo 1993435 4486985 := bstep (se 2 (by rfl) ⟨1682619, by rfl⟩ : syracuseStep 4486985 = 3365239) B3365239
theorem B2991323 : Blo 1993435 2991323 := bstep (se 1 (by rfl) ⟨2243492, by rfl⟩ : syracuseStep 2991323 = 4486985) B4486985
theorem B1994215 : Blo 1993435 1994215 := bstep (se 1 (by rfl) ⟨1495661, by rfl⟩ : syracuseStep 1994215 = 2991323) B2991323
theorem B2243497 : Blo 1993435 2243497 := bbase (se 2 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 2243497 = 1682623) (by norm_num)
theorem B2991329 : Blo 1993435 2991329 := bstep (se 2 (by rfl) ⟨1121748, by rfl⟩ : syracuseStep 2991329 = 2243497) B2243497
theorem B1994219 : Blo 1993435 1994219 := bstep (se 1 (by rfl) ⟨1495664, by rfl⟩ : syracuseStep 1994219 = 2991329) B2991329
theorem B3032149 : Blo 1993435 3032149 := bbase (se 8 (by rfl) ⟨17766, by rfl⟩ : syracuseStep 3032149 = 35533) (by norm_num)
theorem B4042865 : Blo 1993435 4042865 := bstep (se 2 (by rfl) ⟨1516074, by rfl⟩ : syracuseStep 4042865 = 3032149) B3032149
theorem B2695243 : Blo 1993435 2695243 := bstep (se 1 (by rfl) ⟨2021432, by rfl⟩ : syracuseStep 2695243 = 4042865) B4042865
theorem B3593657 : Blo 1993435 3593657 := bstep (se 2 (by rfl) ⟨1347621, by rfl⟩ : syracuseStep 3593657 = 2695243) B2695243
theorem B9583085 : Blo 1993435 9583085 := bstep (se 3 (by rfl) ⟨1796828, by rfl⟩ : syracuseStep 9583085 = 3593657) B3593657
theorem B6388723 : Blo 1993435 6388723 := bstep (se 1 (by rfl) ⟨4791542, by rfl⟩ : syracuseStep 6388723 = 9583085) B9583085
theorem B8518297 : Blo 1993435 8518297 := bstep (se 2 (by rfl) ⟨3194361, by rfl⟩ : syracuseStep 8518297 = 6388723) B6388723
theorem B11357729 : Blo 1993435 11357729 := bstep (se 2 (by rfl) ⟨4259148, by rfl⟩ : syracuseStep 11357729 = 8518297) B8518297
theorem B7571819 : Blo 1993435 7571819 := bstep (se 1 (by rfl) ⟨5678864, by rfl⟩ : syracuseStep 7571819 = 11357729) B11357729
theorem B5047879 : Blo 1993435 5047879 := bstep (se 1 (by rfl) ⟨3785909, by rfl⟩ : syracuseStep 5047879 = 7571819) B7571819
theorem B6730505 : Blo 1993435 6730505 := bstep (se 2 (by rfl) ⟨2523939, by rfl⟩ : syracuseStep 6730505 = 5047879) B5047879
theorem B4487003 : Blo 1993435 4487003 := bstep (se 1 (by rfl) ⟨3365252, by rfl⟩ : syracuseStep 4487003 = 6730505) B6730505
theorem B2991335 : Blo 1993435 2991335 := bstep (se 1 (by rfl) ⟨2243501, by rfl⟩ : syracuseStep 2991335 = 4487003) B4487003
theorem B1994223 : Blo 1993435 1994223 := bstep (se 1 (by rfl) ⟨1495667, by rfl⟩ : syracuseStep 1994223 = 2991335) B2991335
theorem B2991341 : Blo 1993435 2991341 := bbase (se 3 (by rfl) ⟨560876, by rfl⟩ : syracuseStep 2991341 = 1121753) (by norm_num)
theorem B1994227 : Blo 1993435 1994227 := bstep (se 1 (by rfl) ⟨1495670, by rfl⟩ : syracuseStep 1994227 = 2991341) B2991341
theorem B4487021 : Blo 1993435 4487021 := bbase (se 3 (by rfl) ⟨841316, by rfl⟩ : syracuseStep 4487021 = 1682633) (by norm_num)
theorem B2991347 : Blo 1993435 2991347 := bstep (se 1 (by rfl) ⟨2243510, by rfl⟩ : syracuseStep 2991347 = 4487021) B4487021
theorem B1994231 : Blo 1993435 1994231 := bstep (se 1 (by rfl) ⟨1495673, by rfl⟩ : syracuseStep 1994231 = 2991347) B2991347
theorem B3785933 : Blo 1993435 3785933 := bbase (se 3 (by rfl) ⟨709862, by rfl⟩ : syracuseStep 3785933 = 1419725) (by norm_num)
theorem B2523955 : Blo 1993435 2523955 := bstep (se 1 (by rfl) ⟨1892966, by rfl⟩ : syracuseStep 2523955 = 3785933) B3785933
theorem B3365273 : Blo 1993435 3365273 := bstep (se 2 (by rfl) ⟨1261977, by rfl⟩ : syracuseStep 3365273 = 2523955) B2523955
theorem B2243515 : Blo 1993435 2243515 := bstep (se 1 (by rfl) ⟨1682636, by rfl⟩ : syracuseStep 2243515 = 3365273) B3365273
theorem B2991353 : Blo 1993435 2991353 := bstep (se 2 (by rfl) ⟨1121757, by rfl⟩ : syracuseStep 2991353 = 2243515) B2243515
theorem B1994235 : Blo 1993435 1994235 := bstep (se 1 (by rfl) ⟨1495676, by rfl⟩ : syracuseStep 1994235 = 2991353) B2991353
theorem B14374741 : Blo 1993435 14374741 := bbase (se 9 (by rfl) ⟨42113, by rfl⟩ : syracuseStep 14374741 = 84227) (by norm_num)
theorem B19166321 : Blo 1993435 19166321 := bstep (se 2 (by rfl) ⟨7187370, by rfl⟩ : syracuseStep 19166321 = 14374741) B14374741
theorem B51110189 : Blo 1993435 51110189 := bstep (se 3 (by rfl) ⟨9583160, by rfl⟩ : syracuseStep 51110189 = 19166321) B19166321
theorem B34073459 : Blo 1993435 34073459 := bstep (se 1 (by rfl) ⟨25555094, by rfl⟩ : syracuseStep 34073459 = 51110189) B51110189
theorem B22715639 : Blo 1993435 22715639 := bstep (se 1 (by rfl) ⟨17036729, by rfl⟩ : syracuseStep 22715639 = 34073459) B34073459
theorem B15143759 : Blo 1993435 15143759 := bstep (se 1 (by rfl) ⟨11357819, by rfl⟩ : syracuseStep 15143759 = 22715639) B22715639
theorem B10095839 : Blo 1993435 10095839 := bstep (se 1 (by rfl) ⟨7571879, by rfl⟩ : syracuseStep 10095839 = 15143759) B15143759
theorem B6730559 : Blo 1993435 6730559 := bstep (se 1 (by rfl) ⟨5047919, by rfl⟩ : syracuseStep 6730559 = 10095839) B10095839
theorem B4487039 : Blo 1993435 4487039 := bstep (se 1 (by rfl) ⟨3365279, by rfl⟩ : syracuseStep 4487039 = 6730559) B6730559
theorem B2991359 : Blo 1993435 2991359 := bstep (se 1 (by rfl) ⟨2243519, by rfl⟩ : syracuseStep 2991359 = 4487039) B4487039
theorem B1994239 : Blo 1993435 1994239 := bstep (se 1 (by rfl) ⟨1495679, by rfl⟩ : syracuseStep 1994239 = 2991359) B2991359
theorem B2991365 : Blo 1993435 2991365 := bbase (se 4 (by rfl) ⟨280440, by rfl⟩ : syracuseStep 2991365 = 560881) (by norm_num)
theorem B1994243 : Blo 1993435 1994243 := bstep (se 1 (by rfl) ⟨1495682, by rfl⟩ : syracuseStep 1994243 = 2991365) B2991365
theorem B3365293 : Blo 1993435 3365293 := bbase (se 3 (by rfl) ⟨630992, by rfl⟩ : syracuseStep 3365293 = 1261985) (by norm_num)
theorem B4487057 : Blo 1993435 4487057 := bstep (se 2 (by rfl) ⟨1682646, by rfl⟩ : syracuseStep 4487057 = 3365293) B3365293
theorem B2991371 : Blo 1993435 2991371 := bstep (se 1 (by rfl) ⟨2243528, by rfl⟩ : syracuseStep 2991371 = 4487057) B4487057
theorem B1994247 : Blo 1993435 1994247 := bstep (se 1 (by rfl) ⟨1495685, by rfl⟩ : syracuseStep 1994247 = 2991371) B2991371
theorem B2243533 : Blo 1993435 2243533 := bbase (se 3 (by rfl) ⟨420662, by rfl⟩ : syracuseStep 2243533 = 841325) (by norm_num)
theorem B2991377 : Blo 1993435 2991377 := bstep (se 2 (by rfl) ⟨1121766, by rfl⟩ : syracuseStep 2991377 = 2243533) B2243533
theorem B1994251 : Blo 1993435 1994251 := bstep (se 1 (by rfl) ⟨1495688, by rfl⟩ : syracuseStep 1994251 = 2991377) B2991377
theorem B6730613 : Blo 1993435 6730613 := bbase (se 5 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 6730613 = 630995) (by norm_num)
theorem B4487075 : Blo 1993435 4487075 := bstep (se 1 (by rfl) ⟨3365306, by rfl⟩ : syracuseStep 4487075 = 6730613) B6730613
theorem B2991383 : Blo 1993435 2991383 := bstep (se 1 (by rfl) ⟨2243537, by rfl⟩ : syracuseStep 2991383 = 4487075) B4487075
theorem B1994255 : Blo 1993435 1994255 := bstep (se 1 (by rfl) ⟨1495691, by rfl⟩ : syracuseStep 1994255 = 2991383) B2991383
theorem B2991389 : Blo 1993435 2991389 := bbase (se 3 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 2991389 = 1121771) (by norm_num)
theorem B1994259 : Blo 1993435 1994259 := bstep (se 1 (by rfl) ⟨1495694, by rfl⟩ : syracuseStep 1994259 = 2991389) B2991389
theorem B4487093 : Blo 1993435 4487093 := bbase (se 5 (by rfl) ⟨210332, by rfl⟩ : syracuseStep 4487093 = 420665) (by norm_num)
theorem B2991395 : Blo 1993435 2991395 := bstep (se 1 (by rfl) ⟨2243546, by rfl⟩ : syracuseStep 2991395 = 4487093) B4487093
theorem B1994263 : Blo 1993435 1994263 := bstep (se 1 (by rfl) ⟨1495697, by rfl⟩ : syracuseStep 1994263 = 2991395) B2991395
theorem B4548325 : Blo 1993435 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B6064433 : Blo 1993435 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B4042955 : Blo 1993435 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B2695303 : Blo 1993435 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B3593737 : Blo 1993435 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B4791649 : Blo 1993435 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B6388865 : Blo 1993435 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B4259243 : Blo 1993435 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B11357981 : Blo 1993435 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B7571987 : Blo 1993435 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B5047991 : Blo 1993435 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B3365327 : Blo 1993435 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2243551 : Blo 1993435 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B2991401 : Blo 1993435 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B1994267 : Blo 1993435 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B2395829 : Blo 1993435 2395829 := bbase (se 5 (by rfl) ⟨112304, by rfl⟩ : syracuseStep 2395829 = 224609) (by norm_num)
theorem B6388877 : Blo 1993435 6388877 := bstep (se 3 (by rfl) ⟨1197914, by rfl⟩ : syracuseStep 6388877 = 2395829) B2395829
theorem B4259251 : Blo 1993435 4259251 := bstep (se 1 (by rfl) ⟨3194438, by rfl⟩ : syracuseStep 4259251 = 6388877) B6388877
theorem B5679001 : Blo 1993435 5679001 := bstep (se 2 (by rfl) ⟨2129625, by rfl⟩ : syracuseStep 5679001 = 4259251) B4259251
theorem B7572001 : Blo 1993435 7572001 := bstep (se 2 (by rfl) ⟨2839500, by rfl⟩ : syracuseStep 7572001 = 5679001) B5679001
theorem B10096001 : Blo 1993435 10096001 := bstep (se 2 (by rfl) ⟨3786000, by rfl⟩ : syracuseStep 10096001 = 7572001) B7572001
theorem B6730667 : Blo 1993435 6730667 := bstep (se 1 (by rfl) ⟨5048000, by rfl⟩ : syracuseStep 6730667 = 10096001) B10096001
theorem B4487111 : Blo 1993435 4487111 := bstep (se 1 (by rfl) ⟨3365333, by rfl⟩ : syracuseStep 4487111 = 6730667) B6730667
theorem B2991407 : Blo 1993435 2991407 := bstep (se 1 (by rfl) ⟨2243555, by rfl⟩ : syracuseStep 2991407 = 4487111) B4487111
theorem B1994271 : Blo 1993435 1994271 := bstep (se 1 (by rfl) ⟨1495703, by rfl⟩ : syracuseStep 1994271 = 2991407) B2991407
theorem B2991413 : Blo 1993435 2991413 := bbase (se 5 (by rfl) ⟨140222, by rfl⟩ : syracuseStep 2991413 = 280445) (by norm_num)
theorem B1994275 : Blo 1993435 1994275 := bstep (se 1 (by rfl) ⟨1495706, by rfl⟩ : syracuseStep 1994275 = 2991413) B2991413
theorem B5048021 : Blo 1993435 5048021 := bbase (se 7 (by rfl) ⟨59156, by rfl⟩ : syracuseStep 5048021 = 118313) (by norm_num)
theorem B3365347 : Blo 1993435 3365347 := bstep (se 1 (by rfl) ⟨2524010, by rfl⟩ : syracuseStep 3365347 = 5048021) B5048021
theorem B4487129 : Blo 1993435 4487129 := bstep (se 2 (by rfl) ⟨1682673, by rfl⟩ : syracuseStep 4487129 = 3365347) B3365347
theorem B2991419 : Blo 1993435 2991419 := bstep (se 1 (by rfl) ⟨2243564, by rfl⟩ : syracuseStep 2991419 = 4487129) B4487129
theorem B1994279 : Blo 1993435 1994279 := bstep (se 1 (by rfl) ⟨1495709, by rfl⟩ : syracuseStep 1994279 = 2991419) B2991419
theorem B2243569 : Blo 1993435 2243569 := bbase (se 2 (by rfl) ⟨841338, by rfl⟩ : syracuseStep 2243569 = 1682677) (by norm_num)
theorem B2991425 : Blo 1993435 2991425 := bstep (se 2 (by rfl) ⟨1121784, by rfl⟩ : syracuseStep 2991425 = 2243569) B2243569
theorem B1994283 : Blo 1993435 1994283 := bstep (se 1 (by rfl) ⟨1495712, by rfl⟩ : syracuseStep 1994283 = 2991425) B2991425
theorem B8085989 : Blo 1993435 8085989 := bbase (se 4 (by rfl) ⟨758061, by rfl⟩ : syracuseStep 8085989 = 1516123) (by norm_num)
theorem B5390659 : Blo 1993435 5390659 := bstep (se 1 (by rfl) ⟨4042994, by rfl⟩ : syracuseStep 5390659 = 8085989) B8085989
theorem B7187545 : Blo 1993435 7187545 := bstep (se 2 (by rfl) ⟨2695329, by rfl⟩ : syracuseStep 7187545 = 5390659) B5390659
theorem B9583393 : Blo 1993435 9583393 := bstep (se 2 (by rfl) ⟨3593772, by rfl⟩ : syracuseStep 9583393 = 7187545) B7187545
theorem B12777857 : Blo 1993435 12777857 := bstep (se 2 (by rfl) ⟨4791696, by rfl⟩ : syracuseStep 12777857 = 9583393) B9583393
theorem B8518571 : Blo 1993435 8518571 := bstep (se 1 (by rfl) ⟨6388928, by rfl⟩ : syracuseStep 8518571 = 12777857) B12777857
theorem B5679047 : Blo 1993435 5679047 := bstep (se 1 (by rfl) ⟨4259285, by rfl⟩ : syracuseStep 5679047 = 8518571) B8518571
theorem B3786031 : Blo 1993435 3786031 := bstep (se 1 (by rfl) ⟨2839523, by rfl⟩ : syracuseStep 3786031 = 5679047) B5679047
theorem B5048041 : Blo 1993435 5048041 := bstep (se 2 (by rfl) ⟨1893015, by rfl⟩ : syracuseStep 5048041 = 3786031) B3786031
theorem B6730721 : Blo 1993435 6730721 := bstep (se 2 (by rfl) ⟨2524020, by rfl⟩ : syracuseStep 6730721 = 5048041) B5048041
theorem B4487147 : Blo 1993435 4487147 := bstep (se 1 (by rfl) ⟨3365360, by rfl⟩ : syracuseStep 4487147 = 6730721) B6730721
theorem B2991431 : Blo 1993435 2991431 := bstep (se 1 (by rfl) ⟨2243573, by rfl⟩ : syracuseStep 2991431 = 4487147) B4487147
theorem B1994287 : Blo 1993435 1994287 := bstep (se 1 (by rfl) ⟨1495715, by rfl⟩ : syracuseStep 1994287 = 2991431) B2991431
theorem B2991437 : Blo 1993435 2991437 := bbase (se 3 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 2991437 = 1121789) (by norm_num)
theorem B1994291 : Blo 1993435 1994291 := bstep (se 1 (by rfl) ⟨1495718, by rfl⟩ : syracuseStep 1994291 = 2991437) B2991437
theorem B4487165 : Blo 1993435 4487165 := bbase (se 3 (by rfl) ⟨841343, by rfl⟩ : syracuseStep 4487165 = 1682687) (by norm_num)
theorem B2991443 : Blo 1993435 2991443 := bstep (se 1 (by rfl) ⟨2243582, by rfl⟩ : syracuseStep 2991443 = 4487165) B4487165
theorem B1994295 : Blo 1993435 1994295 := bstep (se 1 (by rfl) ⟨1495721, by rfl⟩ : syracuseStep 1994295 = 2991443) B2991443
theorem B3365381 : Blo 1993435 3365381 := bbase (se 4 (by rfl) ⟨315504, by rfl⟩ : syracuseStep 3365381 = 631009) (by norm_num)
theorem B2243587 : Blo 1993435 2243587 := bstep (se 1 (by rfl) ⟨1682690, by rfl⟩ : syracuseStep 2243587 = 3365381) B3365381
theorem B2991449 : Blo 1993435 2991449 := bstep (se 2 (by rfl) ⟨1121793, by rfl⟩ : syracuseStep 2991449 = 2243587) B2243587
theorem B1994299 : Blo 1993435 1994299 := bstep (se 1 (by rfl) ⟨1495724, by rfl⟩ : syracuseStep 1994299 = 2991449) B2991449
theorem B15144245 : Blo 1993435 15144245 := bbase (se 5 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 15144245 = 1419773) (by norm_num)
theorem B10096163 : Blo 1993435 10096163 := bstep (se 1 (by rfl) ⟨7572122, by rfl⟩ : syracuseStep 10096163 = 15144245) B15144245
theorem B6730775 : Blo 1993435 6730775 := bstep (se 1 (by rfl) ⟨5048081, by rfl⟩ : syracuseStep 6730775 = 10096163) B10096163
theorem B4487183 : Blo 1993435 4487183 := bstep (se 1 (by rfl) ⟨3365387, by rfl⟩ : syracuseStep 4487183 = 6730775) B6730775
theorem B2991455 : Blo 1993435 2991455 := bstep (se 1 (by rfl) ⟨2243591, by rfl⟩ : syracuseStep 2991455 = 4487183) B4487183
theorem B1994303 : Blo 1993435 1994303 := bstep (se 1 (by rfl) ⟨1495727, by rfl⟩ : syracuseStep 1994303 = 2991455) B2991455
theorem B2991461 : Blo 1993435 2991461 := bbase (se 4 (by rfl) ⟨280449, by rfl⟩ : syracuseStep 2991461 = 560899) (by norm_num)
theorem B1994307 : Blo 1993435 1994307 := bstep (se 1 (by rfl) ⟨1495730, by rfl⟩ : syracuseStep 1994307 = 2991461) B2991461
theorem B3786077 : Blo 1993435 3786077 := bbase (se 3 (by rfl) ⟨709889, by rfl⟩ : syracuseStep 3786077 = 1419779) (by norm_num)
theorem B2524051 : Blo 1993435 2524051 := bstep (se 1 (by rfl) ⟨1893038, by rfl⟩ : syracuseStep 2524051 = 3786077) B3786077
theorem B3365401 : Blo 1993435 3365401 := bstep (se 2 (by rfl) ⟨1262025, by rfl⟩ : syracuseStep 3365401 = 2524051) B2524051
theorem B4487201 : Blo 1993435 4487201 := bstep (se 2 (by rfl) ⟨1682700, by rfl⟩ : syracuseStep 4487201 = 3365401) B3365401
theorem B2991467 : Blo 1993435 2991467 := bstep (se 1 (by rfl) ⟨2243600, by rfl⟩ : syracuseStep 2991467 = 4487201) B4487201
theorem B1994311 : Blo 1993435 1994311 := bstep (se 1 (by rfl) ⟨1495733, by rfl⟩ : syracuseStep 1994311 = 2991467) B2991467
theorem B2243605 : Blo 1993435 2243605 := bbase (se 6 (by rfl) ⟨52584, by rfl⟩ : syracuseStep 2243605 = 105169) (by norm_num)
theorem B2991473 : Blo 1993435 2991473 := bstep (se 2 (by rfl) ⟨1121802, by rfl⟩ : syracuseStep 2991473 = 2243605) B2243605
theorem B1994315 : Blo 1993435 1994315 := bstep (se 1 (by rfl) ⟨1495736, by rfl⟩ : syracuseStep 1994315 = 2991473) B2991473
theorem B2524061 : Blo 1993435 2524061 := bbase (se 3 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 2524061 = 946523) (by norm_num)
theorem B6730829 : Blo 1993435 6730829 := bstep (se 3 (by rfl) ⟨1262030, by rfl⟩ : syracuseStep 6730829 = 2524061) B2524061
theorem B4487219 : Blo 1993435 4487219 := bstep (se 1 (by rfl) ⟨3365414, by rfl⟩ : syracuseStep 4487219 = 6730829) B6730829
theorem B2991479 : Blo 1993435 2991479 := bstep (se 1 (by rfl) ⟨2243609, by rfl⟩ : syracuseStep 2991479 = 4487219) B4487219
theorem B1994319 : Blo 1993435 1994319 := bstep (se 1 (by rfl) ⟨1495739, by rfl⟩ : syracuseStep 1994319 = 2991479) B2991479
theorem B2991485 : Blo 1993435 2991485 := bbase (se 3 (by rfl) ⟨560903, by rfl⟩ : syracuseStep 2991485 = 1121807) (by norm_num)
theorem B1994323 : Blo 1993435 1994323 := bstep (se 1 (by rfl) ⟨1495742, by rfl⟩ : syracuseStep 1994323 = 2991485) B2991485
theorem B4487237 : Blo 1993435 4487237 := bbase (se 4 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 4487237 = 841357) (by norm_num)
theorem B2991491 : Blo 1993435 2991491 := bstep (se 1 (by rfl) ⟨2243618, by rfl⟩ : syracuseStep 2991491 = 4487237) B4487237
theorem B1994327 : Blo 1993435 1994327 := bstep (se 1 (by rfl) ⟨1495745, by rfl⟩ : syracuseStep 1994327 = 2991491) B2991491
theorem B5679173 : Blo 1993435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 1993435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 1993435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 1993435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 1993435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2991497 : Blo 1993435 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B1994331 : Blo 1993435 1994331 := bstep (se 1 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 1994331 = 2991497) B2991497
theorem B10096325 : Blo 1993435 10096325 := bbase (se 4 (by rfl) ⟨946530, by rfl⟩ : syracuseStep 10096325 = 1893061) (by norm_num)
theorem B6730883 : Blo 1993435 6730883 := bstep (se 1 (by rfl) ⟨5048162, by rfl⟩ : syracuseStep 6730883 = 10096325) B10096325
theorem B4487255 : Blo 1993435 4487255 := bstep (se 1 (by rfl) ⟨3365441, by rfl⟩ : syracuseStep 4487255 = 6730883) B6730883
theorem B2991503 : Blo 1993435 2991503 := bstep (se 1 (by rfl) ⟨2243627, by rfl⟩ : syracuseStep 2991503 = 4487255) B4487255
theorem B1994335 : Blo 1993435 1994335 := bstep (se 1 (by rfl) ⟨1495751, by rfl⟩ : syracuseStep 1994335 = 2991503) B2991503
theorem B2991509 : Blo 1993435 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B1994339 : Blo 1993435 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B4259405 : Blo 1993435 4259405 := bbase (se 3 (by rfl) ⟨798638, by rfl⟩ : syracuseStep 4259405 = 1597277) (by norm_num)
theorem B11358413 : Blo 1993435 11358413 := bstep (se 3 (by rfl) ⟨2129702, by rfl⟩ : syracuseStep 11358413 = 4259405) B4259405
theorem B7572275 : Blo 1993435 7572275 := bstep (se 1 (by rfl) ⟨5679206, by rfl⟩ : syracuseStep 7572275 = 11358413) B11358413
theorem B5048183 : Blo 1993435 5048183 := bstep (se 1 (by rfl) ⟨3786137, by rfl⟩ : syracuseStep 5048183 = 7572275) B7572275
theorem B3365455 : Blo 1993435 3365455 := bstep (se 1 (by rfl) ⟨2524091, by rfl⟩ : syracuseStep 3365455 = 5048183) B5048183
theorem B4487273 : Blo 1993435 4487273 := bstep (se 2 (by rfl) ⟨1682727, by rfl⟩ : syracuseStep 4487273 = 3365455) B3365455
theorem B2991515 : Blo 1993435 2991515 := bstep (se 1 (by rfl) ⟨2243636, by rfl⟩ : syracuseStep 2991515 = 4487273) B4487273
theorem B1994343 : Blo 1993435 1994343 := bstep (se 1 (by rfl) ⟨1495757, by rfl⟩ : syracuseStep 1994343 = 2991515) B2991515
theorem B2243641 : Blo 1993435 2243641 := bbase (se 2 (by rfl) ⟨841365, by rfl⟩ : syracuseStep 2243641 = 1682731) (by norm_num)
theorem B2991521 : Blo 1993435 2991521 := bstep (se 2 (by rfl) ⟨1121820, by rfl⟩ : syracuseStep 2991521 = 2243641) B2243641
theorem B1994347 : Blo 1993435 1994347 := bstep (se 1 (by rfl) ⟨1495760, by rfl⟩ : syracuseStep 1994347 = 2991521) B2991521
theorem B4043125 : Blo 1993435 4043125 := bbase (se 5 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 4043125 = 379043) (by norm_num)
theorem B5390833 : Blo 1993435 5390833 := bstep (se 2 (by rfl) ⟨2021562, by rfl⟩ : syracuseStep 5390833 = 4043125) B4043125
theorem B7187777 : Blo 1993435 7187777 := bstep (se 2 (by rfl) ⟨2695416, by rfl⟩ : syracuseStep 7187777 = 5390833) B5390833
theorem B4791851 : Blo 1993435 4791851 := bstep (se 1 (by rfl) ⟨3593888, by rfl⟩ : syracuseStep 4791851 = 7187777) B7187777
theorem B3194567 : Blo 1993435 3194567 := bstep (se 1 (by rfl) ⟨2395925, by rfl⟩ : syracuseStep 3194567 = 4791851) B4791851
theorem B2129711 : Blo 1993435 2129711 := bstep (se 1 (by rfl) ⟨1597283, by rfl⟩ : syracuseStep 2129711 = 3194567) B3194567
theorem B5679229 : Blo 1993435 5679229 := bstep (se 3 (by rfl) ⟨1064855, by rfl⟩ : syracuseStep 5679229 = 2129711) B2129711
theorem B7572305 : Blo 1993435 7572305 := bstep (se 2 (by rfl) ⟨2839614, by rfl⟩ : syracuseStep 7572305 = 5679229) B5679229
theorem B5048203 : Blo 1993435 5048203 := bstep (se 1 (by rfl) ⟨3786152, by rfl⟩ : syracuseStep 5048203 = 7572305) B7572305
theorem B6730937 : Blo 1993435 6730937 := bstep (se 2 (by rfl) ⟨2524101, by rfl⟩ : syracuseStep 6730937 = 5048203) B5048203
theorem B4487291 : Blo 1993435 4487291 := bstep (se 1 (by rfl) ⟨3365468, by rfl⟩ : syracuseStep 4487291 = 6730937) B6730937
theorem B2991527 : Blo 1993435 2991527 := bstep (se 1 (by rfl) ⟨2243645, by rfl⟩ : syracuseStep 2991527 = 4487291) B4487291
theorem B1994351 : Blo 1993435 1994351 := bstep (se 1 (by rfl) ⟨1495763, by rfl⟩ : syracuseStep 1994351 = 2991527) B2991527
theorem B2991533 : Blo 1993435 2991533 := bbase (se 3 (by rfl) ⟨560912, by rfl⟩ : syracuseStep 2991533 = 1121825) (by norm_num)
theorem B1994355 : Blo 1993435 1994355 := bstep (se 1 (by rfl) ⟨1495766, by rfl⟩ : syracuseStep 1994355 = 2991533) B2991533
theorem B4487309 : Blo 1993435 4487309 := bbase (se 3 (by rfl) ⟨841370, by rfl⟩ : syracuseStep 4487309 = 1682741) (by norm_num)
theorem B2991539 : Blo 1993435 2991539 := bstep (se 1 (by rfl) ⟨2243654, by rfl⟩ : syracuseStep 2991539 = 4487309) B4487309
theorem B1994359 : Blo 1993435 1994359 := bstep (se 1 (by rfl) ⟨1495769, by rfl⟩ : syracuseStep 1994359 = 2991539) B2991539
theorem B2524117 : Blo 1993435 2524117 := bbase (se 7 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 2524117 = 59159) (by norm_num)
theorem B3365489 : Blo 1993435 3365489 := bstep (se 2 (by rfl) ⟨1262058, by rfl⟩ : syracuseStep 3365489 = 2524117) B2524117
theorem B2243659 : Blo 1993435 2243659 := bstep (se 1 (by rfl) ⟨1682744, by rfl⟩ : syracuseStep 2243659 = 3365489) B3365489
theorem B2991545 : Blo 1993435 2991545 := bstep (se 2 (by rfl) ⟨1121829, by rfl⟩ : syracuseStep 2991545 = 2243659) B2243659
theorem B1994363 : Blo 1993435 1994363 := bstep (se 1 (by rfl) ⟨1495772, by rfl⟩ : syracuseStep 1994363 = 2991545) B2991545
theorem B4990709 : Blo 1993435 4990709 := bbase (se 5 (by rfl) ⟨233939, by rfl⟩ : syracuseStep 4990709 = 467879) (by norm_num)
theorem B3327139 : Blo 1993435 3327139 := bstep (se 1 (by rfl) ⟨2495354, by rfl⟩ : syracuseStep 3327139 = 4990709) B4990709
theorem B17744741 : Blo 1993435 17744741 := bstep (se 4 (by rfl) ⟨1663569, by rfl⟩ : syracuseStep 17744741 = 3327139) B3327139
theorem B11829827 : Blo 1993435 11829827 := bstep (se 1 (by rfl) ⟨8872370, by rfl⟩ : syracuseStep 11829827 = 17744741) B17744741
theorem B7886551 : Blo 1993435 7886551 := bstep (se 1 (by rfl) ⟨5914913, by rfl⟩ : syracuseStep 7886551 = 11829827) B11829827
theorem B10515401 : Blo 1993435 10515401 := bstep (se 2 (by rfl) ⟨3943275, by rfl⟩ : syracuseStep 10515401 = 7886551) B7886551
theorem B7010267 : Blo 1993435 7010267 := bstep (se 1 (by rfl) ⟨5257700, by rfl⟩ : syracuseStep 7010267 = 10515401) B10515401
theorem B18694045 : Blo 1993435 18694045 := bstep (se 3 (by rfl) ⟨3505133, by rfl⟩ : syracuseStep 18694045 = 7010267) B7010267
theorem B24925393 : Blo 1993435 24925393 := bstep (se 2 (by rfl) ⟨9347022, by rfl⟩ : syracuseStep 24925393 = 18694045) B18694045
theorem B33233857 : Blo 1993435 33233857 := bstep (se 2 (by rfl) ⟨12462696, by rfl⟩ : syracuseStep 33233857 = 24925393) B24925393
theorem B177247237 : Blo 1993435 177247237 := bstep (se 4 (by rfl) ⟨16616928, by rfl⟩ : syracuseStep 177247237 = 33233857) B33233857
theorem B236329649 : Blo 1993435 236329649 := bstep (se 2 (by rfl) ⟨88623618, by rfl⟩ : syracuseStep 236329649 = 177247237) B177247237
theorem B157553099 : Blo 1993435 157553099 := bstep (se 1 (by rfl) ⟨118164824, by rfl⟩ : syracuseStep 157553099 = 236329649) B236329649
theorem B105035399 : Blo 1993435 105035399 := bstep (se 1 (by rfl) ⟨78776549, by rfl⟩ : syracuseStep 105035399 = 157553099) B157553099
theorem B70023599 : Blo 1993435 70023599 := bstep (se 1 (by rfl) ⟨52517699, by rfl⟩ : syracuseStep 70023599 = 105035399) B105035399
theorem B46682399 : Blo 1993435 46682399 := bstep (se 1 (by rfl) ⟨35011799, by rfl⟩ : syracuseStep 46682399 = 70023599) B70023599
theorem B31121599 : Blo 1993435 31121599 := bstep (se 1 (by rfl) ⟨23341199, by rfl⟩ : syracuseStep 31121599 = 46682399) B46682399
theorem B41495465 : Blo 1993435 41495465 := bstep (se 2 (by rfl) ⟨15560799, by rfl⟩ : syracuseStep 41495465 = 31121599) B31121599
theorem B27663643 : Blo 1993435 27663643 := bstep (se 1 (by rfl) ⟨20747732, by rfl⟩ : syracuseStep 27663643 = 41495465) B41495465
theorem B36884857 : Blo 1993435 36884857 := bstep (se 2 (by rfl) ⟨13831821, by rfl⟩ : syracuseStep 36884857 = 27663643) B27663643
theorem B49179809 : Blo 1993435 49179809 := bstep (se 2 (by rfl) ⟨18442428, by rfl⟩ : syracuseStep 49179809 = 36884857) B36884857
theorem B32786539 : Blo 1993435 32786539 := bstep (se 1 (by rfl) ⟨24589904, by rfl⟩ : syracuseStep 32786539 = 49179809) B49179809
theorem B174861541 : Blo 1993435 174861541 := bstep (se 4 (by rfl) ⟨16393269, by rfl⟩ : syracuseStep 174861541 = 32786539) B32786539
theorem B233148721 : Blo 1993435 233148721 := bstep (se 2 (by rfl) ⟨87430770, by rfl⟩ : syracuseStep 233148721 = 174861541) B174861541
theorem B310864961 : Blo 1993435 310864961 := bstep (se 2 (by rfl) ⟨116574360, by rfl⟩ : syracuseStep 310864961 = 233148721) B233148721
theorem B207243307 : Blo 1993435 207243307 := bstep (se 1 (by rfl) ⟨155432480, by rfl⟩ : syracuseStep 207243307 = 310864961) B310864961
theorem B276324409 : Blo 1993435 276324409 := bstep (se 2 (by rfl) ⟨103621653, by rfl⟩ : syracuseStep 276324409 = 207243307) B207243307
theorem B368432545 : Blo 1993435 368432545 := bstep (se 2 (by rfl) ⟨138162204, by rfl⟩ : syracuseStep 368432545 = 276324409) B276324409
theorem B491243393 : Blo 1993435 491243393 := bstep (se 2 (by rfl) ⟨184216272, by rfl⟩ : syracuseStep 491243393 = 368432545) B368432545
theorem B327495595 : Blo 1993435 327495595 := bstep (se 1 (by rfl) ⟨245621696, by rfl⟩ : syracuseStep 327495595 = 491243393) B491243393
theorem B436660793 : Blo 1993435 436660793 := bstep (se 2 (by rfl) ⟨163747797, by rfl⟩ : syracuseStep 436660793 = 327495595) B327495595
theorem B291107195 : Blo 1993435 291107195 := bstep (se 1 (by rfl) ⟨218330396, by rfl⟩ : syracuseStep 291107195 = 436660793) B436660793
theorem B194071463 : Blo 1993435 194071463 := bstep (se 1 (by rfl) ⟨145553597, by rfl⟩ : syracuseStep 194071463 = 291107195) B291107195
theorem B129380975 : Blo 1993435 129380975 := bstep (se 1 (by rfl) ⟨97035731, by rfl⟩ : syracuseStep 129380975 = 194071463) B194071463
theorem B86253983 : Blo 1993435 86253983 := bstep (se 1 (by rfl) ⟨64690487, by rfl⟩ : syracuseStep 86253983 = 129380975) B129380975
theorem B57502655 : Blo 1993435 57502655 := bstep (se 1 (by rfl) ⟨43126991, by rfl⟩ : syracuseStep 57502655 = 86253983) B86253983
theorem B38335103 : Blo 1993435 38335103 := bstep (se 1 (by rfl) ⟨28751327, by rfl⟩ : syracuseStep 38335103 = 57502655) B57502655
theorem B25556735 : Blo 1993435 25556735 := bstep (se 1 (by rfl) ⟨19167551, by rfl⟩ : syracuseStep 25556735 = 38335103) B38335103
theorem B17037823 : Blo 1993435 17037823 := bstep (se 1 (by rfl) ⟨12778367, by rfl⟩ : syracuseStep 17037823 = 25556735) B25556735
theorem B22717097 : Blo 1993435 22717097 := bstep (se 2 (by rfl) ⟨8518911, by rfl⟩ : syracuseStep 22717097 = 17037823) B17037823
theorem B15144731 : Blo 1993435 15144731 := bstep (se 1 (by rfl) ⟨11358548, by rfl⟩ : syracuseStep 15144731 = 22717097) B22717097
theorem B10096487 : Blo 1993435 10096487 := bstep (se 1 (by rfl) ⟨7572365, by rfl⟩ : syracuseStep 10096487 = 15144731) B15144731
theorem B6730991 : Blo 1993435 6730991 := bstep (se 1 (by rfl) ⟨5048243, by rfl⟩ : syracuseStep 6730991 = 10096487) B10096487
theorem B4487327 : Blo 1993435 4487327 := bstep (se 1 (by rfl) ⟨3365495, by rfl⟩ : syracuseStep 4487327 = 6730991) B6730991
theorem B2991551 : Blo 1993435 2991551 := bstep (se 1 (by rfl) ⟨2243663, by rfl⟩ : syracuseStep 2991551 = 4487327) B4487327
theorem B1994367 : Blo 1993435 1994367 := bstep (se 1 (by rfl) ⟨1495775, by rfl⟩ : syracuseStep 1994367 = 2991551) B2991551
theorem B2991557 : Blo 1993435 2991557 := bbase (se 4 (by rfl) ⟨280458, by rfl⟩ : syracuseStep 2991557 = 560917) (by norm_num)
theorem B1994371 : Blo 1993435 1994371 := bstep (se 1 (by rfl) ⟨1495778, by rfl⟩ : syracuseStep 1994371 = 2991557) B2991557
theorem B3365509 : Blo 1993435 3365509 := bbase (se 4 (by rfl) ⟨315516, by rfl⟩ : syracuseStep 3365509 = 631033) (by norm_num)
theorem B4487345 : Blo 1993435 4487345 := bstep (se 2 (by rfl) ⟨1682754, by rfl⟩ : syracuseStep 4487345 = 3365509) B3365509
theorem B2991563 : Blo 1993435 2991563 := bstep (se 1 (by rfl) ⟨2243672, by rfl⟩ : syracuseStep 2991563 = 4487345) B4487345
theorem B1994375 : Blo 1993435 1994375 := bstep (se 1 (by rfl) ⟨1495781, by rfl⟩ : syracuseStep 1994375 = 2991563) B2991563
theorem B2243677 : Blo 1993435 2243677 := bbase (se 3 (by rfl) ⟨420689, by rfl⟩ : syracuseStep 2243677 = 841379) (by norm_num)
theorem B2991569 : Blo 1993435 2991569 := bstep (se 2 (by rfl) ⟨1121838, by rfl⟩ : syracuseStep 2991569 = 2243677) B2243677
theorem B1994379 : Blo 1993435 1994379 := bstep (se 1 (by rfl) ⟨1495784, by rfl⟩ : syracuseStep 1994379 = 2991569) B2991569
theorem B6731045 : Blo 1993435 6731045 := bbase (se 4 (by rfl) ⟨631035, by rfl⟩ : syracuseStep 6731045 = 1262071) (by norm_num)
theorem B4487363 : Blo 1993435 4487363 := bstep (se 1 (by rfl) ⟨3365522, by rfl⟩ : syracuseStep 4487363 = 6731045) B6731045
theorem B2991575 : Blo 1993435 2991575 := bstep (se 1 (by rfl) ⟨2243681, by rfl⟩ : syracuseStep 2991575 = 4487363) B4487363
theorem B1994383 : Blo 1993435 1994383 := bstep (se 1 (by rfl) ⟨1495787, by rfl⟩ : syracuseStep 1994383 = 2991575) B2991575
theorem B2991581 : Blo 1993435 2991581 := bbase (se 3 (by rfl) ⟨560921, by rfl⟩ : syracuseStep 2991581 = 1121843) (by norm_num)
theorem B1994387 : Blo 1993435 1994387 := bstep (se 1 (by rfl) ⟨1495790, by rfl⟩ : syracuseStep 1994387 = 2991581) B2991581
theorem B4487381 : Blo 1993435 4487381 := bbase (se 7 (by rfl) ⟨52586, by rfl⟩ : syracuseStep 4487381 = 105173) (by norm_num)
theorem B2991587 : Blo 1993435 2991587 := bstep (se 1 (by rfl) ⟨2243690, by rfl⟩ : syracuseStep 2991587 = 4487381) B4487381
theorem B1994391 : Blo 1993435 1994391 := bstep (se 1 (by rfl) ⟨1495793, by rfl⟩ : syracuseStep 1994391 = 2991587) B2991587
theorem B2878421 : Blo 1993435 2878421 := bbase (se 7 (by rfl) ⟨33731, by rfl⟩ : syracuseStep 2878421 = 67463) (by norm_num)
theorem B30703157 : Blo 1993435 30703157 := bstep (se 5 (by rfl) ⟨1439210, by rfl⟩ : syracuseStep 30703157 = 2878421) B2878421
theorem B20468771 : Blo 1993435 20468771 := bstep (se 1 (by rfl) ⟨15351578, by rfl⟩ : syracuseStep 20468771 = 30703157) B30703157
theorem B13645847 : Blo 1993435 13645847 := bstep (se 1 (by rfl) ⟨10234385, by rfl⟩ : syracuseStep 13645847 = 20468771) B20468771
theorem B36388925 : Blo 1993435 36388925 := bstep (se 3 (by rfl) ⟨6822923, by rfl⟩ : syracuseStep 36388925 = 13645847) B13645847
theorem B24259283 : Blo 1993435 24259283 := bstep (se 1 (by rfl) ⟨18194462, by rfl⟩ : syracuseStep 24259283 = 36388925) B36388925
theorem B16172855 : Blo 1993435 16172855 := bstep (se 1 (by rfl) ⟨12129641, by rfl⟩ : syracuseStep 16172855 = 24259283) B24259283
theorem B10781903 : Blo 1993435 10781903 := bstep (se 1 (by rfl) ⟨8086427, by rfl⟩ : syracuseStep 10781903 = 16172855) B16172855
theorem B7187935 : Blo 1993435 7187935 := bstep (se 1 (by rfl) ⟨5390951, by rfl⟩ : syracuseStep 7187935 = 10781903) B10781903
theorem B9583913 : Blo 1993435 9583913 := bstep (se 2 (by rfl) ⟨3593967, by rfl⟩ : syracuseStep 9583913 = 7187935) B7187935
theorem B6389275 : Blo 1993435 6389275 := bstep (se 1 (by rfl) ⟨4791956, by rfl⟩ : syracuseStep 6389275 = 9583913) B9583913
theorem B8519033 : Blo 1993435 8519033 := bstep (se 2 (by rfl) ⟨3194637, by rfl⟩ : syracuseStep 8519033 = 6389275) B6389275
theorem B5679355 : Blo 1993435 5679355 := bstep (se 1 (by rfl) ⟨4259516, by rfl⟩ : syracuseStep 5679355 = 8519033) B8519033
theorem B7572473 : Blo 1993435 7572473 := bstep (se 2 (by rfl) ⟨2839677, by rfl⟩ : syracuseStep 7572473 = 5679355) B5679355
theorem B5048315 : Blo 1993435 5048315 := bstep (se 1 (by rfl) ⟨3786236, by rfl⟩ : syracuseStep 5048315 = 7572473) B7572473
theorem B3365543 : Blo 1993435 3365543 := bstep (se 1 (by rfl) ⟨2524157, by rfl⟩ : syracuseStep 3365543 = 5048315) B5048315
theorem B2243695 : Blo 1993435 2243695 := bstep (se 1 (by rfl) ⟨1682771, by rfl⟩ : syracuseStep 2243695 = 3365543) B3365543
theorem B2991593 : Blo 1993435 2991593 := bstep (se 2 (by rfl) ⟨1121847, by rfl⟩ : syracuseStep 2991593 = 2243695) B2243695
theorem B1994395 : Blo 1993435 1994395 := bstep (se 1 (by rfl) ⟨1495796, by rfl⟩ : syracuseStep 1994395 = 2991593) B2991593
theorem B4791965 : Blo 1993435 4791965 := bbase (se 3 (by rfl) ⟨898493, by rfl⟩ : syracuseStep 4791965 = 1796987) (by norm_num)
theorem B12778573 : Blo 1993435 12778573 := bstep (se 3 (by rfl) ⟨2395982, by rfl⟩ : syracuseStep 12778573 = 4791965) B4791965
theorem B17038097 : Blo 1993435 17038097 := bstep (se 2 (by rfl) ⟨6389286, by rfl⟩ : syracuseStep 17038097 = 12778573) B12778573
theorem B11358731 : Blo 1993435 11358731 := bstep (se 1 (by rfl) ⟨8519048, by rfl⟩ : syracuseStep 11358731 = 17038097) B17038097
theorem B7572487 : Blo 1993435 7572487 := bstep (se 1 (by rfl) ⟨5679365, by rfl⟩ : syracuseStep 7572487 = 11358731) B11358731
theorem B10096649 : Blo 1993435 10096649 := bstep (se 2 (by rfl) ⟨3786243, by rfl⟩ : syracuseStep 10096649 = 7572487) B7572487
theorem B6731099 : Blo 1993435 6731099 := bstep (se 1 (by rfl) ⟨5048324, by rfl⟩ : syracuseStep 6731099 = 10096649) B10096649
theorem B4487399 : Blo 1993435 4487399 := bstep (se 1 (by rfl) ⟨3365549, by rfl⟩ : syracuseStep 4487399 = 6731099) B6731099
theorem B2991599 : Blo 1993435 2991599 := bstep (se 1 (by rfl) ⟨2243699, by rfl⟩ : syracuseStep 2991599 = 4487399) B4487399
theorem B1994399 : Blo 1993435 1994399 := bstep (se 1 (by rfl) ⟨1495799, by rfl⟩ : syracuseStep 1994399 = 2991599) B2991599
theorem B2991605 : Blo 1993435 2991605 := bbase (se 5 (by rfl) ⟨140231, by rfl⟩ : syracuseStep 2991605 = 280463) (by norm_num)
theorem B1994403 : Blo 1993435 1994403 := bstep (se 1 (by rfl) ⟨1495802, by rfl⟩ : syracuseStep 1994403 = 2991605) B2991605
theorem B2395993 : Blo 1993435 2395993 := bbase (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) (by norm_num)
theorem B3194657 : Blo 1993435 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B2129771 : Blo 1993435 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B5679389 : Blo 1993435 5679389 := bstep (se 3 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 5679389 = 2129771) B2129771
theorem B3786259 : Blo 1993435 3786259 := bstep (se 1 (by rfl) ⟨2839694, by rfl⟩ : syracuseStep 3786259 = 5679389) B5679389
theorem B5048345 : Blo 1993435 5048345 := bstep (se 2 (by rfl) ⟨1893129, by rfl⟩ : syracuseStep 5048345 = 3786259) B3786259
theorem B3365563 : Blo 1993435 3365563 := bstep (se 1 (by rfl) ⟨2524172, by rfl⟩ : syracuseStep 3365563 = 5048345) B5048345
theorem B4487417 : Blo 1993435 4487417 := bstep (se 2 (by rfl) ⟨1682781, by rfl⟩ : syracuseStep 4487417 = 3365563) B3365563
theorem B2991611 : Blo 1993435 2991611 := bstep (se 1 (by rfl) ⟨2243708, by rfl⟩ : syracuseStep 2991611 = 4487417) B4487417
theorem B1994407 : Blo 1993435 1994407 := bstep (se 1 (by rfl) ⟨1495805, by rfl⟩ : syracuseStep 1994407 = 2991611) B2991611
theorem B2243713 : Blo 1993435 2243713 := bbase (se 2 (by rfl) ⟨841392, by rfl⟩ : syracuseStep 2243713 = 1682785) (by norm_num)
theorem B2991617 : Blo 1993435 2991617 := bstep (se 2 (by rfl) ⟨1121856, by rfl⟩ : syracuseStep 2991617 = 2243713) B2243713
theorem B1994411 : Blo 1993435 1994411 := bstep (se 1 (by rfl) ⟨1495808, by rfl⟩ : syracuseStep 1994411 = 2991617) B2991617
theorem B5048365 : Blo 1993435 5048365 := bbase (se 3 (by rfl) ⟨946568, by rfl⟩ : syracuseStep 5048365 = 1893137) (by norm_num)
theorem B6731153 : Blo 1993435 6731153 := bstep (se 2 (by rfl) ⟨2524182, by rfl⟩ : syracuseStep 6731153 = 5048365) B5048365
theorem B4487435 : Blo 1993435 4487435 := bstep (se 1 (by rfl) ⟨3365576, by rfl⟩ : syracuseStep 4487435 = 6731153) B6731153
theorem B2991623 : Blo 1993435 2991623 := bstep (se 1 (by rfl) ⟨2243717, by rfl⟩ : syracuseStep 2991623 = 4487435) B4487435
theorem B1994415 : Blo 1993435 1994415 := bstep (se 1 (by rfl) ⟨1495811, by rfl⟩ : syracuseStep 1994415 = 2991623) B2991623
theorem B2991629 : Blo 1993435 2991629 := bbase (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) (by norm_num)
theorem B1994419 : Blo 1993435 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B4487453 : Blo 1993435 4487453 := bbase (se 3 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 4487453 = 1682795) (by norm_num)
theorem B2991635 : Blo 1993435 2991635 := bstep (se 1 (by rfl) ⟨2243726, by rfl⟩ : syracuseStep 2991635 = 4487453) B4487453
theorem B1994423 : Blo 1993435 1994423 := bstep (se 1 (by rfl) ⟨1495817, by rfl⟩ : syracuseStep 1994423 = 2991635) B2991635
theorem B3365597 : Blo 1993435 3365597 := bbase (se 3 (by rfl) ⟨631049, by rfl⟩ : syracuseStep 3365597 = 1262099) (by norm_num)
theorem B2243731 : Blo 1993435 2243731 := bstep (se 1 (by rfl) ⟨1682798, by rfl⟩ : syracuseStep 2243731 = 3365597) B3365597
theorem B2991641 : Blo 1993435 2991641 := bstep (se 2 (by rfl) ⟨1121865, by rfl⟩ : syracuseStep 2991641 = 2243731) B2243731
theorem B1994427 : Blo 1993435 1994427 := bstep (se 1 (by rfl) ⟨1495820, by rfl⟩ : syracuseStep 1994427 = 2991641) B2991641
theorem B2396021 : Blo 1993435 2396021 := bbase (se 5 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 2396021 = 224627) (by norm_num)
theorem B6389389 : Blo 1993435 6389389 := bstep (se 3 (by rfl) ⟨1198010, by rfl⟩ : syracuseStep 6389389 = 2396021) B2396021
theorem B8519185 : Blo 1993435 8519185 := bstep (se 2 (by rfl) ⟨3194694, by rfl⟩ : syracuseStep 8519185 = 6389389) B6389389
theorem B11358913 : Blo 1993435 11358913 := bstep (se 2 (by rfl) ⟨4259592, by rfl⟩ : syracuseStep 11358913 = 8519185) B8519185
theorem B15145217 : Blo 1993435 15145217 := bstep (se 2 (by rfl) ⟨5679456, by rfl⟩ : syracuseStep 15145217 = 11358913) B11358913
theorem B10096811 : Blo 1993435 10096811 := bstep (se 1 (by rfl) ⟨7572608, by rfl⟩ : syracuseStep 10096811 = 15145217) B15145217
theorem B6731207 : Blo 1993435 6731207 := bstep (se 1 (by rfl) ⟨5048405, by rfl⟩ : syracuseStep 6731207 = 10096811) B10096811
theorem B4487471 : Blo 1993435 4487471 := bstep (se 1 (by rfl) ⟨3365603, by rfl⟩ : syracuseStep 4487471 = 6731207) B6731207
theorem B2991647 : Blo 1993435 2991647 := bstep (se 1 (by rfl) ⟨2243735, by rfl⟩ : syracuseStep 2991647 = 4487471) B4487471
theorem B1994431 : Blo 1993435 1994431 := bstep (se 1 (by rfl) ⟨1495823, by rfl⟩ : syracuseStep 1994431 = 2991647) B2991647
theorem B2991653 : Blo 1993435 2991653 := bbase (se 4 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 2991653 = 560935) (by norm_num)
theorem B1994435 : Blo 1993435 1994435 := bstep (se 1 (by rfl) ⟨1495826, by rfl⟩ : syracuseStep 1994435 = 2991653) B2991653
theorem B2524213 : Blo 1993435 2524213 := bbase (se 5 (by rfl) ⟨118322, by rfl⟩ : syracuseStep 2524213 = 236645) (by norm_num)
theorem B3365617 : Blo 1993435 3365617 := bstep (se 2 (by rfl) ⟨1262106, by rfl⟩ : syracuseStep 3365617 = 2524213) B2524213
theorem B4487489 : Blo 1993435 4487489 := bstep (se 2 (by rfl) ⟨1682808, by rfl⟩ : syracuseStep 4487489 = 3365617) B3365617
theorem B2991659 : Blo 1993435 2991659 := bstep (se 1 (by rfl) ⟨2243744, by rfl⟩ : syracuseStep 2991659 = 4487489) B4487489
theorem B1994439 : Blo 1993435 1994439 := bstep (se 1 (by rfl) ⟨1495829, by rfl⟩ : syracuseStep 1994439 = 2991659) B2991659
theorem B2243749 : Blo 1993435 2243749 := bbase (se 4 (by rfl) ⟨210351, by rfl⟩ : syracuseStep 2243749 = 420703) (by norm_num)
theorem B2991665 : Blo 1993435 2991665 := bstep (se 2 (by rfl) ⟨1121874, by rfl⟩ : syracuseStep 2991665 = 2243749) B2243749
theorem B1994443 : Blo 1993435 1994443 := bstep (se 1 (by rfl) ⟨1495832, by rfl⟩ : syracuseStep 1994443 = 2991665) B2991665
theorem B3594061 : Blo 1993435 3594061 := bbase (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) (by norm_num)
theorem B19168325 : Blo 1993435 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B12778883 : Blo 1993435 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B8519255 : Blo 1993435 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B5679503 : Blo 1993435 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B3786335 : Blo 1993435 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B2524223 : Blo 1993435 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B6731261 : Blo 1993435 6731261 := bstep (se 3 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 6731261 = 2524223) B2524223
theorem B4487507 : Blo 1993435 4487507 := bstep (se 1 (by rfl) ⟨3365630, by rfl⟩ : syracuseStep 4487507 = 6731261) B6731261
theorem B2991671 : Blo 1993435 2991671 := bstep (se 1 (by rfl) ⟨2243753, by rfl⟩ : syracuseStep 2991671 = 4487507) B4487507
theorem B1994447 : Blo 1993435 1994447 := bstep (se 1 (by rfl) ⟨1495835, by rfl⟩ : syracuseStep 1994447 = 2991671) B2991671
theorem B2991677 : Blo 1993435 2991677 := bbase (se 3 (by rfl) ⟨560939, by rfl⟩ : syracuseStep 2991677 = 1121879) (by norm_num)
theorem B1994451 : Blo 1993435 1994451 := bstep (se 1 (by rfl) ⟨1495838, by rfl⟩ : syracuseStep 1994451 = 2991677) B2991677
theorem B4487525 : Blo 1993435 4487525 := bbase (se 4 (by rfl) ⟨420705, by rfl⟩ : syracuseStep 4487525 = 841411) (by norm_num)
theorem B2991683 : Blo 1993435 2991683 := bstep (se 1 (by rfl) ⟨2243762, by rfl⟩ : syracuseStep 2991683 = 4487525) B4487525
theorem B1994455 : Blo 1993435 1994455 := bstep (se 1 (by rfl) ⟨1495841, by rfl⟩ : syracuseStep 1994455 = 2991683) B2991683
theorem B5048477 : Blo 1993435 5048477 := bbase (se 3 (by rfl) ⟨946589, by rfl⟩ : syracuseStep 5048477 = 1893179) (by norm_num)
theorem B3365651 : Blo 1993435 3365651 := bstep (se 1 (by rfl) ⟨2524238, by rfl⟩ : syracuseStep 3365651 = 5048477) B5048477
theorem B2243767 : Blo 1993435 2243767 := bstep (se 1 (by rfl) ⟨1682825, by rfl⟩ : syracuseStep 2243767 = 3365651) B3365651
theorem B2991689 : Blo 1993435 2991689 := bstep (se 2 (by rfl) ⟨1121883, by rfl⟩ : syracuseStep 2991689 = 2243767) B2243767
theorem B1994459 : Blo 1993435 1994459 := bstep (se 1 (by rfl) ⟨1495844, by rfl⟩ : syracuseStep 1994459 = 2991689) B2991689
theorem B3786365 : Blo 1993435 3786365 := bbase (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) (by norm_num)
theorem B10096973 : Blo 1993435 10096973 := bstep (se 3 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 10096973 = 3786365) B3786365
theorem B6731315 : Blo 1993435 6731315 := bstep (se 1 (by rfl) ⟨5048486, by rfl⟩ : syracuseStep 6731315 = 10096973) B10096973
theorem B4487543 : Blo 1993435 4487543 := bstep (se 1 (by rfl) ⟨3365657, by rfl⟩ : syracuseStep 4487543 = 6731315) B6731315
theorem B2991695 : Blo 1993435 2991695 := bstep (se 1 (by rfl) ⟨2243771, by rfl⟩ : syracuseStep 2991695 = 4487543) B4487543
theorem B1994463 : Blo 1993435 1994463 := bstep (se 1 (by rfl) ⟨1495847, by rfl⟩ : syracuseStep 1994463 = 2991695) B2991695
theorem B2991701 : Blo 1993435 2991701 := bbase (se 8 (by rfl) ⟨17529, by rfl⟩ : syracuseStep 2991701 = 35059) (by norm_num)
theorem B1994467 : Blo 1993435 1994467 := bstep (se 1 (by rfl) ⟨1495850, by rfl⟩ : syracuseStep 1994467 = 2991701) B2991701
theorem B5391157 : Blo 1993435 5391157 := bbase (se 5 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 5391157 = 505421) (by norm_num)
theorem B7188209 : Blo 1993435 7188209 := bstep (se 2 (by rfl) ⟨2695578, by rfl⟩ : syracuseStep 7188209 = 5391157) B5391157
theorem B4792139 : Blo 1993435 4792139 := bstep (se 1 (by rfl) ⟨3594104, by rfl⟩ : syracuseStep 4792139 = 7188209) B7188209
theorem B3194759 : Blo 1993435 3194759 := bstep (se 1 (by rfl) ⟨2396069, by rfl⟩ : syracuseStep 3194759 = 4792139) B4792139
theorem B8519357 : Blo 1993435 8519357 := bstep (se 3 (by rfl) ⟨1597379, by rfl⟩ : syracuseStep 8519357 = 3194759) B3194759
theorem B5679571 : Blo 1993435 5679571 := bstep (se 1 (by rfl) ⟨4259678, by rfl⟩ : syracuseStep 5679571 = 8519357) B8519357
theorem B7572761 : Blo 1993435 7572761 := bstep (se 2 (by rfl) ⟨2839785, by rfl⟩ : syracuseStep 7572761 = 5679571) B5679571
theorem B5048507 : Blo 1993435 5048507 := bstep (se 1 (by rfl) ⟨3786380, by rfl⟩ : syracuseStep 5048507 = 7572761) B7572761
theorem B3365671 : Blo 1993435 3365671 := bstep (se 1 (by rfl) ⟨2524253, by rfl⟩ : syracuseStep 3365671 = 5048507) B5048507
theorem B4487561 : Blo 1993435 4487561 := bstep (se 2 (by rfl) ⟨1682835, by rfl⟩ : syracuseStep 4487561 = 3365671) B3365671
theorem B2991707 : Blo 1993435 2991707 := bstep (se 1 (by rfl) ⟨2243780, by rfl⟩ : syracuseStep 2991707 = 4487561) B4487561
theorem B1994471 : Blo 1993435 1994471 := bstep (se 1 (by rfl) ⟨1495853, by rfl⟩ : syracuseStep 1994471 = 2991707) B2991707
theorem B2243785 : Blo 1993435 2243785 := bbase (se 2 (by rfl) ⟨841419, by rfl⟩ : syracuseStep 2243785 = 1682839) (by norm_num)
theorem B2991713 : Blo 1993435 2991713 := bstep (se 2 (by rfl) ⟨1121892, by rfl⟩ : syracuseStep 2991713 = 2243785) B2243785
theorem B1994475 : Blo 1993435 1994475 := bstep (se 1 (by rfl) ⟨1495856, by rfl⟩ : syracuseStep 1994475 = 2991713) B2991713
theorem B3411605 : Blo 1993435 3411605 := bbase (se 6 (by rfl) ⟨79959, by rfl⟩ : syracuseStep 3411605 = 159919) (by norm_num)
theorem B9097613 : Blo 1993435 9097613 := bstep (se 3 (by rfl) ⟨1705802, by rfl⟩ : syracuseStep 9097613 = 3411605) B3411605
theorem B6065075 : Blo 1993435 6065075 := bstep (se 1 (by rfl) ⟨4548806, by rfl⟩ : syracuseStep 6065075 = 9097613) B9097613
theorem B16173533 : Blo 1993435 16173533 := bstep (se 3 (by rfl) ⟨3032537, by rfl⟩ : syracuseStep 16173533 = 6065075) B6065075
theorem B10782355 : Blo 1993435 10782355 := bstep (se 1 (by rfl) ⟨8086766, by rfl⟩ : syracuseStep 10782355 = 16173533) B16173533
theorem B14376473 : Blo 1993435 14376473 := bstep (se 2 (by rfl) ⟨5391177, by rfl⟩ : syracuseStep 14376473 = 10782355) B10782355
theorem B9584315 : Blo 1993435 9584315 := bstep (se 1 (by rfl) ⟨7188236, by rfl⟩ : syracuseStep 9584315 = 14376473) B14376473
theorem B6389543 : Blo 1993435 6389543 := bstep (se 1 (by rfl) ⟨4792157, by rfl⟩ : syracuseStep 6389543 = 9584315) B9584315
theorem B17038781 : Blo 1993435 17038781 := bstep (se 3 (by rfl) ⟨3194771, by rfl⟩ : syracuseStep 17038781 = 6389543) B6389543
theorem B11359187 : Blo 1993435 11359187 := bstep (se 1 (by rfl) ⟨8519390, by rfl⟩ : syracuseStep 11359187 = 17038781) B17038781
theorem B7572791 : Blo 1993435 7572791 := bstep (se 1 (by rfl) ⟨5679593, by rfl⟩ : syracuseStep 7572791 = 11359187) B11359187
theorem B5048527 : Blo 1993435 5048527 := bstep (se 1 (by rfl) ⟨3786395, by rfl⟩ : syracuseStep 5048527 = 7572791) B7572791
theorem B6731369 : Blo 1993435 6731369 := bstep (se 2 (by rfl) ⟨2524263, by rfl⟩ : syracuseStep 6731369 = 5048527) B5048527
theorem B4487579 : Blo 1993435 4487579 := bstep (se 1 (by rfl) ⟨3365684, by rfl⟩ : syracuseStep 4487579 = 6731369) B6731369
theorem B2991719 : Blo 1993435 2991719 := bstep (se 1 (by rfl) ⟨2243789, by rfl⟩ : syracuseStep 2991719 = 4487579) B4487579
theorem B1994479 : Blo 1993435 1994479 := bstep (se 1 (by rfl) ⟨1495859, by rfl⟩ : syracuseStep 1994479 = 2991719) B2991719
theorem B2991725 : Blo 1993435 2991725 := bbase (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) (by norm_num)
theorem B1994483 : Blo 1993435 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B4487597 : Blo 1993435 4487597 := bbase (se 3 (by rfl) ⟨841424, by rfl⟩ : syracuseStep 4487597 = 1682849) (by norm_num)
theorem B2991731 : Blo 1993435 2991731 := bstep (se 1 (by rfl) ⟨2243798, by rfl⟩ : syracuseStep 2991731 = 4487597) B4487597
theorem B1994487 : Blo 1993435 1994487 := bstep (se 1 (by rfl) ⟨1495865, by rfl⟩ : syracuseStep 1994487 = 2991731) B2991731
theorem B2129861 : Blo 1993435 2129861 := bbase (se 4 (by rfl) ⟨199674, by rfl⟩ : syracuseStep 2129861 = 399349) (by norm_num)
theorem B5679629 : Blo 1993435 5679629 := bstep (se 3 (by rfl) ⟨1064930, by rfl⟩ : syracuseStep 5679629 = 2129861) B2129861
theorem B3786419 : Blo 1993435 3786419 := bstep (se 1 (by rfl) ⟨2839814, by rfl⟩ : syracuseStep 3786419 = 5679629) B5679629
theorem B2524279 : Blo 1993435 2524279 := bstep (se 1 (by rfl) ⟨1893209, by rfl⟩ : syracuseStep 2524279 = 3786419) B3786419
theorem B3365705 : Blo 1993435 3365705 := bstep (se 2 (by rfl) ⟨1262139, by rfl⟩ : syracuseStep 3365705 = 2524279) B2524279
theorem B2243803 : Blo 1993435 2243803 := bstep (se 1 (by rfl) ⟨1682852, by rfl⟩ : syracuseStep 2243803 = 3365705) B3365705
theorem B2991737 : Blo 1993435 2991737 := bstep (se 2 (by rfl) ⟨1121901, by rfl⟩ : syracuseStep 2991737 = 2243803) B2243803
theorem B1994491 : Blo 1993435 1994491 := bstep (se 1 (by rfl) ⟨1495868, by rfl⟩ : syracuseStep 1994491 = 2991737) B2991737
theorem B245637461 : Blo 1993435 245637461 := bbase (se 10 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 245637461 = 719641) (by norm_num)
theorem B163758307 : Blo 1993435 163758307 := bstep (se 1 (by rfl) ⟨122818730, by rfl⟩ : syracuseStep 163758307 = 245637461) B245637461
theorem B218344409 : Blo 1993435 218344409 := bstep (se 2 (by rfl) ⟨81879153, by rfl⟩ : syracuseStep 218344409 = 163758307) B163758307
theorem B145562939 : Blo 1993435 145562939 := bstep (se 1 (by rfl) ⟨109172204, by rfl⟩ : syracuseStep 145562939 = 218344409) B218344409
theorem B97041959 : Blo 1993435 97041959 := bstep (se 1 (by rfl) ⟨72781469, by rfl⟩ : syracuseStep 97041959 = 145562939) B145562939
theorem B64694639 : Blo 1993435 64694639 := bstep (se 1 (by rfl) ⟨48520979, by rfl⟩ : syracuseStep 64694639 = 97041959) B97041959
theorem B43129759 : Blo 1993435 43129759 := bstep (se 1 (by rfl) ⟨32347319, by rfl⟩ : syracuseStep 43129759 = 64694639) B64694639
theorem B57506345 : Blo 1993435 57506345 := bstep (se 2 (by rfl) ⟨21564879, by rfl⟩ : syracuseStep 57506345 = 43129759) B43129759
theorem B38337563 : Blo 1993435 38337563 := bstep (se 1 (by rfl) ⟨28753172, by rfl⟩ : syracuseStep 38337563 = 57506345) B57506345
theorem B25558375 : Blo 1993435 25558375 := bstep (se 1 (by rfl) ⟨19168781, by rfl⟩ : syracuseStep 25558375 = 38337563) B38337563
theorem B34077833 : Blo 1993435 34077833 := bstep (se 2 (by rfl) ⟨12779187, by rfl⟩ : syracuseStep 34077833 = 25558375) B25558375
theorem B22718555 : Blo 1993435 22718555 := bstep (se 1 (by rfl) ⟨17038916, by rfl⟩ : syracuseStep 22718555 = 34077833) B34077833
theorem B15145703 : Blo 1993435 15145703 := bstep (se 1 (by rfl) ⟨11359277, by rfl⟩ : syracuseStep 15145703 = 22718555) B22718555
theorem B10097135 : Blo 1993435 10097135 := bstep (se 1 (by rfl) ⟨7572851, by rfl⟩ : syracuseStep 10097135 = 15145703) B15145703
theorem B6731423 : Blo 1993435 6731423 := bstep (se 1 (by rfl) ⟨5048567, by rfl⟩ : syracuseStep 6731423 = 10097135) B10097135
theorem B4487615 : Blo 1993435 4487615 := bstep (se 1 (by rfl) ⟨3365711, by rfl⟩ : syracuseStep 4487615 = 6731423) B6731423
theorem B2991743 : Blo 1993435 2991743 := bstep (se 1 (by rfl) ⟨2243807, by rfl⟩ : syracuseStep 2991743 = 4487615) B4487615
theorem B1994495 : Blo 1993435 1994495 := bstep (se 1 (by rfl) ⟨1495871, by rfl⟩ : syracuseStep 1994495 = 2991743) B2991743
theorem B2991749 : Blo 1993435 2991749 := bbase (se 4 (by rfl) ⟨280476, by rfl⟩ : syracuseStep 2991749 = 560953) (by norm_num)
theorem B1994499 : Blo 1993435 1994499 := bstep (se 1 (by rfl) ⟨1495874, by rfl⟩ : syracuseStep 1994499 = 2991749) B2991749
theorem B3365725 : Blo 1993435 3365725 := bbase (se 3 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 3365725 = 1262147) (by norm_num)
theorem B4487633 : Blo 1993435 4487633 := bstep (se 2 (by rfl) ⟨1682862, by rfl⟩ : syracuseStep 4487633 = 3365725) B3365725
theorem B2991755 : Blo 1993435 2991755 := bstep (se 1 (by rfl) ⟨2243816, by rfl⟩ : syracuseStep 2991755 = 4487633) B4487633
theorem B1994503 : Blo 1993435 1994503 := bstep (se 1 (by rfl) ⟨1495877, by rfl⟩ : syracuseStep 1994503 = 2991755) B2991755
theorem B2243821 : Blo 1993435 2243821 := bbase (se 3 (by rfl) ⟨420716, by rfl⟩ : syracuseStep 2243821 = 841433) (by norm_num)
theorem B2991761 : Blo 1993435 2991761 := bstep (se 2 (by rfl) ⟨1121910, by rfl⟩ : syracuseStep 2991761 = 2243821) B2243821
theorem B1994507 : Blo 1993435 1994507 := bstep (se 1 (by rfl) ⟨1495880, by rfl⟩ : syracuseStep 1994507 = 2991761) B2991761
theorem B6731477 : Blo 1993435 6731477 := bbase (se 7 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 6731477 = 157769) (by norm_num)
theorem B4487651 : Blo 1993435 4487651 := bstep (se 1 (by rfl) ⟨3365738, by rfl⟩ : syracuseStep 4487651 = 6731477) B6731477
theorem B2991767 : Blo 1993435 2991767 := bstep (se 1 (by rfl) ⟨2243825, by rfl⟩ : syracuseStep 2991767 = 4487651) B4487651
theorem B1994511 : Blo 1993435 1994511 := bstep (se 1 (by rfl) ⟨1495883, by rfl⟩ : syracuseStep 1994511 = 2991767) B2991767
theorem B2991773 : Blo 1993435 2991773 := bbase (se 3 (by rfl) ⟨560957, by rfl⟩ : syracuseStep 2991773 = 1121915) (by norm_num)
theorem B1994515 : Blo 1993435 1994515 := bstep (se 1 (by rfl) ⟨1495886, by rfl⟩ : syracuseStep 1994515 = 2991773) B2991773
theorem B4487669 : Blo 1993435 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B2991779 : Blo 1993435 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B1994519 : Blo 1993435 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B3838141 : Blo 1993435 3838141 := bbase (se 3 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 3838141 = 1439303) (by norm_num)
theorem B5117521 : Blo 1993435 5117521 := bstep (se 2 (by rfl) ⟨1919070, by rfl⟩ : syracuseStep 5117521 = 3838141) B3838141
theorem B6823361 : Blo 1993435 6823361 := bstep (se 2 (by rfl) ⟨2558760, by rfl⟩ : syracuseStep 6823361 = 5117521) B5117521
theorem B4548907 : Blo 1993435 4548907 := bstep (se 1 (by rfl) ⟨3411680, by rfl⟩ : syracuseStep 4548907 = 6823361) B6823361
theorem B6065209 : Blo 1993435 6065209 := bstep (se 2 (by rfl) ⟨2274453, by rfl⟩ : syracuseStep 6065209 = 4548907) B4548907
theorem B32347781 : Blo 1993435 32347781 := bstep (se 4 (by rfl) ⟨3032604, by rfl⟩ : syracuseStep 32347781 = 6065209) B6065209
theorem B21565187 : Blo 1993435 21565187 := bstep (se 1 (by rfl) ⟨16173890, by rfl⟩ : syracuseStep 21565187 = 32347781) B32347781
theorem B14376791 : Blo 1993435 14376791 := bstep (se 1 (by rfl) ⟨10782593, by rfl⟩ : syracuseStep 14376791 = 21565187) B21565187
theorem B38338109 : Blo 1993435 38338109 := bstep (se 3 (by rfl) ⟨7188395, by rfl⟩ : syracuseStep 38338109 = 14376791) B14376791
theorem B25558739 : Blo 1993435 25558739 := bstep (se 1 (by rfl) ⟨19169054, by rfl⟩ : syracuseStep 25558739 = 38338109) B38338109
theorem B17039159 : Blo 1993435 17039159 := bstep (se 1 (by rfl) ⟨12779369, by rfl⟩ : syracuseStep 17039159 = 25558739) B25558739
theorem B11359439 : Blo 1993435 11359439 := bstep (se 1 (by rfl) ⟨8519579, by rfl⟩ : syracuseStep 11359439 = 17039159) B17039159
theorem B7572959 : Blo 1993435 7572959 := bstep (se 1 (by rfl) ⟨5679719, by rfl⟩ : syracuseStep 7572959 = 11359439) B11359439
theorem B5048639 : Blo 1993435 5048639 := bstep (se 1 (by rfl) ⟨3786479, by rfl⟩ : syracuseStep 5048639 = 7572959) B7572959
theorem B3365759 : Blo 1993435 3365759 := bstep (se 1 (by rfl) ⟨2524319, by rfl⟩ : syracuseStep 3365759 = 5048639) B5048639
theorem B2243839 : Blo 1993435 2243839 := bstep (se 1 (by rfl) ⟨1682879, by rfl⟩ : syracuseStep 2243839 = 3365759) B3365759
theorem B2991785 : Blo 1993435 2991785 := bstep (se 2 (by rfl) ⟨1121919, by rfl⟩ : syracuseStep 2991785 = 2243839) B2243839
theorem B1994523 : Blo 1993435 1994523 := bstep (se 1 (by rfl) ⟨1495892, by rfl⟩ : syracuseStep 1994523 = 2991785) B2991785
theorem B2396137 : Blo 1993435 2396137 := bbase (se 2 (by rfl) ⟨898551, by rfl⟩ : syracuseStep 2396137 = 1797103) (by norm_num)
theorem B3194849 : Blo 1993435 3194849 := bstep (se 2 (by rfl) ⟨1198068, by rfl⟩ : syracuseStep 3194849 = 2396137) B2396137
theorem B2129899 : Blo 1993435 2129899 := bstep (se 1 (by rfl) ⟨1597424, by rfl⟩ : syracuseStep 2129899 = 3194849) B3194849
theorem B2839865 : Blo 1993435 2839865 := bstep (se 2 (by rfl) ⟨1064949, by rfl⟩ : syracuseStep 2839865 = 2129899) B2129899
theorem B7572973 : Blo 1993435 7572973 := bstep (se 3 (by rfl) ⟨1419932, by rfl⟩ : syracuseStep 7572973 = 2839865) B2839865
theorem B10097297 : Blo 1993435 10097297 := bstep (se 2 (by rfl) ⟨3786486, by rfl⟩ : syracuseStep 10097297 = 7572973) B7572973
theorem B6731531 : Blo 1993435 6731531 := bstep (se 1 (by rfl) ⟨5048648, by rfl⟩ : syracuseStep 6731531 = 10097297) B10097297
theorem B4487687 : Blo 1993435 4487687 := bstep (se 1 (by rfl) ⟨3365765, by rfl⟩ : syracuseStep 4487687 = 6731531) B6731531
theorem B2991791 : Blo 1993435 2991791 := bstep (se 1 (by rfl) ⟨2243843, by rfl⟩ : syracuseStep 2991791 = 4487687) B4487687
theorem B1994527 : Blo 1993435 1994527 := bstep (se 1 (by rfl) ⟨1495895, by rfl⟩ : syracuseStep 1994527 = 2991791) B2991791
theorem B2991797 : Blo 1993435 2991797 := bbase (se 5 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 2991797 = 280481) (by norm_num)
theorem B1994531 : Blo 1993435 1994531 := bstep (se 1 (by rfl) ⟨1495898, by rfl⟩ : syracuseStep 1994531 = 2991797) B2991797
theorem B5048669 : Blo 1993435 5048669 := bbase (se 3 (by rfl) ⟨946625, by rfl⟩ : syracuseStep 5048669 = 1893251) (by norm_num)
theorem B3365779 : Blo 1993435 3365779 := bstep (se 1 (by rfl) ⟨2524334, by rfl⟩ : syracuseStep 3365779 = 5048669) B5048669
theorem B4487705 : Blo 1993435 4487705 := bstep (se 2 (by rfl) ⟨1682889, by rfl⟩ : syracuseStep 4487705 = 3365779) B3365779
theorem B2991803 : Blo 1993435 2991803 := bstep (se 1 (by rfl) ⟨2243852, by rfl⟩ : syracuseStep 2991803 = 4487705) B4487705
theorem B1994535 : Blo 1993435 1994535 := bstep (se 1 (by rfl) ⟨1495901, by rfl⟩ : syracuseStep 1994535 = 2991803) B2991803
theorem B2243857 : Blo 1993435 2243857 := bbase (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) (by norm_num)
theorem B2991809 : Blo 1993435 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B1994539 : Blo 1993435 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B3786517 : Blo 1993435 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B5048689 : Blo 1993435 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B6731585 : Blo 1993435 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B4487723 : Blo 1993435 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B2991815 : Blo 1993435 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B1994543 : Blo 1993435 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B2991821 : Blo 1993435 2991821 := bbase (se 3 (by rfl) ⟨560966, by rfl⟩ : syracuseStep 2991821 = 1121933) (by norm_num)
theorem B1994547 : Blo 1993435 1994547 := bstep (se 1 (by rfl) ⟨1495910, by rfl⟩ : syracuseStep 1994547 = 2991821) B2991821
theorem B4487741 : Blo 1993435 4487741 := bbase (se 3 (by rfl) ⟨841451, by rfl⟩ : syracuseStep 4487741 = 1682903) (by norm_num)
theorem B2991827 : Blo 1993435 2991827 := bstep (se 1 (by rfl) ⟨2243870, by rfl⟩ : syracuseStep 2991827 = 4487741) B4487741
theorem B1994551 : Blo 1993435 1994551 := bstep (se 1 (by rfl) ⟨1495913, by rfl⟩ : syracuseStep 1994551 = 2991827) B2991827
theorem B3365813 : Blo 1993435 3365813 := bbase (se 5 (by rfl) ⟨157772, by rfl⟩ : syracuseStep 3365813 = 315545) (by norm_num)
theorem B2243875 : Blo 1993435 2243875 := bstep (se 1 (by rfl) ⟨1682906, by rfl⟩ : syracuseStep 2243875 = 3365813) B3365813
theorem B2991833 : Blo 1993435 2991833 := bstep (se 2 (by rfl) ⟨1121937, by rfl⟩ : syracuseStep 2991833 = 2243875) B2243875
theorem B1994555 : Blo 1993435 1994555 := bstep (se 1 (by rfl) ⟨1495916, by rfl⟩ : syracuseStep 1994555 = 2991833) B2991833
theorem B2129933 : Blo 1993435 2129933 := bbase (se 3 (by rfl) ⟨399362, by rfl⟩ : syracuseStep 2129933 = 798725) (by norm_num)
theorem B5679821 : Blo 1993435 5679821 := bstep (se 3 (by rfl) ⟨1064966, by rfl⟩ : syracuseStep 5679821 = 2129933) B2129933
theorem B15146189 : Blo 1993435 15146189 := bstep (se 3 (by rfl) ⟨2839910, by rfl⟩ : syracuseStep 15146189 = 5679821) B5679821
theorem B10097459 : Blo 1993435 10097459 := bstep (se 1 (by rfl) ⟨7573094, by rfl⟩ : syracuseStep 10097459 = 15146189) B15146189
theorem B6731639 : Blo 1993435 6731639 := bstep (se 1 (by rfl) ⟨5048729, by rfl⟩ : syracuseStep 6731639 = 10097459) B10097459
theorem B4487759 : Blo 1993435 4487759 := bstep (se 1 (by rfl) ⟨3365819, by rfl⟩ : syracuseStep 4487759 = 6731639) B6731639
theorem B2991839 : Blo 1993435 2991839 := bstep (se 1 (by rfl) ⟨2243879, by rfl⟩ : syracuseStep 2991839 = 4487759) B4487759
theorem B1994559 : Blo 1993435 1994559 := bstep (se 1 (by rfl) ⟨1495919, by rfl⟩ : syracuseStep 1994559 = 2991839) B2991839
theorem B2991845 : Blo 1993435 2991845 := bbase (se 4 (by rfl) ⟨280485, by rfl⟩ : syracuseStep 2991845 = 560971) (by norm_num)
theorem B1994563 : Blo 1993435 1994563 := bstep (se 1 (by rfl) ⟨1495922, by rfl⟩ : syracuseStep 1994563 = 2991845) B2991845
theorem B5679845 : Blo 1993435 5679845 := bbase (se 4 (by rfl) ⟨532485, by rfl⟩ : syracuseStep 5679845 = 1064971) (by norm_num)
theorem B3786563 : Blo 1993435 3786563 := bstep (se 1 (by rfl) ⟨2839922, by rfl⟩ : syracuseStep 3786563 = 5679845) B5679845
theorem B2524375 : Blo 1993435 2524375 := bstep (se 1 (by rfl) ⟨1893281, by rfl⟩ : syracuseStep 2524375 = 3786563) B3786563
theorem B3365833 : Blo 1993435 3365833 := bstep (se 2 (by rfl) ⟨1262187, by rfl⟩ : syracuseStep 3365833 = 2524375) B2524375
theorem B4487777 : Blo 1993435 4487777 := bstep (se 2 (by rfl) ⟨1682916, by rfl⟩ : syracuseStep 4487777 = 3365833) B3365833
theorem B2991851 : Blo 1993435 2991851 := bstep (se 1 (by rfl) ⟨2243888, by rfl⟩ : syracuseStep 2991851 = 4487777) B4487777
theorem B1994567 : Blo 1993435 1994567 := bstep (se 1 (by rfl) ⟨1495925, by rfl⟩ : syracuseStep 1994567 = 2991851) B2991851
theorem B2243893 : Blo 1993435 2243893 := bbase (se 5 (by rfl) ⟨105182, by rfl⟩ : syracuseStep 2243893 = 210365) (by norm_num)
theorem B2991857 : Blo 1993435 2991857 := bstep (se 2 (by rfl) ⟨1121946, by rfl⟩ : syracuseStep 2991857 = 2243893) B2243893
theorem B1994571 : Blo 1993435 1994571 := bstep (se 1 (by rfl) ⟨1495928, by rfl⟩ : syracuseStep 1994571 = 2991857) B2991857
theorem B2524385 : Blo 1993435 2524385 := bbase (se 2 (by rfl) ⟨946644, by rfl⟩ : syracuseStep 2524385 = 1893289) (by norm_num)
theorem B6731693 : Blo 1993435 6731693 := bstep (se 3 (by rfl) ⟨1262192, by rfl⟩ : syracuseStep 6731693 = 2524385) B2524385
theorem B4487795 : Blo 1993435 4487795 := bstep (se 1 (by rfl) ⟨3365846, by rfl⟩ : syracuseStep 4487795 = 6731693) B6731693
theorem B2991863 : Blo 1993435 2991863 := bstep (se 1 (by rfl) ⟨2243897, by rfl⟩ : syracuseStep 2991863 = 4487795) B4487795
theorem B1994575 : Blo 1993435 1994575 := bstep (se 1 (by rfl) ⟨1495931, by rfl⟩ : syracuseStep 1994575 = 2991863) B2991863
theorem B2991869 : Blo 1993435 2991869 := bbase (se 3 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 2991869 = 1121951) (by norm_num)
theorem B1994579 : Blo 1993435 1994579 := bstep (se 1 (by rfl) ⟨1495934, by rfl⟩ : syracuseStep 1994579 = 2991869) B2991869
theorem B4487813 : Blo 1993435 4487813 := bbase (se 4 (by rfl) ⟨420732, by rfl⟩ : syracuseStep 4487813 = 841465) (by norm_num)
theorem B2991875 : Blo 1993435 2991875 := bstep (se 1 (by rfl) ⟨2243906, by rfl⟩ : syracuseStep 2991875 = 4487813) B4487813
theorem B1994583 : Blo 1993435 1994583 := bstep (se 1 (by rfl) ⟨1495937, by rfl⟩ : syracuseStep 1994583 = 2991875) B2991875
theorem B9584837 : Blo 1993435 9584837 := bbase (se 4 (by rfl) ⟨898578, by rfl⟩ : syracuseStep 9584837 = 1797157) (by norm_num)
theorem B6389891 : Blo 1993435 6389891 := bstep (se 1 (by rfl) ⟨4792418, by rfl⟩ : syracuseStep 6389891 = 9584837) B9584837
theorem B4259927 : Blo 1993435 4259927 := bstep (se 1 (by rfl) ⟨3194945, by rfl⟩ : syracuseStep 4259927 = 6389891) B6389891
theorem B2839951 : Blo 1993435 2839951 := bstep (se 1 (by rfl) ⟨2129963, by rfl⟩ : syracuseStep 2839951 = 4259927) B4259927
theorem B3786601 : Blo 1993435 3786601 := bstep (se 2 (by rfl) ⟨1419975, by rfl⟩ : syracuseStep 3786601 = 2839951) B2839951
theorem B5048801 : Blo 1993435 5048801 := bstep (se 2 (by rfl) ⟨1893300, by rfl⟩ : syracuseStep 5048801 = 3786601) B3786601
theorem B3365867 : Blo 1993435 3365867 := bstep (se 1 (by rfl) ⟨2524400, by rfl⟩ : syracuseStep 3365867 = 5048801) B5048801
theorem B2243911 : Blo 1993435 2243911 := bstep (se 1 (by rfl) ⟨1682933, by rfl⟩ : syracuseStep 2243911 = 3365867) B3365867
theorem B2991881 : Blo 1993435 2991881 := bstep (se 2 (by rfl) ⟨1121955, by rfl⟩ : syracuseStep 2991881 = 2243911) B2243911
theorem B1994587 : Blo 1993435 1994587 := bstep (se 1 (by rfl) ⟨1495940, by rfl⟩ : syracuseStep 1994587 = 2991881) B2991881
theorem B10097621 : Blo 1993435 10097621 := bbase (se 7 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 10097621 = 236663) (by norm_num)
theorem B6731747 : Blo 1993435 6731747 := bstep (se 1 (by rfl) ⟨5048810, by rfl⟩ : syracuseStep 6731747 = 10097621) B10097621
theorem B4487831 : Blo 1993435 4487831 := bstep (se 1 (by rfl) ⟨3365873, by rfl⟩ : syracuseStep 4487831 = 6731747) B6731747
theorem B2991887 : Blo 1993435 2991887 := bstep (se 1 (by rfl) ⟨2243915, by rfl⟩ : syracuseStep 2991887 = 4487831) B4487831
theorem B1994591 : Blo 1993435 1994591 := bstep (se 1 (by rfl) ⟨1495943, by rfl⟩ : syracuseStep 1994591 = 2991887) B2991887
theorem B2991893 : Blo 1993435 2991893 := bbase (se 6 (by rfl) ⟨70122, by rfl⟩ : syracuseStep 2991893 = 140245) (by norm_num)
theorem B1994595 : Blo 1993435 1994595 := bstep (se 1 (by rfl) ⟨1495946, by rfl⟩ : syracuseStep 1994595 = 2991893) B2991893
theorem B17746805 : Blo 1993435 17746805 := bbase (se 5 (by rfl) ⟨831881, by rfl⟩ : syracuseStep 17746805 = 1663763) (by norm_num)
theorem B11831203 : Blo 1993435 11831203 := bstep (se 1 (by rfl) ⟨8873402, by rfl⟩ : syracuseStep 11831203 = 17746805) B17746805
theorem B63099749 : Blo 1993435 63099749 := bstep (se 4 (by rfl) ⟨5915601, by rfl⟩ : syracuseStep 63099749 = 11831203) B11831203
theorem B168265997 : Blo 1993435 168265997 := bstep (se 3 (by rfl) ⟨31549874, by rfl⟩ : syracuseStep 168265997 = 63099749) B63099749
theorem B112177331 : Blo 1993435 112177331 := bstep (se 1 (by rfl) ⟨84132998, by rfl⟩ : syracuseStep 112177331 = 168265997) B168265997
theorem B74784887 : Blo 1993435 74784887 := bstep (se 1 (by rfl) ⟨56088665, by rfl⟩ : syracuseStep 74784887 = 112177331) B112177331
theorem B49856591 : Blo 1993435 49856591 := bstep (se 1 (by rfl) ⟨37392443, by rfl⟩ : syracuseStep 49856591 = 74784887) B74784887
theorem B132950909 : Blo 1993435 132950909 := bstep (se 3 (by rfl) ⟨24928295, by rfl⟩ : syracuseStep 132950909 = 49856591) B49856591
theorem B88633939 : Blo 1993435 88633939 := bstep (se 1 (by rfl) ⟨66475454, by rfl⟩ : syracuseStep 88633939 = 132950909) B132950909
theorem B118178585 : Blo 1993435 118178585 := bstep (se 2 (by rfl) ⟨44316969, by rfl⟩ : syracuseStep 118178585 = 88633939) B88633939
theorem B78785723 : Blo 1993435 78785723 := bstep (se 1 (by rfl) ⟨59089292, by rfl⟩ : syracuseStep 78785723 = 118178585) B118178585
theorem B52523815 : Blo 1993435 52523815 := bstep (se 1 (by rfl) ⟨39392861, by rfl⟩ : syracuseStep 52523815 = 78785723) B78785723
theorem B70031753 : Blo 1993435 70031753 := bstep (se 2 (by rfl) ⟨26261907, by rfl⟩ : syracuseStep 70031753 = 52523815) B52523815
theorem B46687835 : Blo 1993435 46687835 := bstep (se 1 (by rfl) ⟨35015876, by rfl⟩ : syracuseStep 46687835 = 70031753) B70031753
theorem B31125223 : Blo 1993435 31125223 := bstep (se 1 (by rfl) ⟨23343917, by rfl⟩ : syracuseStep 31125223 = 46687835) B46687835
theorem B41500297 : Blo 1993435 41500297 := bstep (se 2 (by rfl) ⟨15562611, by rfl⟩ : syracuseStep 41500297 = 31125223) B31125223
theorem B55333729 : Blo 1993435 55333729 := bstep (se 2 (by rfl) ⟨20750148, by rfl⟩ : syracuseStep 55333729 = 41500297) B41500297
theorem B73778305 : Blo 1993435 73778305 := bstep (se 2 (by rfl) ⟨27666864, by rfl⟩ : syracuseStep 73778305 = 55333729) B55333729
theorem B98371073 : Blo 1993435 98371073 := bstep (se 2 (by rfl) ⟨36889152, by rfl⟩ : syracuseStep 98371073 = 73778305) B73778305
theorem B65580715 : Blo 1993435 65580715 := bstep (se 1 (by rfl) ⟨49185536, by rfl⟩ : syracuseStep 65580715 = 98371073) B98371073
theorem B87440953 : Blo 1993435 87440953 := bstep (se 2 (by rfl) ⟨32790357, by rfl⟩ : syracuseStep 87440953 = 65580715) B65580715
theorem B116587937 : Blo 1993435 116587937 := bstep (se 2 (by rfl) ⟨43720476, by rfl⟩ : syracuseStep 116587937 = 87440953) B87440953
theorem B310901165 : Blo 1993435 310901165 := bstep (se 3 (by rfl) ⟨58293968, by rfl⟩ : syracuseStep 310901165 = 116587937) B116587937
theorem B207267443 : Blo 1993435 207267443 := bstep (se 1 (by rfl) ⟨155450582, by rfl⟩ : syracuseStep 207267443 = 310901165) B310901165
theorem B138178295 : Blo 1993435 138178295 := bstep (se 1 (by rfl) ⟨103633721, by rfl⟩ : syracuseStep 138178295 = 207267443) B207267443
theorem B92118863 : Blo 1993435 92118863 := bstep (se 1 (by rfl) ⟨69089147, by rfl⟩ : syracuseStep 92118863 = 138178295) B138178295
theorem B61412575 : Blo 1993435 61412575 := bstep (se 1 (by rfl) ⟨46059431, by rfl⟩ : syracuseStep 61412575 = 92118863) B92118863
theorem B81883433 : Blo 1993435 81883433 := bstep (se 2 (by rfl) ⟨30706287, by rfl⟩ : syracuseStep 81883433 = 61412575) B61412575
theorem B218355821 : Blo 1993435 218355821 := bstep (se 3 (by rfl) ⟨40941716, by rfl⟩ : syracuseStep 218355821 = 81883433) B81883433
theorem B145570547 : Blo 1993435 145570547 := bstep (se 1 (by rfl) ⟨109177910, by rfl⟩ : syracuseStep 145570547 = 218355821) B218355821
theorem B97047031 : Blo 1993435 97047031 := bstep (se 1 (by rfl) ⟨72785273, by rfl⟩ : syracuseStep 97047031 = 145570547) B145570547
theorem B129396041 : Blo 1993435 129396041 := bstep (se 2 (by rfl) ⟨48523515, by rfl⟩ : syracuseStep 129396041 = 97047031) B97047031
theorem B86264027 : Blo 1993435 86264027 := bstep (se 1 (by rfl) ⟨64698020, by rfl⟩ : syracuseStep 86264027 = 129396041) B129396041
theorem B57509351 : Blo 1993435 57509351 := bstep (se 1 (by rfl) ⟨43132013, by rfl⟩ : syracuseStep 57509351 = 86264027) B86264027
theorem B38339567 : Blo 1993435 38339567 := bstep (se 1 (by rfl) ⟨28754675, by rfl⟩ : syracuseStep 38339567 = 57509351) B57509351
theorem B25559711 : Blo 1993435 25559711 := bstep (se 1 (by rfl) ⟨19169783, by rfl⟩ : syracuseStep 25559711 = 38339567) B38339567
theorem B17039807 : Blo 1993435 17039807 := bstep (se 1 (by rfl) ⟨12779855, by rfl⟩ : syracuseStep 17039807 = 25559711) B25559711
theorem B11359871 : Blo 1993435 11359871 := bstep (se 1 (by rfl) ⟨8519903, by rfl⟩ : syracuseStep 11359871 = 17039807) B17039807
theorem B7573247 : Blo 1993435 7573247 := bstep (se 1 (by rfl) ⟨5679935, by rfl⟩ : syracuseStep 7573247 = 11359871) B11359871
theorem B5048831 : Blo 1993435 5048831 := bstep (se 1 (by rfl) ⟨3786623, by rfl⟩ : syracuseStep 5048831 = 7573247) B7573247
theorem B3365887 : Blo 1993435 3365887 := bstep (se 1 (by rfl) ⟨2524415, by rfl⟩ : syracuseStep 3365887 = 5048831) B5048831
theorem B4487849 : Blo 1993435 4487849 := bstep (se 2 (by rfl) ⟨1682943, by rfl⟩ : syracuseStep 4487849 = 3365887) B3365887
theorem B2991899 : Blo 1993435 2991899 := bstep (se 1 (by rfl) ⟨2243924, by rfl⟩ : syracuseStep 2991899 = 4487849) B4487849
theorem B1994599 : Blo 1993435 1994599 := bstep (se 1 (by rfl) ⟨1495949, by rfl⟩ : syracuseStep 1994599 = 2991899) B2991899
theorem B2243929 : Blo 1993435 2243929 := bbase (se 2 (by rfl) ⟨841473, by rfl⟩ : syracuseStep 2243929 = 1682947) (by norm_num)
theorem B2991905 : Blo 1993435 2991905 := bstep (se 2 (by rfl) ⟨1121964, by rfl⟩ : syracuseStep 2991905 = 2243929) B2243929
theorem B1994603 : Blo 1993435 1994603 := bstep (se 1 (by rfl) ⟨1495952, by rfl⟩ : syracuseStep 1994603 = 2991905) B2991905
theorem B2396233 : Blo 1993435 2396233 := bbase (se 2 (by rfl) ⟨898587, by rfl⟩ : syracuseStep 2396233 = 1797175) (by norm_num)
theorem B3194977 : Blo 1993435 3194977 := bstep (se 2 (by rfl) ⟨1198116, by rfl⟩ : syracuseStep 3194977 = 2396233) B2396233
theorem B4259969 : Blo 1993435 4259969 := bstep (se 2 (by rfl) ⟨1597488, by rfl⟩ : syracuseStep 4259969 = 3194977) B3194977
theorem B2839979 : Blo 1993435 2839979 := bstep (se 1 (by rfl) ⟨2129984, by rfl⟩ : syracuseStep 2839979 = 4259969) B4259969
theorem B7573277 : Blo 1993435 7573277 := bstep (se 3 (by rfl) ⟨1419989, by rfl⟩ : syracuseStep 7573277 = 2839979) B2839979
theorem B5048851 : Blo 1993435 5048851 := bstep (se 1 (by rfl) ⟨3786638, by rfl⟩ : syracuseStep 5048851 = 7573277) B7573277
theorem B6731801 : Blo 1993435 6731801 := bstep (se 2 (by rfl) ⟨2524425, by rfl⟩ : syracuseStep 6731801 = 5048851) B5048851
theorem B4487867 : Blo 1993435 4487867 := bstep (se 1 (by rfl) ⟨3365900, by rfl⟩ : syracuseStep 4487867 = 6731801) B6731801
theorem B2991911 : Blo 1993435 2991911 := bstep (se 1 (by rfl) ⟨2243933, by rfl⟩ : syracuseStep 2991911 = 4487867) B4487867
theorem B1994607 : Blo 1993435 1994607 := bstep (se 1 (by rfl) ⟨1495955, by rfl⟩ : syracuseStep 1994607 = 2991911) B2991911
theorem B2991917 : Blo 1993435 2991917 := bbase (se 3 (by rfl) ⟨560984, by rfl⟩ : syracuseStep 2991917 = 1121969) (by norm_num)
theorem B1994611 : Blo 1993435 1994611 := bstep (se 1 (by rfl) ⟨1495958, by rfl⟩ : syracuseStep 1994611 = 2991917) B2991917
theorem B4487885 : Blo 1993435 4487885 := bbase (se 3 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 4487885 = 1682957) (by norm_num)
theorem B2991923 : Blo 1993435 2991923 := bstep (se 1 (by rfl) ⟨2243942, by rfl⟩ : syracuseStep 2991923 = 4487885) B4487885
theorem B1994615 : Blo 1993435 1994615 := bstep (se 1 (by rfl) ⟨1495961, by rfl⟩ : syracuseStep 1994615 = 2991923) B2991923
theorem B2524441 : Blo 1993435 2524441 := bbase (se 2 (by rfl) ⟨946665, by rfl⟩ : syracuseStep 2524441 = 1893331) (by norm_num)
theorem B3365921 : Blo 1993435 3365921 := bstep (se 2 (by rfl) ⟨1262220, by rfl⟩ : syracuseStep 3365921 = 2524441) B2524441
theorem B2243947 : Blo 1993435 2243947 := bstep (se 1 (by rfl) ⟨1682960, by rfl⟩ : syracuseStep 2243947 = 3365921) B3365921
theorem B2991929 : Blo 1993435 2991929 := bstep (se 2 (by rfl) ⟨1121973, by rfl⟩ : syracuseStep 2991929 = 2243947) B2243947
theorem B1994619 : Blo 1993435 1994619 := bstep (se 1 (by rfl) ⟨1495964, by rfl⟩ : syracuseStep 1994619 = 2991929) B2991929
theorem B8520005 : Blo 1993435 8520005 := bbase (se 4 (by rfl) ⟨798750, by rfl⟩ : syracuseStep 8520005 = 1597501) (by norm_num)
theorem B22720013 : Blo 1993435 22720013 := bstep (se 3 (by rfl) ⟨4260002, by rfl⟩ : syracuseStep 22720013 = 8520005) B8520005
theorem B15146675 : Blo 1993435 15146675 := bstep (se 1 (by rfl) ⟨11360006, by rfl⟩ : syracuseStep 15146675 = 22720013) B22720013
theorem B10097783 : Blo 1993435 10097783 := bstep (se 1 (by rfl) ⟨7573337, by rfl⟩ : syracuseStep 10097783 = 15146675) B15146675
theorem B6731855 : Blo 1993435 6731855 := bstep (se 1 (by rfl) ⟨5048891, by rfl⟩ : syracuseStep 6731855 = 10097783) B10097783
theorem B4487903 : Blo 1993435 4487903 := bstep (se 1 (by rfl) ⟨3365927, by rfl⟩ : syracuseStep 4487903 = 6731855) B6731855
theorem B2991935 : Blo 1993435 2991935 := bstep (se 1 (by rfl) ⟨2243951, by rfl⟩ : syracuseStep 2991935 = 4487903) B4487903
theorem B1994623 : Blo 1993435 1994623 := bstep (se 1 (by rfl) ⟨1495967, by rfl⟩ : syracuseStep 1994623 = 2991935) B2991935
theorem B2991941 : Blo 1993435 2991941 := bbase (se 4 (by rfl) ⟨280494, by rfl⟩ : syracuseStep 2991941 = 560989) (by norm_num)
theorem B1994627 : Blo 1993435 1994627 := bstep (se 1 (by rfl) ⟨1495970, by rfl⟩ : syracuseStep 1994627 = 2991941) B2991941
theorem B3365941 : Blo 1993435 3365941 := bbase (se 5 (by rfl) ⟨157778, by rfl⟩ : syracuseStep 3365941 = 315557) (by norm_num)
theorem B4487921 : Blo 1993435 4487921 := bstep (se 2 (by rfl) ⟨1682970, by rfl⟩ : syracuseStep 4487921 = 3365941) B3365941
theorem B2991947 : Blo 1993435 2991947 := bstep (se 1 (by rfl) ⟨2243960, by rfl⟩ : syracuseStep 2991947 = 4487921) B4487921
theorem B1994631 : Blo 1993435 1994631 := bstep (se 1 (by rfl) ⟨1495973, by rfl⟩ : syracuseStep 1994631 = 2991947) B2991947
theorem B2243965 : Blo 1993435 2243965 := bbase (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) (by norm_num)
theorem B2991953 : Blo 1993435 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B1994635 : Blo 1993435 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B6731909 : Blo 1993435 6731909 := bbase (se 4 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 6731909 = 1262233) (by norm_num)
theorem B4487939 : Blo 1993435 4487939 := bstep (se 1 (by rfl) ⟨3365954, by rfl⟩ : syracuseStep 4487939 = 6731909) B6731909
theorem B2991959 : Blo 1993435 2991959 := bstep (se 1 (by rfl) ⟨2243969, by rfl⟩ : syracuseStep 2991959 = 4487939) B4487939
theorem B1994639 : Blo 1993435 1994639 := bstep (se 1 (by rfl) ⟨1495979, by rfl⟩ : syracuseStep 1994639 = 2991959) B2991959
theorem B2991965 : Blo 1993435 2991965 := bbase (se 3 (by rfl) ⟨560993, by rfl⟩ : syracuseStep 2991965 = 1121987) (by norm_num)
theorem B1994643 : Blo 1993435 1994643 := bstep (se 1 (by rfl) ⟨1495982, by rfl⟩ : syracuseStep 1994643 = 2991965) B2991965
theorem B4487957 : Blo 1993435 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B2991971 : Blo 1993435 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B1994647 : Blo 1993435 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B7573445 : Blo 1993435 7573445 := bbase (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) (by norm_num)
theorem B5048963 : Blo 1993435 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B3365975 : Blo 1993435 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B2243983 : Blo 1993435 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B2991977 : Blo 1993435 2991977 := bstep (se 2 (by rfl) ⟨1121991, by rfl⟩ : syracuseStep 2991977 = 2243983) B2243983
theorem B1994651 : Blo 1993435 1994651 := bstep (se 1 (by rfl) ⟨1495988, by rfl⟩ : syracuseStep 1994651 = 2991977) B2991977
theorem B12131221 : Blo 1993435 12131221 := bbase (se 6 (by rfl) ⟨284325, by rfl⟩ : syracuseStep 12131221 = 568651) (by norm_num)
theorem B16174961 : Blo 1993435 16174961 := bstep (se 2 (by rfl) ⟨6065610, by rfl⟩ : syracuseStep 16174961 = 12131221) B12131221
theorem B10783307 : Blo 1993435 10783307 := bstep (se 1 (by rfl) ⟨8087480, by rfl⟩ : syracuseStep 10783307 = 16174961) B16174961
theorem B7188871 : Blo 1993435 7188871 := bstep (se 1 (by rfl) ⟨5391653, by rfl⟩ : syracuseStep 7188871 = 10783307) B10783307
theorem B9585161 : Blo 1993435 9585161 := bstep (se 2 (by rfl) ⟨3594435, by rfl⟩ : syracuseStep 9585161 = 7188871) B7188871
theorem B6390107 : Blo 1993435 6390107 := bstep (se 1 (by rfl) ⟨4792580, by rfl⟩ : syracuseStep 6390107 = 9585161) B9585161
theorem B4260071 : Blo 1993435 4260071 := bstep (se 1 (by rfl) ⟨3195053, by rfl⟩ : syracuseStep 4260071 = 6390107) B6390107
theorem B11360189 : Blo 1993435 11360189 := bstep (se 3 (by rfl) ⟨2130035, by rfl⟩ : syracuseStep 11360189 = 4260071) B4260071
theorem B7573459 : Blo 1993435 7573459 := bstep (se 1 (by rfl) ⟨5680094, by rfl⟩ : syracuseStep 7573459 = 11360189) B11360189
theorem B10097945 : Blo 1993435 10097945 := bstep (se 2 (by rfl) ⟨3786729, by rfl⟩ : syracuseStep 10097945 = 7573459) B7573459
theorem B6731963 : Blo 1993435 6731963 := bstep (se 1 (by rfl) ⟨5048972, by rfl⟩ : syracuseStep 6731963 = 10097945) B10097945
theorem B4487975 : Blo 1993435 4487975 := bstep (se 1 (by rfl) ⟨3365981, by rfl⟩ : syracuseStep 4487975 = 6731963) B6731963
theorem B2991983 : Blo 1993435 2991983 := bstep (se 1 (by rfl) ⟨2243987, by rfl⟩ : syracuseStep 2991983 = 4487975) B4487975
theorem B1994655 : Blo 1993435 1994655 := bstep (se 1 (by rfl) ⟨1495991, by rfl⟩ : syracuseStep 1994655 = 2991983) B2991983
theorem B2991989 : Blo 1993435 2991989 := bbase (se 5 (by rfl) ⟨140249, by rfl⟩ : syracuseStep 2991989 = 280499) (by norm_num)
theorem B1994659 : Blo 1993435 1994659 := bstep (se 1 (by rfl) ⟨1495994, by rfl⟩ : syracuseStep 1994659 = 2991989) B2991989
theorem B4549229 : Blo 1993435 4549229 := bbase (se 3 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 4549229 = 1705961) (by norm_num)
theorem B3032819 : Blo 1993435 3032819 := bstep (se 1 (by rfl) ⟨2274614, by rfl⟩ : syracuseStep 3032819 = 4549229) B4549229
theorem B2021879 : Blo 1993435 2021879 := bstep (se 1 (by rfl) ⟨1516409, by rfl⟩ : syracuseStep 2021879 = 3032819) B3032819
theorem B5391677 : Blo 1993435 5391677 := bstep (se 3 (by rfl) ⟨1010939, by rfl⟩ : syracuseStep 5391677 = 2021879) B2021879
theorem B3594451 : Blo 1993435 3594451 := bstep (se 1 (by rfl) ⟨2695838, by rfl⟩ : syracuseStep 3594451 = 5391677) B5391677
theorem B4792601 : Blo 1993435 4792601 := bstep (se 2 (by rfl) ⟨1797225, by rfl⟩ : syracuseStep 4792601 = 3594451) B3594451
theorem B3195067 : Blo 1993435 3195067 := bstep (se 1 (by rfl) ⟨2396300, by rfl⟩ : syracuseStep 3195067 = 4792601) B4792601
theorem B4260089 : Blo 1993435 4260089 := bstep (se 2 (by rfl) ⟨1597533, by rfl⟩ : syracuseStep 4260089 = 3195067) B3195067
theorem B2840059 : Blo 1993435 2840059 := bstep (se 1 (by rfl) ⟨2130044, by rfl⟩ : syracuseStep 2840059 = 4260089) B4260089
theorem B3786745 : Blo 1993435 3786745 := bstep (se 2 (by rfl) ⟨1420029, by rfl⟩ : syracuseStep 3786745 = 2840059) B2840059
theorem B5048993 : Blo 1993435 5048993 := bstep (se 2 (by rfl) ⟨1893372, by rfl⟩ : syracuseStep 5048993 = 3786745) B3786745
theorem B3365995 : Blo 1993435 3365995 := bstep (se 1 (by rfl) ⟨2524496, by rfl⟩ : syracuseStep 3365995 = 5048993) B5048993
theorem B4487993 : Blo 1993435 4487993 := bstep (se 2 (by rfl) ⟨1682997, by rfl⟩ : syracuseStep 4487993 = 3365995) B3365995
theorem B2991995 : Blo 1993435 2991995 := bstep (se 1 (by rfl) ⟨2243996, by rfl⟩ : syracuseStep 2991995 = 4487993) B4487993
theorem B1994663 : Blo 1993435 1994663 := bstep (se 1 (by rfl) ⟨1495997, by rfl⟩ : syracuseStep 1994663 = 2991995) B2991995
theorem B2244001 : Blo 1993435 2244001 := bbase (se 2 (by rfl) ⟨841500, by rfl⟩ : syracuseStep 2244001 = 1683001) (by norm_num)
theorem B2992001 : Blo 1993435 2992001 := bstep (se 2 (by rfl) ⟨1122000, by rfl⟩ : syracuseStep 2992001 = 2244001) B2244001
theorem B1994667 : Blo 1993435 1994667 := bstep (se 1 (by rfl) ⟨1496000, by rfl⟩ : syracuseStep 1994667 = 2992001) B2992001
theorem B5049013 : Blo 1993435 5049013 := bbase (se 5 (by rfl) ⟨236672, by rfl⟩ : syracuseStep 5049013 = 473345) (by norm_num)
theorem B6732017 : Blo 1993435 6732017 := bstep (se 2 (by rfl) ⟨2524506, by rfl⟩ : syracuseStep 6732017 = 5049013) B5049013
theorem B4488011 : Blo 1993435 4488011 := bstep (se 1 (by rfl) ⟨3366008, by rfl⟩ : syracuseStep 4488011 = 6732017) B6732017
theorem B2992007 : Blo 1993435 2992007 := bstep (se 1 (by rfl) ⟨2244005, by rfl⟩ : syracuseStep 2992007 = 4488011) B4488011
theorem B1994671 : Blo 1993435 1994671 := bstep (se 1 (by rfl) ⟨1496003, by rfl⟩ : syracuseStep 1994671 = 2992007) B2992007
theorem B2992013 : Blo 1993435 2992013 := bbase (se 3 (by rfl) ⟨561002, by rfl⟩ : syracuseStep 2992013 = 1122005) (by norm_num)
theorem B1994675 : Blo 1993435 1994675 := bstep (se 1 (by rfl) ⟨1496006, by rfl⟩ : syracuseStep 1994675 = 2992013) B2992013
theorem B4488029 : Blo 1993435 4488029 := bbase (se 3 (by rfl) ⟨841505, by rfl⟩ : syracuseStep 4488029 = 1683011) (by norm_num)
theorem B2992019 : Blo 1993435 2992019 := bstep (se 1 (by rfl) ⟨2244014, by rfl⟩ : syracuseStep 2992019 = 4488029) B4488029
theorem B1994679 : Blo 1993435 1994679 := bstep (se 1 (by rfl) ⟨1496009, by rfl⟩ : syracuseStep 1994679 = 2992019) B2992019
theorem B3366029 : Blo 1993435 3366029 := bbase (se 3 (by rfl) ⟨631130, by rfl⟩ : syracuseStep 3366029 = 1262261) (by norm_num)
theorem B2244019 : Blo 1993435 2244019 := bstep (se 1 (by rfl) ⟨1683014, by rfl⟩ : syracuseStep 2244019 = 3366029) B3366029
theorem B2992025 : Blo 1993435 2992025 := bstep (se 2 (by rfl) ⟨1122009, by rfl⟩ : syracuseStep 2992025 = 2244019) B2244019
theorem B1994683 : Blo 1993435 1994683 := bstep (se 1 (by rfl) ⟨1496012, by rfl⟩ : syracuseStep 1994683 = 2992025) B2992025
theorem B3594493 : Blo 1993435 3594493 := bbase (se 3 (by rfl) ⟨673967, by rfl⟩ : syracuseStep 3594493 = 1347935) (by norm_num)
theorem B4792657 : Blo 1993435 4792657 := bstep (se 2 (by rfl) ⟨1797246, by rfl⟩ : syracuseStep 4792657 = 3594493) B3594493
theorem B6390209 : Blo 1993435 6390209 := bstep (se 2 (by rfl) ⟨2396328, by rfl⟩ : syracuseStep 6390209 = 4792657) B4792657
theorem B17040557 : Blo 1993435 17040557 := bstep (se 3 (by rfl) ⟨3195104, by rfl⟩ : syracuseStep 17040557 = 6390209) B6390209
theorem B11360371 : Blo 1993435 11360371 := bstep (se 1 (by rfl) ⟨8520278, by rfl⟩ : syracuseStep 11360371 = 17040557) B17040557
theorem B15147161 : Blo 1993435 15147161 := bstep (se 2 (by rfl) ⟨5680185, by rfl⟩ : syracuseStep 15147161 = 11360371) B11360371
theorem B10098107 : Blo 1993435 10098107 := bstep (se 1 (by rfl) ⟨7573580, by rfl⟩ : syracuseStep 10098107 = 15147161) B15147161
theorem B6732071 : Blo 1993435 6732071 := bstep (se 1 (by rfl) ⟨5049053, by rfl⟩ : syracuseStep 6732071 = 10098107) B10098107
theorem B4488047 : Blo 1993435 4488047 := bstep (se 1 (by rfl) ⟨3366035, by rfl⟩ : syracuseStep 4488047 = 6732071) B6732071
theorem B2992031 : Blo 1993435 2992031 := bstep (se 1 (by rfl) ⟨2244023, by rfl⟩ : syracuseStep 2992031 = 4488047) B4488047
theorem B1994687 : Blo 1993435 1994687 := bstep (se 1 (by rfl) ⟨1496015, by rfl⟩ : syracuseStep 1994687 = 2992031) B2992031
theorem B2992037 : Blo 1993435 2992037 := bbase (se 4 (by rfl) ⟨280503, by rfl⟩ : syracuseStep 2992037 = 561007) (by norm_num)
theorem B1994691 : Blo 1993435 1994691 := bstep (se 1 (by rfl) ⟨1496018, by rfl⟩ : syracuseStep 1994691 = 2992037) B2992037
theorem B2524537 : Blo 1993435 2524537 := bbase (se 2 (by rfl) ⟨946701, by rfl⟩ : syracuseStep 2524537 = 1893403) (by norm_num)
theorem B3366049 : Blo 1993435 3366049 := bstep (se 2 (by rfl) ⟨1262268, by rfl⟩ : syracuseStep 3366049 = 2524537) B2524537
theorem B4488065 : Blo 1993435 4488065 := bstep (se 2 (by rfl) ⟨1683024, by rfl⟩ : syracuseStep 4488065 = 3366049) B3366049
theorem B2992043 : Blo 1993435 2992043 := bstep (se 1 (by rfl) ⟨2244032, by rfl⟩ : syracuseStep 2992043 = 4488065) B4488065
theorem B1994695 : Blo 1993435 1994695 := bstep (se 1 (by rfl) ⟨1496021, by rfl⟩ : syracuseStep 1994695 = 2992043) B2992043
theorem B2244037 : Blo 1993435 2244037 := bbase (se 4 (by rfl) ⟨210378, by rfl⟩ : syracuseStep 2244037 = 420757) (by norm_num)
theorem B2992049 : Blo 1993435 2992049 := bstep (se 2 (by rfl) ⟨1122018, by rfl⟩ : syracuseStep 2992049 = 2244037) B2244037
theorem B1994699 : Blo 1993435 1994699 := bstep (se 1 (by rfl) ⟨1496024, by rfl⟩ : syracuseStep 1994699 = 2992049) B2992049
theorem B3786821 : Blo 1993435 3786821 := bbase (se 4 (by rfl) ⟨355014, by rfl⟩ : syracuseStep 3786821 = 710029) (by norm_num)
theorem B2524547 : Blo 1993435 2524547 := bstep (se 1 (by rfl) ⟨1893410, by rfl⟩ : syracuseStep 2524547 = 3786821) B3786821
theorem B6732125 : Blo 1993435 6732125 := bstep (se 3 (by rfl) ⟨1262273, by rfl⟩ : syracuseStep 6732125 = 2524547) B2524547
theorem B4488083 : Blo 1993435 4488083 := bstep (se 1 (by rfl) ⟨3366062, by rfl⟩ : syracuseStep 4488083 = 6732125) B6732125
theorem B2992055 : Blo 1993435 2992055 := bstep (se 1 (by rfl) ⟨2244041, by rfl⟩ : syracuseStep 2992055 = 4488083) B4488083
theorem B1994703 : Blo 1993435 1994703 := bstep (se 1 (by rfl) ⟨1496027, by rfl⟩ : syracuseStep 1994703 = 2992055) B2992055
theorem B2992061 : Blo 1993435 2992061 := bbase (se 3 (by rfl) ⟨561011, by rfl⟩ : syracuseStep 2992061 = 1122023) (by norm_num)
theorem B1994707 : Blo 1993435 1994707 := bstep (se 1 (by rfl) ⟨1496030, by rfl⟩ : syracuseStep 1994707 = 2992061) B2992061
theorem B4488101 : Blo 1993435 4488101 := bbase (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) (by norm_num)
theorem B2992067 : Blo 1993435 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B1994711 : Blo 1993435 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B5049125 : Blo 1993435 5049125 := bbase (se 4 (by rfl) ⟨473355, by rfl⟩ : syracuseStep 5049125 = 946711) (by norm_num)
theorem B3366083 : Blo 1993435 3366083 := bstep (se 1 (by rfl) ⟨2524562, by rfl⟩ : syracuseStep 3366083 = 5049125) B5049125
theorem B2244055 : Blo 1993435 2244055 := bstep (se 1 (by rfl) ⟨1683041, by rfl⟩ : syracuseStep 2244055 = 3366083) B3366083
theorem B2992073 : Blo 1993435 2992073 := bstep (se 2 (by rfl) ⟨1122027, by rfl⟩ : syracuseStep 2992073 = 2244055) B2244055
theorem B1994715 : Blo 1993435 1994715 := bstep (se 1 (by rfl) ⟨1496036, by rfl⟩ : syracuseStep 1994715 = 2992073) B2992073
theorem B5680277 : Blo 1993435 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B3786851 : Blo 1993435 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B10098269 : Blo 1993435 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B6732179 : Blo 1993435 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B4488119 : Blo 1993435 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B2992079 : Blo 1993435 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B1994719 : Blo 1993435 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B2992085 : Blo 1993435 2992085 := bbase (se 7 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 2992085 = 70127) (by norm_num)
theorem B1994723 : Blo 1993435 1994723 := bstep (se 1 (by rfl) ⟨1496042, by rfl⟩ : syracuseStep 1994723 = 2992085) B2992085
theorem B7573733 : Blo 1993435 7573733 := bbase (se 4 (by rfl) ⟨710037, by rfl⟩ : syracuseStep 7573733 = 1420075) (by norm_num)
theorem B5049155 : Blo 1993435 5049155 := bstep (se 1 (by rfl) ⟨3786866, by rfl⟩ : syracuseStep 5049155 = 7573733) B7573733
theorem B3366103 : Blo 1993435 3366103 := bstep (se 1 (by rfl) ⟨2524577, by rfl⟩ : syracuseStep 3366103 = 5049155) B5049155
theorem B4488137 : Blo 1993435 4488137 := bstep (se 2 (by rfl) ⟨1683051, by rfl⟩ : syracuseStep 4488137 = 3366103) B3366103
theorem B2992091 : Blo 1993435 2992091 := bstep (se 1 (by rfl) ⟨2244068, by rfl⟩ : syracuseStep 2992091 = 4488137) B4488137
theorem B1994727 : Blo 1993435 1994727 := bstep (se 1 (by rfl) ⟨1496045, by rfl⟩ : syracuseStep 1994727 = 2992091) B2992091
theorem B2244073 : Blo 1993435 2244073 := bbase (se 2 (by rfl) ⟨841527, by rfl⟩ : syracuseStep 2244073 = 1683055) (by norm_num)
theorem B2992097 : Blo 1993435 2992097 := bstep (se 2 (by rfl) ⟨1122036, by rfl⟩ : syracuseStep 2992097 = 2244073) B2244073
theorem B1994731 : Blo 1993435 1994731 := bstep (se 1 (by rfl) ⟨1496048, by rfl⟩ : syracuseStep 1994731 = 2992097) B2992097
theorem B2130121 : Blo 1993435 2130121 := bbase (se 2 (by rfl) ⟨798795, by rfl⟩ : syracuseStep 2130121 = 1597591) (by norm_num)
theorem B11360645 : Blo 1993435 11360645 := bstep (se 4 (by rfl) ⟨1065060, by rfl⟩ : syracuseStep 11360645 = 2130121) B2130121
theorem B7573763 : Blo 1993435 7573763 := bstep (se 1 (by rfl) ⟨5680322, by rfl⟩ : syracuseStep 7573763 = 11360645) B11360645
theorem B5049175 : Blo 1993435 5049175 := bstep (se 1 (by rfl) ⟨3786881, by rfl⟩ : syracuseStep 5049175 = 7573763) B7573763
theorem B6732233 : Blo 1993435 6732233 := bstep (se 2 (by rfl) ⟨2524587, by rfl⟩ : syracuseStep 6732233 = 5049175) B5049175
theorem B4488155 : Blo 1993435 4488155 := bstep (se 1 (by rfl) ⟨3366116, by rfl⟩ : syracuseStep 4488155 = 6732233) B6732233
theorem B2992103 : Blo 1993435 2992103 := bstep (se 1 (by rfl) ⟨2244077, by rfl⟩ : syracuseStep 2992103 = 4488155) B4488155
theorem B1994735 : Blo 1993435 1994735 := bstep (se 1 (by rfl) ⟨1496051, by rfl⟩ : syracuseStep 1994735 = 2992103) B2992103
theorem B2992109 : Blo 1993435 2992109 := bbase (se 3 (by rfl) ⟨561020, by rfl⟩ : syracuseStep 2992109 = 1122041) (by norm_num)
theorem B1994739 : Blo 1993435 1994739 := bstep (se 1 (by rfl) ⟨1496054, by rfl⟩ : syracuseStep 1994739 = 2992109) B2992109
theorem B4488173 : Blo 1993435 4488173 := bbase (se 3 (by rfl) ⟨841532, by rfl⟩ : syracuseStep 4488173 = 1683065) (by norm_num)
theorem B2992115 : Blo 1993435 2992115 := bstep (se 1 (by rfl) ⟨2244086, by rfl⟩ : syracuseStep 2992115 = 4488173) B4488173
theorem B1994743 : Blo 1993435 1994743 := bstep (se 1 (by rfl) ⟨1496057, by rfl⟩ : syracuseStep 1994743 = 2992115) B2992115
theorem B4260269 : Blo 1993435 4260269 := bbase (se 3 (by rfl) ⟨798800, by rfl⟩ : syracuseStep 4260269 = 1597601) (by norm_num)
theorem B2840179 : Blo 1993435 2840179 := bstep (se 1 (by rfl) ⟨2130134, by rfl⟩ : syracuseStep 2840179 = 4260269) B4260269
theorem B3786905 : Blo 1993435 3786905 := bstep (se 2 (by rfl) ⟨1420089, by rfl⟩ : syracuseStep 3786905 = 2840179) B2840179
theorem B2524603 : Blo 1993435 2524603 := bstep (se 1 (by rfl) ⟨1893452, by rfl⟩ : syracuseStep 2524603 = 3786905) B3786905
theorem B3366137 : Blo 1993435 3366137 := bstep (se 2 (by rfl) ⟨1262301, by rfl⟩ : syracuseStep 3366137 = 2524603) B2524603
theorem B2244091 : Blo 1993435 2244091 := bstep (se 1 (by rfl) ⟨1683068, by rfl⟩ : syracuseStep 2244091 = 3366137) B3366137
theorem B2992121 : Blo 1993435 2992121 := bstep (se 2 (by rfl) ⟨1122045, by rfl⟩ : syracuseStep 2992121 = 2244091) B2244091
theorem B1994747 : Blo 1993435 1994747 := bstep (se 1 (by rfl) ⟨1496060, by rfl⟩ : syracuseStep 1994747 = 2992121) B2992121
theorem B3282989 : Blo 1993435 3282989 := bbase (se 3 (by rfl) ⟨615560, by rfl⟩ : syracuseStep 3282989 = 1231121) (by norm_num)
theorem B8754637 : Blo 1993435 8754637 := bstep (se 3 (by rfl) ⟨1641494, by rfl⟩ : syracuseStep 8754637 = 3282989) B3282989
theorem B11672849 : Blo 1993435 11672849 := bstep (se 2 (by rfl) ⟨4377318, by rfl⟩ : syracuseStep 11672849 = 8754637) B8754637
theorem B7781899 : Blo 1993435 7781899 := bstep (se 1 (by rfl) ⟨5836424, by rfl⟩ : syracuseStep 7781899 = 11672849) B11672849
theorem B10375865 : Blo 1993435 10375865 := bstep (se 2 (by rfl) ⟨3890949, by rfl⟩ : syracuseStep 10375865 = 7781899) B7781899
theorem B6917243 : Blo 1993435 6917243 := bstep (se 1 (by rfl) ⟨5187932, by rfl⟩ : syracuseStep 6917243 = 10375865) B10375865
theorem B18445981 : Blo 1993435 18445981 := bstep (se 3 (by rfl) ⟨3458621, by rfl⟩ : syracuseStep 18445981 = 6917243) B6917243
theorem B24594641 : Blo 1993435 24594641 := bstep (se 2 (by rfl) ⟨9222990, by rfl⟩ : syracuseStep 24594641 = 18445981) B18445981
theorem B16396427 : Blo 1993435 16396427 := bstep (se 1 (by rfl) ⟨12297320, by rfl⟩ : syracuseStep 16396427 = 24594641) B24594641
theorem B10930951 : Blo 1993435 10930951 := bstep (se 1 (by rfl) ⟨8198213, by rfl⟩ : syracuseStep 10930951 = 16396427) B16396427
theorem B14574601 : Blo 1993435 14574601 := bstep (se 2 (by rfl) ⟨5465475, by rfl⟩ : syracuseStep 14574601 = 10930951) B10930951
theorem B19432801 : Blo 1993435 19432801 := bstep (se 2 (by rfl) ⟨7287300, by rfl⟩ : syracuseStep 19432801 = 14574601) B14574601
theorem B103641605 : Blo 1993435 103641605 := bstep (se 4 (by rfl) ⟨9716400, by rfl⟩ : syracuseStep 103641605 = 19432801) B19432801
theorem B69094403 : Blo 1993435 69094403 := bstep (se 1 (by rfl) ⟨51820802, by rfl⟩ : syracuseStep 69094403 = 103641605) B103641605
theorem B46062935 : Blo 1993435 46062935 := bstep (se 1 (by rfl) ⟨34547201, by rfl⟩ : syracuseStep 46062935 = 69094403) B69094403
theorem B30708623 : Blo 1993435 30708623 := bstep (se 1 (by rfl) ⟨23031467, by rfl⟩ : syracuseStep 30708623 = 46062935) B46062935
theorem B81889661 : Blo 1993435 81889661 := bstep (se 3 (by rfl) ⟨15354311, by rfl⟩ : syracuseStep 81889661 = 30708623) B30708623
theorem B218372429 : Blo 1993435 218372429 := bstep (se 3 (by rfl) ⟨40944830, by rfl⟩ : syracuseStep 218372429 = 81889661) B81889661
theorem B145581619 : Blo 1993435 145581619 := bstep (se 1 (by rfl) ⟨109186214, by rfl⟩ : syracuseStep 145581619 = 218372429) B218372429
theorem B194108825 : Blo 1993435 194108825 := bstep (se 2 (by rfl) ⟨72790809, by rfl⟩ : syracuseStep 194108825 = 145581619) B145581619
theorem B129405883 : Blo 1993435 129405883 := bstep (se 1 (by rfl) ⟨97054412, by rfl⟩ : syracuseStep 129405883 = 194108825) B194108825
theorem B172541177 : Blo 1993435 172541177 := bstep (se 2 (by rfl) ⟨64702941, by rfl⟩ : syracuseStep 172541177 = 129405883) B129405883
theorem B115027451 : Blo 1993435 115027451 := bstep (se 1 (by rfl) ⟨86270588, by rfl⟩ : syracuseStep 115027451 = 172541177) B172541177
theorem B76684967 : Blo 1993435 76684967 := bstep (se 1 (by rfl) ⟨57513725, by rfl⟩ : syracuseStep 76684967 = 115027451) B115027451
theorem B51123311 : Blo 1993435 51123311 := bstep (se 1 (by rfl) ⟨38342483, by rfl⟩ : syracuseStep 51123311 = 76684967) B76684967
theorem B34082207 : Blo 1993435 34082207 := bstep (se 1 (by rfl) ⟨25561655, by rfl⟩ : syracuseStep 34082207 = 51123311) B51123311
theorem B22721471 : Blo 1993435 22721471 := bstep (se 1 (by rfl) ⟨17041103, by rfl⟩ : syracuseStep 22721471 = 34082207) B34082207
theorem B15147647 : Blo 1993435 15147647 := bstep (se 1 (by rfl) ⟨11360735, by rfl⟩ : syracuseStep 15147647 = 22721471) B22721471
theorem B10098431 : Blo 1993435 10098431 := bstep (se 1 (by rfl) ⟨7573823, by rfl⟩ : syracuseStep 10098431 = 15147647) B15147647
theorem B6732287 : Blo 1993435 6732287 := bstep (se 1 (by rfl) ⟨5049215, by rfl⟩ : syracuseStep 6732287 = 10098431) B10098431
theorem B4488191 : Blo 1993435 4488191 := bstep (se 1 (by rfl) ⟨3366143, by rfl⟩ : syracuseStep 4488191 = 6732287) B6732287
theorem B2992127 : Blo 1993435 2992127 := bstep (se 1 (by rfl) ⟨2244095, by rfl⟩ : syracuseStep 2992127 = 4488191) B4488191
theorem B1994751 : Blo 1993435 1994751 := bstep (se 1 (by rfl) ⟨1496063, by rfl⟩ : syracuseStep 1994751 = 2992127) B2992127
theorem B2992133 : Blo 1993435 2992133 := bbase (se 4 (by rfl) ⟨280512, by rfl⟩ : syracuseStep 2992133 = 561025) (by norm_num)
theorem B1994755 : Blo 1993435 1994755 := bstep (se 1 (by rfl) ⟨1496066, by rfl⟩ : syracuseStep 1994755 = 2992133) B2992133
theorem B3366157 : Blo 1993435 3366157 := bbase (se 3 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 3366157 = 1262309) (by norm_num)
theorem B4488209 : Blo 1993435 4488209 := bstep (se 2 (by rfl) ⟨1683078, by rfl⟩ : syracuseStep 4488209 = 3366157) B3366157
theorem B2992139 : Blo 1993435 2992139 := bstep (se 1 (by rfl) ⟨2244104, by rfl⟩ : syracuseStep 2992139 = 4488209) B4488209
theorem B1994759 : Blo 1993435 1994759 := bstep (se 1 (by rfl) ⟨1496069, by rfl⟩ : syracuseStep 1994759 = 2992139) B2992139
theorem B2244109 : Blo 1993435 2244109 := bbase (se 3 (by rfl) ⟨420770, by rfl⟩ : syracuseStep 2244109 = 841541) (by norm_num)
theorem B2992145 : Blo 1993435 2992145 := bstep (se 2 (by rfl) ⟨1122054, by rfl⟩ : syracuseStep 2992145 = 2244109) B2244109
theorem B1994763 : Blo 1993435 1994763 := bstep (se 1 (by rfl) ⟨1496072, by rfl⟩ : syracuseStep 1994763 = 2992145) B2992145
theorem B6732341 : Blo 1993435 6732341 := bbase (se 5 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 6732341 = 631157) (by norm_num)
theorem B4488227 : Blo 1993435 4488227 := bstep (se 1 (by rfl) ⟨3366170, by rfl⟩ : syracuseStep 4488227 = 6732341) B6732341
theorem B2992151 : Blo 1993435 2992151 := bstep (se 1 (by rfl) ⟨2244113, by rfl⟩ : syracuseStep 2992151 = 4488227) B4488227
theorem B1994767 : Blo 1993435 1994767 := bstep (se 1 (by rfl) ⟨1496075, by rfl⟩ : syracuseStep 1994767 = 2992151) B2992151
theorem B2992157 : Blo 1993435 2992157 := bbase (se 3 (by rfl) ⟨561029, by rfl⟩ : syracuseStep 2992157 = 1122059) (by norm_num)
theorem B1994771 : Blo 1993435 1994771 := bstep (se 1 (by rfl) ⟨1496078, by rfl⟩ : syracuseStep 1994771 = 2992157) B2992157
theorem B4488245 : Blo 1993435 4488245 := bbase (se 5 (by rfl) ⟨210386, by rfl⟩ : syracuseStep 4488245 = 420773) (by norm_num)
theorem B2992163 : Blo 1993435 2992163 := bstep (se 1 (by rfl) ⟨2244122, by rfl⟩ : syracuseStep 2992163 = 4488245) B4488245
theorem B1994775 : Blo 1993435 1994775 := bstep (se 1 (by rfl) ⟨1496081, by rfl⟩ : syracuseStep 1994775 = 2992163) B2992163
theorem B3158837 : Blo 1993435 3158837 := bbase (se 5 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 3158837 = 296141) (by norm_num)
theorem B2105891 : Blo 1993435 2105891 := bstep (se 1 (by rfl) ⟨1579418, by rfl⟩ : syracuseStep 2105891 = 3158837) B3158837
theorem B22462837 : Blo 1993435 22462837 := bstep (se 5 (by rfl) ⟨1052945, by rfl⟩ : syracuseStep 22462837 = 2105891) B2105891
theorem B119801797 : Blo 1993435 119801797 := bstep (se 4 (by rfl) ⟨11231418, by rfl⟩ : syracuseStep 119801797 = 22462837) B22462837
theorem B638942917 : Blo 1993435 638942917 := bstep (se 4 (by rfl) ⟨59900898, by rfl⟩ : syracuseStep 638942917 = 119801797) B119801797
theorem B851923889 : Blo 1993435 851923889 := bstep (se 2 (by rfl) ⟨319471458, by rfl⟩ : syracuseStep 851923889 = 638942917) B638942917
theorem B567949259 : Blo 1993435 567949259 := bstep (se 1 (by rfl) ⟨425961944, by rfl⟩ : syracuseStep 567949259 = 851923889) B851923889
theorem B378632839 : Blo 1993435 378632839 := bstep (se 1 (by rfl) ⟨283974629, by rfl⟩ : syracuseStep 378632839 = 567949259) B567949259
theorem B504843785 : Blo 1993435 504843785 := bstep (se 2 (by rfl) ⟨189316419, by rfl⟩ : syracuseStep 504843785 = 378632839) B378632839
theorem B336562523 : Blo 1993435 336562523 := bstep (se 1 (by rfl) ⟨252421892, by rfl⟩ : syracuseStep 336562523 = 504843785) B504843785
theorem B224375015 : Blo 1993435 224375015 := bstep (se 1 (by rfl) ⟨168281261, by rfl⟩ : syracuseStep 224375015 = 336562523) B336562523
theorem B149583343 : Blo 1993435 149583343 := bstep (se 1 (by rfl) ⟨112187507, by rfl⟩ : syracuseStep 149583343 = 224375015) B224375015
theorem B199444457 : Blo 1993435 199444457 := bstep (se 2 (by rfl) ⟨74791671, by rfl⟩ : syracuseStep 199444457 = 149583343) B149583343
theorem B132962971 : Blo 1993435 132962971 := bstep (se 1 (by rfl) ⟨99722228, by rfl⟩ : syracuseStep 132962971 = 199444457) B199444457
theorem B177283961 : Blo 1993435 177283961 := bstep (se 2 (by rfl) ⟨66481485, by rfl⟩ : syracuseStep 177283961 = 132962971) B132962971
theorem B118189307 : Blo 1993435 118189307 := bstep (se 1 (by rfl) ⟨88641980, by rfl⟩ : syracuseStep 118189307 = 177283961) B177283961
theorem B78792871 : Blo 1993435 78792871 := bstep (se 1 (by rfl) ⟨59094653, by rfl⟩ : syracuseStep 78792871 = 118189307) B118189307
theorem B105057161 : Blo 1993435 105057161 := bstep (se 2 (by rfl) ⟨39396435, by rfl⟩ : syracuseStep 105057161 = 78792871) B78792871
theorem B70038107 : Blo 1993435 70038107 := bstep (se 1 (by rfl) ⟨52528580, by rfl⟩ : syracuseStep 70038107 = 105057161) B105057161
theorem B46692071 : Blo 1993435 46692071 := bstep (se 1 (by rfl) ⟨35019053, by rfl⟩ : syracuseStep 46692071 = 70038107) B70038107
theorem B31128047 : Blo 1993435 31128047 := bstep (se 1 (by rfl) ⟨23346035, by rfl⟩ : syracuseStep 31128047 = 46692071) B46692071
theorem B20752031 : Blo 1993435 20752031 := bstep (se 1 (by rfl) ⟨15564023, by rfl⟩ : syracuseStep 20752031 = 31128047) B31128047
theorem B13834687 : Blo 1993435 13834687 := bstep (se 1 (by rfl) ⟨10376015, by rfl⟩ : syracuseStep 13834687 = 20752031) B20752031
theorem B18446249 : Blo 1993435 18446249 := bstep (se 2 (by rfl) ⟨6917343, by rfl⟩ : syracuseStep 18446249 = 13834687) B13834687
theorem B49189997 : Blo 1993435 49189997 := bstep (se 3 (by rfl) ⟨9223124, by rfl⟩ : syracuseStep 49189997 = 18446249) B18446249
theorem B32793331 : Blo 1993435 32793331 := bstep (se 1 (by rfl) ⟨24594998, by rfl⟩ : syracuseStep 32793331 = 49189997) B49189997
theorem B43724441 : Blo 1993435 43724441 := bstep (se 2 (by rfl) ⟨16396665, by rfl⟩ : syracuseStep 43724441 = 32793331) B32793331
theorem B29149627 : Blo 1993435 29149627 := bstep (se 1 (by rfl) ⟨21862220, by rfl⟩ : syracuseStep 29149627 = 43724441) B43724441
theorem B38866169 : Blo 1993435 38866169 := bstep (se 2 (by rfl) ⟨14574813, by rfl⟩ : syracuseStep 38866169 = 29149627) B29149627
theorem B25910779 : Blo 1993435 25910779 := bstep (se 1 (by rfl) ⟨19433084, by rfl⟩ : syracuseStep 25910779 = 38866169) B38866169
theorem B34547705 : Blo 1993435 34547705 := bstep (se 2 (by rfl) ⟨12955389, by rfl⟩ : syracuseStep 34547705 = 25910779) B25910779
theorem B23031803 : Blo 1993435 23031803 := bstep (se 1 (by rfl) ⟨17273852, by rfl⟩ : syracuseStep 23031803 = 34547705) B34547705
theorem B15354535 : Blo 1993435 15354535 := bstep (se 1 (by rfl) ⟨11515901, by rfl⟩ : syracuseStep 15354535 = 23031803) B23031803
theorem B20472713 : Blo 1993435 20472713 := bstep (se 2 (by rfl) ⟨7677267, by rfl⟩ : syracuseStep 20472713 = 15354535) B15354535
theorem B13648475 : Blo 1993435 13648475 := bstep (se 1 (by rfl) ⟨10236356, by rfl⟩ : syracuseStep 13648475 = 20472713) B20472713
theorem B9098983 : Blo 1993435 9098983 := bstep (se 1 (by rfl) ⟨6824237, by rfl⟩ : syracuseStep 9098983 = 13648475) B13648475
theorem B12131977 : Blo 1993435 12131977 := bstep (se 2 (by rfl) ⟨4549491, by rfl⟩ : syracuseStep 12131977 = 9098983) B9098983
theorem B16175969 : Blo 1993435 16175969 := bstep (se 2 (by rfl) ⟨6065988, by rfl⟩ : syracuseStep 16175969 = 12131977) B12131977
theorem B10783979 : Blo 1993435 10783979 := bstep (se 1 (by rfl) ⟨8087984, by rfl⟩ : syracuseStep 10783979 = 16175969) B16175969
theorem B7189319 : Blo 1993435 7189319 := bstep (se 1 (by rfl) ⟨5391989, by rfl⟩ : syracuseStep 7189319 = 10783979) B10783979
theorem B4792879 : Blo 1993435 4792879 := bstep (se 1 (by rfl) ⟨3594659, by rfl⟩ : syracuseStep 4792879 = 7189319) B7189319
theorem B6390505 : Blo 1993435 6390505 := bstep (se 2 (by rfl) ⟨2396439, by rfl⟩ : syracuseStep 6390505 = 4792879) B4792879
theorem B8520673 : Blo 1993435 8520673 := bstep (se 2 (by rfl) ⟨3195252, by rfl⟩ : syracuseStep 8520673 = 6390505) B6390505
theorem B11360897 : Blo 1993435 11360897 := bstep (se 2 (by rfl) ⟨4260336, by rfl⟩ : syracuseStep 11360897 = 8520673) B8520673
theorem B7573931 : Blo 1993435 7573931 := bstep (se 1 (by rfl) ⟨5680448, by rfl⟩ : syracuseStep 7573931 = 11360897) B11360897
theorem B5049287 : Blo 1993435 5049287 := bstep (se 1 (by rfl) ⟨3786965, by rfl⟩ : syracuseStep 5049287 = 7573931) B7573931
theorem B3366191 : Blo 1993435 3366191 := bstep (se 1 (by rfl) ⟨2524643, by rfl⟩ : syracuseStep 3366191 = 5049287) B5049287
theorem B2244127 : Blo 1993435 2244127 := bstep (se 1 (by rfl) ⟨1683095, by rfl⟩ : syracuseStep 2244127 = 3366191) B3366191
theorem B2992169 : Blo 1993435 2992169 := bstep (se 2 (by rfl) ⟨1122063, by rfl⟩ : syracuseStep 2992169 = 2244127) B2244127
theorem B1994779 : Blo 1993435 1994779 := bstep (se 1 (by rfl) ⟨1496084, by rfl⟩ : syracuseStep 1994779 = 2992169) B2992169
theorem B6390517 : Blo 1993435 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B8520689 : Blo 1993435 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B5680459 : Blo 1993435 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B7573945 : Blo 1993435 7573945 := bstep (se 2 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 7573945 = 5680459) B5680459
theorem B10098593 : Blo 1993435 10098593 := bstep (se 2 (by rfl) ⟨3786972, by rfl⟩ : syracuseStep 10098593 = 7573945) B7573945
theorem B6732395 : Blo 1993435 6732395 := bstep (se 1 (by rfl) ⟨5049296, by rfl⟩ : syracuseStep 6732395 = 10098593) B10098593
theorem B4488263 : Blo 1993435 4488263 := bstep (se 1 (by rfl) ⟨3366197, by rfl⟩ : syracuseStep 4488263 = 6732395) B6732395
theorem B2992175 : Blo 1993435 2992175 := bstep (se 1 (by rfl) ⟨2244131, by rfl⟩ : syracuseStep 2992175 = 4488263) B4488263
theorem B1994783 : Blo 1993435 1994783 := bstep (se 1 (by rfl) ⟨1496087, by rfl⟩ : syracuseStep 1994783 = 2992175) B2992175
theorem B2992181 : Blo 1993435 2992181 := bbase (se 5 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 2992181 = 280517) (by norm_num)
theorem B1994787 : Blo 1993435 1994787 := bstep (se 1 (by rfl) ⟨1496090, by rfl⟩ : syracuseStep 1994787 = 2992181) B2992181
theorem B5049317 : Blo 1993435 5049317 := bbase (se 4 (by rfl) ⟨473373, by rfl⟩ : syracuseStep 5049317 = 946747) (by norm_num)
theorem B3366211 : Blo 1993435 3366211 := bstep (se 1 (by rfl) ⟨2524658, by rfl⟩ : syracuseStep 3366211 = 5049317) B5049317
theorem B4488281 : Blo 1993435 4488281 := bstep (se 2 (by rfl) ⟨1683105, by rfl⟩ : syracuseStep 4488281 = 3366211) B3366211
theorem B2992187 : Blo 1993435 2992187 := bstep (se 1 (by rfl) ⟨2244140, by rfl⟩ : syracuseStep 2992187 = 4488281) B4488281
theorem B1994791 : Blo 1993435 1994791 := bstep (se 1 (by rfl) ⟨1496093, by rfl⟩ : syracuseStep 1994791 = 2992187) B2992187
theorem B2244145 : Blo 1993435 2244145 := bbase (se 2 (by rfl) ⟨841554, by rfl⟩ : syracuseStep 2244145 = 1683109) (by norm_num)
theorem B2992193 : Blo 1993435 2992193 := bstep (se 2 (by rfl) ⟨1122072, by rfl⟩ : syracuseStep 2992193 = 2244145) B2244145
theorem B1994795 : Blo 1993435 1994795 := bstep (se 1 (by rfl) ⟨1496096, by rfl⟩ : syracuseStep 1994795 = 2992193) B2992193
theorem B2879005 : Blo 1993435 2879005 := bbase (se 3 (by rfl) ⟨539813, by rfl⟩ : syracuseStep 2879005 = 1079627) (by norm_num)
theorem B3838673 : Blo 1993435 3838673 := bstep (se 2 (by rfl) ⟨1439502, by rfl⟩ : syracuseStep 3838673 = 2879005) B2879005
theorem B2559115 : Blo 1993435 2559115 := bstep (se 1 (by rfl) ⟨1919336, by rfl⟩ : syracuseStep 2559115 = 3838673) B3838673
theorem B3412153 : Blo 1993435 3412153 := bstep (se 2 (by rfl) ⟨1279557, by rfl⟩ : syracuseStep 3412153 = 2559115) B2559115
theorem B4549537 : Blo 1993435 4549537 := bstep (se 2 (by rfl) ⟨1706076, by rfl⟩ : syracuseStep 4549537 = 3412153) B3412153
theorem B24264197 : Blo 1993435 24264197 := bstep (se 4 (by rfl) ⟨2274768, by rfl⟩ : syracuseStep 24264197 = 4549537) B4549537
theorem B16176131 : Blo 1993435 16176131 := bstep (se 1 (by rfl) ⟨12132098, by rfl⟩ : syracuseStep 16176131 = 24264197) B24264197
theorem B10784087 : Blo 1993435 10784087 := bstep (se 1 (by rfl) ⟨8088065, by rfl⟩ : syracuseStep 10784087 = 16176131) B16176131
theorem B7189391 : Blo 1993435 7189391 := bstep (se 1 (by rfl) ⟨5392043, by rfl⟩ : syracuseStep 7189391 = 10784087) B10784087
theorem B4792927 : Blo 1993435 4792927 := bstep (se 1 (by rfl) ⟨3594695, by rfl⟩ : syracuseStep 4792927 = 7189391) B7189391
theorem B6390569 : Blo 1993435 6390569 := bstep (se 2 (by rfl) ⟨2396463, by rfl⟩ : syracuseStep 6390569 = 4792927) B4792927
theorem B4260379 : Blo 1993435 4260379 := bstep (se 1 (by rfl) ⟨3195284, by rfl⟩ : syracuseStep 4260379 = 6390569) B6390569
theorem B5680505 : Blo 1993435 5680505 := bstep (se 2 (by rfl) ⟨2130189, by rfl⟩ : syracuseStep 5680505 = 4260379) B4260379
theorem B3787003 : Blo 1993435 3787003 := bstep (se 1 (by rfl) ⟨2840252, by rfl⟩ : syracuseStep 3787003 = 5680505) B5680505
theorem B5049337 : Blo 1993435 5049337 := bstep (se 2 (by rfl) ⟨1893501, by rfl⟩ : syracuseStep 5049337 = 3787003) B3787003
theorem B6732449 : Blo 1993435 6732449 := bstep (se 2 (by rfl) ⟨2524668, by rfl⟩ : syracuseStep 6732449 = 5049337) B5049337
theorem B4488299 : Blo 1993435 4488299 := bstep (se 1 (by rfl) ⟨3366224, by rfl⟩ : syracuseStep 4488299 = 6732449) B6732449
theorem B2992199 : Blo 1993435 2992199 := bstep (se 1 (by rfl) ⟨2244149, by rfl⟩ : syracuseStep 2992199 = 4488299) B4488299
theorem B1994799 : Blo 1993435 1994799 := bstep (se 1 (by rfl) ⟨1496099, by rfl⟩ : syracuseStep 1994799 = 2992199) B2992199
theorem B2992205 : Blo 1993435 2992205 := bbase (se 3 (by rfl) ⟨561038, by rfl⟩ : syracuseStep 2992205 = 1122077) (by norm_num)
theorem B1994803 : Blo 1993435 1994803 := bstep (se 1 (by rfl) ⟨1496102, by rfl⟩ : syracuseStep 1994803 = 2992205) B2992205
theorem B4488317 : Blo 1993435 4488317 := bbase (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) (by norm_num)
theorem B2992211 : Blo 1993435 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B1994807 : Blo 1993435 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B3366245 : Blo 1993435 3366245 := bbase (se 4 (by rfl) ⟨315585, by rfl⟩ : syracuseStep 3366245 = 631171) (by norm_num)
theorem B2244163 : Blo 1993435 2244163 := bstep (se 1 (by rfl) ⟨1683122, by rfl⟩ : syracuseStep 2244163 = 3366245) B3366245
theorem B2992217 : Blo 1993435 2992217 := bstep (se 2 (by rfl) ⟨1122081, by rfl⟩ : syracuseStep 2992217 = 2244163) B2244163
theorem B1994811 : Blo 1993435 1994811 := bstep (se 1 (by rfl) ⟨1496108, by rfl⟩ : syracuseStep 1994811 = 2992217) B2992217
theorem B4260413 : Blo 1993435 4260413 := bbase (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) (by norm_num)
theorem B2840275 : Blo 1993435 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B15148133 : Blo 1993435 15148133 := bstep (se 4 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 15148133 = 2840275) B2840275
theorem B10098755 : Blo 1993435 10098755 := bstep (se 1 (by rfl) ⟨7574066, by rfl⟩ : syracuseStep 10098755 = 15148133) B15148133
theorem B6732503 : Blo 1993435 6732503 := bstep (se 1 (by rfl) ⟨5049377, by rfl⟩ : syracuseStep 6732503 = 10098755) B10098755
theorem B4488335 : Blo 1993435 4488335 := bstep (se 1 (by rfl) ⟨3366251, by rfl⟩ : syracuseStep 4488335 = 6732503) B6732503
theorem B2992223 : Blo 1993435 2992223 := bstep (se 1 (by rfl) ⟨2244167, by rfl⟩ : syracuseStep 2992223 = 4488335) B4488335
theorem B1994815 : Blo 1993435 1994815 := bstep (se 1 (by rfl) ⟨1496111, by rfl⟩ : syracuseStep 1994815 = 2992223) B2992223
theorem B2992229 : Blo 1993435 2992229 := bbase (se 4 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 2992229 = 561043) (by norm_num)
theorem B1994819 : Blo 1993435 1994819 := bstep (se 1 (by rfl) ⟨1496114, by rfl⟩ : syracuseStep 1994819 = 2992229) B2992229
theorem B2022041 : Blo 1993435 2022041 := bbase (se 2 (by rfl) ⟨758265, by rfl⟩ : syracuseStep 2022041 = 1516531) (by norm_num)
theorem B5392109 : Blo 1993435 5392109 := bstep (se 3 (by rfl) ⟨1011020, by rfl⟩ : syracuseStep 5392109 = 2022041) B2022041
theorem B14378957 : Blo 1993435 14378957 := bstep (se 3 (by rfl) ⟨2696054, by rfl⟩ : syracuseStep 14378957 = 5392109) B5392109
theorem B9585971 : Blo 1993435 9585971 := bstep (se 1 (by rfl) ⟨7189478, by rfl⟩ : syracuseStep 9585971 = 14378957) B14378957
theorem B6390647 : Blo 1993435 6390647 := bstep (se 1 (by rfl) ⟨4792985, by rfl⟩ : syracuseStep 6390647 = 9585971) B9585971
theorem B4260431 : Blo 1993435 4260431 := bstep (se 1 (by rfl) ⟨3195323, by rfl⟩ : syracuseStep 4260431 = 6390647) B6390647
theorem B2840287 : Blo 1993435 2840287 := bstep (se 1 (by rfl) ⟨2130215, by rfl⟩ : syracuseStep 2840287 = 4260431) B4260431
theorem B3787049 : Blo 1993435 3787049 := bstep (se 2 (by rfl) ⟨1420143, by rfl⟩ : syracuseStep 3787049 = 2840287) B2840287
theorem B2524699 : Blo 1993435 2524699 := bstep (se 1 (by rfl) ⟨1893524, by rfl⟩ : syracuseStep 2524699 = 3787049) B3787049
theorem B3366265 : Blo 1993435 3366265 := bstep (se 2 (by rfl) ⟨1262349, by rfl⟩ : syracuseStep 3366265 = 2524699) B2524699
theorem B4488353 : Blo 1993435 4488353 := bstep (se 2 (by rfl) ⟨1683132, by rfl⟩ : syracuseStep 4488353 = 3366265) B3366265
theorem B2992235 : Blo 1993435 2992235 := bstep (se 1 (by rfl) ⟨2244176, by rfl⟩ : syracuseStep 2992235 = 4488353) B4488353
theorem B1994823 : Blo 1993435 1994823 := bstep (se 1 (by rfl) ⟨1496117, by rfl⟩ : syracuseStep 1994823 = 2992235) B2992235
theorem B2244181 : Blo 1993435 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B2992241 : Blo 1993435 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B1994827 : Blo 1993435 1994827 := bstep (se 1 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 1994827 = 2992241) B2992241
theorem B2524709 : Blo 1993435 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B6732557 : Blo 1993435 6732557 := bstep (se 3 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 6732557 = 2524709) B2524709
theorem B4488371 : Blo 1993435 4488371 := bstep (se 1 (by rfl) ⟨3366278, by rfl⟩ : syracuseStep 4488371 = 6732557) B6732557
theorem B2992247 : Blo 1993435 2992247 := bstep (se 1 (by rfl) ⟨2244185, by rfl⟩ : syracuseStep 2992247 = 4488371) B4488371
theorem B1994831 : Blo 1993435 1994831 := bstep (se 1 (by rfl) ⟨1496123, by rfl⟩ : syracuseStep 1994831 = 2992247) B2992247
theorem B2992253 : Blo 1993435 2992253 := bbase (se 3 (by rfl) ⟨561047, by rfl⟩ : syracuseStep 2992253 = 1122095) (by norm_num)
theorem B1994835 : Blo 1993435 1994835 := bstep (se 1 (by rfl) ⟨1496126, by rfl⟩ : syracuseStep 1994835 = 2992253) B2992253
theorem B4488389 : Blo 1993435 4488389 := bbase (se 4 (by rfl) ⟨420786, by rfl⟩ : syracuseStep 4488389 = 841573) (by norm_num)
theorem B2992259 : Blo 1993435 2992259 := bstep (se 1 (by rfl) ⟨2244194, by rfl⟩ : syracuseStep 2992259 = 4488389) B4488389
theorem B1994839 : Blo 1993435 1994839 := bstep (se 1 (by rfl) ⟨1496129, by rfl⟩ : syracuseStep 1994839 = 2992259) B2992259
theorem B8088245 : Blo 1993435 8088245 := bbase (se 5 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 8088245 = 758273) (by norm_num)
theorem B5392163 : Blo 1993435 5392163 := bstep (se 1 (by rfl) ⟨4044122, by rfl⟩ : syracuseStep 5392163 = 8088245) B8088245
theorem B3594775 : Blo 1993435 3594775 := bstep (se 1 (by rfl) ⟨2696081, by rfl⟩ : syracuseStep 3594775 = 5392163) B5392163
theorem B4793033 : Blo 1993435 4793033 := bstep (se 2 (by rfl) ⟨1797387, by rfl⟩ : syracuseStep 4793033 = 3594775) B3594775
theorem B12781421 : Blo 1993435 12781421 := bstep (se 3 (by rfl) ⟨2396516, by rfl⟩ : syracuseStep 12781421 = 4793033) B4793033
theorem B8520947 : Blo 1993435 8520947 := bstep (se 1 (by rfl) ⟨6390710, by rfl⟩ : syracuseStep 8520947 = 12781421) B12781421
theorem B5680631 : Blo 1993435 5680631 := bstep (se 1 (by rfl) ⟨4260473, by rfl⟩ : syracuseStep 5680631 = 8520947) B8520947
theorem B3787087 : Blo 1993435 3787087 := bstep (se 1 (by rfl) ⟨2840315, by rfl⟩ : syracuseStep 3787087 = 5680631) B5680631
theorem B5049449 : Blo 1993435 5049449 := bstep (se 2 (by rfl) ⟨1893543, by rfl⟩ : syracuseStep 5049449 = 3787087) B3787087
theorem B3366299 : Blo 1993435 3366299 := bstep (se 1 (by rfl) ⟨2524724, by rfl⟩ : syracuseStep 3366299 = 5049449) B5049449
theorem B2244199 : Blo 1993435 2244199 := bstep (se 1 (by rfl) ⟨1683149, by rfl⟩ : syracuseStep 2244199 = 3366299) B3366299
theorem B2992265 : Blo 1993435 2992265 := bstep (se 2 (by rfl) ⟨1122099, by rfl⟩ : syracuseStep 2992265 = 2244199) B2244199
theorem B1994843 : Blo 1993435 1994843 := bstep (se 1 (by rfl) ⟨1496132, by rfl⟩ : syracuseStep 1994843 = 2992265) B2992265
theorem B10098917 : Blo 1993435 10098917 := bbase (se 4 (by rfl) ⟨946773, by rfl⟩ : syracuseStep 10098917 = 1893547) (by norm_num)
theorem B6732611 : Blo 1993435 6732611 := bstep (se 1 (by rfl) ⟨5049458, by rfl⟩ : syracuseStep 6732611 = 10098917) B10098917
theorem B4488407 : Blo 1993435 4488407 := bstep (se 1 (by rfl) ⟨3366305, by rfl⟩ : syracuseStep 4488407 = 6732611) B6732611
theorem B2992271 : Blo 1993435 2992271 := bstep (se 1 (by rfl) ⟨2244203, by rfl⟩ : syracuseStep 2992271 = 4488407) B4488407
theorem B1994847 : Blo 1993435 1994847 := bstep (se 1 (by rfl) ⟨1496135, by rfl⟩ : syracuseStep 1994847 = 2992271) B2992271
theorem B2992277 : Blo 1993435 2992277 := bbase (se 6 (by rfl) ⟨70131, by rfl⟩ : syracuseStep 2992277 = 140263) (by norm_num)
theorem B1994851 : Blo 1993435 1994851 := bstep (se 1 (by rfl) ⟨1496138, by rfl⟩ : syracuseStep 1994851 = 2992277) B2992277
theorem B8520997 : Blo 1993435 8520997 := bbase (se 4 (by rfl) ⟨798843, by rfl⟩ : syracuseStep 8520997 = 1597687) (by norm_num)
theorem B11361329 : Blo 1993435 11361329 := bstep (se 2 (by rfl) ⟨4260498, by rfl⟩ : syracuseStep 11361329 = 8520997) B8520997
theorem B7574219 : Blo 1993435 7574219 := bstep (se 1 (by rfl) ⟨5680664, by rfl⟩ : syracuseStep 7574219 = 11361329) B11361329
theorem B5049479 : Blo 1993435 5049479 := bstep (se 1 (by rfl) ⟨3787109, by rfl⟩ : syracuseStep 5049479 = 7574219) B7574219
theorem B3366319 : Blo 1993435 3366319 := bstep (se 1 (by rfl) ⟨2524739, by rfl⟩ : syracuseStep 3366319 = 5049479) B5049479
theorem B4488425 : Blo 1993435 4488425 := bstep (se 2 (by rfl) ⟨1683159, by rfl⟩ : syracuseStep 4488425 = 3366319) B3366319
theorem B2992283 : Blo 1993435 2992283 := bstep (se 1 (by rfl) ⟨2244212, by rfl⟩ : syracuseStep 2992283 = 4488425) B4488425
theorem B1994855 : Blo 1993435 1994855 := bstep (se 1 (by rfl) ⟨1496141, by rfl⟩ : syracuseStep 1994855 = 2992283) B2992283
theorem B2244217 : Blo 1993435 2244217 := bbase (se 2 (by rfl) ⟨841581, by rfl⟩ : syracuseStep 2244217 = 1683163) (by norm_num)
theorem B2992289 : Blo 1993435 2992289 := bstep (se 2 (by rfl) ⟨1122108, by rfl⟩ : syracuseStep 2992289 = 2244217) B2244217
theorem B1994859 : Blo 1993435 1994859 := bstep (se 1 (by rfl) ⟨1496144, by rfl⟩ : syracuseStep 1994859 = 2992289) B2992289
theorem B7677589 : Blo 1993435 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B10236785 : Blo 1993435 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B27298093 : Blo 1993435 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B36397457 : Blo 1993435 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B24264971 : Blo 1993435 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B16176647 : Blo 1993435 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B10784431 : Blo 1993435 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B14379241 : Blo 1993435 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B19172321 : Blo 1993435 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B12781547 : Blo 1993435 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B8521031 : Blo 1993435 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B5680687 : Blo 1993435 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B7574249 : Blo 1993435 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B5049499 : Blo 1993435 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B6732665 : Blo 1993435 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B4488443 : Blo 1993435 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B2992295 : Blo 1993435 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B1994863 : Blo 1993435 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B2992301 : Blo 1993435 2992301 := bbase (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) (by norm_num)
theorem B1994867 : Blo 1993435 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B4488461 : Blo 1993435 4488461 := bbase (se 3 (by rfl) ⟨841586, by rfl⟩ : syracuseStep 4488461 = 1683173) (by norm_num)
theorem B2992307 : Blo 1993435 2992307 := bstep (se 1 (by rfl) ⟨2244230, by rfl⟩ : syracuseStep 2992307 = 4488461) B4488461
theorem B1994871 : Blo 1993435 1994871 := bstep (se 1 (by rfl) ⟨1496153, by rfl⟩ : syracuseStep 1994871 = 2992307) B2992307
theorem B2524765 : Blo 1993435 2524765 := bbase (se 3 (by rfl) ⟨473393, by rfl⟩ : syracuseStep 2524765 = 946787) (by norm_num)
theorem B3366353 : Blo 1993435 3366353 := bstep (se 2 (by rfl) ⟨1262382, by rfl⟩ : syracuseStep 3366353 = 2524765) B2524765
theorem B2244235 : Blo 1993435 2244235 := bstep (se 1 (by rfl) ⟨1683176, by rfl⟩ : syracuseStep 2244235 = 3366353) B3366353
theorem B2992313 : Blo 1993435 2992313 := bstep (se 2 (by rfl) ⟨1122117, by rfl⟩ : syracuseStep 2992313 = 2244235) B2244235
theorem B1994875 : Blo 1993435 1994875 := bstep (se 1 (by rfl) ⟨1496156, by rfl⟩ : syracuseStep 1994875 = 2992313) B2992313
theorem B17042197 : Blo 1993435 17042197 := bbase (se 6 (by rfl) ⟨399426, by rfl⟩ : syracuseStep 17042197 = 798853) (by norm_num)
theorem B22722929 : Blo 1993435 22722929 := bstep (se 2 (by rfl) ⟨8521098, by rfl⟩ : syracuseStep 22722929 = 17042197) B17042197
theorem B15148619 : Blo 1993435 15148619 := bstep (se 1 (by rfl) ⟨11361464, by rfl⟩ : syracuseStep 15148619 = 22722929) B22722929
theorem B10099079 : Blo 1993435 10099079 := bstep (se 1 (by rfl) ⟨7574309, by rfl⟩ : syracuseStep 10099079 = 15148619) B15148619
theorem B6732719 : Blo 1993435 6732719 := bstep (se 1 (by rfl) ⟨5049539, by rfl⟩ : syracuseStep 6732719 = 10099079) B10099079
theorem B4488479 : Blo 1993435 4488479 := bstep (se 1 (by rfl) ⟨3366359, by rfl⟩ : syracuseStep 4488479 = 6732719) B6732719
theorem B2992319 : Blo 1993435 2992319 := bstep (se 1 (by rfl) ⟨2244239, by rfl⟩ : syracuseStep 2992319 = 4488479) B4488479
theorem B1994879 : Blo 1993435 1994879 := bstep (se 1 (by rfl) ⟨1496159, by rfl⟩ : syracuseStep 1994879 = 2992319) B2992319
theorem B2992325 : Blo 1993435 2992325 := bbase (se 4 (by rfl) ⟨280530, by rfl⟩ : syracuseStep 2992325 = 561061) (by norm_num)
theorem B1994883 : Blo 1993435 1994883 := bstep (se 1 (by rfl) ⟨1496162, by rfl⟩ : syracuseStep 1994883 = 2992325) B2992325
theorem B3366373 : Blo 1993435 3366373 := bbase (se 4 (by rfl) ⟨315597, by rfl⟩ : syracuseStep 3366373 = 631195) (by norm_num)
theorem B4488497 : Blo 1993435 4488497 := bstep (se 2 (by rfl) ⟨1683186, by rfl⟩ : syracuseStep 4488497 = 3366373) B3366373
theorem B2992331 : Blo 1993435 2992331 := bstep (se 1 (by rfl) ⟨2244248, by rfl⟩ : syracuseStep 2992331 = 4488497) B4488497
theorem B1994887 : Blo 1993435 1994887 := bstep (se 1 (by rfl) ⟨1496165, by rfl⟩ : syracuseStep 1994887 = 2992331) B2992331
theorem B2244253 : Blo 1993435 2244253 := bbase (se 3 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 2244253 = 841595) (by norm_num)
theorem B2992337 : Blo 1993435 2992337 := bstep (se 2 (by rfl) ⟨1122126, by rfl⟩ : syracuseStep 2992337 = 2244253) B2244253
theorem B1994891 : Blo 1993435 1994891 := bstep (se 1 (by rfl) ⟨1496168, by rfl⟩ : syracuseStep 1994891 = 2992337) B2992337
theorem B6732773 : Blo 1993435 6732773 := bbase (se 4 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 6732773 = 1262395) (by norm_num)
theorem B4488515 : Blo 1993435 4488515 := bstep (se 1 (by rfl) ⟨3366386, by rfl⟩ : syracuseStep 4488515 = 6732773) B6732773
theorem B2992343 : Blo 1993435 2992343 := bstep (se 1 (by rfl) ⟨2244257, by rfl⟩ : syracuseStep 2992343 = 4488515) B4488515
theorem B1994895 : Blo 1993435 1994895 := bstep (se 1 (by rfl) ⟨1496171, by rfl⟩ : syracuseStep 1994895 = 2992343) B2992343
theorem B2992349 : Blo 1993435 2992349 := bbase (se 3 (by rfl) ⟨561065, by rfl⟩ : syracuseStep 2992349 = 1122131) (by norm_num)
theorem B1994899 : Blo 1993435 1994899 := bstep (se 1 (by rfl) ⟨1496174, by rfl⟩ : syracuseStep 1994899 = 2992349) B2992349
theorem B4488533 : Blo 1993435 4488533 := bbase (se 11 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 4488533 = 6575) (by norm_num)
theorem B2992355 : Blo 1993435 2992355 := bstep (se 1 (by rfl) ⟨2244266, by rfl⟩ : syracuseStep 2992355 = 4488533) B4488533
theorem B1994903 : Blo 1993435 1994903 := bstep (se 1 (by rfl) ⟨1496177, by rfl⟩ : syracuseStep 1994903 = 2992355) B2992355
theorem B2130305 : Blo 1993435 2130305 := bbase (se 2 (by rfl) ⟨798864, by rfl⟩ : syracuseStep 2130305 = 1597729) (by norm_num)
theorem B5680813 : Blo 1993435 5680813 := bstep (se 3 (by rfl) ⟨1065152, by rfl⟩ : syracuseStep 5680813 = 2130305) B2130305
theorem B7574417 : Blo 1993435 7574417 := bstep (se 2 (by rfl) ⟨2840406, by rfl⟩ : syracuseStep 7574417 = 5680813) B5680813
theorem B5049611 : Blo 1993435 5049611 := bstep (se 1 (by rfl) ⟨3787208, by rfl⟩ : syracuseStep 5049611 = 7574417) B7574417
theorem B3366407 : Blo 1993435 3366407 := bstep (se 1 (by rfl) ⟨2524805, by rfl⟩ : syracuseStep 3366407 = 5049611) B5049611
theorem B2244271 : Blo 1993435 2244271 := bstep (se 1 (by rfl) ⟨1683203, by rfl⟩ : syracuseStep 2244271 = 3366407) B3366407
theorem B2992361 : Blo 1993435 2992361 := bstep (se 2 (by rfl) ⟨1122135, by rfl⟩ : syracuseStep 2992361 = 2244271) B2244271
theorem B1994907 : Blo 1993435 1994907 := bstep (se 1 (by rfl) ⟨1496180, by rfl⟩ : syracuseStep 1994907 = 2992361) B2992361
theorem B8088517 : Blo 1993435 8088517 := bbase (se 4 (by rfl) ⟨758298, by rfl⟩ : syracuseStep 8088517 = 1516597) (by norm_num)
theorem B43138757 : Blo 1993435 43138757 := bstep (se 4 (by rfl) ⟨4044258, by rfl⟩ : syracuseStep 43138757 = 8088517) B8088517
theorem B28759171 : Blo 1993435 28759171 := bstep (se 1 (by rfl) ⟨21569378, by rfl⟩ : syracuseStep 28759171 = 43138757) B43138757
theorem B38345561 : Blo 1993435 38345561 := bstep (se 2 (by rfl) ⟨14379585, by rfl⟩ : syracuseStep 38345561 = 28759171) B28759171
theorem B25563707 : Blo 1993435 25563707 := bstep (se 1 (by rfl) ⟨19172780, by rfl⟩ : syracuseStep 25563707 = 38345561) B38345561
theorem B17042471 : Blo 1993435 17042471 := bstep (se 1 (by rfl) ⟨12781853, by rfl⟩ : syracuseStep 17042471 = 25563707) B25563707
theorem B11361647 : Blo 1993435 11361647 := bstep (se 1 (by rfl) ⟨8521235, by rfl⟩ : syracuseStep 11361647 = 17042471) B17042471
theorem B7574431 : Blo 1993435 7574431 := bstep (se 1 (by rfl) ⟨5680823, by rfl⟩ : syracuseStep 7574431 = 11361647) B11361647
theorem B10099241 : Blo 1993435 10099241 := bstep (se 2 (by rfl) ⟨3787215, by rfl⟩ : syracuseStep 10099241 = 7574431) B7574431
theorem B6732827 : Blo 1993435 6732827 := bstep (se 1 (by rfl) ⟨5049620, by rfl⟩ : syracuseStep 6732827 = 10099241) B10099241
theorem B4488551 : Blo 1993435 4488551 := bstep (se 1 (by rfl) ⟨3366413, by rfl⟩ : syracuseStep 4488551 = 6732827) B6732827
theorem B2992367 : Blo 1993435 2992367 := bstep (se 1 (by rfl) ⟨2244275, by rfl⟩ : syracuseStep 2992367 = 4488551) B4488551
theorem B1994911 : Blo 1993435 1994911 := bstep (se 1 (by rfl) ⟨1496183, by rfl⟩ : syracuseStep 1994911 = 2992367) B2992367
theorem B2992373 : Blo 1993435 2992373 := bbase (se 5 (by rfl) ⟨140267, by rfl⟩ : syracuseStep 2992373 = 280535) (by norm_num)
theorem B1994915 : Blo 1993435 1994915 := bstep (se 1 (by rfl) ⟨1496186, by rfl⟩ : syracuseStep 1994915 = 2992373) B2992373
theorem B4858613 : Blo 1993435 4858613 := bbase (se 5 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 4858613 = 455495) (by norm_num)
theorem B3239075 : Blo 1993435 3239075 := bstep (se 1 (by rfl) ⟨2429306, by rfl⟩ : syracuseStep 3239075 = 4858613) B4858613
theorem B2159383 : Blo 1993435 2159383 := bstep (se 1 (by rfl) ⟨1619537, by rfl⟩ : syracuseStep 2159383 = 3239075) B3239075
theorem B2879177 : Blo 1993435 2879177 := bstep (se 2 (by rfl) ⟨1079691, by rfl⟩ : syracuseStep 2879177 = 2159383) B2159383
theorem B30711221 : Blo 1993435 30711221 := bstep (se 5 (by rfl) ⟨1439588, by rfl⟩ : syracuseStep 30711221 = 2879177) B2879177
theorem B20474147 : Blo 1993435 20474147 := bstep (se 1 (by rfl) ⟨15355610, by rfl⟩ : syracuseStep 20474147 = 30711221) B30711221
theorem B54597725 : Blo 1993435 54597725 := bstep (se 3 (by rfl) ⟨10237073, by rfl⟩ : syracuseStep 54597725 = 20474147) B20474147
theorem B36398483 : Blo 1993435 36398483 := bstep (se 1 (by rfl) ⟨27298862, by rfl⟩ : syracuseStep 36398483 = 54597725) B54597725
theorem B24265655 : Blo 1993435 24265655 := bstep (se 1 (by rfl) ⟨18199241, by rfl⟩ : syracuseStep 24265655 = 36398483) B36398483
theorem B16177103 : Blo 1993435 16177103 := bstep (se 1 (by rfl) ⟨12132827, by rfl⟩ : syracuseStep 16177103 = 24265655) B24265655
theorem B10784735 : Blo 1993435 10784735 := bstep (se 1 (by rfl) ⟨8088551, by rfl⟩ : syracuseStep 10784735 = 16177103) B16177103
theorem B7189823 : Blo 1993435 7189823 := bstep (se 1 (by rfl) ⟨5392367, by rfl⟩ : syracuseStep 7189823 = 10784735) B10784735
theorem B19172861 : Blo 1993435 19172861 := bstep (se 3 (by rfl) ⟨3594911, by rfl⟩ : syracuseStep 19172861 = 7189823) B7189823
theorem B12781907 : Blo 1993435 12781907 := bstep (se 1 (by rfl) ⟨9586430, by rfl⟩ : syracuseStep 12781907 = 19172861) B19172861
theorem B8521271 : Blo 1993435 8521271 := bstep (se 1 (by rfl) ⟨6390953, by rfl⟩ : syracuseStep 8521271 = 12781907) B12781907
theorem B5680847 : Blo 1993435 5680847 := bstep (se 1 (by rfl) ⟨4260635, by rfl⟩ : syracuseStep 5680847 = 8521271) B8521271
theorem B3787231 : Blo 1993435 3787231 := bstep (se 1 (by rfl) ⟨2840423, by rfl⟩ : syracuseStep 3787231 = 5680847) B5680847
theorem B5049641 : Blo 1993435 5049641 := bstep (se 2 (by rfl) ⟨1893615, by rfl⟩ : syracuseStep 5049641 = 3787231) B3787231
theorem B3366427 : Blo 1993435 3366427 := bstep (se 1 (by rfl) ⟨2524820, by rfl⟩ : syracuseStep 3366427 = 5049641) B5049641
theorem B4488569 : Blo 1993435 4488569 := bstep (se 2 (by rfl) ⟨1683213, by rfl⟩ : syracuseStep 4488569 = 3366427) B3366427
theorem B2992379 : Blo 1993435 2992379 := bstep (se 1 (by rfl) ⟨2244284, by rfl⟩ : syracuseStep 2992379 = 4488569) B4488569
theorem B1994919 : Blo 1993435 1994919 := bstep (se 1 (by rfl) ⟨1496189, by rfl⟩ : syracuseStep 1994919 = 2992379) B2992379
theorem B2244289 : Blo 1993435 2244289 := bbase (se 2 (by rfl) ⟨841608, by rfl⟩ : syracuseStep 2244289 = 1683217) (by norm_num)
theorem B2992385 : Blo 1993435 2992385 := bstep (se 2 (by rfl) ⟨1122144, by rfl⟩ : syracuseStep 2992385 = 2244289) B2244289
theorem B1994923 : Blo 1993435 1994923 := bstep (se 1 (by rfl) ⟨1496192, by rfl⟩ : syracuseStep 1994923 = 2992385) B2992385
theorem B5049661 : Blo 1993435 5049661 := bbase (se 3 (by rfl) ⟨946811, by rfl⟩ : syracuseStep 5049661 = 1893623) (by norm_num)
theorem B6732881 : Blo 1993435 6732881 := bstep (se 2 (by rfl) ⟨2524830, by rfl⟩ : syracuseStep 6732881 = 5049661) B5049661
theorem B4488587 : Blo 1993435 4488587 := bstep (se 1 (by rfl) ⟨3366440, by rfl⟩ : syracuseStep 4488587 = 6732881) B6732881
theorem B2992391 : Blo 1993435 2992391 := bstep (se 1 (by rfl) ⟨2244293, by rfl⟩ : syracuseStep 2992391 = 4488587) B4488587
theorem B1994927 : Blo 1993435 1994927 := bstep (se 1 (by rfl) ⟨1496195, by rfl⟩ : syracuseStep 1994927 = 2992391) B2992391
theorem B2992397 : Blo 1993435 2992397 := bbase (se 3 (by rfl) ⟨561074, by rfl⟩ : syracuseStep 2992397 = 1122149) (by norm_num)
theorem B1994931 : Blo 1993435 1994931 := bstep (se 1 (by rfl) ⟨1496198, by rfl⟩ : syracuseStep 1994931 = 2992397) B2992397
theorem B4488605 : Blo 1993435 4488605 := bbase (se 3 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 4488605 = 1683227) (by norm_num)
theorem B2992403 : Blo 1993435 2992403 := bstep (se 1 (by rfl) ⟨2244302, by rfl⟩ : syracuseStep 2992403 = 4488605) B4488605
theorem B1994935 : Blo 1993435 1994935 := bstep (se 1 (by rfl) ⟨1496201, by rfl⟩ : syracuseStep 1994935 = 2992403) B2992403
theorem B3366461 : Blo 1993435 3366461 := bbase (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) (by norm_num)
theorem B2244307 : Blo 1993435 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B2992409 : Blo 1993435 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B1994939 : Blo 1993435 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B4044325 : Blo 1993435 4044325 := bbase (se 4 (by rfl) ⟨379155, by rfl⟩ : syracuseStep 4044325 = 758311) (by norm_num)
theorem B5392433 : Blo 1993435 5392433 := bstep (se 2 (by rfl) ⟨2022162, by rfl⟩ : syracuseStep 5392433 = 4044325) B4044325
theorem B3594955 : Blo 1993435 3594955 := bstep (se 1 (by rfl) ⟨2696216, by rfl⟩ : syracuseStep 3594955 = 5392433) B5392433
theorem B4793273 : Blo 1993435 4793273 := bstep (se 2 (by rfl) ⟨1797477, by rfl⟩ : syracuseStep 4793273 = 3594955) B3594955
theorem B3195515 : Blo 1993435 3195515 := bstep (se 1 (by rfl) ⟨2396636, by rfl⟩ : syracuseStep 3195515 = 4793273) B4793273
theorem B2130343 : Blo 1993435 2130343 := bstep (se 1 (by rfl) ⟨1597757, by rfl⟩ : syracuseStep 2130343 = 3195515) B3195515
theorem B11361829 : Blo 1993435 11361829 := bstep (se 4 (by rfl) ⟨1065171, by rfl⟩ : syracuseStep 11361829 = 2130343) B2130343
theorem B15149105 : Blo 1993435 15149105 := bstep (se 2 (by rfl) ⟨5680914, by rfl⟩ : syracuseStep 15149105 = 11361829) B11361829
theorem B10099403 : Blo 1993435 10099403 := bstep (se 1 (by rfl) ⟨7574552, by rfl⟩ : syracuseStep 10099403 = 15149105) B15149105
theorem B6732935 : Blo 1993435 6732935 := bstep (se 1 (by rfl) ⟨5049701, by rfl⟩ : syracuseStep 6732935 = 10099403) B10099403
theorem B4488623 : Blo 1993435 4488623 := bstep (se 1 (by rfl) ⟨3366467, by rfl⟩ : syracuseStep 4488623 = 6732935) B6732935
theorem B2992415 : Blo 1993435 2992415 := bstep (se 1 (by rfl) ⟨2244311, by rfl⟩ : syracuseStep 2992415 = 4488623) B4488623
theorem B1994943 : Blo 1993435 1994943 := bstep (se 1 (by rfl) ⟨1496207, by rfl⟩ : syracuseStep 1994943 = 2992415) B2992415
theorem B2992421 : Blo 1993435 2992421 := bbase (se 4 (by rfl) ⟨280539, by rfl⟩ : syracuseStep 2992421 = 561079) (by norm_num)
theorem B1994947 : Blo 1993435 1994947 := bstep (se 1 (by rfl) ⟨1496210, by rfl⟩ : syracuseStep 1994947 = 2992421) B2992421
theorem B2524861 : Blo 1993435 2524861 := bbase (se 3 (by rfl) ⟨473411, by rfl⟩ : syracuseStep 2524861 = 946823) (by norm_num)
theorem B3366481 : Blo 1993435 3366481 := bstep (se 2 (by rfl) ⟨1262430, by rfl⟩ : syracuseStep 3366481 = 2524861) B2524861
theorem B4488641 : Blo 1993435 4488641 := bstep (se 2 (by rfl) ⟨1683240, by rfl⟩ : syracuseStep 4488641 = 3366481) B3366481
theorem B2992427 : Blo 1993435 2992427 := bstep (se 1 (by rfl) ⟨2244320, by rfl⟩ : syracuseStep 2992427 = 4488641) B4488641
theorem B1994951 : Blo 1993435 1994951 := bstep (se 1 (by rfl) ⟨1496213, by rfl⟩ : syracuseStep 1994951 = 2992427) B2992427
theorem B2244325 : Blo 1993435 2244325 := bbase (se 4 (by rfl) ⟨210405, by rfl⟩ : syracuseStep 2244325 = 420811) (by norm_num)
theorem B2992433 : Blo 1993435 2992433 := bstep (se 2 (by rfl) ⟨1122162, by rfl⟩ : syracuseStep 2992433 = 2244325) B2244325
theorem B1994955 : Blo 1993435 1994955 := bstep (se 1 (by rfl) ⟨1496216, by rfl⟩ : syracuseStep 1994955 = 2992433) B2992433
theorem B3195541 : Blo 1993435 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B4260721 : Blo 1993435 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B5680961 : Blo 1993435 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B3787307 : Blo 1993435 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B2524871 : Blo 1993435 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B6732989 : Blo 1993435 6732989 := bstep (se 3 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 6732989 = 2524871) B2524871
theorem B4488659 : Blo 1993435 4488659 := bstep (se 1 (by rfl) ⟨3366494, by rfl⟩ : syracuseStep 4488659 = 6732989) B6732989
theorem B2992439 : Blo 1993435 2992439 := bstep (se 1 (by rfl) ⟨2244329, by rfl⟩ : syracuseStep 2992439 = 4488659) B4488659
theorem B1994959 : Blo 1993435 1994959 := bstep (se 1 (by rfl) ⟨1496219, by rfl⟩ : syracuseStep 1994959 = 2992439) B2992439
theorem B2992445 : Blo 1993435 2992445 := bbase (se 3 (by rfl) ⟨561083, by rfl⟩ : syracuseStep 2992445 = 1122167) (by norm_num)
theorem B1994963 : Blo 1993435 1994963 := bstep (se 1 (by rfl) ⟨1496222, by rfl⟩ : syracuseStep 1994963 = 2992445) B2992445
theorem B4488677 : Blo 1993435 4488677 := bbase (se 4 (by rfl) ⟨420813, by rfl⟩ : syracuseStep 4488677 = 841627) (by norm_num)
theorem B2992451 : Blo 1993435 2992451 := bstep (se 1 (by rfl) ⟨2244338, by rfl⟩ : syracuseStep 2992451 = 4488677) B4488677
theorem B1994967 : Blo 1993435 1994967 := bstep (se 1 (by rfl) ⟨1496225, by rfl⟩ : syracuseStep 1994967 = 2992451) B2992451
theorem B5049773 : Blo 1993435 5049773 := bbase (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) (by norm_num)
theorem B3366515 : Blo 1993435 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B2244343 : Blo 1993435 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B2992457 : Blo 1993435 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B1994971 : Blo 1993435 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B3595013 : Blo 1993435 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B2396675 : Blo 1993435 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B6391133 : Blo 1993435 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B4260755 : Blo 1993435 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B2840503 : Blo 1993435 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B3787337 : Blo 1993435 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B10099565 : Blo 1993435 10099565 := bstep (se 3 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 10099565 = 3787337) B3787337
theorem B6733043 : Blo 1993435 6733043 := bstep (se 1 (by rfl) ⟨5049782, by rfl⟩ : syracuseStep 6733043 = 10099565) B10099565
theorem B4488695 : Blo 1993435 4488695 := bstep (se 1 (by rfl) ⟨3366521, by rfl⟩ : syracuseStep 4488695 = 6733043) B6733043
theorem B2992463 : Blo 1993435 2992463 := bstep (se 1 (by rfl) ⟨2244347, by rfl⟩ : syracuseStep 2992463 = 4488695) B4488695
theorem B1994975 : Blo 1993435 1994975 := bstep (se 1 (by rfl) ⟨1496231, by rfl⟩ : syracuseStep 1994975 = 2992463) B2992463
theorem B2992469 : Blo 1993435 2992469 := bbase (se 10 (by rfl) ⟨4383, by rfl⟩ : syracuseStep 2992469 = 8767) (by norm_num)
theorem B1994979 : Blo 1993435 1994979 := bstep (se 1 (by rfl) ⟨1496234, by rfl⟩ : syracuseStep 1994979 = 2992469) B2992469
theorem B5681029 : Blo 1993435 5681029 := bbase (se 4 (by rfl) ⟨532596, by rfl⟩ : syracuseStep 5681029 = 1065193) (by norm_num)
theorem B7574705 : Blo 1993435 7574705 := bstep (se 2 (by rfl) ⟨2840514, by rfl⟩ : syracuseStep 7574705 = 5681029) B5681029
theorem B5049803 : Blo 1993435 5049803 := bstep (se 1 (by rfl) ⟨3787352, by rfl⟩ : syracuseStep 5049803 = 7574705) B7574705
theorem B3366535 : Blo 1993435 3366535 := bstep (se 1 (by rfl) ⟨2524901, by rfl⟩ : syracuseStep 3366535 = 5049803) B5049803
theorem B4488713 : Blo 1993435 4488713 := bstep (se 2 (by rfl) ⟨1683267, by rfl⟩ : syracuseStep 4488713 = 3366535) B3366535
theorem B2992475 : Blo 1993435 2992475 := bstep (se 1 (by rfl) ⟨2244356, by rfl⟩ : syracuseStep 2992475 = 4488713) B4488713
theorem B1994983 : Blo 1993435 1994983 := bstep (se 1 (by rfl) ⟨1496237, by rfl⟩ : syracuseStep 1994983 = 2992475) B2992475
theorem B2244361 : Blo 1993435 2244361 := bbase (se 2 (by rfl) ⟨841635, by rfl⟩ : syracuseStep 2244361 = 1683271) (by norm_num)
theorem B2992481 : Blo 1993435 2992481 := bstep (se 2 (by rfl) ⟨1122180, by rfl⟩ : syracuseStep 2992481 = 2244361) B2244361
theorem B1994987 : Blo 1993435 1994987 := bstep (se 1 (by rfl) ⟨1496240, by rfl⟩ : syracuseStep 1994987 = 2992481) B2992481
theorem B4044421 : Blo 1993435 4044421 := bbase (se 4 (by rfl) ⟨379164, by rfl⟩ : syracuseStep 4044421 = 758329) (by norm_num)
theorem B21570245 : Blo 1993435 21570245 := bstep (se 4 (by rfl) ⟨2022210, by rfl⟩ : syracuseStep 21570245 = 4044421) B4044421
theorem B14380163 : Blo 1993435 14380163 := bstep (se 1 (by rfl) ⟨10785122, by rfl⟩ : syracuseStep 14380163 = 21570245) B21570245
theorem B9586775 : Blo 1993435 9586775 := bstep (se 1 (by rfl) ⟨7190081, by rfl⟩ : syracuseStep 9586775 = 14380163) B14380163
theorem B25564733 : Blo 1993435 25564733 := bstep (se 3 (by rfl) ⟨4793387, by rfl⟩ : syracuseStep 25564733 = 9586775) B9586775
theorem B17043155 : Blo 1993435 17043155 := bstep (se 1 (by rfl) ⟨12782366, by rfl⟩ : syracuseStep 17043155 = 25564733) B25564733
theorem B11362103 : Blo 1993435 11362103 := bstep (se 1 (by rfl) ⟨8521577, by rfl⟩ : syracuseStep 11362103 = 17043155) B17043155
theorem B7574735 : Blo 1993435 7574735 := bstep (se 1 (by rfl) ⟨5681051, by rfl⟩ : syracuseStep 7574735 = 11362103) B11362103
theorem B5049823 : Blo 1993435 5049823 := bstep (se 1 (by rfl) ⟨3787367, by rfl⟩ : syracuseStep 5049823 = 7574735) B7574735
theorem B6733097 : Blo 1993435 6733097 := bstep (se 2 (by rfl) ⟨2524911, by rfl⟩ : syracuseStep 6733097 = 5049823) B5049823
theorem B4488731 : Blo 1993435 4488731 := bstep (se 1 (by rfl) ⟨3366548, by rfl⟩ : syracuseStep 4488731 = 6733097) B6733097
theorem B2992487 : Blo 1993435 2992487 := bstep (se 1 (by rfl) ⟨2244365, by rfl⟩ : syracuseStep 2992487 = 4488731) B4488731
theorem B1994991 : Blo 1993435 1994991 := bstep (se 1 (by rfl) ⟨1496243, by rfl⟩ : syracuseStep 1994991 = 2992487) B2992487
theorem B2992493 : Blo 1993435 2992493 := bbase (se 3 (by rfl) ⟨561092, by rfl⟩ : syracuseStep 2992493 = 1122185) (by norm_num)
theorem B1994995 : Blo 1993435 1994995 := bstep (se 1 (by rfl) ⟨1496246, by rfl⟩ : syracuseStep 1994995 = 2992493) B2992493
theorem B4488749 : Blo 1993435 4488749 := bbase (se 3 (by rfl) ⟨841640, by rfl⟩ : syracuseStep 4488749 = 1683281) (by norm_num)
theorem B2992499 : Blo 1993435 2992499 := bstep (se 1 (by rfl) ⟨2244374, by rfl⟩ : syracuseStep 2992499 = 4488749) B4488749
theorem B1994999 : Blo 1993435 1994999 := bstep (se 1 (by rfl) ⟨1496249, by rfl⟩ : syracuseStep 1994999 = 2992499) B2992499
theorem B5758597 : Blo 1993435 5758597 := bbase (se 4 (by rfl) ⟨539868, by rfl⟩ : syracuseStep 5758597 = 1079737) (by norm_num)
theorem B30712517 : Blo 1993435 30712517 := bstep (se 4 (by rfl) ⟨2879298, by rfl⟩ : syracuseStep 30712517 = 5758597) B5758597
theorem B20475011 : Blo 1993435 20475011 := bstep (se 1 (by rfl) ⟨15356258, by rfl⟩ : syracuseStep 20475011 = 30712517) B30712517
theorem B13650007 : Blo 1993435 13650007 := bstep (se 1 (by rfl) ⟨10237505, by rfl⟩ : syracuseStep 13650007 = 20475011) B20475011
theorem B18200009 : Blo 1993435 18200009 := bstep (se 2 (by rfl) ⟨6825003, by rfl⟩ : syracuseStep 18200009 = 13650007) B13650007
theorem B48533357 : Blo 1993435 48533357 := bstep (se 3 (by rfl) ⟨9100004, by rfl⟩ : syracuseStep 48533357 = 18200009) B18200009
theorem B32355571 : Blo 1993435 32355571 := bstep (se 1 (by rfl) ⟨24266678, by rfl⟩ : syracuseStep 32355571 = 48533357) B48533357
theorem B43140761 : Blo 1993435 43140761 := bstep (se 2 (by rfl) ⟨16177785, by rfl⟩ : syracuseStep 43140761 = 32355571) B32355571
theorem B28760507 : Blo 1993435 28760507 := bstep (se 1 (by rfl) ⟨21570380, by rfl⟩ : syracuseStep 28760507 = 43140761) B43140761
theorem B19173671 : Blo 1993435 19173671 := bstep (se 1 (by rfl) ⟨14380253, by rfl⟩ : syracuseStep 19173671 = 28760507) B28760507
theorem B12782447 : Blo 1993435 12782447 := bstep (se 1 (by rfl) ⟨9586835, by rfl⟩ : syracuseStep 12782447 = 19173671) B19173671
theorem B8521631 : Blo 1993435 8521631 := bstep (se 1 (by rfl) ⟨6391223, by rfl⟩ : syracuseStep 8521631 = 12782447) B12782447
theorem B5681087 : Blo 1993435 5681087 := bstep (se 1 (by rfl) ⟨4260815, by rfl⟩ : syracuseStep 5681087 = 8521631) B8521631
theorem B3787391 : Blo 1993435 3787391 := bstep (se 1 (by rfl) ⟨2840543, by rfl⟩ : syracuseStep 3787391 = 5681087) B5681087
theorem B2524927 : Blo 1993435 2524927 := bstep (se 1 (by rfl) ⟨1893695, by rfl⟩ : syracuseStep 2524927 = 3787391) B3787391
theorem B3366569 : Blo 1993435 3366569 := bstep (se 2 (by rfl) ⟨1262463, by rfl⟩ : syracuseStep 3366569 = 2524927) B2524927
theorem B2244379 : Blo 1993435 2244379 := bstep (se 1 (by rfl) ⟨1683284, by rfl⟩ : syracuseStep 2244379 = 3366569) B3366569
theorem B2992505 : Blo 1993435 2992505 := bstep (se 2 (by rfl) ⟨1122189, by rfl⟩ : syracuseStep 2992505 = 2244379) B2244379
theorem B1995003 : Blo 1993435 1995003 := bstep (se 1 (by rfl) ⟨1496252, by rfl⟩ : syracuseStep 1995003 = 2992505) B2992505
theorem B2396713 : Blo 1993435 2396713 := bbase (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) (by norm_num)
theorem B3195617 : Blo 1993435 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B34086581 : Blo 1993435 34086581 := bstep (se 5 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 34086581 = 3195617) B3195617
theorem B22724387 : Blo 1993435 22724387 := bstep (se 1 (by rfl) ⟨17043290, by rfl⟩ : syracuseStep 22724387 = 34086581) B34086581
theorem B15149591 : Blo 1993435 15149591 := bstep (se 1 (by rfl) ⟨11362193, by rfl⟩ : syracuseStep 15149591 = 22724387) B22724387
theorem B10099727 : Blo 1993435 10099727 := bstep (se 1 (by rfl) ⟨7574795, by rfl⟩ : syracuseStep 10099727 = 15149591) B15149591
theorem B6733151 : Blo 1993435 6733151 := bstep (se 1 (by rfl) ⟨5049863, by rfl⟩ : syracuseStep 6733151 = 10099727) B10099727
theorem B4488767 : Blo 1993435 4488767 := bstep (se 1 (by rfl) ⟨3366575, by rfl⟩ : syracuseStep 4488767 = 6733151) B6733151
theorem B2992511 : Blo 1993435 2992511 := bstep (se 1 (by rfl) ⟨2244383, by rfl⟩ : syracuseStep 2992511 = 4488767) B4488767
theorem B1995007 : Blo 1993435 1995007 := bstep (se 1 (by rfl) ⟨1496255, by rfl⟩ : syracuseStep 1995007 = 2992511) B2992511
theorem B2992517 : Blo 1993435 2992517 := bbase (se 4 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 2992517 = 561097) (by norm_num)
theorem B1995011 : Blo 1993435 1995011 := bstep (se 1 (by rfl) ⟨1496258, by rfl⟩ : syracuseStep 1995011 = 2992517) B2992517
theorem B3366589 : Blo 1993435 3366589 := bbase (se 3 (by rfl) ⟨631235, by rfl⟩ : syracuseStep 3366589 = 1262471) (by norm_num)
theorem B4488785 : Blo 1993435 4488785 := bstep (se 2 (by rfl) ⟨1683294, by rfl⟩ : syracuseStep 4488785 = 3366589) B3366589
theorem B2992523 : Blo 1993435 2992523 := bstep (se 1 (by rfl) ⟨2244392, by rfl⟩ : syracuseStep 2992523 = 4488785) B4488785
theorem B1995015 : Blo 1993435 1995015 := bstep (se 1 (by rfl) ⟨1496261, by rfl⟩ : syracuseStep 1995015 = 2992523) B2992523
theorem B2244397 : Blo 1993435 2244397 := bbase (se 3 (by rfl) ⟨420824, by rfl⟩ : syracuseStep 2244397 = 841649) (by norm_num)
theorem B2992529 : Blo 1993435 2992529 := bstep (se 2 (by rfl) ⟨1122198, by rfl⟩ : syracuseStep 2992529 = 2244397) B2244397
theorem B1995019 : Blo 1993435 1995019 := bstep (se 1 (by rfl) ⟨1496264, by rfl⟩ : syracuseStep 1995019 = 2992529) B2992529
theorem B6733205 : Blo 1993435 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B4488803 : Blo 1993435 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B2992535 : Blo 1993435 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B1995023 : Blo 1993435 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B2992541 : Blo 1993435 2992541 := bbase (se 3 (by rfl) ⟨561101, by rfl⟩ : syracuseStep 2992541 = 1122203) (by norm_num)
theorem B1995027 : Blo 1993435 1995027 := bstep (se 1 (by rfl) ⟨1496270, by rfl⟩ : syracuseStep 1995027 = 2992541) B2992541
theorem B4488821 : Blo 1993435 4488821 := bbase (se 5 (by rfl) ⟨210413, by rfl⟩ : syracuseStep 4488821 = 420827) (by norm_num)
theorem B2992547 : Blo 1993435 2992547 := bstep (se 1 (by rfl) ⟨2244410, by rfl⟩ : syracuseStep 2992547 = 4488821) B4488821
theorem B1995031 : Blo 1993435 1995031 := bstep (se 1 (by rfl) ⟨1496273, by rfl⟩ : syracuseStep 1995031 = 2992547) B2992547
theorem B2696341 : Blo 1993435 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B3595121 : Blo 1993435 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B2396747 : Blo 1993435 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B6391325 : Blo 1993435 6391325 := bstep (se 3 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 6391325 = 2396747) B2396747
theorem B17043533 : Blo 1993435 17043533 := bstep (se 3 (by rfl) ⟨3195662, by rfl⟩ : syracuseStep 17043533 = 6391325) B6391325
theorem B11362355 : Blo 1993435 11362355 := bstep (se 1 (by rfl) ⟨8521766, by rfl⟩ : syracuseStep 11362355 = 17043533) B17043533
theorem B7574903 : Blo 1993435 7574903 := bstep (se 1 (by rfl) ⟨5681177, by rfl⟩ : syracuseStep 7574903 = 11362355) B11362355
theorem B5049935 : Blo 1993435 5049935 := bstep (se 1 (by rfl) ⟨3787451, by rfl⟩ : syracuseStep 5049935 = 7574903) B7574903
theorem B3366623 : Blo 1993435 3366623 := bstep (se 1 (by rfl) ⟨2524967, by rfl⟩ : syracuseStep 3366623 = 5049935) B5049935
theorem B2244415 : Blo 1993435 2244415 := bstep (se 1 (by rfl) ⟨1683311, by rfl⟩ : syracuseStep 2244415 = 3366623) B3366623
theorem B2992553 : Blo 1993435 2992553 := bstep (se 2 (by rfl) ⟨1122207, by rfl⟩ : syracuseStep 2992553 = 2244415) B2244415
theorem B1995035 : Blo 1993435 1995035 := bstep (se 1 (by rfl) ⟨1496276, by rfl⟩ : syracuseStep 1995035 = 2992553) B2992553
theorem B7574917 : Blo 1993435 7574917 := bbase (se 4 (by rfl) ⟨710148, by rfl⟩ : syracuseStep 7574917 = 1420297) (by norm_num)
theorem B10099889 : Blo 1993435 10099889 := bstep (se 2 (by rfl) ⟨3787458, by rfl⟩ : syracuseStep 10099889 = 7574917) B7574917
theorem B6733259 : Blo 1993435 6733259 := bstep (se 1 (by rfl) ⟨5049944, by rfl⟩ : syracuseStep 6733259 = 10099889) B10099889
theorem B4488839 : Blo 1993435 4488839 := bstep (se 1 (by rfl) ⟨3366629, by rfl⟩ : syracuseStep 4488839 = 6733259) B6733259
theorem B2992559 : Blo 1993435 2992559 := bstep (se 1 (by rfl) ⟨2244419, by rfl⟩ : syracuseStep 2992559 = 4488839) B4488839
theorem B1995039 : Blo 1993435 1995039 := bstep (se 1 (by rfl) ⟨1496279, by rfl⟩ : syracuseStep 1995039 = 2992559) B2992559
theorem B2992565 : Blo 1993435 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B1995043 : Blo 1993435 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B5049965 : Blo 1993435 5049965 := bbase (se 3 (by rfl) ⟨946868, by rfl⟩ : syracuseStep 5049965 = 1893737) (by norm_num)
theorem B3366643 : Blo 1993435 3366643 := bstep (se 1 (by rfl) ⟨2524982, by rfl⟩ : syracuseStep 3366643 = 5049965) B5049965
theorem B4488857 : Blo 1993435 4488857 := bstep (se 2 (by rfl) ⟨1683321, by rfl⟩ : syracuseStep 4488857 = 3366643) B3366643
theorem B2992571 : Blo 1993435 2992571 := bstep (se 1 (by rfl) ⟨2244428, by rfl⟩ : syracuseStep 2992571 = 4488857) B4488857
theorem B1995047 : Blo 1993435 1995047 := bstep (se 1 (by rfl) ⟨1496285, by rfl⟩ : syracuseStep 1995047 = 2992571) B2992571
theorem B2244433 : Blo 1993435 2244433 := bbase (se 2 (by rfl) ⟨841662, by rfl⟩ : syracuseStep 2244433 = 1683325) (by norm_num)
theorem B2992577 : Blo 1993435 2992577 := bstep (se 2 (by rfl) ⟨1122216, by rfl⟩ : syracuseStep 2992577 = 2244433) B2244433
theorem B1995051 : Blo 1993435 1995051 := bstep (se 1 (by rfl) ⟨1496288, by rfl⟩ : syracuseStep 1995051 = 2992577) B2992577
theorem B2275061 : Blo 1993435 2275061 := bbase (se 5 (by rfl) ⟨106643, by rfl⟩ : syracuseStep 2275061 = 213287) (by norm_num)
theorem B6066829 : Blo 1993435 6066829 := bstep (se 3 (by rfl) ⟨1137530, by rfl⟩ : syracuseStep 6066829 = 2275061) B2275061
theorem B8089105 : Blo 1993435 8089105 := bstep (se 2 (by rfl) ⟨3033414, by rfl⟩ : syracuseStep 8089105 = 6066829) B6066829
theorem B10785473 : Blo 1993435 10785473 := bstep (se 2 (by rfl) ⟨4044552, by rfl⟩ : syracuseStep 10785473 = 8089105) B8089105
theorem B7190315 : Blo 1993435 7190315 := bstep (se 1 (by rfl) ⟨5392736, by rfl⟩ : syracuseStep 7190315 = 10785473) B10785473
theorem B4793543 : Blo 1993435 4793543 := bstep (se 1 (by rfl) ⟨3595157, by rfl⟩ : syracuseStep 4793543 = 7190315) B7190315
theorem B3195695 : Blo 1993435 3195695 := bstep (se 1 (by rfl) ⟨2396771, by rfl⟩ : syracuseStep 3195695 = 4793543) B4793543
theorem B2130463 : Blo 1993435 2130463 := bstep (se 1 (by rfl) ⟨1597847, by rfl⟩ : syracuseStep 2130463 = 3195695) B3195695
theorem B2840617 : Blo 1993435 2840617 := bstep (se 2 (by rfl) ⟨1065231, by rfl⟩ : syracuseStep 2840617 = 2130463) B2130463
theorem B3787489 : Blo 1993435 3787489 := bstep (se 2 (by rfl) ⟨1420308, by rfl⟩ : syracuseStep 3787489 = 2840617) B2840617
theorem B5049985 : Blo 1993435 5049985 := bstep (se 2 (by rfl) ⟨1893744, by rfl⟩ : syracuseStep 5049985 = 3787489) B3787489
theorem B6733313 : Blo 1993435 6733313 := bstep (se 2 (by rfl) ⟨2524992, by rfl⟩ : syracuseStep 6733313 = 5049985) B5049985
theorem B4488875 : Blo 1993435 4488875 := bstep (se 1 (by rfl) ⟨3366656, by rfl⟩ : syracuseStep 4488875 = 6733313) B6733313
theorem B2992583 : Blo 1993435 2992583 := bstep (se 1 (by rfl) ⟨2244437, by rfl⟩ : syracuseStep 2992583 = 4488875) B4488875
theorem B1995055 : Blo 1993435 1995055 := bstep (se 1 (by rfl) ⟨1496291, by rfl⟩ : syracuseStep 1995055 = 2992583) B2992583
theorem B2992589 : Blo 1993435 2992589 := bbase (se 3 (by rfl) ⟨561110, by rfl⟩ : syracuseStep 2992589 = 1122221) (by norm_num)
theorem B1995059 : Blo 1993435 1995059 := bstep (se 1 (by rfl) ⟨1496294, by rfl⟩ : syracuseStep 1995059 = 2992589) B2992589
theorem B4488893 : Blo 1993435 4488893 := bbase (se 3 (by rfl) ⟨841667, by rfl⟩ : syracuseStep 4488893 = 1683335) (by norm_num)
theorem B2992595 : Blo 1993435 2992595 := bstep (se 1 (by rfl) ⟨2244446, by rfl⟩ : syracuseStep 2992595 = 4488893) B4488893
theorem B1995063 : Blo 1993435 1995063 := bstep (se 1 (by rfl) ⟨1496297, by rfl⟩ : syracuseStep 1995063 = 2992595) B2992595
theorem B3366677 : Blo 1993435 3366677 := bbase (se 6 (by rfl) ⟨78906, by rfl⟩ : syracuseStep 3366677 = 157813) (by norm_num)
theorem B2244451 : Blo 1993435 2244451 := bstep (se 1 (by rfl) ⟨1683338, by rfl⟩ : syracuseStep 2244451 = 3366677) B3366677
theorem B2992601 : Blo 1993435 2992601 := bstep (se 2 (by rfl) ⟨1122225, by rfl⟩ : syracuseStep 2992601 = 2244451) B2244451
theorem B1995067 : Blo 1993435 1995067 := bstep (se 1 (by rfl) ⟨1496300, by rfl⟩ : syracuseStep 1995067 = 2992601) B2992601
theorem B48534997 : Blo 1993435 48534997 := bbase (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) (by norm_num)
theorem B64713329 : Blo 1993435 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B43142219 : Blo 1993435 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B28761479 : Blo 1993435 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B19174319 : Blo 1993435 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B12782879 : Blo 1993435 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B8521919 : Blo 1993435 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B5681279 : Blo 1993435 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B15150077 : Blo 1993435 15150077 := bstep (se 3 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 15150077 = 5681279) B5681279
theorem B10100051 : Blo 1993435 10100051 := bstep (se 1 (by rfl) ⟨7575038, by rfl⟩ : syracuseStep 10100051 = 15150077) B15150077
theorem B6733367 : Blo 1993435 6733367 := bstep (se 1 (by rfl) ⟨5050025, by rfl⟩ : syracuseStep 6733367 = 10100051) B10100051
theorem B4488911 : Blo 1993435 4488911 := bstep (se 1 (by rfl) ⟨3366683, by rfl⟩ : syracuseStep 4488911 = 6733367) B6733367
theorem B2992607 : Blo 1993435 2992607 := bstep (se 1 (by rfl) ⟨2244455, by rfl⟩ : syracuseStep 2992607 = 4488911) B4488911
theorem B1995071 : Blo 1993435 1995071 := bstep (se 1 (by rfl) ⟨1496303, by rfl⟩ : syracuseStep 1995071 = 2992607) B2992607
theorem B2992613 : Blo 1993435 2992613 := bbase (se 4 (by rfl) ⟨280557, by rfl⟩ : syracuseStep 2992613 = 561115) (by norm_num)
theorem B1995075 : Blo 1993435 1995075 := bstep (se 1 (by rfl) ⟨1496306, by rfl⟩ : syracuseStep 1995075 = 2992613) B2992613
theorem B12782933 : Blo 1993435 12782933 := bbase (se 11 (by rfl) ⟨9362, by rfl⟩ : syracuseStep 12782933 = 18725) (by norm_num)
theorem B8521955 : Blo 1993435 8521955 := bstep (se 1 (by rfl) ⟨6391466, by rfl⟩ : syracuseStep 8521955 = 12782933) B12782933
theorem B5681303 : Blo 1993435 5681303 := bstep (se 1 (by rfl) ⟨4260977, by rfl⟩ : syracuseStep 5681303 = 8521955) B8521955
theorem B3787535 : Blo 1993435 3787535 := bstep (se 1 (by rfl) ⟨2840651, by rfl⟩ : syracuseStep 3787535 = 5681303) B5681303
theorem B2525023 : Blo 1993435 2525023 := bstep (se 1 (by rfl) ⟨1893767, by rfl⟩ : syracuseStep 2525023 = 3787535) B3787535
theorem B3366697 : Blo 1993435 3366697 := bstep (se 2 (by rfl) ⟨1262511, by rfl⟩ : syracuseStep 3366697 = 2525023) B2525023
theorem B4488929 : Blo 1993435 4488929 := bstep (se 2 (by rfl) ⟨1683348, by rfl⟩ : syracuseStep 4488929 = 3366697) B3366697
theorem B2992619 : Blo 1993435 2992619 := bstep (se 1 (by rfl) ⟨2244464, by rfl⟩ : syracuseStep 2992619 = 4488929) B4488929
theorem B1995079 : Blo 1993435 1995079 := bstep (se 1 (by rfl) ⟨1496309, by rfl⟩ : syracuseStep 1995079 = 2992619) B2992619
theorem B2244469 : Blo 1993435 2244469 := bbase (se 5 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 2244469 = 210419) (by norm_num)
theorem B2992625 : Blo 1993435 2992625 := bstep (se 2 (by rfl) ⟨1122234, by rfl⟩ : syracuseStep 2992625 = 2244469) B2244469
theorem B1995083 : Blo 1993435 1995083 := bstep (se 1 (by rfl) ⟨1496312, by rfl⟩ : syracuseStep 1995083 = 2992625) B2992625
theorem B2525033 : Blo 1993435 2525033 := bbase (se 2 (by rfl) ⟨946887, by rfl⟩ : syracuseStep 2525033 = 1893775) (by norm_num)
theorem B6733421 : Blo 1993435 6733421 := bstep (se 3 (by rfl) ⟨1262516, by rfl⟩ : syracuseStep 6733421 = 2525033) B2525033
theorem B4488947 : Blo 1993435 4488947 := bstep (se 1 (by rfl) ⟨3366710, by rfl⟩ : syracuseStep 4488947 = 6733421) B6733421
theorem B2992631 : Blo 1993435 2992631 := bstep (se 1 (by rfl) ⟨2244473, by rfl⟩ : syracuseStep 2992631 = 4488947) B4488947
theorem B1995087 : Blo 1993435 1995087 := bstep (se 1 (by rfl) ⟨1496315, by rfl⟩ : syracuseStep 1995087 = 2992631) B2992631
theorem B2992637 : Blo 1993435 2992637 := bbase (se 3 (by rfl) ⟨561119, by rfl⟩ : syracuseStep 2992637 = 1122239) (by norm_num)
theorem B1995091 : Blo 1993435 1995091 := bstep (se 1 (by rfl) ⟨1496318, by rfl⟩ : syracuseStep 1995091 = 2992637) B2992637
theorem B4488965 : Blo 1993435 4488965 := bbase (se 4 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 4488965 = 841681) (by norm_num)
theorem B2992643 : Blo 1993435 2992643 := bstep (se 1 (by rfl) ⟨2244482, by rfl⟩ : syracuseStep 2992643 = 4488965) B4488965
theorem B1995095 : Blo 1993435 1995095 := bstep (se 1 (by rfl) ⟨1496321, by rfl⟩ : syracuseStep 1995095 = 2992643) B2992643
theorem B3787573 : Blo 1993435 3787573 := bbase (se 5 (by rfl) ⟨177542, by rfl⟩ : syracuseStep 3787573 = 355085) (by norm_num)
theorem B5050097 : Blo 1993435 5050097 := bstep (se 2 (by rfl) ⟨1893786, by rfl⟩ : syracuseStep 5050097 = 3787573) B3787573
theorem B3366731 : Blo 1993435 3366731 := bstep (se 1 (by rfl) ⟨2525048, by rfl⟩ : syracuseStep 3366731 = 5050097) B5050097
theorem B2244487 : Blo 1993435 2244487 := bstep (se 1 (by rfl) ⟨1683365, by rfl⟩ : syracuseStep 2244487 = 3366731) B3366731
theorem B2992649 : Blo 1993435 2992649 := bstep (se 2 (by rfl) ⟨1122243, by rfl⟩ : syracuseStep 2992649 = 2244487) B2244487
theorem B1995099 : Blo 1993435 1995099 := bstep (se 1 (by rfl) ⟨1496324, by rfl⟩ : syracuseStep 1995099 = 2992649) B2992649
theorem B10100213 : Blo 1993435 10100213 := bbase (se 5 (by rfl) ⟨473447, by rfl⟩ : syracuseStep 10100213 = 946895) (by norm_num)
theorem B6733475 : Blo 1993435 6733475 := bstep (se 1 (by rfl) ⟨5050106, by rfl⟩ : syracuseStep 6733475 = 10100213) B10100213
theorem B4488983 : Blo 1993435 4488983 := bstep (se 1 (by rfl) ⟨3366737, by rfl⟩ : syracuseStep 4488983 = 6733475) B6733475
theorem B2992655 : Blo 1993435 2992655 := bstep (se 1 (by rfl) ⟨2244491, by rfl⟩ : syracuseStep 2992655 = 4488983) B4488983
theorem B1995103 : Blo 1993435 1995103 := bstep (se 1 (by rfl) ⟨1496327, by rfl⟩ : syracuseStep 1995103 = 2992655) B2992655
theorem B2992661 : Blo 1993435 2992661 := bbase (se 6 (by rfl) ⟨70140, by rfl⟩ : syracuseStep 2992661 = 140281) (by norm_num)
theorem B1995107 : Blo 1993435 1995107 := bstep (se 1 (by rfl) ⟨1496330, by rfl⟩ : syracuseStep 1995107 = 2992661) B2992661
theorem B17044181 : Blo 1993435 17044181 := bbase (se 7 (by rfl) ⟨199736, by rfl⟩ : syracuseStep 17044181 = 399473) (by norm_num)
theorem B11362787 : Blo 1993435 11362787 := bstep (se 1 (by rfl) ⟨8522090, by rfl⟩ : syracuseStep 11362787 = 17044181) B17044181
theorem B7575191 : Blo 1993435 7575191 := bstep (se 1 (by rfl) ⟨5681393, by rfl⟩ : syracuseStep 7575191 = 11362787) B11362787
theorem B5050127 : Blo 1993435 5050127 := bstep (se 1 (by rfl) ⟨3787595, by rfl⟩ : syracuseStep 5050127 = 7575191) B7575191
theorem B3366751 : Blo 1993435 3366751 := bstep (se 1 (by rfl) ⟨2525063, by rfl⟩ : syracuseStep 3366751 = 5050127) B5050127
theorem B4489001 : Blo 1993435 4489001 := bstep (se 2 (by rfl) ⟨1683375, by rfl⟩ : syracuseStep 4489001 = 3366751) B3366751
theorem B2992667 : Blo 1993435 2992667 := bstep (se 1 (by rfl) ⟨2244500, by rfl⟩ : syracuseStep 2992667 = 4489001) B4489001
theorem B1995111 : Blo 1993435 1995111 := bstep (se 1 (by rfl) ⟨1496333, by rfl⟩ : syracuseStep 1995111 = 2992667) B2992667
theorem B2244505 : Blo 1993435 2244505 := bbase (se 2 (by rfl) ⟨841689, by rfl⟩ : syracuseStep 2244505 = 1683379) (by norm_num)
theorem B2992673 : Blo 1993435 2992673 := bstep (se 2 (by rfl) ⟨1122252, by rfl⟩ : syracuseStep 2992673 = 2244505) B2244505
theorem B1995115 : Blo 1993435 1995115 := bstep (se 1 (by rfl) ⟨1496336, by rfl⟩ : syracuseStep 1995115 = 2992673) B2992673
theorem B7575221 : Blo 1993435 7575221 := bbase (se 5 (by rfl) ⟨355088, by rfl⟩ : syracuseStep 7575221 = 710177) (by norm_num)
theorem B5050147 : Blo 1993435 5050147 := bstep (se 1 (by rfl) ⟨3787610, by rfl⟩ : syracuseStep 5050147 = 7575221) B7575221
theorem B6733529 : Blo 1993435 6733529 := bstep (se 2 (by rfl) ⟨2525073, by rfl⟩ : syracuseStep 6733529 = 5050147) B5050147
theorem B4489019 : Blo 1993435 4489019 := bstep (se 1 (by rfl) ⟨3366764, by rfl⟩ : syracuseStep 4489019 = 6733529) B6733529
theorem B2992679 : Blo 1993435 2992679 := bstep (se 1 (by rfl) ⟨2244509, by rfl⟩ : syracuseStep 2992679 = 4489019) B4489019
theorem B1995119 : Blo 1993435 1995119 := bstep (se 1 (by rfl) ⟨1496339, by rfl⟩ : syracuseStep 1995119 = 2992679) B2992679
theorem B2992685 : Blo 1993435 2992685 := bbase (se 3 (by rfl) ⟨561128, by rfl⟩ : syracuseStep 2992685 = 1122257) (by norm_num)
theorem B1995123 : Blo 1993435 1995123 := bstep (se 1 (by rfl) ⟨1496342, by rfl⟩ : syracuseStep 1995123 = 2992685) B2992685
theorem B4489037 : Blo 1993435 4489037 := bbase (se 3 (by rfl) ⟨841694, by rfl⟩ : syracuseStep 4489037 = 1683389) (by norm_num)
theorem B2992691 : Blo 1993435 2992691 := bstep (se 1 (by rfl) ⟨2244518, by rfl⟩ : syracuseStep 2992691 = 4489037) B4489037
theorem B1995127 : Blo 1993435 1995127 := bstep (se 1 (by rfl) ⟨1496345, by rfl⟩ : syracuseStep 1995127 = 2992691) B2992691
theorem B2525089 : Blo 1993435 2525089 := bbase (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) (by norm_num)
theorem B3366785 : Blo 1993435 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B2244523 : Blo 1993435 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B2992697 : Blo 1993435 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B1995131 : Blo 1993435 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B22725845 : Blo 1993435 22725845 := bbase (se 7 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 22725845 = 532637) (by norm_num)
theorem B15150563 : Blo 1993435 15150563 := bstep (se 1 (by rfl) ⟨11362922, by rfl⟩ : syracuseStep 15150563 = 22725845) B22725845
theorem B10100375 : Blo 1993435 10100375 := bstep (se 1 (by rfl) ⟨7575281, by rfl⟩ : syracuseStep 10100375 = 15150563) B15150563
theorem B6733583 : Blo 1993435 6733583 := bstep (se 1 (by rfl) ⟨5050187, by rfl⟩ : syracuseStep 6733583 = 10100375) B10100375
theorem B4489055 : Blo 1993435 4489055 := bstep (se 1 (by rfl) ⟨3366791, by rfl⟩ : syracuseStep 4489055 = 6733583) B6733583
theorem B2992703 : Blo 1993435 2992703 := bstep (se 1 (by rfl) ⟨2244527, by rfl⟩ : syracuseStep 2992703 = 4489055) B4489055
theorem B1995135 : Blo 1993435 1995135 := bstep (se 1 (by rfl) ⟨1496351, by rfl⟩ : syracuseStep 1995135 = 2992703) B2992703
theorem B2992709 : Blo 1993435 2992709 := bbase (se 4 (by rfl) ⟨280566, by rfl⟩ : syracuseStep 2992709 = 561133) (by norm_num)
theorem B1995139 : Blo 1993435 1995139 := bstep (se 1 (by rfl) ⟨1496354, by rfl⟩ : syracuseStep 1995139 = 2992709) B2992709
theorem B3366805 : Blo 1993435 3366805 := bbase (se 6 (by rfl) ⟨78909, by rfl⟩ : syracuseStep 3366805 = 157819) (by norm_num)
theorem B4489073 : Blo 1993435 4489073 := bstep (se 2 (by rfl) ⟨1683402, by rfl⟩ : syracuseStep 4489073 = 3366805) B3366805
theorem B2992715 : Blo 1993435 2992715 := bstep (se 1 (by rfl) ⟨2244536, by rfl⟩ : syracuseStep 2992715 = 4489073) B4489073
theorem B1995143 : Blo 1993435 1995143 := bstep (se 1 (by rfl) ⟨1496357, by rfl⟩ : syracuseStep 1995143 = 2992715) B2992715
theorem B2244541 : Blo 1993435 2244541 := bbase (se 3 (by rfl) ⟨420851, by rfl⟩ : syracuseStep 2244541 = 841703) (by norm_num)
theorem B2992721 : Blo 1993435 2992721 := bstep (se 2 (by rfl) ⟨1122270, by rfl⟩ : syracuseStep 2992721 = 2244541) B2244541
theorem B1995147 : Blo 1993435 1995147 := bstep (se 1 (by rfl) ⟨1496360, by rfl⟩ : syracuseStep 1995147 = 2992721) B2992721
theorem B6733637 : Blo 1993435 6733637 := bbase (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) (by norm_num)
theorem B4489091 : Blo 1993435 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B2992727 : Blo 1993435 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B1995151 : Blo 1993435 1995151 := bstep (se 1 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 1995151 = 2992727) B2992727
theorem B2992733 : Blo 1993435 2992733 := bbase (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) (by norm_num)
theorem B1995155 : Blo 1993435 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B4489109 : Blo 1993435 4489109 := bbase (se 6 (by rfl) ⟨105213, by rfl⟩ : syracuseStep 4489109 = 210427) (by norm_num)
theorem B2992739 : Blo 1993435 2992739 := bstep (se 1 (by rfl) ⟨2244554, by rfl⟩ : syracuseStep 2992739 = 4489109) B4489109
theorem B1995159 : Blo 1993435 1995159 := bstep (se 1 (by rfl) ⟨1496369, by rfl⟩ : syracuseStep 1995159 = 2992739) B2992739
theorem B4261157 : Blo 1993435 4261157 := bbase (se 4 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 4261157 = 798967) (by norm_num)
theorem B2840771 : Blo 1993435 2840771 := bstep (se 1 (by rfl) ⟨2130578, by rfl⟩ : syracuseStep 2840771 = 4261157) B4261157
theorem B7575389 : Blo 1993435 7575389 := bstep (se 3 (by rfl) ⟨1420385, by rfl⟩ : syracuseStep 7575389 = 2840771) B2840771
theorem B5050259 : Blo 1993435 5050259 := bstep (se 1 (by rfl) ⟨3787694, by rfl⟩ : syracuseStep 5050259 = 7575389) B7575389
theorem B3366839 : Blo 1993435 3366839 := bstep (se 1 (by rfl) ⟨2525129, by rfl⟩ : syracuseStep 3366839 = 5050259) B5050259
theorem B2244559 : Blo 1993435 2244559 := bstep (se 1 (by rfl) ⟨1683419, by rfl⟩ : syracuseStep 2244559 = 3366839) B3366839
theorem B2992745 : Blo 1993435 2992745 := bstep (se 2 (by rfl) ⟨1122279, by rfl⟩ : syracuseStep 2992745 = 2244559) B2244559
theorem B1995163 : Blo 1993435 1995163 := bstep (se 1 (by rfl) ⟨1496372, by rfl⟩ : syracuseStep 1995163 = 2992745) B2992745
theorem B9587621 : Blo 1993435 9587621 := bbase (se 4 (by rfl) ⟨898839, by rfl⟩ : syracuseStep 9587621 = 1797679) (by norm_num)
theorem B6391747 : Blo 1993435 6391747 := bstep (se 1 (by rfl) ⟨4793810, by rfl⟩ : syracuseStep 6391747 = 9587621) B9587621
theorem B8522329 : Blo 1993435 8522329 := bstep (se 2 (by rfl) ⟨3195873, by rfl⟩ : syracuseStep 8522329 = 6391747) B6391747
theorem B11363105 : Blo 1993435 11363105 := bstep (se 2 (by rfl) ⟨4261164, by rfl⟩ : syracuseStep 11363105 = 8522329) B8522329
theorem B7575403 : Blo 1993435 7575403 := bstep (se 1 (by rfl) ⟨5681552, by rfl⟩ : syracuseStep 7575403 = 11363105) B11363105
theorem B10100537 : Blo 1993435 10100537 := bstep (se 2 (by rfl) ⟨3787701, by rfl⟩ : syracuseStep 10100537 = 7575403) B7575403
theorem B6733691 : Blo 1993435 6733691 := bstep (se 1 (by rfl) ⟨5050268, by rfl⟩ : syracuseStep 6733691 = 10100537) B10100537
theorem B4489127 : Blo 1993435 4489127 := bstep (se 1 (by rfl) ⟨3366845, by rfl⟩ : syracuseStep 4489127 = 6733691) B6733691
theorem B2992751 : Blo 1993435 2992751 := bstep (se 1 (by rfl) ⟨2244563, by rfl⟩ : syracuseStep 2992751 = 4489127) B4489127
theorem B1995167 : Blo 1993435 1995167 := bstep (se 1 (by rfl) ⟨1496375, by rfl⟩ : syracuseStep 1995167 = 2992751) B2992751
theorem B2992757 : Blo 1993435 2992757 := bbase (se 5 (by rfl) ⟨140285, by rfl⟩ : syracuseStep 2992757 = 280571) (by norm_num)
theorem B1995171 : Blo 1993435 1995171 := bstep (se 1 (by rfl) ⟨1496378, by rfl⟩ : syracuseStep 1995171 = 2992757) B2992757
theorem B3787717 : Blo 1993435 3787717 := bbase (se 4 (by rfl) ⟨355098, by rfl⟩ : syracuseStep 3787717 = 710197) (by norm_num)
theorem B5050289 : Blo 1993435 5050289 := bstep (se 2 (by rfl) ⟨1893858, by rfl⟩ : syracuseStep 5050289 = 3787717) B3787717
theorem B3366859 : Blo 1993435 3366859 := bstep (se 1 (by rfl) ⟨2525144, by rfl⟩ : syracuseStep 3366859 = 5050289) B5050289
theorem B4489145 : Blo 1993435 4489145 := bstep (se 2 (by rfl) ⟨1683429, by rfl⟩ : syracuseStep 4489145 = 3366859) B3366859
theorem B2992763 : Blo 1993435 2992763 := bstep (se 1 (by rfl) ⟨2244572, by rfl⟩ : syracuseStep 2992763 = 4489145) B4489145
theorem B1995175 : Blo 1993435 1995175 := bstep (se 1 (by rfl) ⟨1496381, by rfl⟩ : syracuseStep 1995175 = 2992763) B2992763
theorem B2244577 : Blo 1993435 2244577 := bbase (se 2 (by rfl) ⟨841716, by rfl⟩ : syracuseStep 2244577 = 1683433) (by norm_num)
theorem B2992769 : Blo 1993435 2992769 := bstep (se 2 (by rfl) ⟨1122288, by rfl⟩ : syracuseStep 2992769 = 2244577) B2244577
theorem B1995179 : Blo 1993435 1995179 := bstep (se 1 (by rfl) ⟨1496384, by rfl⟩ : syracuseStep 1995179 = 2992769) B2992769
theorem B5050309 : Blo 1993435 5050309 := bbase (se 4 (by rfl) ⟨473466, by rfl⟩ : syracuseStep 5050309 = 946933) (by norm_num)
theorem B6733745 : Blo 1993435 6733745 := bstep (se 2 (by rfl) ⟨2525154, by rfl⟩ : syracuseStep 6733745 = 5050309) B5050309
theorem B4489163 : Blo 1993435 4489163 := bstep (se 1 (by rfl) ⟨3366872, by rfl⟩ : syracuseStep 4489163 = 6733745) B6733745
theorem B2992775 : Blo 1993435 2992775 := bstep (se 1 (by rfl) ⟨2244581, by rfl⟩ : syracuseStep 2992775 = 4489163) B4489163
theorem B1995183 : Blo 1993435 1995183 := bstep (se 1 (by rfl) ⟨1496387, by rfl⟩ : syracuseStep 1995183 = 2992775) B2992775
theorem B2992781 : Blo 1993435 2992781 := bbase (se 3 (by rfl) ⟨561146, by rfl⟩ : syracuseStep 2992781 = 1122293) (by norm_num)
theorem B1995187 : Blo 1993435 1995187 := bstep (se 1 (by rfl) ⟨1496390, by rfl⟩ : syracuseStep 1995187 = 2992781) B2992781
theorem B4489181 : Blo 1993435 4489181 := bbase (se 3 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 4489181 = 1683443) (by norm_num)
theorem B2992787 : Blo 1993435 2992787 := bstep (se 1 (by rfl) ⟨2244590, by rfl⟩ : syracuseStep 2992787 = 4489181) B4489181
theorem B1995191 : Blo 1993435 1995191 := bstep (se 1 (by rfl) ⟨1496393, by rfl⟩ : syracuseStep 1995191 = 2992787) B2992787
theorem B3366893 : Blo 1993435 3366893 := bbase (se 3 (by rfl) ⟨631292, by rfl⟩ : syracuseStep 3366893 = 1262585) (by norm_num)
theorem B2244595 : Blo 1993435 2244595 := bstep (se 1 (by rfl) ⟨1683446, by rfl⟩ : syracuseStep 2244595 = 3366893) B3366893
theorem B2992793 : Blo 1993435 2992793 := bstep (se 2 (by rfl) ⟨1122297, by rfl⟩ : syracuseStep 2992793 = 2244595) B2244595
theorem B1995195 : Blo 1993435 1995195 := bstep (se 1 (by rfl) ⟨1496396, by rfl⟩ : syracuseStep 1995195 = 2992793) B2992793
theorem B2879581 : Blo 1993435 2879581 := bbase (se 3 (by rfl) ⟨539921, by rfl⟩ : syracuseStep 2879581 = 1079843) (by norm_num)
theorem B3839441 : Blo 1993435 3839441 := bstep (se 2 (by rfl) ⟨1439790, by rfl⟩ : syracuseStep 3839441 = 2879581) B2879581
theorem B10238509 : Blo 1993435 10238509 := bstep (se 3 (by rfl) ⟨1919720, by rfl⟩ : syracuseStep 10238509 = 3839441) B3839441
theorem B13651345 : Blo 1993435 13651345 := bstep (se 2 (by rfl) ⟨5119254, by rfl⟩ : syracuseStep 13651345 = 10238509) B10238509
theorem B18201793 : Blo 1993435 18201793 := bstep (se 2 (by rfl) ⟨6825672, by rfl⟩ : syracuseStep 18201793 = 13651345) B13651345
theorem B24269057 : Blo 1993435 24269057 := bstep (se 2 (by rfl) ⟨9100896, by rfl⟩ : syracuseStep 24269057 = 18201793) B18201793
theorem B16179371 : Blo 1993435 16179371 := bstep (se 1 (by rfl) ⟨12134528, by rfl⟩ : syracuseStep 16179371 = 24269057) B24269057
theorem B10786247 : Blo 1993435 10786247 := bstep (se 1 (by rfl) ⟨8089685, by rfl⟩ : syracuseStep 10786247 = 16179371) B16179371
theorem B7190831 : Blo 1993435 7190831 := bstep (se 1 (by rfl) ⟨5393123, by rfl⟩ : syracuseStep 7190831 = 10786247) B10786247
theorem B4793887 : Blo 1993435 4793887 := bstep (se 1 (by rfl) ⟨3595415, by rfl⟩ : syracuseStep 4793887 = 7190831) B7190831
theorem B25567397 : Blo 1993435 25567397 := bstep (se 4 (by rfl) ⟨2396943, by rfl⟩ : syracuseStep 25567397 = 4793887) B4793887
theorem B17044931 : Blo 1993435 17044931 := bstep (se 1 (by rfl) ⟨12783698, by rfl⟩ : syracuseStep 17044931 = 25567397) B25567397
theorem B11363287 : Blo 1993435 11363287 := bstep (se 1 (by rfl) ⟨8522465, by rfl⟩ : syracuseStep 11363287 = 17044931) B17044931
theorem B15151049 : Blo 1993435 15151049 := bstep (se 2 (by rfl) ⟨5681643, by rfl⟩ : syracuseStep 15151049 = 11363287) B11363287
theorem B10100699 : Blo 1993435 10100699 := bstep (se 1 (by rfl) ⟨7575524, by rfl⟩ : syracuseStep 10100699 = 15151049) B15151049
theorem B6733799 : Blo 1993435 6733799 := bstep (se 1 (by rfl) ⟨5050349, by rfl⟩ : syracuseStep 6733799 = 10100699) B10100699
theorem B4489199 : Blo 1993435 4489199 := bstep (se 1 (by rfl) ⟨3366899, by rfl⟩ : syracuseStep 4489199 = 6733799) B6733799
theorem B2992799 : Blo 1993435 2992799 := bstep (se 1 (by rfl) ⟨2244599, by rfl⟩ : syracuseStep 2992799 = 4489199) B4489199
theorem B1995199 : Blo 1993435 1995199 := bstep (se 1 (by rfl) ⟨1496399, by rfl⟩ : syracuseStep 1995199 = 2992799) B2992799
theorem B2992805 : Blo 1993435 2992805 := bbase (se 4 (by rfl) ⟨280575, by rfl⟩ : syracuseStep 2992805 = 561151) (by norm_num)
theorem B1995203 : Blo 1993435 1995203 := bstep (se 1 (by rfl) ⟨1496402, by rfl⟩ : syracuseStep 1995203 = 2992805) B2992805
theorem B2525185 : Blo 1993435 2525185 := bbase (se 2 (by rfl) ⟨946944, by rfl⟩ : syracuseStep 2525185 = 1893889) (by norm_num)
theorem B3366913 : Blo 1993435 3366913 := bstep (se 2 (by rfl) ⟨1262592, by rfl⟩ : syracuseStep 3366913 = 2525185) B2525185
theorem B4489217 : Blo 1993435 4489217 := bstep (se 2 (by rfl) ⟨1683456, by rfl⟩ : syracuseStep 4489217 = 3366913) B3366913
theorem B2992811 : Blo 1993435 2992811 := bstep (se 1 (by rfl) ⟨2244608, by rfl⟩ : syracuseStep 2992811 = 4489217) B4489217
theorem B1995207 : Blo 1993435 1995207 := bstep (se 1 (by rfl) ⟨1496405, by rfl⟩ : syracuseStep 1995207 = 2992811) B2992811
theorem B2244613 : Blo 1993435 2244613 := bbase (se 4 (by rfl) ⟨210432, by rfl⟩ : syracuseStep 2244613 = 420865) (by norm_num)
theorem B2992817 : Blo 1993435 2992817 := bstep (se 2 (by rfl) ⟨1122306, by rfl⟩ : syracuseStep 2992817 = 2244613) B2244613
theorem B1995211 : Blo 1993435 1995211 := bstep (se 1 (by rfl) ⟨1496408, by rfl⟩ : syracuseStep 1995211 = 2992817) B2992817
theorem B2840845 : Blo 1993435 2840845 := bbase (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) (by norm_num)
theorem B3787793 : Blo 1993435 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B2525195 : Blo 1993435 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B6733853 : Blo 1993435 6733853 := bstep (se 3 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 6733853 = 2525195) B2525195
theorem B4489235 : Blo 1993435 4489235 := bstep (se 1 (by rfl) ⟨3366926, by rfl⟩ : syracuseStep 4489235 = 6733853) B6733853
theorem B2992823 : Blo 1993435 2992823 := bstep (se 1 (by rfl) ⟨2244617, by rfl⟩ : syracuseStep 2992823 = 4489235) B4489235
theorem B1995215 : Blo 1993435 1995215 := bstep (se 1 (by rfl) ⟨1496411, by rfl⟩ : syracuseStep 1995215 = 2992823) B2992823
theorem B2992829 : Blo 1993435 2992829 := bbase (se 3 (by rfl) ⟨561155, by rfl⟩ : syracuseStep 2992829 = 1122311) (by norm_num)
theorem B1995219 : Blo 1993435 1995219 := bstep (se 1 (by rfl) ⟨1496414, by rfl⟩ : syracuseStep 1995219 = 2992829) B2992829
theorem B4489253 : Blo 1993435 4489253 := bbase (se 4 (by rfl) ⟨420867, by rfl⟩ : syracuseStep 4489253 = 841735) (by norm_num)
theorem B2992835 : Blo 1993435 2992835 := bstep (se 1 (by rfl) ⟨2244626, by rfl⟩ : syracuseStep 2992835 = 4489253) B4489253
theorem B1995223 : Blo 1993435 1995223 := bstep (se 1 (by rfl) ⟨1496417, by rfl⟩ : syracuseStep 1995223 = 2992835) B2992835
theorem B5050421 : Blo 1993435 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B3366947 : Blo 1993435 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B2244631 : Blo 1993435 2244631 := bstep (se 1 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 2244631 = 3366947) B3366947
theorem B2992841 : Blo 1993435 2992841 := bstep (se 2 (by rfl) ⟨1122315, by rfl⟩ : syracuseStep 2992841 = 2244631) B2244631
theorem B1995227 : Blo 1993435 1995227 := bstep (se 1 (by rfl) ⟨1496420, by rfl⟩ : syracuseStep 1995227 = 2992841) B2992841
theorem B10786421 : Blo 1993435 10786421 := bbase (se 5 (by rfl) ⟨505613, by rfl⟩ : syracuseStep 10786421 = 1011227) (by norm_num)
theorem B7190947 : Blo 1993435 7190947 := bstep (se 1 (by rfl) ⟨5393210, by rfl⟩ : syracuseStep 7190947 = 10786421) B10786421
theorem B9587929 : Blo 1993435 9587929 := bstep (se 2 (by rfl) ⟨3595473, by rfl⟩ : syracuseStep 9587929 = 7190947) B7190947
theorem B12783905 : Blo 1993435 12783905 := bstep (se 2 (by rfl) ⟨4793964, by rfl⟩ : syracuseStep 12783905 = 9587929) B9587929
theorem B8522603 : Blo 1993435 8522603 := bstep (se 1 (by rfl) ⟨6391952, by rfl⟩ : syracuseStep 8522603 = 12783905) B12783905
theorem B5681735 : Blo 1993435 5681735 := bstep (se 1 (by rfl) ⟨4261301, by rfl⟩ : syracuseStep 5681735 = 8522603) B8522603
theorem B3787823 : Blo 1993435 3787823 := bstep (se 1 (by rfl) ⟨2840867, by rfl⟩ : syracuseStep 3787823 = 5681735) B5681735
theorem B10100861 : Blo 1993435 10100861 := bstep (se 3 (by rfl) ⟨1893911, by rfl⟩ : syracuseStep 10100861 = 3787823) B3787823
theorem B6733907 : Blo 1993435 6733907 := bstep (se 1 (by rfl) ⟨5050430, by rfl⟩ : syracuseStep 6733907 = 10100861) B10100861
theorem B4489271 : Blo 1993435 4489271 := bstep (se 1 (by rfl) ⟨3366953, by rfl⟩ : syracuseStep 4489271 = 6733907) B6733907
theorem B2992847 : Blo 1993435 2992847 := bstep (se 1 (by rfl) ⟨2244635, by rfl⟩ : syracuseStep 2992847 = 4489271) B4489271
theorem B1995231 : Blo 1993435 1995231 := bstep (se 1 (by rfl) ⟨1496423, by rfl⟩ : syracuseStep 1995231 = 2992847) B2992847
theorem B2992853 : Blo 1993435 2992853 := bbase (se 7 (by rfl) ⟨35072, by rfl⟩ : syracuseStep 2992853 = 70145) (by norm_num)
theorem B1995235 : Blo 1993435 1995235 := bstep (se 1 (by rfl) ⟨1496426, by rfl⟩ : syracuseStep 1995235 = 2992853) B2992853
theorem B4044925 : Blo 1993435 4044925 := bbase (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) (by norm_num)
theorem B5393233 : Blo 1993435 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B7190977 : Blo 1993435 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B9587969 : Blo 1993435 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B6391979 : Blo 1993435 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B4261319 : Blo 1993435 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B2840879 : Blo 1993435 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B7575677 : Blo 1993435 7575677 := bstep (se 3 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 7575677 = 2840879) B2840879
theorem B5050451 : Blo 1993435 5050451 := bstep (se 1 (by rfl) ⟨3787838, by rfl⟩ : syracuseStep 5050451 = 7575677) B7575677
theorem B3366967 : Blo 1993435 3366967 := bstep (se 1 (by rfl) ⟨2525225, by rfl⟩ : syracuseStep 3366967 = 5050451) B5050451
theorem B4489289 : Blo 1993435 4489289 := bstep (se 2 (by rfl) ⟨1683483, by rfl⟩ : syracuseStep 4489289 = 3366967) B3366967
theorem B2992859 : Blo 1993435 2992859 := bstep (se 1 (by rfl) ⟨2244644, by rfl⟩ : syracuseStep 2992859 = 4489289) B4489289
theorem B1995239 : Blo 1993435 1995239 := bstep (se 1 (by rfl) ⟨1496429, by rfl⟩ : syracuseStep 1995239 = 2992859) B2992859
theorem B2244649 : Blo 1993435 2244649 := bbase (se 2 (by rfl) ⟨841743, by rfl⟩ : syracuseStep 2244649 = 1683487) (by norm_num)
theorem B2992865 : Blo 1993435 2992865 := bstep (se 2 (by rfl) ⟨1122324, by rfl⟩ : syracuseStep 2992865 = 2244649) B2244649
theorem B1995243 : Blo 1993435 1995243 := bstep (se 1 (by rfl) ⟨1496432, by rfl⟩ : syracuseStep 1995243 = 2992865) B2992865
theorem B21573013 : Blo 1993435 21573013 := bbase (se 6 (by rfl) ⟨505617, by rfl⟩ : syracuseStep 21573013 = 1011235) (by norm_num)
theorem B28764017 : Blo 1993435 28764017 := bstep (se 2 (by rfl) ⟨10786506, by rfl⟩ : syracuseStep 28764017 = 21573013) B21573013
theorem B19176011 : Blo 1993435 19176011 := bstep (se 1 (by rfl) ⟨14382008, by rfl⟩ : syracuseStep 19176011 = 28764017) B28764017
theorem B12784007 : Blo 1993435 12784007 := bstep (se 1 (by rfl) ⟨9588005, by rfl⟩ : syracuseStep 12784007 = 19176011) B19176011
theorem B8522671 : Blo 1993435 8522671 := bstep (se 1 (by rfl) ⟨6392003, by rfl⟩ : syracuseStep 8522671 = 12784007) B12784007
theorem B11363561 : Blo 1993435 11363561 := bstep (se 2 (by rfl) ⟨4261335, by rfl⟩ : syracuseStep 11363561 = 8522671) B8522671
theorem B7575707 : Blo 1993435 7575707 := bstep (se 1 (by rfl) ⟨5681780, by rfl⟩ : syracuseStep 7575707 = 11363561) B11363561
theorem B5050471 : Blo 1993435 5050471 := bstep (se 1 (by rfl) ⟨3787853, by rfl⟩ : syracuseStep 5050471 = 7575707) B7575707
theorem B6733961 : Blo 1993435 6733961 := bstep (se 2 (by rfl) ⟨2525235, by rfl⟩ : syracuseStep 6733961 = 5050471) B5050471
theorem B4489307 : Blo 1993435 4489307 := bstep (se 1 (by rfl) ⟨3366980, by rfl⟩ : syracuseStep 4489307 = 6733961) B6733961
theorem B2992871 : Blo 1993435 2992871 := bstep (se 1 (by rfl) ⟨2244653, by rfl⟩ : syracuseStep 2992871 = 4489307) B4489307
theorem B1995247 : Blo 1993435 1995247 := bstep (se 1 (by rfl) ⟨1496435, by rfl⟩ : syracuseStep 1995247 = 2992871) B2992871
theorem B2992877 : Blo 1993435 2992877 := bbase (se 3 (by rfl) ⟨561164, by rfl⟩ : syracuseStep 2992877 = 1122329) (by norm_num)
theorem B1995251 : Blo 1993435 1995251 := bstep (se 1 (by rfl) ⟨1496438, by rfl⟩ : syracuseStep 1995251 = 2992877) B2992877
theorem B4489325 : Blo 1993435 4489325 := bbase (se 3 (by rfl) ⟨841748, by rfl⟩ : syracuseStep 4489325 = 1683497) (by norm_num)
theorem B2992883 : Blo 1993435 2992883 := bstep (se 1 (by rfl) ⟨2244662, by rfl⟩ : syracuseStep 2992883 = 4489325) B4489325
theorem B1995255 : Blo 1993435 1995255 := bstep (se 1 (by rfl) ⟨1496441, by rfl⟩ : syracuseStep 1995255 = 2992883) B2992883
theorem B3787877 : Blo 1993435 3787877 := bbase (se 4 (by rfl) ⟨355113, by rfl⟩ : syracuseStep 3787877 = 710227) (by norm_num)
theorem B2525251 : Blo 1993435 2525251 := bstep (se 1 (by rfl) ⟨1893938, by rfl⟩ : syracuseStep 2525251 = 3787877) B3787877
theorem B3367001 : Blo 1993435 3367001 := bstep (se 2 (by rfl) ⟨1262625, by rfl⟩ : syracuseStep 3367001 = 2525251) B2525251
theorem B2244667 : Blo 1993435 2244667 := bstep (se 1 (by rfl) ⟨1683500, by rfl⟩ : syracuseStep 2244667 = 3367001) B3367001
theorem B2992889 : Blo 1993435 2992889 := bstep (se 2 (by rfl) ⟨1122333, by rfl⟩ : syracuseStep 2992889 = 2244667) B2244667
theorem B1995259 : Blo 1993435 1995259 := bstep (se 1 (by rfl) ⟨1496444, by rfl⟩ : syracuseStep 1995259 = 2992889) B2992889
theorem B7191061 : Blo 1993435 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B38352325 : Blo 1993435 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B51136433 : Blo 1993435 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B34090955 : Blo 1993435 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B22727303 : Blo 1993435 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B15151535 : Blo 1993435 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B10101023 : Blo 1993435 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B6734015 : Blo 1993435 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B4489343 : Blo 1993435 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B2992895 : Blo 1993435 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B1995263 : Blo 1993435 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B2992901 : Blo 1993435 2992901 := bbase (se 4 (by rfl) ⟨280584, by rfl⟩ : syracuseStep 2992901 = 561169) (by norm_num)
theorem B1995267 : Blo 1993435 1995267 := bstep (se 1 (by rfl) ⟨1496450, by rfl⟩ : syracuseStep 1995267 = 2992901) B2992901
theorem B3367021 : Blo 1993435 3367021 := bbase (se 3 (by rfl) ⟨631316, by rfl⟩ : syracuseStep 3367021 = 1262633) (by norm_num)
theorem B4489361 : Blo 1993435 4489361 := bstep (se 2 (by rfl) ⟨1683510, by rfl⟩ : syracuseStep 4489361 = 3367021) B3367021
theorem B2992907 : Blo 1993435 2992907 := bstep (se 1 (by rfl) ⟨2244680, by rfl⟩ : syracuseStep 2992907 = 4489361) B4489361
theorem B1995271 : Blo 1993435 1995271 := bstep (se 1 (by rfl) ⟨1496453, by rfl⟩ : syracuseStep 1995271 = 2992907) B2992907
theorem B2244685 : Blo 1993435 2244685 := bbase (se 3 (by rfl) ⟨420878, by rfl⟩ : syracuseStep 2244685 = 841757) (by norm_num)
theorem B2992913 : Blo 1993435 2992913 := bstep (se 2 (by rfl) ⟨1122342, by rfl⟩ : syracuseStep 2992913 = 2244685) B2244685
theorem B1995275 : Blo 1993435 1995275 := bstep (se 1 (by rfl) ⟨1496456, by rfl⟩ : syracuseStep 1995275 = 2992913) B2992913
theorem B6734069 : Blo 1993435 6734069 := bbase (se 5 (by rfl) ⟨315659, by rfl⟩ : syracuseStep 6734069 = 631319) (by norm_num)
theorem B4489379 : Blo 1993435 4489379 := bstep (se 1 (by rfl) ⟨3367034, by rfl⟩ : syracuseStep 4489379 = 6734069) B6734069
theorem B2992919 : Blo 1993435 2992919 := bstep (se 1 (by rfl) ⟨2244689, by rfl⟩ : syracuseStep 2992919 = 4489379) B4489379
theorem B1995279 : Blo 1993435 1995279 := bstep (se 1 (by rfl) ⟨1496459, by rfl⟩ : syracuseStep 1995279 = 2992919) B2992919
theorem B2992925 : Blo 1993435 2992925 := bbase (se 3 (by rfl) ⟨561173, by rfl⟩ : syracuseStep 2992925 = 1122347) (by norm_num)
theorem B1995283 : Blo 1993435 1995283 := bstep (se 1 (by rfl) ⟨1496462, by rfl⟩ : syracuseStep 1995283 = 2992925) B2992925
theorem B4489397 : Blo 1993435 4489397 := bbase (se 5 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 4489397 = 420881) (by norm_num)
theorem B2992931 : Blo 1993435 2992931 := bstep (se 1 (by rfl) ⟨2244698, by rfl⟩ : syracuseStep 2992931 = 4489397) B4489397
theorem B1995287 : Blo 1993435 1995287 := bstep (se 1 (by rfl) ⟨1496465, by rfl⟩ : syracuseStep 1995287 = 2992931) B2992931
theorem B4319573 : Blo 1993435 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B11518861 : Blo 1993435 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B15358481 : Blo 1993435 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B10238987 : Blo 1993435 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B27303965 : Blo 1993435 27303965 := bstep (se 3 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 27303965 = 10238987) B10238987
theorem B18202643 : Blo 1993435 18202643 := bstep (se 1 (by rfl) ⟨13651982, by rfl⟩ : syracuseStep 18202643 = 27303965) B27303965
theorem B12135095 : Blo 1993435 12135095 := bstep (se 1 (by rfl) ⟨9101321, by rfl⟩ : syracuseStep 12135095 = 18202643) B18202643
theorem B8090063 : Blo 1993435 8090063 := bstep (se 1 (by rfl) ⟨6067547, by rfl⟩ : syracuseStep 8090063 = 12135095) B12135095
theorem B5393375 : Blo 1993435 5393375 := bstep (se 1 (by rfl) ⟨4045031, by rfl⟩ : syracuseStep 5393375 = 8090063) B8090063
theorem B3595583 : Blo 1993435 3595583 := bstep (se 1 (by rfl) ⟨2696687, by rfl⟩ : syracuseStep 3595583 = 5393375) B5393375
theorem B2397055 : Blo 1993435 2397055 := bstep (se 1 (by rfl) ⟨1797791, by rfl⟩ : syracuseStep 2397055 = 3595583) B3595583
theorem B3196073 : Blo 1993435 3196073 := bstep (se 2 (by rfl) ⟨1198527, by rfl⟩ : syracuseStep 3196073 = 2397055) B2397055
theorem B2130715 : Blo 1993435 2130715 := bstep (se 1 (by rfl) ⟨1598036, by rfl⟩ : syracuseStep 2130715 = 3196073) B3196073
theorem B11363813 : Blo 1993435 11363813 := bstep (se 4 (by rfl) ⟨1065357, by rfl⟩ : syracuseStep 11363813 = 2130715) B2130715
theorem B7575875 : Blo 1993435 7575875 := bstep (se 1 (by rfl) ⟨5681906, by rfl⟩ : syracuseStep 7575875 = 11363813) B11363813
theorem B5050583 : Blo 1993435 5050583 := bstep (se 1 (by rfl) ⟨3787937, by rfl⟩ : syracuseStep 5050583 = 7575875) B7575875
theorem B3367055 : Blo 1993435 3367055 := bstep (se 1 (by rfl) ⟨2525291, by rfl⟩ : syracuseStep 3367055 = 5050583) B5050583
theorem B2244703 : Blo 1993435 2244703 := bstep (se 1 (by rfl) ⟨1683527, by rfl⟩ : syracuseStep 2244703 = 3367055) B3367055
theorem B2992937 : Blo 1993435 2992937 := bstep (se 2 (by rfl) ⟨1122351, by rfl⟩ : syracuseStep 2992937 = 2244703) B2244703
theorem B1995291 : Blo 1993435 1995291 := bstep (se 1 (by rfl) ⟨1496468, by rfl⟩ : syracuseStep 1995291 = 2992937) B2992937
theorem B4550669 : Blo 1993435 4550669 := bbase (se 3 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 4550669 = 1706501) (by norm_num)
theorem B3033779 : Blo 1993435 3033779 := bstep (se 1 (by rfl) ⟨2275334, by rfl⟩ : syracuseStep 3033779 = 4550669) B4550669
theorem B8090077 : Blo 1993435 8090077 := bstep (se 3 (by rfl) ⟨1516889, by rfl⟩ : syracuseStep 8090077 = 3033779) B3033779
theorem B10786769 : Blo 1993435 10786769 := bstep (se 2 (by rfl) ⟨4045038, by rfl⟩ : syracuseStep 10786769 = 8090077) B8090077
theorem B7191179 : Blo 1993435 7191179 := bstep (se 1 (by rfl) ⟨5393384, by rfl⟩ : syracuseStep 7191179 = 10786769) B10786769
theorem B4794119 : Blo 1993435 4794119 := bstep (se 1 (by rfl) ⟨3595589, by rfl⟩ : syracuseStep 4794119 = 7191179) B7191179
theorem B3196079 : Blo 1993435 3196079 := bstep (se 1 (by rfl) ⟨2397059, by rfl⟩ : syracuseStep 3196079 = 4794119) B4794119
theorem B2130719 : Blo 1993435 2130719 := bstep (se 1 (by rfl) ⟨1598039, by rfl⟩ : syracuseStep 2130719 = 3196079) B3196079
theorem B5681917 : Blo 1993435 5681917 := bstep (se 3 (by rfl) ⟨1065359, by rfl⟩ : syracuseStep 5681917 = 2130719) B2130719
theorem B7575889 : Blo 1993435 7575889 := bstep (se 2 (by rfl) ⟨2840958, by rfl⟩ : syracuseStep 7575889 = 5681917) B5681917
theorem B10101185 : Blo 1993435 10101185 := bstep (se 2 (by rfl) ⟨3787944, by rfl⟩ : syracuseStep 10101185 = 7575889) B7575889
theorem B6734123 : Blo 1993435 6734123 := bstep (se 1 (by rfl) ⟨5050592, by rfl⟩ : syracuseStep 6734123 = 10101185) B10101185
theorem B4489415 : Blo 1993435 4489415 := bstep (se 1 (by rfl) ⟨3367061, by rfl⟩ : syracuseStep 4489415 = 6734123) B6734123
theorem B2992943 : Blo 1993435 2992943 := bstep (se 1 (by rfl) ⟨2244707, by rfl⟩ : syracuseStep 2992943 = 4489415) B4489415
theorem B1995295 : Blo 1993435 1995295 := bstep (se 1 (by rfl) ⟨1496471, by rfl⟩ : syracuseStep 1995295 = 2992943) B2992943
theorem B2992949 : Blo 1993435 2992949 := bbase (se 5 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 2992949 = 280589) (by norm_num)
theorem B1995299 : Blo 1993435 1995299 := bstep (se 1 (by rfl) ⟨1496474, by rfl⟩ : syracuseStep 1995299 = 2992949) B2992949
theorem B5050613 : Blo 1993435 5050613 := bbase (se 5 (by rfl) ⟨236747, by rfl⟩ : syracuseStep 5050613 = 473495) (by norm_num)
theorem B3367075 : Blo 1993435 3367075 := bstep (se 1 (by rfl) ⟨2525306, by rfl⟩ : syracuseStep 3367075 = 5050613) B5050613
theorem B4489433 : Blo 1993435 4489433 := bstep (se 2 (by rfl) ⟨1683537, by rfl⟩ : syracuseStep 4489433 = 3367075) B3367075
theorem B2992955 : Blo 1993435 2992955 := bstep (se 1 (by rfl) ⟨2244716, by rfl⟩ : syracuseStep 2992955 = 4489433) B4489433
theorem B1995303 : Blo 1993435 1995303 := bstep (se 1 (by rfl) ⟨1496477, by rfl⟩ : syracuseStep 1995303 = 2992955) B2992955
theorem B2244721 : Blo 1993435 2244721 := bbase (se 2 (by rfl) ⟨841770, by rfl⟩ : syracuseStep 2244721 = 1683541) (by norm_num)
theorem B2992961 : Blo 1993435 2992961 := bstep (se 2 (by rfl) ⟨1122360, by rfl⟩ : syracuseStep 2992961 = 2244721) B2244721
theorem B1995307 : Blo 1993435 1995307 := bstep (se 1 (by rfl) ⟨1496480, by rfl⟩ : syracuseStep 1995307 = 2992961) B2992961
theorem B4794157 : Blo 1993435 4794157 := bbase (se 3 (by rfl) ⟨898904, by rfl⟩ : syracuseStep 4794157 = 1797809) (by norm_num)
theorem B6392209 : Blo 1993435 6392209 := bstep (se 2 (by rfl) ⟨2397078, by rfl⟩ : syracuseStep 6392209 = 4794157) B4794157
theorem B8522945 : Blo 1993435 8522945 := bstep (se 2 (by rfl) ⟨3196104, by rfl⟩ : syracuseStep 8522945 = 6392209) B6392209
theorem B5681963 : Blo 1993435 5681963 := bstep (se 1 (by rfl) ⟨4261472, by rfl⟩ : syracuseStep 5681963 = 8522945) B8522945
theorem B3787975 : Blo 1993435 3787975 := bstep (se 1 (by rfl) ⟨2840981, by rfl⟩ : syracuseStep 3787975 = 5681963) B5681963
theorem B5050633 : Blo 1993435 5050633 := bstep (se 2 (by rfl) ⟨1893987, by rfl⟩ : syracuseStep 5050633 = 3787975) B3787975
theorem B6734177 : Blo 1993435 6734177 := bstep (se 2 (by rfl) ⟨2525316, by rfl⟩ : syracuseStep 6734177 = 5050633) B5050633
theorem B4489451 : Blo 1993435 4489451 := bstep (se 1 (by rfl) ⟨3367088, by rfl⟩ : syracuseStep 4489451 = 6734177) B6734177
theorem B2992967 : Blo 1993435 2992967 := bstep (se 1 (by rfl) ⟨2244725, by rfl⟩ : syracuseStep 2992967 = 4489451) B4489451
theorem B1995311 : Blo 1993435 1995311 := bstep (se 1 (by rfl) ⟨1496483, by rfl⟩ : syracuseStep 1995311 = 2992967) B2992967
theorem B2992973 : Blo 1993435 2992973 := bbase (se 3 (by rfl) ⟨561182, by rfl⟩ : syracuseStep 2992973 = 1122365) (by norm_num)
theorem B1995315 : Blo 1993435 1995315 := bstep (se 1 (by rfl) ⟨1496486, by rfl⟩ : syracuseStep 1995315 = 2992973) B2992973
theorem B4489469 : Blo 1993435 4489469 := bbase (se 3 (by rfl) ⟨841775, by rfl⟩ : syracuseStep 4489469 = 1683551) (by norm_num)
theorem B2992979 : Blo 1993435 2992979 := bstep (se 1 (by rfl) ⟨2244734, by rfl⟩ : syracuseStep 2992979 = 4489469) B4489469
theorem B1995319 : Blo 1993435 1995319 := bstep (se 1 (by rfl) ⟨1496489, by rfl⟩ : syracuseStep 1995319 = 2992979) B2992979
theorem B3367109 : Blo 1993435 3367109 := bbase (se 4 (by rfl) ⟨315666, by rfl⟩ : syracuseStep 3367109 = 631333) (by norm_num)
theorem B2244739 : Blo 1993435 2244739 := bstep (se 1 (by rfl) ⟨1683554, by rfl⟩ : syracuseStep 2244739 = 3367109) B3367109
theorem B2992985 : Blo 1993435 2992985 := bstep (se 2 (by rfl) ⟨1122369, by rfl⟩ : syracuseStep 2992985 = 2244739) B2244739
theorem B1995323 : Blo 1993435 1995323 := bstep (se 1 (by rfl) ⟨1496492, by rfl⟩ : syracuseStep 1995323 = 2992985) B2992985
theorem B15152021 : Blo 1993435 15152021 := bbase (se 6 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 15152021 = 710251) (by norm_num)
theorem B10101347 : Blo 1993435 10101347 := bstep (se 1 (by rfl) ⟨7576010, by rfl⟩ : syracuseStep 10101347 = 15152021) B15152021
theorem B6734231 : Blo 1993435 6734231 := bstep (se 1 (by rfl) ⟨5050673, by rfl⟩ : syracuseStep 6734231 = 10101347) B10101347
theorem B4489487 : Blo 1993435 4489487 := bstep (se 1 (by rfl) ⟨3367115, by rfl⟩ : syracuseStep 4489487 = 6734231) B6734231
theorem B2992991 : Blo 1993435 2992991 := bstep (se 1 (by rfl) ⟨2244743, by rfl⟩ : syracuseStep 2992991 = 4489487) B4489487
theorem B1995327 : Blo 1993435 1995327 := bstep (se 1 (by rfl) ⟨1496495, by rfl⟩ : syracuseStep 1995327 = 2992991) B2992991
theorem B2992997 : Blo 1993435 2992997 := bbase (se 4 (by rfl) ⟨280593, by rfl⟩ : syracuseStep 2992997 = 561187) (by norm_num)
theorem B1995331 : Blo 1993435 1995331 := bstep (se 1 (by rfl) ⟨1496498, by rfl⟩ : syracuseStep 1995331 = 2992997) B2992997
theorem B3788021 : Blo 1993435 3788021 := bbase (se 5 (by rfl) ⟨177563, by rfl⟩ : syracuseStep 3788021 = 355127) (by norm_num)
theorem B2525347 : Blo 1993435 2525347 := bstep (se 1 (by rfl) ⟨1894010, by rfl⟩ : syracuseStep 2525347 = 3788021) B3788021
theorem B3367129 : Blo 1993435 3367129 := bstep (se 2 (by rfl) ⟨1262673, by rfl⟩ : syracuseStep 3367129 = 2525347) B2525347
theorem B4489505 : Blo 1993435 4489505 := bstep (se 2 (by rfl) ⟨1683564, by rfl⟩ : syracuseStep 4489505 = 3367129) B3367129
theorem B2993003 : Blo 1993435 2993003 := bstep (se 1 (by rfl) ⟨2244752, by rfl⟩ : syracuseStep 2993003 = 4489505) B4489505
theorem B1995335 : Blo 1993435 1995335 := bstep (se 1 (by rfl) ⟨1496501, by rfl⟩ : syracuseStep 1995335 = 2993003) B2993003
theorem B2244757 : Blo 1993435 2244757 := bbase (se 6 (by rfl) ⟨52611, by rfl⟩ : syracuseStep 2244757 = 105223) (by norm_num)
theorem B2993009 : Blo 1993435 2993009 := bstep (se 2 (by rfl) ⟨1122378, by rfl⟩ : syracuseStep 2993009 = 2244757) B2244757
theorem B1995339 : Blo 1993435 1995339 := bstep (se 1 (by rfl) ⟨1496504, by rfl⟩ : syracuseStep 1995339 = 2993009) B2993009
theorem B2525357 : Blo 1993435 2525357 := bbase (se 3 (by rfl) ⟨473504, by rfl⟩ : syracuseStep 2525357 = 947009) (by norm_num)
theorem B6734285 : Blo 1993435 6734285 := bstep (se 3 (by rfl) ⟨1262678, by rfl⟩ : syracuseStep 6734285 = 2525357) B2525357
theorem B4489523 : Blo 1993435 4489523 := bstep (se 1 (by rfl) ⟨3367142, by rfl⟩ : syracuseStep 4489523 = 6734285) B6734285
theorem B2993015 : Blo 1993435 2993015 := bstep (se 1 (by rfl) ⟨2244761, by rfl⟩ : syracuseStep 2993015 = 4489523) B4489523
theorem B1995343 : Blo 1993435 1995343 := bstep (se 1 (by rfl) ⟨1496507, by rfl⟩ : syracuseStep 1995343 = 2993015) B2993015
theorem B2993021 : Blo 1993435 2993021 := bbase (se 3 (by rfl) ⟨561191, by rfl⟩ : syracuseStep 2993021 = 1122383) (by norm_num)
theorem B1995347 : Blo 1993435 1995347 := bstep (se 1 (by rfl) ⟨1496510, by rfl⟩ : syracuseStep 1995347 = 2993021) B2993021
theorem B4489541 : Blo 1993435 4489541 := bbase (se 4 (by rfl) ⟨420894, by rfl⟩ : syracuseStep 4489541 = 841789) (by norm_num)
theorem B2993027 : Blo 1993435 2993027 := bstep (se 1 (by rfl) ⟨2244770, by rfl⟩ : syracuseStep 2993027 = 4489541) B4489541
theorem B1995351 : Blo 1993435 1995351 := bstep (se 1 (by rfl) ⟨1496513, by rfl⟩ : syracuseStep 1995351 = 2993027) B2993027
theorem B18203221 : Blo 1993435 18203221 := bbase (se 8 (by rfl) ⟨106659, by rfl⟩ : syracuseStep 18203221 = 213319) (by norm_num)
theorem B24270961 : Blo 1993435 24270961 := bstep (se 2 (by rfl) ⟨9101610, by rfl⟩ : syracuseStep 24270961 = 18203221) B18203221
theorem B32361281 : Blo 1993435 32361281 := bstep (se 2 (by rfl) ⟨12135480, by rfl⟩ : syracuseStep 32361281 = 24270961) B24270961
theorem B21574187 : Blo 1993435 21574187 := bstep (se 1 (by rfl) ⟨16180640, by rfl⟩ : syracuseStep 21574187 = 32361281) B32361281
theorem B14382791 : Blo 1993435 14382791 := bstep (se 1 (by rfl) ⟨10787093, by rfl⟩ : syracuseStep 14382791 = 21574187) B21574187
theorem B9588527 : Blo 1993435 9588527 := bstep (se 1 (by rfl) ⟨7191395, by rfl⟩ : syracuseStep 9588527 = 14382791) B14382791
theorem B6392351 : Blo 1993435 6392351 := bstep (se 1 (by rfl) ⟨4794263, by rfl⟩ : syracuseStep 6392351 = 9588527) B9588527
theorem B4261567 : Blo 1993435 4261567 := bstep (se 1 (by rfl) ⟨3196175, by rfl⟩ : syracuseStep 4261567 = 6392351) B6392351
theorem B5682089 : Blo 1993435 5682089 := bstep (se 2 (by rfl) ⟨2130783, by rfl⟩ : syracuseStep 5682089 = 4261567) B4261567
theorem B3788059 : Blo 1993435 3788059 := bstep (se 1 (by rfl) ⟨2841044, by rfl⟩ : syracuseStep 3788059 = 5682089) B5682089
theorem B5050745 : Blo 1993435 5050745 := bstep (se 2 (by rfl) ⟨1894029, by rfl⟩ : syracuseStep 5050745 = 3788059) B3788059
theorem B3367163 : Blo 1993435 3367163 := bstep (se 1 (by rfl) ⟨2525372, by rfl⟩ : syracuseStep 3367163 = 5050745) B5050745
theorem B2244775 : Blo 1993435 2244775 := bstep (se 1 (by rfl) ⟨1683581, by rfl⟩ : syracuseStep 2244775 = 3367163) B3367163
theorem B2993033 : Blo 1993435 2993033 := bstep (se 2 (by rfl) ⟨1122387, by rfl⟩ : syracuseStep 2993033 = 2244775) B2244775
theorem B1995355 : Blo 1993435 1995355 := bstep (se 1 (by rfl) ⟨1496516, by rfl⟩ : syracuseStep 1995355 = 2993033) B2993033
theorem B10101509 : Blo 1993435 10101509 := bbase (se 4 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 10101509 = 1894033) (by norm_num)
theorem B6734339 : Blo 1993435 6734339 := bstep (se 1 (by rfl) ⟨5050754, by rfl⟩ : syracuseStep 6734339 = 10101509) B10101509
theorem B4489559 : Blo 1993435 4489559 := bstep (se 1 (by rfl) ⟨3367169, by rfl⟩ : syracuseStep 4489559 = 6734339) B6734339
theorem B2993039 : Blo 1993435 2993039 := bstep (se 1 (by rfl) ⟨2244779, by rfl⟩ : syracuseStep 2993039 = 4489559) B4489559
theorem B1995359 : Blo 1993435 1995359 := bstep (se 1 (by rfl) ⟨1496519, by rfl⟩ : syracuseStep 1995359 = 2993039) B2993039
theorem B2993045 : Blo 1993435 2993045 := bbase (se 6 (by rfl) ⟨70149, by rfl⟩ : syracuseStep 2993045 = 140299) (by norm_num)
theorem B1995363 : Blo 1993435 1995363 := bstep (se 1 (by rfl) ⟨1496522, by rfl⟩ : syracuseStep 1995363 = 2993045) B2993045
theorem B11364245 : Blo 1993435 11364245 := bbase (se 6 (by rfl) ⟨266349, by rfl⟩ : syracuseStep 11364245 = 532699) (by norm_num)
theorem B7576163 : Blo 1993435 7576163 := bstep (se 1 (by rfl) ⟨5682122, by rfl⟩ : syracuseStep 7576163 = 11364245) B11364245
theorem B5050775 : Blo 1993435 5050775 := bstep (se 1 (by rfl) ⟨3788081, by rfl⟩ : syracuseStep 5050775 = 7576163) B7576163
theorem B3367183 : Blo 1993435 3367183 := bstep (se 1 (by rfl) ⟨2525387, by rfl⟩ : syracuseStep 3367183 = 5050775) B5050775
theorem B4489577 : Blo 1993435 4489577 := bstep (se 2 (by rfl) ⟨1683591, by rfl⟩ : syracuseStep 4489577 = 3367183) B3367183
theorem B2993051 : Blo 1993435 2993051 := bstep (se 1 (by rfl) ⟨2244788, by rfl⟩ : syracuseStep 2993051 = 4489577) B4489577
theorem B1995367 : Blo 1993435 1995367 := bstep (se 1 (by rfl) ⟨1496525, by rfl⟩ : syracuseStep 1995367 = 2993051) B2993051
theorem B2244793 : Blo 1993435 2244793 := bbase (se 2 (by rfl) ⟨841797, by rfl⟩ : syracuseStep 2244793 = 1683595) (by norm_num)
theorem B2993057 : Blo 1993435 2993057 := bstep (se 2 (by rfl) ⟨1122396, by rfl⟩ : syracuseStep 2993057 = 2244793) B2244793
theorem B1995371 : Blo 1993435 1995371 := bstep (se 1 (by rfl) ⟨1496528, by rfl⟩ : syracuseStep 1995371 = 2993057) B2993057
theorem B6826277 : Blo 1993435 6826277 := bbase (se 4 (by rfl) ⟨639963, by rfl⟩ : syracuseStep 6826277 = 1279927) (by norm_num)
theorem B4550851 : Blo 1993435 4550851 := bstep (se 1 (by rfl) ⟨3413138, by rfl⟩ : syracuseStep 4550851 = 6826277) B6826277
theorem B6067801 : Blo 1993435 6067801 := bstep (se 2 (by rfl) ⟨2275425, by rfl⟩ : syracuseStep 6067801 = 4550851) B4550851
theorem B8090401 : Blo 1993435 8090401 := bstep (se 2 (by rfl) ⟨3033900, by rfl⟩ : syracuseStep 8090401 = 6067801) B6067801
theorem B10787201 : Blo 1993435 10787201 := bstep (se 2 (by rfl) ⟨4045200, by rfl⟩ : syracuseStep 10787201 = 8090401) B8090401
theorem B7191467 : Blo 1993435 7191467 := bstep (se 1 (by rfl) ⟨5393600, by rfl⟩ : syracuseStep 7191467 = 10787201) B10787201
theorem B4794311 : Blo 1993435 4794311 := bstep (se 1 (by rfl) ⟨3595733, by rfl⟩ : syracuseStep 4794311 = 7191467) B7191467
theorem B3196207 : Blo 1993435 3196207 := bstep (se 1 (by rfl) ⟨2397155, by rfl⟩ : syracuseStep 3196207 = 4794311) B4794311
theorem B4261609 : Blo 1993435 4261609 := bstep (se 2 (by rfl) ⟨1598103, by rfl⟩ : syracuseStep 4261609 = 3196207) B3196207
theorem B5682145 : Blo 1993435 5682145 := bstep (se 2 (by rfl) ⟨2130804, by rfl⟩ : syracuseStep 5682145 = 4261609) B4261609
theorem B7576193 : Blo 1993435 7576193 := bstep (se 2 (by rfl) ⟨2841072, by rfl⟩ : syracuseStep 7576193 = 5682145) B5682145
theorem B5050795 : Blo 1993435 5050795 := bstep (se 1 (by rfl) ⟨3788096, by rfl⟩ : syracuseStep 5050795 = 7576193) B7576193
theorem B6734393 : Blo 1993435 6734393 := bstep (se 2 (by rfl) ⟨2525397, by rfl⟩ : syracuseStep 6734393 = 5050795) B5050795
theorem B4489595 : Blo 1993435 4489595 := bstep (se 1 (by rfl) ⟨3367196, by rfl⟩ : syracuseStep 4489595 = 6734393) B6734393
theorem B2993063 : Blo 1993435 2993063 := bstep (se 1 (by rfl) ⟨2244797, by rfl⟩ : syracuseStep 2993063 = 4489595) B4489595
theorem B1995375 : Blo 1993435 1995375 := bstep (se 1 (by rfl) ⟨1496531, by rfl⟩ : syracuseStep 1995375 = 2993063) B2993063
theorem B2993069 : Blo 1993435 2993069 := bbase (se 3 (by rfl) ⟨561200, by rfl⟩ : syracuseStep 2993069 = 1122401) (by norm_num)
theorem B1995379 : Blo 1993435 1995379 := bstep (se 1 (by rfl) ⟨1496534, by rfl⟩ : syracuseStep 1995379 = 2993069) B2993069
theorem B4489613 : Blo 1993435 4489613 := bbase (se 3 (by rfl) ⟨841802, by rfl⟩ : syracuseStep 4489613 = 1683605) (by norm_num)
theorem B2993075 : Blo 1993435 2993075 := bstep (se 1 (by rfl) ⟨2244806, by rfl⟩ : syracuseStep 2993075 = 4489613) B4489613
theorem B1995383 : Blo 1993435 1995383 := bstep (se 1 (by rfl) ⟨1496537, by rfl⟩ : syracuseStep 1995383 = 2993075) B2993075
theorem B2525413 : Blo 1993435 2525413 := bbase (se 4 (by rfl) ⟨236757, by rfl⟩ : syracuseStep 2525413 = 473515) (by norm_num)
theorem B3367217 : Blo 1993435 3367217 := bstep (se 2 (by rfl) ⟨1262706, by rfl⟩ : syracuseStep 3367217 = 2525413) B2525413
theorem B2244811 : Blo 1993435 2244811 := bstep (se 1 (by rfl) ⟨1683608, by rfl⟩ : syracuseStep 2244811 = 3367217) B3367217
theorem B2993081 : Blo 1993435 2993081 := bstep (se 2 (by rfl) ⟨1122405, by rfl⟩ : syracuseStep 2993081 = 2244811) B2244811
theorem B1995387 : Blo 1993435 1995387 := bstep (se 1 (by rfl) ⟨1496540, by rfl⟩ : syracuseStep 1995387 = 2993081) B2993081
theorem B2696821 : Blo 1993435 2696821 := bbase (se 5 (by rfl) ⟨126413, by rfl⟩ : syracuseStep 2696821 = 252827) (by norm_num)
theorem B14383045 : Blo 1993435 14383045 := bstep (se 4 (by rfl) ⟨1348410, by rfl⟩ : syracuseStep 14383045 = 2696821) B2696821
theorem B19177393 : Blo 1993435 19177393 := bstep (se 2 (by rfl) ⟨7191522, by rfl⟩ : syracuseStep 19177393 = 14383045) B14383045
theorem B25569857 : Blo 1993435 25569857 := bstep (se 2 (by rfl) ⟨9588696, by rfl⟩ : syracuseStep 25569857 = 19177393) B19177393
theorem B17046571 : Blo 1993435 17046571 := bstep (se 1 (by rfl) ⟨12784928, by rfl⟩ : syracuseStep 17046571 = 25569857) B25569857
theorem B22728761 : Blo 1993435 22728761 := bstep (se 2 (by rfl) ⟨8523285, by rfl⟩ : syracuseStep 22728761 = 17046571) B17046571
theorem B15152507 : Blo 1993435 15152507 := bstep (se 1 (by rfl) ⟨11364380, by rfl⟩ : syracuseStep 15152507 = 22728761) B22728761
theorem B10101671 : Blo 1993435 10101671 := bstep (se 1 (by rfl) ⟨7576253, by rfl⟩ : syracuseStep 10101671 = 15152507) B15152507
theorem B6734447 : Blo 1993435 6734447 := bstep (se 1 (by rfl) ⟨5050835, by rfl⟩ : syracuseStep 6734447 = 10101671) B10101671
theorem B4489631 : Blo 1993435 4489631 := bstep (se 1 (by rfl) ⟨3367223, by rfl⟩ : syracuseStep 4489631 = 6734447) B6734447
theorem B2993087 : Blo 1993435 2993087 := bstep (se 1 (by rfl) ⟨2244815, by rfl⟩ : syracuseStep 2993087 = 4489631) B4489631
theorem B1995391 : Blo 1993435 1995391 := bstep (se 1 (by rfl) ⟨1496543, by rfl⟩ : syracuseStep 1995391 = 2993087) B2993087
theorem B2993093 : Blo 1993435 2993093 := bbase (se 4 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 2993093 = 561205) (by norm_num)
theorem B1995395 : Blo 1993435 1995395 := bstep (se 1 (by rfl) ⟨1496546, by rfl⟩ : syracuseStep 1995395 = 2993093) B2993093
theorem B3367237 : Blo 1993435 3367237 := bbase (se 4 (by rfl) ⟨315678, by rfl⟩ : syracuseStep 3367237 = 631357) (by norm_num)
theorem B4489649 : Blo 1993435 4489649 := bstep (se 2 (by rfl) ⟨1683618, by rfl⟩ : syracuseStep 4489649 = 3367237) B3367237
theorem B2993099 : Blo 1993435 2993099 := bstep (se 1 (by rfl) ⟨2244824, by rfl⟩ : syracuseStep 2993099 = 4489649) B4489649
theorem B1995399 : Blo 1993435 1995399 := bstep (se 1 (by rfl) ⟨1496549, by rfl⟩ : syracuseStep 1995399 = 2993099) B2993099
theorem B2244829 : Blo 1993435 2244829 := bbase (se 3 (by rfl) ⟨420905, by rfl⟩ : syracuseStep 2244829 = 841811) (by norm_num)
theorem B2993105 : Blo 1993435 2993105 := bstep (se 2 (by rfl) ⟨1122414, by rfl⟩ : syracuseStep 2993105 = 2244829) B2244829
theorem B1995403 : Blo 1993435 1995403 := bstep (se 1 (by rfl) ⟨1496552, by rfl⟩ : syracuseStep 1995403 = 2993105) B2993105
theorem B6734501 : Blo 1993435 6734501 := bbase (se 4 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 6734501 = 1262719) (by norm_num)
theorem B4489667 : Blo 1993435 4489667 := bstep (se 1 (by rfl) ⟨3367250, by rfl⟩ : syracuseStep 4489667 = 6734501) B6734501
theorem B2993111 : Blo 1993435 2993111 := bstep (se 1 (by rfl) ⟨2244833, by rfl⟩ : syracuseStep 2993111 = 4489667) B4489667
theorem B1995407 : Blo 1993435 1995407 := bstep (se 1 (by rfl) ⟨1496555, by rfl⟩ : syracuseStep 1995407 = 2993111) B2993111
theorem B2993117 : Blo 1993435 2993117 := bbase (se 3 (by rfl) ⟨561209, by rfl⟩ : syracuseStep 2993117 = 1122419) (by norm_num)
theorem B1995411 : Blo 1993435 1995411 := bstep (se 1 (by rfl) ⟨1496558, by rfl⟩ : syracuseStep 1995411 = 2993117) B2993117
theorem B4489685 : Blo 1993435 4489685 := bbase (se 7 (by rfl) ⟨52613, by rfl⟩ : syracuseStep 4489685 = 105227) (by norm_num)
theorem B2993123 : Blo 1993435 2993123 := bstep (se 1 (by rfl) ⟨2244842, by rfl⟩ : syracuseStep 2993123 = 4489685) B4489685
theorem B1995415 : Blo 1993435 1995415 := bstep (se 1 (by rfl) ⟨1496561, by rfl⟩ : syracuseStep 1995415 = 2993123) B2993123
theorem B6150725 : Blo 1993435 6150725 := bbase (se 4 (by rfl) ⟨576630, by rfl⟩ : syracuseStep 6150725 = 1153261) (by norm_num)
theorem B4100483 : Blo 1993435 4100483 := bstep (se 1 (by rfl) ⟨3075362, by rfl⟩ : syracuseStep 4100483 = 6150725) B6150725
theorem B10934621 : Blo 1993435 10934621 := bstep (se 3 (by rfl) ⟨2050241, by rfl⟩ : syracuseStep 10934621 = 4100483) B4100483
theorem B7289747 : Blo 1993435 7289747 := bstep (se 1 (by rfl) ⟨5467310, by rfl⟩ : syracuseStep 7289747 = 10934621) B10934621
theorem B4859831 : Blo 1993435 4859831 := bstep (se 1 (by rfl) ⟨3644873, by rfl⟩ : syracuseStep 4859831 = 7289747) B7289747
theorem B3239887 : Blo 1993435 3239887 := bstep (se 1 (by rfl) ⟨2429915, by rfl⟩ : syracuseStep 3239887 = 4859831) B4859831
theorem B4319849 : Blo 1993435 4319849 := bstep (se 2 (by rfl) ⟨1619943, by rfl⟩ : syracuseStep 4319849 = 3239887) B3239887
theorem B11519597 : Blo 1993435 11519597 := bstep (se 3 (by rfl) ⟨2159924, by rfl⟩ : syracuseStep 11519597 = 4319849) B4319849
theorem B7679731 : Blo 1993435 7679731 := bstep (se 1 (by rfl) ⟨5759798, by rfl⟩ : syracuseStep 7679731 = 11519597) B11519597
theorem B10239641 : Blo 1993435 10239641 := bstep (se 2 (by rfl) ⟨3839865, by rfl⟩ : syracuseStep 10239641 = 7679731) B7679731
theorem B6826427 : Blo 1993435 6826427 := bstep (se 1 (by rfl) ⟨5119820, by rfl⟩ : syracuseStep 6826427 = 10239641) B10239641
theorem B4550951 : Blo 1993435 4550951 := bstep (se 1 (by rfl) ⟨3413213, by rfl⟩ : syracuseStep 4550951 = 6826427) B6826427
theorem B12135869 : Blo 1993435 12135869 := bstep (se 3 (by rfl) ⟨2275475, by rfl⟩ : syracuseStep 12135869 = 4550951) B4550951
theorem B8090579 : Blo 1993435 8090579 := bstep (se 1 (by rfl) ⟨6067934, by rfl⟩ : syracuseStep 8090579 = 12135869) B12135869
theorem B5393719 : Blo 1993435 5393719 := bstep (se 1 (by rfl) ⟨4045289, by rfl⟩ : syracuseStep 5393719 = 8090579) B8090579
theorem B28766501 : Blo 1993435 28766501 := bstep (se 4 (by rfl) ⟨2696859, by rfl⟩ : syracuseStep 28766501 = 5393719) B5393719
theorem B19177667 : Blo 1993435 19177667 := bstep (se 1 (by rfl) ⟨14383250, by rfl⟩ : syracuseStep 19177667 = 28766501) B28766501
theorem B12785111 : Blo 1993435 12785111 := bstep (se 1 (by rfl) ⟨9588833, by rfl⟩ : syracuseStep 12785111 = 19177667) B19177667
theorem B8523407 : Blo 1993435 8523407 := bstep (se 1 (by rfl) ⟨6392555, by rfl⟩ : syracuseStep 8523407 = 12785111) B12785111
theorem B5682271 : Blo 1993435 5682271 := bstep (se 1 (by rfl) ⟨4261703, by rfl⟩ : syracuseStep 5682271 = 8523407) B8523407
theorem B7576361 : Blo 1993435 7576361 := bstep (se 2 (by rfl) ⟨2841135, by rfl⟩ : syracuseStep 7576361 = 5682271) B5682271
theorem B5050907 : Blo 1993435 5050907 := bstep (se 1 (by rfl) ⟨3788180, by rfl⟩ : syracuseStep 5050907 = 7576361) B7576361
theorem B3367271 : Blo 1993435 3367271 := bstep (se 1 (by rfl) ⟨2525453, by rfl⟩ : syracuseStep 3367271 = 5050907) B5050907
theorem B2244847 : Blo 1993435 2244847 := bstep (se 1 (by rfl) ⟨1683635, by rfl⟩ : syracuseStep 2244847 = 3367271) B3367271
theorem B2993129 : Blo 1993435 2993129 := bstep (se 2 (by rfl) ⟨1122423, by rfl⟩ : syracuseStep 2993129 = 2244847) B2244847
theorem B1995419 : Blo 1993435 1995419 := bstep (se 1 (by rfl) ⟨1496564, by rfl⟩ : syracuseStep 1995419 = 2993129) B2993129
theorem B3033973 : Blo 1993435 3033973 := bbase (se 5 (by rfl) ⟨142217, by rfl⟩ : syracuseStep 3033973 = 284435) (by norm_num)
theorem B4045297 : Blo 1993435 4045297 := bstep (se 2 (by rfl) ⟨1516986, by rfl⟩ : syracuseStep 4045297 = 3033973) B3033973
theorem B5393729 : Blo 1993435 5393729 := bstep (se 2 (by rfl) ⟨2022648, by rfl⟩ : syracuseStep 5393729 = 4045297) B4045297
theorem B14383277 : Blo 1993435 14383277 := bstep (se 3 (by rfl) ⟨2696864, by rfl⟩ : syracuseStep 14383277 = 5393729) B5393729
theorem B9588851 : Blo 1993435 9588851 := bstep (se 1 (by rfl) ⟨7191638, by rfl⟩ : syracuseStep 9588851 = 14383277) B14383277
theorem B6392567 : Blo 1993435 6392567 := bstep (se 1 (by rfl) ⟨4794425, by rfl⟩ : syracuseStep 6392567 = 9588851) B9588851
theorem B17046845 : Blo 1993435 17046845 := bstep (se 3 (by rfl) ⟨3196283, by rfl⟩ : syracuseStep 17046845 = 6392567) B6392567
theorem B11364563 : Blo 1993435 11364563 := bstep (se 1 (by rfl) ⟨8523422, by rfl⟩ : syracuseStep 11364563 = 17046845) B17046845
theorem B7576375 : Blo 1993435 7576375 := bstep (se 1 (by rfl) ⟨5682281, by rfl⟩ : syracuseStep 7576375 = 11364563) B11364563
theorem B10101833 : Blo 1993435 10101833 := bstep (se 2 (by rfl) ⟨3788187, by rfl⟩ : syracuseStep 10101833 = 7576375) B7576375
theorem B6734555 : Blo 1993435 6734555 := bstep (se 1 (by rfl) ⟨5050916, by rfl⟩ : syracuseStep 6734555 = 10101833) B10101833
theorem B4489703 : Blo 1993435 4489703 := bstep (se 1 (by rfl) ⟨3367277, by rfl⟩ : syracuseStep 4489703 = 6734555) B6734555
theorem B2993135 : Blo 1993435 2993135 := bstep (se 1 (by rfl) ⟨2244851, by rfl⟩ : syracuseStep 2993135 = 4489703) B4489703
theorem B1995423 : Blo 1993435 1995423 := bstep (se 1 (by rfl) ⟨1496567, by rfl⟩ : syracuseStep 1995423 = 2993135) B2993135
theorem B2993141 : Blo 1993435 2993141 := bbase (se 5 (by rfl) ⟨140303, by rfl⟩ : syracuseStep 2993141 = 280607) (by norm_num)
theorem B1995427 : Blo 1993435 1995427 := bstep (se 1 (by rfl) ⟨1496570, by rfl⟩ : syracuseStep 1995427 = 2993141) B2993141
theorem B6067973 : Blo 1993435 6067973 := bbase (se 4 (by rfl) ⟨568872, by rfl⟩ : syracuseStep 6067973 = 1137745) (by norm_num)
theorem B4045315 : Blo 1993435 4045315 := bstep (se 1 (by rfl) ⟨3033986, by rfl⟩ : syracuseStep 4045315 = 6067973) B6067973
theorem B5393753 : Blo 1993435 5393753 := bstep (se 2 (by rfl) ⟨2022657, by rfl⟩ : syracuseStep 5393753 = 4045315) B4045315
theorem B3595835 : Blo 1993435 3595835 := bstep (se 1 (by rfl) ⟨2696876, by rfl⟩ : syracuseStep 3595835 = 5393753) B5393753
theorem B2397223 : Blo 1993435 2397223 := bstep (se 1 (by rfl) ⟨1797917, by rfl⟩ : syracuseStep 2397223 = 3595835) B3595835
theorem B3196297 : Blo 1993435 3196297 := bstep (se 2 (by rfl) ⟨1198611, by rfl⟩ : syracuseStep 3196297 = 2397223) B2397223
theorem B4261729 : Blo 1993435 4261729 := bstep (se 2 (by rfl) ⟨1598148, by rfl⟩ : syracuseStep 4261729 = 3196297) B3196297
theorem B5682305 : Blo 1993435 5682305 := bstep (se 2 (by rfl) ⟨2130864, by rfl⟩ : syracuseStep 5682305 = 4261729) B4261729
theorem B3788203 : Blo 1993435 3788203 := bstep (se 1 (by rfl) ⟨2841152, by rfl⟩ : syracuseStep 3788203 = 5682305) B5682305
theorem B5050937 : Blo 1993435 5050937 := bstep (se 2 (by rfl) ⟨1894101, by rfl⟩ : syracuseStep 5050937 = 3788203) B3788203
theorem B3367291 : Blo 1993435 3367291 := bstep (se 1 (by rfl) ⟨2525468, by rfl⟩ : syracuseStep 3367291 = 5050937) B5050937
theorem B4489721 : Blo 1993435 4489721 := bstep (se 2 (by rfl) ⟨1683645, by rfl⟩ : syracuseStep 4489721 = 3367291) B3367291
theorem B2993147 : Blo 1993435 2993147 := bstep (se 1 (by rfl) ⟨2244860, by rfl⟩ : syracuseStep 2993147 = 4489721) B4489721
theorem B1995431 : Blo 1993435 1995431 := bstep (se 1 (by rfl) ⟨1496573, by rfl⟩ : syracuseStep 1995431 = 2993147) B2993147
theorem B2244865 : Blo 1993435 2244865 := bbase (se 2 (by rfl) ⟨841824, by rfl⟩ : syracuseStep 2244865 = 1683649) (by norm_num)
theorem B2993153 : Blo 1993435 2993153 := bstep (se 2 (by rfl) ⟨1122432, by rfl⟩ : syracuseStep 2993153 = 2244865) B2244865
theorem B1995435 : Blo 1993435 1995435 := bstep (se 1 (by rfl) ⟨1496576, by rfl⟩ : syracuseStep 1995435 = 2993153) B2993153
theorem C0 (j : ℕ) (h1 : 498358 ≤ j) (h2 : j ≤ 498858) : Blo 1993435 (4 * j + 3) := by
  interval_cases j
  · exact B1993435
  · exact B1993439
  · exact B1993443
  · exact B1993447
  · exact B1993451
  · exact B1993455
  · exact B1993459
  · exact B1993463
  · exact B1993467
  · exact B1993471
  · exact B1993475
  · exact B1993479
  · exact B1993483
  · exact B1993487
  · exact B1993491
  · exact B1993495
  · exact B1993499
  · exact B1993503
  · exact B1993507
  · exact B1993511
  · exact B1993515
  · exact B1993519
  · exact B1993523
  · exact B1993527
  · exact B1993531
  · exact B1993535
  · exact B1993539
  · exact B1993543
  · exact B1993547
  · exact B1993551
  · exact B1993555
  · exact B1993559
  · exact B1993563
  · exact B1993567
  · exact B1993571
  · exact B1993575
  · exact B1993579
  · exact B1993583
  · exact B1993587
  · exact B1993591
  · exact B1993595
  · exact B1993599
  · exact B1993603
  · exact B1993607
  · exact B1993611
  · exact B1993615
  · exact B1993619
  · exact B1993623
  · exact B1993627
  · exact B1993631
  · exact B1993635
  · exact B1993639
  · exact B1993643
  · exact B1993647
  · exact B1993651
  · exact B1993655
  · exact B1993659
  · exact B1993663
  · exact B1993667
  · exact B1993671
  · exact B1993675
  · exact B1993679
  · exact B1993683
  · exact B1993687
  · exact B1993691
  · exact B1993695
  · exact B1993699
  · exact B1993703
  · exact B1993707
  · exact B1993711
  · exact B1993715
  · exact B1993719
  · exact B1993723
  · exact B1993727
  · exact B1993731
  · exact B1993735
  · exact B1993739
  · exact B1993743
  · exact B1993747
  · exact B1993751
  · exact B1993755
  · exact B1993759
  · exact B1993763
  · exact B1993767
  · exact B1993771
  · exact B1993775
  · exact B1993779
  · exact B1993783
  · exact B1993787
  · exact B1993791
  · exact B1993795
  · exact B1993799
  · exact B1993803
  · exact B1993807
  · exact B1993811
  · exact B1993815
  · exact B1993819
  · exact B1993823
  · exact B1993827
  · exact B1993831
  · exact B1993835
  · exact B1993839
  · exact B1993843
  · exact B1993847
  · exact B1993851
  · exact B1993855
  · exact B1993859
  · exact B1993863
  · exact B1993867
  · exact B1993871
  · exact B1993875
  · exact B1993879
  · exact B1993883
  · exact B1993887
  · exact B1993891
  · exact B1993895
  · exact B1993899
  · exact B1993903
  · exact B1993907
  · exact B1993911
  · exact B1993915
  · exact B1993919
  · exact B1993923
  · exact B1993927
  · exact B1993931
  · exact B1993935
  · exact B1993939
  · exact B1993943
  · exact B1993947
  · exact B1993951
  · exact B1993955
  · exact B1993959
  · exact B1993963
  · exact B1993967
  · exact B1993971
  · exact B1993975
  · exact B1993979
  · exact B1993983
  · exact B1993987
  · exact B1993991
  · exact B1993995
  · exact B1993999
  · exact B1994003
  · exact B1994007
  · exact B1994011
  · exact B1994015
  · exact B1994019
  · exact B1994023
  · exact B1994027
  · exact B1994031
  · exact B1994035
  · exact B1994039
  · exact B1994043
  · exact B1994047
  · exact B1994051
  · exact B1994055
  · exact B1994059
  · exact B1994063
  · exact B1994067
  · exact B1994071
  · exact B1994075
  · exact B1994079
  · exact B1994083
  · exact B1994087
  · exact B1994091
  · exact B1994095
  · exact B1994099
  · exact B1994103
  · exact B1994107
  · exact B1994111
  · exact B1994115
  · exact B1994119
  · exact B1994123
  · exact B1994127
  · exact B1994131
  · exact B1994135
  · exact B1994139
  · exact B1994143
  · exact B1994147
  · exact B1994151
  · exact B1994155
  · exact B1994159
  · exact B1994163
  · exact B1994167
  · exact B1994171
  · exact B1994175
  · exact B1994179
  · exact B1994183
  · exact B1994187
  · exact B1994191
  · exact B1994195
  · exact B1994199
  · exact B1994203
  · exact B1994207
  · exact B1994211
  · exact B1994215
  · exact B1994219
  · exact B1994223
  · exact B1994227
  · exact B1994231
  · exact B1994235
  · exact B1994239
  · exact B1994243
  · exact B1994247
  · exact B1994251
  · exact B1994255
  · exact B1994259
  · exact B1994263
  · exact B1994267
  · exact B1994271
  · exact B1994275
  · exact B1994279
  · exact B1994283
  · exact B1994287
  · exact B1994291
  · exact B1994295
  · exact B1994299
  · exact B1994303
  · exact B1994307
  · exact B1994311
  · exact B1994315
  · exact B1994319
  · exact B1994323
  · exact B1994327
  · exact B1994331
  · exact B1994335
  · exact B1994339
  · exact B1994343
  · exact B1994347
  · exact B1994351
  · exact B1994355
  · exact B1994359
  · exact B1994363
  · exact B1994367
  · exact B1994371
  · exact B1994375
  · exact B1994379
  · exact B1994383
  · exact B1994387
  · exact B1994391
  · exact B1994395
  · exact B1994399
  · exact B1994403
  · exact B1994407
  · exact B1994411
  · exact B1994415
  · exact B1994419
  · exact B1994423
  · exact B1994427
  · exact B1994431
  · exact B1994435
  · exact B1994439
  · exact B1994443
  · exact B1994447
  · exact B1994451
  · exact B1994455
  · exact B1994459
  · exact B1994463
  · exact B1994467
  · exact B1994471
  · exact B1994475
  · exact B1994479
  · exact B1994483
  · exact B1994487
  · exact B1994491
  · exact B1994495
  · exact B1994499
  · exact B1994503
  · exact B1994507
  · exact B1994511
  · exact B1994515
  · exact B1994519
  · exact B1994523
  · exact B1994527
  · exact B1994531
  · exact B1994535
  · exact B1994539
  · exact B1994543
  · exact B1994547
  · exact B1994551
  · exact B1994555
  · exact B1994559
  · exact B1994563
  · exact B1994567
  · exact B1994571
  · exact B1994575
  · exact B1994579
  · exact B1994583
  · exact B1994587
  · exact B1994591
  · exact B1994595
  · exact B1994599
  · exact B1994603
  · exact B1994607
  · exact B1994611
  · exact B1994615
  · exact B1994619
  · exact B1994623
  · exact B1994627
  · exact B1994631
  · exact B1994635
  · exact B1994639
  · exact B1994643
  · exact B1994647
  · exact B1994651
  · exact B1994655
  · exact B1994659
  · exact B1994663
  · exact B1994667
  · exact B1994671
  · exact B1994675
  · exact B1994679
  · exact B1994683
  · exact B1994687
  · exact B1994691
  · exact B1994695
  · exact B1994699
  · exact B1994703
  · exact B1994707
  · exact B1994711
  · exact B1994715
  · exact B1994719
  · exact B1994723
  · exact B1994727
  · exact B1994731
  · exact B1994735
  · exact B1994739
  · exact B1994743
  · exact B1994747
  · exact B1994751
  · exact B1994755
  · exact B1994759
  · exact B1994763
  · exact B1994767
  · exact B1994771
  · exact B1994775
  · exact B1994779
  · exact B1994783
  · exact B1994787
  · exact B1994791
  · exact B1994795
  · exact B1994799
  · exact B1994803
  · exact B1994807
  · exact B1994811
  · exact B1994815
  · exact B1994819
  · exact B1994823
  · exact B1994827
  · exact B1994831
  · exact B1994835
  · exact B1994839
  · exact B1994843
  · exact B1994847
  · exact B1994851
  · exact B1994855
  · exact B1994859
  · exact B1994863
  · exact B1994867
  · exact B1994871
  · exact B1994875
  · exact B1994879
  · exact B1994883
  · exact B1994887
  · exact B1994891
  · exact B1994895
  · exact B1994899
  · exact B1994903
  · exact B1994907
  · exact B1994911
  · exact B1994915
  · exact B1994919
  · exact B1994923
  · exact B1994927
  · exact B1994931
  · exact B1994935
  · exact B1994939
  · exact B1994943
  · exact B1994947
  · exact B1994951
  · exact B1994955
  · exact B1994959
  · exact B1994963
  · exact B1994967
  · exact B1994971
  · exact B1994975
  · exact B1994979
  · exact B1994983
  · exact B1994987
  · exact B1994991
  · exact B1994995
  · exact B1994999
  · exact B1995003
  · exact B1995007
  · exact B1995011
  · exact B1995015
  · exact B1995019
  · exact B1995023
  · exact B1995027
  · exact B1995031
  · exact B1995035
  · exact B1995039
  · exact B1995043
  · exact B1995047
  · exact B1995051
  · exact B1995055
  · exact B1995059
  · exact B1995063
  · exact B1995067
  · exact B1995071
  · exact B1995075
  · exact B1995079
  · exact B1995083
  · exact B1995087
  · exact B1995091
  · exact B1995095
  · exact B1995099
  · exact B1995103
  · exact B1995107
  · exact B1995111
  · exact B1995115
  · exact B1995119
  · exact B1995123
  · exact B1995127
  · exact B1995131
  · exact B1995135
  · exact B1995139
  · exact B1995143
  · exact B1995147
  · exact B1995151
  · exact B1995155
  · exact B1995159
  · exact B1995163
  · exact B1995167
  · exact B1995171
  · exact B1995175
  · exact B1995179
  · exact B1995183
  · exact B1995187
  · exact B1995191
  · exact B1995195
  · exact B1995199
  · exact B1995203
  · exact B1995207
  · exact B1995211
  · exact B1995215
  · exact B1995219
  · exact B1995223
  · exact B1995227
  · exact B1995231
  · exact B1995235
  · exact B1995239
  · exact B1995243
  · exact B1995247
  · exact B1995251
  · exact B1995255
  · exact B1995259
  · exact B1995263
  · exact B1995267
  · exact B1995271
  · exact B1995275
  · exact B1995279
  · exact B1995283
  · exact B1995287
  · exact B1995291
  · exact B1995295
  · exact B1995299
  · exact B1995303
  · exact B1995307
  · exact B1995311
  · exact B1995315
  · exact B1995319
  · exact B1995323
  · exact B1995327
  · exact B1995331
  · exact B1995335
  · exact B1995339
  · exact B1995343
  · exact B1995347
  · exact B1995351
  · exact B1995355
  · exact B1995359
  · exact B1995363
  · exact B1995367
  · exact B1995371
  · exact B1995375
  · exact B1995379
  · exact B1995383
  · exact B1995387
  · exact B1995391
  · exact B1995395
  · exact B1995399
  · exact B1995403
  · exact B1995407
  · exact B1995411
  · exact B1995415
  · exact B1995419
  · exact B1995423
  · exact B1995427
  · exact B1995431
  · exact B1995435
theorem solution (m : ℕ) (hlo : 1993435 ≤ m) (hhi : m ≤ 1995435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 498358 ≤ j := by omega
    have hj2 : j ≤ 498858 := by omega
    have hb : Blo 1993435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
