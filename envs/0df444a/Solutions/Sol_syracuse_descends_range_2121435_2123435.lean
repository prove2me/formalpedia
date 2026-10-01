-- Prove2me | solution 1 for syracuse_descends_range_2121435_2123435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:57.31385+00:00
-- url     : https://prove2.me/submissions/ebcc4f18-c7d3-4374-a84b-741f20bf9aa4

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

theorem B5369885 : Blo 2121435 5369885 := bbase (se 3 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 5369885 = 2013707) (by norm_num)
theorem B3579923 : Blo 2121435 3579923 := bstep (se 1 (by rfl) ⟨2684942, by rfl⟩ : syracuseStep 3579923 = 5369885) B5369885
theorem B2386615 : Blo 2121435 2386615 := bstep (se 1 (by rfl) ⟨1789961, by rfl⟩ : syracuseStep 2386615 = 3579923) B3579923
theorem B3182153 : Blo 2121435 3182153 := bstep (se 2 (by rfl) ⟨1193307, by rfl⟩ : syracuseStep 3182153 = 2386615) B2386615
theorem B2121435 : Blo 2121435 2121435 := bstep (se 1 (by rfl) ⟨1591076, by rfl⟩ : syracuseStep 2121435 = 3182153) B3182153
theorem B4027421 : Blo 2121435 4027421 := bbase (se 3 (by rfl) ⟨755141, by rfl⟩ : syracuseStep 4027421 = 1510283) (by norm_num)
theorem B10739789 : Blo 2121435 10739789 := bstep (se 3 (by rfl) ⟨2013710, by rfl⟩ : syracuseStep 10739789 = 4027421) B4027421
theorem B7159859 : Blo 2121435 7159859 := bstep (se 1 (by rfl) ⟨5369894, by rfl⟩ : syracuseStep 7159859 = 10739789) B10739789
theorem B4773239 : Blo 2121435 4773239 := bstep (se 1 (by rfl) ⟨3579929, by rfl⟩ : syracuseStep 4773239 = 7159859) B7159859
theorem B3182159 : Blo 2121435 3182159 := bstep (se 1 (by rfl) ⟨2386619, by rfl⟩ : syracuseStep 3182159 = 4773239) B4773239
theorem B2121439 : Blo 2121435 2121439 := bstep (se 1 (by rfl) ⟨1591079, by rfl⟩ : syracuseStep 2121439 = 3182159) B3182159
theorem B3182165 : Blo 2121435 3182165 := bbase (se 8 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 3182165 = 37291) (by norm_num)
theorem B2121443 : Blo 2121435 2121443 := bstep (se 1 (by rfl) ⟨1591082, by rfl⟩ : syracuseStep 2121443 = 3182165) B3182165
theorem B9061733 : Blo 2121435 9061733 := bbase (se 4 (by rfl) ⟨849537, by rfl⟩ : syracuseStep 9061733 = 1699075) (by norm_num)
theorem B6041155 : Blo 2121435 6041155 := bstep (se 1 (by rfl) ⟨4530866, by rfl⟩ : syracuseStep 6041155 = 9061733) B9061733
theorem B8054873 : Blo 2121435 8054873 := bstep (se 2 (by rfl) ⟨3020577, by rfl⟩ : syracuseStep 8054873 = 6041155) B6041155
theorem B5369915 : Blo 2121435 5369915 := bstep (se 1 (by rfl) ⟨4027436, by rfl⟩ : syracuseStep 5369915 = 8054873) B8054873
theorem B3579943 : Blo 2121435 3579943 := bstep (se 1 (by rfl) ⟨2684957, by rfl⟩ : syracuseStep 3579943 = 5369915) B5369915
theorem B4773257 : Blo 2121435 4773257 := bstep (se 2 (by rfl) ⟨1789971, by rfl⟩ : syracuseStep 4773257 = 3579943) B3579943
theorem B3182171 : Blo 2121435 3182171 := bstep (se 1 (by rfl) ⟨2386628, by rfl⟩ : syracuseStep 3182171 = 4773257) B4773257
theorem B2121447 : Blo 2121435 2121447 := bstep (se 1 (by rfl) ⟨1591085, by rfl⟩ : syracuseStep 2121447 = 3182171) B3182171
theorem B2386633 : Blo 2121435 2386633 := bbase (se 2 (by rfl) ⟨894987, by rfl⟩ : syracuseStep 2386633 = 1789975) (by norm_num)
theorem B3182177 : Blo 2121435 3182177 := bstep (se 2 (by rfl) ⟨1193316, by rfl⟩ : syracuseStep 3182177 = 2386633) B2386633
theorem B2121451 : Blo 2121435 2121451 := bstep (se 1 (by rfl) ⟨1591088, by rfl⟩ : syracuseStep 2121451 = 3182177) B3182177
theorem B6796325 : Blo 2121435 6796325 := bbase (se 4 (by rfl) ⟨637155, by rfl⟩ : syracuseStep 6796325 = 1274311) (by norm_num)
theorem B18123533 : Blo 2121435 18123533 := bstep (se 3 (by rfl) ⟨3398162, by rfl⟩ : syracuseStep 18123533 = 6796325) B6796325
theorem B12082355 : Blo 2121435 12082355 := bstep (se 1 (by rfl) ⟨9061766, by rfl⟩ : syracuseStep 12082355 = 18123533) B18123533
theorem B8054903 : Blo 2121435 8054903 := bstep (se 1 (by rfl) ⟨6041177, by rfl⟩ : syracuseStep 8054903 = 12082355) B12082355
theorem B5369935 : Blo 2121435 5369935 := bstep (se 1 (by rfl) ⟨4027451, by rfl⟩ : syracuseStep 5369935 = 8054903) B8054903
theorem B7159913 : Blo 2121435 7159913 := bstep (se 2 (by rfl) ⟨2684967, by rfl⟩ : syracuseStep 7159913 = 5369935) B5369935
theorem B4773275 : Blo 2121435 4773275 := bstep (se 1 (by rfl) ⟨3579956, by rfl⟩ : syracuseStep 4773275 = 7159913) B7159913
theorem B3182183 : Blo 2121435 3182183 := bstep (se 1 (by rfl) ⟨2386637, by rfl⟩ : syracuseStep 3182183 = 4773275) B4773275
theorem B2121455 : Blo 2121435 2121455 := bstep (se 1 (by rfl) ⟨1591091, by rfl⟩ : syracuseStep 2121455 = 3182183) B3182183
theorem B3182189 : Blo 2121435 3182189 := bbase (se 3 (by rfl) ⟨596660, by rfl⟩ : syracuseStep 3182189 = 1193321) (by norm_num)
theorem B2121459 : Blo 2121435 2121459 := bstep (se 1 (by rfl) ⟨1591094, by rfl⟩ : syracuseStep 2121459 = 3182189) B3182189
theorem B4773293 : Blo 2121435 4773293 := bbase (se 3 (by rfl) ⟨894992, by rfl⟩ : syracuseStep 4773293 = 1789985) (by norm_num)
theorem B3182195 : Blo 2121435 3182195 := bstep (se 1 (by rfl) ⟨2386646, by rfl⟩ : syracuseStep 3182195 = 4773293) B4773293
theorem B2121463 : Blo 2121435 2121463 := bstep (se 1 (by rfl) ⟨1591097, by rfl⟩ : syracuseStep 2121463 = 3182195) B3182195
theorem B8601653 : Blo 2121435 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B5734435 : Blo 2121435 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B7645913 : Blo 2121435 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B5097275 : Blo 2121435 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B3398183 : Blo 2121435 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B2265455 : Blo 2121435 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B6041213 : Blo 2121435 6041213 := bstep (se 3 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 6041213 = 2265455) B2265455
theorem B4027475 : Blo 2121435 4027475 := bstep (se 1 (by rfl) ⟨3020606, by rfl⟩ : syracuseStep 4027475 = 6041213) B6041213
theorem B2684983 : Blo 2121435 2684983 := bstep (se 1 (by rfl) ⟨2013737, by rfl⟩ : syracuseStep 2684983 = 4027475) B4027475
theorem B3579977 : Blo 2121435 3579977 := bstep (se 2 (by rfl) ⟨1342491, by rfl⟩ : syracuseStep 3579977 = 2684983) B2684983
theorem B2386651 : Blo 2121435 2386651 := bstep (se 1 (by rfl) ⟨1789988, by rfl⟩ : syracuseStep 2386651 = 3579977) B3579977
theorem B3182201 : Blo 2121435 3182201 := bstep (se 2 (by rfl) ⟨1193325, by rfl⟩ : syracuseStep 3182201 = 2386651) B2386651
theorem B2121467 : Blo 2121435 2121467 := bstep (se 1 (by rfl) ⟨1591100, by rfl⟩ : syracuseStep 2121467 = 3182201) B3182201
theorem B6983093 : Blo 2121435 6983093 := bbase (se 5 (by rfl) ⟨327332, by rfl⟩ : syracuseStep 6983093 = 654665) (by norm_num)
theorem B4655395 : Blo 2121435 4655395 := bstep (se 1 (by rfl) ⟨3491546, by rfl⟩ : syracuseStep 4655395 = 6983093) B6983093
theorem B6207193 : Blo 2121435 6207193 := bstep (se 2 (by rfl) ⟨2327697, by rfl⟩ : syracuseStep 6207193 = 4655395) B4655395
theorem B33105029 : Blo 2121435 33105029 := bstep (se 4 (by rfl) ⟨3103596, by rfl⟩ : syracuseStep 33105029 = 6207193) B6207193
theorem B88280077 : Blo 2121435 88280077 := bstep (se 3 (by rfl) ⟨16552514, by rfl⟩ : syracuseStep 88280077 = 33105029) B33105029
theorem B117706769 : Blo 2121435 117706769 := bstep (se 2 (by rfl) ⟨44140038, by rfl⟩ : syracuseStep 117706769 = 88280077) B88280077
theorem B78471179 : Blo 2121435 78471179 := bstep (se 1 (by rfl) ⟨58853384, by rfl⟩ : syracuseStep 78471179 = 117706769) B117706769
theorem B52314119 : Blo 2121435 52314119 := bstep (se 1 (by rfl) ⟨39235589, by rfl⟩ : syracuseStep 52314119 = 78471179) B78471179
theorem B34876079 : Blo 2121435 34876079 := bstep (se 1 (by rfl) ⟨26157059, by rfl⟩ : syracuseStep 34876079 = 52314119) B52314119
theorem B23250719 : Blo 2121435 23250719 := bstep (se 1 (by rfl) ⟨17438039, by rfl⟩ : syracuseStep 23250719 = 34876079) B34876079
theorem B15500479 : Blo 2121435 15500479 := bstep (se 1 (by rfl) ⟨11625359, by rfl⟩ : syracuseStep 15500479 = 23250719) B23250719
theorem B20667305 : Blo 2121435 20667305 := bstep (se 2 (by rfl) ⟨7750239, by rfl⟩ : syracuseStep 20667305 = 15500479) B15500479
theorem B13778203 : Blo 2121435 13778203 := bstep (se 1 (by rfl) ⟨10333652, by rfl⟩ : syracuseStep 13778203 = 20667305) B20667305
theorem B18370937 : Blo 2121435 18370937 := bstep (se 2 (by rfl) ⟨6889101, by rfl⟩ : syracuseStep 18370937 = 13778203) B13778203
theorem B12247291 : Blo 2121435 12247291 := bstep (se 1 (by rfl) ⟨9185468, by rfl⟩ : syracuseStep 12247291 = 18370937) B18370937
theorem B65318885 : Blo 2121435 65318885 := bstep (se 4 (by rfl) ⟨6123645, by rfl⟩ : syracuseStep 65318885 = 12247291) B12247291
theorem B43545923 : Blo 2121435 43545923 := bstep (se 1 (by rfl) ⟨32659442, by rfl⟩ : syracuseStep 43545923 = 65318885) B65318885
theorem B29030615 : Blo 2121435 29030615 := bstep (se 1 (by rfl) ⟨21772961, by rfl⟩ : syracuseStep 29030615 = 43545923) B43545923
theorem B19353743 : Blo 2121435 19353743 := bstep (se 1 (by rfl) ⟨14515307, by rfl⟩ : syracuseStep 19353743 = 29030615) B29030615
theorem B12902495 : Blo 2121435 12902495 := bstep (se 1 (by rfl) ⟨9676871, by rfl⟩ : syracuseStep 12902495 = 19353743) B19353743
theorem B137626613 : Blo 2121435 137626613 := bstep (se 5 (by rfl) ⟨6451247, by rfl⟩ : syracuseStep 137626613 = 12902495) B12902495
theorem B91751075 : Blo 2121435 91751075 := bstep (se 1 (by rfl) ⟨68813306, by rfl⟩ : syracuseStep 91751075 = 137626613) B137626613
theorem B61167383 : Blo 2121435 61167383 := bstep (se 1 (by rfl) ⟨45875537, by rfl⟩ : syracuseStep 61167383 = 91751075) B91751075
theorem B40778255 : Blo 2121435 40778255 := bstep (se 1 (by rfl) ⟨30583691, by rfl⟩ : syracuseStep 40778255 = 61167383) B61167383
theorem B27185503 : Blo 2121435 27185503 := bstep (se 1 (by rfl) ⟨20389127, by rfl⟩ : syracuseStep 27185503 = 40778255) B40778255
theorem B36247337 : Blo 2121435 36247337 := bstep (se 2 (by rfl) ⟨13592751, by rfl⟩ : syracuseStep 36247337 = 27185503) B27185503
theorem B24164891 : Blo 2121435 24164891 := bstep (se 1 (by rfl) ⟨18123668, by rfl⟩ : syracuseStep 24164891 = 36247337) B36247337
theorem B16109927 : Blo 2121435 16109927 := bstep (se 1 (by rfl) ⟨12082445, by rfl⟩ : syracuseStep 16109927 = 24164891) B24164891
theorem B10739951 : Blo 2121435 10739951 := bstep (se 1 (by rfl) ⟨8054963, by rfl⟩ : syracuseStep 10739951 = 16109927) B16109927
theorem B7159967 : Blo 2121435 7159967 := bstep (se 1 (by rfl) ⟨5369975, by rfl⟩ : syracuseStep 7159967 = 10739951) B10739951
theorem B4773311 : Blo 2121435 4773311 := bstep (se 1 (by rfl) ⟨3579983, by rfl⟩ : syracuseStep 4773311 = 7159967) B7159967
theorem B3182207 : Blo 2121435 3182207 := bstep (se 1 (by rfl) ⟨2386655, by rfl⟩ : syracuseStep 3182207 = 4773311) B4773311
theorem B2121471 : Blo 2121435 2121471 := bstep (se 1 (by rfl) ⟨1591103, by rfl⟩ : syracuseStep 2121471 = 3182207) B3182207
theorem B3182213 : Blo 2121435 3182213 := bbase (se 4 (by rfl) ⟨298332, by rfl⟩ : syracuseStep 3182213 = 596665) (by norm_num)
theorem B2121475 : Blo 2121435 2121475 := bstep (se 1 (by rfl) ⟨1591106, by rfl⟩ : syracuseStep 2121475 = 3182213) B3182213
theorem B3579997 : Blo 2121435 3579997 := bbase (se 3 (by rfl) ⟨671249, by rfl⟩ : syracuseStep 3579997 = 1342499) (by norm_num)
theorem B4773329 : Blo 2121435 4773329 := bstep (se 2 (by rfl) ⟨1789998, by rfl⟩ : syracuseStep 4773329 = 3579997) B3579997
theorem B3182219 : Blo 2121435 3182219 := bstep (se 1 (by rfl) ⟨2386664, by rfl⟩ : syracuseStep 3182219 = 4773329) B4773329
theorem B2121479 : Blo 2121435 2121479 := bstep (se 1 (by rfl) ⟨1591109, by rfl⟩ : syracuseStep 2121479 = 3182219) B3182219
theorem B2386669 : Blo 2121435 2386669 := bbase (se 3 (by rfl) ⟨447500, by rfl⟩ : syracuseStep 2386669 = 895001) (by norm_num)
theorem B3182225 : Blo 2121435 3182225 := bstep (se 2 (by rfl) ⟨1193334, by rfl⟩ : syracuseStep 3182225 = 2386669) B2386669
theorem B2121483 : Blo 2121435 2121483 := bstep (se 1 (by rfl) ⟨1591112, by rfl⟩ : syracuseStep 2121483 = 3182225) B3182225
theorem B7160021 : Blo 2121435 7160021 := bbase (se 7 (by rfl) ⟨83906, by rfl⟩ : syracuseStep 7160021 = 167813) (by norm_num)
theorem B4773347 : Blo 2121435 4773347 := bstep (se 1 (by rfl) ⟨3580010, by rfl⟩ : syracuseStep 4773347 = 7160021) B7160021
theorem B3182231 : Blo 2121435 3182231 := bstep (se 1 (by rfl) ⟨2386673, by rfl⟩ : syracuseStep 3182231 = 4773347) B4773347
theorem B2121487 : Blo 2121435 2121487 := bstep (se 1 (by rfl) ⟨1591115, by rfl⟩ : syracuseStep 2121487 = 3182231) B3182231
theorem B3182237 : Blo 2121435 3182237 := bbase (se 3 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 3182237 = 1193339) (by norm_num)
theorem B2121491 : Blo 2121435 2121491 := bstep (se 1 (by rfl) ⟨1591118, by rfl⟩ : syracuseStep 2121491 = 3182237) B3182237
theorem B4773365 : Blo 2121435 4773365 := bbase (se 5 (by rfl) ⟨223751, by rfl⟩ : syracuseStep 4773365 = 447503) (by norm_num)
theorem B3182243 : Blo 2121435 3182243 := bstep (se 1 (by rfl) ⟨2386682, by rfl⟩ : syracuseStep 3182243 = 4773365) B4773365
theorem B2121495 : Blo 2121435 2121495 := bstep (se 1 (by rfl) ⟨1591121, by rfl⟩ : syracuseStep 2121495 = 3182243) B3182243
theorem B4838501 : Blo 2121435 4838501 := bbase (se 4 (by rfl) ⟨453609, by rfl⟩ : syracuseStep 4838501 = 907219) (by norm_num)
theorem B12902669 : Blo 2121435 12902669 := bstep (se 3 (by rfl) ⟨2419250, by rfl⟩ : syracuseStep 12902669 = 4838501) B4838501
theorem B8601779 : Blo 2121435 8601779 := bstep (se 1 (by rfl) ⟨6451334, by rfl⟩ : syracuseStep 8601779 = 12902669) B12902669
theorem B5734519 : Blo 2121435 5734519 := bstep (se 1 (by rfl) ⟨4300889, by rfl⟩ : syracuseStep 5734519 = 8601779) B8601779
theorem B30584101 : Blo 2121435 30584101 := bstep (se 4 (by rfl) ⟨2867259, by rfl⟩ : syracuseStep 30584101 = 5734519) B5734519
theorem B40778801 : Blo 2121435 40778801 := bstep (se 2 (by rfl) ⟨15292050, by rfl⟩ : syracuseStep 40778801 = 30584101) B30584101
theorem B27185867 : Blo 2121435 27185867 := bstep (se 1 (by rfl) ⟨20389400, by rfl⟩ : syracuseStep 27185867 = 40778801) B40778801
theorem B18123911 : Blo 2121435 18123911 := bstep (se 1 (by rfl) ⟨13592933, by rfl⟩ : syracuseStep 18123911 = 27185867) B27185867
theorem B12082607 : Blo 2121435 12082607 := bstep (se 1 (by rfl) ⟨9061955, by rfl⟩ : syracuseStep 12082607 = 18123911) B18123911
theorem B8055071 : Blo 2121435 8055071 := bstep (se 1 (by rfl) ⟨6041303, by rfl⟩ : syracuseStep 8055071 = 12082607) B12082607
theorem B5370047 : Blo 2121435 5370047 := bstep (se 1 (by rfl) ⟨4027535, by rfl⟩ : syracuseStep 5370047 = 8055071) B8055071
theorem B3580031 : Blo 2121435 3580031 := bstep (se 1 (by rfl) ⟨2685023, by rfl⟩ : syracuseStep 3580031 = 5370047) B5370047
theorem B2386687 : Blo 2121435 2386687 := bstep (se 1 (by rfl) ⟨1790015, by rfl⟩ : syracuseStep 2386687 = 3580031) B3580031
theorem B3182249 : Blo 2121435 3182249 := bstep (se 2 (by rfl) ⟨1193343, by rfl⟩ : syracuseStep 3182249 = 2386687) B2386687
theorem B2121499 : Blo 2121435 2121499 := bstep (se 1 (by rfl) ⟨1591124, by rfl⟩ : syracuseStep 2121499 = 3182249) B3182249
theorem B2265493 : Blo 2121435 2265493 := bbase (se 6 (by rfl) ⟨53097, by rfl⟩ : syracuseStep 2265493 = 106195) (by norm_num)
theorem B3020657 : Blo 2121435 3020657 := bstep (se 2 (by rfl) ⟨1132746, by rfl⟩ : syracuseStep 3020657 = 2265493) B2265493
theorem B8055085 : Blo 2121435 8055085 := bstep (se 3 (by rfl) ⟨1510328, by rfl⟩ : syracuseStep 8055085 = 3020657) B3020657
theorem B10740113 : Blo 2121435 10740113 := bstep (se 2 (by rfl) ⟨4027542, by rfl⟩ : syracuseStep 10740113 = 8055085) B8055085
theorem B7160075 : Blo 2121435 7160075 := bstep (se 1 (by rfl) ⟨5370056, by rfl⟩ : syracuseStep 7160075 = 10740113) B10740113
theorem B4773383 : Blo 2121435 4773383 := bstep (se 1 (by rfl) ⟨3580037, by rfl⟩ : syracuseStep 4773383 = 7160075) B7160075
theorem B3182255 : Blo 2121435 3182255 := bstep (se 1 (by rfl) ⟨2386691, by rfl⟩ : syracuseStep 3182255 = 4773383) B4773383
theorem B2121503 : Blo 2121435 2121503 := bstep (se 1 (by rfl) ⟨1591127, by rfl⟩ : syracuseStep 2121503 = 3182255) B3182255
theorem B3182261 : Blo 2121435 3182261 := bbase (se 5 (by rfl) ⟨149168, by rfl⟩ : syracuseStep 3182261 = 298337) (by norm_num)
theorem B2121507 : Blo 2121435 2121507 := bstep (se 1 (by rfl) ⟨1591130, by rfl⟩ : syracuseStep 2121507 = 3182261) B3182261
theorem B5370077 : Blo 2121435 5370077 := bbase (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) (by norm_num)
theorem B3580051 : Blo 2121435 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B4773401 : Blo 2121435 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B3182267 : Blo 2121435 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B2121511 : Blo 2121435 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B2386705 : Blo 2121435 2386705 := bbase (se 2 (by rfl) ⟨895014, by rfl⟩ : syracuseStep 2386705 = 1790029) (by norm_num)
theorem B3182273 : Blo 2121435 3182273 := bstep (se 2 (by rfl) ⟨1193352, by rfl⟩ : syracuseStep 3182273 = 2386705) B2386705
theorem B2121515 : Blo 2121435 2121515 := bstep (se 1 (by rfl) ⟨1591136, by rfl⟩ : syracuseStep 2121515 = 3182273) B3182273
theorem B4027573 : Blo 2121435 4027573 := bbase (se 5 (by rfl) ⟨188792, by rfl⟩ : syracuseStep 4027573 = 377585) (by norm_num)
theorem B5370097 : Blo 2121435 5370097 := bstep (se 2 (by rfl) ⟨2013786, by rfl⟩ : syracuseStep 5370097 = 4027573) B4027573
theorem B7160129 : Blo 2121435 7160129 := bstep (se 2 (by rfl) ⟨2685048, by rfl⟩ : syracuseStep 7160129 = 5370097) B5370097
theorem B4773419 : Blo 2121435 4773419 := bstep (se 1 (by rfl) ⟨3580064, by rfl⟩ : syracuseStep 4773419 = 7160129) B7160129
theorem B3182279 : Blo 2121435 3182279 := bstep (se 1 (by rfl) ⟨2386709, by rfl⟩ : syracuseStep 3182279 = 4773419) B4773419
theorem B2121519 : Blo 2121435 2121519 := bstep (se 1 (by rfl) ⟨1591139, by rfl⟩ : syracuseStep 2121519 = 3182279) B3182279
theorem B3182285 : Blo 2121435 3182285 := bbase (se 3 (by rfl) ⟨596678, by rfl⟩ : syracuseStep 3182285 = 1193357) (by norm_num)
theorem B2121523 : Blo 2121435 2121523 := bstep (se 1 (by rfl) ⟨1591142, by rfl⟩ : syracuseStep 2121523 = 3182285) B3182285
theorem B4773437 : Blo 2121435 4773437 := bbase (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) (by norm_num)
theorem B3182291 : Blo 2121435 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2121527 : Blo 2121435 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B3580085 : Blo 2121435 3580085 := bbase (se 5 (by rfl) ⟨167816, by rfl⟩ : syracuseStep 3580085 = 335633) (by norm_num)
theorem B2386723 : Blo 2121435 2386723 := bstep (se 1 (by rfl) ⟨1790042, by rfl⟩ : syracuseStep 2386723 = 3580085) B3580085
theorem B3182297 : Blo 2121435 3182297 := bstep (se 2 (by rfl) ⟨1193361, by rfl⟩ : syracuseStep 3182297 = 2386723) B2386723
theorem B2121531 : Blo 2121435 2121531 := bstep (se 1 (by rfl) ⟨1591148, by rfl⟩ : syracuseStep 2121531 = 3182297) B3182297
theorem B5097437 : Blo 2121435 5097437 := bbase (se 3 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 5097437 = 1911539) (by norm_num)
theorem B3398291 : Blo 2121435 3398291 := bstep (se 1 (by rfl) ⟨2548718, by rfl⟩ : syracuseStep 3398291 = 5097437) B5097437
theorem B2265527 : Blo 2121435 2265527 := bstep (se 1 (by rfl) ⟨1699145, by rfl⟩ : syracuseStep 2265527 = 3398291) B3398291
theorem B6041405 : Blo 2121435 6041405 := bstep (se 3 (by rfl) ⟨1132763, by rfl⟩ : syracuseStep 6041405 = 2265527) B2265527
theorem B16110413 : Blo 2121435 16110413 := bstep (se 3 (by rfl) ⟨3020702, by rfl⟩ : syracuseStep 16110413 = 6041405) B6041405
theorem B10740275 : Blo 2121435 10740275 := bstep (se 1 (by rfl) ⟨8055206, by rfl⟩ : syracuseStep 10740275 = 16110413) B16110413
theorem B7160183 : Blo 2121435 7160183 := bstep (se 1 (by rfl) ⟨5370137, by rfl⟩ : syracuseStep 7160183 = 10740275) B10740275
theorem B4773455 : Blo 2121435 4773455 := bstep (se 1 (by rfl) ⟨3580091, by rfl⟩ : syracuseStep 4773455 = 7160183) B7160183
theorem B3182303 : Blo 2121435 3182303 := bstep (se 1 (by rfl) ⟨2386727, by rfl⟩ : syracuseStep 3182303 = 4773455) B4773455
theorem B2121535 : Blo 2121435 2121535 := bstep (se 1 (by rfl) ⟨1591151, by rfl⟩ : syracuseStep 2121535 = 3182303) B3182303
theorem B3182309 : Blo 2121435 3182309 := bbase (se 4 (by rfl) ⟨298341, by rfl⟩ : syracuseStep 3182309 = 596683) (by norm_num)
theorem B2121539 : Blo 2121435 2121539 := bstep (se 1 (by rfl) ⟨1591154, by rfl⟩ : syracuseStep 2121539 = 3182309) B3182309
theorem B6041429 : Blo 2121435 6041429 := bbase (se 9 (by rfl) ⟨17699, by rfl⟩ : syracuseStep 6041429 = 35399) (by norm_num)
theorem B4027619 : Blo 2121435 4027619 := bstep (se 1 (by rfl) ⟨3020714, by rfl⟩ : syracuseStep 4027619 = 6041429) B6041429
theorem B2685079 : Blo 2121435 2685079 := bstep (se 1 (by rfl) ⟨2013809, by rfl⟩ : syracuseStep 2685079 = 4027619) B4027619
theorem B3580105 : Blo 2121435 3580105 := bstep (se 2 (by rfl) ⟨1342539, by rfl⟩ : syracuseStep 3580105 = 2685079) B2685079
theorem B4773473 : Blo 2121435 4773473 := bstep (se 2 (by rfl) ⟨1790052, by rfl⟩ : syracuseStep 4773473 = 3580105) B3580105
theorem B3182315 : Blo 2121435 3182315 := bstep (se 1 (by rfl) ⟨2386736, by rfl⟩ : syracuseStep 3182315 = 4773473) B4773473
theorem B2121543 : Blo 2121435 2121543 := bstep (se 1 (by rfl) ⟨1591157, by rfl⟩ : syracuseStep 2121543 = 3182315) B3182315
theorem B2386741 : Blo 2121435 2386741 := bbase (se 5 (by rfl) ⟨111878, by rfl⟩ : syracuseStep 2386741 = 223757) (by norm_num)
theorem B3182321 : Blo 2121435 3182321 := bstep (se 2 (by rfl) ⟨1193370, by rfl⟩ : syracuseStep 3182321 = 2386741) B2386741
theorem B2121547 : Blo 2121435 2121547 := bstep (se 1 (by rfl) ⟨1591160, by rfl⟩ : syracuseStep 2121547 = 3182321) B3182321
theorem B2685089 : Blo 2121435 2685089 := bbase (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) (by norm_num)
theorem B7160237 : Blo 2121435 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B4773491 : Blo 2121435 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B3182327 : Blo 2121435 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B2121551 : Blo 2121435 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B3182333 : Blo 2121435 3182333 := bbase (se 3 (by rfl) ⟨596687, by rfl⟩ : syracuseStep 3182333 = 1193375) (by norm_num)
theorem B2121555 : Blo 2121435 2121555 := bstep (se 1 (by rfl) ⟨1591166, by rfl⟩ : syracuseStep 2121555 = 3182333) B3182333
theorem B4773509 : Blo 2121435 4773509 := bbase (se 4 (by rfl) ⟨447516, by rfl⟩ : syracuseStep 4773509 = 895033) (by norm_num)
theorem B3182339 : Blo 2121435 3182339 := bstep (se 1 (by rfl) ⟨2386754, by rfl⟩ : syracuseStep 3182339 = 4773509) B4773509
theorem B2121559 : Blo 2121435 2121559 := bstep (se 1 (by rfl) ⟨1591169, by rfl⟩ : syracuseStep 2121559 = 3182339) B3182339
theorem B4301021 : Blo 2121435 4301021 := bbase (se 3 (by rfl) ⟨806441, by rfl⟩ : syracuseStep 4301021 = 1612883) (by norm_num)
theorem B2867347 : Blo 2121435 2867347 := bstep (se 1 (by rfl) ⟨2150510, by rfl⟩ : syracuseStep 2867347 = 4301021) B4301021
theorem B3823129 : Blo 2121435 3823129 := bstep (se 2 (by rfl) ⟨1433673, by rfl⟩ : syracuseStep 3823129 = 2867347) B2867347
theorem B5097505 : Blo 2121435 5097505 := bstep (se 2 (by rfl) ⟨1911564, by rfl⟩ : syracuseStep 5097505 = 3823129) B3823129
theorem B6796673 : Blo 2121435 6796673 := bstep (se 2 (by rfl) ⟨2548752, by rfl⟩ : syracuseStep 6796673 = 5097505) B5097505
theorem B4531115 : Blo 2121435 4531115 := bstep (se 1 (by rfl) ⟨3398336, by rfl⟩ : syracuseStep 4531115 = 6796673) B6796673
theorem B3020743 : Blo 2121435 3020743 := bstep (se 1 (by rfl) ⟨2265557, by rfl⟩ : syracuseStep 3020743 = 4531115) B4531115
theorem B4027657 : Blo 2121435 4027657 := bstep (se 2 (by rfl) ⟨1510371, by rfl⟩ : syracuseStep 4027657 = 3020743) B3020743
theorem B5370209 : Blo 2121435 5370209 := bstep (se 2 (by rfl) ⟨2013828, by rfl⟩ : syracuseStep 5370209 = 4027657) B4027657
theorem B3580139 : Blo 2121435 3580139 := bstep (se 1 (by rfl) ⟨2685104, by rfl⟩ : syracuseStep 3580139 = 5370209) B5370209
theorem B2386759 : Blo 2121435 2386759 := bstep (se 1 (by rfl) ⟨1790069, by rfl⟩ : syracuseStep 2386759 = 3580139) B3580139
theorem B3182345 : Blo 2121435 3182345 := bstep (se 2 (by rfl) ⟨1193379, by rfl⟩ : syracuseStep 3182345 = 2386759) B2386759
theorem B2121563 : Blo 2121435 2121563 := bstep (se 1 (by rfl) ⟨1591172, by rfl⟩ : syracuseStep 2121563 = 3182345) B3182345
theorem B10740437 : Blo 2121435 10740437 := bbase (se 7 (by rfl) ⟨125864, by rfl⟩ : syracuseStep 10740437 = 251729) (by norm_num)
theorem B7160291 : Blo 2121435 7160291 := bstep (se 1 (by rfl) ⟨5370218, by rfl⟩ : syracuseStep 7160291 = 10740437) B10740437
theorem B4773527 : Blo 2121435 4773527 := bstep (se 1 (by rfl) ⟨3580145, by rfl⟩ : syracuseStep 4773527 = 7160291) B7160291
theorem B3182351 : Blo 2121435 3182351 := bstep (se 1 (by rfl) ⟨2386763, by rfl⟩ : syracuseStep 3182351 = 4773527) B4773527
theorem B2121567 : Blo 2121435 2121567 := bstep (se 1 (by rfl) ⟨1591175, by rfl⟩ : syracuseStep 2121567 = 3182351) B3182351
theorem B3182357 : Blo 2121435 3182357 := bbase (se 6 (by rfl) ⟨74586, by rfl⟩ : syracuseStep 3182357 = 149173) (by norm_num)
theorem B2121571 : Blo 2121435 2121571 := bstep (se 1 (by rfl) ⟨1591178, by rfl⟩ : syracuseStep 2121571 = 3182357) B3182357
theorem B61170389 : Blo 2121435 61170389 := bbase (se 7 (by rfl) ⟨716840, by rfl⟩ : syracuseStep 61170389 = 1433681) (by norm_num)
theorem B40780259 : Blo 2121435 40780259 := bstep (se 1 (by rfl) ⟨30585194, by rfl⟩ : syracuseStep 40780259 = 61170389) B61170389
theorem B27186839 : Blo 2121435 27186839 := bstep (se 1 (by rfl) ⟨20390129, by rfl⟩ : syracuseStep 27186839 = 40780259) B40780259
theorem B18124559 : Blo 2121435 18124559 := bstep (se 1 (by rfl) ⟨13593419, by rfl⟩ : syracuseStep 18124559 = 27186839) B27186839
theorem B12083039 : Blo 2121435 12083039 := bstep (se 1 (by rfl) ⟨9062279, by rfl⟩ : syracuseStep 12083039 = 18124559) B18124559
theorem B8055359 : Blo 2121435 8055359 := bstep (se 1 (by rfl) ⟨6041519, by rfl⟩ : syracuseStep 8055359 = 12083039) B12083039
theorem B5370239 : Blo 2121435 5370239 := bstep (se 1 (by rfl) ⟨4027679, by rfl⟩ : syracuseStep 5370239 = 8055359) B8055359
theorem B3580159 : Blo 2121435 3580159 := bstep (se 1 (by rfl) ⟨2685119, by rfl⟩ : syracuseStep 3580159 = 5370239) B5370239
theorem B4773545 : Blo 2121435 4773545 := bstep (se 2 (by rfl) ⟨1790079, by rfl⟩ : syracuseStep 4773545 = 3580159) B3580159
theorem B3182363 : Blo 2121435 3182363 := bstep (se 1 (by rfl) ⟨2386772, by rfl⟩ : syracuseStep 3182363 = 4773545) B4773545
theorem B2121575 : Blo 2121435 2121575 := bstep (se 1 (by rfl) ⟨1591181, by rfl⟩ : syracuseStep 2121575 = 3182363) B3182363
theorem B2386777 : Blo 2121435 2386777 := bbase (se 2 (by rfl) ⟨895041, by rfl⟩ : syracuseStep 2386777 = 1790083) (by norm_num)
theorem B3182369 : Blo 2121435 3182369 := bstep (se 2 (by rfl) ⟨1193388, by rfl⟩ : syracuseStep 3182369 = 2386777) B2386777
theorem B2121579 : Blo 2121435 2121579 := bstep (se 1 (by rfl) ⟨1591184, by rfl⟩ : syracuseStep 2121579 = 3182369) B3182369
theorem B4531157 : Blo 2121435 4531157 := bbase (se 7 (by rfl) ⟨53099, by rfl⟩ : syracuseStep 4531157 = 106199) (by norm_num)
theorem B3020771 : Blo 2121435 3020771 := bstep (se 1 (by rfl) ⟨2265578, by rfl⟩ : syracuseStep 3020771 = 4531157) B4531157
theorem B8055389 : Blo 2121435 8055389 := bstep (se 3 (by rfl) ⟨1510385, by rfl⟩ : syracuseStep 8055389 = 3020771) B3020771
theorem B5370259 : Blo 2121435 5370259 := bstep (se 1 (by rfl) ⟨4027694, by rfl⟩ : syracuseStep 5370259 = 8055389) B8055389
theorem B7160345 : Blo 2121435 7160345 := bstep (se 2 (by rfl) ⟨2685129, by rfl⟩ : syracuseStep 7160345 = 5370259) B5370259
theorem B4773563 : Blo 2121435 4773563 := bstep (se 1 (by rfl) ⟨3580172, by rfl⟩ : syracuseStep 4773563 = 7160345) B7160345
theorem B3182375 : Blo 2121435 3182375 := bstep (se 1 (by rfl) ⟨2386781, by rfl⟩ : syracuseStep 3182375 = 4773563) B4773563
theorem B2121583 : Blo 2121435 2121583 := bstep (se 1 (by rfl) ⟨1591187, by rfl⟩ : syracuseStep 2121583 = 3182375) B3182375
theorem B3182381 : Blo 2121435 3182381 := bbase (se 3 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 3182381 = 1193393) (by norm_num)
theorem B2121587 : Blo 2121435 2121587 := bstep (se 1 (by rfl) ⟨1591190, by rfl⟩ : syracuseStep 2121587 = 3182381) B3182381
theorem B4773581 : Blo 2121435 4773581 := bbase (se 3 (by rfl) ⟨895046, by rfl⟩ : syracuseStep 4773581 = 1790093) (by norm_num)
theorem B3182387 : Blo 2121435 3182387 := bstep (se 1 (by rfl) ⟨2386790, by rfl⟩ : syracuseStep 3182387 = 4773581) B4773581
theorem B2121591 : Blo 2121435 2121591 := bstep (se 1 (by rfl) ⟨1591193, by rfl⟩ : syracuseStep 2121591 = 3182387) B3182387
theorem B2685145 : Blo 2121435 2685145 := bbase (se 2 (by rfl) ⟨1006929, by rfl⟩ : syracuseStep 2685145 = 2013859) (by norm_num)
theorem B3580193 : Blo 2121435 3580193 := bstep (se 2 (by rfl) ⟨1342572, by rfl⟩ : syracuseStep 3580193 = 2685145) B2685145
theorem B2386795 : Blo 2121435 2386795 := bstep (se 1 (by rfl) ⟨1790096, by rfl⟩ : syracuseStep 2386795 = 3580193) B3580193
theorem B3182393 : Blo 2121435 3182393 := bstep (se 2 (by rfl) ⟨1193397, by rfl⟩ : syracuseStep 3182393 = 2386795) B2386795
theorem B2121595 : Blo 2121435 2121595 := bstep (se 1 (by rfl) ⟨1591196, by rfl⟩ : syracuseStep 2121595 = 3182393) B3182393
theorem B4301093 : Blo 2121435 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B2867395 : Blo 2121435 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B3823193 : Blo 2121435 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B2548795 : Blo 2121435 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B3398393 : Blo 2121435 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B9062381 : Blo 2121435 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B24166349 : Blo 2121435 24166349 := bstep (se 3 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 24166349 = 9062381) B9062381
theorem B16110899 : Blo 2121435 16110899 := bstep (se 1 (by rfl) ⟨12083174, by rfl⟩ : syracuseStep 16110899 = 24166349) B24166349
theorem B10740599 : Blo 2121435 10740599 := bstep (se 1 (by rfl) ⟨8055449, by rfl⟩ : syracuseStep 10740599 = 16110899) B16110899
theorem B7160399 : Blo 2121435 7160399 := bstep (se 1 (by rfl) ⟨5370299, by rfl⟩ : syracuseStep 7160399 = 10740599) B10740599
theorem B4773599 : Blo 2121435 4773599 := bstep (se 1 (by rfl) ⟨3580199, by rfl⟩ : syracuseStep 4773599 = 7160399) B7160399
theorem B3182399 : Blo 2121435 3182399 := bstep (se 1 (by rfl) ⟨2386799, by rfl⟩ : syracuseStep 3182399 = 4773599) B4773599
theorem B2121599 : Blo 2121435 2121599 := bstep (se 1 (by rfl) ⟨1591199, by rfl⟩ : syracuseStep 2121599 = 3182399) B3182399
theorem B3182405 : Blo 2121435 3182405 := bbase (se 4 (by rfl) ⟨298350, by rfl⟩ : syracuseStep 3182405 = 596701) (by norm_num)
theorem B2121603 : Blo 2121435 2121603 := bstep (se 1 (by rfl) ⟨1591202, by rfl⟩ : syracuseStep 2121603 = 3182405) B3182405
theorem B3580213 : Blo 2121435 3580213 := bbase (se 5 (by rfl) ⟨167822, by rfl⟩ : syracuseStep 3580213 = 335645) (by norm_num)
theorem B4773617 : Blo 2121435 4773617 := bstep (se 2 (by rfl) ⟨1790106, by rfl⟩ : syracuseStep 4773617 = 3580213) B3580213
theorem B3182411 : Blo 2121435 3182411 := bstep (se 1 (by rfl) ⟨2386808, by rfl⟩ : syracuseStep 3182411 = 4773617) B4773617
theorem B2121607 : Blo 2121435 2121607 := bstep (se 1 (by rfl) ⟨1591205, by rfl⟩ : syracuseStep 2121607 = 3182411) B3182411
theorem B2386813 : Blo 2121435 2386813 := bbase (se 3 (by rfl) ⟨447527, by rfl⟩ : syracuseStep 2386813 = 895055) (by norm_num)
theorem B3182417 : Blo 2121435 3182417 := bstep (se 2 (by rfl) ⟨1193406, by rfl⟩ : syracuseStep 3182417 = 2386813) B2386813
theorem B2121611 : Blo 2121435 2121611 := bstep (se 1 (by rfl) ⟨1591208, by rfl⟩ : syracuseStep 2121611 = 3182417) B3182417
theorem B7160453 : Blo 2121435 7160453 := bbase (se 4 (by rfl) ⟨671292, by rfl⟩ : syracuseStep 7160453 = 1342585) (by norm_num)
theorem B4773635 : Blo 2121435 4773635 := bstep (se 1 (by rfl) ⟨3580226, by rfl⟩ : syracuseStep 4773635 = 7160453) B7160453
theorem B3182423 : Blo 2121435 3182423 := bstep (se 1 (by rfl) ⟨2386817, by rfl⟩ : syracuseStep 3182423 = 4773635) B4773635
theorem B2121615 : Blo 2121435 2121615 := bstep (se 1 (by rfl) ⟨1591211, by rfl⟩ : syracuseStep 2121615 = 3182423) B3182423
theorem B3182429 : Blo 2121435 3182429 := bbase (se 3 (by rfl) ⟨596705, by rfl⟩ : syracuseStep 3182429 = 1193411) (by norm_num)
theorem B2121619 : Blo 2121435 2121619 := bstep (se 1 (by rfl) ⟨1591214, by rfl⟩ : syracuseStep 2121619 = 3182429) B3182429
theorem B4773653 : Blo 2121435 4773653 := bbase (se 6 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 4773653 = 223765) (by norm_num)
theorem B3182435 : Blo 2121435 3182435 := bstep (se 1 (by rfl) ⟨2386826, by rfl⟩ : syracuseStep 3182435 = 4773653) B4773653
theorem B2121623 : Blo 2121435 2121623 := bstep (se 1 (by rfl) ⟨1591217, by rfl⟩ : syracuseStep 2121623 = 3182435) B3182435
theorem B8055557 : Blo 2121435 8055557 := bbase (se 4 (by rfl) ⟨755208, by rfl⟩ : syracuseStep 8055557 = 1510417) (by norm_num)
theorem B5370371 : Blo 2121435 5370371 := bstep (se 1 (by rfl) ⟨4027778, by rfl⟩ : syracuseStep 5370371 = 8055557) B8055557
theorem B3580247 : Blo 2121435 3580247 := bstep (se 1 (by rfl) ⟨2685185, by rfl⟩ : syracuseStep 3580247 = 5370371) B5370371
theorem B2386831 : Blo 2121435 2386831 := bstep (se 1 (by rfl) ⟨1790123, by rfl⟩ : syracuseStep 2386831 = 3580247) B3580247
theorem B3182441 : Blo 2121435 3182441 := bstep (se 2 (by rfl) ⟨1193415, by rfl⟩ : syracuseStep 3182441 = 2386831) B2386831
theorem B2121627 : Blo 2121435 2121627 := bstep (se 1 (by rfl) ⟨1591220, by rfl⟩ : syracuseStep 2121627 = 3182441) B3182441
theorem B7646501 : Blo 2121435 7646501 := bbase (se 4 (by rfl) ⟨716859, by rfl⟩ : syracuseStep 7646501 = 1433719) (by norm_num)
theorem B5097667 : Blo 2121435 5097667 := bstep (se 1 (by rfl) ⟨3823250, by rfl⟩ : syracuseStep 5097667 = 7646501) B7646501
theorem B6796889 : Blo 2121435 6796889 := bstep (se 2 (by rfl) ⟨2548833, by rfl⟩ : syracuseStep 6796889 = 5097667) B5097667
theorem B4531259 : Blo 2121435 4531259 := bstep (se 1 (by rfl) ⟨3398444, by rfl⟩ : syracuseStep 4531259 = 6796889) B6796889
theorem B12083357 : Blo 2121435 12083357 := bstep (se 3 (by rfl) ⟨2265629, by rfl⟩ : syracuseStep 12083357 = 4531259) B4531259
theorem B8055571 : Blo 2121435 8055571 := bstep (se 1 (by rfl) ⟨6041678, by rfl⟩ : syracuseStep 8055571 = 12083357) B12083357
theorem B10740761 : Blo 2121435 10740761 := bstep (se 2 (by rfl) ⟨4027785, by rfl⟩ : syracuseStep 10740761 = 8055571) B8055571
theorem B7160507 : Blo 2121435 7160507 := bstep (se 1 (by rfl) ⟨5370380, by rfl⟩ : syracuseStep 7160507 = 10740761) B10740761
theorem B4773671 : Blo 2121435 4773671 := bstep (se 1 (by rfl) ⟨3580253, by rfl⟩ : syracuseStep 4773671 = 7160507) B7160507
theorem B3182447 : Blo 2121435 3182447 := bstep (se 1 (by rfl) ⟨2386835, by rfl⟩ : syracuseStep 3182447 = 4773671) B4773671
theorem B2121631 : Blo 2121435 2121631 := bstep (se 1 (by rfl) ⟨1591223, by rfl⟩ : syracuseStep 2121631 = 3182447) B3182447
theorem B3182453 : Blo 2121435 3182453 := bbase (se 5 (by rfl) ⟨149177, by rfl⟩ : syracuseStep 3182453 = 298355) (by norm_num)
theorem B2121635 : Blo 2121435 2121635 := bstep (se 1 (by rfl) ⟨1591226, by rfl⟩ : syracuseStep 2121635 = 3182453) B3182453
theorem B4531277 : Blo 2121435 4531277 := bbase (se 3 (by rfl) ⟨849614, by rfl⟩ : syracuseStep 4531277 = 1699229) (by norm_num)
theorem B3020851 : Blo 2121435 3020851 := bstep (se 1 (by rfl) ⟨2265638, by rfl⟩ : syracuseStep 3020851 = 4531277) B4531277
theorem B4027801 : Blo 2121435 4027801 := bstep (se 2 (by rfl) ⟨1510425, by rfl⟩ : syracuseStep 4027801 = 3020851) B3020851
theorem B5370401 : Blo 2121435 5370401 := bstep (se 2 (by rfl) ⟨2013900, by rfl⟩ : syracuseStep 5370401 = 4027801) B4027801
theorem B3580267 : Blo 2121435 3580267 := bstep (se 1 (by rfl) ⟨2685200, by rfl⟩ : syracuseStep 3580267 = 5370401) B5370401
theorem B4773689 : Blo 2121435 4773689 := bstep (se 2 (by rfl) ⟨1790133, by rfl⟩ : syracuseStep 4773689 = 3580267) B3580267
theorem B3182459 : Blo 2121435 3182459 := bstep (se 1 (by rfl) ⟨2386844, by rfl⟩ : syracuseStep 3182459 = 4773689) B4773689
theorem B2121639 : Blo 2121435 2121639 := bstep (se 1 (by rfl) ⟨1591229, by rfl⟩ : syracuseStep 2121639 = 3182459) B3182459
theorem B2386849 : Blo 2121435 2386849 := bbase (se 2 (by rfl) ⟨895068, by rfl⟩ : syracuseStep 2386849 = 1790137) (by norm_num)
theorem B3182465 : Blo 2121435 3182465 := bstep (se 2 (by rfl) ⟨1193424, by rfl⟩ : syracuseStep 3182465 = 2386849) B2386849
theorem B2121643 : Blo 2121435 2121643 := bstep (se 1 (by rfl) ⟨1591232, by rfl⟩ : syracuseStep 2121643 = 3182465) B3182465
theorem B5370421 : Blo 2121435 5370421 := bbase (se 5 (by rfl) ⟨251738, by rfl⟩ : syracuseStep 5370421 = 503477) (by norm_num)
theorem B7160561 : Blo 2121435 7160561 := bstep (se 2 (by rfl) ⟨2685210, by rfl⟩ : syracuseStep 7160561 = 5370421) B5370421
theorem B4773707 : Blo 2121435 4773707 := bstep (se 1 (by rfl) ⟨3580280, by rfl⟩ : syracuseStep 4773707 = 7160561) B7160561
theorem B3182471 : Blo 2121435 3182471 := bstep (se 1 (by rfl) ⟨2386853, by rfl⟩ : syracuseStep 3182471 = 4773707) B4773707
theorem B2121647 : Blo 2121435 2121647 := bstep (se 1 (by rfl) ⟨1591235, by rfl⟩ : syracuseStep 2121647 = 3182471) B3182471
theorem B3182477 : Blo 2121435 3182477 := bbase (se 3 (by rfl) ⟨596714, by rfl⟩ : syracuseStep 3182477 = 1193429) (by norm_num)
theorem B2121651 : Blo 2121435 2121651 := bstep (se 1 (by rfl) ⟨1591238, by rfl⟩ : syracuseStep 2121651 = 3182477) B3182477
theorem B4773725 : Blo 2121435 4773725 := bbase (se 3 (by rfl) ⟨895073, by rfl⟩ : syracuseStep 4773725 = 1790147) (by norm_num)
theorem B3182483 : Blo 2121435 3182483 := bstep (se 1 (by rfl) ⟨2386862, by rfl⟩ : syracuseStep 3182483 = 4773725) B4773725
theorem B2121655 : Blo 2121435 2121655 := bstep (se 1 (by rfl) ⟨1591241, by rfl⟩ : syracuseStep 2121655 = 3182483) B3182483
theorem B3580301 : Blo 2121435 3580301 := bbase (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) (by norm_num)
theorem B2386867 : Blo 2121435 2386867 := bstep (se 1 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 2386867 = 3580301) B3580301
theorem B3182489 : Blo 2121435 3182489 := bstep (se 2 (by rfl) ⟨1193433, by rfl⟩ : syracuseStep 3182489 = 2386867) B2386867
theorem B2121659 : Blo 2121435 2121659 := bstep (se 1 (by rfl) ⟨1591244, by rfl⟩ : syracuseStep 2121659 = 3182489) B3182489
theorem B5237797 : Blo 2121435 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B6983729 : Blo 2121435 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B4655819 : Blo 2121435 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3103879 : Blo 2121435 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B4138505 : Blo 2121435 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B2759003 : Blo 2121435 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B29429365 : Blo 2121435 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B39239153 : Blo 2121435 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B26159435 : Blo 2121435 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B17439623 : Blo 2121435 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B11626415 : Blo 2121435 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B7750943 : Blo 2121435 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B5167295 : Blo 2121435 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B3444863 : Blo 2121435 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B9186301 : Blo 2121435 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B12248401 : Blo 2121435 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B16331201 : Blo 2121435 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B10887467 : Blo 2121435 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B29033245 : Blo 2121435 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B38710993 : Blo 2121435 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B51614657 : Blo 2121435 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B34409771 : Blo 2121435 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B22939847 : Blo 2121435 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B15293231 : Blo 2121435 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B10195487 : Blo 2121435 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B6796991 : Blo 2121435 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B18125309 : Blo 2121435 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B12083539 : Blo 2121435 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B16111385 : Blo 2121435 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B10740923 : Blo 2121435 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B7160615 : Blo 2121435 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B4773743 : Blo 2121435 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B3182495 : Blo 2121435 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B2121663 : Blo 2121435 2121663 := bstep (se 1 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 2121663 = 3182495) B3182495
theorem B3182501 : Blo 2121435 3182501 := bbase (se 4 (by rfl) ⟨298359, by rfl⟩ : syracuseStep 3182501 = 596719) (by norm_num)
theorem B2121667 : Blo 2121435 2121667 := bstep (se 1 (by rfl) ⟨1591250, by rfl⟩ : syracuseStep 2121667 = 3182501) B3182501
theorem B2685241 : Blo 2121435 2685241 := bbase (se 2 (by rfl) ⟨1006965, by rfl⟩ : syracuseStep 2685241 = 2013931) (by norm_num)
theorem B3580321 : Blo 2121435 3580321 := bstep (se 2 (by rfl) ⟨1342620, by rfl⟩ : syracuseStep 3580321 = 2685241) B2685241
theorem B4773761 : Blo 2121435 4773761 := bstep (se 2 (by rfl) ⟨1790160, by rfl⟩ : syracuseStep 4773761 = 3580321) B3580321
theorem B3182507 : Blo 2121435 3182507 := bstep (se 1 (by rfl) ⟨2386880, by rfl⟩ : syracuseStep 3182507 = 4773761) B4773761
theorem B2121671 : Blo 2121435 2121671 := bstep (se 1 (by rfl) ⟨1591253, by rfl⟩ : syracuseStep 2121671 = 3182507) B3182507
theorem B2386885 : Blo 2121435 2386885 := bbase (se 4 (by rfl) ⟨223770, by rfl⟩ : syracuseStep 2386885 = 447541) (by norm_num)
theorem B3182513 : Blo 2121435 3182513 := bstep (se 2 (by rfl) ⟨1193442, by rfl⟩ : syracuseStep 3182513 = 2386885) B2386885
theorem B2121675 : Blo 2121435 2121675 := bstep (se 1 (by rfl) ⟨1591256, by rfl⟩ : syracuseStep 2121675 = 3182513) B3182513
theorem B4027877 : Blo 2121435 4027877 := bbase (se 4 (by rfl) ⟨377613, by rfl⟩ : syracuseStep 4027877 = 755227) (by norm_num)
theorem B2685251 : Blo 2121435 2685251 := bstep (se 1 (by rfl) ⟨2013938, by rfl⟩ : syracuseStep 2685251 = 4027877) B4027877
theorem B7160669 : Blo 2121435 7160669 := bstep (se 3 (by rfl) ⟨1342625, by rfl⟩ : syracuseStep 7160669 = 2685251) B2685251
theorem B4773779 : Blo 2121435 4773779 := bstep (se 1 (by rfl) ⟨3580334, by rfl⟩ : syracuseStep 4773779 = 7160669) B7160669
theorem B3182519 : Blo 2121435 3182519 := bstep (se 1 (by rfl) ⟨2386889, by rfl⟩ : syracuseStep 3182519 = 4773779) B4773779
theorem B2121679 : Blo 2121435 2121679 := bstep (se 1 (by rfl) ⟨1591259, by rfl⟩ : syracuseStep 2121679 = 3182519) B3182519
theorem B3182525 : Blo 2121435 3182525 := bbase (se 3 (by rfl) ⟨596723, by rfl⟩ : syracuseStep 3182525 = 1193447) (by norm_num)
theorem B2121683 : Blo 2121435 2121683 := bstep (se 1 (by rfl) ⟨1591262, by rfl⟩ : syracuseStep 2121683 = 3182525) B3182525
theorem B4773797 : Blo 2121435 4773797 := bbase (se 4 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 4773797 = 895087) (by norm_num)
theorem B3182531 : Blo 2121435 3182531 := bstep (se 1 (by rfl) ⟨2386898, by rfl⟩ : syracuseStep 3182531 = 4773797) B4773797
theorem B2121687 : Blo 2121435 2121687 := bstep (se 1 (by rfl) ⟨1591265, by rfl⟩ : syracuseStep 2121687 = 3182531) B3182531
theorem B5370533 : Blo 2121435 5370533 := bbase (se 4 (by rfl) ⟨503487, by rfl⟩ : syracuseStep 5370533 = 1006975) (by norm_num)
theorem B3580355 : Blo 2121435 3580355 := bstep (se 1 (by rfl) ⟨2685266, by rfl⟩ : syracuseStep 3580355 = 5370533) B5370533
theorem B2386903 : Blo 2121435 2386903 := bstep (se 1 (by rfl) ⟨1790177, by rfl⟩ : syracuseStep 2386903 = 3580355) B3580355
theorem B3182537 : Blo 2121435 3182537 := bstep (se 2 (by rfl) ⟨1193451, by rfl⟩ : syracuseStep 3182537 = 2386903) B2386903
theorem B2121691 : Blo 2121435 2121691 := bstep (se 1 (by rfl) ⟨1591268, by rfl⟩ : syracuseStep 2121691 = 3182537) B3182537
theorem B6041861 : Blo 2121435 6041861 := bbase (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) (by norm_num)
theorem B4027907 : Blo 2121435 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B10741085 : Blo 2121435 10741085 := bstep (se 3 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 10741085 = 4027907) B4027907
theorem B7160723 : Blo 2121435 7160723 := bstep (se 1 (by rfl) ⟨5370542, by rfl⟩ : syracuseStep 7160723 = 10741085) B10741085
theorem B4773815 : Blo 2121435 4773815 := bstep (se 1 (by rfl) ⟨3580361, by rfl⟩ : syracuseStep 4773815 = 7160723) B7160723
theorem B3182543 : Blo 2121435 3182543 := bstep (se 1 (by rfl) ⟨2386907, by rfl⟩ : syracuseStep 3182543 = 4773815) B4773815
theorem B2121695 : Blo 2121435 2121695 := bstep (se 1 (by rfl) ⟨1591271, by rfl⟩ : syracuseStep 2121695 = 3182543) B3182543
theorem B3182549 : Blo 2121435 3182549 := bbase (se 7 (by rfl) ⟨37295, by rfl⟩ : syracuseStep 3182549 = 74591) (by norm_num)
theorem B2121699 : Blo 2121435 2121699 := bstep (se 1 (by rfl) ⟨1591274, by rfl⟩ : syracuseStep 2121699 = 3182549) B3182549
theorem B8055845 : Blo 2121435 8055845 := bbase (se 4 (by rfl) ⟨755235, by rfl⟩ : syracuseStep 8055845 = 1510471) (by norm_num)
theorem B5370563 : Blo 2121435 5370563 := bstep (se 1 (by rfl) ⟨4027922, by rfl⟩ : syracuseStep 5370563 = 8055845) B8055845
theorem B3580375 : Blo 2121435 3580375 := bstep (se 1 (by rfl) ⟨2685281, by rfl⟩ : syracuseStep 3580375 = 5370563) B5370563
theorem B4773833 : Blo 2121435 4773833 := bstep (se 2 (by rfl) ⟨1790187, by rfl⟩ : syracuseStep 4773833 = 3580375) B3580375
theorem B3182555 : Blo 2121435 3182555 := bstep (se 1 (by rfl) ⟨2386916, by rfl⟩ : syracuseStep 3182555 = 4773833) B4773833
theorem B2121703 : Blo 2121435 2121703 := bstep (se 1 (by rfl) ⟨1591277, by rfl⟩ : syracuseStep 2121703 = 3182555) B3182555
theorem B2386921 : Blo 2121435 2386921 := bbase (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) (by norm_num)
theorem B3182561 : Blo 2121435 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B2121707 : Blo 2121435 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B3398573 : Blo 2121435 3398573 := bbase (se 3 (by rfl) ⟨637232, by rfl⟩ : syracuseStep 3398573 = 1274465) (by norm_num)
theorem B2265715 : Blo 2121435 2265715 := bstep (se 1 (by rfl) ⟨1699286, by rfl⟩ : syracuseStep 2265715 = 3398573) B3398573
theorem B12083813 : Blo 2121435 12083813 := bstep (se 4 (by rfl) ⟨1132857, by rfl⟩ : syracuseStep 12083813 = 2265715) B2265715
theorem B8055875 : Blo 2121435 8055875 := bstep (se 1 (by rfl) ⟨6041906, by rfl⟩ : syracuseStep 8055875 = 12083813) B12083813
theorem B5370583 : Blo 2121435 5370583 := bstep (se 1 (by rfl) ⟨4027937, by rfl⟩ : syracuseStep 5370583 = 8055875) B8055875
theorem B7160777 : Blo 2121435 7160777 := bstep (se 2 (by rfl) ⟨2685291, by rfl⟩ : syracuseStep 7160777 = 5370583) B5370583
theorem B4773851 : Blo 2121435 4773851 := bstep (se 1 (by rfl) ⟨3580388, by rfl⟩ : syracuseStep 4773851 = 7160777) B7160777
theorem B3182567 : Blo 2121435 3182567 := bstep (se 1 (by rfl) ⟨2386925, by rfl⟩ : syracuseStep 3182567 = 4773851) B4773851
theorem B2121711 : Blo 2121435 2121711 := bstep (se 1 (by rfl) ⟨1591283, by rfl⟩ : syracuseStep 2121711 = 3182567) B3182567
theorem B3182573 : Blo 2121435 3182573 := bbase (se 3 (by rfl) ⟨596732, by rfl⟩ : syracuseStep 3182573 = 1193465) (by norm_num)
theorem B2121715 : Blo 2121435 2121715 := bstep (se 1 (by rfl) ⟨1591286, by rfl⟩ : syracuseStep 2121715 = 3182573) B3182573
theorem B4773869 : Blo 2121435 4773869 := bbase (se 3 (by rfl) ⟨895100, by rfl⟩ : syracuseStep 4773869 = 1790201) (by norm_num)
theorem B3182579 : Blo 2121435 3182579 := bstep (se 1 (by rfl) ⟨2386934, by rfl⟩ : syracuseStep 3182579 = 4773869) B4773869
theorem B2121719 : Blo 2121435 2121719 := bstep (se 1 (by rfl) ⟨1591289, by rfl⟩ : syracuseStep 2121719 = 3182579) B3182579
theorem B2548945 : Blo 2121435 2548945 := bbase (se 2 (by rfl) ⟨955854, by rfl⟩ : syracuseStep 2548945 = 1911709) (by norm_num)
theorem B3398593 : Blo 2121435 3398593 := bstep (se 2 (by rfl) ⟨1274472, by rfl⟩ : syracuseStep 3398593 = 2548945) B2548945
theorem B4531457 : Blo 2121435 4531457 := bstep (se 2 (by rfl) ⟨1699296, by rfl⟩ : syracuseStep 4531457 = 3398593) B3398593
theorem B3020971 : Blo 2121435 3020971 := bstep (se 1 (by rfl) ⟨2265728, by rfl⟩ : syracuseStep 3020971 = 4531457) B4531457
theorem B4027961 : Blo 2121435 4027961 := bstep (se 2 (by rfl) ⟨1510485, by rfl⟩ : syracuseStep 4027961 = 3020971) B3020971
theorem B2685307 : Blo 2121435 2685307 := bstep (se 1 (by rfl) ⟨2013980, by rfl⟩ : syracuseStep 2685307 = 4027961) B4027961
theorem B3580409 : Blo 2121435 3580409 := bstep (se 2 (by rfl) ⟨1342653, by rfl⟩ : syracuseStep 3580409 = 2685307) B2685307
theorem B2386939 : Blo 2121435 2386939 := bstep (se 1 (by rfl) ⟨1790204, by rfl⟩ : syracuseStep 2386939 = 3580409) B3580409
theorem B3182585 : Blo 2121435 3182585 := bstep (se 2 (by rfl) ⟨1193469, by rfl⟩ : syracuseStep 3182585 = 2386939) B2386939
theorem B2121723 : Blo 2121435 2121723 := bstep (se 1 (by rfl) ⟨1591292, by rfl⟩ : syracuseStep 2121723 = 3182585) B3182585
theorem B6540053 : Blo 2121435 6540053 := bbase (se 6 (by rfl) ⟨153282, by rfl⟩ : syracuseStep 6540053 = 306565) (by norm_num)
theorem B69760565 : Blo 2121435 69760565 := bstep (se 5 (by rfl) ⟨3270026, by rfl⟩ : syracuseStep 69760565 = 6540053) B6540053
theorem B46507043 : Blo 2121435 46507043 := bstep (se 1 (by rfl) ⟨34880282, by rfl⟩ : syracuseStep 46507043 = 69760565) B69760565
theorem B31004695 : Blo 2121435 31004695 := bstep (se 1 (by rfl) ⟨23253521, by rfl⟩ : syracuseStep 31004695 = 46507043) B46507043
theorem B41339593 : Blo 2121435 41339593 := bstep (se 2 (by rfl) ⟨15502347, by rfl⟩ : syracuseStep 41339593 = 31004695) B31004695
theorem B55119457 : Blo 2121435 55119457 := bstep (se 2 (by rfl) ⟨20669796, by rfl⟩ : syracuseStep 55119457 = 41339593) B41339593
theorem B73492609 : Blo 2121435 73492609 := bstep (se 2 (by rfl) ⟨27559728, by rfl⟩ : syracuseStep 73492609 = 55119457) B55119457
theorem B97990145 : Blo 2121435 97990145 := bstep (se 2 (by rfl) ⟨36746304, by rfl⟩ : syracuseStep 97990145 = 73492609) B73492609
theorem B65326763 : Blo 2121435 65326763 := bstep (se 1 (by rfl) ⟨48995072, by rfl⟩ : syracuseStep 65326763 = 97990145) B97990145
theorem B174204701 : Blo 2121435 174204701 := bstep (se 3 (by rfl) ⟨32663381, by rfl⟩ : syracuseStep 174204701 = 65326763) B65326763
theorem B116136467 : Blo 2121435 116136467 := bstep (se 1 (by rfl) ⟨87102350, by rfl⟩ : syracuseStep 116136467 = 174204701) B174204701
theorem B77424311 : Blo 2121435 77424311 := bstep (se 1 (by rfl) ⟨58068233, by rfl⟩ : syracuseStep 77424311 = 116136467) B116136467
theorem B51616207 : Blo 2121435 51616207 := bstep (se 1 (by rfl) ⟨38712155, by rfl⟩ : syracuseStep 51616207 = 77424311) B77424311
theorem B275286437 : Blo 2121435 275286437 := bstep (se 4 (by rfl) ⟨25808103, by rfl⟩ : syracuseStep 275286437 = 51616207) B51616207
theorem B183524291 : Blo 2121435 183524291 := bstep (se 1 (by rfl) ⟨137643218, by rfl⟩ : syracuseStep 183524291 = 275286437) B275286437
theorem B122349527 : Blo 2121435 122349527 := bstep (se 1 (by rfl) ⟨91762145, by rfl⟩ : syracuseStep 122349527 = 183524291) B183524291
theorem B81566351 : Blo 2121435 81566351 := bstep (se 1 (by rfl) ⟨61174763, by rfl⟩ : syracuseStep 81566351 = 122349527) B122349527
theorem B54377567 : Blo 2121435 54377567 := bstep (se 1 (by rfl) ⟨40783175, by rfl⟩ : syracuseStep 54377567 = 81566351) B81566351
theorem B36251711 : Blo 2121435 36251711 := bstep (se 1 (by rfl) ⟨27188783, by rfl⟩ : syracuseStep 36251711 = 54377567) B54377567
theorem B24167807 : Blo 2121435 24167807 := bstep (se 1 (by rfl) ⟨18125855, by rfl⟩ : syracuseStep 24167807 = 36251711) B36251711
theorem B16111871 : Blo 2121435 16111871 := bstep (se 1 (by rfl) ⟨12083903, by rfl⟩ : syracuseStep 16111871 = 24167807) B24167807
theorem B10741247 : Blo 2121435 10741247 := bstep (se 1 (by rfl) ⟨8055935, by rfl⟩ : syracuseStep 10741247 = 16111871) B16111871
theorem B7160831 : Blo 2121435 7160831 := bstep (se 1 (by rfl) ⟨5370623, by rfl⟩ : syracuseStep 7160831 = 10741247) B10741247
theorem B4773887 : Blo 2121435 4773887 := bstep (se 1 (by rfl) ⟨3580415, by rfl⟩ : syracuseStep 4773887 = 7160831) B7160831
theorem B3182591 : Blo 2121435 3182591 := bstep (se 1 (by rfl) ⟨2386943, by rfl⟩ : syracuseStep 3182591 = 4773887) B4773887
theorem B2121727 : Blo 2121435 2121727 := bstep (se 1 (by rfl) ⟨1591295, by rfl⟩ : syracuseStep 2121727 = 3182591) B3182591
theorem B3182597 : Blo 2121435 3182597 := bbase (se 4 (by rfl) ⟨298368, by rfl⟩ : syracuseStep 3182597 = 596737) (by norm_num)
theorem B2121731 : Blo 2121435 2121731 := bstep (se 1 (by rfl) ⟨1591298, by rfl⟩ : syracuseStep 2121731 = 3182597) B3182597
theorem B3580429 : Blo 2121435 3580429 := bbase (se 3 (by rfl) ⟨671330, by rfl⟩ : syracuseStep 3580429 = 1342661) (by norm_num)
theorem B4773905 : Blo 2121435 4773905 := bstep (se 2 (by rfl) ⟨1790214, by rfl⟩ : syracuseStep 4773905 = 3580429) B3580429
theorem B3182603 : Blo 2121435 3182603 := bstep (se 1 (by rfl) ⟨2386952, by rfl⟩ : syracuseStep 3182603 = 4773905) B4773905
theorem B2121735 : Blo 2121435 2121735 := bstep (se 1 (by rfl) ⟨1591301, by rfl⟩ : syracuseStep 2121735 = 3182603) B3182603
theorem B2386957 : Blo 2121435 2386957 := bbase (se 3 (by rfl) ⟨447554, by rfl⟩ : syracuseStep 2386957 = 895109) (by norm_num)
theorem B3182609 : Blo 2121435 3182609 := bstep (se 2 (by rfl) ⟨1193478, by rfl⟩ : syracuseStep 3182609 = 2386957) B2386957
theorem B2121739 : Blo 2121435 2121739 := bstep (se 1 (by rfl) ⟨1591304, by rfl⟩ : syracuseStep 2121739 = 3182609) B3182609
theorem B7160885 : Blo 2121435 7160885 := bbase (se 5 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 7160885 = 671333) (by norm_num)
theorem B4773923 : Blo 2121435 4773923 := bstep (se 1 (by rfl) ⟨3580442, by rfl⟩ : syracuseStep 4773923 = 7160885) B7160885
theorem B3182615 : Blo 2121435 3182615 := bstep (se 1 (by rfl) ⟨2386961, by rfl⟩ : syracuseStep 3182615 = 4773923) B4773923
theorem B2121743 : Blo 2121435 2121743 := bstep (se 1 (by rfl) ⟨1591307, by rfl⟩ : syracuseStep 2121743 = 3182615) B3182615
theorem B3182621 : Blo 2121435 3182621 := bbase (se 3 (by rfl) ⟨596741, by rfl⟩ : syracuseStep 3182621 = 1193483) (by norm_num)
theorem B2121747 : Blo 2121435 2121747 := bstep (se 1 (by rfl) ⟨1591310, by rfl⟩ : syracuseStep 2121747 = 3182621) B3182621
theorem B4773941 : Blo 2121435 4773941 := bbase (se 5 (by rfl) ⟨223778, by rfl⟩ : syracuseStep 4773941 = 447557) (by norm_num)
theorem B3182627 : Blo 2121435 3182627 := bstep (se 1 (by rfl) ⟨2386970, by rfl⟩ : syracuseStep 3182627 = 4773941) B4773941
theorem B2121751 : Blo 2121435 2121751 := bstep (se 1 (by rfl) ⟨1591313, by rfl⟩ : syracuseStep 2121751 = 3182627) B3182627
theorem B4839085 : Blo 2121435 4839085 := bbase (se 3 (by rfl) ⟨907328, by rfl⟩ : syracuseStep 4839085 = 1814657) (by norm_num)
theorem B25808453 : Blo 2121435 25808453 := bstep (se 4 (by rfl) ⟨2419542, by rfl⟩ : syracuseStep 25808453 = 4839085) B4839085
theorem B17205635 : Blo 2121435 17205635 := bstep (se 1 (by rfl) ⟨12904226, by rfl⟩ : syracuseStep 17205635 = 25808453) B25808453
theorem B11470423 : Blo 2121435 11470423 := bstep (se 1 (by rfl) ⟨8602817, by rfl⟩ : syracuseStep 11470423 = 17205635) B17205635
theorem B15293897 : Blo 2121435 15293897 := bstep (se 2 (by rfl) ⟨5735211, by rfl⟩ : syracuseStep 15293897 = 11470423) B11470423
theorem B10195931 : Blo 2121435 10195931 := bstep (se 1 (by rfl) ⟨7646948, by rfl⟩ : syracuseStep 10195931 = 15293897) B15293897
theorem B6797287 : Blo 2121435 6797287 := bstep (se 1 (by rfl) ⟨5097965, by rfl⟩ : syracuseStep 6797287 = 10195931) B10195931
theorem B9063049 : Blo 2121435 9063049 := bstep (se 2 (by rfl) ⟨3398643, by rfl⟩ : syracuseStep 9063049 = 6797287) B6797287
theorem B12084065 : Blo 2121435 12084065 := bstep (se 2 (by rfl) ⟨4531524, by rfl⟩ : syracuseStep 12084065 = 9063049) B9063049
theorem B8056043 : Blo 2121435 8056043 := bstep (se 1 (by rfl) ⟨6042032, by rfl⟩ : syracuseStep 8056043 = 12084065) B12084065
theorem B5370695 : Blo 2121435 5370695 := bstep (se 1 (by rfl) ⟨4028021, by rfl⟩ : syracuseStep 5370695 = 8056043) B8056043
theorem B3580463 : Blo 2121435 3580463 := bstep (se 1 (by rfl) ⟨2685347, by rfl⟩ : syracuseStep 3580463 = 5370695) B5370695
theorem B2386975 : Blo 2121435 2386975 := bstep (se 1 (by rfl) ⟨1790231, by rfl⟩ : syracuseStep 2386975 = 3580463) B3580463
theorem B3182633 : Blo 2121435 3182633 := bstep (se 2 (by rfl) ⟨1193487, by rfl⟩ : syracuseStep 3182633 = 2386975) B2386975
theorem B2121755 : Blo 2121435 2121755 := bstep (se 1 (by rfl) ⟨1591316, by rfl⟩ : syracuseStep 2121755 = 3182633) B3182633
theorem B3445021 : Blo 2121435 3445021 := bbase (se 3 (by rfl) ⟨645941, by rfl⟩ : syracuseStep 3445021 = 1291883) (by norm_num)
theorem B4593361 : Blo 2121435 4593361 := bstep (se 2 (by rfl) ⟨1722510, by rfl⟩ : syracuseStep 4593361 = 3445021) B3445021
theorem B6124481 : Blo 2121435 6124481 := bstep (se 2 (by rfl) ⟨2296680, by rfl⟩ : syracuseStep 6124481 = 4593361) B4593361
theorem B4082987 : Blo 2121435 4082987 := bstep (se 1 (by rfl) ⟨3062240, by rfl⟩ : syracuseStep 4082987 = 6124481) B6124481
theorem B10887965 : Blo 2121435 10887965 := bstep (se 3 (by rfl) ⟨2041493, by rfl⟩ : syracuseStep 10887965 = 4082987) B4082987
theorem B7258643 : Blo 2121435 7258643 := bstep (se 1 (by rfl) ⟨5443982, by rfl⟩ : syracuseStep 7258643 = 10887965) B10887965
theorem B4839095 : Blo 2121435 4839095 := bstep (se 1 (by rfl) ⟨3629321, by rfl⟩ : syracuseStep 4839095 = 7258643) B7258643
theorem B3226063 : Blo 2121435 3226063 := bstep (se 1 (by rfl) ⟨2419547, by rfl⟩ : syracuseStep 3226063 = 4839095) B4839095
theorem B4301417 : Blo 2121435 4301417 := bstep (se 2 (by rfl) ⟨1613031, by rfl⟩ : syracuseStep 4301417 = 3226063) B3226063
theorem B2867611 : Blo 2121435 2867611 := bstep (se 1 (by rfl) ⟨2150708, by rfl⟩ : syracuseStep 2867611 = 4301417) B4301417
theorem B3823481 : Blo 2121435 3823481 := bstep (se 2 (by rfl) ⟨1433805, by rfl⟩ : syracuseStep 3823481 = 2867611) B2867611
theorem B10195949 : Blo 2121435 10195949 := bstep (se 3 (by rfl) ⟨1911740, by rfl⟩ : syracuseStep 10195949 = 3823481) B3823481
theorem B6797299 : Blo 2121435 6797299 := bstep (se 1 (by rfl) ⟨5097974, by rfl⟩ : syracuseStep 6797299 = 10195949) B10195949
theorem B9063065 : Blo 2121435 9063065 := bstep (se 2 (by rfl) ⟨3398649, by rfl⟩ : syracuseStep 9063065 = 6797299) B6797299
theorem B6042043 : Blo 2121435 6042043 := bstep (se 1 (by rfl) ⟨4531532, by rfl⟩ : syracuseStep 6042043 = 9063065) B9063065
theorem B8056057 : Blo 2121435 8056057 := bstep (se 2 (by rfl) ⟨3021021, by rfl⟩ : syracuseStep 8056057 = 6042043) B6042043
theorem B10741409 : Blo 2121435 10741409 := bstep (se 2 (by rfl) ⟨4028028, by rfl⟩ : syracuseStep 10741409 = 8056057) B8056057
theorem B7160939 : Blo 2121435 7160939 := bstep (se 1 (by rfl) ⟨5370704, by rfl⟩ : syracuseStep 7160939 = 10741409) B10741409
theorem B4773959 : Blo 2121435 4773959 := bstep (se 1 (by rfl) ⟨3580469, by rfl⟩ : syracuseStep 4773959 = 7160939) B7160939
theorem B3182639 : Blo 2121435 3182639 := bstep (se 1 (by rfl) ⟨2386979, by rfl⟩ : syracuseStep 3182639 = 4773959) B4773959
theorem B2121759 : Blo 2121435 2121759 := bstep (se 1 (by rfl) ⟨1591319, by rfl⟩ : syracuseStep 2121759 = 3182639) B3182639
theorem B3182645 : Blo 2121435 3182645 := bbase (se 5 (by rfl) ⟨149186, by rfl⟩ : syracuseStep 3182645 = 298373) (by norm_num)
theorem B2121763 : Blo 2121435 2121763 := bstep (se 1 (by rfl) ⟨1591322, by rfl⟩ : syracuseStep 2121763 = 3182645) B3182645
theorem B5370725 : Blo 2121435 5370725 := bbase (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) (by norm_num)
theorem B3580483 : Blo 2121435 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B4773977 : Blo 2121435 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B3182651 : Blo 2121435 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B2121767 : Blo 2121435 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B2386993 : Blo 2121435 2386993 := bbase (se 2 (by rfl) ⟨895122, by rfl⟩ : syracuseStep 2386993 = 1790245) (by norm_num)
theorem B3182657 : Blo 2121435 3182657 := bstep (se 2 (by rfl) ⟨1193496, by rfl⟩ : syracuseStep 3182657 = 2386993) B2386993
theorem B2121771 : Blo 2121435 2121771 := bstep (se 1 (by rfl) ⟨1591328, by rfl⟩ : syracuseStep 2121771 = 3182657) B3182657
theorem B2583785 : Blo 2121435 2583785 := bbase (se 2 (by rfl) ⟨968919, by rfl⟩ : syracuseStep 2583785 = 1937839) (by norm_num)
theorem B6890093 : Blo 2121435 6890093 := bstep (se 3 (by rfl) ⟨1291892, by rfl⟩ : syracuseStep 6890093 = 2583785) B2583785
theorem B4593395 : Blo 2121435 4593395 := bstep (se 1 (by rfl) ⟨3445046, by rfl⟩ : syracuseStep 4593395 = 6890093) B6890093
theorem B12249053 : Blo 2121435 12249053 := bstep (se 3 (by rfl) ⟨2296697, by rfl⟩ : syracuseStep 12249053 = 4593395) B4593395
theorem B8166035 : Blo 2121435 8166035 := bstep (se 1 (by rfl) ⟨6124526, by rfl⟩ : syracuseStep 8166035 = 12249053) B12249053
theorem B5444023 : Blo 2121435 5444023 := bstep (se 1 (by rfl) ⟨4083017, by rfl⟩ : syracuseStep 5444023 = 8166035) B8166035
theorem B7258697 : Blo 2121435 7258697 := bstep (se 2 (by rfl) ⟨2722011, by rfl⟩ : syracuseStep 7258697 = 5444023) B5444023
theorem B4839131 : Blo 2121435 4839131 := bstep (se 1 (by rfl) ⟨3629348, by rfl⟩ : syracuseStep 4839131 = 7258697) B7258697
theorem B3226087 : Blo 2121435 3226087 := bstep (se 1 (by rfl) ⟨2419565, by rfl⟩ : syracuseStep 3226087 = 4839131) B4839131
theorem B17205797 : Blo 2121435 17205797 := bstep (se 4 (by rfl) ⟨1613043, by rfl⟩ : syracuseStep 17205797 = 3226087) B3226087
theorem B11470531 : Blo 2121435 11470531 := bstep (se 1 (by rfl) ⟨8602898, by rfl⟩ : syracuseStep 11470531 = 17205797) B17205797
theorem B15294041 : Blo 2121435 15294041 := bstep (se 2 (by rfl) ⟨5735265, by rfl⟩ : syracuseStep 15294041 = 11470531) B11470531
theorem B10196027 : Blo 2121435 10196027 := bstep (se 1 (by rfl) ⟨7647020, by rfl⟩ : syracuseStep 10196027 = 15294041) B15294041
theorem B6797351 : Blo 2121435 6797351 := bstep (se 1 (by rfl) ⟨5098013, by rfl⟩ : syracuseStep 6797351 = 10196027) B10196027
theorem B4531567 : Blo 2121435 4531567 := bstep (se 1 (by rfl) ⟨3398675, by rfl⟩ : syracuseStep 4531567 = 6797351) B6797351
theorem B6042089 : Blo 2121435 6042089 := bstep (se 2 (by rfl) ⟨2265783, by rfl⟩ : syracuseStep 6042089 = 4531567) B4531567
theorem B4028059 : Blo 2121435 4028059 := bstep (se 1 (by rfl) ⟨3021044, by rfl⟩ : syracuseStep 4028059 = 6042089) B6042089
theorem B5370745 : Blo 2121435 5370745 := bstep (se 2 (by rfl) ⟨2014029, by rfl⟩ : syracuseStep 5370745 = 4028059) B4028059
theorem B7160993 : Blo 2121435 7160993 := bstep (se 2 (by rfl) ⟨2685372, by rfl⟩ : syracuseStep 7160993 = 5370745) B5370745
theorem B4773995 : Blo 2121435 4773995 := bstep (se 1 (by rfl) ⟨3580496, by rfl⟩ : syracuseStep 4773995 = 7160993) B7160993
theorem B3182663 : Blo 2121435 3182663 := bstep (se 1 (by rfl) ⟨2386997, by rfl⟩ : syracuseStep 3182663 = 4773995) B4773995
theorem B2121775 : Blo 2121435 2121775 := bstep (se 1 (by rfl) ⟨1591331, by rfl⟩ : syracuseStep 2121775 = 3182663) B3182663
theorem B3182669 : Blo 2121435 3182669 := bbase (se 3 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 3182669 = 1193501) (by norm_num)
theorem B2121779 : Blo 2121435 2121779 := bstep (se 1 (by rfl) ⟨1591334, by rfl⟩ : syracuseStep 2121779 = 3182669) B3182669
theorem B4774013 : Blo 2121435 4774013 := bbase (se 3 (by rfl) ⟨895127, by rfl⟩ : syracuseStep 4774013 = 1790255) (by norm_num)
theorem B3182675 : Blo 2121435 3182675 := bstep (se 1 (by rfl) ⟨2387006, by rfl⟩ : syracuseStep 3182675 = 4774013) B4774013
theorem B2121783 : Blo 2121435 2121783 := bstep (se 1 (by rfl) ⟨1591337, by rfl⟩ : syracuseStep 2121783 = 3182675) B3182675
theorem B3580517 : Blo 2121435 3580517 := bbase (se 4 (by rfl) ⟨335673, by rfl⟩ : syracuseStep 3580517 = 671347) (by norm_num)
theorem B2387011 : Blo 2121435 2387011 := bstep (se 1 (by rfl) ⟨1790258, by rfl⟩ : syracuseStep 2387011 = 3580517) B3580517
theorem B3182681 : Blo 2121435 3182681 := bstep (se 2 (by rfl) ⟨1193505, by rfl⟩ : syracuseStep 3182681 = 2387011) B2387011
theorem B2121787 : Blo 2121435 2121787 := bstep (se 1 (by rfl) ⟨1591340, by rfl⟩ : syracuseStep 2121787 = 3182681) B3182681
theorem B3398701 : Blo 2121435 3398701 := bbase (se 3 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 3398701 = 1274513) (by norm_num)
theorem B4531601 : Blo 2121435 4531601 := bstep (se 2 (by rfl) ⟨1699350, by rfl⟩ : syracuseStep 4531601 = 3398701) B3398701
theorem B3021067 : Blo 2121435 3021067 := bstep (se 1 (by rfl) ⟨2265800, by rfl⟩ : syracuseStep 3021067 = 4531601) B4531601
theorem B16112357 : Blo 2121435 16112357 := bstep (se 4 (by rfl) ⟨1510533, by rfl⟩ : syracuseStep 16112357 = 3021067) B3021067
theorem B10741571 : Blo 2121435 10741571 := bstep (se 1 (by rfl) ⟨8056178, by rfl⟩ : syracuseStep 10741571 = 16112357) B16112357
theorem B7161047 : Blo 2121435 7161047 := bstep (se 1 (by rfl) ⟨5370785, by rfl⟩ : syracuseStep 7161047 = 10741571) B10741571
theorem B4774031 : Blo 2121435 4774031 := bstep (se 1 (by rfl) ⟨3580523, by rfl⟩ : syracuseStep 4774031 = 7161047) B7161047
theorem B3182687 : Blo 2121435 3182687 := bstep (se 1 (by rfl) ⟨2387015, by rfl⟩ : syracuseStep 3182687 = 4774031) B4774031
theorem B2121791 : Blo 2121435 2121791 := bstep (se 1 (by rfl) ⟨1591343, by rfl⟩ : syracuseStep 2121791 = 3182687) B3182687
theorem B3182693 : Blo 2121435 3182693 := bbase (se 4 (by rfl) ⟨298377, by rfl⟩ : syracuseStep 3182693 = 596755) (by norm_num)
theorem B2121795 : Blo 2121435 2121795 := bstep (se 1 (by rfl) ⟨1591346, by rfl⟩ : syracuseStep 2121795 = 3182693) B3182693
theorem B6797429 : Blo 2121435 6797429 := bbase (se 5 (by rfl) ⟨318629, by rfl⟩ : syracuseStep 6797429 = 637259) (by norm_num)
theorem B4531619 : Blo 2121435 4531619 := bstep (se 1 (by rfl) ⟨3398714, by rfl⟩ : syracuseStep 4531619 = 6797429) B6797429
theorem B3021079 : Blo 2121435 3021079 := bstep (se 1 (by rfl) ⟨2265809, by rfl⟩ : syracuseStep 3021079 = 4531619) B4531619
theorem B4028105 : Blo 2121435 4028105 := bstep (se 2 (by rfl) ⟨1510539, by rfl⟩ : syracuseStep 4028105 = 3021079) B3021079
theorem B2685403 : Blo 2121435 2685403 := bstep (se 1 (by rfl) ⟨2014052, by rfl⟩ : syracuseStep 2685403 = 4028105) B4028105
theorem B3580537 : Blo 2121435 3580537 := bstep (se 2 (by rfl) ⟨1342701, by rfl⟩ : syracuseStep 3580537 = 2685403) B2685403
theorem B4774049 : Blo 2121435 4774049 := bstep (se 2 (by rfl) ⟨1790268, by rfl⟩ : syracuseStep 4774049 = 3580537) B3580537
theorem B3182699 : Blo 2121435 3182699 := bstep (se 1 (by rfl) ⟨2387024, by rfl⟩ : syracuseStep 3182699 = 4774049) B4774049
theorem B2121799 : Blo 2121435 2121799 := bstep (se 1 (by rfl) ⟨1591349, by rfl⟩ : syracuseStep 2121799 = 3182699) B3182699
theorem B2387029 : Blo 2121435 2387029 := bbase (se 8 (by rfl) ⟨13986, by rfl⟩ : syracuseStep 2387029 = 27973) (by norm_num)
theorem B3182705 : Blo 2121435 3182705 := bstep (se 2 (by rfl) ⟨1193514, by rfl⟩ : syracuseStep 3182705 = 2387029) B2387029
theorem B2121803 : Blo 2121435 2121803 := bstep (se 1 (by rfl) ⟨1591352, by rfl⟩ : syracuseStep 2121803 = 3182705) B3182705
theorem B2685413 : Blo 2121435 2685413 := bbase (se 4 (by rfl) ⟨251757, by rfl⟩ : syracuseStep 2685413 = 503515) (by norm_num)
theorem B7161101 : Blo 2121435 7161101 := bstep (se 3 (by rfl) ⟨1342706, by rfl⟩ : syracuseStep 7161101 = 2685413) B2685413
theorem B4774067 : Blo 2121435 4774067 := bstep (se 1 (by rfl) ⟨3580550, by rfl⟩ : syracuseStep 4774067 = 7161101) B7161101
theorem B3182711 : Blo 2121435 3182711 := bstep (se 1 (by rfl) ⟨2387033, by rfl⟩ : syracuseStep 3182711 = 4774067) B4774067
theorem B2121807 : Blo 2121435 2121807 := bstep (se 1 (by rfl) ⟨1591355, by rfl⟩ : syracuseStep 2121807 = 3182711) B3182711
theorem B3182717 : Blo 2121435 3182717 := bbase (se 3 (by rfl) ⟨596759, by rfl⟩ : syracuseStep 3182717 = 1193519) (by norm_num)
theorem B2121811 : Blo 2121435 2121811 := bstep (se 1 (by rfl) ⟨1591358, by rfl⟩ : syracuseStep 2121811 = 3182717) B3182717
theorem B4774085 : Blo 2121435 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B3182723 : Blo 2121435 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B2121815 : Blo 2121435 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B34412309 : Blo 2121435 34412309 := bbase (se 6 (by rfl) ⟨806538, by rfl⟩ : syracuseStep 34412309 = 1613077) (by norm_num)
theorem B22941539 : Blo 2121435 22941539 := bstep (se 1 (by rfl) ⟨17206154, by rfl⟩ : syracuseStep 22941539 = 34412309) B34412309
theorem B15294359 : Blo 2121435 15294359 := bstep (se 1 (by rfl) ⟨11470769, by rfl⟩ : syracuseStep 15294359 = 22941539) B22941539
theorem B10196239 : Blo 2121435 10196239 := bstep (se 1 (by rfl) ⟨7647179, by rfl⟩ : syracuseStep 10196239 = 15294359) B15294359
theorem B13594985 : Blo 2121435 13594985 := bstep (se 2 (by rfl) ⟨5098119, by rfl⟩ : syracuseStep 13594985 = 10196239) B10196239
theorem B9063323 : Blo 2121435 9063323 := bstep (se 1 (by rfl) ⟨6797492, by rfl⟩ : syracuseStep 9063323 = 13594985) B13594985
theorem B6042215 : Blo 2121435 6042215 := bstep (se 1 (by rfl) ⟨4531661, by rfl⟩ : syracuseStep 6042215 = 9063323) B9063323
theorem B4028143 : Blo 2121435 4028143 := bstep (se 1 (by rfl) ⟨3021107, by rfl⟩ : syracuseStep 4028143 = 6042215) B6042215
theorem B5370857 : Blo 2121435 5370857 := bstep (se 2 (by rfl) ⟨2014071, by rfl⟩ : syracuseStep 5370857 = 4028143) B4028143
theorem B3580571 : Blo 2121435 3580571 := bstep (se 1 (by rfl) ⟨2685428, by rfl⟩ : syracuseStep 3580571 = 5370857) B5370857
theorem B2387047 : Blo 2121435 2387047 := bstep (se 1 (by rfl) ⟨1790285, by rfl⟩ : syracuseStep 2387047 = 3580571) B3580571
theorem B3182729 : Blo 2121435 3182729 := bstep (se 2 (by rfl) ⟨1193523, by rfl⟩ : syracuseStep 3182729 = 2387047) B2387047
theorem B2121819 : Blo 2121435 2121819 := bstep (se 1 (by rfl) ⟨1591364, by rfl⟩ : syracuseStep 2121819 = 3182729) B3182729
theorem B10741733 : Blo 2121435 10741733 := bbase (se 4 (by rfl) ⟨1007037, by rfl⟩ : syracuseStep 10741733 = 2014075) (by norm_num)
theorem B7161155 : Blo 2121435 7161155 := bstep (se 1 (by rfl) ⟨5370866, by rfl⟩ : syracuseStep 7161155 = 10741733) B10741733
theorem B4774103 : Blo 2121435 4774103 := bstep (se 1 (by rfl) ⟨3580577, by rfl⟩ : syracuseStep 4774103 = 7161155) B7161155
theorem B3182735 : Blo 2121435 3182735 := bstep (se 1 (by rfl) ⟨2387051, by rfl⟩ : syracuseStep 3182735 = 4774103) B4774103
theorem B2121823 : Blo 2121435 2121823 := bstep (se 1 (by rfl) ⟨1591367, by rfl⟩ : syracuseStep 2121823 = 3182735) B3182735
theorem B3182741 : Blo 2121435 3182741 := bbase (se 6 (by rfl) ⟨74595, by rfl⟩ : syracuseStep 3182741 = 149191) (by norm_num)
theorem B2121827 : Blo 2121435 2121827 := bstep (se 1 (by rfl) ⟨1591370, by rfl⟩ : syracuseStep 2121827 = 3182741) B3182741
theorem B3398765 : Blo 2121435 3398765 := bbase (se 3 (by rfl) ⟨637268, by rfl⟩ : syracuseStep 3398765 = 1274537) (by norm_num)
theorem B9063373 : Blo 2121435 9063373 := bstep (se 3 (by rfl) ⟨1699382, by rfl⟩ : syracuseStep 9063373 = 3398765) B3398765
theorem B12084497 : Blo 2121435 12084497 := bstep (se 2 (by rfl) ⟨4531686, by rfl⟩ : syracuseStep 12084497 = 9063373) B9063373
theorem B8056331 : Blo 2121435 8056331 := bstep (se 1 (by rfl) ⟨6042248, by rfl⟩ : syracuseStep 8056331 = 12084497) B12084497
theorem B5370887 : Blo 2121435 5370887 := bstep (se 1 (by rfl) ⟨4028165, by rfl⟩ : syracuseStep 5370887 = 8056331) B8056331
theorem B3580591 : Blo 2121435 3580591 := bstep (se 1 (by rfl) ⟨2685443, by rfl⟩ : syracuseStep 3580591 = 5370887) B5370887
theorem B4774121 : Blo 2121435 4774121 := bstep (se 2 (by rfl) ⟨1790295, by rfl⟩ : syracuseStep 4774121 = 3580591) B3580591
theorem B3182747 : Blo 2121435 3182747 := bstep (se 1 (by rfl) ⟨2387060, by rfl⟩ : syracuseStep 3182747 = 4774121) B4774121
theorem B2121831 : Blo 2121435 2121831 := bstep (se 1 (by rfl) ⟨1591373, by rfl⟩ : syracuseStep 2121831 = 3182747) B3182747
theorem B2387065 : Blo 2121435 2387065 := bbase (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) (by norm_num)
theorem B3182753 : Blo 2121435 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B2121835 : Blo 2121435 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B4905301 : Blo 2121435 4905301 := bbase (se 10 (by rfl) ⟨7185, by rfl⟩ : syracuseStep 4905301 = 14371) (by norm_num)
theorem B6540401 : Blo 2121435 6540401 := bstep (se 2 (by rfl) ⟨2452650, by rfl⟩ : syracuseStep 6540401 = 4905301) B4905301
theorem B4360267 : Blo 2121435 4360267 := bstep (se 1 (by rfl) ⟨3270200, by rfl⟩ : syracuseStep 4360267 = 6540401) B6540401
theorem B5813689 : Blo 2121435 5813689 := bstep (se 2 (by rfl) ⟨2180133, by rfl⟩ : syracuseStep 5813689 = 4360267) B4360267
theorem B7751585 : Blo 2121435 7751585 := bstep (se 2 (by rfl) ⟨2906844, by rfl⟩ : syracuseStep 7751585 = 5813689) B5813689
theorem B20670893 : Blo 2121435 20670893 := bstep (se 3 (by rfl) ⟨3875792, by rfl⟩ : syracuseStep 20670893 = 7751585) B7751585
theorem B13780595 : Blo 2121435 13780595 := bstep (se 1 (by rfl) ⟨10335446, by rfl⟩ : syracuseStep 13780595 = 20670893) B20670893
theorem B9187063 : Blo 2121435 9187063 := bstep (se 1 (by rfl) ⟨6890297, by rfl⟩ : syracuseStep 9187063 = 13780595) B13780595
theorem B48997669 : Blo 2121435 48997669 := bstep (se 4 (by rfl) ⟨4593531, by rfl⟩ : syracuseStep 48997669 = 9187063) B9187063
theorem B65330225 : Blo 2121435 65330225 := bstep (se 2 (by rfl) ⟨24498834, by rfl⟩ : syracuseStep 65330225 = 48997669) B48997669
theorem B43553483 : Blo 2121435 43553483 := bstep (se 1 (by rfl) ⟨32665112, by rfl⟩ : syracuseStep 43553483 = 65330225) B65330225
theorem B29035655 : Blo 2121435 29035655 := bstep (se 1 (by rfl) ⟨21776741, by rfl⟩ : syracuseStep 29035655 = 43553483) B43553483
theorem B19357103 : Blo 2121435 19357103 := bstep (se 1 (by rfl) ⟨14517827, by rfl⟩ : syracuseStep 19357103 = 29035655) B29035655
theorem B51618941 : Blo 2121435 51618941 := bstep (se 3 (by rfl) ⟨9678551, by rfl⟩ : syracuseStep 51618941 = 19357103) B19357103
theorem B34412627 : Blo 2121435 34412627 := bstep (se 1 (by rfl) ⟨25809470, by rfl⟩ : syracuseStep 34412627 = 51618941) B51618941
theorem B22941751 : Blo 2121435 22941751 := bstep (se 1 (by rfl) ⟨17206313, by rfl⟩ : syracuseStep 22941751 = 34412627) B34412627
theorem B30589001 : Blo 2121435 30589001 := bstep (se 2 (by rfl) ⟨11470875, by rfl⟩ : syracuseStep 30589001 = 22941751) B22941751
theorem B20392667 : Blo 2121435 20392667 := bstep (se 1 (by rfl) ⟨15294500, by rfl⟩ : syracuseStep 20392667 = 30589001) B30589001
theorem B13595111 : Blo 2121435 13595111 := bstep (se 1 (by rfl) ⟨10196333, by rfl⟩ : syracuseStep 13595111 = 20392667) B20392667
theorem B9063407 : Blo 2121435 9063407 := bstep (se 1 (by rfl) ⟨6797555, by rfl⟩ : syracuseStep 9063407 = 13595111) B13595111
theorem B6042271 : Blo 2121435 6042271 := bstep (se 1 (by rfl) ⟨4531703, by rfl⟩ : syracuseStep 6042271 = 9063407) B9063407
theorem B8056361 : Blo 2121435 8056361 := bstep (se 2 (by rfl) ⟨3021135, by rfl⟩ : syracuseStep 8056361 = 6042271) B6042271
theorem B5370907 : Blo 2121435 5370907 := bstep (se 1 (by rfl) ⟨4028180, by rfl⟩ : syracuseStep 5370907 = 8056361) B8056361
theorem B7161209 : Blo 2121435 7161209 := bstep (se 2 (by rfl) ⟨2685453, by rfl⟩ : syracuseStep 7161209 = 5370907) B5370907
theorem B4774139 : Blo 2121435 4774139 := bstep (se 1 (by rfl) ⟨3580604, by rfl⟩ : syracuseStep 4774139 = 7161209) B7161209
theorem B3182759 : Blo 2121435 3182759 := bstep (se 1 (by rfl) ⟨2387069, by rfl⟩ : syracuseStep 3182759 = 4774139) B4774139
theorem B2121839 : Blo 2121435 2121839 := bstep (se 1 (by rfl) ⟨1591379, by rfl⟩ : syracuseStep 2121839 = 3182759) B3182759
theorem B3182765 : Blo 2121435 3182765 := bbase (se 3 (by rfl) ⟨596768, by rfl⟩ : syracuseStep 3182765 = 1193537) (by norm_num)
theorem B2121843 : Blo 2121435 2121843 := bstep (se 1 (by rfl) ⟨1591382, by rfl⟩ : syracuseStep 2121843 = 3182765) B3182765
theorem B4774157 : Blo 2121435 4774157 := bbase (se 3 (by rfl) ⟨895154, by rfl⟩ : syracuseStep 4774157 = 1790309) (by norm_num)
theorem B3182771 : Blo 2121435 3182771 := bstep (se 1 (by rfl) ⟨2387078, by rfl⟩ : syracuseStep 3182771 = 4774157) B4774157
theorem B2121847 : Blo 2121435 2121847 := bstep (se 1 (by rfl) ⟨1591385, by rfl⟩ : syracuseStep 2121847 = 3182771) B3182771
theorem B2685469 : Blo 2121435 2685469 := bbase (se 3 (by rfl) ⟨503525, by rfl⟩ : syracuseStep 2685469 = 1007051) (by norm_num)
theorem B3580625 : Blo 2121435 3580625 := bstep (se 2 (by rfl) ⟨1342734, by rfl⟩ : syracuseStep 3580625 = 2685469) B2685469
theorem B2387083 : Blo 2121435 2387083 := bstep (se 1 (by rfl) ⟨1790312, by rfl⟩ : syracuseStep 2387083 = 3580625) B3580625
theorem B3182777 : Blo 2121435 3182777 := bstep (se 2 (by rfl) ⟨1193541, by rfl⟩ : syracuseStep 3182777 = 2387083) B2387083
theorem B2121851 : Blo 2121435 2121851 := bstep (se 1 (by rfl) ⟨1591388, by rfl⟩ : syracuseStep 2121851 = 3182777) B3182777
theorem B5098205 : Blo 2121435 5098205 := bbase (se 3 (by rfl) ⟨955913, by rfl⟩ : syracuseStep 5098205 = 1911827) (by norm_num)
theorem B3398803 : Blo 2121435 3398803 := bstep (se 1 (by rfl) ⟨2549102, by rfl⟩ : syracuseStep 3398803 = 5098205) B5098205
theorem B18126949 : Blo 2121435 18126949 := bstep (se 4 (by rfl) ⟨1699401, by rfl⟩ : syracuseStep 18126949 = 3398803) B3398803
theorem B24169265 : Blo 2121435 24169265 := bstep (se 2 (by rfl) ⟨9063474, by rfl⟩ : syracuseStep 24169265 = 18126949) B18126949
theorem B16112843 : Blo 2121435 16112843 := bstep (se 1 (by rfl) ⟨12084632, by rfl⟩ : syracuseStep 16112843 = 24169265) B24169265
theorem B10741895 : Blo 2121435 10741895 := bstep (se 1 (by rfl) ⟨8056421, by rfl⟩ : syracuseStep 10741895 = 16112843) B16112843
theorem B7161263 : Blo 2121435 7161263 := bstep (se 1 (by rfl) ⟨5370947, by rfl⟩ : syracuseStep 7161263 = 10741895) B10741895
theorem B4774175 : Blo 2121435 4774175 := bstep (se 1 (by rfl) ⟨3580631, by rfl⟩ : syracuseStep 4774175 = 7161263) B7161263
theorem B3182783 : Blo 2121435 3182783 := bstep (se 1 (by rfl) ⟨2387087, by rfl⟩ : syracuseStep 3182783 = 4774175) B4774175
theorem B2121855 : Blo 2121435 2121855 := bstep (se 1 (by rfl) ⟨1591391, by rfl⟩ : syracuseStep 2121855 = 3182783) B3182783
theorem B3182789 : Blo 2121435 3182789 := bbase (se 4 (by rfl) ⟨298386, by rfl⟩ : syracuseStep 3182789 = 596773) (by norm_num)
theorem B2121859 : Blo 2121435 2121859 := bstep (se 1 (by rfl) ⟨1591394, by rfl⟩ : syracuseStep 2121859 = 3182789) B3182789
theorem B3580645 : Blo 2121435 3580645 := bbase (se 4 (by rfl) ⟨335685, by rfl⟩ : syracuseStep 3580645 = 671371) (by norm_num)
theorem B4774193 : Blo 2121435 4774193 := bstep (se 2 (by rfl) ⟨1790322, by rfl⟩ : syracuseStep 4774193 = 3580645) B3580645
theorem B3182795 : Blo 2121435 3182795 := bstep (se 1 (by rfl) ⟨2387096, by rfl⟩ : syracuseStep 3182795 = 4774193) B4774193
theorem B2121863 : Blo 2121435 2121863 := bstep (se 1 (by rfl) ⟨1591397, by rfl⟩ : syracuseStep 2121863 = 3182795) B3182795
theorem B2387101 : Blo 2121435 2387101 := bbase (se 3 (by rfl) ⟨447581, by rfl⟩ : syracuseStep 2387101 = 895163) (by norm_num)
theorem B3182801 : Blo 2121435 3182801 := bstep (se 2 (by rfl) ⟨1193550, by rfl⟩ : syracuseStep 3182801 = 2387101) B2387101
theorem B2121867 : Blo 2121435 2121867 := bstep (se 1 (by rfl) ⟨1591400, by rfl⟩ : syracuseStep 2121867 = 3182801) B3182801
theorem B7161317 : Blo 2121435 7161317 := bbase (se 4 (by rfl) ⟨671373, by rfl⟩ : syracuseStep 7161317 = 1342747) (by norm_num)
theorem B4774211 : Blo 2121435 4774211 := bstep (se 1 (by rfl) ⟨3580658, by rfl⟩ : syracuseStep 4774211 = 7161317) B7161317
theorem B3182807 : Blo 2121435 3182807 := bstep (se 1 (by rfl) ⟨2387105, by rfl⟩ : syracuseStep 3182807 = 4774211) B4774211
theorem B2121871 : Blo 2121435 2121871 := bstep (se 1 (by rfl) ⟨1591403, by rfl⟩ : syracuseStep 2121871 = 3182807) B3182807
theorem B3182813 : Blo 2121435 3182813 := bbase (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) (by norm_num)
theorem B2121875 : Blo 2121435 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B4774229 : Blo 2121435 4774229 := bbase (se 10 (by rfl) ⟨6993, by rfl⟩ : syracuseStep 4774229 = 13987) (by norm_num)
theorem B3182819 : Blo 2121435 3182819 := bstep (se 1 (by rfl) ⟨2387114, by rfl⟩ : syracuseStep 3182819 = 4774229) B4774229
theorem B2121879 : Blo 2121435 2121879 := bstep (se 1 (by rfl) ⟨1591409, by rfl⟩ : syracuseStep 2121879 = 3182819) B3182819
theorem B2549137 : Blo 2121435 2549137 := bbase (se 2 (by rfl) ⟨955926, by rfl⟩ : syracuseStep 2549137 = 1911853) (by norm_num)
theorem B3398849 : Blo 2121435 3398849 := bstep (se 2 (by rfl) ⟨1274568, by rfl⟩ : syracuseStep 3398849 = 2549137) B2549137
theorem B2265899 : Blo 2121435 2265899 := bstep (se 1 (by rfl) ⟨1699424, by rfl⟩ : syracuseStep 2265899 = 3398849) B3398849
theorem B6042397 : Blo 2121435 6042397 := bstep (se 3 (by rfl) ⟨1132949, by rfl⟩ : syracuseStep 6042397 = 2265899) B2265899
theorem B8056529 : Blo 2121435 8056529 := bstep (se 2 (by rfl) ⟨3021198, by rfl⟩ : syracuseStep 8056529 = 6042397) B6042397
theorem B5371019 : Blo 2121435 5371019 := bstep (se 1 (by rfl) ⟨4028264, by rfl⟩ : syracuseStep 5371019 = 8056529) B8056529
theorem B3580679 : Blo 2121435 3580679 := bstep (se 1 (by rfl) ⟨2685509, by rfl⟩ : syracuseStep 3580679 = 5371019) B5371019
theorem B2387119 : Blo 2121435 2387119 := bstep (se 1 (by rfl) ⟨1790339, by rfl⟩ : syracuseStep 2387119 = 3580679) B3580679
theorem B3182825 : Blo 2121435 3182825 := bstep (se 2 (by rfl) ⟨1193559, by rfl⟩ : syracuseStep 3182825 = 2387119) B2387119
theorem B2121883 : Blo 2121435 2121883 := bstep (se 1 (by rfl) ⟨1591412, by rfl⟩ : syracuseStep 2121883 = 3182825) B3182825
theorem B5444309 : Blo 2121435 5444309 := bbase (se 7 (by rfl) ⟨63800, by rfl⟩ : syracuseStep 5444309 = 127601) (by norm_num)
theorem B3629539 : Blo 2121435 3629539 := bstep (se 1 (by rfl) ⟨2722154, by rfl⟩ : syracuseStep 3629539 = 5444309) B5444309
theorem B19357541 : Blo 2121435 19357541 := bstep (se 4 (by rfl) ⟨1814769, by rfl⟩ : syracuseStep 19357541 = 3629539) B3629539
theorem B12905027 : Blo 2121435 12905027 := bstep (se 1 (by rfl) ⟨9678770, by rfl⟩ : syracuseStep 12905027 = 19357541) B19357541
theorem B8603351 : Blo 2121435 8603351 := bstep (se 1 (by rfl) ⟨6452513, by rfl⟩ : syracuseStep 8603351 = 12905027) B12905027
theorem B5735567 : Blo 2121435 5735567 := bstep (se 1 (by rfl) ⟨4301675, by rfl⟩ : syracuseStep 5735567 = 8603351) B8603351
theorem B15294845 : Blo 2121435 15294845 := bstep (se 3 (by rfl) ⟨2867783, by rfl⟩ : syracuseStep 15294845 = 5735567) B5735567
theorem B40786253 : Blo 2121435 40786253 := bstep (se 3 (by rfl) ⟨7647422, by rfl⟩ : syracuseStep 40786253 = 15294845) B15294845
theorem B27190835 : Blo 2121435 27190835 := bstep (se 1 (by rfl) ⟨20393126, by rfl⟩ : syracuseStep 27190835 = 40786253) B40786253
theorem B18127223 : Blo 2121435 18127223 := bstep (se 1 (by rfl) ⟨13595417, by rfl⟩ : syracuseStep 18127223 = 27190835) B27190835
theorem B12084815 : Blo 2121435 12084815 := bstep (se 1 (by rfl) ⟨9063611, by rfl⟩ : syracuseStep 12084815 = 18127223) B18127223
theorem B8056543 : Blo 2121435 8056543 := bstep (se 1 (by rfl) ⟨6042407, by rfl⟩ : syracuseStep 8056543 = 12084815) B12084815
theorem B10742057 : Blo 2121435 10742057 := bstep (se 2 (by rfl) ⟨4028271, by rfl⟩ : syracuseStep 10742057 = 8056543) B8056543
theorem B7161371 : Blo 2121435 7161371 := bstep (se 1 (by rfl) ⟨5371028, by rfl⟩ : syracuseStep 7161371 = 10742057) B10742057
theorem B4774247 : Blo 2121435 4774247 := bstep (se 1 (by rfl) ⟨3580685, by rfl⟩ : syracuseStep 4774247 = 7161371) B7161371
theorem B3182831 : Blo 2121435 3182831 := bstep (se 1 (by rfl) ⟨2387123, by rfl⟩ : syracuseStep 3182831 = 4774247) B4774247
theorem B2121887 : Blo 2121435 2121887 := bstep (se 1 (by rfl) ⟨1591415, by rfl⟩ : syracuseStep 2121887 = 3182831) B3182831
theorem B3182837 : Blo 2121435 3182837 := bbase (se 5 (by rfl) ⟨149195, by rfl⟩ : syracuseStep 3182837 = 298391) (by norm_num)
theorem B2121891 : Blo 2121435 2121891 := bstep (se 1 (by rfl) ⟨1591418, by rfl⟩ : syracuseStep 2121891 = 3182837) B3182837
theorem B12905077 : Blo 2121435 12905077 := bbase (se 5 (by rfl) ⟨604925, by rfl⟩ : syracuseStep 12905077 = 1209851) (by norm_num)
theorem B17206769 : Blo 2121435 17206769 := bstep (se 2 (by rfl) ⟨6452538, by rfl⟩ : syracuseStep 17206769 = 12905077) B12905077
theorem B45884717 : Blo 2121435 45884717 := bstep (se 3 (by rfl) ⟨8603384, by rfl⟩ : syracuseStep 45884717 = 17206769) B17206769
theorem B30589811 : Blo 2121435 30589811 := bstep (se 1 (by rfl) ⟨22942358, by rfl⟩ : syracuseStep 30589811 = 45884717) B45884717
theorem B20393207 : Blo 2121435 20393207 := bstep (se 1 (by rfl) ⟨15294905, by rfl⟩ : syracuseStep 20393207 = 30589811) B30589811
theorem B13595471 : Blo 2121435 13595471 := bstep (se 1 (by rfl) ⟨10196603, by rfl⟩ : syracuseStep 13595471 = 20393207) B20393207
theorem B9063647 : Blo 2121435 9063647 := bstep (se 1 (by rfl) ⟨6797735, by rfl⟩ : syracuseStep 9063647 = 13595471) B13595471
theorem B6042431 : Blo 2121435 6042431 := bstep (se 1 (by rfl) ⟨4531823, by rfl⟩ : syracuseStep 6042431 = 9063647) B9063647
theorem B4028287 : Blo 2121435 4028287 := bstep (se 1 (by rfl) ⟨3021215, by rfl⟩ : syracuseStep 4028287 = 6042431) B6042431
theorem B5371049 : Blo 2121435 5371049 := bstep (se 2 (by rfl) ⟨2014143, by rfl⟩ : syracuseStep 5371049 = 4028287) B4028287
theorem B3580699 : Blo 2121435 3580699 := bstep (se 1 (by rfl) ⟨2685524, by rfl⟩ : syracuseStep 3580699 = 5371049) B5371049
theorem B4774265 : Blo 2121435 4774265 := bstep (se 2 (by rfl) ⟨1790349, by rfl⟩ : syracuseStep 4774265 = 3580699) B3580699
theorem B3182843 : Blo 2121435 3182843 := bstep (se 1 (by rfl) ⟨2387132, by rfl⟩ : syracuseStep 3182843 = 4774265) B4774265
theorem B2121895 : Blo 2121435 2121895 := bstep (se 1 (by rfl) ⟨1591421, by rfl⟩ : syracuseStep 2121895 = 3182843) B3182843
theorem B2387137 : Blo 2121435 2387137 := bbase (se 2 (by rfl) ⟨895176, by rfl⟩ : syracuseStep 2387137 = 1790353) (by norm_num)
theorem B3182849 : Blo 2121435 3182849 := bstep (se 2 (by rfl) ⟨1193568, by rfl⟩ : syracuseStep 3182849 = 2387137) B2387137
theorem B2121899 : Blo 2121435 2121899 := bstep (se 1 (by rfl) ⟨1591424, by rfl⟩ : syracuseStep 2121899 = 3182849) B3182849
theorem B5371069 : Blo 2121435 5371069 := bbase (se 3 (by rfl) ⟨1007075, by rfl⟩ : syracuseStep 5371069 = 2014151) (by norm_num)
theorem B7161425 : Blo 2121435 7161425 := bstep (se 2 (by rfl) ⟨2685534, by rfl⟩ : syracuseStep 7161425 = 5371069) B5371069
theorem B4774283 : Blo 2121435 4774283 := bstep (se 1 (by rfl) ⟨3580712, by rfl⟩ : syracuseStep 4774283 = 7161425) B7161425
theorem B3182855 : Blo 2121435 3182855 := bstep (se 1 (by rfl) ⟨2387141, by rfl⟩ : syracuseStep 3182855 = 4774283) B4774283
theorem B2121903 : Blo 2121435 2121903 := bstep (se 1 (by rfl) ⟨1591427, by rfl⟩ : syracuseStep 2121903 = 3182855) B3182855
theorem B3182861 : Blo 2121435 3182861 := bbase (se 3 (by rfl) ⟨596786, by rfl⟩ : syracuseStep 3182861 = 1193573) (by norm_num)
theorem B2121907 : Blo 2121435 2121907 := bstep (se 1 (by rfl) ⟨1591430, by rfl⟩ : syracuseStep 2121907 = 3182861) B3182861
theorem B4774301 : Blo 2121435 4774301 := bbase (se 3 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 4774301 = 1790363) (by norm_num)
theorem B3182867 : Blo 2121435 3182867 := bstep (se 1 (by rfl) ⟨2387150, by rfl⟩ : syracuseStep 3182867 = 4774301) B4774301
theorem B2121911 : Blo 2121435 2121911 := bstep (se 1 (by rfl) ⟨1591433, by rfl⟩ : syracuseStep 2121911 = 3182867) B3182867
theorem B3580733 : Blo 2121435 3580733 := bbase (se 3 (by rfl) ⟨671387, by rfl⟩ : syracuseStep 3580733 = 1342775) (by norm_num)
theorem B2387155 : Blo 2121435 2387155 := bstep (se 1 (by rfl) ⟨1790366, by rfl⟩ : syracuseStep 2387155 = 3580733) B3580733
theorem B3182873 : Blo 2121435 3182873 := bstep (se 2 (by rfl) ⟨1193577, by rfl⟩ : syracuseStep 3182873 = 2387155) B2387155
theorem B2121915 : Blo 2121435 2121915 := bstep (se 1 (by rfl) ⟨1591436, by rfl⟩ : syracuseStep 2121915 = 3182873) B3182873
theorem B2265937 : Blo 2121435 2265937 := bbase (se 2 (by rfl) ⟨849726, by rfl⟩ : syracuseStep 2265937 = 1699453) (by norm_num)
theorem B12084997 : Blo 2121435 12084997 := bstep (se 4 (by rfl) ⟨1132968, by rfl⟩ : syracuseStep 12084997 = 2265937) B2265937
theorem B16113329 : Blo 2121435 16113329 := bstep (se 2 (by rfl) ⟨6042498, by rfl⟩ : syracuseStep 16113329 = 12084997) B12084997
theorem B10742219 : Blo 2121435 10742219 := bstep (se 1 (by rfl) ⟨8056664, by rfl⟩ : syracuseStep 10742219 = 16113329) B16113329
theorem B7161479 : Blo 2121435 7161479 := bstep (se 1 (by rfl) ⟨5371109, by rfl⟩ : syracuseStep 7161479 = 10742219) B10742219
theorem B4774319 : Blo 2121435 4774319 := bstep (se 1 (by rfl) ⟨3580739, by rfl⟩ : syracuseStep 4774319 = 7161479) B7161479
theorem B3182879 : Blo 2121435 3182879 := bstep (se 1 (by rfl) ⟨2387159, by rfl⟩ : syracuseStep 3182879 = 4774319) B4774319
theorem B2121919 : Blo 2121435 2121919 := bstep (se 1 (by rfl) ⟨1591439, by rfl⟩ : syracuseStep 2121919 = 3182879) B3182879
theorem B3182885 : Blo 2121435 3182885 := bbase (se 4 (by rfl) ⟨298395, by rfl⟩ : syracuseStep 3182885 = 596791) (by norm_num)
theorem B2121923 : Blo 2121435 2121923 := bstep (se 1 (by rfl) ⟨1591442, by rfl⟩ : syracuseStep 2121923 = 3182885) B3182885
theorem B2685565 : Blo 2121435 2685565 := bbase (se 3 (by rfl) ⟨503543, by rfl⟩ : syracuseStep 2685565 = 1007087) (by norm_num)
theorem B3580753 : Blo 2121435 3580753 := bstep (se 2 (by rfl) ⟨1342782, by rfl⟩ : syracuseStep 3580753 = 2685565) B2685565
theorem B4774337 : Blo 2121435 4774337 := bstep (se 2 (by rfl) ⟨1790376, by rfl⟩ : syracuseStep 4774337 = 3580753) B3580753
theorem B3182891 : Blo 2121435 3182891 := bstep (se 1 (by rfl) ⟨2387168, by rfl⟩ : syracuseStep 3182891 = 4774337) B4774337
theorem B2121927 : Blo 2121435 2121927 := bstep (se 1 (by rfl) ⟨1591445, by rfl⟩ : syracuseStep 2121927 = 3182891) B3182891
theorem B2387173 : Blo 2121435 2387173 := bbase (se 4 (by rfl) ⟨223797, by rfl⟩ : syracuseStep 2387173 = 447595) (by norm_num)
theorem B3182897 : Blo 2121435 3182897 := bstep (se 2 (by rfl) ⟨1193586, by rfl⟩ : syracuseStep 3182897 = 2387173) B2387173
theorem B2121931 : Blo 2121435 2121931 := bstep (se 1 (by rfl) ⟨1591448, by rfl⟩ : syracuseStep 2121931 = 3182897) B3182897
theorem B4531909 : Blo 2121435 4531909 := bbase (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) (by norm_num)
theorem B6042545 : Blo 2121435 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B4028363 : Blo 2121435 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B2685575 : Blo 2121435 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B7161533 : Blo 2121435 7161533 := bstep (se 3 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 7161533 = 2685575) B2685575
theorem B4774355 : Blo 2121435 4774355 := bstep (se 1 (by rfl) ⟨3580766, by rfl⟩ : syracuseStep 4774355 = 7161533) B7161533
theorem B3182903 : Blo 2121435 3182903 := bstep (se 1 (by rfl) ⟨2387177, by rfl⟩ : syracuseStep 3182903 = 4774355) B4774355
theorem B2121935 : Blo 2121435 2121935 := bstep (se 1 (by rfl) ⟨1591451, by rfl⟩ : syracuseStep 2121935 = 3182903) B3182903
theorem B3182909 : Blo 2121435 3182909 := bbase (se 3 (by rfl) ⟨596795, by rfl⟩ : syracuseStep 3182909 = 1193591) (by norm_num)
theorem B2121939 : Blo 2121435 2121939 := bstep (se 1 (by rfl) ⟨1591454, by rfl⟩ : syracuseStep 2121939 = 3182909) B3182909
theorem B4774373 : Blo 2121435 4774373 := bbase (se 4 (by rfl) ⟨447597, by rfl⟩ : syracuseStep 4774373 = 895195) (by norm_num)
theorem B3182915 : Blo 2121435 3182915 := bstep (se 1 (by rfl) ⟨2387186, by rfl⟩ : syracuseStep 3182915 = 4774373) B4774373
theorem B2121943 : Blo 2121435 2121943 := bstep (se 1 (by rfl) ⟨1591457, by rfl⟩ : syracuseStep 2121943 = 3182915) B3182915
theorem B5371181 : Blo 2121435 5371181 := bbase (se 3 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 5371181 = 2014193) (by norm_num)
theorem B3580787 : Blo 2121435 3580787 := bstep (se 1 (by rfl) ⟨2685590, by rfl⟩ : syracuseStep 3580787 = 5371181) B5371181
theorem B2387191 : Blo 2121435 2387191 := bstep (se 1 (by rfl) ⟨1790393, by rfl⟩ : syracuseStep 2387191 = 3580787) B3580787
theorem B3182921 : Blo 2121435 3182921 := bstep (se 2 (by rfl) ⟨1193595, by rfl⟩ : syracuseStep 3182921 = 2387191) B2387191
theorem B2121947 : Blo 2121435 2121947 := bstep (se 1 (by rfl) ⟨1591460, by rfl⟩ : syracuseStep 2121947 = 3182921) B3182921
theorem B2722237 : Blo 2121435 2722237 := bbase (se 3 (by rfl) ⟨510419, by rfl⟩ : syracuseStep 2722237 = 1020839) (by norm_num)
theorem B14518597 : Blo 2121435 14518597 := bstep (se 4 (by rfl) ⟨1361118, by rfl⟩ : syracuseStep 14518597 = 2722237) B2722237
theorem B19358129 : Blo 2121435 19358129 := bstep (se 2 (by rfl) ⟨7259298, by rfl⟩ : syracuseStep 19358129 = 14518597) B14518597
theorem B12905419 : Blo 2121435 12905419 := bstep (se 1 (by rfl) ⟨9679064, by rfl⟩ : syracuseStep 12905419 = 19358129) B19358129
theorem B17207225 : Blo 2121435 17207225 := bstep (se 2 (by rfl) ⟨6452709, by rfl⟩ : syracuseStep 17207225 = 12905419) B12905419
theorem B11471483 : Blo 2121435 11471483 := bstep (se 1 (by rfl) ⟨8603612, by rfl⟩ : syracuseStep 11471483 = 17207225) B17207225
theorem B7647655 : Blo 2121435 7647655 := bstep (se 1 (by rfl) ⟨5735741, by rfl⟩ : syracuseStep 7647655 = 11471483) B11471483
theorem B10196873 : Blo 2121435 10196873 := bstep (se 2 (by rfl) ⟨3823827, by rfl⟩ : syracuseStep 10196873 = 7647655) B7647655
theorem B6797915 : Blo 2121435 6797915 := bstep (se 1 (by rfl) ⟨5098436, by rfl⟩ : syracuseStep 6797915 = 10196873) B10196873
theorem B4531943 : Blo 2121435 4531943 := bstep (se 1 (by rfl) ⟨3398957, by rfl⟩ : syracuseStep 4531943 = 6797915) B6797915
theorem B3021295 : Blo 2121435 3021295 := bstep (se 1 (by rfl) ⟨2265971, by rfl⟩ : syracuseStep 3021295 = 4531943) B4531943
theorem B4028393 : Blo 2121435 4028393 := bstep (se 2 (by rfl) ⟨1510647, by rfl⟩ : syracuseStep 4028393 = 3021295) B3021295
theorem B10742381 : Blo 2121435 10742381 := bstep (se 3 (by rfl) ⟨2014196, by rfl⟩ : syracuseStep 10742381 = 4028393) B4028393
theorem B7161587 : Blo 2121435 7161587 := bstep (se 1 (by rfl) ⟨5371190, by rfl⟩ : syracuseStep 7161587 = 10742381) B10742381
theorem B4774391 : Blo 2121435 4774391 := bstep (se 1 (by rfl) ⟨3580793, by rfl⟩ : syracuseStep 4774391 = 7161587) B7161587
theorem B3182927 : Blo 2121435 3182927 := bstep (se 1 (by rfl) ⟨2387195, by rfl⟩ : syracuseStep 3182927 = 4774391) B4774391
theorem B2121951 : Blo 2121435 2121951 := bstep (se 1 (by rfl) ⟨1591463, by rfl⟩ : syracuseStep 2121951 = 3182927) B3182927
theorem B3182933 : Blo 2121435 3182933 := bbase (se 10 (by rfl) ⟨4662, by rfl⟩ : syracuseStep 3182933 = 9325) (by norm_num)
theorem B2121955 : Blo 2121435 2121955 := bstep (se 1 (by rfl) ⟨1591466, by rfl⟩ : syracuseStep 2121955 = 3182933) B3182933
theorem B6042613 : Blo 2121435 6042613 := bbase (se 5 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 6042613 = 566495) (by norm_num)
theorem B8056817 : Blo 2121435 8056817 := bstep (se 2 (by rfl) ⟨3021306, by rfl⟩ : syracuseStep 8056817 = 6042613) B6042613
theorem B5371211 : Blo 2121435 5371211 := bstep (se 1 (by rfl) ⟨4028408, by rfl⟩ : syracuseStep 5371211 = 8056817) B8056817
theorem B3580807 : Blo 2121435 3580807 := bstep (se 1 (by rfl) ⟨2685605, by rfl⟩ : syracuseStep 3580807 = 5371211) B5371211
theorem B4774409 : Blo 2121435 4774409 := bstep (se 2 (by rfl) ⟨1790403, by rfl⟩ : syracuseStep 4774409 = 3580807) B3580807
theorem B3182939 : Blo 2121435 3182939 := bstep (se 1 (by rfl) ⟨2387204, by rfl⟩ : syracuseStep 3182939 = 4774409) B4774409
theorem B2121959 : Blo 2121435 2121959 := bstep (se 1 (by rfl) ⟨1591469, by rfl⟩ : syracuseStep 2121959 = 3182939) B3182939
theorem B2387209 : Blo 2121435 2387209 := bbase (se 2 (by rfl) ⟨895203, by rfl⟩ : syracuseStep 2387209 = 1790407) (by norm_num)
theorem B3182945 : Blo 2121435 3182945 := bstep (se 2 (by rfl) ⟨1193604, by rfl⟩ : syracuseStep 3182945 = 2387209) B2387209
theorem B2121963 : Blo 2121435 2121963 := bstep (se 1 (by rfl) ⟨1591472, by rfl⟩ : syracuseStep 2121963 = 3182945) B3182945
theorem B2549237 : Blo 2121435 2549237 := bbase (se 5 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 2549237 = 238991) (by norm_num)
theorem B27191861 : Blo 2121435 27191861 := bstep (se 5 (by rfl) ⟨1274618, by rfl⟩ : syracuseStep 27191861 = 2549237) B2549237
theorem B18127907 : Blo 2121435 18127907 := bstep (se 1 (by rfl) ⟨13595930, by rfl⟩ : syracuseStep 18127907 = 27191861) B27191861
theorem B12085271 : Blo 2121435 12085271 := bstep (se 1 (by rfl) ⟨9063953, by rfl⟩ : syracuseStep 12085271 = 18127907) B18127907
theorem B8056847 : Blo 2121435 8056847 := bstep (se 1 (by rfl) ⟨6042635, by rfl⟩ : syracuseStep 8056847 = 12085271) B12085271
theorem B5371231 : Blo 2121435 5371231 := bstep (se 1 (by rfl) ⟨4028423, by rfl⟩ : syracuseStep 5371231 = 8056847) B8056847
theorem B7161641 : Blo 2121435 7161641 := bstep (se 2 (by rfl) ⟨2685615, by rfl⟩ : syracuseStep 7161641 = 5371231) B5371231
theorem B4774427 : Blo 2121435 4774427 := bstep (se 1 (by rfl) ⟨3580820, by rfl⟩ : syracuseStep 4774427 = 7161641) B7161641
theorem B3182951 : Blo 2121435 3182951 := bstep (se 1 (by rfl) ⟨2387213, by rfl⟩ : syracuseStep 3182951 = 4774427) B4774427
theorem B2121967 : Blo 2121435 2121967 := bstep (se 1 (by rfl) ⟨1591475, by rfl⟩ : syracuseStep 2121967 = 3182951) B3182951
theorem B3182957 : Blo 2121435 3182957 := bbase (se 3 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 3182957 = 1193609) (by norm_num)
theorem B2121971 : Blo 2121435 2121971 := bstep (se 1 (by rfl) ⟨1591478, by rfl⟩ : syracuseStep 2121971 = 3182957) B3182957
theorem B4774445 : Blo 2121435 4774445 := bbase (se 3 (by rfl) ⟨895208, by rfl⟩ : syracuseStep 4774445 = 1790417) (by norm_num)
theorem B3182963 : Blo 2121435 3182963 := bstep (se 1 (by rfl) ⟨2387222, by rfl⟩ : syracuseStep 3182963 = 4774445) B4774445
theorem B2121975 : Blo 2121435 2121975 := bstep (se 1 (by rfl) ⟨1591481, by rfl⟩ : syracuseStep 2121975 = 3182963) B3182963
theorem B10889093 : Blo 2121435 10889093 := bbase (se 4 (by rfl) ⟨1020852, by rfl⟩ : syracuseStep 10889093 = 2041705) (by norm_num)
theorem B7259395 : Blo 2121435 7259395 := bstep (se 1 (by rfl) ⟨5444546, by rfl⟩ : syracuseStep 7259395 = 10889093) B10889093
theorem B9679193 : Blo 2121435 9679193 := bstep (se 2 (by rfl) ⟨3629697, by rfl⟩ : syracuseStep 9679193 = 7259395) B7259395
theorem B6452795 : Blo 2121435 6452795 := bstep (se 1 (by rfl) ⟨4839596, by rfl⟩ : syracuseStep 6452795 = 9679193) B9679193
theorem B17207453 : Blo 2121435 17207453 := bstep (se 3 (by rfl) ⟨3226397, by rfl⟩ : syracuseStep 17207453 = 6452795) B6452795
theorem B11471635 : Blo 2121435 11471635 := bstep (se 1 (by rfl) ⟨8603726, by rfl⟩ : syracuseStep 11471635 = 17207453) B17207453
theorem B15295513 : Blo 2121435 15295513 := bstep (se 2 (by rfl) ⟨5735817, by rfl⟩ : syracuseStep 15295513 = 11471635) B11471635
theorem B20394017 : Blo 2121435 20394017 := bstep (se 2 (by rfl) ⟨7647756, by rfl⟩ : syracuseStep 20394017 = 15295513) B15295513
theorem B13596011 : Blo 2121435 13596011 := bstep (se 1 (by rfl) ⟨10197008, by rfl⟩ : syracuseStep 13596011 = 20394017) B20394017
theorem B9064007 : Blo 2121435 9064007 := bstep (se 1 (by rfl) ⟨6798005, by rfl⟩ : syracuseStep 9064007 = 13596011) B13596011
theorem B6042671 : Blo 2121435 6042671 := bstep (se 1 (by rfl) ⟨4532003, by rfl⟩ : syracuseStep 6042671 = 9064007) B9064007
theorem B4028447 : Blo 2121435 4028447 := bstep (se 1 (by rfl) ⟨3021335, by rfl⟩ : syracuseStep 4028447 = 6042671) B6042671
theorem B2685631 : Blo 2121435 2685631 := bstep (se 1 (by rfl) ⟨2014223, by rfl⟩ : syracuseStep 2685631 = 4028447) B4028447
theorem B3580841 : Blo 2121435 3580841 := bstep (se 2 (by rfl) ⟨1342815, by rfl⟩ : syracuseStep 3580841 = 2685631) B2685631
theorem B2387227 : Blo 2121435 2387227 := bstep (se 1 (by rfl) ⟨1790420, by rfl⟩ : syracuseStep 2387227 = 3580841) B3580841
theorem B3182969 : Blo 2121435 3182969 := bstep (se 2 (by rfl) ⟨1193613, by rfl⟩ : syracuseStep 3182969 = 2387227) B2387227
theorem B2121979 : Blo 2121435 2121979 := bstep (se 1 (by rfl) ⟨1591484, by rfl⟩ : syracuseStep 2121979 = 3182969) B3182969
theorem B36256085 : Blo 2121435 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B24170723 : Blo 2121435 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B16113815 : Blo 2121435 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B10742543 : Blo 2121435 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B7161695 : Blo 2121435 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B4774463 : Blo 2121435 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B3182975 : Blo 2121435 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B2121983 : Blo 2121435 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B3182981 : Blo 2121435 3182981 := bbase (se 4 (by rfl) ⟨298404, by rfl⟩ : syracuseStep 3182981 = 596809) (by norm_num)
theorem B2121987 : Blo 2121435 2121987 := bstep (se 1 (by rfl) ⟨1591490, by rfl⟩ : syracuseStep 2121987 = 3182981) B3182981
theorem B3580861 : Blo 2121435 3580861 := bbase (se 3 (by rfl) ⟨671411, by rfl⟩ : syracuseStep 3580861 = 1342823) (by norm_num)
theorem B4774481 : Blo 2121435 4774481 := bstep (se 2 (by rfl) ⟨1790430, by rfl⟩ : syracuseStep 4774481 = 3580861) B3580861
theorem B3182987 : Blo 2121435 3182987 := bstep (se 1 (by rfl) ⟨2387240, by rfl⟩ : syracuseStep 3182987 = 4774481) B4774481
theorem B2121991 : Blo 2121435 2121991 := bstep (se 1 (by rfl) ⟨1591493, by rfl⟩ : syracuseStep 2121991 = 3182987) B3182987
theorem B2387245 : Blo 2121435 2387245 := bbase (se 3 (by rfl) ⟨447608, by rfl⟩ : syracuseStep 2387245 = 895217) (by norm_num)
theorem B3182993 : Blo 2121435 3182993 := bstep (se 2 (by rfl) ⟨1193622, by rfl⟩ : syracuseStep 3182993 = 2387245) B2387245
theorem B2121995 : Blo 2121435 2121995 := bstep (se 1 (by rfl) ⟨1591496, by rfl⟩ : syracuseStep 2121995 = 3182993) B3182993
theorem B7161749 : Blo 2121435 7161749 := bbase (se 6 (by rfl) ⟨167853, by rfl⟩ : syracuseStep 7161749 = 335707) (by norm_num)
theorem B4774499 : Blo 2121435 4774499 := bstep (se 1 (by rfl) ⟨3580874, by rfl⟩ : syracuseStep 4774499 = 7161749) B7161749
theorem B3182999 : Blo 2121435 3182999 := bstep (se 1 (by rfl) ⟨2387249, by rfl⟩ : syracuseStep 3182999 = 4774499) B4774499
theorem B2121999 : Blo 2121435 2121999 := bstep (se 1 (by rfl) ⟨1591499, by rfl⟩ : syracuseStep 2121999 = 3182999) B3182999
theorem B3183005 : Blo 2121435 3183005 := bbase (se 3 (by rfl) ⟨596813, by rfl⟩ : syracuseStep 3183005 = 1193627) (by norm_num)
theorem B2122003 : Blo 2121435 2122003 := bstep (se 1 (by rfl) ⟨1591502, by rfl⟩ : syracuseStep 2122003 = 3183005) B3183005
theorem B4774517 : Blo 2121435 4774517 := bbase (se 5 (by rfl) ⟨223805, by rfl⟩ : syracuseStep 4774517 = 447611) (by norm_num)
theorem B3183011 : Blo 2121435 3183011 := bstep (se 1 (by rfl) ⟨2387258, by rfl⟩ : syracuseStep 3183011 = 4774517) B4774517
theorem B2122007 : Blo 2121435 2122007 := bstep (se 1 (by rfl) ⟨1591505, by rfl⟩ : syracuseStep 2122007 = 3183011) B3183011
theorem B5973893 : Blo 2121435 5973893 := bbase (se 4 (by rfl) ⟨560052, by rfl⟩ : syracuseStep 5973893 = 1120105) (by norm_num)
theorem B63721525 : Blo 2121435 63721525 := bstep (se 5 (by rfl) ⟨2986946, by rfl⟩ : syracuseStep 63721525 = 5973893) B5973893
theorem B84962033 : Blo 2121435 84962033 := bstep (se 2 (by rfl) ⟨31860762, by rfl⟩ : syracuseStep 84962033 = 63721525) B63721525
theorem B56641355 : Blo 2121435 56641355 := bstep (se 1 (by rfl) ⟨42481016, by rfl⟩ : syracuseStep 56641355 = 84962033) B84962033
theorem B37760903 : Blo 2121435 37760903 := bstep (se 1 (by rfl) ⟨28320677, by rfl⟩ : syracuseStep 37760903 = 56641355) B56641355
theorem B25173935 : Blo 2121435 25173935 := bstep (se 1 (by rfl) ⟨18880451, by rfl⟩ : syracuseStep 25173935 = 37760903) B37760903
theorem B16782623 : Blo 2121435 16782623 := bstep (se 1 (by rfl) ⟨12586967, by rfl⟩ : syracuseStep 16782623 = 25173935) B25173935
theorem B11188415 : Blo 2121435 11188415 := bstep (se 1 (by rfl) ⟨8391311, by rfl⟩ : syracuseStep 11188415 = 16782623) B16782623
theorem B29835773 : Blo 2121435 29835773 := bstep (se 3 (by rfl) ⟨5594207, by rfl⟩ : syracuseStep 29835773 = 11188415) B11188415
theorem B19890515 : Blo 2121435 19890515 := bstep (se 1 (by rfl) ⟨14917886, by rfl⟩ : syracuseStep 19890515 = 29835773) B29835773
theorem B13260343 : Blo 2121435 13260343 := bstep (se 1 (by rfl) ⟨9945257, by rfl⟩ : syracuseStep 13260343 = 19890515) B19890515
theorem B17680457 : Blo 2121435 17680457 := bstep (se 2 (by rfl) ⟨6630171, by rfl⟩ : syracuseStep 17680457 = 13260343) B13260343
theorem B11786971 : Blo 2121435 11786971 := bstep (se 1 (by rfl) ⟨8840228, by rfl⟩ : syracuseStep 11786971 = 17680457) B17680457
theorem B15715961 : Blo 2121435 15715961 := bstep (se 2 (by rfl) ⟨5893485, by rfl⟩ : syracuseStep 15715961 = 11786971) B11786971
theorem B10477307 : Blo 2121435 10477307 := bstep (se 1 (by rfl) ⟨7857980, by rfl⟩ : syracuseStep 10477307 = 15715961) B15715961
theorem B27939485 : Blo 2121435 27939485 := bstep (se 3 (by rfl) ⟨5238653, by rfl⟩ : syracuseStep 27939485 = 10477307) B10477307
theorem B18626323 : Blo 2121435 18626323 := bstep (se 1 (by rfl) ⟨13969742, by rfl⟩ : syracuseStep 18626323 = 27939485) B27939485
theorem B24835097 : Blo 2121435 24835097 := bstep (se 2 (by rfl) ⟨9313161, by rfl⟩ : syracuseStep 24835097 = 18626323) B18626323
theorem B16556731 : Blo 2121435 16556731 := bstep (se 1 (by rfl) ⟨12417548, by rfl⟩ : syracuseStep 16556731 = 24835097) B24835097
theorem B88302565 : Blo 2121435 88302565 := bstep (se 4 (by rfl) ⟨8278365, by rfl⟩ : syracuseStep 88302565 = 16556731) B16556731
theorem B117736753 : Blo 2121435 117736753 := bstep (se 2 (by rfl) ⟨44151282, by rfl⟩ : syracuseStep 117736753 = 88302565) B88302565
theorem B156982337 : Blo 2121435 156982337 := bstep (se 2 (by rfl) ⟨58868376, by rfl⟩ : syracuseStep 156982337 = 117736753) B117736753
theorem B104654891 : Blo 2121435 104654891 := bstep (se 1 (by rfl) ⟨78491168, by rfl⟩ : syracuseStep 104654891 = 156982337) B156982337
theorem B69769927 : Blo 2121435 69769927 := bstep (se 1 (by rfl) ⟨52327445, by rfl⟩ : syracuseStep 69769927 = 104654891) B104654891
theorem B93026569 : Blo 2121435 93026569 := bstep (se 2 (by rfl) ⟨34884963, by rfl⟩ : syracuseStep 93026569 = 69769927) B69769927
theorem B124035425 : Blo 2121435 124035425 := bstep (se 2 (by rfl) ⟨46513284, by rfl⟩ : syracuseStep 124035425 = 93026569) B93026569
theorem B82690283 : Blo 2121435 82690283 := bstep (se 1 (by rfl) ⟨62017712, by rfl⟩ : syracuseStep 82690283 = 124035425) B124035425
theorem B55126855 : Blo 2121435 55126855 := bstep (se 1 (by rfl) ⟨41345141, by rfl⟩ : syracuseStep 55126855 = 82690283) B82690283
theorem B73502473 : Blo 2121435 73502473 := bstep (se 2 (by rfl) ⟨27563427, by rfl⟩ : syracuseStep 73502473 = 55126855) B55126855
theorem B98003297 : Blo 2121435 98003297 := bstep (se 2 (by rfl) ⟨36751236, by rfl⟩ : syracuseStep 98003297 = 73502473) B73502473
theorem B65335531 : Blo 2121435 65335531 := bstep (se 1 (by rfl) ⟨49001648, by rfl⟩ : syracuseStep 65335531 = 98003297) B98003297
theorem B87114041 : Blo 2121435 87114041 := bstep (se 2 (by rfl) ⟨32667765, by rfl⟩ : syracuseStep 87114041 = 65335531) B65335531
theorem B58076027 : Blo 2121435 58076027 := bstep (se 1 (by rfl) ⟨43557020, by rfl⟩ : syracuseStep 58076027 = 87114041) B87114041
theorem B38717351 : Blo 2121435 38717351 := bstep (se 1 (by rfl) ⟨29038013, by rfl⟩ : syracuseStep 38717351 = 58076027) B58076027
theorem B25811567 : Blo 2121435 25811567 := bstep (se 1 (by rfl) ⟨19358675, by rfl⟩ : syracuseStep 25811567 = 38717351) B38717351
theorem B17207711 : Blo 2121435 17207711 := bstep (se 1 (by rfl) ⟨12905783, by rfl⟩ : syracuseStep 17207711 = 25811567) B25811567
theorem B11471807 : Blo 2121435 11471807 := bstep (se 1 (by rfl) ⟨8603855, by rfl⟩ : syracuseStep 11471807 = 17207711) B17207711
theorem B7647871 : Blo 2121435 7647871 := bstep (se 1 (by rfl) ⟨5735903, by rfl⟩ : syracuseStep 7647871 = 11471807) B11471807
theorem B10197161 : Blo 2121435 10197161 := bstep (se 2 (by rfl) ⟨3823935, by rfl⟩ : syracuseStep 10197161 = 7647871) B7647871
theorem B6798107 : Blo 2121435 6798107 := bstep (se 1 (by rfl) ⟨5098580, by rfl⟩ : syracuseStep 6798107 = 10197161) B10197161
theorem B18128285 : Blo 2121435 18128285 := bstep (se 3 (by rfl) ⟨3399053, by rfl⟩ : syracuseStep 18128285 = 6798107) B6798107
theorem B12085523 : Blo 2121435 12085523 := bstep (se 1 (by rfl) ⟨9064142, by rfl⟩ : syracuseStep 12085523 = 18128285) B18128285
theorem B8057015 : Blo 2121435 8057015 := bstep (se 1 (by rfl) ⟨6042761, by rfl⟩ : syracuseStep 8057015 = 12085523) B12085523
theorem B5371343 : Blo 2121435 5371343 := bstep (se 1 (by rfl) ⟨4028507, by rfl⟩ : syracuseStep 5371343 = 8057015) B8057015
theorem B3580895 : Blo 2121435 3580895 := bstep (se 1 (by rfl) ⟨2685671, by rfl⟩ : syracuseStep 3580895 = 5371343) B5371343
theorem B2387263 : Blo 2121435 2387263 := bstep (se 1 (by rfl) ⟨1790447, by rfl⟩ : syracuseStep 2387263 = 3580895) B3580895
theorem B3183017 : Blo 2121435 3183017 := bstep (se 2 (by rfl) ⟨1193631, by rfl⟩ : syracuseStep 3183017 = 2387263) B2387263
theorem B2122011 : Blo 2121435 2122011 := bstep (se 1 (by rfl) ⟨1591508, by rfl⟩ : syracuseStep 2122011 = 3183017) B3183017
theorem B8057029 : Blo 2121435 8057029 := bbase (se 4 (by rfl) ⟨755346, by rfl⟩ : syracuseStep 8057029 = 1510693) (by norm_num)
theorem B10742705 : Blo 2121435 10742705 := bstep (se 2 (by rfl) ⟨4028514, by rfl⟩ : syracuseStep 10742705 = 8057029) B8057029
theorem B7161803 : Blo 2121435 7161803 := bstep (se 1 (by rfl) ⟨5371352, by rfl⟩ : syracuseStep 7161803 = 10742705) B10742705
theorem B4774535 : Blo 2121435 4774535 := bstep (se 1 (by rfl) ⟨3580901, by rfl⟩ : syracuseStep 4774535 = 7161803) B7161803
theorem B3183023 : Blo 2121435 3183023 := bstep (se 1 (by rfl) ⟨2387267, by rfl⟩ : syracuseStep 3183023 = 4774535) B4774535
theorem B2122015 : Blo 2121435 2122015 := bstep (se 1 (by rfl) ⟨1591511, by rfl⟩ : syracuseStep 2122015 = 3183023) B3183023
theorem B3183029 : Blo 2121435 3183029 := bbase (se 5 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 3183029 = 298409) (by norm_num)
theorem B2122019 : Blo 2121435 2122019 := bstep (se 1 (by rfl) ⟨1591514, by rfl⟩ : syracuseStep 2122019 = 3183029) B3183029
theorem B5371373 : Blo 2121435 5371373 := bbase (se 3 (by rfl) ⟨1007132, by rfl⟩ : syracuseStep 5371373 = 2014265) (by norm_num)
theorem B3580915 : Blo 2121435 3580915 := bstep (se 1 (by rfl) ⟨2685686, by rfl⟩ : syracuseStep 3580915 = 5371373) B5371373
theorem B4774553 : Blo 2121435 4774553 := bstep (se 2 (by rfl) ⟨1790457, by rfl⟩ : syracuseStep 4774553 = 3580915) B3580915
theorem B3183035 : Blo 2121435 3183035 := bstep (se 1 (by rfl) ⟨2387276, by rfl⟩ : syracuseStep 3183035 = 4774553) B4774553
theorem B2122023 : Blo 2121435 2122023 := bstep (se 1 (by rfl) ⟨1591517, by rfl⟩ : syracuseStep 2122023 = 3183035) B3183035
theorem B2387281 : Blo 2121435 2387281 := bbase (se 2 (by rfl) ⟨895230, by rfl⟩ : syracuseStep 2387281 = 1790461) (by norm_num)
theorem B3183041 : Blo 2121435 3183041 := bstep (se 2 (by rfl) ⟨1193640, by rfl⟩ : syracuseStep 3183041 = 2387281) B2387281
theorem B2122027 : Blo 2121435 2122027 := bstep (se 1 (by rfl) ⟨1591520, by rfl⟩ : syracuseStep 2122027 = 3183041) B3183041
theorem B2266057 : Blo 2121435 2266057 := bbase (se 2 (by rfl) ⟨849771, by rfl⟩ : syracuseStep 2266057 = 1699543) (by norm_num)
theorem B3021409 : Blo 2121435 3021409 := bstep (se 2 (by rfl) ⟨1133028, by rfl⟩ : syracuseStep 3021409 = 2266057) B2266057
theorem B4028545 : Blo 2121435 4028545 := bstep (se 2 (by rfl) ⟨1510704, by rfl⟩ : syracuseStep 4028545 = 3021409) B3021409
theorem B5371393 : Blo 2121435 5371393 := bstep (se 2 (by rfl) ⟨2014272, by rfl⟩ : syracuseStep 5371393 = 4028545) B4028545
theorem B7161857 : Blo 2121435 7161857 := bstep (se 2 (by rfl) ⟨2685696, by rfl⟩ : syracuseStep 7161857 = 5371393) B5371393
theorem B4774571 : Blo 2121435 4774571 := bstep (se 1 (by rfl) ⟨3580928, by rfl⟩ : syracuseStep 4774571 = 7161857) B7161857
theorem B3183047 : Blo 2121435 3183047 := bstep (se 1 (by rfl) ⟨2387285, by rfl⟩ : syracuseStep 3183047 = 4774571) B4774571
theorem B2122031 : Blo 2121435 2122031 := bstep (se 1 (by rfl) ⟨1591523, by rfl⟩ : syracuseStep 2122031 = 3183047) B3183047
theorem B3183053 : Blo 2121435 3183053 := bbase (se 3 (by rfl) ⟨596822, by rfl⟩ : syracuseStep 3183053 = 1193645) (by norm_num)
theorem B2122035 : Blo 2121435 2122035 := bstep (se 1 (by rfl) ⟨1591526, by rfl⟩ : syracuseStep 2122035 = 3183053) B3183053
theorem B4774589 : Blo 2121435 4774589 := bbase (se 3 (by rfl) ⟨895235, by rfl⟩ : syracuseStep 4774589 = 1790471) (by norm_num)
theorem B3183059 : Blo 2121435 3183059 := bstep (se 1 (by rfl) ⟨2387294, by rfl⟩ : syracuseStep 3183059 = 4774589) B4774589
theorem B2122039 : Blo 2121435 2122039 := bstep (se 1 (by rfl) ⟨1591529, by rfl⟩ : syracuseStep 2122039 = 3183059) B3183059
theorem B3580949 : Blo 2121435 3580949 := bbase (se 6 (by rfl) ⟨83928, by rfl⟩ : syracuseStep 3580949 = 167857) (by norm_num)
theorem B2387299 : Blo 2121435 2387299 := bstep (se 1 (by rfl) ⟨1790474, by rfl⟩ : syracuseStep 2387299 = 3580949) B3580949
theorem B3183065 : Blo 2121435 3183065 := bstep (se 2 (by rfl) ⟨1193649, by rfl⟩ : syracuseStep 3183065 = 2387299) B2387299
theorem B2122043 : Blo 2121435 2122043 := bstep (se 1 (by rfl) ⟨1591532, by rfl⟩ : syracuseStep 2122043 = 3183065) B3183065
theorem B20954965 : Blo 2121435 20954965 := bbase (se 9 (by rfl) ⟨61391, by rfl⟩ : syracuseStep 20954965 = 122783) (by norm_num)
theorem B27939953 : Blo 2121435 27939953 := bstep (se 2 (by rfl) ⟨10477482, by rfl⟩ : syracuseStep 27939953 = 20954965) B20954965
theorem B18626635 : Blo 2121435 18626635 := bstep (se 1 (by rfl) ⟨13969976, by rfl⟩ : syracuseStep 18626635 = 27939953) B27939953
theorem B24835513 : Blo 2121435 24835513 := bstep (se 2 (by rfl) ⟨9313317, by rfl⟩ : syracuseStep 24835513 = 18626635) B18626635
theorem B33114017 : Blo 2121435 33114017 := bstep (se 2 (by rfl) ⟨12417756, by rfl⟩ : syracuseStep 33114017 = 24835513) B24835513
theorem B22076011 : Blo 2121435 22076011 := bstep (se 1 (by rfl) ⟨16557008, by rfl⟩ : syracuseStep 22076011 = 33114017) B33114017
theorem B29434681 : Blo 2121435 29434681 := bstep (se 2 (by rfl) ⟨11038005, by rfl⟩ : syracuseStep 29434681 = 22076011) B22076011
theorem B156984965 : Blo 2121435 156984965 := bstep (se 4 (by rfl) ⟨14717340, by rfl⟩ : syracuseStep 156984965 = 29434681) B29434681
theorem B104656643 : Blo 2121435 104656643 := bstep (se 1 (by rfl) ⟨78492482, by rfl⟩ : syracuseStep 104656643 = 156984965) B156984965
theorem B69771095 : Blo 2121435 69771095 := bstep (se 1 (by rfl) ⟨52328321, by rfl⟩ : syracuseStep 69771095 = 104656643) B104656643
theorem B46514063 : Blo 2121435 46514063 := bstep (se 1 (by rfl) ⟨34885547, by rfl⟩ : syracuseStep 46514063 = 69771095) B69771095
theorem B31009375 : Blo 2121435 31009375 := bstep (se 1 (by rfl) ⟨23257031, by rfl⟩ : syracuseStep 31009375 = 46514063) B46514063
theorem B165383333 : Blo 2121435 165383333 := bstep (se 4 (by rfl) ⟨15504687, by rfl⟩ : syracuseStep 165383333 = 31009375) B31009375
theorem B110255555 : Blo 2121435 110255555 := bstep (se 1 (by rfl) ⟨82691666, by rfl⟩ : syracuseStep 110255555 = 165383333) B165383333
theorem B73503703 : Blo 2121435 73503703 := bstep (se 1 (by rfl) ⟨55127777, by rfl⟩ : syracuseStep 73503703 = 110255555) B110255555
theorem B392019749 : Blo 2121435 392019749 := bstep (se 4 (by rfl) ⟨36751851, by rfl⟩ : syracuseStep 392019749 = 73503703) B73503703
theorem B261346499 : Blo 2121435 261346499 := bstep (se 1 (by rfl) ⟨196009874, by rfl⟩ : syracuseStep 261346499 = 392019749) B392019749
theorem B174230999 : Blo 2121435 174230999 := bstep (se 1 (by rfl) ⟨130673249, by rfl⟩ : syracuseStep 174230999 = 261346499) B261346499
theorem B116153999 : Blo 2121435 116153999 := bstep (se 1 (by rfl) ⟨87115499, by rfl⟩ : syracuseStep 116153999 = 174230999) B174230999
theorem B77435999 : Blo 2121435 77435999 := bstep (se 1 (by rfl) ⟨58076999, by rfl⟩ : syracuseStep 77435999 = 116153999) B116153999
theorem B51623999 : Blo 2121435 51623999 := bstep (se 1 (by rfl) ⟨38717999, by rfl⟩ : syracuseStep 51623999 = 77435999) B77435999
theorem B34415999 : Blo 2121435 34415999 := bstep (se 1 (by rfl) ⟨25811999, by rfl⟩ : syracuseStep 34415999 = 51623999) B51623999
theorem B22943999 : Blo 2121435 22943999 := bstep (se 1 (by rfl) ⟨17207999, by rfl⟩ : syracuseStep 22943999 = 34415999) B34415999
theorem B15295999 : Blo 2121435 15295999 := bstep (se 1 (by rfl) ⟨11471999, by rfl⟩ : syracuseStep 15295999 = 22943999) B22943999
theorem B20394665 : Blo 2121435 20394665 := bstep (se 2 (by rfl) ⟨7647999, by rfl⟩ : syracuseStep 20394665 = 15295999) B15295999
theorem B13596443 : Blo 2121435 13596443 := bstep (se 1 (by rfl) ⟨10197332, by rfl⟩ : syracuseStep 13596443 = 20394665) B20394665
theorem B9064295 : Blo 2121435 9064295 := bstep (se 1 (by rfl) ⟨6798221, by rfl⟩ : syracuseStep 9064295 = 13596443) B13596443
theorem B6042863 : Blo 2121435 6042863 := bstep (se 1 (by rfl) ⟨4532147, by rfl⟩ : syracuseStep 6042863 = 9064295) B9064295
theorem B16114301 : Blo 2121435 16114301 := bstep (se 3 (by rfl) ⟨3021431, by rfl⟩ : syracuseStep 16114301 = 6042863) B6042863
theorem B10742867 : Blo 2121435 10742867 := bstep (se 1 (by rfl) ⟨8057150, by rfl⟩ : syracuseStep 10742867 = 16114301) B16114301
theorem B7161911 : Blo 2121435 7161911 := bstep (se 1 (by rfl) ⟨5371433, by rfl⟩ : syracuseStep 7161911 = 10742867) B10742867
theorem B4774607 : Blo 2121435 4774607 := bstep (se 1 (by rfl) ⟨3580955, by rfl⟩ : syracuseStep 4774607 = 7161911) B7161911
theorem B3183071 : Blo 2121435 3183071 := bstep (se 1 (by rfl) ⟨2387303, by rfl⟩ : syracuseStep 3183071 = 4774607) B4774607
theorem B2122047 : Blo 2121435 2122047 := bstep (se 1 (by rfl) ⟨1591535, by rfl⟩ : syracuseStep 2122047 = 3183071) B3183071
theorem B3183077 : Blo 2121435 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B2122051 : Blo 2121435 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B2419885 : Blo 2121435 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B12906053 : Blo 2121435 12906053 := bstep (se 4 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 12906053 = 2419885) B2419885
theorem B8604035 : Blo 2121435 8604035 := bstep (se 1 (by rfl) ⟨6453026, by rfl⟩ : syracuseStep 8604035 = 12906053) B12906053
theorem B5736023 : Blo 2121435 5736023 := bstep (se 1 (by rfl) ⟨4302017, by rfl⟩ : syracuseStep 5736023 = 8604035) B8604035
theorem B3824015 : Blo 2121435 3824015 := bstep (se 1 (by rfl) ⟨2868011, by rfl⟩ : syracuseStep 3824015 = 5736023) B5736023
theorem B10197373 : Blo 2121435 10197373 := bstep (se 3 (by rfl) ⟨1912007, by rfl⟩ : syracuseStep 10197373 = 3824015) B3824015
theorem B13596497 : Blo 2121435 13596497 := bstep (se 2 (by rfl) ⟨5098686, by rfl⟩ : syracuseStep 13596497 = 10197373) B10197373
theorem B9064331 : Blo 2121435 9064331 := bstep (se 1 (by rfl) ⟨6798248, by rfl⟩ : syracuseStep 9064331 = 13596497) B13596497
theorem B6042887 : Blo 2121435 6042887 := bstep (se 1 (by rfl) ⟨4532165, by rfl⟩ : syracuseStep 6042887 = 9064331) B9064331
theorem B4028591 : Blo 2121435 4028591 := bstep (se 1 (by rfl) ⟨3021443, by rfl⟩ : syracuseStep 4028591 = 6042887) B6042887
theorem B2685727 : Blo 2121435 2685727 := bstep (se 1 (by rfl) ⟨2014295, by rfl⟩ : syracuseStep 2685727 = 4028591) B4028591
theorem B3580969 : Blo 2121435 3580969 := bstep (se 2 (by rfl) ⟨1342863, by rfl⟩ : syracuseStep 3580969 = 2685727) B2685727
theorem B4774625 : Blo 2121435 4774625 := bstep (se 2 (by rfl) ⟨1790484, by rfl⟩ : syracuseStep 4774625 = 3580969) B3580969
theorem B3183083 : Blo 2121435 3183083 := bstep (se 1 (by rfl) ⟨2387312, by rfl⟩ : syracuseStep 3183083 = 4774625) B4774625
theorem B2122055 : Blo 2121435 2122055 := bstep (se 1 (by rfl) ⟨1591541, by rfl⟩ : syracuseStep 2122055 = 3183083) B3183083
theorem B2387317 : Blo 2121435 2387317 := bbase (se 5 (by rfl) ⟨111905, by rfl⟩ : syracuseStep 2387317 = 223811) (by norm_num)
theorem B3183089 : Blo 2121435 3183089 := bstep (se 2 (by rfl) ⟨1193658, by rfl⟩ : syracuseStep 3183089 = 2387317) B2387317
theorem B2122059 : Blo 2121435 2122059 := bstep (se 1 (by rfl) ⟨1591544, by rfl⟩ : syracuseStep 2122059 = 3183089) B3183089
theorem B2685737 : Blo 2121435 2685737 := bbase (se 2 (by rfl) ⟨1007151, by rfl⟩ : syracuseStep 2685737 = 2014303) (by norm_num)
theorem B7161965 : Blo 2121435 7161965 := bstep (se 3 (by rfl) ⟨1342868, by rfl⟩ : syracuseStep 7161965 = 2685737) B2685737
theorem B4774643 : Blo 2121435 4774643 := bstep (se 1 (by rfl) ⟨3580982, by rfl⟩ : syracuseStep 4774643 = 7161965) B7161965
theorem B3183095 : Blo 2121435 3183095 := bstep (se 1 (by rfl) ⟨2387321, by rfl⟩ : syracuseStep 3183095 = 4774643) B4774643
theorem B2122063 : Blo 2121435 2122063 := bstep (se 1 (by rfl) ⟨1591547, by rfl⟩ : syracuseStep 2122063 = 3183095) B3183095
theorem B3183101 : Blo 2121435 3183101 := bbase (se 3 (by rfl) ⟨596831, by rfl⟩ : syracuseStep 3183101 = 1193663) (by norm_num)
theorem B2122067 : Blo 2121435 2122067 := bstep (se 1 (by rfl) ⟨1591550, by rfl⟩ : syracuseStep 2122067 = 3183101) B3183101
theorem B4774661 : Blo 2121435 4774661 := bbase (se 4 (by rfl) ⟨447624, by rfl⟩ : syracuseStep 4774661 = 895249) (by norm_num)
theorem B3183107 : Blo 2121435 3183107 := bstep (se 1 (by rfl) ⟨2387330, by rfl⟩ : syracuseStep 3183107 = 4774661) B4774661
theorem B2122071 : Blo 2121435 2122071 := bstep (se 1 (by rfl) ⟨1591553, by rfl⟩ : syracuseStep 2122071 = 3183107) B3183107
theorem B4028629 : Blo 2121435 4028629 := bbase (se 7 (by rfl) ⟨47210, by rfl⟩ : syracuseStep 4028629 = 94421) (by norm_num)
theorem B5371505 : Blo 2121435 5371505 := bstep (se 2 (by rfl) ⟨2014314, by rfl⟩ : syracuseStep 5371505 = 4028629) B4028629
theorem B3581003 : Blo 2121435 3581003 := bstep (se 1 (by rfl) ⟨2685752, by rfl⟩ : syracuseStep 3581003 = 5371505) B5371505
theorem B2387335 : Blo 2121435 2387335 := bstep (se 1 (by rfl) ⟨1790501, by rfl⟩ : syracuseStep 2387335 = 3581003) B3581003
theorem B3183113 : Blo 2121435 3183113 := bstep (se 2 (by rfl) ⟨1193667, by rfl⟩ : syracuseStep 3183113 = 2387335) B2387335
theorem B2122075 : Blo 2121435 2122075 := bstep (se 1 (by rfl) ⟨1591556, by rfl⟩ : syracuseStep 2122075 = 3183113) B3183113
theorem B10743029 : Blo 2121435 10743029 := bbase (se 5 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 10743029 = 1007159) (by norm_num)
theorem B7162019 : Blo 2121435 7162019 := bstep (se 1 (by rfl) ⟨5371514, by rfl⟩ : syracuseStep 7162019 = 10743029) B10743029
theorem B4774679 : Blo 2121435 4774679 := bstep (se 1 (by rfl) ⟨3581009, by rfl⟩ : syracuseStep 4774679 = 7162019) B7162019
theorem B3183119 : Blo 2121435 3183119 := bstep (se 1 (by rfl) ⟨2387339, by rfl⟩ : syracuseStep 3183119 = 4774679) B4774679
theorem B2122079 : Blo 2121435 2122079 := bstep (se 1 (by rfl) ⟨1591559, by rfl⟩ : syracuseStep 2122079 = 3183119) B3183119
theorem B3183125 : Blo 2121435 3183125 := bbase (se 6 (by rfl) ⟨74604, by rfl⟩ : syracuseStep 3183125 = 149209) (by norm_num)
theorem B2122083 : Blo 2121435 2122083 := bstep (se 1 (by rfl) ⟨1591562, by rfl⟩ : syracuseStep 2122083 = 3183125) B3183125
theorem B2151041 : Blo 2121435 2151041 := bbase (se 2 (by rfl) ⟨806640, by rfl⟩ : syracuseStep 2151041 = 1613281) (by norm_num)
theorem B5736109 : Blo 2121435 5736109 := bstep (se 3 (by rfl) ⟨1075520, by rfl⟩ : syracuseStep 5736109 = 2151041) B2151041
theorem B7648145 : Blo 2121435 7648145 := bstep (se 2 (by rfl) ⟨2868054, by rfl⟩ : syracuseStep 7648145 = 5736109) B5736109
theorem B5098763 : Blo 2121435 5098763 := bstep (se 1 (by rfl) ⟨3824072, by rfl⟩ : syracuseStep 5098763 = 7648145) B7648145
theorem B3399175 : Blo 2121435 3399175 := bstep (se 1 (by rfl) ⟨2549381, by rfl⟩ : syracuseStep 3399175 = 5098763) B5098763
theorem B18128933 : Blo 2121435 18128933 := bstep (se 4 (by rfl) ⟨1699587, by rfl⟩ : syracuseStep 18128933 = 3399175) B3399175
theorem B12085955 : Blo 2121435 12085955 := bstep (se 1 (by rfl) ⟨9064466, by rfl⟩ : syracuseStep 12085955 = 18128933) B18128933
theorem B8057303 : Blo 2121435 8057303 := bstep (se 1 (by rfl) ⟨6042977, by rfl⟩ : syracuseStep 8057303 = 12085955) B12085955
theorem B5371535 : Blo 2121435 5371535 := bstep (se 1 (by rfl) ⟨4028651, by rfl⟩ : syracuseStep 5371535 = 8057303) B8057303
theorem B3581023 : Blo 2121435 3581023 := bstep (se 1 (by rfl) ⟨2685767, by rfl⟩ : syracuseStep 3581023 = 5371535) B5371535
theorem B4774697 : Blo 2121435 4774697 := bstep (se 2 (by rfl) ⟨1790511, by rfl⟩ : syracuseStep 4774697 = 3581023) B3581023
theorem B3183131 : Blo 2121435 3183131 := bstep (se 1 (by rfl) ⟨2387348, by rfl⟩ : syracuseStep 3183131 = 4774697) B4774697
theorem B2122087 : Blo 2121435 2122087 := bstep (se 1 (by rfl) ⟨1591565, by rfl⟩ : syracuseStep 2122087 = 3183131) B3183131
theorem B2387353 : Blo 2121435 2387353 := bbase (se 2 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 2387353 = 1790515) (by norm_num)
theorem B3183137 : Blo 2121435 3183137 := bstep (se 2 (by rfl) ⟨1193676, by rfl⟩ : syracuseStep 3183137 = 2387353) B2387353
theorem B2122091 : Blo 2121435 2122091 := bstep (se 1 (by rfl) ⟨1591568, by rfl⟩ : syracuseStep 2122091 = 3183137) B3183137
theorem B8057333 : Blo 2121435 8057333 := bbase (se 5 (by rfl) ⟨377687, by rfl⟩ : syracuseStep 8057333 = 755375) (by norm_num)
theorem B5371555 : Blo 2121435 5371555 := bstep (se 1 (by rfl) ⟨4028666, by rfl⟩ : syracuseStep 5371555 = 8057333) B8057333
theorem B7162073 : Blo 2121435 7162073 := bstep (se 2 (by rfl) ⟨2685777, by rfl⟩ : syracuseStep 7162073 = 5371555) B5371555
theorem B4774715 : Blo 2121435 4774715 := bstep (se 1 (by rfl) ⟨3581036, by rfl⟩ : syracuseStep 4774715 = 7162073) B7162073
theorem B3183143 : Blo 2121435 3183143 := bstep (se 1 (by rfl) ⟨2387357, by rfl⟩ : syracuseStep 3183143 = 4774715) B4774715
theorem B2122095 : Blo 2121435 2122095 := bstep (se 1 (by rfl) ⟨1591571, by rfl⟩ : syracuseStep 2122095 = 3183143) B3183143
theorem B3183149 : Blo 2121435 3183149 := bbase (se 3 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 3183149 = 1193681) (by norm_num)
theorem B2122099 : Blo 2121435 2122099 := bstep (se 1 (by rfl) ⟨1591574, by rfl⟩ : syracuseStep 2122099 = 3183149) B3183149
theorem B4774733 : Blo 2121435 4774733 := bbase (se 3 (by rfl) ⟨895262, by rfl⟩ : syracuseStep 4774733 = 1790525) (by norm_num)
theorem B3183155 : Blo 2121435 3183155 := bstep (se 1 (by rfl) ⟨2387366, by rfl⟩ : syracuseStep 3183155 = 4774733) B4774733
theorem B2122103 : Blo 2121435 2122103 := bstep (se 1 (by rfl) ⟨1591577, by rfl⟩ : syracuseStep 2122103 = 3183155) B3183155
theorem B2685793 : Blo 2121435 2685793 := bbase (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) (by norm_num)
theorem B3581057 : Blo 2121435 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B2387371 : Blo 2121435 2387371 := bstep (se 1 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 2387371 = 3581057) B3581057
theorem B3183161 : Blo 2121435 3183161 := bstep (se 2 (by rfl) ⟨1193685, by rfl⟩ : syracuseStep 3183161 = 2387371) B2387371
theorem B2122107 : Blo 2121435 2122107 := bstep (se 1 (by rfl) ⟨1591580, by rfl⟩ : syracuseStep 2122107 = 3183161) B3183161
theorem B24172181 : Blo 2121435 24172181 := bbase (se 6 (by rfl) ⟨566535, by rfl⟩ : syracuseStep 24172181 = 1133071) (by norm_num)
theorem B16114787 : Blo 2121435 16114787 := bstep (se 1 (by rfl) ⟨12086090, by rfl⟩ : syracuseStep 16114787 = 24172181) B24172181
theorem B10743191 : Blo 2121435 10743191 := bstep (se 1 (by rfl) ⟨8057393, by rfl⟩ : syracuseStep 10743191 = 16114787) B16114787
theorem B7162127 : Blo 2121435 7162127 := bstep (se 1 (by rfl) ⟨5371595, by rfl⟩ : syracuseStep 7162127 = 10743191) B10743191
theorem B4774751 : Blo 2121435 4774751 := bstep (se 1 (by rfl) ⟨3581063, by rfl⟩ : syracuseStep 4774751 = 7162127) B7162127
theorem B3183167 : Blo 2121435 3183167 := bstep (se 1 (by rfl) ⟨2387375, by rfl⟩ : syracuseStep 3183167 = 4774751) B4774751
theorem B2122111 : Blo 2121435 2122111 := bstep (se 1 (by rfl) ⟨1591583, by rfl⟩ : syracuseStep 2122111 = 3183167) B3183167
theorem B3183173 : Blo 2121435 3183173 := bbase (se 4 (by rfl) ⟨298422, by rfl⟩ : syracuseStep 3183173 = 596845) (by norm_num)
theorem B2122115 : Blo 2121435 2122115 := bstep (se 1 (by rfl) ⟨1591586, by rfl⟩ : syracuseStep 2122115 = 3183173) B3183173
theorem B3581077 : Blo 2121435 3581077 := bbase (se 6 (by rfl) ⟨83931, by rfl⟩ : syracuseStep 3581077 = 167863) (by norm_num)
theorem B4774769 : Blo 2121435 4774769 := bstep (se 2 (by rfl) ⟨1790538, by rfl⟩ : syracuseStep 4774769 = 3581077) B3581077
theorem B3183179 : Blo 2121435 3183179 := bstep (se 1 (by rfl) ⟨2387384, by rfl⟩ : syracuseStep 3183179 = 4774769) B4774769
theorem B2122119 : Blo 2121435 2122119 := bstep (se 1 (by rfl) ⟨1591589, by rfl⟩ : syracuseStep 2122119 = 3183179) B3183179
theorem B2387389 : Blo 2121435 2387389 := bbase (se 3 (by rfl) ⟨447635, by rfl⟩ : syracuseStep 2387389 = 895271) (by norm_num)
theorem B3183185 : Blo 2121435 3183185 := bstep (se 2 (by rfl) ⟨1193694, by rfl⟩ : syracuseStep 3183185 = 2387389) B2387389
theorem B2122123 : Blo 2121435 2122123 := bstep (se 1 (by rfl) ⟨1591592, by rfl⟩ : syracuseStep 2122123 = 3183185) B3183185
theorem B7162181 : Blo 2121435 7162181 := bbase (se 4 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 7162181 = 1342909) (by norm_num)
theorem B4774787 : Blo 2121435 4774787 := bstep (se 1 (by rfl) ⟨3581090, by rfl⟩ : syracuseStep 4774787 = 7162181) B7162181
theorem B3183191 : Blo 2121435 3183191 := bstep (se 1 (by rfl) ⟨2387393, by rfl⟩ : syracuseStep 3183191 = 4774787) B4774787
theorem B2122127 : Blo 2121435 2122127 := bstep (se 1 (by rfl) ⟨1591595, by rfl⟩ : syracuseStep 2122127 = 3183191) B3183191
theorem B3183197 : Blo 2121435 3183197 := bbase (se 3 (by rfl) ⟨596849, by rfl⟩ : syracuseStep 3183197 = 1193699) (by norm_num)
theorem B2122131 : Blo 2121435 2122131 := bstep (se 1 (by rfl) ⟨1591598, by rfl⟩ : syracuseStep 2122131 = 3183197) B3183197
theorem B4774805 : Blo 2121435 4774805 := bbase (se 6 (by rfl) ⟨111909, by rfl⟩ : syracuseStep 4774805 = 223819) (by norm_num)
theorem B3183203 : Blo 2121435 3183203 := bstep (se 1 (by rfl) ⟨2387402, by rfl⟩ : syracuseStep 3183203 = 4774805) B4774805
theorem B2122135 : Blo 2121435 2122135 := bstep (se 1 (by rfl) ⟨1591601, by rfl⟩ : syracuseStep 2122135 = 3183203) B3183203
theorem B9679925 : Blo 2121435 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B6453283 : Blo 2121435 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B8604377 : Blo 2121435 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B5736251 : Blo 2121435 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B3824167 : Blo 2121435 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B5098889 : Blo 2121435 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B3399259 : Blo 2121435 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B4532345 : Blo 2121435 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B3021563 : Blo 2121435 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B8057501 : Blo 2121435 8057501 := bstep (se 3 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 8057501 = 3021563) B3021563
theorem B5371667 : Blo 2121435 5371667 := bstep (se 1 (by rfl) ⟨4028750, by rfl⟩ : syracuseStep 5371667 = 8057501) B8057501
theorem B3581111 : Blo 2121435 3581111 := bstep (se 1 (by rfl) ⟨2685833, by rfl⟩ : syracuseStep 3581111 = 5371667) B5371667
theorem B2387407 : Blo 2121435 2387407 := bstep (se 1 (by rfl) ⟨1790555, by rfl⟩ : syracuseStep 2387407 = 3581111) B3581111
theorem B3183209 : Blo 2121435 3183209 := bstep (se 2 (by rfl) ⟨1193703, by rfl⟩ : syracuseStep 3183209 = 2387407) B2387407
theorem B2122139 : Blo 2121435 2122139 := bstep (se 1 (by rfl) ⟨1591604, by rfl⟩ : syracuseStep 2122139 = 3183209) B3183209
theorem B3824173 : Blo 2121435 3824173 := bbase (se 3 (by rfl) ⟨717032, by rfl⟩ : syracuseStep 3824173 = 1434065) (by norm_num)
theorem B5098897 : Blo 2121435 5098897 := bstep (se 2 (by rfl) ⟨1912086, by rfl⟩ : syracuseStep 5098897 = 3824173) B3824173
theorem B6798529 : Blo 2121435 6798529 := bstep (se 2 (by rfl) ⟨2549448, by rfl⟩ : syracuseStep 6798529 = 5098897) B5098897
theorem B9064705 : Blo 2121435 9064705 := bstep (se 2 (by rfl) ⟨3399264, by rfl⟩ : syracuseStep 9064705 = 6798529) B6798529
theorem B12086273 : Blo 2121435 12086273 := bstep (se 2 (by rfl) ⟨4532352, by rfl⟩ : syracuseStep 12086273 = 9064705) B9064705
theorem B8057515 : Blo 2121435 8057515 := bstep (se 1 (by rfl) ⟨6043136, by rfl⟩ : syracuseStep 8057515 = 12086273) B12086273
theorem B10743353 : Blo 2121435 10743353 := bstep (se 2 (by rfl) ⟨4028757, by rfl⟩ : syracuseStep 10743353 = 8057515) B8057515
theorem B7162235 : Blo 2121435 7162235 := bstep (se 1 (by rfl) ⟨5371676, by rfl⟩ : syracuseStep 7162235 = 10743353) B10743353
theorem B4774823 : Blo 2121435 4774823 := bstep (se 1 (by rfl) ⟨3581117, by rfl⟩ : syracuseStep 4774823 = 7162235) B7162235
theorem B3183215 : Blo 2121435 3183215 := bstep (se 1 (by rfl) ⟨2387411, by rfl⟩ : syracuseStep 3183215 = 4774823) B4774823
theorem B2122143 : Blo 2121435 2122143 := bstep (se 1 (by rfl) ⟨1591607, by rfl⟩ : syracuseStep 2122143 = 3183215) B3183215
theorem B3183221 : Blo 2121435 3183221 := bbase (se 5 (by rfl) ⟨149213, by rfl⟩ : syracuseStep 3183221 = 298427) (by norm_num)
theorem B2122147 : Blo 2121435 2122147 := bstep (se 1 (by rfl) ⟨1591610, by rfl⟩ : syracuseStep 2122147 = 3183221) B3183221
theorem B4028773 : Blo 2121435 4028773 := bbase (se 4 (by rfl) ⟨377697, by rfl⟩ : syracuseStep 4028773 = 755395) (by norm_num)
theorem B5371697 : Blo 2121435 5371697 := bstep (se 2 (by rfl) ⟨2014386, by rfl⟩ : syracuseStep 5371697 = 4028773) B4028773
theorem B3581131 : Blo 2121435 3581131 := bstep (se 1 (by rfl) ⟨2685848, by rfl⟩ : syracuseStep 3581131 = 5371697) B5371697
theorem B4774841 : Blo 2121435 4774841 := bstep (se 2 (by rfl) ⟨1790565, by rfl⟩ : syracuseStep 4774841 = 3581131) B3581131
theorem B3183227 : Blo 2121435 3183227 := bstep (se 1 (by rfl) ⟨2387420, by rfl⟩ : syracuseStep 3183227 = 4774841) B4774841
theorem B2122151 : Blo 2121435 2122151 := bstep (se 1 (by rfl) ⟨1591613, by rfl⟩ : syracuseStep 2122151 = 3183227) B3183227
theorem B2387425 : Blo 2121435 2387425 := bbase (se 2 (by rfl) ⟨895284, by rfl⟩ : syracuseStep 2387425 = 1790569) (by norm_num)
theorem B3183233 : Blo 2121435 3183233 := bstep (se 2 (by rfl) ⟨1193712, by rfl⟩ : syracuseStep 3183233 = 2387425) B2387425
theorem B2122155 : Blo 2121435 2122155 := bstep (se 1 (by rfl) ⟨1591616, by rfl⟩ : syracuseStep 2122155 = 3183233) B3183233
theorem B5371717 : Blo 2121435 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B7162289 : Blo 2121435 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B4774859 : Blo 2121435 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B3183239 : Blo 2121435 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B2122159 : Blo 2121435 2122159 := bstep (se 1 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 2122159 = 3183239) B3183239
theorem B3183245 : Blo 2121435 3183245 := bbase (se 3 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 3183245 = 1193717) (by norm_num)
theorem B2122163 : Blo 2121435 2122163 := bstep (se 1 (by rfl) ⟨1591622, by rfl⟩ : syracuseStep 2122163 = 3183245) B3183245
theorem B4774877 : Blo 2121435 4774877 := bbase (se 3 (by rfl) ⟨895289, by rfl⟩ : syracuseStep 4774877 = 1790579) (by norm_num)
theorem B3183251 : Blo 2121435 3183251 := bstep (se 1 (by rfl) ⟨2387438, by rfl⟩ : syracuseStep 3183251 = 4774877) B4774877
theorem B2122167 : Blo 2121435 2122167 := bstep (se 1 (by rfl) ⟨1591625, by rfl⟩ : syracuseStep 2122167 = 3183251) B3183251
theorem B3581165 : Blo 2121435 3581165 := bbase (se 3 (by rfl) ⟨671468, by rfl⟩ : syracuseStep 3581165 = 1342937) (by norm_num)
theorem B2387443 : Blo 2121435 2387443 := bstep (se 1 (by rfl) ⟨1790582, by rfl⟩ : syracuseStep 2387443 = 3581165) B3581165
theorem B3183257 : Blo 2121435 3183257 := bstep (se 2 (by rfl) ⟨1193721, by rfl⟩ : syracuseStep 3183257 = 2387443) B2387443
theorem B2122171 : Blo 2121435 2122171 := bstep (se 1 (by rfl) ⟨1591628, by rfl⟩ : syracuseStep 2122171 = 3183257) B3183257
theorem B2420021 : Blo 2121435 2420021 := bbase (se 5 (by rfl) ⟨113438, by rfl⟩ : syracuseStep 2420021 = 226877) (by norm_num)
theorem B6453389 : Blo 2121435 6453389 := bstep (se 3 (by rfl) ⟨1210010, by rfl⟩ : syracuseStep 6453389 = 2420021) B2420021
theorem B17209037 : Blo 2121435 17209037 := bstep (se 3 (by rfl) ⟨3226694, by rfl⟩ : syracuseStep 17209037 = 6453389) B6453389
theorem B11472691 : Blo 2121435 11472691 := bstep (se 1 (by rfl) ⟨8604518, by rfl⟩ : syracuseStep 11472691 = 17209037) B17209037
theorem B15296921 : Blo 2121435 15296921 := bstep (se 2 (by rfl) ⟨5736345, by rfl⟩ : syracuseStep 15296921 = 11472691) B11472691
theorem B10197947 : Blo 2121435 10197947 := bstep (se 1 (by rfl) ⟨7648460, by rfl⟩ : syracuseStep 10197947 = 15296921) B15296921
theorem B27194525 : Blo 2121435 27194525 := bstep (se 3 (by rfl) ⟨5098973, by rfl⟩ : syracuseStep 27194525 = 10197947) B10197947
theorem B18129683 : Blo 2121435 18129683 := bstep (se 1 (by rfl) ⟨13597262, by rfl⟩ : syracuseStep 18129683 = 27194525) B27194525
theorem B12086455 : Blo 2121435 12086455 := bstep (se 1 (by rfl) ⟨9064841, by rfl⟩ : syracuseStep 12086455 = 18129683) B18129683
theorem B16115273 : Blo 2121435 16115273 := bstep (se 2 (by rfl) ⟨6043227, by rfl⟩ : syracuseStep 16115273 = 12086455) B12086455
theorem B10743515 : Blo 2121435 10743515 := bstep (se 1 (by rfl) ⟨8057636, by rfl⟩ : syracuseStep 10743515 = 16115273) B16115273
theorem B7162343 : Blo 2121435 7162343 := bstep (se 1 (by rfl) ⟨5371757, by rfl⟩ : syracuseStep 7162343 = 10743515) B10743515
theorem B4774895 : Blo 2121435 4774895 := bstep (se 1 (by rfl) ⟨3581171, by rfl⟩ : syracuseStep 4774895 = 7162343) B7162343
theorem B3183263 : Blo 2121435 3183263 := bstep (se 1 (by rfl) ⟨2387447, by rfl⟩ : syracuseStep 3183263 = 4774895) B4774895
theorem B2122175 : Blo 2121435 2122175 := bstep (se 1 (by rfl) ⟨1591631, by rfl⟩ : syracuseStep 2122175 = 3183263) B3183263
theorem B3183269 : Blo 2121435 3183269 := bbase (se 4 (by rfl) ⟨298431, by rfl⟩ : syracuseStep 3183269 = 596863) (by norm_num)
theorem B2122179 : Blo 2121435 2122179 := bstep (se 1 (by rfl) ⟨1591634, by rfl⟩ : syracuseStep 2122179 = 3183269) B3183269
theorem B2685889 : Blo 2121435 2685889 := bbase (se 2 (by rfl) ⟨1007208, by rfl⟩ : syracuseStep 2685889 = 2014417) (by norm_num)
theorem B3581185 : Blo 2121435 3581185 := bstep (se 2 (by rfl) ⟨1342944, by rfl⟩ : syracuseStep 3581185 = 2685889) B2685889
theorem B4774913 : Blo 2121435 4774913 := bstep (se 2 (by rfl) ⟨1790592, by rfl⟩ : syracuseStep 4774913 = 3581185) B3581185
theorem B3183275 : Blo 2121435 3183275 := bstep (se 1 (by rfl) ⟨2387456, by rfl⟩ : syracuseStep 3183275 = 4774913) B4774913
theorem B2122183 : Blo 2121435 2122183 := bstep (se 1 (by rfl) ⟨1591637, by rfl⟩ : syracuseStep 2122183 = 3183275) B3183275
theorem B2387461 : Blo 2121435 2387461 := bbase (se 4 (by rfl) ⟨223824, by rfl⟩ : syracuseStep 2387461 = 447649) (by norm_num)
theorem B3183281 : Blo 2121435 3183281 := bstep (se 2 (by rfl) ⟨1193730, by rfl⟩ : syracuseStep 3183281 = 2387461) B2387461
theorem B2122187 : Blo 2121435 2122187 := bstep (se 1 (by rfl) ⟨1591640, by rfl⟩ : syracuseStep 2122187 = 3183281) B3183281
theorem B3021637 : Blo 2121435 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B4028849 : Blo 2121435 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B2685899 : Blo 2121435 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B7162397 : Blo 2121435 7162397 := bstep (se 3 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 7162397 = 2685899) B2685899
theorem B4774931 : Blo 2121435 4774931 := bstep (se 1 (by rfl) ⟨3581198, by rfl⟩ : syracuseStep 4774931 = 7162397) B7162397
theorem B3183287 : Blo 2121435 3183287 := bstep (se 1 (by rfl) ⟨2387465, by rfl⟩ : syracuseStep 3183287 = 4774931) B4774931
theorem B2122191 : Blo 2121435 2122191 := bstep (se 1 (by rfl) ⟨1591643, by rfl⟩ : syracuseStep 2122191 = 3183287) B3183287
theorem B3183293 : Blo 2121435 3183293 := bbase (se 3 (by rfl) ⟨596867, by rfl⟩ : syracuseStep 3183293 = 1193735) (by norm_num)
theorem B2122195 : Blo 2121435 2122195 := bstep (se 1 (by rfl) ⟨1591646, by rfl⟩ : syracuseStep 2122195 = 3183293) B3183293
theorem B4774949 : Blo 2121435 4774949 := bbase (se 4 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 4774949 = 895303) (by norm_num)
theorem B3183299 : Blo 2121435 3183299 := bstep (se 1 (by rfl) ⟨2387474, by rfl⟩ : syracuseStep 3183299 = 4774949) B4774949
theorem B2122199 : Blo 2121435 2122199 := bstep (se 1 (by rfl) ⟨1591649, by rfl⟩ : syracuseStep 2122199 = 3183299) B3183299
theorem B5371829 : Blo 2121435 5371829 := bbase (se 5 (by rfl) ⟨251804, by rfl⟩ : syracuseStep 5371829 = 503609) (by norm_num)
theorem B3581219 : Blo 2121435 3581219 := bstep (se 1 (by rfl) ⟨2685914, by rfl⟩ : syracuseStep 3581219 = 5371829) B5371829
theorem B2387479 : Blo 2121435 2387479 := bstep (se 1 (by rfl) ⟨1790609, by rfl⟩ : syracuseStep 2387479 = 3581219) B3581219
theorem B3183305 : Blo 2121435 3183305 := bstep (se 2 (by rfl) ⟨1193739, by rfl⟩ : syracuseStep 3183305 = 2387479) B2387479
theorem B2122203 : Blo 2121435 2122203 := bstep (se 1 (by rfl) ⟨1591652, by rfl⟩ : syracuseStep 2122203 = 3183305) B3183305
theorem B4302325 : Blo 2121435 4302325 := bbase (se 5 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 4302325 = 403343) (by norm_num)
theorem B5736433 : Blo 2121435 5736433 := bstep (se 2 (by rfl) ⟨2151162, by rfl⟩ : syracuseStep 5736433 = 4302325) B4302325
theorem B7648577 : Blo 2121435 7648577 := bstep (se 2 (by rfl) ⟨2868216, by rfl⟩ : syracuseStep 7648577 = 5736433) B5736433
theorem B5099051 : Blo 2121435 5099051 := bstep (se 1 (by rfl) ⟨3824288, by rfl⟩ : syracuseStep 5099051 = 7648577) B7648577
theorem B13597469 : Blo 2121435 13597469 := bstep (se 3 (by rfl) ⟨2549525, by rfl⟩ : syracuseStep 13597469 = 5099051) B5099051
theorem B9064979 : Blo 2121435 9064979 := bstep (se 1 (by rfl) ⟨6798734, by rfl⟩ : syracuseStep 9064979 = 13597469) B13597469
theorem B6043319 : Blo 2121435 6043319 := bstep (se 1 (by rfl) ⟨4532489, by rfl⟩ : syracuseStep 6043319 = 9064979) B9064979
theorem B4028879 : Blo 2121435 4028879 := bstep (se 1 (by rfl) ⟨3021659, by rfl⟩ : syracuseStep 4028879 = 6043319) B6043319
theorem B10743677 : Blo 2121435 10743677 := bstep (se 3 (by rfl) ⟨2014439, by rfl⟩ : syracuseStep 10743677 = 4028879) B4028879
theorem B7162451 : Blo 2121435 7162451 := bstep (se 1 (by rfl) ⟨5371838, by rfl⟩ : syracuseStep 7162451 = 10743677) B10743677
theorem B4774967 : Blo 2121435 4774967 := bstep (se 1 (by rfl) ⟨3581225, by rfl⟩ : syracuseStep 4774967 = 7162451) B7162451
theorem B3183311 : Blo 2121435 3183311 := bstep (se 1 (by rfl) ⟨2387483, by rfl⟩ : syracuseStep 3183311 = 4774967) B4774967
theorem B2122207 : Blo 2121435 2122207 := bstep (se 1 (by rfl) ⟨1591655, by rfl⟩ : syracuseStep 2122207 = 3183311) B3183311
theorem B3183317 : Blo 2121435 3183317 := bbase (se 7 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 3183317 = 74609) (by norm_num)
theorem B2122211 : Blo 2121435 2122211 := bstep (se 1 (by rfl) ⟨1591658, by rfl⟩ : syracuseStep 2122211 = 3183317) B3183317
theorem B3630101 : Blo 2121435 3630101 := bbase (se 6 (by rfl) ⟨85080, by rfl⟩ : syracuseStep 3630101 = 170161) (by norm_num)
theorem B38721077 : Blo 2121435 38721077 := bstep (se 5 (by rfl) ⟨1815050, by rfl⟩ : syracuseStep 38721077 = 3630101) B3630101
theorem B25814051 : Blo 2121435 25814051 := bstep (se 1 (by rfl) ⟨19360538, by rfl⟩ : syracuseStep 25814051 = 38721077) B38721077
theorem B17209367 : Blo 2121435 17209367 := bstep (se 1 (by rfl) ⟨12907025, by rfl⟩ : syracuseStep 17209367 = 25814051) B25814051
theorem B11472911 : Blo 2121435 11472911 := bstep (se 1 (by rfl) ⟨8604683, by rfl⟩ : syracuseStep 11472911 = 17209367) B17209367
theorem B7648607 : Blo 2121435 7648607 := bstep (se 1 (by rfl) ⟨5736455, by rfl⟩ : syracuseStep 7648607 = 11472911) B11472911
theorem B5099071 : Blo 2121435 5099071 := bstep (se 1 (by rfl) ⟨3824303, by rfl⟩ : syracuseStep 5099071 = 7648607) B7648607
theorem B6798761 : Blo 2121435 6798761 := bstep (se 2 (by rfl) ⟨2549535, by rfl⟩ : syracuseStep 6798761 = 5099071) B5099071
theorem B4532507 : Blo 2121435 4532507 := bstep (se 1 (by rfl) ⟨3399380, by rfl⟩ : syracuseStep 4532507 = 6798761) B6798761
theorem B3021671 : Blo 2121435 3021671 := bstep (se 1 (by rfl) ⟨2266253, by rfl⟩ : syracuseStep 3021671 = 4532507) B4532507
theorem B8057789 : Blo 2121435 8057789 := bstep (se 3 (by rfl) ⟨1510835, by rfl⟩ : syracuseStep 8057789 = 3021671) B3021671
theorem B5371859 : Blo 2121435 5371859 := bstep (se 1 (by rfl) ⟨4028894, by rfl⟩ : syracuseStep 5371859 = 8057789) B8057789
theorem B3581239 : Blo 2121435 3581239 := bstep (se 1 (by rfl) ⟨2685929, by rfl⟩ : syracuseStep 3581239 = 5371859) B5371859
theorem B4774985 : Blo 2121435 4774985 := bstep (se 2 (by rfl) ⟨1790619, by rfl⟩ : syracuseStep 4774985 = 3581239) B3581239
theorem B3183323 : Blo 2121435 3183323 := bstep (se 1 (by rfl) ⟨2387492, by rfl⟩ : syracuseStep 3183323 = 4774985) B4774985
theorem B2122215 : Blo 2121435 2122215 := bstep (se 1 (by rfl) ⟨1591661, by rfl⟩ : syracuseStep 2122215 = 3183323) B3183323
theorem B2387497 : Blo 2121435 2387497 := bbase (se 2 (by rfl) ⟨895311, by rfl⟩ : syracuseStep 2387497 = 1790623) (by norm_num)
theorem B3183329 : Blo 2121435 3183329 := bstep (se 2 (by rfl) ⟨1193748, by rfl⟩ : syracuseStep 3183329 = 2387497) B2387497
theorem B2122219 : Blo 2121435 2122219 := bstep (se 1 (by rfl) ⟨1591664, by rfl⟩ : syracuseStep 2122219 = 3183329) B3183329
theorem B3824317 : Blo 2121435 3824317 := bbase (se 3 (by rfl) ⟨717059, by rfl⟩ : syracuseStep 3824317 = 1434119) (by norm_num)
theorem B20396357 : Blo 2121435 20396357 := bstep (se 4 (by rfl) ⟨1912158, by rfl⟩ : syracuseStep 20396357 = 3824317) B3824317
theorem B13597571 : Blo 2121435 13597571 := bstep (se 1 (by rfl) ⟨10198178, by rfl⟩ : syracuseStep 13597571 = 20396357) B20396357
theorem B9065047 : Blo 2121435 9065047 := bstep (se 1 (by rfl) ⟨6798785, by rfl⟩ : syracuseStep 9065047 = 13597571) B13597571
theorem B12086729 : Blo 2121435 12086729 := bstep (se 2 (by rfl) ⟨4532523, by rfl⟩ : syracuseStep 12086729 = 9065047) B9065047
theorem B8057819 : Blo 2121435 8057819 := bstep (se 1 (by rfl) ⟨6043364, by rfl⟩ : syracuseStep 8057819 = 12086729) B12086729
theorem B5371879 : Blo 2121435 5371879 := bstep (se 1 (by rfl) ⟨4028909, by rfl⟩ : syracuseStep 5371879 = 8057819) B8057819
theorem B7162505 : Blo 2121435 7162505 := bstep (se 2 (by rfl) ⟨2685939, by rfl⟩ : syracuseStep 7162505 = 5371879) B5371879
theorem B4775003 : Blo 2121435 4775003 := bstep (se 1 (by rfl) ⟨3581252, by rfl⟩ : syracuseStep 4775003 = 7162505) B7162505
theorem B3183335 : Blo 2121435 3183335 := bstep (se 1 (by rfl) ⟨2387501, by rfl⟩ : syracuseStep 3183335 = 4775003) B4775003
theorem B2122223 : Blo 2121435 2122223 := bstep (se 1 (by rfl) ⟨1591667, by rfl⟩ : syracuseStep 2122223 = 3183335) B3183335
theorem B3183341 : Blo 2121435 3183341 := bbase (se 3 (by rfl) ⟨596876, by rfl⟩ : syracuseStep 3183341 = 1193753) (by norm_num)
theorem B2122227 : Blo 2121435 2122227 := bstep (se 1 (by rfl) ⟨1591670, by rfl⟩ : syracuseStep 2122227 = 3183341) B3183341
theorem B4775021 : Blo 2121435 4775021 := bbase (se 3 (by rfl) ⟨895316, by rfl⟩ : syracuseStep 4775021 = 1790633) (by norm_num)
theorem B3183347 : Blo 2121435 3183347 := bstep (se 1 (by rfl) ⟨2387510, by rfl⟩ : syracuseStep 3183347 = 4775021) B4775021
theorem B2122231 : Blo 2121435 2122231 := bstep (se 1 (by rfl) ⟨1591673, by rfl⟩ : syracuseStep 2122231 = 3183347) B3183347
theorem B4028933 : Blo 2121435 4028933 := bbase (se 4 (by rfl) ⟨377712, by rfl⟩ : syracuseStep 4028933 = 755425) (by norm_num)
theorem B2685955 : Blo 2121435 2685955 := bstep (se 1 (by rfl) ⟨2014466, by rfl⟩ : syracuseStep 2685955 = 4028933) B4028933
theorem B3581273 : Blo 2121435 3581273 := bstep (se 2 (by rfl) ⟨1342977, by rfl⟩ : syracuseStep 3581273 = 2685955) B2685955
theorem B2387515 : Blo 2121435 2387515 := bstep (se 1 (by rfl) ⟨1790636, by rfl⟩ : syracuseStep 2387515 = 3581273) B3581273
theorem B3183353 : Blo 2121435 3183353 := bstep (se 2 (by rfl) ⟨1193757, by rfl⟩ : syracuseStep 3183353 = 2387515) B2387515
theorem B2122235 : Blo 2121435 2122235 := bstep (se 1 (by rfl) ⟨1591676, by rfl⟩ : syracuseStep 2122235 = 3183353) B3183353
theorem B2453113 : Blo 2121435 2453113 := bbase (se 2 (by rfl) ⟨919917, by rfl⟩ : syracuseStep 2453113 = 1839835) (by norm_num)
theorem B3270817 : Blo 2121435 3270817 := bstep (se 2 (by rfl) ⟨1226556, by rfl⟩ : syracuseStep 3270817 = 2453113) B2453113
theorem B4361089 : Blo 2121435 4361089 := bstep (se 2 (by rfl) ⟨1635408, by rfl⟩ : syracuseStep 4361089 = 3270817) B3270817
theorem B5814785 : Blo 2121435 5814785 := bstep (se 2 (by rfl) ⟨2180544, by rfl⟩ : syracuseStep 5814785 = 4361089) B4361089
theorem B15506093 : Blo 2121435 15506093 := bstep (se 3 (by rfl) ⟨2907392, by rfl⟩ : syracuseStep 15506093 = 5814785) B5814785
theorem B10337395 : Blo 2121435 10337395 := bstep (se 1 (by rfl) ⟨7753046, by rfl⟩ : syracuseStep 10337395 = 15506093) B15506093
theorem B13783193 : Blo 2121435 13783193 := bstep (se 2 (by rfl) ⟨5168697, by rfl⟩ : syracuseStep 13783193 = 10337395) B10337395
theorem B9188795 : Blo 2121435 9188795 := bstep (se 1 (by rfl) ⟨6891596, by rfl⟩ : syracuseStep 9188795 = 13783193) B13783193
theorem B6125863 : Blo 2121435 6125863 := bstep (se 1 (by rfl) ⟨4594397, by rfl⟩ : syracuseStep 6125863 = 9188795) B9188795
theorem B8167817 : Blo 2121435 8167817 := bstep (se 2 (by rfl) ⟨3062931, by rfl⟩ : syracuseStep 8167817 = 6125863) B6125863
theorem B21780845 : Blo 2121435 21780845 := bstep (se 3 (by rfl) ⟨4083908, by rfl⟩ : syracuseStep 21780845 = 8167817) B8167817
theorem B14520563 : Blo 2121435 14520563 := bstep (se 1 (by rfl) ⟨10890422, by rfl⟩ : syracuseStep 14520563 = 21780845) B21780845
theorem B9680375 : Blo 2121435 9680375 := bstep (se 1 (by rfl) ⟨7260281, by rfl⟩ : syracuseStep 9680375 = 14520563) B14520563
theorem B6453583 : Blo 2121435 6453583 := bstep (se 1 (by rfl) ⟨4840187, by rfl⟩ : syracuseStep 6453583 = 9680375) B9680375
theorem B34419109 : Blo 2121435 34419109 := bstep (se 4 (by rfl) ⟨3226791, by rfl⟩ : syracuseStep 34419109 = 6453583) B6453583
theorem B45892145 : Blo 2121435 45892145 := bstep (se 2 (by rfl) ⟨17209554, by rfl⟩ : syracuseStep 45892145 = 34419109) B34419109
theorem B30594763 : Blo 2121435 30594763 := bstep (se 1 (by rfl) ⟨22946072, by rfl⟩ : syracuseStep 30594763 = 45892145) B45892145
theorem B40793017 : Blo 2121435 40793017 := bstep (se 2 (by rfl) ⟨15297381, by rfl⟩ : syracuseStep 40793017 = 30594763) B30594763
theorem B54390689 : Blo 2121435 54390689 := bstep (se 2 (by rfl) ⟨20396508, by rfl⟩ : syracuseStep 54390689 = 40793017) B40793017
theorem B36260459 : Blo 2121435 36260459 := bstep (se 1 (by rfl) ⟨27195344, by rfl⟩ : syracuseStep 36260459 = 54390689) B54390689
theorem B24173639 : Blo 2121435 24173639 := bstep (se 1 (by rfl) ⟨18130229, by rfl⟩ : syracuseStep 24173639 = 36260459) B36260459
theorem B16115759 : Blo 2121435 16115759 := bstep (se 1 (by rfl) ⟨12086819, by rfl⟩ : syracuseStep 16115759 = 24173639) B24173639
theorem B10743839 : Blo 2121435 10743839 := bstep (se 1 (by rfl) ⟨8057879, by rfl⟩ : syracuseStep 10743839 = 16115759) B16115759
theorem B7162559 : Blo 2121435 7162559 := bstep (se 1 (by rfl) ⟨5371919, by rfl⟩ : syracuseStep 7162559 = 10743839) B10743839
theorem B4775039 : Blo 2121435 4775039 := bstep (se 1 (by rfl) ⟨3581279, by rfl⟩ : syracuseStep 4775039 = 7162559) B7162559
theorem B3183359 : Blo 2121435 3183359 := bstep (se 1 (by rfl) ⟨2387519, by rfl⟩ : syracuseStep 3183359 = 4775039) B4775039
theorem B2122239 : Blo 2121435 2122239 := bstep (se 1 (by rfl) ⟨1591679, by rfl⟩ : syracuseStep 2122239 = 3183359) B3183359
theorem B3183365 : Blo 2121435 3183365 := bbase (se 4 (by rfl) ⟨298440, by rfl⟩ : syracuseStep 3183365 = 596881) (by norm_num)
theorem B2122243 : Blo 2121435 2122243 := bstep (se 1 (by rfl) ⟨1591682, by rfl⟩ : syracuseStep 2122243 = 3183365) B3183365
theorem B3581293 : Blo 2121435 3581293 := bbase (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) (by norm_num)
theorem B4775057 : Blo 2121435 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B3183371 : Blo 2121435 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B2122247 : Blo 2121435 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2387533 : Blo 2121435 2387533 := bbase (se 3 (by rfl) ⟨447662, by rfl⟩ : syracuseStep 2387533 = 895325) (by norm_num)
theorem B3183377 : Blo 2121435 3183377 := bstep (se 2 (by rfl) ⟨1193766, by rfl⟩ : syracuseStep 3183377 = 2387533) B2387533
theorem B2122251 : Blo 2121435 2122251 := bstep (se 1 (by rfl) ⟨1591688, by rfl⟩ : syracuseStep 2122251 = 3183377) B3183377
theorem B7162613 : Blo 2121435 7162613 := bbase (se 5 (by rfl) ⟨335747, by rfl⟩ : syracuseStep 7162613 = 671495) (by norm_num)
theorem B4775075 : Blo 2121435 4775075 := bstep (se 1 (by rfl) ⟨3581306, by rfl⟩ : syracuseStep 4775075 = 7162613) B7162613
theorem B3183383 : Blo 2121435 3183383 := bstep (se 1 (by rfl) ⟨2387537, by rfl⟩ : syracuseStep 3183383 = 4775075) B4775075
theorem B2122255 : Blo 2121435 2122255 := bstep (se 1 (by rfl) ⟨1591691, by rfl⟩ : syracuseStep 2122255 = 3183383) B3183383
theorem B3183389 : Blo 2121435 3183389 := bbase (se 3 (by rfl) ⟨596885, by rfl⟩ : syracuseStep 3183389 = 1193771) (by norm_num)
theorem B2122259 : Blo 2121435 2122259 := bstep (se 1 (by rfl) ⟨1591694, by rfl⟩ : syracuseStep 2122259 = 3183389) B3183389
theorem B4775093 : Blo 2121435 4775093 := bbase (se 5 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 4775093 = 447665) (by norm_num)
theorem B3183395 : Blo 2121435 3183395 := bstep (se 1 (by rfl) ⟨2387546, by rfl⟩ : syracuseStep 3183395 = 4775093) B4775093
theorem B2122263 : Blo 2121435 2122263 := bstep (se 1 (by rfl) ⟨1591697, by rfl⟩ : syracuseStep 2122263 = 3183395) B3183395
theorem B2266309 : Blo 2121435 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B12086981 : Blo 2121435 12086981 := bstep (se 4 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 12086981 = 2266309) B2266309
theorem B8057987 : Blo 2121435 8057987 := bstep (se 1 (by rfl) ⟨6043490, by rfl⟩ : syracuseStep 8057987 = 12086981) B12086981
theorem B5371991 : Blo 2121435 5371991 := bstep (se 1 (by rfl) ⟨4028993, by rfl⟩ : syracuseStep 5371991 = 8057987) B8057987
theorem B3581327 : Blo 2121435 3581327 := bstep (se 1 (by rfl) ⟨2685995, by rfl⟩ : syracuseStep 3581327 = 5371991) B5371991
theorem B2387551 : Blo 2121435 2387551 := bstep (se 1 (by rfl) ⟨1790663, by rfl⟩ : syracuseStep 2387551 = 3581327) B3581327
theorem B3183401 : Blo 2121435 3183401 := bstep (se 2 (by rfl) ⟨1193775, by rfl⟩ : syracuseStep 3183401 = 2387551) B2387551
theorem B2122267 : Blo 2121435 2122267 := bstep (se 1 (by rfl) ⟨1591700, by rfl⟩ : syracuseStep 2122267 = 3183401) B3183401
theorem B2266313 : Blo 2121435 2266313 := bbase (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) (by norm_num)
theorem B6043501 : Blo 2121435 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B8058001 : Blo 2121435 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B10744001 : Blo 2121435 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B7162667 : Blo 2121435 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B4775111 : Blo 2121435 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B3183407 : Blo 2121435 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B2122271 : Blo 2121435 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B3183413 : Blo 2121435 3183413 := bbase (se 5 (by rfl) ⟨149222, by rfl⟩ : syracuseStep 3183413 = 298445) (by norm_num)
theorem B2122275 : Blo 2121435 2122275 := bstep (se 1 (by rfl) ⟨1591706, by rfl⟩ : syracuseStep 2122275 = 3183413) B3183413
theorem B5372021 : Blo 2121435 5372021 := bbase (se 5 (by rfl) ⟨251813, by rfl⟩ : syracuseStep 5372021 = 503627) (by norm_num)
theorem B3581347 : Blo 2121435 3581347 := bstep (se 1 (by rfl) ⟨2686010, by rfl⟩ : syracuseStep 3581347 = 5372021) B5372021
theorem B4775129 : Blo 2121435 4775129 := bstep (se 2 (by rfl) ⟨1790673, by rfl⟩ : syracuseStep 4775129 = 3581347) B3581347
theorem B3183419 : Blo 2121435 3183419 := bstep (se 1 (by rfl) ⟨2387564, by rfl⟩ : syracuseStep 3183419 = 4775129) B4775129
theorem B2122279 : Blo 2121435 2122279 := bstep (se 1 (by rfl) ⟨1591709, by rfl⟩ : syracuseStep 2122279 = 3183419) B3183419
theorem B2387569 : Blo 2121435 2387569 := bbase (se 2 (by rfl) ⟨895338, by rfl⟩ : syracuseStep 2387569 = 1790677) (by norm_num)
theorem B3183425 : Blo 2121435 3183425 := bstep (se 2 (by rfl) ⟨1193784, by rfl⟩ : syracuseStep 3183425 = 2387569) B2387569
theorem B2122283 : Blo 2121435 2122283 := bstep (se 1 (by rfl) ⟨1591712, by rfl⟩ : syracuseStep 2122283 = 3183425) B3183425
theorem B9680597 : Blo 2121435 9680597 := bbase (se 7 (by rfl) ⟨113444, by rfl⟩ : syracuseStep 9680597 = 226889) (by norm_num)
theorem B6453731 : Blo 2121435 6453731 := bstep (se 1 (by rfl) ⟨4840298, by rfl⟩ : syracuseStep 6453731 = 9680597) B9680597
theorem B4302487 : Blo 2121435 4302487 := bstep (se 1 (by rfl) ⟨3226865, by rfl⟩ : syracuseStep 4302487 = 6453731) B6453731
theorem B22946597 : Blo 2121435 22946597 := bstep (se 4 (by rfl) ⟨2151243, by rfl⟩ : syracuseStep 22946597 = 4302487) B4302487
theorem B15297731 : Blo 2121435 15297731 := bstep (se 1 (by rfl) ⟨11473298, by rfl⟩ : syracuseStep 15297731 = 22946597) B22946597
theorem B10198487 : Blo 2121435 10198487 := bstep (se 1 (by rfl) ⟨7648865, by rfl⟩ : syracuseStep 10198487 = 15297731) B15297731
theorem B6798991 : Blo 2121435 6798991 := bstep (se 1 (by rfl) ⟨5099243, by rfl⟩ : syracuseStep 6798991 = 10198487) B10198487
theorem B9065321 : Blo 2121435 9065321 := bstep (se 2 (by rfl) ⟨3399495, by rfl⟩ : syracuseStep 9065321 = 6798991) B6798991
theorem B6043547 : Blo 2121435 6043547 := bstep (se 1 (by rfl) ⟨4532660, by rfl⟩ : syracuseStep 6043547 = 9065321) B9065321
theorem B4029031 : Blo 2121435 4029031 := bstep (se 1 (by rfl) ⟨3021773, by rfl⟩ : syracuseStep 4029031 = 6043547) B6043547
theorem B5372041 : Blo 2121435 5372041 := bstep (se 2 (by rfl) ⟨2014515, by rfl⟩ : syracuseStep 5372041 = 4029031) B4029031
theorem B7162721 : Blo 2121435 7162721 := bstep (se 2 (by rfl) ⟨2686020, by rfl⟩ : syracuseStep 7162721 = 5372041) B5372041
theorem B4775147 : Blo 2121435 4775147 := bstep (se 1 (by rfl) ⟨3581360, by rfl⟩ : syracuseStep 4775147 = 7162721) B7162721
theorem B3183431 : Blo 2121435 3183431 := bstep (se 1 (by rfl) ⟨2387573, by rfl⟩ : syracuseStep 3183431 = 4775147) B4775147
theorem B2122287 : Blo 2121435 2122287 := bstep (se 1 (by rfl) ⟨1591715, by rfl⟩ : syracuseStep 2122287 = 3183431) B3183431
theorem B3183437 : Blo 2121435 3183437 := bbase (se 3 (by rfl) ⟨596894, by rfl⟩ : syracuseStep 3183437 = 1193789) (by norm_num)
theorem B2122291 : Blo 2121435 2122291 := bstep (se 1 (by rfl) ⟨1591718, by rfl⟩ : syracuseStep 2122291 = 3183437) B3183437
theorem B4775165 : Blo 2121435 4775165 := bbase (se 3 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 4775165 = 1790687) (by norm_num)
theorem B3183443 : Blo 2121435 3183443 := bstep (se 1 (by rfl) ⟨2387582, by rfl⟩ : syracuseStep 3183443 = 4775165) B4775165
theorem B2122295 : Blo 2121435 2122295 := bstep (se 1 (by rfl) ⟨1591721, by rfl⟩ : syracuseStep 2122295 = 3183443) B3183443
theorem B3581381 : Blo 2121435 3581381 := bbase (se 4 (by rfl) ⟨335754, by rfl⟩ : syracuseStep 3581381 = 671509) (by norm_num)
theorem B2387587 : Blo 2121435 2387587 := bstep (se 1 (by rfl) ⟨1790690, by rfl⟩ : syracuseStep 2387587 = 3581381) B3581381
theorem B3183449 : Blo 2121435 3183449 := bstep (se 2 (by rfl) ⟨1193793, by rfl⟩ : syracuseStep 3183449 = 2387587) B2387587
theorem B2122299 : Blo 2121435 2122299 := bstep (se 1 (by rfl) ⟨1591724, by rfl⟩ : syracuseStep 2122299 = 3183449) B3183449
theorem B16116245 : Blo 2121435 16116245 := bbase (se 6 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 16116245 = 755449) (by norm_num)
theorem B10744163 : Blo 2121435 10744163 := bstep (se 1 (by rfl) ⟨8058122, by rfl⟩ : syracuseStep 10744163 = 16116245) B16116245
theorem B7162775 : Blo 2121435 7162775 := bstep (se 1 (by rfl) ⟨5372081, by rfl⟩ : syracuseStep 7162775 = 10744163) B10744163
theorem B4775183 : Blo 2121435 4775183 := bstep (se 1 (by rfl) ⟨3581387, by rfl⟩ : syracuseStep 4775183 = 7162775) B7162775
theorem B3183455 : Blo 2121435 3183455 := bstep (se 1 (by rfl) ⟨2387591, by rfl⟩ : syracuseStep 3183455 = 4775183) B4775183
theorem B2122303 : Blo 2121435 2122303 := bstep (se 1 (by rfl) ⟨1591727, by rfl⟩ : syracuseStep 2122303 = 3183455) B3183455
theorem B3183461 : Blo 2121435 3183461 := bbase (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) (by norm_num)
theorem B2122307 : Blo 2121435 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B4029077 : Blo 2121435 4029077 := bbase (se 6 (by rfl) ⟨94431, by rfl⟩ : syracuseStep 4029077 = 188863) (by norm_num)
theorem B2686051 : Blo 2121435 2686051 := bstep (se 1 (by rfl) ⟨2014538, by rfl⟩ : syracuseStep 2686051 = 4029077) B4029077
theorem B3581401 : Blo 2121435 3581401 := bstep (se 2 (by rfl) ⟨1343025, by rfl⟩ : syracuseStep 3581401 = 2686051) B2686051
theorem B4775201 : Blo 2121435 4775201 := bstep (se 2 (by rfl) ⟨1790700, by rfl⟩ : syracuseStep 4775201 = 3581401) B3581401
theorem B3183467 : Blo 2121435 3183467 := bstep (se 1 (by rfl) ⟨2387600, by rfl⟩ : syracuseStep 3183467 = 4775201) B4775201
theorem B2122311 : Blo 2121435 2122311 := bstep (se 1 (by rfl) ⟨1591733, by rfl⟩ : syracuseStep 2122311 = 3183467) B3183467
theorem B2387605 : Blo 2121435 2387605 := bbase (se 6 (by rfl) ⟨55959, by rfl⟩ : syracuseStep 2387605 = 111919) (by norm_num)
theorem B3183473 : Blo 2121435 3183473 := bstep (se 2 (by rfl) ⟨1193802, by rfl⟩ : syracuseStep 3183473 = 2387605) B2387605
theorem B2122315 : Blo 2121435 2122315 := bstep (se 1 (by rfl) ⟨1591736, by rfl⟩ : syracuseStep 2122315 = 3183473) B3183473
theorem B2686061 : Blo 2121435 2686061 := bbase (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) (by norm_num)
theorem B7162829 : Blo 2121435 7162829 := bstep (se 3 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 7162829 = 2686061) B2686061
theorem B4775219 : Blo 2121435 4775219 := bstep (se 1 (by rfl) ⟨3581414, by rfl⟩ : syracuseStep 4775219 = 7162829) B7162829
theorem B3183479 : Blo 2121435 3183479 := bstep (se 1 (by rfl) ⟨2387609, by rfl⟩ : syracuseStep 3183479 = 4775219) B4775219
theorem B2122319 : Blo 2121435 2122319 := bstep (se 1 (by rfl) ⟨1591739, by rfl⟩ : syracuseStep 2122319 = 3183479) B3183479
theorem B3183485 : Blo 2121435 3183485 := bbase (se 3 (by rfl) ⟨596903, by rfl⟩ : syracuseStep 3183485 = 1193807) (by norm_num)
theorem B2122323 : Blo 2121435 2122323 := bstep (se 1 (by rfl) ⟨1591742, by rfl⟩ : syracuseStep 2122323 = 3183485) B3183485
theorem B4775237 : Blo 2121435 4775237 := bbase (se 4 (by rfl) ⟨447678, by rfl⟩ : syracuseStep 4775237 = 895357) (by norm_num)
theorem B3183491 : Blo 2121435 3183491 := bstep (se 1 (by rfl) ⟨2387618, by rfl⟩ : syracuseStep 3183491 = 4775237) B4775237
theorem B2122327 : Blo 2121435 2122327 := bstep (se 1 (by rfl) ⟨1591745, by rfl⟩ : syracuseStep 2122327 = 3183491) B3183491
theorem B2151289 : Blo 2121435 2151289 := bbase (se 2 (by rfl) ⟨806733, by rfl⟩ : syracuseStep 2151289 = 1613467) (by norm_num)
theorem B2868385 : Blo 2121435 2868385 := bstep (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) B2151289
theorem B3824513 : Blo 2121435 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B2549675 : Blo 2121435 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B6799133 : Blo 2121435 6799133 := bstep (se 3 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 6799133 = 2549675) B2549675
theorem B4532755 : Blo 2121435 4532755 := bstep (se 1 (by rfl) ⟨3399566, by rfl⟩ : syracuseStep 4532755 = 6799133) B6799133
theorem B6043673 : Blo 2121435 6043673 := bstep (se 2 (by rfl) ⟨2266377, by rfl⟩ : syracuseStep 6043673 = 4532755) B4532755
theorem B4029115 : Blo 2121435 4029115 := bstep (se 1 (by rfl) ⟨3021836, by rfl⟩ : syracuseStep 4029115 = 6043673) B6043673
theorem B5372153 : Blo 2121435 5372153 := bstep (se 2 (by rfl) ⟨2014557, by rfl⟩ : syracuseStep 5372153 = 4029115) B4029115
theorem B3581435 : Blo 2121435 3581435 := bstep (se 1 (by rfl) ⟨2686076, by rfl⟩ : syracuseStep 3581435 = 5372153) B5372153
theorem B2387623 : Blo 2121435 2387623 := bstep (se 1 (by rfl) ⟨1790717, by rfl⟩ : syracuseStep 2387623 = 3581435) B3581435
theorem B3183497 : Blo 2121435 3183497 := bstep (se 2 (by rfl) ⟨1193811, by rfl⟩ : syracuseStep 3183497 = 2387623) B2387623
theorem B2122331 : Blo 2121435 2122331 := bstep (se 1 (by rfl) ⟨1591748, by rfl⟩ : syracuseStep 2122331 = 3183497) B3183497
theorem B10744325 : Blo 2121435 10744325 := bbase (se 4 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 10744325 = 2014561) (by norm_num)
theorem B7162883 : Blo 2121435 7162883 := bstep (se 1 (by rfl) ⟨5372162, by rfl⟩ : syracuseStep 7162883 = 10744325) B10744325
theorem B4775255 : Blo 2121435 4775255 := bstep (se 1 (by rfl) ⟨3581441, by rfl⟩ : syracuseStep 4775255 = 7162883) B7162883
theorem B3183503 : Blo 2121435 3183503 := bstep (se 1 (by rfl) ⟨2387627, by rfl⟩ : syracuseStep 3183503 = 4775255) B4775255
theorem B2122335 : Blo 2121435 2122335 := bstep (se 1 (by rfl) ⟨1591751, by rfl⟩ : syracuseStep 2122335 = 3183503) B3183503
theorem B3183509 : Blo 2121435 3183509 := bbase (se 6 (by rfl) ⟨74613, by rfl⟩ : syracuseStep 3183509 = 149227) (by norm_num)
theorem B2122339 : Blo 2121435 2122339 := bstep (se 1 (by rfl) ⟨1591754, by rfl⟩ : syracuseStep 2122339 = 3183509) B3183509
theorem B12087413 : Blo 2121435 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B8058275 : Blo 2121435 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B5372183 : Blo 2121435 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B3581455 : Blo 2121435 3581455 := bstep (se 1 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 3581455 = 5372183) B5372183
theorem B4775273 : Blo 2121435 4775273 := bstep (se 2 (by rfl) ⟨1790727, by rfl⟩ : syracuseStep 4775273 = 3581455) B3581455
theorem B3183515 : Blo 2121435 3183515 := bstep (se 1 (by rfl) ⟨2387636, by rfl⟩ : syracuseStep 3183515 = 4775273) B4775273
theorem B2122343 : Blo 2121435 2122343 := bstep (se 1 (by rfl) ⟨1591757, by rfl⟩ : syracuseStep 2122343 = 3183515) B3183515
theorem B2387641 : Blo 2121435 2387641 := bbase (se 2 (by rfl) ⟨895365, by rfl⟩ : syracuseStep 2387641 = 1790731) (by norm_num)
theorem B3183521 : Blo 2121435 3183521 := bstep (se 2 (by rfl) ⟨1193820, by rfl⟩ : syracuseStep 3183521 = 2387641) B2387641
theorem B2122347 : Blo 2121435 2122347 := bstep (se 1 (by rfl) ⟨1591760, by rfl⟩ : syracuseStep 2122347 = 3183521) B3183521
theorem B4532797 : Blo 2121435 4532797 := bbase (se 3 (by rfl) ⟨849899, by rfl⟩ : syracuseStep 4532797 = 1699799) (by norm_num)
theorem B6043729 : Blo 2121435 6043729 := bstep (se 2 (by rfl) ⟨2266398, by rfl⟩ : syracuseStep 6043729 = 4532797) B4532797
theorem B8058305 : Blo 2121435 8058305 := bstep (se 2 (by rfl) ⟨3021864, by rfl⟩ : syracuseStep 8058305 = 6043729) B6043729
theorem B5372203 : Blo 2121435 5372203 := bstep (se 1 (by rfl) ⟨4029152, by rfl⟩ : syracuseStep 5372203 = 8058305) B8058305
theorem B7162937 : Blo 2121435 7162937 := bstep (se 2 (by rfl) ⟨2686101, by rfl⟩ : syracuseStep 7162937 = 5372203) B5372203
theorem B4775291 : Blo 2121435 4775291 := bstep (se 1 (by rfl) ⟨3581468, by rfl⟩ : syracuseStep 4775291 = 7162937) B7162937
theorem B3183527 : Blo 2121435 3183527 := bstep (se 1 (by rfl) ⟨2387645, by rfl⟩ : syracuseStep 3183527 = 4775291) B4775291
theorem B2122351 : Blo 2121435 2122351 := bstep (se 1 (by rfl) ⟨1591763, by rfl⟩ : syracuseStep 2122351 = 3183527) B3183527
theorem B3183533 : Blo 2121435 3183533 := bbase (se 3 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 3183533 = 1193825) (by norm_num)
theorem B2122355 : Blo 2121435 2122355 := bstep (se 1 (by rfl) ⟨1591766, by rfl⟩ : syracuseStep 2122355 = 3183533) B3183533
theorem B4775309 : Blo 2121435 4775309 := bbase (se 3 (by rfl) ⟨895370, by rfl⟩ : syracuseStep 4775309 = 1790741) (by norm_num)
theorem B3183539 : Blo 2121435 3183539 := bstep (se 1 (by rfl) ⟨2387654, by rfl⟩ : syracuseStep 3183539 = 4775309) B4775309
theorem B2122359 : Blo 2121435 2122359 := bstep (se 1 (by rfl) ⟨1591769, by rfl⟩ : syracuseStep 2122359 = 3183539) B3183539
theorem B2686117 : Blo 2121435 2686117 := bbase (se 4 (by rfl) ⟨251823, by rfl⟩ : syracuseStep 2686117 = 503647) (by norm_num)
theorem B3581489 : Blo 2121435 3581489 := bstep (se 2 (by rfl) ⟨1343058, by rfl⟩ : syracuseStep 3581489 = 2686117) B2686117
theorem B2387659 : Blo 2121435 2387659 := bstep (se 1 (by rfl) ⟨1790744, by rfl⟩ : syracuseStep 2387659 = 3581489) B3581489
theorem B3183545 : Blo 2121435 3183545 := bstep (se 2 (by rfl) ⟨1193829, by rfl⟩ : syracuseStep 3183545 = 2387659) B2387659
theorem B2122363 : Blo 2121435 2122363 := bstep (se 1 (by rfl) ⟨1591772, by rfl⟩ : syracuseStep 2122363 = 3183545) B3183545
theorem B29439125 : Blo 2121435 29439125 := bbase (se 6 (by rfl) ⟨689979, by rfl⟩ : syracuseStep 29439125 = 1379959) (by norm_num)
theorem B19626083 : Blo 2121435 19626083 := bstep (se 1 (by rfl) ⟨14719562, by rfl⟩ : syracuseStep 19626083 = 29439125) B29439125
theorem B13084055 : Blo 2121435 13084055 := bstep (se 1 (by rfl) ⟨9813041, by rfl⟩ : syracuseStep 13084055 = 19626083) B19626083
theorem B8722703 : Blo 2121435 8722703 := bstep (se 1 (by rfl) ⟨6542027, by rfl⟩ : syracuseStep 8722703 = 13084055) B13084055
theorem B5815135 : Blo 2121435 5815135 := bstep (se 1 (by rfl) ⟨4361351, by rfl⟩ : syracuseStep 5815135 = 8722703) B8722703
theorem B31014053 : Blo 2121435 31014053 := bstep (se 4 (by rfl) ⟨2907567, by rfl⟩ : syracuseStep 31014053 = 5815135) B5815135
theorem B20676035 : Blo 2121435 20676035 := bstep (se 1 (by rfl) ⟨15507026, by rfl⟩ : syracuseStep 20676035 = 31014053) B31014053
theorem B13784023 : Blo 2121435 13784023 := bstep (se 1 (by rfl) ⟨10338017, by rfl⟩ : syracuseStep 13784023 = 20676035) B20676035
theorem B73514789 : Blo 2121435 73514789 := bstep (se 4 (by rfl) ⟨6892011, by rfl⟩ : syracuseStep 73514789 = 13784023) B13784023
theorem B49009859 : Blo 2121435 49009859 := bstep (se 1 (by rfl) ⟨36757394, by rfl⟩ : syracuseStep 49009859 = 73514789) B73514789
theorem B32673239 : Blo 2121435 32673239 := bstep (se 1 (by rfl) ⟨24504929, by rfl⟩ : syracuseStep 32673239 = 49009859) B49009859
theorem B21782159 : Blo 2121435 21782159 := bstep (se 1 (by rfl) ⟨16336619, by rfl⟩ : syracuseStep 21782159 = 32673239) B32673239
theorem B14521439 : Blo 2121435 14521439 := bstep (se 1 (by rfl) ⟨10891079, by rfl⟩ : syracuseStep 14521439 = 21782159) B21782159
theorem B9680959 : Blo 2121435 9680959 := bstep (se 1 (by rfl) ⟨7260719, by rfl⟩ : syracuseStep 9680959 = 14521439) B14521439
theorem B12907945 : Blo 2121435 12907945 := bstep (se 2 (by rfl) ⟨4840479, by rfl⟩ : syracuseStep 12907945 = 9680959) B9680959
theorem B17210593 : Blo 2121435 17210593 := bstep (se 2 (by rfl) ⟨6453972, by rfl⟩ : syracuseStep 17210593 = 12907945) B12907945
theorem B22947457 : Blo 2121435 22947457 := bstep (se 2 (by rfl) ⟨8605296, by rfl⟩ : syracuseStep 22947457 = 17210593) B17210593
theorem B30596609 : Blo 2121435 30596609 := bstep (se 2 (by rfl) ⟨11473728, by rfl⟩ : syracuseStep 30596609 = 22947457) B22947457
theorem B20397739 : Blo 2121435 20397739 := bstep (se 1 (by rfl) ⟨15298304, by rfl⟩ : syracuseStep 20397739 = 30596609) B30596609
theorem B27196985 : Blo 2121435 27196985 := bstep (se 2 (by rfl) ⟨10198869, by rfl⟩ : syracuseStep 27196985 = 20397739) B20397739
theorem B18131323 : Blo 2121435 18131323 := bstep (se 1 (by rfl) ⟨13598492, by rfl⟩ : syracuseStep 18131323 = 27196985) B27196985
theorem B24175097 : Blo 2121435 24175097 := bstep (se 2 (by rfl) ⟨9065661, by rfl⟩ : syracuseStep 24175097 = 18131323) B18131323
theorem B16116731 : Blo 2121435 16116731 := bstep (se 1 (by rfl) ⟨12087548, by rfl⟩ : syracuseStep 16116731 = 24175097) B24175097
theorem B10744487 : Blo 2121435 10744487 := bstep (se 1 (by rfl) ⟨8058365, by rfl⟩ : syracuseStep 10744487 = 16116731) B16116731
theorem B7162991 : Blo 2121435 7162991 := bstep (se 1 (by rfl) ⟨5372243, by rfl⟩ : syracuseStep 7162991 = 10744487) B10744487
theorem B4775327 : Blo 2121435 4775327 := bstep (se 1 (by rfl) ⟨3581495, by rfl⟩ : syracuseStep 4775327 = 7162991) B7162991
theorem B3183551 : Blo 2121435 3183551 := bstep (se 1 (by rfl) ⟨2387663, by rfl⟩ : syracuseStep 3183551 = 4775327) B4775327
theorem B2122367 : Blo 2121435 2122367 := bstep (se 1 (by rfl) ⟨1591775, by rfl⟩ : syracuseStep 2122367 = 3183551) B3183551
theorem B3183557 : Blo 2121435 3183557 := bbase (se 4 (by rfl) ⟨298458, by rfl⟩ : syracuseStep 3183557 = 596917) (by norm_num)
theorem B2122371 : Blo 2121435 2122371 := bstep (se 1 (by rfl) ⟨1591778, by rfl⟩ : syracuseStep 2122371 = 3183557) B3183557
theorem B3581509 : Blo 2121435 3581509 := bbase (se 4 (by rfl) ⟨335766, by rfl⟩ : syracuseStep 3581509 = 671533) (by norm_num)
theorem B4775345 : Blo 2121435 4775345 := bstep (se 2 (by rfl) ⟨1790754, by rfl⟩ : syracuseStep 4775345 = 3581509) B3581509
theorem B3183563 : Blo 2121435 3183563 := bstep (se 1 (by rfl) ⟨2387672, by rfl⟩ : syracuseStep 3183563 = 4775345) B4775345
theorem B2122375 : Blo 2121435 2122375 := bstep (se 1 (by rfl) ⟨1591781, by rfl⟩ : syracuseStep 2122375 = 3183563) B3183563
theorem B2387677 : Blo 2121435 2387677 := bbase (se 3 (by rfl) ⟨447689, by rfl⟩ : syracuseStep 2387677 = 895379) (by norm_num)
theorem B3183569 : Blo 2121435 3183569 := bstep (se 2 (by rfl) ⟨1193838, by rfl⟩ : syracuseStep 3183569 = 2387677) B2387677
theorem B2122379 : Blo 2121435 2122379 := bstep (se 1 (by rfl) ⟨1591784, by rfl⟩ : syracuseStep 2122379 = 3183569) B3183569
theorem B7163045 : Blo 2121435 7163045 := bbase (se 4 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 7163045 = 1343071) (by norm_num)
theorem B4775363 : Blo 2121435 4775363 := bstep (se 1 (by rfl) ⟨3581522, by rfl⟩ : syracuseStep 4775363 = 7163045) B7163045
theorem B3183575 : Blo 2121435 3183575 := bstep (se 1 (by rfl) ⟨2387681, by rfl⟩ : syracuseStep 3183575 = 4775363) B4775363
theorem B2122383 : Blo 2121435 2122383 := bstep (se 1 (by rfl) ⟨1591787, by rfl⟩ : syracuseStep 2122383 = 3183575) B3183575
theorem B3183581 : Blo 2121435 3183581 := bbase (se 3 (by rfl) ⟨596921, by rfl⟩ : syracuseStep 3183581 = 1193843) (by norm_num)
theorem B2122387 : Blo 2121435 2122387 := bstep (se 1 (by rfl) ⟨1591790, by rfl⟩ : syracuseStep 2122387 = 3183581) B3183581
theorem B4775381 : Blo 2121435 4775381 := bbase (se 7 (by rfl) ⟨55961, by rfl⟩ : syracuseStep 4775381 = 111923) (by norm_num)
theorem B3183587 : Blo 2121435 3183587 := bstep (se 1 (by rfl) ⟨2387690, by rfl⟩ : syracuseStep 3183587 = 4775381) B4775381
theorem B2122391 : Blo 2121435 2122391 := bstep (se 1 (by rfl) ⟨1591793, by rfl⟩ : syracuseStep 2122391 = 3183587) B3183587
theorem B5445613 : Blo 2121435 5445613 := bbase (se 3 (by rfl) ⟨1021052, by rfl⟩ : syracuseStep 5445613 = 2042105) (by norm_num)
theorem B29043269 : Blo 2121435 29043269 := bstep (se 4 (by rfl) ⟨2722806, by rfl⟩ : syracuseStep 29043269 = 5445613) B5445613
theorem B19362179 : Blo 2121435 19362179 := bstep (se 1 (by rfl) ⟨14521634, by rfl⟩ : syracuseStep 19362179 = 29043269) B29043269
theorem B12908119 : Blo 2121435 12908119 := bstep (se 1 (by rfl) ⟨9681089, by rfl⟩ : syracuseStep 12908119 = 19362179) B19362179
theorem B17210825 : Blo 2121435 17210825 := bstep (se 2 (by rfl) ⟨6454059, by rfl⟩ : syracuseStep 17210825 = 12908119) B12908119
theorem B11473883 : Blo 2121435 11473883 := bstep (se 1 (by rfl) ⟨8605412, by rfl⟩ : syracuseStep 11473883 = 17210825) B17210825
theorem B7649255 : Blo 2121435 7649255 := bstep (se 1 (by rfl) ⟨5736941, by rfl⟩ : syracuseStep 7649255 = 11473883) B11473883
theorem B20398013 : Blo 2121435 20398013 := bstep (se 3 (by rfl) ⟨3824627, by rfl⟩ : syracuseStep 20398013 = 7649255) B7649255
theorem B13598675 : Blo 2121435 13598675 := bstep (se 1 (by rfl) ⟨10199006, by rfl⟩ : syracuseStep 13598675 = 20398013) B20398013
theorem B9065783 : Blo 2121435 9065783 := bstep (se 1 (by rfl) ⟨6799337, by rfl⟩ : syracuseStep 9065783 = 13598675) B13598675
theorem B6043855 : Blo 2121435 6043855 := bstep (se 1 (by rfl) ⟨4532891, by rfl⟩ : syracuseStep 6043855 = 9065783) B9065783
theorem B8058473 : Blo 2121435 8058473 := bstep (se 2 (by rfl) ⟨3021927, by rfl⟩ : syracuseStep 8058473 = 6043855) B6043855
theorem B5372315 : Blo 2121435 5372315 := bstep (se 1 (by rfl) ⟨4029236, by rfl⟩ : syracuseStep 5372315 = 8058473) B8058473
theorem B3581543 : Blo 2121435 3581543 := bstep (se 1 (by rfl) ⟨2686157, by rfl⟩ : syracuseStep 3581543 = 5372315) B5372315
theorem B2387695 : Blo 2121435 2387695 := bstep (se 1 (by rfl) ⟨1790771, by rfl⟩ : syracuseStep 2387695 = 3581543) B3581543
theorem B3183593 : Blo 2121435 3183593 := bstep (se 2 (by rfl) ⟨1193847, by rfl⟩ : syracuseStep 3183593 = 2387695) B2387695
theorem B2122395 : Blo 2121435 2122395 := bstep (se 1 (by rfl) ⟨1591796, by rfl⟩ : syracuseStep 2122395 = 3183593) B3183593
theorem B6799349 : Blo 2121435 6799349 := bbase (se 5 (by rfl) ⟨318719, by rfl⟩ : syracuseStep 6799349 = 637439) (by norm_num)
theorem B18131597 : Blo 2121435 18131597 := bstep (se 3 (by rfl) ⟨3399674, by rfl⟩ : syracuseStep 18131597 = 6799349) B6799349
theorem B12087731 : Blo 2121435 12087731 := bstep (se 1 (by rfl) ⟨9065798, by rfl⟩ : syracuseStep 12087731 = 18131597) B18131597
theorem B8058487 : Blo 2121435 8058487 := bstep (se 1 (by rfl) ⟨6043865, by rfl⟩ : syracuseStep 8058487 = 12087731) B12087731
theorem B10744649 : Blo 2121435 10744649 := bstep (se 2 (by rfl) ⟨4029243, by rfl⟩ : syracuseStep 10744649 = 8058487) B8058487
theorem B7163099 : Blo 2121435 7163099 := bstep (se 1 (by rfl) ⟨5372324, by rfl⟩ : syracuseStep 7163099 = 10744649) B10744649
theorem B4775399 : Blo 2121435 4775399 := bstep (se 1 (by rfl) ⟨3581549, by rfl⟩ : syracuseStep 4775399 = 7163099) B7163099
theorem B3183599 : Blo 2121435 3183599 := bstep (se 1 (by rfl) ⟨2387699, by rfl⟩ : syracuseStep 3183599 = 4775399) B4775399
theorem B2122399 : Blo 2121435 2122399 := bstep (se 1 (by rfl) ⟨1591799, by rfl⟩ : syracuseStep 2122399 = 3183599) B3183599
theorem B3183605 : Blo 2121435 3183605 := bbase (se 5 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 3183605 = 298463) (by norm_num)
theorem B2122403 : Blo 2121435 2122403 := bstep (se 1 (by rfl) ⟨1591802, by rfl⟩ : syracuseStep 2122403 = 3183605) B3183605
theorem B4532917 : Blo 2121435 4532917 := bbase (se 5 (by rfl) ⟨212480, by rfl⟩ : syracuseStep 4532917 = 424961) (by norm_num)
theorem B6043889 : Blo 2121435 6043889 := bstep (se 2 (by rfl) ⟨2266458, by rfl⟩ : syracuseStep 6043889 = 4532917) B4532917
theorem B4029259 : Blo 2121435 4029259 := bstep (se 1 (by rfl) ⟨3021944, by rfl⟩ : syracuseStep 4029259 = 6043889) B6043889
theorem B5372345 : Blo 2121435 5372345 := bstep (se 2 (by rfl) ⟨2014629, by rfl⟩ : syracuseStep 5372345 = 4029259) B4029259
theorem B3581563 : Blo 2121435 3581563 := bstep (se 1 (by rfl) ⟨2686172, by rfl⟩ : syracuseStep 3581563 = 5372345) B5372345
theorem B4775417 : Blo 2121435 4775417 := bstep (se 2 (by rfl) ⟨1790781, by rfl⟩ : syracuseStep 4775417 = 3581563) B3581563
theorem B3183611 : Blo 2121435 3183611 := bstep (se 1 (by rfl) ⟨2387708, by rfl⟩ : syracuseStep 3183611 = 4775417) B4775417
theorem B2122407 : Blo 2121435 2122407 := bstep (se 1 (by rfl) ⟨1591805, by rfl⟩ : syracuseStep 2122407 = 3183611) B3183611
theorem B2387713 : Blo 2121435 2387713 := bbase (se 2 (by rfl) ⟨895392, by rfl⟩ : syracuseStep 2387713 = 1790785) (by norm_num)
theorem B3183617 : Blo 2121435 3183617 := bstep (se 2 (by rfl) ⟨1193856, by rfl⟩ : syracuseStep 3183617 = 2387713) B2387713
theorem B2122411 : Blo 2121435 2122411 := bstep (se 1 (by rfl) ⟨1591808, by rfl⟩ : syracuseStep 2122411 = 3183617) B3183617
theorem B5372365 : Blo 2121435 5372365 := bbase (se 3 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 5372365 = 2014637) (by norm_num)
theorem B7163153 : Blo 2121435 7163153 := bstep (se 2 (by rfl) ⟨2686182, by rfl⟩ : syracuseStep 7163153 = 5372365) B5372365
theorem B4775435 : Blo 2121435 4775435 := bstep (se 1 (by rfl) ⟨3581576, by rfl⟩ : syracuseStep 4775435 = 7163153) B7163153
theorem B3183623 : Blo 2121435 3183623 := bstep (se 1 (by rfl) ⟨2387717, by rfl⟩ : syracuseStep 3183623 = 4775435) B4775435
theorem B2122415 : Blo 2121435 2122415 := bstep (se 1 (by rfl) ⟨1591811, by rfl⟩ : syracuseStep 2122415 = 3183623) B3183623
theorem B3183629 : Blo 2121435 3183629 := bbase (se 3 (by rfl) ⟨596930, by rfl⟩ : syracuseStep 3183629 = 1193861) (by norm_num)
theorem B2122419 : Blo 2121435 2122419 := bstep (se 1 (by rfl) ⟨1591814, by rfl⟩ : syracuseStep 2122419 = 3183629) B3183629
theorem B4775453 : Blo 2121435 4775453 := bbase (se 3 (by rfl) ⟨895397, by rfl⟩ : syracuseStep 4775453 = 1790795) (by norm_num)
theorem B3183635 : Blo 2121435 3183635 := bstep (se 1 (by rfl) ⟨2387726, by rfl⟩ : syracuseStep 3183635 = 4775453) B4775453
theorem B2122423 : Blo 2121435 2122423 := bstep (se 1 (by rfl) ⟨1591817, by rfl⟩ : syracuseStep 2122423 = 3183635) B3183635
theorem B3581597 : Blo 2121435 3581597 := bbase (se 3 (by rfl) ⟨671549, by rfl⟩ : syracuseStep 3581597 = 1343099) (by norm_num)
theorem B2387731 : Blo 2121435 2387731 := bstep (se 1 (by rfl) ⟨1790798, by rfl⟩ : syracuseStep 2387731 = 3581597) B3581597
theorem B3183641 : Blo 2121435 3183641 := bstep (se 2 (by rfl) ⟨1193865, by rfl⟩ : syracuseStep 3183641 = 2387731) B2387731
theorem B2122427 : Blo 2121435 2122427 := bstep (se 1 (by rfl) ⟨1591820, by rfl⟩ : syracuseStep 2122427 = 3183641) B3183641
theorem B4594813 : Blo 2121435 4594813 := bbase (se 3 (by rfl) ⟨861527, by rfl⟩ : syracuseStep 4594813 = 1723055) (by norm_num)
theorem B24505669 : Blo 2121435 24505669 := bstep (se 4 (by rfl) ⟨2297406, by rfl⟩ : syracuseStep 24505669 = 4594813) B4594813
theorem B32674225 : Blo 2121435 32674225 := bstep (se 2 (by rfl) ⟨12252834, by rfl⟩ : syracuseStep 32674225 = 24505669) B24505669
theorem B43565633 : Blo 2121435 43565633 := bstep (se 2 (by rfl) ⟨16337112, by rfl⟩ : syracuseStep 43565633 = 32674225) B32674225
theorem B29043755 : Blo 2121435 29043755 := bstep (se 1 (by rfl) ⟨21782816, by rfl⟩ : syracuseStep 29043755 = 43565633) B43565633
theorem B19362503 : Blo 2121435 19362503 := bstep (se 1 (by rfl) ⟨14521877, by rfl⟩ : syracuseStep 19362503 = 29043755) B29043755
theorem B12908335 : Blo 2121435 12908335 := bstep (se 1 (by rfl) ⟨9681251, by rfl⟩ : syracuseStep 12908335 = 19362503) B19362503
theorem B17211113 : Blo 2121435 17211113 := bstep (se 2 (by rfl) ⟨6454167, by rfl⟩ : syracuseStep 17211113 = 12908335) B12908335
theorem B11474075 : Blo 2121435 11474075 := bstep (se 1 (by rfl) ⟨8605556, by rfl⟩ : syracuseStep 11474075 = 17211113) B17211113
theorem B30597533 : Blo 2121435 30597533 := bstep (se 3 (by rfl) ⟨5737037, by rfl⟩ : syracuseStep 30597533 = 11474075) B11474075
theorem B20398355 : Blo 2121435 20398355 := bstep (se 1 (by rfl) ⟨15298766, by rfl⟩ : syracuseStep 20398355 = 30597533) B30597533
theorem B13598903 : Blo 2121435 13598903 := bstep (se 1 (by rfl) ⟨10199177, by rfl⟩ : syracuseStep 13598903 = 20398355) B20398355
theorem B9065935 : Blo 2121435 9065935 := bstep (se 1 (by rfl) ⟨6799451, by rfl⟩ : syracuseStep 9065935 = 13598903) B13598903
theorem B12087913 : Blo 2121435 12087913 := bstep (se 2 (by rfl) ⟨4532967, by rfl⟩ : syracuseStep 12087913 = 9065935) B9065935
theorem B16117217 : Blo 2121435 16117217 := bstep (se 2 (by rfl) ⟨6043956, by rfl⟩ : syracuseStep 16117217 = 12087913) B12087913
theorem B10744811 : Blo 2121435 10744811 := bstep (se 1 (by rfl) ⟨8058608, by rfl⟩ : syracuseStep 10744811 = 16117217) B16117217
theorem B7163207 : Blo 2121435 7163207 := bstep (se 1 (by rfl) ⟨5372405, by rfl⟩ : syracuseStep 7163207 = 10744811) B10744811
theorem B4775471 : Blo 2121435 4775471 := bstep (se 1 (by rfl) ⟨3581603, by rfl⟩ : syracuseStep 4775471 = 7163207) B7163207
theorem B3183647 : Blo 2121435 3183647 := bstep (se 1 (by rfl) ⟨2387735, by rfl⟩ : syracuseStep 3183647 = 4775471) B4775471
theorem B2122431 : Blo 2121435 2122431 := bstep (se 1 (by rfl) ⟨1591823, by rfl⟩ : syracuseStep 2122431 = 3183647) B3183647
theorem B3183653 : Blo 2121435 3183653 := bbase (se 4 (by rfl) ⟨298467, by rfl⟩ : syracuseStep 3183653 = 596935) (by norm_num)
theorem B2122435 : Blo 2121435 2122435 := bstep (se 1 (by rfl) ⟨1591826, by rfl⟩ : syracuseStep 2122435 = 3183653) B3183653
theorem B2686213 : Blo 2121435 2686213 := bbase (se 4 (by rfl) ⟨251832, by rfl⟩ : syracuseStep 2686213 = 503665) (by norm_num)
theorem B3581617 : Blo 2121435 3581617 := bstep (se 2 (by rfl) ⟨1343106, by rfl⟩ : syracuseStep 3581617 = 2686213) B2686213
theorem B4775489 : Blo 2121435 4775489 := bstep (se 2 (by rfl) ⟨1790808, by rfl⟩ : syracuseStep 4775489 = 3581617) B3581617
theorem B3183659 : Blo 2121435 3183659 := bstep (se 1 (by rfl) ⟨2387744, by rfl⟩ : syracuseStep 3183659 = 4775489) B4775489
theorem B2122439 : Blo 2121435 2122439 := bstep (se 1 (by rfl) ⟨1591829, by rfl⟩ : syracuseStep 2122439 = 3183659) B3183659
theorem B2387749 : Blo 2121435 2387749 := bbase (se 4 (by rfl) ⟨223851, by rfl⟩ : syracuseStep 2387749 = 447703) (by norm_num)
theorem B3183665 : Blo 2121435 3183665 := bstep (se 2 (by rfl) ⟨1193874, by rfl⟩ : syracuseStep 3183665 = 2387749) B2387749
theorem B2122443 : Blo 2121435 2122443 := bstep (se 1 (by rfl) ⟨1591832, by rfl⟩ : syracuseStep 2122443 = 3183665) B3183665
theorem B9066005 : Blo 2121435 9066005 := bbase (se 6 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 9066005 = 424969) (by norm_num)
theorem B6044003 : Blo 2121435 6044003 := bstep (se 1 (by rfl) ⟨4533002, by rfl⟩ : syracuseStep 6044003 = 9066005) B9066005
theorem B4029335 : Blo 2121435 4029335 := bstep (se 1 (by rfl) ⟨3022001, by rfl⟩ : syracuseStep 4029335 = 6044003) B6044003
theorem B2686223 : Blo 2121435 2686223 := bstep (se 1 (by rfl) ⟨2014667, by rfl⟩ : syracuseStep 2686223 = 4029335) B4029335
theorem B7163261 : Blo 2121435 7163261 := bstep (se 3 (by rfl) ⟨1343111, by rfl⟩ : syracuseStep 7163261 = 2686223) B2686223
theorem B4775507 : Blo 2121435 4775507 := bstep (se 1 (by rfl) ⟨3581630, by rfl⟩ : syracuseStep 4775507 = 7163261) B7163261
theorem B3183671 : Blo 2121435 3183671 := bstep (se 1 (by rfl) ⟨2387753, by rfl⟩ : syracuseStep 3183671 = 4775507) B4775507
theorem B2122447 : Blo 2121435 2122447 := bstep (se 1 (by rfl) ⟨1591835, by rfl⟩ : syracuseStep 2122447 = 3183671) B3183671
theorem B3183677 : Blo 2121435 3183677 := bbase (se 3 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 3183677 = 1193879) (by norm_num)
theorem B2122451 : Blo 2121435 2122451 := bstep (se 1 (by rfl) ⟨1591838, by rfl⟩ : syracuseStep 2122451 = 3183677) B3183677
theorem B4775525 : Blo 2121435 4775525 := bbase (se 4 (by rfl) ⟨447705, by rfl⟩ : syracuseStep 4775525 = 895411) (by norm_num)
theorem B3183683 : Blo 2121435 3183683 := bstep (se 1 (by rfl) ⟨2387762, by rfl⟩ : syracuseStep 3183683 = 4775525) B4775525
theorem B2122455 : Blo 2121435 2122455 := bstep (se 1 (by rfl) ⟨1591841, by rfl⟩ : syracuseStep 2122455 = 3183683) B3183683
theorem B5372477 : Blo 2121435 5372477 := bbase (se 3 (by rfl) ⟨1007339, by rfl⟩ : syracuseStep 5372477 = 2014679) (by norm_num)
theorem B3581651 : Blo 2121435 3581651 := bstep (se 1 (by rfl) ⟨2686238, by rfl⟩ : syracuseStep 3581651 = 5372477) B5372477
theorem B2387767 : Blo 2121435 2387767 := bstep (se 1 (by rfl) ⟨1790825, by rfl⟩ : syracuseStep 2387767 = 3581651) B3581651
theorem B3183689 : Blo 2121435 3183689 := bstep (se 2 (by rfl) ⟨1193883, by rfl⟩ : syracuseStep 3183689 = 2387767) B2387767
theorem B2122459 : Blo 2121435 2122459 := bstep (se 1 (by rfl) ⟨1591844, by rfl⟩ : syracuseStep 2122459 = 3183689) B3183689
theorem B4029365 : Blo 2121435 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B10744973 : Blo 2121435 10744973 := bstep (se 3 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 10744973 = 4029365) B4029365
theorem B7163315 : Blo 2121435 7163315 := bstep (se 1 (by rfl) ⟨5372486, by rfl⟩ : syracuseStep 7163315 = 10744973) B10744973
theorem B4775543 : Blo 2121435 4775543 := bstep (se 1 (by rfl) ⟨3581657, by rfl⟩ : syracuseStep 4775543 = 7163315) B7163315
theorem B3183695 : Blo 2121435 3183695 := bstep (se 1 (by rfl) ⟨2387771, by rfl⟩ : syracuseStep 3183695 = 4775543) B4775543
theorem B2122463 : Blo 2121435 2122463 := bstep (se 1 (by rfl) ⟨1591847, by rfl⟩ : syracuseStep 2122463 = 3183695) B3183695
theorem B3183701 : Blo 2121435 3183701 := bbase (se 8 (by rfl) ⟨18654, by rfl⟩ : syracuseStep 3183701 = 37309) (by norm_num)
theorem B2122467 : Blo 2121435 2122467 := bstep (se 1 (by rfl) ⟨1591850, by rfl⟩ : syracuseStep 2122467 = 3183701) B3183701
theorem B11474293 : Blo 2121435 11474293 := bbase (se 5 (by rfl) ⟨537857, by rfl⟩ : syracuseStep 11474293 = 1075715) (by norm_num)
theorem B15299057 : Blo 2121435 15299057 := bstep (se 2 (by rfl) ⟨5737146, by rfl⟩ : syracuseStep 15299057 = 11474293) B11474293
theorem B10199371 : Blo 2121435 10199371 := bstep (se 1 (by rfl) ⟨7649528, by rfl⟩ : syracuseStep 10199371 = 15299057) B15299057
theorem B13599161 : Blo 2121435 13599161 := bstep (se 2 (by rfl) ⟨5099685, by rfl⟩ : syracuseStep 13599161 = 10199371) B10199371
theorem B9066107 : Blo 2121435 9066107 := bstep (se 1 (by rfl) ⟨6799580, by rfl⟩ : syracuseStep 9066107 = 13599161) B13599161
theorem B6044071 : Blo 2121435 6044071 := bstep (se 1 (by rfl) ⟨4533053, by rfl⟩ : syracuseStep 6044071 = 9066107) B9066107
theorem B8058761 : Blo 2121435 8058761 := bstep (se 2 (by rfl) ⟨3022035, by rfl⟩ : syracuseStep 8058761 = 6044071) B6044071
theorem B5372507 : Blo 2121435 5372507 := bstep (se 1 (by rfl) ⟨4029380, by rfl⟩ : syracuseStep 5372507 = 8058761) B8058761
theorem B3581671 : Blo 2121435 3581671 := bstep (se 1 (by rfl) ⟨2686253, by rfl⟩ : syracuseStep 3581671 = 5372507) B5372507
theorem B4775561 : Blo 2121435 4775561 := bstep (se 2 (by rfl) ⟨1790835, by rfl⟩ : syracuseStep 4775561 = 3581671) B3581671
theorem B3183707 : Blo 2121435 3183707 := bstep (se 1 (by rfl) ⟨2387780, by rfl⟩ : syracuseStep 3183707 = 4775561) B4775561
theorem B2122471 : Blo 2121435 2122471 := bstep (se 1 (by rfl) ⟨1591853, by rfl⟩ : syracuseStep 2122471 = 3183707) B3183707
theorem B2387785 : Blo 2121435 2387785 := bbase (se 2 (by rfl) ⟨895419, by rfl⟩ : syracuseStep 2387785 = 1790839) (by norm_num)
theorem B3183713 : Blo 2121435 3183713 := bstep (se 2 (by rfl) ⟨1193892, by rfl⟩ : syracuseStep 3183713 = 2387785) B2387785
theorem B2122475 : Blo 2121435 2122475 := bstep (se 1 (by rfl) ⟨1591856, by rfl⟩ : syracuseStep 2122475 = 3183713) B3183713
theorem B3147437 : Blo 2121435 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B8393165 : Blo 2121435 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B5595443 : Blo 2121435 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B3730295 : Blo 2121435 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B2486863 : Blo 2121435 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B3315817 : Blo 2121435 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B4421089 : Blo 2121435 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B5894785 : Blo 2121435 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B31438853 : Blo 2121435 31438853 := bstep (se 4 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 31438853 = 5894785) B5894785
theorem B20959235 : Blo 2121435 20959235 := bstep (se 1 (by rfl) ⟨15719426, by rfl⟩ : syracuseStep 20959235 = 31438853) B31438853
theorem B13972823 : Blo 2121435 13972823 := bstep (se 1 (by rfl) ⟨10479617, by rfl⟩ : syracuseStep 13972823 = 20959235) B20959235
theorem B9315215 : Blo 2121435 9315215 := bstep (se 1 (by rfl) ⟨6986411, by rfl⟩ : syracuseStep 9315215 = 13972823) B13972823
theorem B6210143 : Blo 2121435 6210143 := bstep (se 1 (by rfl) ⟨4657607, by rfl⟩ : syracuseStep 6210143 = 9315215) B9315215
theorem B4140095 : Blo 2121435 4140095 := bstep (se 1 (by rfl) ⟨3105071, by rfl⟩ : syracuseStep 4140095 = 6210143) B6210143
theorem B44161013 : Blo 2121435 44161013 := bstep (se 5 (by rfl) ⟨2070047, by rfl⟩ : syracuseStep 44161013 = 4140095) B4140095
theorem B29440675 : Blo 2121435 29440675 := bstep (se 1 (by rfl) ⟨22080506, by rfl⟩ : syracuseStep 29440675 = 44161013) B44161013
theorem B39254233 : Blo 2121435 39254233 := bstep (se 2 (by rfl) ⟨14720337, by rfl⟩ : syracuseStep 39254233 = 29440675) B29440675
theorem B52338977 : Blo 2121435 52338977 := bstep (se 2 (by rfl) ⟨19627116, by rfl⟩ : syracuseStep 52338977 = 39254233) B39254233
theorem B34892651 : Blo 2121435 34892651 := bstep (se 1 (by rfl) ⟨26169488, by rfl⟩ : syracuseStep 34892651 = 52338977) B52338977
theorem B93047069 : Blo 2121435 93047069 := bstep (se 3 (by rfl) ⟨17446325, by rfl⟩ : syracuseStep 93047069 = 34892651) B34892651
theorem B248125517 : Blo 2121435 248125517 := bstep (se 3 (by rfl) ⟨46523534, by rfl⟩ : syracuseStep 248125517 = 93047069) B93047069
theorem B165417011 : Blo 2121435 165417011 := bstep (se 1 (by rfl) ⟨124062758, by rfl⟩ : syracuseStep 165417011 = 248125517) B248125517
theorem B110278007 : Blo 2121435 110278007 := bstep (se 1 (by rfl) ⟨82708505, by rfl⟩ : syracuseStep 110278007 = 165417011) B165417011
theorem B73518671 : Blo 2121435 73518671 := bstep (se 1 (by rfl) ⟨55139003, by rfl⟩ : syracuseStep 73518671 = 110278007) B110278007
theorem B49012447 : Blo 2121435 49012447 := bstep (se 1 (by rfl) ⟨36759335, by rfl⟩ : syracuseStep 49012447 = 73518671) B73518671
theorem B65349929 : Blo 2121435 65349929 := bstep (se 2 (by rfl) ⟨24506223, by rfl⟩ : syracuseStep 65349929 = 49012447) B49012447
theorem B43566619 : Blo 2121435 43566619 := bstep (se 1 (by rfl) ⟨32674964, by rfl⟩ : syracuseStep 43566619 = 65349929) B65349929
theorem B58088825 : Blo 2121435 58088825 := bstep (se 2 (by rfl) ⟨21783309, by rfl⟩ : syracuseStep 58088825 = 43566619) B43566619
theorem B38725883 : Blo 2121435 38725883 := bstep (se 1 (by rfl) ⟨29044412, by rfl⟩ : syracuseStep 38725883 = 58088825) B58088825
theorem B25817255 : Blo 2121435 25817255 := bstep (se 1 (by rfl) ⟨19362941, by rfl⟩ : syracuseStep 25817255 = 38725883) B38725883
theorem B17211503 : Blo 2121435 17211503 := bstep (se 1 (by rfl) ⟨12908627, by rfl⟩ : syracuseStep 17211503 = 25817255) B25817255
theorem B11474335 : Blo 2121435 11474335 := bstep (se 1 (by rfl) ⟨8605751, by rfl⟩ : syracuseStep 11474335 = 17211503) B17211503
theorem B15299113 : Blo 2121435 15299113 := bstep (se 2 (by rfl) ⟨5737167, by rfl⟩ : syracuseStep 15299113 = 11474335) B11474335
theorem B20398817 : Blo 2121435 20398817 := bstep (se 2 (by rfl) ⟨7649556, by rfl⟩ : syracuseStep 20398817 = 15299113) B15299113
theorem B13599211 : Blo 2121435 13599211 := bstep (se 1 (by rfl) ⟨10199408, by rfl⟩ : syracuseStep 13599211 = 20398817) B20398817
theorem B18132281 : Blo 2121435 18132281 := bstep (se 2 (by rfl) ⟨6799605, by rfl⟩ : syracuseStep 18132281 = 13599211) B13599211
theorem B12088187 : Blo 2121435 12088187 := bstep (se 1 (by rfl) ⟨9066140, by rfl⟩ : syracuseStep 12088187 = 18132281) B18132281
theorem B8058791 : Blo 2121435 8058791 := bstep (se 1 (by rfl) ⟨6044093, by rfl⟩ : syracuseStep 8058791 = 12088187) B12088187
theorem B5372527 : Blo 2121435 5372527 := bstep (se 1 (by rfl) ⟨4029395, by rfl⟩ : syracuseStep 5372527 = 8058791) B8058791
theorem B7163369 : Blo 2121435 7163369 := bstep (se 2 (by rfl) ⟨2686263, by rfl⟩ : syracuseStep 7163369 = 5372527) B5372527
theorem B4775579 : Blo 2121435 4775579 := bstep (se 1 (by rfl) ⟨3581684, by rfl⟩ : syracuseStep 4775579 = 7163369) B7163369
theorem B3183719 : Blo 2121435 3183719 := bstep (se 1 (by rfl) ⟨2387789, by rfl⟩ : syracuseStep 3183719 = 4775579) B4775579
theorem B2122479 : Blo 2121435 2122479 := bstep (se 1 (by rfl) ⟨1591859, by rfl⟩ : syracuseStep 2122479 = 3183719) B3183719
theorem B3183725 : Blo 2121435 3183725 := bbase (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) (by norm_num)
theorem B2122483 : Blo 2121435 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B4775597 : Blo 2121435 4775597 := bbase (se 3 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 4775597 = 1790849) (by norm_num)
theorem B3183731 : Blo 2121435 3183731 := bstep (se 1 (by rfl) ⟨2387798, by rfl⟩ : syracuseStep 3183731 = 4775597) B4775597
theorem B2122487 : Blo 2121435 2122487 := bstep (se 1 (by rfl) ⟨1591865, by rfl⟩ : syracuseStep 2122487 = 3183731) B3183731
theorem B4906813 : Blo 2121435 4906813 := bbase (se 3 (by rfl) ⟨920027, by rfl⟩ : syracuseStep 4906813 = 1840055) (by norm_num)
theorem B6542417 : Blo 2121435 6542417 := bstep (se 2 (by rfl) ⟨2453406, by rfl⟩ : syracuseStep 6542417 = 4906813) B4906813
theorem B4361611 : Blo 2121435 4361611 := bstep (se 1 (by rfl) ⟨3271208, by rfl⟩ : syracuseStep 4361611 = 6542417) B6542417
theorem B5815481 : Blo 2121435 5815481 := bstep (se 2 (by rfl) ⟨2180805, by rfl⟩ : syracuseStep 5815481 = 4361611) B4361611
theorem B15507949 : Blo 2121435 15507949 := bstep (se 3 (by rfl) ⟨2907740, by rfl⟩ : syracuseStep 15507949 = 5815481) B5815481
theorem B20677265 : Blo 2121435 20677265 := bstep (se 2 (by rfl) ⟨7753974, by rfl⟩ : syracuseStep 20677265 = 15507949) B15507949
theorem B13784843 : Blo 2121435 13784843 := bstep (se 1 (by rfl) ⟨10338632, by rfl⟩ : syracuseStep 13784843 = 20677265) B20677265
theorem B9189895 : Blo 2121435 9189895 := bstep (se 1 (by rfl) ⟨6892421, by rfl⟩ : syracuseStep 9189895 = 13784843) B13784843
theorem B12253193 : Blo 2121435 12253193 := bstep (se 2 (by rfl) ⟨4594947, by rfl⟩ : syracuseStep 12253193 = 9189895) B9189895
theorem B8168795 : Blo 2121435 8168795 := bstep (se 1 (by rfl) ⟨6126596, by rfl⟩ : syracuseStep 8168795 = 12253193) B12253193
theorem B5445863 : Blo 2121435 5445863 := bstep (se 1 (by rfl) ⟨4084397, by rfl⟩ : syracuseStep 5445863 = 8168795) B8168795
theorem B3630575 : Blo 2121435 3630575 := bstep (se 1 (by rfl) ⟨2722931, by rfl⟩ : syracuseStep 3630575 = 5445863) B5445863
theorem B2420383 : Blo 2121435 2420383 := bstep (se 1 (by rfl) ⟨1815287, by rfl⟩ : syracuseStep 2420383 = 3630575) B3630575
theorem B3227177 : Blo 2121435 3227177 := bstep (se 2 (by rfl) ⟨1210191, by rfl⟩ : syracuseStep 3227177 = 2420383) B2420383
theorem B2151451 : Blo 2121435 2151451 := bstep (se 1 (by rfl) ⟨1613588, by rfl⟩ : syracuseStep 2151451 = 3227177) B3227177
theorem B11474405 : Blo 2121435 11474405 := bstep (se 4 (by rfl) ⟨1075725, by rfl⟩ : syracuseStep 11474405 = 2151451) B2151451
theorem B7649603 : Blo 2121435 7649603 := bstep (se 1 (by rfl) ⟨5737202, by rfl⟩ : syracuseStep 7649603 = 11474405) B11474405
theorem B5099735 : Blo 2121435 5099735 := bstep (se 1 (by rfl) ⟨3824801, by rfl⟩ : syracuseStep 5099735 = 7649603) B7649603
theorem B3399823 : Blo 2121435 3399823 := bstep (se 1 (by rfl) ⟨2549867, by rfl⟩ : syracuseStep 3399823 = 5099735) B5099735
theorem B4533097 : Blo 2121435 4533097 := bstep (se 2 (by rfl) ⟨1699911, by rfl⟩ : syracuseStep 4533097 = 3399823) B3399823
theorem B6044129 : Blo 2121435 6044129 := bstep (se 2 (by rfl) ⟨2266548, by rfl⟩ : syracuseStep 6044129 = 4533097) B4533097
theorem B4029419 : Blo 2121435 4029419 := bstep (se 1 (by rfl) ⟨3022064, by rfl⟩ : syracuseStep 4029419 = 6044129) B6044129
theorem B2686279 : Blo 2121435 2686279 := bstep (se 1 (by rfl) ⟨2014709, by rfl⟩ : syracuseStep 2686279 = 4029419) B4029419
theorem B3581705 : Blo 2121435 3581705 := bstep (se 2 (by rfl) ⟨1343139, by rfl⟩ : syracuseStep 3581705 = 2686279) B2686279
theorem B2387803 : Blo 2121435 2387803 := bstep (se 1 (by rfl) ⟨1790852, by rfl⟩ : syracuseStep 2387803 = 3581705) B3581705
theorem B3183737 : Blo 2121435 3183737 := bstep (se 2 (by rfl) ⟨1193901, by rfl⟩ : syracuseStep 3183737 = 2387803) B2387803
theorem B2122491 : Blo 2121435 2122491 := bstep (se 1 (by rfl) ⟨1591868, by rfl⟩ : syracuseStep 2122491 = 3183737) B3183737
theorem B220557653 : Blo 2121435 220557653 := bbase (se 10 (by rfl) ⟨323082, by rfl⟩ : syracuseStep 220557653 = 646165) (by norm_num)
theorem B147038435 : Blo 2121435 147038435 := bstep (se 1 (by rfl) ⟨110278826, by rfl⟩ : syracuseStep 147038435 = 220557653) B220557653
theorem B98025623 : Blo 2121435 98025623 := bstep (se 1 (by rfl) ⟨73519217, by rfl⟩ : syracuseStep 98025623 = 147038435) B147038435
theorem B65350415 : Blo 2121435 65350415 := bstep (se 1 (by rfl) ⟨49012811, by rfl⟩ : syracuseStep 65350415 = 98025623) B98025623
theorem B43566943 : Blo 2121435 43566943 := bstep (se 1 (by rfl) ⟨32675207, by rfl⟩ : syracuseStep 43566943 = 65350415) B65350415
theorem B58089257 : Blo 2121435 58089257 := bstep (se 2 (by rfl) ⟨21783471, by rfl⟩ : syracuseStep 58089257 = 43566943) B43566943
theorem B38726171 : Blo 2121435 38726171 := bstep (se 1 (by rfl) ⟨29044628, by rfl⟩ : syracuseStep 38726171 = 58089257) B58089257
theorem B25817447 : Blo 2121435 25817447 := bstep (se 1 (by rfl) ⟨19363085, by rfl⟩ : syracuseStep 25817447 = 38726171) B38726171
theorem B17211631 : Blo 2121435 17211631 := bstep (se 1 (by rfl) ⟨12908723, by rfl⟩ : syracuseStep 17211631 = 25817447) B25817447
theorem B22948841 : Blo 2121435 22948841 := bstep (se 2 (by rfl) ⟨8605815, by rfl⟩ : syracuseStep 22948841 = 17211631) B17211631
theorem B15299227 : Blo 2121435 15299227 := bstep (se 1 (by rfl) ⟨11474420, by rfl⟩ : syracuseStep 15299227 = 22948841) B22948841
theorem B20398969 : Blo 2121435 20398969 := bstep (se 2 (by rfl) ⟨7649613, by rfl⟩ : syracuseStep 20398969 = 15299227) B15299227
theorem B27198625 : Blo 2121435 27198625 := bstep (se 2 (by rfl) ⟨10199484, by rfl⟩ : syracuseStep 27198625 = 20398969) B20398969
theorem B36264833 : Blo 2121435 36264833 := bstep (se 2 (by rfl) ⟨13599312, by rfl⟩ : syracuseStep 36264833 = 27198625) B27198625
theorem B24176555 : Blo 2121435 24176555 := bstep (se 1 (by rfl) ⟨18132416, by rfl⟩ : syracuseStep 24176555 = 36264833) B36264833
theorem B16117703 : Blo 2121435 16117703 := bstep (se 1 (by rfl) ⟨12088277, by rfl⟩ : syracuseStep 16117703 = 24176555) B24176555
theorem B10745135 : Blo 2121435 10745135 := bstep (se 1 (by rfl) ⟨8058851, by rfl⟩ : syracuseStep 10745135 = 16117703) B16117703
theorem B7163423 : Blo 2121435 7163423 := bstep (se 1 (by rfl) ⟨5372567, by rfl⟩ : syracuseStep 7163423 = 10745135) B10745135
theorem B4775615 : Blo 2121435 4775615 := bstep (se 1 (by rfl) ⟨3581711, by rfl⟩ : syracuseStep 4775615 = 7163423) B7163423
theorem B3183743 : Blo 2121435 3183743 := bstep (se 1 (by rfl) ⟨2387807, by rfl⟩ : syracuseStep 3183743 = 4775615) B4775615
theorem B2122495 : Blo 2121435 2122495 := bstep (se 1 (by rfl) ⟨1591871, by rfl⟩ : syracuseStep 2122495 = 3183743) B3183743
theorem B3183749 : Blo 2121435 3183749 := bbase (se 4 (by rfl) ⟨298476, by rfl⟩ : syracuseStep 3183749 = 596953) (by norm_num)
theorem B2122499 : Blo 2121435 2122499 := bstep (se 1 (by rfl) ⟨1591874, by rfl⟩ : syracuseStep 2122499 = 3183749) B3183749
theorem B3581725 : Blo 2121435 3581725 := bbase (se 3 (by rfl) ⟨671573, by rfl⟩ : syracuseStep 3581725 = 1343147) (by norm_num)
theorem B4775633 : Blo 2121435 4775633 := bstep (se 2 (by rfl) ⟨1790862, by rfl⟩ : syracuseStep 4775633 = 3581725) B3581725
theorem B3183755 : Blo 2121435 3183755 := bstep (se 1 (by rfl) ⟨2387816, by rfl⟩ : syracuseStep 3183755 = 4775633) B4775633
theorem B2122503 : Blo 2121435 2122503 := bstep (se 1 (by rfl) ⟨1591877, by rfl⟩ : syracuseStep 2122503 = 3183755) B3183755
theorem B2387821 : Blo 2121435 2387821 := bbase (se 3 (by rfl) ⟨447716, by rfl⟩ : syracuseStep 2387821 = 895433) (by norm_num)
theorem B3183761 : Blo 2121435 3183761 := bstep (se 2 (by rfl) ⟨1193910, by rfl⟩ : syracuseStep 3183761 = 2387821) B2387821
theorem B2122507 : Blo 2121435 2122507 := bstep (se 1 (by rfl) ⟨1591880, by rfl⟩ : syracuseStep 2122507 = 3183761) B3183761
theorem B7163477 : Blo 2121435 7163477 := bbase (se 8 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 7163477 = 83947) (by norm_num)
theorem B4775651 : Blo 2121435 4775651 := bstep (se 1 (by rfl) ⟨3581738, by rfl⟩ : syracuseStep 4775651 = 7163477) B7163477
theorem B3183767 : Blo 2121435 3183767 := bstep (se 1 (by rfl) ⟨2387825, by rfl⟩ : syracuseStep 3183767 = 4775651) B4775651
theorem B2122511 : Blo 2121435 2122511 := bstep (se 1 (by rfl) ⟨1591883, by rfl⟩ : syracuseStep 2122511 = 3183767) B3183767
theorem B3183773 : Blo 2121435 3183773 := bbase (se 3 (by rfl) ⟨596957, by rfl⟩ : syracuseStep 3183773 = 1193915) (by norm_num)
theorem B2122515 : Blo 2121435 2122515 := bstep (se 1 (by rfl) ⟨1591886, by rfl⟩ : syracuseStep 2122515 = 3183773) B3183773
theorem B4775669 : Blo 2121435 4775669 := bbase (se 5 (by rfl) ⟨223859, by rfl⟩ : syracuseStep 4775669 = 447719) (by norm_num)
theorem B3183779 : Blo 2121435 3183779 := bstep (se 1 (by rfl) ⟨2387834, by rfl⟩ : syracuseStep 3183779 = 4775669) B4775669
theorem B2122519 : Blo 2121435 2122519 := bstep (se 1 (by rfl) ⟨1591889, by rfl⟩ : syracuseStep 2122519 = 3183779) B3183779
theorem B10199621 : Blo 2121435 10199621 := bbase (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) (by norm_num)
theorem B27198989 : Blo 2121435 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B18132659 : Blo 2121435 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B12088439 : Blo 2121435 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B8058959 : Blo 2121435 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B5372639 : Blo 2121435 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B3581759 : Blo 2121435 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B2387839 : Blo 2121435 2387839 := bstep (se 1 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 2387839 = 3581759) B3581759
theorem B3183785 : Blo 2121435 3183785 := bstep (se 2 (by rfl) ⟨1193919, by rfl⟩ : syracuseStep 3183785 = 2387839) B2387839
theorem B2122523 : Blo 2121435 2122523 := bstep (se 1 (by rfl) ⟨1591892, by rfl⟩ : syracuseStep 2122523 = 3183785) B3183785
theorem B4533173 : Blo 2121435 4533173 := bbase (se 5 (by rfl) ⟨212492, by rfl⟩ : syracuseStep 4533173 = 424985) (by norm_num)
theorem B3022115 : Blo 2121435 3022115 := bstep (se 1 (by rfl) ⟨2266586, by rfl⟩ : syracuseStep 3022115 = 4533173) B4533173
theorem B8058973 : Blo 2121435 8058973 := bstep (se 3 (by rfl) ⟨1511057, by rfl⟩ : syracuseStep 8058973 = 3022115) B3022115
theorem B10745297 : Blo 2121435 10745297 := bstep (se 2 (by rfl) ⟨4029486, by rfl⟩ : syracuseStep 10745297 = 8058973) B8058973
theorem B7163531 : Blo 2121435 7163531 := bstep (se 1 (by rfl) ⟨5372648, by rfl⟩ : syracuseStep 7163531 = 10745297) B10745297
theorem B4775687 : Blo 2121435 4775687 := bstep (se 1 (by rfl) ⟨3581765, by rfl⟩ : syracuseStep 4775687 = 7163531) B7163531
theorem B3183791 : Blo 2121435 3183791 := bstep (se 1 (by rfl) ⟨2387843, by rfl⟩ : syracuseStep 3183791 = 4775687) B4775687
theorem B2122527 : Blo 2121435 2122527 := bstep (se 1 (by rfl) ⟨1591895, by rfl⟩ : syracuseStep 2122527 = 3183791) B3183791
theorem B3183797 : Blo 2121435 3183797 := bbase (se 5 (by rfl) ⟨149240, by rfl⟩ : syracuseStep 3183797 = 298481) (by norm_num)
theorem B2122531 : Blo 2121435 2122531 := bstep (se 1 (by rfl) ⟨1591898, by rfl⟩ : syracuseStep 2122531 = 3183797) B3183797
theorem B5372669 : Blo 2121435 5372669 := bbase (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) (by norm_num)
theorem B3581779 : Blo 2121435 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B4775705 : Blo 2121435 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B3183803 : Blo 2121435 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B2122535 : Blo 2121435 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B2387857 : Blo 2121435 2387857 := bbase (se 2 (by rfl) ⟨895446, by rfl⟩ : syracuseStep 2387857 = 1790893) (by norm_num)
theorem B3183809 : Blo 2121435 3183809 := bstep (se 2 (by rfl) ⟨1193928, by rfl⟩ : syracuseStep 3183809 = 2387857) B2387857
theorem B2122539 : Blo 2121435 2122539 := bstep (se 1 (by rfl) ⟨1591904, by rfl⟩ : syracuseStep 2122539 = 3183809) B3183809
theorem B4029517 : Blo 2121435 4029517 := bbase (se 3 (by rfl) ⟨755534, by rfl⟩ : syracuseStep 4029517 = 1511069) (by norm_num)
theorem B5372689 : Blo 2121435 5372689 := bstep (se 2 (by rfl) ⟨2014758, by rfl⟩ : syracuseStep 5372689 = 4029517) B4029517
theorem B7163585 : Blo 2121435 7163585 := bstep (se 2 (by rfl) ⟨2686344, by rfl⟩ : syracuseStep 7163585 = 5372689) B5372689
theorem B4775723 : Blo 2121435 4775723 := bstep (se 1 (by rfl) ⟨3581792, by rfl⟩ : syracuseStep 4775723 = 7163585) B7163585
theorem B3183815 : Blo 2121435 3183815 := bstep (se 1 (by rfl) ⟨2387861, by rfl⟩ : syracuseStep 3183815 = 4775723) B4775723
theorem B2122543 : Blo 2121435 2122543 := bstep (se 1 (by rfl) ⟨1591907, by rfl⟩ : syracuseStep 2122543 = 3183815) B3183815
theorem B3183821 : Blo 2121435 3183821 := bbase (se 3 (by rfl) ⟨596966, by rfl⟩ : syracuseStep 3183821 = 1193933) (by norm_num)
theorem B2122547 : Blo 2121435 2122547 := bstep (se 1 (by rfl) ⟨1591910, by rfl⟩ : syracuseStep 2122547 = 3183821) B3183821
theorem B4775741 : Blo 2121435 4775741 := bbase (se 3 (by rfl) ⟨895451, by rfl⟩ : syracuseStep 4775741 = 1790903) (by norm_num)
theorem B3183827 : Blo 2121435 3183827 := bstep (se 1 (by rfl) ⟨2387870, by rfl⟩ : syracuseStep 3183827 = 4775741) B4775741
theorem B2122551 : Blo 2121435 2122551 := bstep (se 1 (by rfl) ⟨1591913, by rfl⟩ : syracuseStep 2122551 = 3183827) B3183827
theorem B3581813 : Blo 2121435 3581813 := bbase (se 5 (by rfl) ⟨167897, by rfl⟩ : syracuseStep 3581813 = 335795) (by norm_num)
theorem B2387875 : Blo 2121435 2387875 := bstep (se 1 (by rfl) ⟨1790906, by rfl⟩ : syracuseStep 2387875 = 3581813) B3581813
theorem B3183833 : Blo 2121435 3183833 := bstep (se 2 (by rfl) ⟨1193937, by rfl⟩ : syracuseStep 3183833 = 2387875) B2387875
theorem B2122555 : Blo 2121435 2122555 := bstep (se 1 (by rfl) ⟨1591916, by rfl⟩ : syracuseStep 2122555 = 3183833) B3183833
theorem B24507157 : Blo 2121435 24507157 := bbase (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) (by norm_num)
theorem B32676209 : Blo 2121435 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B21784139 : Blo 2121435 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B14522759 : Blo 2121435 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B9681839 : Blo 2121435 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B6454559 : Blo 2121435 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B4303039 : Blo 2121435 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B5737385 : Blo 2121435 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B3824923 : Blo 2121435 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B5099897 : Blo 2121435 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B3399931 : Blo 2121435 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B4533241 : Blo 2121435 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B6044321 : Blo 2121435 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B16118189 : Blo 2121435 16118189 := bstep (se 3 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 16118189 = 6044321) B6044321
theorem B10745459 : Blo 2121435 10745459 := bstep (se 1 (by rfl) ⟨8059094, by rfl⟩ : syracuseStep 10745459 = 16118189) B16118189
theorem B7163639 : Blo 2121435 7163639 := bstep (se 1 (by rfl) ⟨5372729, by rfl⟩ : syracuseStep 7163639 = 10745459) B10745459
theorem B4775759 : Blo 2121435 4775759 := bstep (se 1 (by rfl) ⟨3581819, by rfl⟩ : syracuseStep 4775759 = 7163639) B7163639
theorem B3183839 : Blo 2121435 3183839 := bstep (se 1 (by rfl) ⟨2387879, by rfl⟩ : syracuseStep 3183839 = 4775759) B4775759
theorem B2122559 : Blo 2121435 2122559 := bstep (se 1 (by rfl) ⟨1591919, by rfl⟩ : syracuseStep 2122559 = 3183839) B3183839
theorem B3183845 : Blo 2121435 3183845 := bbase (se 4 (by rfl) ⟨298485, by rfl⟩ : syracuseStep 3183845 = 596971) (by norm_num)
theorem B2122563 : Blo 2121435 2122563 := bstep (se 1 (by rfl) ⟨1591922, by rfl⟩ : syracuseStep 2122563 = 3183845) B3183845
theorem B5099917 : Blo 2121435 5099917 := bbase (se 3 (by rfl) ⟨956234, by rfl⟩ : syracuseStep 5099917 = 1912469) (by norm_num)
theorem B6799889 : Blo 2121435 6799889 := bstep (se 2 (by rfl) ⟨2549958, by rfl⟩ : syracuseStep 6799889 = 5099917) B5099917
theorem B4533259 : Blo 2121435 4533259 := bstep (se 1 (by rfl) ⟨3399944, by rfl⟩ : syracuseStep 4533259 = 6799889) B6799889
theorem B6044345 : Blo 2121435 6044345 := bstep (se 2 (by rfl) ⟨2266629, by rfl⟩ : syracuseStep 6044345 = 4533259) B4533259
theorem B4029563 : Blo 2121435 4029563 := bstep (se 1 (by rfl) ⟨3022172, by rfl⟩ : syracuseStep 4029563 = 6044345) B6044345
theorem B2686375 : Blo 2121435 2686375 := bstep (se 1 (by rfl) ⟨2014781, by rfl⟩ : syracuseStep 2686375 = 4029563) B4029563
theorem B3581833 : Blo 2121435 3581833 := bstep (se 2 (by rfl) ⟨1343187, by rfl⟩ : syracuseStep 3581833 = 2686375) B2686375
theorem B4775777 : Blo 2121435 4775777 := bstep (se 2 (by rfl) ⟨1790916, by rfl⟩ : syracuseStep 4775777 = 3581833) B3581833
theorem B3183851 : Blo 2121435 3183851 := bstep (se 1 (by rfl) ⟨2387888, by rfl⟩ : syracuseStep 3183851 = 4775777) B4775777
theorem B2122567 : Blo 2121435 2122567 := bstep (se 1 (by rfl) ⟨1591925, by rfl⟩ : syracuseStep 2122567 = 3183851) B3183851
theorem B2387893 : Blo 2121435 2387893 := bbase (se 5 (by rfl) ⟨111932, by rfl⟩ : syracuseStep 2387893 = 223865) (by norm_num)
theorem B3183857 : Blo 2121435 3183857 := bstep (se 2 (by rfl) ⟨1193946, by rfl⟩ : syracuseStep 3183857 = 2387893) B2387893
theorem B2122571 : Blo 2121435 2122571 := bstep (se 1 (by rfl) ⟨1591928, by rfl⟩ : syracuseStep 2122571 = 3183857) B3183857
theorem B2686385 : Blo 2121435 2686385 := bbase (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) (by norm_num)
theorem B7163693 : Blo 2121435 7163693 := bstep (se 3 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 7163693 = 2686385) B2686385
theorem B4775795 : Blo 2121435 4775795 := bstep (se 1 (by rfl) ⟨3581846, by rfl⟩ : syracuseStep 4775795 = 7163693) B7163693
theorem B3183863 : Blo 2121435 3183863 := bstep (se 1 (by rfl) ⟨2387897, by rfl⟩ : syracuseStep 3183863 = 4775795) B4775795
theorem B2122575 : Blo 2121435 2122575 := bstep (se 1 (by rfl) ⟨1591931, by rfl⟩ : syracuseStep 2122575 = 3183863) B3183863
theorem B3183869 : Blo 2121435 3183869 := bbase (se 3 (by rfl) ⟨596975, by rfl⟩ : syracuseStep 3183869 = 1193951) (by norm_num)
theorem B2122579 : Blo 2121435 2122579 := bstep (se 1 (by rfl) ⟨1591934, by rfl⟩ : syracuseStep 2122579 = 3183869) B3183869
theorem B4775813 : Blo 2121435 4775813 := bbase (se 4 (by rfl) ⟨447732, by rfl⟩ : syracuseStep 4775813 = 895465) (by norm_num)
theorem B3183875 : Blo 2121435 3183875 := bstep (se 1 (by rfl) ⟨2387906, by rfl⟩ : syracuseStep 3183875 = 4775813) B4775813
theorem B2122583 : Blo 2121435 2122583 := bstep (se 1 (by rfl) ⟨1591937, by rfl⟩ : syracuseStep 2122583 = 3183875) B3183875
theorem B5446109 : Blo 2121435 5446109 := bbase (se 3 (by rfl) ⟨1021145, by rfl⟩ : syracuseStep 5446109 = 2042291) (by norm_num)
theorem B3630739 : Blo 2121435 3630739 := bstep (se 1 (by rfl) ⟨2723054, by rfl⟩ : syracuseStep 3630739 = 5446109) B5446109
theorem B4840985 : Blo 2121435 4840985 := bstep (se 2 (by rfl) ⟨1815369, by rfl⟩ : syracuseStep 4840985 = 3630739) B3630739
theorem B12909293 : Blo 2121435 12909293 := bstep (se 3 (by rfl) ⟨2420492, by rfl⟩ : syracuseStep 12909293 = 4840985) B4840985
theorem B8606195 : Blo 2121435 8606195 := bstep (se 1 (by rfl) ⟨6454646, by rfl⟩ : syracuseStep 8606195 = 12909293) B12909293
theorem B5737463 : Blo 2121435 5737463 := bstep (se 1 (by rfl) ⟨4303097, by rfl⟩ : syracuseStep 5737463 = 8606195) B8606195
theorem B3824975 : Blo 2121435 3824975 := bstep (se 1 (by rfl) ⟨2868731, by rfl⟩ : syracuseStep 3824975 = 5737463) B5737463
theorem B2549983 : Blo 2121435 2549983 := bstep (se 1 (by rfl) ⟨1912487, by rfl⟩ : syracuseStep 2549983 = 3824975) B3824975
theorem B3399977 : Blo 2121435 3399977 := bstep (se 2 (by rfl) ⟨1274991, by rfl⟩ : syracuseStep 3399977 = 2549983) B2549983
theorem B2266651 : Blo 2121435 2266651 := bstep (se 1 (by rfl) ⟨1699988, by rfl⟩ : syracuseStep 2266651 = 3399977) B3399977
theorem B3022201 : Blo 2121435 3022201 := bstep (se 2 (by rfl) ⟨1133325, by rfl⟩ : syracuseStep 3022201 = 2266651) B2266651
theorem B4029601 : Blo 2121435 4029601 := bstep (se 2 (by rfl) ⟨1511100, by rfl⟩ : syracuseStep 4029601 = 3022201) B3022201
theorem B5372801 : Blo 2121435 5372801 := bstep (se 2 (by rfl) ⟨2014800, by rfl⟩ : syracuseStep 5372801 = 4029601) B4029601
theorem B3581867 : Blo 2121435 3581867 := bstep (se 1 (by rfl) ⟨2686400, by rfl⟩ : syracuseStep 3581867 = 5372801) B5372801
theorem B2387911 : Blo 2121435 2387911 := bstep (se 1 (by rfl) ⟨1790933, by rfl⟩ : syracuseStep 2387911 = 3581867) B3581867
theorem B3183881 : Blo 2121435 3183881 := bstep (se 2 (by rfl) ⟨1193955, by rfl⟩ : syracuseStep 3183881 = 2387911) B2387911
theorem B2122587 : Blo 2121435 2122587 := bstep (se 1 (by rfl) ⟨1591940, by rfl⟩ : syracuseStep 2122587 = 3183881) B3183881
theorem B10745621 : Blo 2121435 10745621 := bbase (se 6 (by rfl) ⟨251850, by rfl⟩ : syracuseStep 10745621 = 503701) (by norm_num)
theorem B7163747 : Blo 2121435 7163747 := bstep (se 1 (by rfl) ⟨5372810, by rfl⟩ : syracuseStep 7163747 = 10745621) B10745621
theorem B4775831 : Blo 2121435 4775831 := bstep (se 1 (by rfl) ⟨3581873, by rfl⟩ : syracuseStep 4775831 = 7163747) B7163747
theorem B3183887 : Blo 2121435 3183887 := bstep (se 1 (by rfl) ⟨2387915, by rfl⟩ : syracuseStep 3183887 = 4775831) B4775831
theorem B2122591 : Blo 2121435 2122591 := bstep (se 1 (by rfl) ⟨1591943, by rfl⟩ : syracuseStep 2122591 = 3183887) B3183887
theorem B3183893 : Blo 2121435 3183893 := bbase (se 6 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 3183893 = 149245) (by norm_num)
theorem B2122595 : Blo 2121435 2122595 := bstep (se 1 (by rfl) ⟨1591946, by rfl⟩ : syracuseStep 2122595 = 3183893) B3183893
theorem B30599957 : Blo 2121435 30599957 := bbase (se 6 (by rfl) ⟨717186, by rfl⟩ : syracuseStep 30599957 = 1434373) (by norm_num)
theorem B20399971 : Blo 2121435 20399971 := bstep (se 1 (by rfl) ⟨15299978, by rfl⟩ : syracuseStep 20399971 = 30599957) B30599957
theorem B27199961 : Blo 2121435 27199961 := bstep (se 2 (by rfl) ⟨10199985, by rfl⟩ : syracuseStep 27199961 = 20399971) B20399971
theorem B18133307 : Blo 2121435 18133307 := bstep (se 1 (by rfl) ⟨13599980, by rfl⟩ : syracuseStep 18133307 = 27199961) B27199961
theorem B12088871 : Blo 2121435 12088871 := bstep (se 1 (by rfl) ⟨9066653, by rfl⟩ : syracuseStep 12088871 = 18133307) B18133307
theorem B8059247 : Blo 2121435 8059247 := bstep (se 1 (by rfl) ⟨6044435, by rfl⟩ : syracuseStep 8059247 = 12088871) B12088871
theorem B5372831 : Blo 2121435 5372831 := bstep (se 1 (by rfl) ⟨4029623, by rfl⟩ : syracuseStep 5372831 = 8059247) B8059247
theorem B3581887 : Blo 2121435 3581887 := bstep (se 1 (by rfl) ⟨2686415, by rfl⟩ : syracuseStep 3581887 = 5372831) B5372831
theorem B4775849 : Blo 2121435 4775849 := bstep (se 2 (by rfl) ⟨1790943, by rfl⟩ : syracuseStep 4775849 = 3581887) B3581887
theorem B3183899 : Blo 2121435 3183899 := bstep (se 1 (by rfl) ⟨2387924, by rfl⟩ : syracuseStep 3183899 = 4775849) B4775849
theorem B2122599 : Blo 2121435 2122599 := bstep (se 1 (by rfl) ⟨1591949, by rfl⟩ : syracuseStep 2122599 = 3183899) B3183899
theorem B2387929 : Blo 2121435 2387929 := bbase (se 2 (by rfl) ⟨895473, by rfl⟩ : syracuseStep 2387929 = 1790947) (by norm_num)
theorem B3183905 : Blo 2121435 3183905 := bstep (se 2 (by rfl) ⟨1193964, by rfl⟩ : syracuseStep 3183905 = 2387929) B2387929
theorem B2122603 : Blo 2121435 2122603 := bstep (se 1 (by rfl) ⟨1591952, by rfl⟩ : syracuseStep 2122603 = 3183905) B3183905
theorem B3022229 : Blo 2121435 3022229 := bbase (se 6 (by rfl) ⟨70833, by rfl⟩ : syracuseStep 3022229 = 141667) (by norm_num)
theorem B8059277 : Blo 2121435 8059277 := bstep (se 3 (by rfl) ⟨1511114, by rfl⟩ : syracuseStep 8059277 = 3022229) B3022229
theorem B5372851 : Blo 2121435 5372851 := bstep (se 1 (by rfl) ⟨4029638, by rfl⟩ : syracuseStep 5372851 = 8059277) B8059277
theorem B7163801 : Blo 2121435 7163801 := bstep (se 2 (by rfl) ⟨2686425, by rfl⟩ : syracuseStep 7163801 = 5372851) B5372851
theorem B4775867 : Blo 2121435 4775867 := bstep (se 1 (by rfl) ⟨3581900, by rfl⟩ : syracuseStep 4775867 = 7163801) B7163801
theorem B3183911 : Blo 2121435 3183911 := bstep (se 1 (by rfl) ⟨2387933, by rfl⟩ : syracuseStep 3183911 = 4775867) B4775867
theorem B2122607 : Blo 2121435 2122607 := bstep (se 1 (by rfl) ⟨1591955, by rfl⟩ : syracuseStep 2122607 = 3183911) B3183911
theorem B3183917 : Blo 2121435 3183917 := bbase (se 3 (by rfl) ⟨596984, by rfl⟩ : syracuseStep 3183917 = 1193969) (by norm_num)
theorem B2122611 : Blo 2121435 2122611 := bstep (se 1 (by rfl) ⟨1591958, by rfl⟩ : syracuseStep 2122611 = 3183917) B3183917
theorem B4775885 : Blo 2121435 4775885 := bbase (se 3 (by rfl) ⟨895478, by rfl⟩ : syracuseStep 4775885 = 1790957) (by norm_num)
theorem B3183923 : Blo 2121435 3183923 := bstep (se 1 (by rfl) ⟨2387942, by rfl⟩ : syracuseStep 3183923 = 4775885) B4775885
theorem B2122615 : Blo 2121435 2122615 := bstep (se 1 (by rfl) ⟨1591961, by rfl⟩ : syracuseStep 2122615 = 3183923) B3183923
theorem B2686441 : Blo 2121435 2686441 := bbase (se 2 (by rfl) ⟨1007415, by rfl⟩ : syracuseStep 2686441 = 2014831) (by norm_num)
theorem B3581921 : Blo 2121435 3581921 := bstep (se 2 (by rfl) ⟨1343220, by rfl⟩ : syracuseStep 3581921 = 2686441) B2686441
theorem B2387947 : Blo 2121435 2387947 := bstep (se 1 (by rfl) ⟨1790960, by rfl⟩ : syracuseStep 2387947 = 3581921) B3581921
theorem B3183929 : Blo 2121435 3183929 := bstep (se 2 (by rfl) ⟨1193973, by rfl⟩ : syracuseStep 3183929 = 2387947) B2387947
theorem B2122619 : Blo 2121435 2122619 := bstep (se 1 (by rfl) ⟨1591964, by rfl⟩ : syracuseStep 2122619 = 3183929) B3183929
theorem B2550025 : Blo 2121435 2550025 := bbase (se 2 (by rfl) ⟨956259, by rfl⟩ : syracuseStep 2550025 = 1912519) (by norm_num)
theorem B13600133 : Blo 2121435 13600133 := bstep (se 4 (by rfl) ⟨1275012, by rfl⟩ : syracuseStep 13600133 = 2550025) B2550025
theorem B9066755 : Blo 2121435 9066755 := bstep (se 1 (by rfl) ⟨6800066, by rfl⟩ : syracuseStep 9066755 = 13600133) B13600133
theorem B24178013 : Blo 2121435 24178013 := bstep (se 3 (by rfl) ⟨4533377, by rfl⟩ : syracuseStep 24178013 = 9066755) B9066755
theorem B16118675 : Blo 2121435 16118675 := bstep (se 1 (by rfl) ⟨12089006, by rfl⟩ : syracuseStep 16118675 = 24178013) B24178013
theorem B10745783 : Blo 2121435 10745783 := bstep (se 1 (by rfl) ⟨8059337, by rfl⟩ : syracuseStep 10745783 = 16118675) B16118675
theorem B7163855 : Blo 2121435 7163855 := bstep (se 1 (by rfl) ⟨5372891, by rfl⟩ : syracuseStep 7163855 = 10745783) B10745783
theorem B4775903 : Blo 2121435 4775903 := bstep (se 1 (by rfl) ⟨3581927, by rfl⟩ : syracuseStep 4775903 = 7163855) B7163855
theorem B3183935 : Blo 2121435 3183935 := bstep (se 1 (by rfl) ⟨2387951, by rfl⟩ : syracuseStep 3183935 = 4775903) B4775903
theorem B2122623 : Blo 2121435 2122623 := bstep (se 1 (by rfl) ⟨1591967, by rfl⟩ : syracuseStep 2122623 = 3183935) B3183935
theorem B3183941 : Blo 2121435 3183941 := bbase (se 4 (by rfl) ⟨298494, by rfl⟩ : syracuseStep 3183941 = 596989) (by norm_num)
theorem B2122627 : Blo 2121435 2122627 := bstep (se 1 (by rfl) ⟨1591970, by rfl⟩ : syracuseStep 2122627 = 3183941) B3183941
theorem B3581941 : Blo 2121435 3581941 := bbase (se 5 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 3581941 = 335807) (by norm_num)
theorem B4775921 : Blo 2121435 4775921 := bstep (se 2 (by rfl) ⟨1790970, by rfl⟩ : syracuseStep 4775921 = 3581941) B3581941
theorem B3183947 : Blo 2121435 3183947 := bstep (se 1 (by rfl) ⟨2387960, by rfl⟩ : syracuseStep 3183947 = 4775921) B4775921
theorem B2122631 : Blo 2121435 2122631 := bstep (se 1 (by rfl) ⟨1591973, by rfl⟩ : syracuseStep 2122631 = 3183947) B3183947
theorem B2387965 : Blo 2121435 2387965 := bbase (se 3 (by rfl) ⟨447743, by rfl⟩ : syracuseStep 2387965 = 895487) (by norm_num)
theorem B3183953 : Blo 2121435 3183953 := bstep (se 2 (by rfl) ⟨1193982, by rfl⟩ : syracuseStep 3183953 = 2387965) B2387965
theorem B2122635 : Blo 2121435 2122635 := bstep (se 1 (by rfl) ⟨1591976, by rfl⟩ : syracuseStep 2122635 = 3183953) B3183953
theorem B7163909 : Blo 2121435 7163909 := bbase (se 4 (by rfl) ⟨671616, by rfl⟩ : syracuseStep 7163909 = 1343233) (by norm_num)
theorem B4775939 : Blo 2121435 4775939 := bstep (se 1 (by rfl) ⟨3581954, by rfl⟩ : syracuseStep 4775939 = 7163909) B7163909
theorem B3183959 : Blo 2121435 3183959 := bstep (se 1 (by rfl) ⟨2387969, by rfl⟩ : syracuseStep 3183959 = 4775939) B4775939
theorem B2122639 : Blo 2121435 2122639 := bstep (se 1 (by rfl) ⟨1591979, by rfl⟩ : syracuseStep 2122639 = 3183959) B3183959
theorem B3183965 : Blo 2121435 3183965 := bbase (se 3 (by rfl) ⟨596993, by rfl⟩ : syracuseStep 3183965 = 1193987) (by norm_num)
theorem B2122643 : Blo 2121435 2122643 := bstep (se 1 (by rfl) ⟨1591982, by rfl⟩ : syracuseStep 2122643 = 3183965) B3183965
theorem B4775957 : Blo 2121435 4775957 := bbase (se 6 (by rfl) ⟨111936, by rfl⟩ : syracuseStep 4775957 = 223873) (by norm_num)
theorem B3183971 : Blo 2121435 3183971 := bstep (se 1 (by rfl) ⟨2387978, by rfl⟩ : syracuseStep 3183971 = 4775957) B4775957
theorem B2122647 : Blo 2121435 2122647 := bstep (se 1 (by rfl) ⟨1591985, by rfl⟩ : syracuseStep 2122647 = 3183971) B3183971
theorem B8059445 : Blo 2121435 8059445 := bbase (se 5 (by rfl) ⟨377786, by rfl⟩ : syracuseStep 8059445 = 755573) (by norm_num)
theorem B5372963 : Blo 2121435 5372963 := bstep (se 1 (by rfl) ⟨4029722, by rfl⟩ : syracuseStep 5372963 = 8059445) B8059445
theorem B3581975 : Blo 2121435 3581975 := bstep (se 1 (by rfl) ⟨2686481, by rfl⟩ : syracuseStep 3581975 = 5372963) B5372963
theorem B2387983 : Blo 2121435 2387983 := bstep (se 1 (by rfl) ⟨1790987, by rfl⟩ : syracuseStep 2387983 = 3581975) B3581975
theorem B3183977 : Blo 2121435 3183977 := bstep (se 2 (by rfl) ⟨1193991, by rfl⟩ : syracuseStep 3183977 = 2387983) B2387983
theorem B2122651 : Blo 2121435 2122651 := bstep (se 1 (by rfl) ⟨1591988, by rfl⟩ : syracuseStep 2122651 = 3183977) B3183977
theorem B3400085 : Blo 2121435 3400085 := bbase (se 6 (by rfl) ⟨79689, by rfl⟩ : syracuseStep 3400085 = 159379) (by norm_num)
theorem B2266723 : Blo 2121435 2266723 := bstep (se 1 (by rfl) ⟨1700042, by rfl⟩ : syracuseStep 2266723 = 3400085) B3400085
theorem B12089189 : Blo 2121435 12089189 := bstep (se 4 (by rfl) ⟨1133361, by rfl⟩ : syracuseStep 12089189 = 2266723) B2266723
theorem B8059459 : Blo 2121435 8059459 := bstep (se 1 (by rfl) ⟨6044594, by rfl⟩ : syracuseStep 8059459 = 12089189) B12089189
theorem B10745945 : Blo 2121435 10745945 := bstep (se 2 (by rfl) ⟨4029729, by rfl⟩ : syracuseStep 10745945 = 8059459) B8059459
theorem B7163963 : Blo 2121435 7163963 := bstep (se 1 (by rfl) ⟨5372972, by rfl⟩ : syracuseStep 7163963 = 10745945) B10745945
theorem B4775975 : Blo 2121435 4775975 := bstep (se 1 (by rfl) ⟨3581981, by rfl⟩ : syracuseStep 4775975 = 7163963) B7163963
theorem B3183983 : Blo 2121435 3183983 := bstep (se 1 (by rfl) ⟨2387987, by rfl⟩ : syracuseStep 3183983 = 4775975) B4775975
theorem B2122655 : Blo 2121435 2122655 := bstep (se 1 (by rfl) ⟨1591991, by rfl⟩ : syracuseStep 2122655 = 3183983) B3183983
theorem B3183989 : Blo 2121435 3183989 := bbase (se 5 (by rfl) ⟨149249, by rfl⟩ : syracuseStep 3183989 = 298499) (by norm_num)
theorem B2122659 : Blo 2121435 2122659 := bstep (se 1 (by rfl) ⟨1591994, by rfl⟩ : syracuseStep 2122659 = 3183989) B3183989
theorem B3022309 : Blo 2121435 3022309 := bbase (se 4 (by rfl) ⟨283341, by rfl⟩ : syracuseStep 3022309 = 566683) (by norm_num)
theorem B4029745 : Blo 2121435 4029745 := bstep (se 2 (by rfl) ⟨1511154, by rfl⟩ : syracuseStep 4029745 = 3022309) B3022309
theorem B5372993 : Blo 2121435 5372993 := bstep (se 2 (by rfl) ⟨2014872, by rfl⟩ : syracuseStep 5372993 = 4029745) B4029745
theorem B3581995 : Blo 2121435 3581995 := bstep (se 1 (by rfl) ⟨2686496, by rfl⟩ : syracuseStep 3581995 = 5372993) B5372993
theorem B4775993 : Blo 2121435 4775993 := bstep (se 2 (by rfl) ⟨1790997, by rfl⟩ : syracuseStep 4775993 = 3581995) B3581995
theorem B3183995 : Blo 2121435 3183995 := bstep (se 1 (by rfl) ⟨2387996, by rfl⟩ : syracuseStep 3183995 = 4775993) B4775993
theorem B2122663 : Blo 2121435 2122663 := bstep (se 1 (by rfl) ⟨1591997, by rfl⟩ : syracuseStep 2122663 = 3183995) B3183995
theorem B2388001 : Blo 2121435 2388001 := bbase (se 2 (by rfl) ⟨895500, by rfl⟩ : syracuseStep 2388001 = 1791001) (by norm_num)
theorem B3184001 : Blo 2121435 3184001 := bstep (se 2 (by rfl) ⟨1194000, by rfl⟩ : syracuseStep 3184001 = 2388001) B2388001
theorem B2122667 : Blo 2121435 2122667 := bstep (se 1 (by rfl) ⟨1592000, by rfl⟩ : syracuseStep 2122667 = 3184001) B3184001
theorem B5373013 : Blo 2121435 5373013 := bbase (se 8 (by rfl) ⟨31482, by rfl⟩ : syracuseStep 5373013 = 62965) (by norm_num)
theorem B7164017 : Blo 2121435 7164017 := bstep (se 2 (by rfl) ⟨2686506, by rfl⟩ : syracuseStep 7164017 = 5373013) B5373013
theorem B4776011 : Blo 2121435 4776011 := bstep (se 1 (by rfl) ⟨3582008, by rfl⟩ : syracuseStep 4776011 = 7164017) B7164017
theorem B3184007 : Blo 2121435 3184007 := bstep (se 1 (by rfl) ⟨2388005, by rfl⟩ : syracuseStep 3184007 = 4776011) B4776011
theorem B2122671 : Blo 2121435 2122671 := bstep (se 1 (by rfl) ⟨1592003, by rfl⟩ : syracuseStep 2122671 = 3184007) B3184007
theorem B3184013 : Blo 2121435 3184013 := bbase (se 3 (by rfl) ⟨597002, by rfl⟩ : syracuseStep 3184013 = 1194005) (by norm_num)
theorem B2122675 : Blo 2121435 2122675 := bstep (se 1 (by rfl) ⟨1592006, by rfl⟩ : syracuseStep 2122675 = 3184013) B3184013
theorem B4776029 : Blo 2121435 4776029 := bbase (se 3 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 4776029 = 1791011) (by norm_num)
theorem B3184019 : Blo 2121435 3184019 := bstep (se 1 (by rfl) ⟨2388014, by rfl⟩ : syracuseStep 3184019 = 4776029) B4776029
theorem B2122679 : Blo 2121435 2122679 := bstep (se 1 (by rfl) ⟨1592009, by rfl⟩ : syracuseStep 2122679 = 3184019) B3184019
theorem B3582029 : Blo 2121435 3582029 := bbase (se 3 (by rfl) ⟨671630, by rfl⟩ : syracuseStep 3582029 = 1343261) (by norm_num)
theorem B2388019 : Blo 2121435 2388019 := bstep (se 1 (by rfl) ⟨1791014, by rfl⟩ : syracuseStep 2388019 = 3582029) B3582029
theorem B3184025 : Blo 2121435 3184025 := bstep (se 2 (by rfl) ⟨1194009, by rfl⟩ : syracuseStep 3184025 = 2388019) B2388019
theorem B2122683 : Blo 2121435 2122683 := bstep (se 1 (by rfl) ⟨1592012, by rfl⟩ : syracuseStep 2122683 = 3184025) B3184025
theorem B6127157 : Blo 2121435 6127157 := bbase (se 5 (by rfl) ⟨287210, by rfl⟩ : syracuseStep 6127157 = 574421) (by norm_num)
theorem B4084771 : Blo 2121435 4084771 := bstep (se 1 (by rfl) ⟨3063578, by rfl⟩ : syracuseStep 4084771 = 6127157) B6127157
theorem B5446361 : Blo 2121435 5446361 := bstep (se 2 (by rfl) ⟨2042385, by rfl⟩ : syracuseStep 5446361 = 4084771) B4084771
theorem B3630907 : Blo 2121435 3630907 := bstep (se 1 (by rfl) ⟨2723180, by rfl⟩ : syracuseStep 3630907 = 5446361) B5446361
theorem B19364837 : Blo 2121435 19364837 := bstep (se 4 (by rfl) ⟨1815453, by rfl⟩ : syracuseStep 19364837 = 3630907) B3630907
theorem B51639565 : Blo 2121435 51639565 := bstep (se 3 (by rfl) ⟨9682418, by rfl⟩ : syracuseStep 51639565 = 19364837) B19364837
theorem B68852753 : Blo 2121435 68852753 := bstep (se 2 (by rfl) ⟨25819782, by rfl⟩ : syracuseStep 68852753 = 51639565) B51639565
theorem B45901835 : Blo 2121435 45901835 := bstep (se 1 (by rfl) ⟨34426376, by rfl⟩ : syracuseStep 45901835 = 68852753) B68852753
theorem B30601223 : Blo 2121435 30601223 := bstep (se 1 (by rfl) ⟨22950917, by rfl⟩ : syracuseStep 30601223 = 45901835) B45901835
theorem B20400815 : Blo 2121435 20400815 := bstep (se 1 (by rfl) ⟨15300611, by rfl⟩ : syracuseStep 20400815 = 30601223) B30601223
theorem B13600543 : Blo 2121435 13600543 := bstep (se 1 (by rfl) ⟨10200407, by rfl⟩ : syracuseStep 13600543 = 20400815) B20400815
theorem B18134057 : Blo 2121435 18134057 := bstep (se 2 (by rfl) ⟨6800271, by rfl⟩ : syracuseStep 18134057 = 13600543) B13600543
theorem B12089371 : Blo 2121435 12089371 := bstep (se 1 (by rfl) ⟨9067028, by rfl⟩ : syracuseStep 12089371 = 18134057) B18134057
theorem B16119161 : Blo 2121435 16119161 := bstep (se 2 (by rfl) ⟨6044685, by rfl⟩ : syracuseStep 16119161 = 12089371) B12089371
theorem B10746107 : Blo 2121435 10746107 := bstep (se 1 (by rfl) ⟨8059580, by rfl⟩ : syracuseStep 10746107 = 16119161) B16119161
theorem B7164071 : Blo 2121435 7164071 := bstep (se 1 (by rfl) ⟨5373053, by rfl⟩ : syracuseStep 7164071 = 10746107) B10746107
theorem B4776047 : Blo 2121435 4776047 := bstep (se 1 (by rfl) ⟨3582035, by rfl⟩ : syracuseStep 4776047 = 7164071) B7164071
theorem B3184031 : Blo 2121435 3184031 := bstep (se 1 (by rfl) ⟨2388023, by rfl⟩ : syracuseStep 3184031 = 4776047) B4776047
theorem B2122687 : Blo 2121435 2122687 := bstep (se 1 (by rfl) ⟨1592015, by rfl⟩ : syracuseStep 2122687 = 3184031) B3184031
theorem B3184037 : Blo 2121435 3184037 := bbase (se 4 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 3184037 = 597007) (by norm_num)
theorem B2122691 : Blo 2121435 2122691 := bstep (se 1 (by rfl) ⟨1592018, by rfl⟩ : syracuseStep 2122691 = 3184037) B3184037
theorem B2686537 : Blo 2121435 2686537 := bbase (se 2 (by rfl) ⟨1007451, by rfl⟩ : syracuseStep 2686537 = 2014903) (by norm_num)
theorem B3582049 : Blo 2121435 3582049 := bstep (se 2 (by rfl) ⟨1343268, by rfl⟩ : syracuseStep 3582049 = 2686537) B2686537
theorem B4776065 : Blo 2121435 4776065 := bstep (se 2 (by rfl) ⟨1791024, by rfl⟩ : syracuseStep 4776065 = 3582049) B3582049
theorem B3184043 : Blo 2121435 3184043 := bstep (se 1 (by rfl) ⟨2388032, by rfl⟩ : syracuseStep 3184043 = 4776065) B4776065
theorem B2122695 : Blo 2121435 2122695 := bstep (se 1 (by rfl) ⟨1592021, by rfl⟩ : syracuseStep 2122695 = 3184043) B3184043
theorem B2388037 : Blo 2121435 2388037 := bbase (se 4 (by rfl) ⟨223878, by rfl⟩ : syracuseStep 2388037 = 447757) (by norm_num)
theorem B3184049 : Blo 2121435 3184049 := bstep (se 2 (by rfl) ⟨1194018, by rfl⟩ : syracuseStep 3184049 = 2388037) B2388037
theorem B2122699 : Blo 2121435 2122699 := bstep (se 1 (by rfl) ⟨1592024, by rfl⟩ : syracuseStep 2122699 = 3184049) B3184049
theorem B4029821 : Blo 2121435 4029821 := bbase (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) (by norm_num)
theorem B2686547 : Blo 2121435 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B7164125 : Blo 2121435 7164125 := bstep (se 3 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 7164125 = 2686547) B2686547
theorem B4776083 : Blo 2121435 4776083 := bstep (se 1 (by rfl) ⟨3582062, by rfl⟩ : syracuseStep 4776083 = 7164125) B7164125
theorem B3184055 : Blo 2121435 3184055 := bstep (se 1 (by rfl) ⟨2388041, by rfl⟩ : syracuseStep 3184055 = 4776083) B4776083
theorem B2122703 : Blo 2121435 2122703 := bstep (se 1 (by rfl) ⟨1592027, by rfl⟩ : syracuseStep 2122703 = 3184055) B3184055
theorem B3184061 : Blo 2121435 3184061 := bbase (se 3 (by rfl) ⟨597011, by rfl⟩ : syracuseStep 3184061 = 1194023) (by norm_num)
theorem B2122707 : Blo 2121435 2122707 := bstep (se 1 (by rfl) ⟨1592030, by rfl⟩ : syracuseStep 2122707 = 3184061) B3184061
theorem B4776101 : Blo 2121435 4776101 := bbase (se 4 (by rfl) ⟨447759, by rfl⟩ : syracuseStep 4776101 = 895519) (by norm_num)
theorem B3184067 : Blo 2121435 3184067 := bstep (se 1 (by rfl) ⟨2388050, by rfl⟩ : syracuseStep 3184067 = 4776101) B4776101
theorem B2122711 : Blo 2121435 2122711 := bstep (se 1 (by rfl) ⟨1592033, by rfl⟩ : syracuseStep 2122711 = 3184067) B3184067
theorem B5373125 : Blo 2121435 5373125 := bbase (se 4 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 5373125 = 1007461) (by norm_num)
theorem B3582083 : Blo 2121435 3582083 := bstep (se 1 (by rfl) ⟨2686562, by rfl⟩ : syracuseStep 3582083 = 5373125) B5373125
theorem B2388055 : Blo 2121435 2388055 := bstep (se 1 (by rfl) ⟨1791041, by rfl⟩ : syracuseStep 2388055 = 3582083) B3582083
theorem B3184073 : Blo 2121435 3184073 := bstep (se 2 (by rfl) ⟨1194027, by rfl⟩ : syracuseStep 3184073 = 2388055) B2388055
theorem B2122715 : Blo 2121435 2122715 := bstep (se 1 (by rfl) ⟨1592036, by rfl⟩ : syracuseStep 2122715 = 3184073) B3184073
theorem B6455045 : Blo 2121435 6455045 := bbase (se 4 (by rfl) ⟨605160, by rfl⟩ : syracuseStep 6455045 = 1210321) (by norm_num)
theorem B4303363 : Blo 2121435 4303363 := bstep (se 1 (by rfl) ⟨3227522, by rfl⟩ : syracuseStep 4303363 = 6455045) B6455045
theorem B5737817 : Blo 2121435 5737817 := bstep (se 2 (by rfl) ⟨2151681, by rfl⟩ : syracuseStep 5737817 = 4303363) B4303363
theorem B15300845 : Blo 2121435 15300845 := bstep (se 3 (by rfl) ⟨2868908, by rfl⟩ : syracuseStep 15300845 = 5737817) B5737817
theorem B10200563 : Blo 2121435 10200563 := bstep (se 1 (by rfl) ⟨7650422, by rfl⟩ : syracuseStep 10200563 = 15300845) B15300845
theorem B6800375 : Blo 2121435 6800375 := bstep (se 1 (by rfl) ⟨5100281, by rfl⟩ : syracuseStep 6800375 = 10200563) B10200563
theorem B4533583 : Blo 2121435 4533583 := bstep (se 1 (by rfl) ⟨3400187, by rfl⟩ : syracuseStep 4533583 = 6800375) B6800375
theorem B6044777 : Blo 2121435 6044777 := bstep (se 2 (by rfl) ⟨2266791, by rfl⟩ : syracuseStep 6044777 = 4533583) B4533583
theorem B4029851 : Blo 2121435 4029851 := bstep (se 1 (by rfl) ⟨3022388, by rfl⟩ : syracuseStep 4029851 = 6044777) B6044777
theorem B10746269 : Blo 2121435 10746269 := bstep (se 3 (by rfl) ⟨2014925, by rfl⟩ : syracuseStep 10746269 = 4029851) B4029851
theorem B7164179 : Blo 2121435 7164179 := bstep (se 1 (by rfl) ⟨5373134, by rfl⟩ : syracuseStep 7164179 = 10746269) B10746269
theorem B4776119 : Blo 2121435 4776119 := bstep (se 1 (by rfl) ⟨3582089, by rfl⟩ : syracuseStep 4776119 = 7164179) B7164179
theorem B3184079 : Blo 2121435 3184079 := bstep (se 1 (by rfl) ⟨2388059, by rfl⟩ : syracuseStep 3184079 = 4776119) B4776119
theorem B2122719 : Blo 2121435 2122719 := bstep (se 1 (by rfl) ⟨1592039, by rfl⟩ : syracuseStep 2122719 = 3184079) B3184079
theorem B3184085 : Blo 2121435 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B2122723 : Blo 2121435 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B8059733 : Blo 2121435 8059733 := bbase (se 9 (by rfl) ⟨23612, by rfl⟩ : syracuseStep 8059733 = 47225) (by norm_num)
theorem B5373155 : Blo 2121435 5373155 := bstep (se 1 (by rfl) ⟨4029866, by rfl⟩ : syracuseStep 5373155 = 8059733) B8059733
theorem B3582103 : Blo 2121435 3582103 := bstep (se 1 (by rfl) ⟨2686577, by rfl⟩ : syracuseStep 3582103 = 5373155) B5373155
theorem B4776137 : Blo 2121435 4776137 := bstep (se 2 (by rfl) ⟨1791051, by rfl⟩ : syracuseStep 4776137 = 3582103) B3582103
theorem B3184091 : Blo 2121435 3184091 := bstep (se 1 (by rfl) ⟨2388068, by rfl⟩ : syracuseStep 3184091 = 4776137) B4776137
theorem B2122727 : Blo 2121435 2122727 := bstep (se 1 (by rfl) ⟨1592045, by rfl⟩ : syracuseStep 2122727 = 3184091) B3184091
theorem B2388073 : Blo 2121435 2388073 := bbase (se 2 (by rfl) ⟨895527, by rfl⟩ : syracuseStep 2388073 = 1791055) (by norm_num)
theorem B3184097 : Blo 2121435 3184097 := bstep (se 2 (by rfl) ⟨1194036, by rfl⟩ : syracuseStep 3184097 = 2388073) B2388073
theorem B2122731 : Blo 2121435 2122731 := bstep (se 1 (by rfl) ⟨1592048, by rfl⟩ : syracuseStep 2122731 = 3184097) B3184097
theorem B3400213 : Blo 2121435 3400213 := bbase (se 6 (by rfl) ⟨79692, by rfl⟩ : syracuseStep 3400213 = 159385) (by norm_num)
theorem B4533617 : Blo 2121435 4533617 := bstep (se 2 (by rfl) ⟨1700106, by rfl⟩ : syracuseStep 4533617 = 3400213) B3400213
theorem B12089645 : Blo 2121435 12089645 := bstep (se 3 (by rfl) ⟨2266808, by rfl⟩ : syracuseStep 12089645 = 4533617) B4533617
theorem B8059763 : Blo 2121435 8059763 := bstep (se 1 (by rfl) ⟨6044822, by rfl⟩ : syracuseStep 8059763 = 12089645) B12089645
theorem B5373175 : Blo 2121435 5373175 := bstep (se 1 (by rfl) ⟨4029881, by rfl⟩ : syracuseStep 5373175 = 8059763) B8059763
theorem B7164233 : Blo 2121435 7164233 := bstep (se 2 (by rfl) ⟨2686587, by rfl⟩ : syracuseStep 7164233 = 5373175) B5373175
theorem B4776155 : Blo 2121435 4776155 := bstep (se 1 (by rfl) ⟨3582116, by rfl⟩ : syracuseStep 4776155 = 7164233) B7164233
theorem B3184103 : Blo 2121435 3184103 := bstep (se 1 (by rfl) ⟨2388077, by rfl⟩ : syracuseStep 3184103 = 4776155) B4776155
theorem B2122735 : Blo 2121435 2122735 := bstep (se 1 (by rfl) ⟨1592051, by rfl⟩ : syracuseStep 2122735 = 3184103) B3184103
theorem B3184109 : Blo 2121435 3184109 := bbase (se 3 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 3184109 = 1194041) (by norm_num)
theorem B2122739 : Blo 2121435 2122739 := bstep (se 1 (by rfl) ⟨1592054, by rfl⟩ : syracuseStep 2122739 = 3184109) B3184109
theorem B4776173 : Blo 2121435 4776173 := bbase (se 3 (by rfl) ⟨895532, by rfl⟩ : syracuseStep 4776173 = 1791065) (by norm_num)
theorem B3184115 : Blo 2121435 3184115 := bstep (se 1 (by rfl) ⟨2388086, by rfl⟩ : syracuseStep 3184115 = 4776173) B4776173
theorem B2122743 : Blo 2121435 2122743 := bstep (se 1 (by rfl) ⟨1592057, by rfl⟩ : syracuseStep 2122743 = 3184115) B3184115
theorem B3022429 : Blo 2121435 3022429 := bbase (se 3 (by rfl) ⟨566705, by rfl⟩ : syracuseStep 3022429 = 1133411) (by norm_num)
theorem B4029905 : Blo 2121435 4029905 := bstep (se 2 (by rfl) ⟨1511214, by rfl⟩ : syracuseStep 4029905 = 3022429) B3022429
theorem B2686603 : Blo 2121435 2686603 := bstep (se 1 (by rfl) ⟨2014952, by rfl⟩ : syracuseStep 2686603 = 4029905) B4029905
theorem B3582137 : Blo 2121435 3582137 := bstep (se 2 (by rfl) ⟨1343301, by rfl⟩ : syracuseStep 3582137 = 2686603) B2686603
theorem B2388091 : Blo 2121435 2388091 := bstep (se 1 (by rfl) ⟨1791068, by rfl⟩ : syracuseStep 2388091 = 3582137) B3582137
theorem B3184121 : Blo 2121435 3184121 := bstep (se 2 (by rfl) ⟨1194045, by rfl⟩ : syracuseStep 3184121 = 2388091) B2388091
theorem B2122747 : Blo 2121435 2122747 := bstep (se 1 (by rfl) ⟨1592060, by rfl⟩ : syracuseStep 2122747 = 3184121) B3184121
theorem B81605717 : Blo 2121435 81605717 := bbase (se 8 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 81605717 = 956317) (by norm_num)
theorem B54403811 : Blo 2121435 54403811 := bstep (se 1 (by rfl) ⟨40802858, by rfl⟩ : syracuseStep 54403811 = 81605717) B81605717
theorem B36269207 : Blo 2121435 36269207 := bstep (se 1 (by rfl) ⟨27201905, by rfl⟩ : syracuseStep 36269207 = 54403811) B54403811
theorem B24179471 : Blo 2121435 24179471 := bstep (se 1 (by rfl) ⟨18134603, by rfl⟩ : syracuseStep 24179471 = 36269207) B36269207
theorem B16119647 : Blo 2121435 16119647 := bstep (se 1 (by rfl) ⟨12089735, by rfl⟩ : syracuseStep 16119647 = 24179471) B24179471
theorem B10746431 : Blo 2121435 10746431 := bstep (se 1 (by rfl) ⟨8059823, by rfl⟩ : syracuseStep 10746431 = 16119647) B16119647
theorem B7164287 : Blo 2121435 7164287 := bstep (se 1 (by rfl) ⟨5373215, by rfl⟩ : syracuseStep 7164287 = 10746431) B10746431
theorem B4776191 : Blo 2121435 4776191 := bstep (se 1 (by rfl) ⟨3582143, by rfl⟩ : syracuseStep 4776191 = 7164287) B7164287
theorem B3184127 : Blo 2121435 3184127 := bstep (se 1 (by rfl) ⟨2388095, by rfl⟩ : syracuseStep 3184127 = 4776191) B4776191
theorem B2122751 : Blo 2121435 2122751 := bstep (se 1 (by rfl) ⟨1592063, by rfl⟩ : syracuseStep 2122751 = 3184127) B3184127
theorem B3184133 : Blo 2121435 3184133 := bbase (se 4 (by rfl) ⟨298512, by rfl⟩ : syracuseStep 3184133 = 597025) (by norm_num)
theorem B2122755 : Blo 2121435 2122755 := bstep (se 1 (by rfl) ⟨1592066, by rfl⟩ : syracuseStep 2122755 = 3184133) B3184133
theorem B3582157 : Blo 2121435 3582157 := bbase (se 3 (by rfl) ⟨671654, by rfl⟩ : syracuseStep 3582157 = 1343309) (by norm_num)
theorem B4776209 : Blo 2121435 4776209 := bstep (se 2 (by rfl) ⟨1791078, by rfl⟩ : syracuseStep 4776209 = 3582157) B3582157
theorem B3184139 : Blo 2121435 3184139 := bstep (se 1 (by rfl) ⟨2388104, by rfl⟩ : syracuseStep 3184139 = 4776209) B4776209
theorem B2122759 : Blo 2121435 2122759 := bstep (se 1 (by rfl) ⟨1592069, by rfl⟩ : syracuseStep 2122759 = 3184139) B3184139
theorem B2388109 : Blo 2121435 2388109 := bbase (se 3 (by rfl) ⟨447770, by rfl⟩ : syracuseStep 2388109 = 895541) (by norm_num)
theorem B3184145 : Blo 2121435 3184145 := bstep (se 2 (by rfl) ⟨1194054, by rfl⟩ : syracuseStep 3184145 = 2388109) B2388109
theorem B2122763 : Blo 2121435 2122763 := bstep (se 1 (by rfl) ⟨1592072, by rfl⟩ : syracuseStep 2122763 = 3184145) B3184145
theorem B7164341 : Blo 2121435 7164341 := bbase (se 5 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 7164341 = 671657) (by norm_num)
theorem B4776227 : Blo 2121435 4776227 := bstep (se 1 (by rfl) ⟨3582170, by rfl⟩ : syracuseStep 4776227 = 7164341) B7164341
theorem B3184151 : Blo 2121435 3184151 := bstep (se 1 (by rfl) ⟨2388113, by rfl⟩ : syracuseStep 3184151 = 4776227) B4776227
theorem B2122767 : Blo 2121435 2122767 := bstep (se 1 (by rfl) ⟨1592075, by rfl⟩ : syracuseStep 2122767 = 3184151) B3184151
theorem B3184157 : Blo 2121435 3184157 := bbase (se 3 (by rfl) ⟨597029, by rfl⟩ : syracuseStep 3184157 = 1194059) (by norm_num)
theorem B2122771 : Blo 2121435 2122771 := bstep (se 1 (by rfl) ⟨1592078, by rfl⟩ : syracuseStep 2122771 = 3184157) B3184157
theorem B4776245 : Blo 2121435 4776245 := bbase (se 5 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 4776245 = 447773) (by norm_num)
theorem B3184163 : Blo 2121435 3184163 := bstep (se 1 (by rfl) ⟨2388122, by rfl⟩ : syracuseStep 3184163 = 4776245) B4776245
theorem B2122775 : Blo 2121435 2122775 := bstep (se 1 (by rfl) ⟨1592081, by rfl⟩ : syracuseStep 2122775 = 3184163) B3184163
theorem B51641813 : Blo 2121435 51641813 := bbase (se 7 (by rfl) ⟨605177, by rfl⟩ : syracuseStep 51641813 = 1210355) (by norm_num)
theorem B34427875 : Blo 2121435 34427875 := bstep (se 1 (by rfl) ⟨25820906, by rfl⟩ : syracuseStep 34427875 = 51641813) B51641813
theorem B45903833 : Blo 2121435 45903833 := bstep (se 2 (by rfl) ⟨17213937, by rfl⟩ : syracuseStep 45903833 = 34427875) B34427875
theorem B30602555 : Blo 2121435 30602555 := bstep (se 1 (by rfl) ⟨22951916, by rfl⟩ : syracuseStep 30602555 = 45903833) B45903833
theorem B20401703 : Blo 2121435 20401703 := bstep (se 1 (by rfl) ⟨15301277, by rfl⟩ : syracuseStep 20401703 = 30602555) B30602555
theorem B13601135 : Blo 2121435 13601135 := bstep (se 1 (by rfl) ⟨10200851, by rfl⟩ : syracuseStep 13601135 = 20401703) B20401703
theorem B9067423 : Blo 2121435 9067423 := bstep (se 1 (by rfl) ⟨6800567, by rfl⟩ : syracuseStep 9067423 = 13601135) B13601135
theorem B12089897 : Blo 2121435 12089897 := bstep (se 2 (by rfl) ⟨4533711, by rfl⟩ : syracuseStep 12089897 = 9067423) B9067423
theorem B8059931 : Blo 2121435 8059931 := bstep (se 1 (by rfl) ⟨6044948, by rfl⟩ : syracuseStep 8059931 = 12089897) B12089897
theorem B5373287 : Blo 2121435 5373287 := bstep (se 1 (by rfl) ⟨4029965, by rfl⟩ : syracuseStep 5373287 = 8059931) B8059931
theorem B3582191 : Blo 2121435 3582191 := bstep (se 1 (by rfl) ⟨2686643, by rfl⟩ : syracuseStep 3582191 = 5373287) B5373287
theorem B2388127 : Blo 2121435 2388127 := bstep (se 1 (by rfl) ⟨1791095, by rfl⟩ : syracuseStep 2388127 = 3582191) B3582191
theorem B3184169 : Blo 2121435 3184169 := bstep (se 2 (by rfl) ⟨1194063, by rfl⟩ : syracuseStep 3184169 = 2388127) B2388127
theorem B2122779 : Blo 2121435 2122779 := bstep (se 1 (by rfl) ⟨1592084, by rfl⟩ : syracuseStep 2122779 = 3184169) B3184169
theorem B22951957 : Blo 2121435 22951957 := bbase (se 6 (by rfl) ⟨537936, by rfl⟩ : syracuseStep 22951957 = 1075873) (by norm_num)
theorem B30602609 : Blo 2121435 30602609 := bstep (se 2 (by rfl) ⟨11475978, by rfl⟩ : syracuseStep 30602609 = 22951957) B22951957
theorem B20401739 : Blo 2121435 20401739 := bstep (se 1 (by rfl) ⟨15301304, by rfl⟩ : syracuseStep 20401739 = 30602609) B30602609
theorem B13601159 : Blo 2121435 13601159 := bstep (se 1 (by rfl) ⟨10200869, by rfl⟩ : syracuseStep 13601159 = 20401739) B20401739
theorem B9067439 : Blo 2121435 9067439 := bstep (se 1 (by rfl) ⟨6800579, by rfl⟩ : syracuseStep 9067439 = 13601159) B13601159
theorem B6044959 : Blo 2121435 6044959 := bstep (se 1 (by rfl) ⟨4533719, by rfl⟩ : syracuseStep 6044959 = 9067439) B9067439
theorem B8059945 : Blo 2121435 8059945 := bstep (se 2 (by rfl) ⟨3022479, by rfl⟩ : syracuseStep 8059945 = 6044959) B6044959
theorem B10746593 : Blo 2121435 10746593 := bstep (se 2 (by rfl) ⟨4029972, by rfl⟩ : syracuseStep 10746593 = 8059945) B8059945
theorem B7164395 : Blo 2121435 7164395 := bstep (se 1 (by rfl) ⟨5373296, by rfl⟩ : syracuseStep 7164395 = 10746593) B10746593
theorem B4776263 : Blo 2121435 4776263 := bstep (se 1 (by rfl) ⟨3582197, by rfl⟩ : syracuseStep 4776263 = 7164395) B7164395
theorem B3184175 : Blo 2121435 3184175 := bstep (se 1 (by rfl) ⟨2388131, by rfl⟩ : syracuseStep 3184175 = 4776263) B4776263
theorem B2122783 : Blo 2121435 2122783 := bstep (se 1 (by rfl) ⟨1592087, by rfl⟩ : syracuseStep 2122783 = 3184175) B3184175
theorem B3184181 : Blo 2121435 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B2122787 : Blo 2121435 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B5373317 : Blo 2121435 5373317 := bbase (se 4 (by rfl) ⟨503748, by rfl⟩ : syracuseStep 5373317 = 1007497) (by norm_num)
theorem B3582211 : Blo 2121435 3582211 := bstep (se 1 (by rfl) ⟨2686658, by rfl⟩ : syracuseStep 3582211 = 5373317) B5373317
theorem B4776281 : Blo 2121435 4776281 := bstep (se 2 (by rfl) ⟨1791105, by rfl⟩ : syracuseStep 4776281 = 3582211) B3582211
theorem B3184187 : Blo 2121435 3184187 := bstep (se 1 (by rfl) ⟨2388140, by rfl⟩ : syracuseStep 3184187 = 4776281) B4776281
theorem B2122791 : Blo 2121435 2122791 := bstep (se 1 (by rfl) ⟨1592093, by rfl⟩ : syracuseStep 2122791 = 3184187) B3184187
theorem B2388145 : Blo 2121435 2388145 := bbase (se 2 (by rfl) ⟨895554, by rfl⟩ : syracuseStep 2388145 = 1791109) (by norm_num)
theorem B3184193 : Blo 2121435 3184193 := bstep (se 2 (by rfl) ⟨1194072, by rfl⟩ : syracuseStep 3184193 = 2388145) B2388145
theorem B2122795 : Blo 2121435 2122795 := bstep (se 1 (by rfl) ⟨1592096, by rfl⟩ : syracuseStep 2122795 = 3184193) B3184193
theorem B2266877 : Blo 2121435 2266877 := bbase (se 3 (by rfl) ⟨425039, by rfl⟩ : syracuseStep 2266877 = 850079) (by norm_num)
theorem B6045005 : Blo 2121435 6045005 := bstep (se 3 (by rfl) ⟨1133438, by rfl⟩ : syracuseStep 6045005 = 2266877) B2266877
theorem B4030003 : Blo 2121435 4030003 := bstep (se 1 (by rfl) ⟨3022502, by rfl⟩ : syracuseStep 4030003 = 6045005) B6045005
theorem B5373337 : Blo 2121435 5373337 := bstep (se 2 (by rfl) ⟨2015001, by rfl⟩ : syracuseStep 5373337 = 4030003) B4030003
theorem B7164449 : Blo 2121435 7164449 := bstep (se 2 (by rfl) ⟨2686668, by rfl⟩ : syracuseStep 7164449 = 5373337) B5373337
theorem B4776299 : Blo 2121435 4776299 := bstep (se 1 (by rfl) ⟨3582224, by rfl⟩ : syracuseStep 4776299 = 7164449) B7164449
theorem B3184199 : Blo 2121435 3184199 := bstep (se 1 (by rfl) ⟨2388149, by rfl⟩ : syracuseStep 3184199 = 4776299) B4776299
theorem B2122799 : Blo 2121435 2122799 := bstep (se 1 (by rfl) ⟨1592099, by rfl⟩ : syracuseStep 2122799 = 3184199) B3184199
theorem B3184205 : Blo 2121435 3184205 := bbase (se 3 (by rfl) ⟨597038, by rfl⟩ : syracuseStep 3184205 = 1194077) (by norm_num)
theorem B2122803 : Blo 2121435 2122803 := bstep (se 1 (by rfl) ⟨1592102, by rfl⟩ : syracuseStep 2122803 = 3184205) B3184205
theorem B4776317 : Blo 2121435 4776317 := bbase (se 3 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 4776317 = 1791119) (by norm_num)
theorem B3184211 : Blo 2121435 3184211 := bstep (se 1 (by rfl) ⟨2388158, by rfl⟩ : syracuseStep 3184211 = 4776317) B4776317
theorem B2122807 : Blo 2121435 2122807 := bstep (se 1 (by rfl) ⟨1592105, by rfl⟩ : syracuseStep 2122807 = 3184211) B3184211
theorem B3582245 : Blo 2121435 3582245 := bbase (se 4 (by rfl) ⟨335835, by rfl⟩ : syracuseStep 3582245 = 671671) (by norm_num)
theorem B2388163 : Blo 2121435 2388163 := bstep (se 1 (by rfl) ⟨1791122, by rfl⟩ : syracuseStep 2388163 = 3582245) B3582245
theorem B3184217 : Blo 2121435 3184217 := bstep (se 2 (by rfl) ⟨1194081, by rfl⟩ : syracuseStep 3184217 = 2388163) B2388163
theorem B2122811 : Blo 2121435 2122811 := bstep (se 1 (by rfl) ⟨1592108, by rfl⟩ : syracuseStep 2122811 = 3184217) B3184217
theorem B3022525 : Blo 2121435 3022525 := bbase (se 3 (by rfl) ⟨566723, by rfl⟩ : syracuseStep 3022525 = 1133447) (by norm_num)
theorem B16120133 : Blo 2121435 16120133 := bstep (se 4 (by rfl) ⟨1511262, by rfl⟩ : syracuseStep 16120133 = 3022525) B3022525
theorem B10746755 : Blo 2121435 10746755 := bstep (se 1 (by rfl) ⟨8060066, by rfl⟩ : syracuseStep 10746755 = 16120133) B16120133
theorem B7164503 : Blo 2121435 7164503 := bstep (se 1 (by rfl) ⟨5373377, by rfl⟩ : syracuseStep 7164503 = 10746755) B10746755
theorem B4776335 : Blo 2121435 4776335 := bstep (se 1 (by rfl) ⟨3582251, by rfl⟩ : syracuseStep 4776335 = 7164503) B7164503
theorem B3184223 : Blo 2121435 3184223 := bstep (se 1 (by rfl) ⟨2388167, by rfl⟩ : syracuseStep 3184223 = 4776335) B4776335
theorem B2122815 : Blo 2121435 2122815 := bstep (se 1 (by rfl) ⟨1592111, by rfl⟩ : syracuseStep 2122815 = 3184223) B3184223
theorem B3184229 : Blo 2121435 3184229 := bbase (se 4 (by rfl) ⟨298521, by rfl⟩ : syracuseStep 3184229 = 597043) (by norm_num)
theorem B2122819 : Blo 2121435 2122819 := bstep (se 1 (by rfl) ⟨1592114, by rfl⟩ : syracuseStep 2122819 = 3184229) B3184229
theorem B5100533 : Blo 2121435 5100533 := bbase (se 5 (by rfl) ⟨239087, by rfl⟩ : syracuseStep 5100533 = 478175) (by norm_num)
theorem B3400355 : Blo 2121435 3400355 := bstep (se 1 (by rfl) ⟨2550266, by rfl⟩ : syracuseStep 3400355 = 5100533) B5100533
theorem B2266903 : Blo 2121435 2266903 := bstep (se 1 (by rfl) ⟨1700177, by rfl⟩ : syracuseStep 2266903 = 3400355) B3400355
theorem B3022537 : Blo 2121435 3022537 := bstep (se 2 (by rfl) ⟨1133451, by rfl⟩ : syracuseStep 3022537 = 2266903) B2266903
theorem B4030049 : Blo 2121435 4030049 := bstep (se 2 (by rfl) ⟨1511268, by rfl⟩ : syracuseStep 4030049 = 3022537) B3022537
theorem B2686699 : Blo 2121435 2686699 := bstep (se 1 (by rfl) ⟨2015024, by rfl⟩ : syracuseStep 2686699 = 4030049) B4030049
theorem B3582265 : Blo 2121435 3582265 := bstep (se 2 (by rfl) ⟨1343349, by rfl⟩ : syracuseStep 3582265 = 2686699) B2686699
theorem B4776353 : Blo 2121435 4776353 := bstep (se 2 (by rfl) ⟨1791132, by rfl⟩ : syracuseStep 4776353 = 3582265) B3582265
theorem B3184235 : Blo 2121435 3184235 := bstep (se 1 (by rfl) ⟨2388176, by rfl⟩ : syracuseStep 3184235 = 4776353) B4776353
theorem B2122823 : Blo 2121435 2122823 := bstep (se 1 (by rfl) ⟨1592117, by rfl⟩ : syracuseStep 2122823 = 3184235) B3184235
theorem B2388181 : Blo 2121435 2388181 := bbase (se 7 (by rfl) ⟨27986, by rfl⟩ : syracuseStep 2388181 = 55973) (by norm_num)
theorem B3184241 : Blo 2121435 3184241 := bstep (se 2 (by rfl) ⟨1194090, by rfl⟩ : syracuseStep 3184241 = 2388181) B2388181
theorem B2122827 : Blo 2121435 2122827 := bstep (se 1 (by rfl) ⟨1592120, by rfl⟩ : syracuseStep 2122827 = 3184241) B3184241
theorem B2686709 : Blo 2121435 2686709 := bbase (se 5 (by rfl) ⟨125939, by rfl⟩ : syracuseStep 2686709 = 251879) (by norm_num)
theorem B7164557 : Blo 2121435 7164557 := bstep (se 3 (by rfl) ⟨1343354, by rfl⟩ : syracuseStep 7164557 = 2686709) B2686709
theorem B4776371 : Blo 2121435 4776371 := bstep (se 1 (by rfl) ⟨3582278, by rfl⟩ : syracuseStep 4776371 = 7164557) B7164557
theorem B3184247 : Blo 2121435 3184247 := bstep (se 1 (by rfl) ⟨2388185, by rfl⟩ : syracuseStep 3184247 = 4776371) B4776371
theorem B2122831 : Blo 2121435 2122831 := bstep (se 1 (by rfl) ⟨1592123, by rfl⟩ : syracuseStep 2122831 = 3184247) B3184247
theorem B3184253 : Blo 2121435 3184253 := bbase (se 3 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 3184253 = 1194095) (by norm_num)
theorem B2122835 : Blo 2121435 2122835 := bstep (se 1 (by rfl) ⟨1592126, by rfl⟩ : syracuseStep 2122835 = 3184253) B3184253
theorem B4776389 : Blo 2121435 4776389 := bbase (se 4 (by rfl) ⟨447786, by rfl⟩ : syracuseStep 4776389 = 895573) (by norm_num)
theorem B3184259 : Blo 2121435 3184259 := bstep (se 1 (by rfl) ⟨2388194, by rfl⟩ : syracuseStep 3184259 = 4776389) B4776389
theorem B2122839 : Blo 2121435 2122839 := bstep (se 1 (by rfl) ⟨1592129, by rfl⟩ : syracuseStep 2122839 = 3184259) B3184259
theorem B6800773 : Blo 2121435 6800773 := bbase (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) (by norm_num)
theorem B9067697 : Blo 2121435 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B6045131 : Blo 2121435 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B4030087 : Blo 2121435 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B5373449 : Blo 2121435 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B3582299 : Blo 2121435 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B2388199 : Blo 2121435 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B3184265 : Blo 2121435 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B2122843 : Blo 2121435 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B10746917 : Blo 2121435 10746917 := bbase (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) (by norm_num)
theorem B7164611 : Blo 2121435 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B4776407 : Blo 2121435 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B3184271 : Blo 2121435 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B2122847 : Blo 2121435 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B3184277 : Blo 2121435 3184277 := bbase (se 6 (by rfl) ⟨74631, by rfl⟩ : syracuseStep 3184277 = 149263) (by norm_num)
theorem B2122851 : Blo 2121435 2122851 := bstep (se 1 (by rfl) ⟨1592138, by rfl⟩ : syracuseStep 2122851 = 3184277) B3184277
theorem B13601621 : Blo 2121435 13601621 := bbase (se 9 (by rfl) ⟨39848, by rfl⟩ : syracuseStep 13601621 = 79697) (by norm_num)
theorem B9067747 : Blo 2121435 9067747 := bstep (se 1 (by rfl) ⟨6800810, by rfl⟩ : syracuseStep 9067747 = 13601621) B13601621
theorem B12090329 : Blo 2121435 12090329 := bstep (se 2 (by rfl) ⟨4533873, by rfl⟩ : syracuseStep 12090329 = 9067747) B9067747
theorem B8060219 : Blo 2121435 8060219 := bstep (se 1 (by rfl) ⟨6045164, by rfl⟩ : syracuseStep 8060219 = 12090329) B12090329
theorem B5373479 : Blo 2121435 5373479 := bstep (se 1 (by rfl) ⟨4030109, by rfl⟩ : syracuseStep 5373479 = 8060219) B8060219
theorem B3582319 : Blo 2121435 3582319 := bstep (se 1 (by rfl) ⟨2686739, by rfl⟩ : syracuseStep 3582319 = 5373479) B5373479
theorem B4776425 : Blo 2121435 4776425 := bstep (se 2 (by rfl) ⟨1791159, by rfl⟩ : syracuseStep 4776425 = 3582319) B3582319
theorem B3184283 : Blo 2121435 3184283 := bstep (se 1 (by rfl) ⟨2388212, by rfl⟩ : syracuseStep 3184283 = 4776425) B4776425
theorem B2122855 : Blo 2121435 2122855 := bstep (se 1 (by rfl) ⟨1592141, by rfl⟩ : syracuseStep 2122855 = 3184283) B3184283
theorem B2388217 : Blo 2121435 2388217 := bbase (se 2 (by rfl) ⟨895581, by rfl⟩ : syracuseStep 2388217 = 1791163) (by norm_num)
theorem B3184289 : Blo 2121435 3184289 := bstep (se 2 (by rfl) ⟨1194108, by rfl⟩ : syracuseStep 3184289 = 2388217) B2388217
theorem B2122859 : Blo 2121435 2122859 := bstep (se 1 (by rfl) ⟨1592144, by rfl⟩ : syracuseStep 2122859 = 3184289) B3184289
theorem B9067781 : Blo 2121435 9067781 := bbase (se 4 (by rfl) ⟨850104, by rfl⟩ : syracuseStep 9067781 = 1700209) (by norm_num)
theorem B6045187 : Blo 2121435 6045187 := bstep (se 1 (by rfl) ⟨4533890, by rfl⟩ : syracuseStep 6045187 = 9067781) B9067781
theorem B8060249 : Blo 2121435 8060249 := bstep (se 2 (by rfl) ⟨3022593, by rfl⟩ : syracuseStep 8060249 = 6045187) B6045187
theorem B5373499 : Blo 2121435 5373499 := bstep (se 1 (by rfl) ⟨4030124, by rfl⟩ : syracuseStep 5373499 = 8060249) B8060249
theorem B7164665 : Blo 2121435 7164665 := bstep (se 2 (by rfl) ⟨2686749, by rfl⟩ : syracuseStep 7164665 = 5373499) B5373499
theorem B4776443 : Blo 2121435 4776443 := bstep (se 1 (by rfl) ⟨3582332, by rfl⟩ : syracuseStep 4776443 = 7164665) B7164665
theorem B3184295 : Blo 2121435 3184295 := bstep (se 1 (by rfl) ⟨2388221, by rfl⟩ : syracuseStep 3184295 = 4776443) B4776443
theorem B2122863 : Blo 2121435 2122863 := bstep (se 1 (by rfl) ⟨1592147, by rfl⟩ : syracuseStep 2122863 = 3184295) B3184295
theorem B3184301 : Blo 2121435 3184301 := bbase (se 3 (by rfl) ⟨597056, by rfl⟩ : syracuseStep 3184301 = 1194113) (by norm_num)
theorem B2122867 : Blo 2121435 2122867 := bstep (se 1 (by rfl) ⟨1592150, by rfl⟩ : syracuseStep 2122867 = 3184301) B3184301
theorem B4776461 : Blo 2121435 4776461 := bbase (se 3 (by rfl) ⟨895586, by rfl⟩ : syracuseStep 4776461 = 1791173) (by norm_num)
theorem B3184307 : Blo 2121435 3184307 := bstep (se 1 (by rfl) ⟨2388230, by rfl⟩ : syracuseStep 3184307 = 4776461) B4776461
theorem B2122871 : Blo 2121435 2122871 := bstep (se 1 (by rfl) ⟨1592153, by rfl⟩ : syracuseStep 2122871 = 3184307) B3184307
theorem B2686765 : Blo 2121435 2686765 := bbase (se 3 (by rfl) ⟨503768, by rfl⟩ : syracuseStep 2686765 = 1007537) (by norm_num)
theorem B3582353 : Blo 2121435 3582353 := bstep (se 2 (by rfl) ⟨1343382, by rfl⟩ : syracuseStep 3582353 = 2686765) B2686765
theorem B2388235 : Blo 2121435 2388235 := bstep (se 1 (by rfl) ⟨1791176, by rfl⟩ : syracuseStep 2388235 = 3582353) B3582353
theorem B3184313 : Blo 2121435 3184313 := bstep (se 2 (by rfl) ⟨1194117, by rfl⟩ : syracuseStep 3184313 = 2388235) B2388235
theorem B2122875 : Blo 2121435 2122875 := bstep (se 1 (by rfl) ⟨1592156, by rfl⟩ : syracuseStep 2122875 = 3184313) B3184313
theorem B2585129 : Blo 2121435 2585129 := bbase (se 2 (by rfl) ⟨969423, by rfl⟩ : syracuseStep 2585129 = 1938847) (by norm_num)
theorem B6893677 : Blo 2121435 6893677 := bstep (se 3 (by rfl) ⟨1292564, by rfl⟩ : syracuseStep 6893677 = 2585129) B2585129
theorem B9191569 : Blo 2121435 9191569 := bstep (se 2 (by rfl) ⟨3446838, by rfl⟩ : syracuseStep 9191569 = 6893677) B6893677
theorem B12255425 : Blo 2121435 12255425 := bstep (se 2 (by rfl) ⟨4595784, by rfl⟩ : syracuseStep 12255425 = 9191569) B9191569
theorem B8170283 : Blo 2121435 8170283 := bstep (se 1 (by rfl) ⟨6127712, by rfl⟩ : syracuseStep 8170283 = 12255425) B12255425
theorem B5446855 : Blo 2121435 5446855 := bstep (se 1 (by rfl) ⟨4085141, by rfl⟩ : syracuseStep 5446855 = 8170283) B8170283
theorem B7262473 : Blo 2121435 7262473 := bstep (se 2 (by rfl) ⟨2723427, by rfl⟩ : syracuseStep 7262473 = 5446855) B5446855
theorem B9683297 : Blo 2121435 9683297 := bstep (se 2 (by rfl) ⟨3631236, by rfl⟩ : syracuseStep 9683297 = 7262473) B7262473
theorem B6455531 : Blo 2121435 6455531 := bstep (se 1 (by rfl) ⟨4841648, by rfl⟩ : syracuseStep 6455531 = 9683297) B9683297
theorem B4303687 : Blo 2121435 4303687 := bstep (se 1 (by rfl) ⟨3227765, by rfl⟩ : syracuseStep 4303687 = 6455531) B6455531
theorem B5738249 : Blo 2121435 5738249 := bstep (se 2 (by rfl) ⟨2151843, by rfl⟩ : syracuseStep 5738249 = 4303687) B4303687
theorem B3825499 : Blo 2121435 3825499 := bstep (se 1 (by rfl) ⟨2869124, by rfl⟩ : syracuseStep 3825499 = 5738249) B5738249
theorem B5100665 : Blo 2121435 5100665 := bstep (se 2 (by rfl) ⟨1912749, by rfl⟩ : syracuseStep 5100665 = 3825499) B3825499
theorem B13601773 : Blo 2121435 13601773 := bstep (se 3 (by rfl) ⟨2550332, by rfl⟩ : syracuseStep 13601773 = 5100665) B5100665
theorem B18135697 : Blo 2121435 18135697 := bstep (se 2 (by rfl) ⟨6800886, by rfl⟩ : syracuseStep 18135697 = 13601773) B13601773
theorem B24180929 : Blo 2121435 24180929 := bstep (se 2 (by rfl) ⟨9067848, by rfl⟩ : syracuseStep 24180929 = 18135697) B18135697
theorem B16120619 : Blo 2121435 16120619 := bstep (se 1 (by rfl) ⟨12090464, by rfl⟩ : syracuseStep 16120619 = 24180929) B24180929
theorem B10747079 : Blo 2121435 10747079 := bstep (se 1 (by rfl) ⟨8060309, by rfl⟩ : syracuseStep 10747079 = 16120619) B16120619
theorem B7164719 : Blo 2121435 7164719 := bstep (se 1 (by rfl) ⟨5373539, by rfl⟩ : syracuseStep 7164719 = 10747079) B10747079
theorem B4776479 : Blo 2121435 4776479 := bstep (se 1 (by rfl) ⟨3582359, by rfl⟩ : syracuseStep 4776479 = 7164719) B7164719
theorem B3184319 : Blo 2121435 3184319 := bstep (se 1 (by rfl) ⟨2388239, by rfl⟩ : syracuseStep 3184319 = 4776479) B4776479
theorem B2122879 : Blo 2121435 2122879 := bstep (se 1 (by rfl) ⟨1592159, by rfl⟩ : syracuseStep 2122879 = 3184319) B3184319
theorem B3184325 : Blo 2121435 3184325 := bbase (se 4 (by rfl) ⟨298530, by rfl⟩ : syracuseStep 3184325 = 597061) (by norm_num)
theorem B2122883 : Blo 2121435 2122883 := bstep (se 1 (by rfl) ⟨1592162, by rfl⟩ : syracuseStep 2122883 = 3184325) B3184325
theorem B3582373 : Blo 2121435 3582373 := bbase (se 4 (by rfl) ⟨335847, by rfl⟩ : syracuseStep 3582373 = 671695) (by norm_num)
theorem B4776497 : Blo 2121435 4776497 := bstep (se 2 (by rfl) ⟨1791186, by rfl⟩ : syracuseStep 4776497 = 3582373) B3582373
theorem B3184331 : Blo 2121435 3184331 := bstep (se 1 (by rfl) ⟨2388248, by rfl⟩ : syracuseStep 3184331 = 4776497) B4776497
theorem B2122887 : Blo 2121435 2122887 := bstep (se 1 (by rfl) ⟨1592165, by rfl⟩ : syracuseStep 2122887 = 3184331) B3184331
theorem B2388253 : Blo 2121435 2388253 := bbase (se 3 (by rfl) ⟨447797, by rfl⟩ : syracuseStep 2388253 = 895595) (by norm_num)
theorem B3184337 : Blo 2121435 3184337 := bstep (se 2 (by rfl) ⟨1194126, by rfl⟩ : syracuseStep 3184337 = 2388253) B2388253
theorem B2122891 : Blo 2121435 2122891 := bstep (se 1 (by rfl) ⟨1592168, by rfl⟩ : syracuseStep 2122891 = 3184337) B3184337
theorem B7164773 : Blo 2121435 7164773 := bbase (se 4 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 7164773 = 1343395) (by norm_num)
theorem B4776515 : Blo 2121435 4776515 := bstep (se 1 (by rfl) ⟨3582386, by rfl⟩ : syracuseStep 4776515 = 7164773) B7164773
theorem B3184343 : Blo 2121435 3184343 := bstep (se 1 (by rfl) ⟨2388257, by rfl⟩ : syracuseStep 3184343 = 4776515) B4776515
theorem B2122895 : Blo 2121435 2122895 := bstep (se 1 (by rfl) ⟨1592171, by rfl⟩ : syracuseStep 2122895 = 3184343) B3184343
theorem B3184349 : Blo 2121435 3184349 := bbase (se 3 (by rfl) ⟨597065, by rfl⟩ : syracuseStep 3184349 = 1194131) (by norm_num)
theorem B2122899 : Blo 2121435 2122899 := bstep (se 1 (by rfl) ⟨1592174, by rfl⟩ : syracuseStep 2122899 = 3184349) B3184349
theorem B4776533 : Blo 2121435 4776533 := bbase (se 8 (by rfl) ⟨27987, by rfl⟩ : syracuseStep 4776533 = 55975) (by norm_num)
theorem B3184355 : Blo 2121435 3184355 := bstep (se 1 (by rfl) ⟨2388266, by rfl⟩ : syracuseStep 3184355 = 4776533) B4776533
theorem B2122903 : Blo 2121435 2122903 := bstep (se 1 (by rfl) ⟨1592177, by rfl⟩ : syracuseStep 2122903 = 3184355) B3184355
theorem B2420857 : Blo 2121435 2420857 := bbase (se 2 (by rfl) ⟨907821, by rfl⟩ : syracuseStep 2420857 = 1815643) (by norm_num)
theorem B12911237 : Blo 2121435 12911237 := bstep (se 4 (by rfl) ⟨1210428, by rfl⟩ : syracuseStep 12911237 = 2420857) B2420857
theorem B8607491 : Blo 2121435 8607491 := bstep (se 1 (by rfl) ⟨6455618, by rfl⟩ : syracuseStep 8607491 = 12911237) B12911237
theorem B5738327 : Blo 2121435 5738327 := bstep (se 1 (by rfl) ⟨4303745, by rfl⟩ : syracuseStep 5738327 = 8607491) B8607491
theorem B3825551 : Blo 2121435 3825551 := bstep (se 1 (by rfl) ⟨2869163, by rfl⟩ : syracuseStep 3825551 = 5738327) B5738327
theorem B2550367 : Blo 2121435 2550367 := bstep (se 1 (by rfl) ⟨1912775, by rfl⟩ : syracuseStep 2550367 = 3825551) B3825551
theorem B3400489 : Blo 2121435 3400489 := bstep (se 2 (by rfl) ⟨1275183, by rfl⟩ : syracuseStep 3400489 = 2550367) B2550367
theorem B4533985 : Blo 2121435 4533985 := bstep (se 2 (by rfl) ⟨1700244, by rfl⟩ : syracuseStep 4533985 = 3400489) B3400489
theorem B6045313 : Blo 2121435 6045313 := bstep (se 2 (by rfl) ⟨2266992, by rfl⟩ : syracuseStep 6045313 = 4533985) B4533985
theorem B8060417 : Blo 2121435 8060417 := bstep (se 2 (by rfl) ⟨3022656, by rfl⟩ : syracuseStep 8060417 = 6045313) B6045313
theorem B5373611 : Blo 2121435 5373611 := bstep (se 1 (by rfl) ⟨4030208, by rfl⟩ : syracuseStep 5373611 = 8060417) B8060417
theorem B3582407 : Blo 2121435 3582407 := bstep (se 1 (by rfl) ⟨2686805, by rfl⟩ : syracuseStep 3582407 = 5373611) B5373611
theorem B2388271 : Blo 2121435 2388271 := bstep (se 1 (by rfl) ⟨1791203, by rfl⟩ : syracuseStep 2388271 = 3582407) B3582407
theorem B3184361 : Blo 2121435 3184361 := bstep (se 2 (by rfl) ⟨1194135, by rfl⟩ : syracuseStep 3184361 = 2388271) B2388271
theorem B2122907 : Blo 2121435 2122907 := bstep (se 1 (by rfl) ⟨1592180, by rfl⟩ : syracuseStep 2122907 = 3184361) B3184361
theorem B3825557 : Blo 2121435 3825557 := bbase (se 6 (by rfl) ⟨89661, by rfl⟩ : syracuseStep 3825557 = 179323) (by norm_num)
theorem B2550371 : Blo 2121435 2550371 := bstep (se 1 (by rfl) ⟨1912778, by rfl⟩ : syracuseStep 2550371 = 3825557) B3825557
theorem B27203957 : Blo 2121435 27203957 := bstep (se 5 (by rfl) ⟨1275185, by rfl⟩ : syracuseStep 27203957 = 2550371) B2550371
theorem B18135971 : Blo 2121435 18135971 := bstep (se 1 (by rfl) ⟨13601978, by rfl⟩ : syracuseStep 18135971 = 27203957) B27203957
theorem B12090647 : Blo 2121435 12090647 := bstep (se 1 (by rfl) ⟨9067985, by rfl⟩ : syracuseStep 12090647 = 18135971) B18135971
theorem B8060431 : Blo 2121435 8060431 := bstep (se 1 (by rfl) ⟨6045323, by rfl⟩ : syracuseStep 8060431 = 12090647) B12090647
theorem B10747241 : Blo 2121435 10747241 := bstep (se 2 (by rfl) ⟨4030215, by rfl⟩ : syracuseStep 10747241 = 8060431) B8060431
theorem B7164827 : Blo 2121435 7164827 := bstep (se 1 (by rfl) ⟨5373620, by rfl⟩ : syracuseStep 7164827 = 10747241) B10747241
theorem B4776551 : Blo 2121435 4776551 := bstep (se 1 (by rfl) ⟨3582413, by rfl⟩ : syracuseStep 4776551 = 7164827) B7164827
theorem B3184367 : Blo 2121435 3184367 := bstep (se 1 (by rfl) ⟨2388275, by rfl⟩ : syracuseStep 3184367 = 4776551) B4776551
theorem B2122911 : Blo 2121435 2122911 := bstep (se 1 (by rfl) ⟨1592183, by rfl⟩ : syracuseStep 2122911 = 3184367) B3184367
theorem B3184373 : Blo 2121435 3184373 := bbase (se 5 (by rfl) ⟨149267, by rfl⟩ : syracuseStep 3184373 = 298535) (by norm_num)
theorem B2122915 : Blo 2121435 2122915 := bstep (se 1 (by rfl) ⟨1592186, by rfl⟩ : syracuseStep 2122915 = 3184373) B3184373
theorem B9068021 : Blo 2121435 9068021 := bbase (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) (by norm_num)
theorem B6045347 : Blo 2121435 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B4030231 : Blo 2121435 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B5373641 : Blo 2121435 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B3582427 : Blo 2121435 3582427 := bstep (se 1 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 3582427 = 5373641) B5373641
theorem B4776569 : Blo 2121435 4776569 := bstep (se 2 (by rfl) ⟨1791213, by rfl⟩ : syracuseStep 4776569 = 3582427) B3582427
theorem B3184379 : Blo 2121435 3184379 := bstep (se 1 (by rfl) ⟨2388284, by rfl⟩ : syracuseStep 3184379 = 4776569) B4776569
theorem B2122919 : Blo 2121435 2122919 := bstep (se 1 (by rfl) ⟨1592189, by rfl⟩ : syracuseStep 2122919 = 3184379) B3184379
theorem B2388289 : Blo 2121435 2388289 := bbase (se 2 (by rfl) ⟨895608, by rfl⟩ : syracuseStep 2388289 = 1791217) (by norm_num)
theorem B3184385 : Blo 2121435 3184385 := bstep (se 2 (by rfl) ⟨1194144, by rfl⟩ : syracuseStep 3184385 = 2388289) B2388289
theorem B2122923 : Blo 2121435 2122923 := bstep (se 1 (by rfl) ⟨1592192, by rfl⟩ : syracuseStep 2122923 = 3184385) B3184385
theorem B5373661 : Blo 2121435 5373661 := bbase (se 3 (by rfl) ⟨1007561, by rfl⟩ : syracuseStep 5373661 = 2015123) (by norm_num)
theorem B7164881 : Blo 2121435 7164881 := bstep (se 2 (by rfl) ⟨2686830, by rfl⟩ : syracuseStep 7164881 = 5373661) B5373661
theorem B4776587 : Blo 2121435 4776587 := bstep (se 1 (by rfl) ⟨3582440, by rfl⟩ : syracuseStep 4776587 = 7164881) B7164881
theorem B3184391 : Blo 2121435 3184391 := bstep (se 1 (by rfl) ⟨2388293, by rfl⟩ : syracuseStep 3184391 = 4776587) B4776587
theorem B2122927 : Blo 2121435 2122927 := bstep (se 1 (by rfl) ⟨1592195, by rfl⟩ : syracuseStep 2122927 = 3184391) B3184391
theorem B3184397 : Blo 2121435 3184397 := bbase (se 3 (by rfl) ⟨597074, by rfl⟩ : syracuseStep 3184397 = 1194149) (by norm_num)
theorem B2122931 : Blo 2121435 2122931 := bstep (se 1 (by rfl) ⟨1592198, by rfl⟩ : syracuseStep 2122931 = 3184397) B3184397
theorem B4776605 : Blo 2121435 4776605 := bbase (se 3 (by rfl) ⟨895613, by rfl⟩ : syracuseStep 4776605 = 1791227) (by norm_num)
theorem B3184403 : Blo 2121435 3184403 := bstep (se 1 (by rfl) ⟨2388302, by rfl⟩ : syracuseStep 3184403 = 4776605) B4776605
theorem B2122935 : Blo 2121435 2122935 := bstep (se 1 (by rfl) ⟨1592201, by rfl⟩ : syracuseStep 2122935 = 3184403) B3184403
theorem B3582461 : Blo 2121435 3582461 := bbase (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) (by norm_num)
theorem B2388307 : Blo 2121435 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B3184409 : Blo 2121435 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B2122939 : Blo 2121435 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B4534061 : Blo 2121435 4534061 := bbase (se 3 (by rfl) ⟨850136, by rfl⟩ : syracuseStep 4534061 = 1700273) (by norm_num)
theorem B12090829 : Blo 2121435 12090829 := bstep (se 3 (by rfl) ⟨2267030, by rfl⟩ : syracuseStep 12090829 = 4534061) B4534061
theorem B16121105 : Blo 2121435 16121105 := bstep (se 2 (by rfl) ⟨6045414, by rfl⟩ : syracuseStep 16121105 = 12090829) B12090829
theorem B10747403 : Blo 2121435 10747403 := bstep (se 1 (by rfl) ⟨8060552, by rfl⟩ : syracuseStep 10747403 = 16121105) B16121105
theorem B7164935 : Blo 2121435 7164935 := bstep (se 1 (by rfl) ⟨5373701, by rfl⟩ : syracuseStep 7164935 = 10747403) B10747403
theorem B4776623 : Blo 2121435 4776623 := bstep (se 1 (by rfl) ⟨3582467, by rfl⟩ : syracuseStep 4776623 = 7164935) B7164935
theorem B3184415 : Blo 2121435 3184415 := bstep (se 1 (by rfl) ⟨2388311, by rfl⟩ : syracuseStep 3184415 = 4776623) B4776623
theorem B2122943 : Blo 2121435 2122943 := bstep (se 1 (by rfl) ⟨1592207, by rfl⟩ : syracuseStep 2122943 = 3184415) B3184415
theorem B3184421 : Blo 2121435 3184421 := bbase (se 4 (by rfl) ⟨298539, by rfl⟩ : syracuseStep 3184421 = 597079) (by norm_num)
theorem B2122947 : Blo 2121435 2122947 := bstep (se 1 (by rfl) ⟨1592210, by rfl⟩ : syracuseStep 2122947 = 3184421) B3184421
theorem B2686861 : Blo 2121435 2686861 := bbase (se 3 (by rfl) ⟨503786, by rfl⟩ : syracuseStep 2686861 = 1007573) (by norm_num)
theorem B3582481 : Blo 2121435 3582481 := bstep (se 2 (by rfl) ⟨1343430, by rfl⟩ : syracuseStep 3582481 = 2686861) B2686861
theorem B4776641 : Blo 2121435 4776641 := bstep (se 2 (by rfl) ⟨1791240, by rfl⟩ : syracuseStep 4776641 = 3582481) B3582481
theorem B3184427 : Blo 2121435 3184427 := bstep (se 1 (by rfl) ⟨2388320, by rfl⟩ : syracuseStep 3184427 = 4776641) B4776641
theorem B2122951 : Blo 2121435 2122951 := bstep (se 1 (by rfl) ⟨1592213, by rfl⟩ : syracuseStep 2122951 = 3184427) B3184427
theorem B2388325 : Blo 2121435 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B3184433 : Blo 2121435 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B2122955 : Blo 2121435 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B6045461 : Blo 2121435 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B4030307 : Blo 2121435 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B2686871 : Blo 2121435 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B7164989 : Blo 2121435 7164989 := bstep (se 3 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 7164989 = 2686871) B2686871
theorem B4776659 : Blo 2121435 4776659 := bstep (se 1 (by rfl) ⟨3582494, by rfl⟩ : syracuseStep 4776659 = 7164989) B7164989
theorem B3184439 : Blo 2121435 3184439 := bstep (se 1 (by rfl) ⟨2388329, by rfl⟩ : syracuseStep 3184439 = 4776659) B4776659
theorem B2122959 : Blo 2121435 2122959 := bstep (se 1 (by rfl) ⟨1592219, by rfl⟩ : syracuseStep 2122959 = 3184439) B3184439
theorem B3184445 : Blo 2121435 3184445 := bbase (se 3 (by rfl) ⟨597083, by rfl⟩ : syracuseStep 3184445 = 1194167) (by norm_num)
theorem B2122963 : Blo 2121435 2122963 := bstep (se 1 (by rfl) ⟨1592222, by rfl⟩ : syracuseStep 2122963 = 3184445) B3184445
theorem B4776677 : Blo 2121435 4776677 := bbase (se 4 (by rfl) ⟨447813, by rfl⟩ : syracuseStep 4776677 = 895627) (by norm_num)
theorem B3184451 : Blo 2121435 3184451 := bstep (se 1 (by rfl) ⟨2388338, by rfl⟩ : syracuseStep 3184451 = 4776677) B4776677
theorem B2122967 : Blo 2121435 2122967 := bstep (se 1 (by rfl) ⟨1592225, by rfl⟩ : syracuseStep 2122967 = 3184451) B3184451
theorem B5373773 : Blo 2121435 5373773 := bbase (se 3 (by rfl) ⟨1007582, by rfl⟩ : syracuseStep 5373773 = 2015165) (by norm_num)
theorem B3582515 : Blo 2121435 3582515 := bstep (se 1 (by rfl) ⟨2686886, by rfl⟩ : syracuseStep 3582515 = 5373773) B5373773
theorem B2388343 : Blo 2121435 2388343 := bstep (se 1 (by rfl) ⟨1791257, by rfl⟩ : syracuseStep 2388343 = 3582515) B3582515
theorem B3184457 : Blo 2121435 3184457 := bstep (se 2 (by rfl) ⟨1194171, by rfl⟩ : syracuseStep 3184457 = 2388343) B2388343
theorem B2122971 : Blo 2121435 2122971 := bstep (se 1 (by rfl) ⟨1592228, by rfl⟩ : syracuseStep 2122971 = 3184457) B3184457
theorem B2267065 : Blo 2121435 2267065 := bbase (se 2 (by rfl) ⟨850149, by rfl⟩ : syracuseStep 2267065 = 1700299) (by norm_num)
theorem B3022753 : Blo 2121435 3022753 := bstep (se 2 (by rfl) ⟨1133532, by rfl⟩ : syracuseStep 3022753 = 2267065) B2267065
theorem B4030337 : Blo 2121435 4030337 := bstep (se 2 (by rfl) ⟨1511376, by rfl⟩ : syracuseStep 4030337 = 3022753) B3022753
theorem B10747565 : Blo 2121435 10747565 := bstep (se 3 (by rfl) ⟨2015168, by rfl⟩ : syracuseStep 10747565 = 4030337) B4030337
theorem B7165043 : Blo 2121435 7165043 := bstep (se 1 (by rfl) ⟨5373782, by rfl⟩ : syracuseStep 7165043 = 10747565) B10747565
theorem B4776695 : Blo 2121435 4776695 := bstep (se 1 (by rfl) ⟨3582521, by rfl⟩ : syracuseStep 4776695 = 7165043) B7165043
theorem B3184463 : Blo 2121435 3184463 := bstep (se 1 (by rfl) ⟨2388347, by rfl⟩ : syracuseStep 3184463 = 4776695) B4776695
theorem B2122975 : Blo 2121435 2122975 := bstep (se 1 (by rfl) ⟨1592231, by rfl⟩ : syracuseStep 2122975 = 3184463) B3184463
theorem B3184469 : Blo 2121435 3184469 := bbase (se 9 (by rfl) ⟨9329, by rfl⟩ : syracuseStep 3184469 = 18659) (by norm_num)
theorem B2122979 : Blo 2121435 2122979 := bstep (se 1 (by rfl) ⟨1592234, by rfl⟩ : syracuseStep 2122979 = 3184469) B3184469
theorem B6801221 : Blo 2121435 6801221 := bbase (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) (by norm_num)
theorem B4534147 : Blo 2121435 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B6045529 : Blo 2121435 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B8060705 : Blo 2121435 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B5373803 : Blo 2121435 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B3582535 : Blo 2121435 3582535 := bstep (se 1 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 3582535 = 5373803) B5373803
theorem B4776713 : Blo 2121435 4776713 := bstep (se 2 (by rfl) ⟨1791267, by rfl⟩ : syracuseStep 4776713 = 3582535) B3582535
theorem B3184475 : Blo 2121435 3184475 := bstep (se 1 (by rfl) ⟨2388356, by rfl⟩ : syracuseStep 3184475 = 4776713) B4776713
theorem B2122983 : Blo 2121435 2122983 := bstep (se 1 (by rfl) ⟨1592237, by rfl⟩ : syracuseStep 2122983 = 3184475) B3184475
theorem B2388361 : Blo 2121435 2388361 := bbase (se 2 (by rfl) ⟨895635, by rfl⟩ : syracuseStep 2388361 = 1791271) (by norm_num)
theorem B3184481 : Blo 2121435 3184481 := bstep (se 2 (by rfl) ⟨1194180, by rfl⟩ : syracuseStep 3184481 = 2388361) B2388361
theorem B2122987 : Blo 2121435 2122987 := bstep (se 1 (by rfl) ⟨1592240, by rfl⟩ : syracuseStep 2122987 = 3184481) B3184481
theorem B2298013 : Blo 2121435 2298013 := bbase (se 3 (by rfl) ⟨430877, by rfl⟩ : syracuseStep 2298013 = 861755) (by norm_num)
theorem B12256069 : Blo 2121435 12256069 := bstep (se 4 (by rfl) ⟨1149006, by rfl⟩ : syracuseStep 12256069 = 2298013) B2298013
theorem B16341425 : Blo 2121435 16341425 := bstep (se 2 (by rfl) ⟨6128034, by rfl⟩ : syracuseStep 16341425 = 12256069) B12256069
theorem B10894283 : Blo 2121435 10894283 := bstep (se 1 (by rfl) ⟨8170712, by rfl⟩ : syracuseStep 10894283 = 16341425) B16341425
theorem B7262855 : Blo 2121435 7262855 := bstep (se 1 (by rfl) ⟨5447141, by rfl⟩ : syracuseStep 7262855 = 10894283) B10894283
theorem B4841903 : Blo 2121435 4841903 := bstep (se 1 (by rfl) ⟨3631427, by rfl⟩ : syracuseStep 4841903 = 7262855) B7262855
theorem B12911741 : Blo 2121435 12911741 := bstep (se 3 (by rfl) ⟨2420951, by rfl⟩ : syracuseStep 12911741 = 4841903) B4841903
theorem B8607827 : Blo 2121435 8607827 := bstep (se 1 (by rfl) ⟨6455870, by rfl⟩ : syracuseStep 8607827 = 12911741) B12911741
theorem B22954205 : Blo 2121435 22954205 := bstep (se 3 (by rfl) ⟨4303913, by rfl⟩ : syracuseStep 22954205 = 8607827) B8607827
theorem B61211213 : Blo 2121435 61211213 := bstep (se 3 (by rfl) ⟨11477102, by rfl⟩ : syracuseStep 61211213 = 22954205) B22954205
theorem B40807475 : Blo 2121435 40807475 := bstep (se 1 (by rfl) ⟨30605606, by rfl⟩ : syracuseStep 40807475 = 61211213) B61211213
theorem B27204983 : Blo 2121435 27204983 := bstep (se 1 (by rfl) ⟨20403737, by rfl⟩ : syracuseStep 27204983 = 40807475) B40807475
theorem B18136655 : Blo 2121435 18136655 := bstep (se 1 (by rfl) ⟨13602491, by rfl⟩ : syracuseStep 18136655 = 27204983) B27204983
theorem B12091103 : Blo 2121435 12091103 := bstep (se 1 (by rfl) ⟨9068327, by rfl⟩ : syracuseStep 12091103 = 18136655) B18136655
theorem B8060735 : Blo 2121435 8060735 := bstep (se 1 (by rfl) ⟨6045551, by rfl⟩ : syracuseStep 8060735 = 12091103) B12091103
theorem B5373823 : Blo 2121435 5373823 := bstep (se 1 (by rfl) ⟨4030367, by rfl⟩ : syracuseStep 5373823 = 8060735) B8060735
theorem B7165097 : Blo 2121435 7165097 := bstep (se 2 (by rfl) ⟨2686911, by rfl⟩ : syracuseStep 7165097 = 5373823) B5373823
theorem B4776731 : Blo 2121435 4776731 := bstep (se 1 (by rfl) ⟨3582548, by rfl⟩ : syracuseStep 4776731 = 7165097) B7165097
theorem B3184487 : Blo 2121435 3184487 := bstep (se 1 (by rfl) ⟨2388365, by rfl⟩ : syracuseStep 3184487 = 4776731) B4776731
theorem B2122991 : Blo 2121435 2122991 := bstep (se 1 (by rfl) ⟨1592243, by rfl⟩ : syracuseStep 2122991 = 3184487) B3184487
theorem B3184493 : Blo 2121435 3184493 := bbase (se 3 (by rfl) ⟨597092, by rfl⟩ : syracuseStep 3184493 = 1194185) (by norm_num)
theorem B2122995 : Blo 2121435 2122995 := bstep (se 1 (by rfl) ⟨1592246, by rfl⟩ : syracuseStep 2122995 = 3184493) B3184493
theorem B4776749 : Blo 2121435 4776749 := bbase (se 3 (by rfl) ⟨895640, by rfl⟩ : syracuseStep 4776749 = 1791281) (by norm_num)
theorem B3184499 : Blo 2121435 3184499 := bstep (se 1 (by rfl) ⟨2388374, by rfl⟩ : syracuseStep 3184499 = 4776749) B4776749
theorem B2122999 : Blo 2121435 2122999 := bstep (se 1 (by rfl) ⟨1592249, by rfl⟩ : syracuseStep 2122999 = 3184499) B3184499
theorem B5100965 : Blo 2121435 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B3400643 : Blo 2121435 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B9068381 : Blo 2121435 9068381 := bstep (se 3 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 9068381 = 3400643) B3400643
theorem B6045587 : Blo 2121435 6045587 := bstep (se 1 (by rfl) ⟨4534190, by rfl⟩ : syracuseStep 6045587 = 9068381) B9068381
theorem B4030391 : Blo 2121435 4030391 := bstep (se 1 (by rfl) ⟨3022793, by rfl⟩ : syracuseStep 4030391 = 6045587) B6045587
theorem B2686927 : Blo 2121435 2686927 := bstep (se 1 (by rfl) ⟨2015195, by rfl⟩ : syracuseStep 2686927 = 4030391) B4030391
theorem B3582569 : Blo 2121435 3582569 := bstep (se 2 (by rfl) ⟨1343463, by rfl⟩ : syracuseStep 3582569 = 2686927) B2686927
theorem B2388379 : Blo 2121435 2388379 := bstep (se 1 (by rfl) ⟨1791284, by rfl⟩ : syracuseStep 2388379 = 3582569) B3582569
theorem B3184505 : Blo 2121435 3184505 := bstep (se 2 (by rfl) ⟨1194189, by rfl⟩ : syracuseStep 3184505 = 2388379) B2388379
theorem B2123003 : Blo 2121435 2123003 := bstep (se 1 (by rfl) ⟨1592252, by rfl⟩ : syracuseStep 2123003 = 3184505) B3184505
theorem B2151973 : Blo 2121435 2151973 := bbase (se 4 (by rfl) ⟨201747, by rfl⟩ : syracuseStep 2151973 = 403495) (by norm_num)
theorem B11477189 : Blo 2121435 11477189 := bstep (se 4 (by rfl) ⟨1075986, by rfl⟩ : syracuseStep 11477189 = 2151973) B2151973
theorem B7651459 : Blo 2121435 7651459 := bstep (se 1 (by rfl) ⟨5738594, by rfl⟩ : syracuseStep 7651459 = 11477189) B11477189
theorem B10201945 : Blo 2121435 10201945 := bstep (se 2 (by rfl) ⟨3825729, by rfl⟩ : syracuseStep 10201945 = 7651459) B7651459
theorem B13602593 : Blo 2121435 13602593 := bstep (se 2 (by rfl) ⟨5100972, by rfl⟩ : syracuseStep 13602593 = 10201945) B10201945
theorem B36273581 : Blo 2121435 36273581 := bstep (se 3 (by rfl) ⟨6801296, by rfl⟩ : syracuseStep 36273581 = 13602593) B13602593
theorem B24182387 : Blo 2121435 24182387 := bstep (se 1 (by rfl) ⟨18136790, by rfl⟩ : syracuseStep 24182387 = 36273581) B36273581
theorem B16121591 : Blo 2121435 16121591 := bstep (se 1 (by rfl) ⟨12091193, by rfl⟩ : syracuseStep 16121591 = 24182387) B24182387
theorem B10747727 : Blo 2121435 10747727 := bstep (se 1 (by rfl) ⟨8060795, by rfl⟩ : syracuseStep 10747727 = 16121591) B16121591
theorem B7165151 : Blo 2121435 7165151 := bstep (se 1 (by rfl) ⟨5373863, by rfl⟩ : syracuseStep 7165151 = 10747727) B10747727
theorem B4776767 : Blo 2121435 4776767 := bstep (se 1 (by rfl) ⟨3582575, by rfl⟩ : syracuseStep 4776767 = 7165151) B7165151
theorem B3184511 : Blo 2121435 3184511 := bstep (se 1 (by rfl) ⟨2388383, by rfl⟩ : syracuseStep 3184511 = 4776767) B4776767
theorem B2123007 : Blo 2121435 2123007 := bstep (se 1 (by rfl) ⟨1592255, by rfl⟩ : syracuseStep 2123007 = 3184511) B3184511
theorem B3184517 : Blo 2121435 3184517 := bbase (se 4 (by rfl) ⟨298548, by rfl⟩ : syracuseStep 3184517 = 597097) (by norm_num)
theorem B2123011 : Blo 2121435 2123011 := bstep (se 1 (by rfl) ⟨1592258, by rfl⟩ : syracuseStep 2123011 = 3184517) B3184517
theorem B3582589 : Blo 2121435 3582589 := bbase (se 3 (by rfl) ⟨671735, by rfl⟩ : syracuseStep 3582589 = 1343471) (by norm_num)
theorem B4776785 : Blo 2121435 4776785 := bstep (se 2 (by rfl) ⟨1791294, by rfl⟩ : syracuseStep 4776785 = 3582589) B3582589
theorem B3184523 : Blo 2121435 3184523 := bstep (se 1 (by rfl) ⟨2388392, by rfl⟩ : syracuseStep 3184523 = 4776785) B4776785
theorem B2123015 : Blo 2121435 2123015 := bstep (se 1 (by rfl) ⟨1592261, by rfl⟩ : syracuseStep 2123015 = 3184523) B3184523
theorem B2388397 : Blo 2121435 2388397 := bbase (se 3 (by rfl) ⟨447824, by rfl⟩ : syracuseStep 2388397 = 895649) (by norm_num)
theorem B3184529 : Blo 2121435 3184529 := bstep (se 2 (by rfl) ⟨1194198, by rfl⟩ : syracuseStep 3184529 = 2388397) B2388397
theorem B2123019 : Blo 2121435 2123019 := bstep (se 1 (by rfl) ⟨1592264, by rfl⟩ : syracuseStep 2123019 = 3184529) B3184529
theorem B7165205 : Blo 2121435 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B4776803 : Blo 2121435 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B3184535 : Blo 2121435 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B2123023 : Blo 2121435 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B3184541 : Blo 2121435 3184541 := bbase (se 3 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 3184541 = 1194203) (by norm_num)
theorem B2123027 : Blo 2121435 2123027 := bstep (se 1 (by rfl) ⟨1592270, by rfl⟩ : syracuseStep 2123027 = 3184541) B3184541
theorem B4776821 : Blo 2121435 4776821 := bbase (se 5 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 4776821 = 447827) (by norm_num)
theorem B3184547 : Blo 2121435 3184547 := bstep (se 1 (by rfl) ⟨2388410, by rfl⟩ : syracuseStep 3184547 = 4776821) B4776821
theorem B2123031 : Blo 2121435 2123031 := bstep (se 1 (by rfl) ⟨1592273, by rfl⟩ : syracuseStep 2123031 = 3184547) B3184547
theorem B2298061 : Blo 2121435 2298061 := bbase (se 3 (by rfl) ⟨430886, by rfl⟩ : syracuseStep 2298061 = 861773) (by norm_num)
theorem B12256325 : Blo 2121435 12256325 := bstep (se 4 (by rfl) ⟨1149030, by rfl⟩ : syracuseStep 12256325 = 2298061) B2298061
theorem B8170883 : Blo 2121435 8170883 := bstep (se 1 (by rfl) ⟨6128162, by rfl⟩ : syracuseStep 8170883 = 12256325) B12256325
theorem B5447255 : Blo 2121435 5447255 := bstep (se 1 (by rfl) ⟨4085441, by rfl⟩ : syracuseStep 5447255 = 8170883) B8170883
theorem B14526013 : Blo 2121435 14526013 := bstep (se 3 (by rfl) ⟨2723627, by rfl⟩ : syracuseStep 14526013 = 5447255) B5447255
theorem B19368017 : Blo 2121435 19368017 := bstep (se 2 (by rfl) ⟨7263006, by rfl⟩ : syracuseStep 19368017 = 14526013) B14526013
theorem B12912011 : Blo 2121435 12912011 := bstep (se 1 (by rfl) ⟨9684008, by rfl⟩ : syracuseStep 12912011 = 19368017) B19368017
theorem B8608007 : Blo 2121435 8608007 := bstep (se 1 (by rfl) ⟨6456005, by rfl⟩ : syracuseStep 8608007 = 12912011) B12912011
theorem B5738671 : Blo 2121435 5738671 := bstep (se 1 (by rfl) ⟨4304003, by rfl⟩ : syracuseStep 5738671 = 8608007) B8608007
theorem B30606245 : Blo 2121435 30606245 := bstep (se 4 (by rfl) ⟨2869335, by rfl⟩ : syracuseStep 30606245 = 5738671) B5738671
theorem B20404163 : Blo 2121435 20404163 := bstep (se 1 (by rfl) ⟨15303122, by rfl⟩ : syracuseStep 20404163 = 30606245) B30606245
theorem B13602775 : Blo 2121435 13602775 := bstep (se 1 (by rfl) ⟨10202081, by rfl⟩ : syracuseStep 13602775 = 20404163) B20404163
theorem B18137033 : Blo 2121435 18137033 := bstep (se 2 (by rfl) ⟨6801387, by rfl⟩ : syracuseStep 18137033 = 13602775) B13602775
theorem B12091355 : Blo 2121435 12091355 := bstep (se 1 (by rfl) ⟨9068516, by rfl⟩ : syracuseStep 12091355 = 18137033) B18137033
theorem B8060903 : Blo 2121435 8060903 := bstep (se 1 (by rfl) ⟨6045677, by rfl⟩ : syracuseStep 8060903 = 12091355) B12091355
theorem B5373935 : Blo 2121435 5373935 := bstep (se 1 (by rfl) ⟨4030451, by rfl⟩ : syracuseStep 5373935 = 8060903) B8060903
theorem B3582623 : Blo 2121435 3582623 := bstep (se 1 (by rfl) ⟨2686967, by rfl⟩ : syracuseStep 3582623 = 5373935) B5373935
theorem B2388415 : Blo 2121435 2388415 := bstep (se 1 (by rfl) ⟨1791311, by rfl⟩ : syracuseStep 2388415 = 3582623) B3582623
theorem B3184553 : Blo 2121435 3184553 := bstep (se 2 (by rfl) ⟨1194207, by rfl⟩ : syracuseStep 3184553 = 2388415) B2388415
theorem B2123035 : Blo 2121435 2123035 := bstep (se 1 (by rfl) ⟨1592276, by rfl⟩ : syracuseStep 2123035 = 3184553) B3184553
theorem B8060917 : Blo 2121435 8060917 := bbase (se 5 (by rfl) ⟨377855, by rfl⟩ : syracuseStep 8060917 = 755711) (by norm_num)
theorem B10747889 : Blo 2121435 10747889 := bstep (se 2 (by rfl) ⟨4030458, by rfl⟩ : syracuseStep 10747889 = 8060917) B8060917
theorem B7165259 : Blo 2121435 7165259 := bstep (se 1 (by rfl) ⟨5373944, by rfl⟩ : syracuseStep 7165259 = 10747889) B10747889
theorem B4776839 : Blo 2121435 4776839 := bstep (se 1 (by rfl) ⟨3582629, by rfl⟩ : syracuseStep 4776839 = 7165259) B7165259
theorem B3184559 : Blo 2121435 3184559 := bstep (se 1 (by rfl) ⟨2388419, by rfl⟩ : syracuseStep 3184559 = 4776839) B4776839
theorem B2123039 : Blo 2121435 2123039 := bstep (se 1 (by rfl) ⟨1592279, by rfl⟩ : syracuseStep 2123039 = 3184559) B3184559
theorem B3184565 : Blo 2121435 3184565 := bbase (se 5 (by rfl) ⟨149276, by rfl⟩ : syracuseStep 3184565 = 298553) (by norm_num)
theorem B2123043 : Blo 2121435 2123043 := bstep (se 1 (by rfl) ⟨1592282, by rfl⟩ : syracuseStep 2123043 = 3184565) B3184565
theorem B5373965 : Blo 2121435 5373965 := bbase (se 3 (by rfl) ⟨1007618, by rfl⟩ : syracuseStep 5373965 = 2015237) (by norm_num)
theorem B3582643 : Blo 2121435 3582643 := bstep (se 1 (by rfl) ⟨2686982, by rfl⟩ : syracuseStep 3582643 = 5373965) B5373965
theorem B4776857 : Blo 2121435 4776857 := bstep (se 2 (by rfl) ⟨1791321, by rfl⟩ : syracuseStep 4776857 = 3582643) B3582643
theorem B3184571 : Blo 2121435 3184571 := bstep (se 1 (by rfl) ⟨2388428, by rfl⟩ : syracuseStep 3184571 = 4776857) B4776857
theorem B2123047 : Blo 2121435 2123047 := bstep (se 1 (by rfl) ⟨1592285, by rfl⟩ : syracuseStep 2123047 = 3184571) B3184571
theorem B2388433 : Blo 2121435 2388433 := bbase (se 2 (by rfl) ⟨895662, by rfl⟩ : syracuseStep 2388433 = 1791325) (by norm_num)
theorem B3184577 : Blo 2121435 3184577 := bstep (se 2 (by rfl) ⟨1194216, by rfl⟩ : syracuseStep 3184577 = 2388433) B2388433
theorem B2123051 : Blo 2121435 2123051 := bstep (se 1 (by rfl) ⟨1592288, by rfl⟩ : syracuseStep 2123051 = 3184577) B3184577
theorem B4534301 : Blo 2121435 4534301 := bbase (se 3 (by rfl) ⟨850181, by rfl⟩ : syracuseStep 4534301 = 1700363) (by norm_num)
theorem B3022867 : Blo 2121435 3022867 := bstep (se 1 (by rfl) ⟨2267150, by rfl⟩ : syracuseStep 3022867 = 4534301) B4534301
theorem B4030489 : Blo 2121435 4030489 := bstep (se 2 (by rfl) ⟨1511433, by rfl⟩ : syracuseStep 4030489 = 3022867) B3022867
theorem B5373985 : Blo 2121435 5373985 := bstep (se 2 (by rfl) ⟨2015244, by rfl⟩ : syracuseStep 5373985 = 4030489) B4030489
theorem B7165313 : Blo 2121435 7165313 := bstep (se 2 (by rfl) ⟨2686992, by rfl⟩ : syracuseStep 7165313 = 5373985) B5373985
theorem B4776875 : Blo 2121435 4776875 := bstep (se 1 (by rfl) ⟨3582656, by rfl⟩ : syracuseStep 4776875 = 7165313) B7165313
theorem B3184583 : Blo 2121435 3184583 := bstep (se 1 (by rfl) ⟨2388437, by rfl⟩ : syracuseStep 3184583 = 4776875) B4776875
theorem B2123055 : Blo 2121435 2123055 := bstep (se 1 (by rfl) ⟨1592291, by rfl⟩ : syracuseStep 2123055 = 3184583) B3184583
theorem B3184589 : Blo 2121435 3184589 := bbase (se 3 (by rfl) ⟨597110, by rfl⟩ : syracuseStep 3184589 = 1194221) (by norm_num)
theorem B2123059 : Blo 2121435 2123059 := bstep (se 1 (by rfl) ⟨1592294, by rfl⟩ : syracuseStep 2123059 = 3184589) B3184589
theorem B4776893 : Blo 2121435 4776893 := bbase (se 3 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 4776893 = 1791335) (by norm_num)
theorem B3184595 : Blo 2121435 3184595 := bstep (se 1 (by rfl) ⟨2388446, by rfl⟩ : syracuseStep 3184595 = 4776893) B4776893
theorem B2123063 : Blo 2121435 2123063 := bstep (se 1 (by rfl) ⟨1592297, by rfl⟩ : syracuseStep 2123063 = 3184595) B3184595
theorem B3582677 : Blo 2121435 3582677 := bbase (se 7 (by rfl) ⟨41984, by rfl⟩ : syracuseStep 3582677 = 83969) (by norm_num)
theorem B2388451 : Blo 2121435 2388451 := bstep (se 1 (by rfl) ⟨1791338, by rfl⟩ : syracuseStep 2388451 = 3582677) B3582677
theorem B3184601 : Blo 2121435 3184601 := bstep (se 2 (by rfl) ⟨1194225, by rfl⟩ : syracuseStep 3184601 = 2388451) B2388451
theorem B2123067 : Blo 2121435 2123067 := bstep (se 1 (by rfl) ⟨1592300, by rfl⟩ : syracuseStep 2123067 = 3184601) B3184601
theorem B3631565 : Blo 2121435 3631565 := bbase (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) (by norm_num)
theorem B9684173 : Blo 2121435 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B6456115 : Blo 2121435 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B8608153 : Blo 2121435 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B11477537 : Blo 2121435 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B7651691 : Blo 2121435 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B5101127 : Blo 2121435 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B3400751 : Blo 2121435 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B9068669 : Blo 2121435 9068669 := bstep (se 3 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 9068669 = 3400751) B3400751
theorem B6045779 : Blo 2121435 6045779 := bstep (se 1 (by rfl) ⟨4534334, by rfl⟩ : syracuseStep 6045779 = 9068669) B9068669
theorem B16122077 : Blo 2121435 16122077 := bstep (se 3 (by rfl) ⟨3022889, by rfl⟩ : syracuseStep 16122077 = 6045779) B6045779
theorem B10748051 : Blo 2121435 10748051 := bstep (se 1 (by rfl) ⟨8061038, by rfl⟩ : syracuseStep 10748051 = 16122077) B16122077
theorem B7165367 : Blo 2121435 7165367 := bstep (se 1 (by rfl) ⟨5374025, by rfl⟩ : syracuseStep 7165367 = 10748051) B10748051
theorem B4776911 : Blo 2121435 4776911 := bstep (se 1 (by rfl) ⟨3582683, by rfl⟩ : syracuseStep 4776911 = 7165367) B7165367
theorem B3184607 : Blo 2121435 3184607 := bstep (se 1 (by rfl) ⟨2388455, by rfl⟩ : syracuseStep 3184607 = 4776911) B4776911
theorem B2123071 : Blo 2121435 2123071 := bstep (se 1 (by rfl) ⟨1592303, by rfl⟩ : syracuseStep 2123071 = 3184607) B3184607
theorem B3184613 : Blo 2121435 3184613 := bbase (se 4 (by rfl) ⟨298557, by rfl⟩ : syracuseStep 3184613 = 597115) (by norm_num)
theorem B2123075 : Blo 2121435 2123075 := bstep (se 1 (by rfl) ⟨1592306, by rfl⟩ : syracuseStep 2123075 = 3184613) B3184613
theorem B9192437 : Blo 2121435 9192437 := bbase (se 5 (by rfl) ⟨430895, by rfl⟩ : syracuseStep 9192437 = 861791) (by norm_num)
theorem B6128291 : Blo 2121435 6128291 := bstep (se 1 (by rfl) ⟨4596218, by rfl⟩ : syracuseStep 6128291 = 9192437) B9192437
theorem B4085527 : Blo 2121435 4085527 := bstep (se 1 (by rfl) ⟨3064145, by rfl⟩ : syracuseStep 4085527 = 6128291) B6128291
theorem B5447369 : Blo 2121435 5447369 := bstep (se 2 (by rfl) ⟨2042763, by rfl⟩ : syracuseStep 5447369 = 4085527) B4085527
theorem B14526317 : Blo 2121435 14526317 := bstep (se 3 (by rfl) ⟨2723684, by rfl⟩ : syracuseStep 14526317 = 5447369) B5447369
theorem B9684211 : Blo 2121435 9684211 := bstep (se 1 (by rfl) ⟨7263158, by rfl⟩ : syracuseStep 9684211 = 14526317) B14526317
theorem B12912281 : Blo 2121435 12912281 := bstep (se 2 (by rfl) ⟨4842105, by rfl⟩ : syracuseStep 12912281 = 9684211) B9684211
theorem B8608187 : Blo 2121435 8608187 := bstep (se 1 (by rfl) ⟨6456140, by rfl⟩ : syracuseStep 8608187 = 12912281) B12912281
theorem B5738791 : Blo 2121435 5738791 := bstep (se 1 (by rfl) ⟨4304093, by rfl⟩ : syracuseStep 5738791 = 8608187) B8608187
theorem B7651721 : Blo 2121435 7651721 := bstep (se 2 (by rfl) ⟨2869395, by rfl⟩ : syracuseStep 7651721 = 5738791) B5738791
theorem B5101147 : Blo 2121435 5101147 := bstep (se 1 (by rfl) ⟨3825860, by rfl⟩ : syracuseStep 5101147 = 7651721) B7651721
theorem B6801529 : Blo 2121435 6801529 := bstep (se 2 (by rfl) ⟨2550573, by rfl⟩ : syracuseStep 6801529 = 5101147) B5101147
theorem B9068705 : Blo 2121435 9068705 := bstep (se 2 (by rfl) ⟨3400764, by rfl⟩ : syracuseStep 9068705 = 6801529) B6801529
theorem B6045803 : Blo 2121435 6045803 := bstep (se 1 (by rfl) ⟨4534352, by rfl⟩ : syracuseStep 6045803 = 9068705) B9068705
theorem B4030535 : Blo 2121435 4030535 := bstep (se 1 (by rfl) ⟨3022901, by rfl⟩ : syracuseStep 4030535 = 6045803) B6045803
theorem B2687023 : Blo 2121435 2687023 := bstep (se 1 (by rfl) ⟨2015267, by rfl⟩ : syracuseStep 2687023 = 4030535) B4030535
theorem B3582697 : Blo 2121435 3582697 := bstep (se 2 (by rfl) ⟨1343511, by rfl⟩ : syracuseStep 3582697 = 2687023) B2687023
theorem B4776929 : Blo 2121435 4776929 := bstep (se 2 (by rfl) ⟨1791348, by rfl⟩ : syracuseStep 4776929 = 3582697) B3582697
theorem B3184619 : Blo 2121435 3184619 := bstep (se 1 (by rfl) ⟨2388464, by rfl⟩ : syracuseStep 3184619 = 4776929) B4776929
theorem B2123079 : Blo 2121435 2123079 := bstep (se 1 (by rfl) ⟨1592309, by rfl⟩ : syracuseStep 2123079 = 3184619) B3184619
theorem B2388469 : Blo 2121435 2388469 := bbase (se 5 (by rfl) ⟨111959, by rfl⟩ : syracuseStep 2388469 = 223919) (by norm_num)
theorem B3184625 : Blo 2121435 3184625 := bstep (se 2 (by rfl) ⟨1194234, by rfl⟩ : syracuseStep 3184625 = 2388469) B2388469
theorem B2123083 : Blo 2121435 2123083 := bstep (se 1 (by rfl) ⟨1592312, by rfl⟩ : syracuseStep 2123083 = 3184625) B3184625
theorem B2687033 : Blo 2121435 2687033 := bbase (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) (by norm_num)
theorem B7165421 : Blo 2121435 7165421 := bstep (se 3 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 7165421 = 2687033) B2687033
theorem B4776947 : Blo 2121435 4776947 := bstep (se 1 (by rfl) ⟨3582710, by rfl⟩ : syracuseStep 4776947 = 7165421) B7165421
theorem B3184631 : Blo 2121435 3184631 := bstep (se 1 (by rfl) ⟨2388473, by rfl⟩ : syracuseStep 3184631 = 4776947) B4776947
theorem B2123087 : Blo 2121435 2123087 := bstep (se 1 (by rfl) ⟨1592315, by rfl⟩ : syracuseStep 2123087 = 3184631) B3184631
theorem B3184637 : Blo 2121435 3184637 := bbase (se 3 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 3184637 = 1194239) (by norm_num)
theorem B2123091 : Blo 2121435 2123091 := bstep (se 1 (by rfl) ⟨1592318, by rfl⟩ : syracuseStep 2123091 = 3184637) B3184637
theorem B4776965 : Blo 2121435 4776965 := bbase (se 4 (by rfl) ⟨447840, by rfl⟩ : syracuseStep 4776965 = 895681) (by norm_num)
theorem B3184643 : Blo 2121435 3184643 := bstep (se 1 (by rfl) ⟨2388482, by rfl⟩ : syracuseStep 3184643 = 4776965) B4776965
theorem B2123095 : Blo 2121435 2123095 := bstep (se 1 (by rfl) ⟨1592321, by rfl⟩ : syracuseStep 2123095 = 3184643) B3184643
theorem B4030573 : Blo 2121435 4030573 := bbase (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) (by norm_num)
theorem B5374097 : Blo 2121435 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B3582731 : Blo 2121435 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B2388487 : Blo 2121435 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B3184649 : Blo 2121435 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B2123099 : Blo 2121435 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B10748213 : Blo 2121435 10748213 := bbase (se 5 (by rfl) ⟨503822, by rfl⟩ : syracuseStep 10748213 = 1007645) (by norm_num)
theorem B7165475 : Blo 2121435 7165475 := bstep (se 1 (by rfl) ⟨5374106, by rfl⟩ : syracuseStep 7165475 = 10748213) B10748213
theorem B4776983 : Blo 2121435 4776983 := bstep (se 1 (by rfl) ⟨3582737, by rfl⟩ : syracuseStep 4776983 = 7165475) B7165475
theorem B3184655 : Blo 2121435 3184655 := bstep (se 1 (by rfl) ⟨2388491, by rfl⟩ : syracuseStep 3184655 = 4776983) B4776983
theorem B2123103 : Blo 2121435 2123103 := bstep (se 1 (by rfl) ⟨1592327, by rfl⟩ : syracuseStep 2123103 = 3184655) B3184655
theorem B3184661 : Blo 2121435 3184661 := bbase (se 6 (by rfl) ⟨74640, by rfl⟩ : syracuseStep 3184661 = 149281) (by norm_num)
theorem B2123107 : Blo 2121435 2123107 := bstep (se 1 (by rfl) ⟨1592330, by rfl⟩ : syracuseStep 2123107 = 3184661) B3184661
theorem B2723725 : Blo 2121435 2723725 := bbase (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) (by norm_num)
theorem B14526533 : Blo 2121435 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B9684355 : Blo 2121435 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B12912473 : Blo 2121435 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B8608315 : Blo 2121435 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B11477753 : Blo 2121435 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B7651835 : Blo 2121435 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B5101223 : Blo 2121435 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B13603261 : Blo 2121435 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B18137681 : Blo 2121435 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B12091787 : Blo 2121435 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B8061191 : Blo 2121435 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B5374127 : Blo 2121435 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B3582751 : Blo 2121435 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B4777001 : Blo 2121435 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B3184667 : Blo 2121435 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B2123111 : Blo 2121435 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B2388505 : Blo 2121435 2388505 := bbase (se 2 (by rfl) ⟨895689, by rfl⟩ : syracuseStep 2388505 = 1791379) (by norm_num)
theorem B3184673 : Blo 2121435 3184673 := bstep (se 2 (by rfl) ⟨1194252, by rfl⟩ : syracuseStep 3184673 = 2388505) B2388505
theorem B2123115 : Blo 2121435 2123115 := bstep (se 1 (by rfl) ⟨1592336, by rfl⟩ : syracuseStep 2123115 = 3184673) B3184673
theorem B8061221 : Blo 2121435 8061221 := bbase (se 4 (by rfl) ⟨755739, by rfl⟩ : syracuseStep 8061221 = 1511479) (by norm_num)
theorem B5374147 : Blo 2121435 5374147 := bstep (se 1 (by rfl) ⟨4030610, by rfl⟩ : syracuseStep 5374147 = 8061221) B8061221
theorem B7165529 : Blo 2121435 7165529 := bstep (se 2 (by rfl) ⟨2687073, by rfl⟩ : syracuseStep 7165529 = 5374147) B5374147
theorem B4777019 : Blo 2121435 4777019 := bstep (se 1 (by rfl) ⟨3582764, by rfl⟩ : syracuseStep 4777019 = 7165529) B7165529
theorem B3184679 : Blo 2121435 3184679 := bstep (se 1 (by rfl) ⟨2388509, by rfl⟩ : syracuseStep 3184679 = 4777019) B4777019
theorem B2123119 : Blo 2121435 2123119 := bstep (se 1 (by rfl) ⟨1592339, by rfl⟩ : syracuseStep 2123119 = 3184679) B3184679
theorem B3184685 : Blo 2121435 3184685 := bbase (se 3 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 3184685 = 1194257) (by norm_num)
theorem B2123123 : Blo 2121435 2123123 := bstep (se 1 (by rfl) ⟨1592342, by rfl⟩ : syracuseStep 2123123 = 3184685) B3184685
theorem B4777037 : Blo 2121435 4777037 := bbase (se 3 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 4777037 = 1791389) (by norm_num)
theorem B3184691 : Blo 2121435 3184691 := bstep (se 1 (by rfl) ⟨2388518, by rfl⟩ : syracuseStep 3184691 = 4777037) B4777037
theorem B2123127 : Blo 2121435 2123127 := bstep (se 1 (by rfl) ⟨1592345, by rfl⟩ : syracuseStep 2123127 = 3184691) B3184691
theorem B2687089 : Blo 2121435 2687089 := bbase (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) (by norm_num)
theorem B3582785 : Blo 2121435 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B2388523 : Blo 2121435 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B3184697 : Blo 2121435 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B2123131 : Blo 2121435 2123131 := bstep (se 1 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 2123131 = 3184697) B3184697
theorem B6128453 : Blo 2121435 6128453 := bbase (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) (by norm_num)
theorem B4085635 : Blo 2121435 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B5447513 : Blo 2121435 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B3631675 : Blo 2121435 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B4842233 : Blo 2121435 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B3228155 : Blo 2121435 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B2152103 : Blo 2121435 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B5738941 : Blo 2121435 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B7651921 : Blo 2121435 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B10202561 : Blo 2121435 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B6801707 : Blo 2121435 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B4534471 : Blo 2121435 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B24183845 : Blo 2121435 24183845 := bstep (se 4 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 24183845 = 4534471) B4534471
theorem B16122563 : Blo 2121435 16122563 := bstep (se 1 (by rfl) ⟨12091922, by rfl⟩ : syracuseStep 16122563 = 24183845) B24183845
theorem B10748375 : Blo 2121435 10748375 := bstep (se 1 (by rfl) ⟨8061281, by rfl⟩ : syracuseStep 10748375 = 16122563) B16122563
theorem B7165583 : Blo 2121435 7165583 := bstep (se 1 (by rfl) ⟨5374187, by rfl⟩ : syracuseStep 7165583 = 10748375) B10748375
theorem B4777055 : Blo 2121435 4777055 := bstep (se 1 (by rfl) ⟨3582791, by rfl⟩ : syracuseStep 4777055 = 7165583) B7165583
theorem B3184703 : Blo 2121435 3184703 := bstep (se 1 (by rfl) ⟨2388527, by rfl⟩ : syracuseStep 3184703 = 4777055) B4777055
theorem B2123135 : Blo 2121435 2123135 := bstep (se 1 (by rfl) ⟨1592351, by rfl⟩ : syracuseStep 2123135 = 3184703) B3184703
theorem B3184709 : Blo 2121435 3184709 := bbase (se 4 (by rfl) ⟨298566, by rfl⟩ : syracuseStep 3184709 = 597133) (by norm_num)
theorem B2123139 : Blo 2121435 2123139 := bstep (se 1 (by rfl) ⟨1592354, by rfl⟩ : syracuseStep 2123139 = 3184709) B3184709
theorem B3582805 : Blo 2121435 3582805 := bbase (se 9 (by rfl) ⟨10496, by rfl⟩ : syracuseStep 3582805 = 20993) (by norm_num)
theorem B4777073 : Blo 2121435 4777073 := bstep (se 2 (by rfl) ⟨1791402, by rfl⟩ : syracuseStep 4777073 = 3582805) B3582805
theorem B3184715 : Blo 2121435 3184715 := bstep (se 1 (by rfl) ⟨2388536, by rfl⟩ : syracuseStep 3184715 = 4777073) B4777073
theorem B2123143 : Blo 2121435 2123143 := bstep (se 1 (by rfl) ⟨1592357, by rfl⟩ : syracuseStep 2123143 = 3184715) B3184715
theorem B2388541 : Blo 2121435 2388541 := bbase (se 3 (by rfl) ⟨447851, by rfl⟩ : syracuseStep 2388541 = 895703) (by norm_num)
theorem B3184721 : Blo 2121435 3184721 := bstep (se 2 (by rfl) ⟨1194270, by rfl⟩ : syracuseStep 3184721 = 2388541) B2388541
theorem B2123147 : Blo 2121435 2123147 := bstep (se 1 (by rfl) ⟨1592360, by rfl⟩ : syracuseStep 2123147 = 3184721) B3184721
theorem B7165637 : Blo 2121435 7165637 := bbase (se 4 (by rfl) ⟨671778, by rfl⟩ : syracuseStep 7165637 = 1343557) (by norm_num)
theorem B4777091 : Blo 2121435 4777091 := bstep (se 1 (by rfl) ⟨3582818, by rfl⟩ : syracuseStep 4777091 = 7165637) B7165637
theorem B3184727 : Blo 2121435 3184727 := bstep (se 1 (by rfl) ⟨2388545, by rfl⟩ : syracuseStep 3184727 = 4777091) B4777091
theorem B2123151 : Blo 2121435 2123151 := bstep (se 1 (by rfl) ⟨1592363, by rfl⟩ : syracuseStep 2123151 = 3184727) B3184727
theorem B3184733 : Blo 2121435 3184733 := bbase (se 3 (by rfl) ⟨597137, by rfl⟩ : syracuseStep 3184733 = 1194275) (by norm_num)
theorem B2123155 : Blo 2121435 2123155 := bstep (se 1 (by rfl) ⟨1592366, by rfl⟩ : syracuseStep 2123155 = 3184733) B3184733
theorem B4777109 : Blo 2121435 4777109 := bbase (se 6 (by rfl) ⟨111963, by rfl⟩ : syracuseStep 4777109 = 223927) (by norm_num)
theorem B3184739 : Blo 2121435 3184739 := bstep (se 1 (by rfl) ⟨2388554, by rfl⟩ : syracuseStep 3184739 = 4777109) B4777109
theorem B2123159 : Blo 2121435 2123159 := bstep (se 1 (by rfl) ⟨1592369, by rfl⟩ : syracuseStep 2123159 = 3184739) B3184739
theorem B3023021 : Blo 2121435 3023021 := bbase (se 3 (by rfl) ⟨566816, by rfl⟩ : syracuseStep 3023021 = 1133633) (by norm_num)
theorem B8061389 : Blo 2121435 8061389 := bstep (se 3 (by rfl) ⟨1511510, by rfl⟩ : syracuseStep 8061389 = 3023021) B3023021
theorem B5374259 : Blo 2121435 5374259 := bstep (se 1 (by rfl) ⟨4030694, by rfl⟩ : syracuseStep 5374259 = 8061389) B8061389
theorem B3582839 : Blo 2121435 3582839 := bstep (se 1 (by rfl) ⟨2687129, by rfl⟩ : syracuseStep 3582839 = 5374259) B5374259
theorem B2388559 : Blo 2121435 2388559 := bstep (se 1 (by rfl) ⟨1791419, by rfl⟩ : syracuseStep 2388559 = 3582839) B3582839
theorem B3184745 : Blo 2121435 3184745 := bstep (se 2 (by rfl) ⟨1194279, by rfl⟩ : syracuseStep 3184745 = 2388559) B2388559
theorem B2123163 : Blo 2121435 2123163 := bstep (se 1 (by rfl) ⟨1592372, by rfl⟩ : syracuseStep 2123163 = 3184745) B3184745
theorem B20405429 : Blo 2121435 20405429 := bbase (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) (by norm_num)
theorem B13603619 : Blo 2121435 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B9069079 : Blo 2121435 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B12092105 : Blo 2121435 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B8061403 : Blo 2121435 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B10748537 : Blo 2121435 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B7165691 : Blo 2121435 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B4777127 : Blo 2121435 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B3184751 : Blo 2121435 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B2123167 : Blo 2121435 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B3184757 : Blo 2121435 3184757 := bbase (se 5 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 3184757 = 298571) (by norm_num)
theorem B2123171 : Blo 2121435 2123171 := bstep (se 1 (by rfl) ⟨1592378, by rfl⟩ : syracuseStep 2123171 = 3184757) B3184757
theorem B4030717 : Blo 2121435 4030717 := bbase (se 3 (by rfl) ⟨755759, by rfl⟩ : syracuseStep 4030717 = 1511519) (by norm_num)
theorem B5374289 : Blo 2121435 5374289 := bstep (se 2 (by rfl) ⟨2015358, by rfl⟩ : syracuseStep 5374289 = 4030717) B4030717
theorem B3582859 : Blo 2121435 3582859 := bstep (se 1 (by rfl) ⟨2687144, by rfl⟩ : syracuseStep 3582859 = 5374289) B5374289
theorem B4777145 : Blo 2121435 4777145 := bstep (se 2 (by rfl) ⟨1791429, by rfl⟩ : syracuseStep 4777145 = 3582859) B3582859
theorem B3184763 : Blo 2121435 3184763 := bstep (se 1 (by rfl) ⟨2388572, by rfl⟩ : syracuseStep 3184763 = 4777145) B4777145
theorem B2123175 : Blo 2121435 2123175 := bstep (se 1 (by rfl) ⟨1592381, by rfl⟩ : syracuseStep 2123175 = 3184763) B3184763
theorem B2388577 : Blo 2121435 2388577 := bbase (se 2 (by rfl) ⟨895716, by rfl⟩ : syracuseStep 2388577 = 1791433) (by norm_num)
theorem B3184769 : Blo 2121435 3184769 := bstep (se 2 (by rfl) ⟨1194288, by rfl⟩ : syracuseStep 3184769 = 2388577) B2388577
theorem B2123179 : Blo 2121435 2123179 := bstep (se 1 (by rfl) ⟨1592384, by rfl⟩ : syracuseStep 2123179 = 3184769) B3184769
theorem B5374309 : Blo 2121435 5374309 := bbase (se 4 (by rfl) ⟨503841, by rfl⟩ : syracuseStep 5374309 = 1007683) (by norm_num)
theorem B7165745 : Blo 2121435 7165745 := bstep (se 2 (by rfl) ⟨2687154, by rfl⟩ : syracuseStep 7165745 = 5374309) B5374309
theorem B4777163 : Blo 2121435 4777163 := bstep (se 1 (by rfl) ⟨3582872, by rfl⟩ : syracuseStep 4777163 = 7165745) B7165745
theorem B3184775 : Blo 2121435 3184775 := bstep (se 1 (by rfl) ⟨2388581, by rfl⟩ : syracuseStep 3184775 = 4777163) B4777163
theorem B2123183 : Blo 2121435 2123183 := bstep (se 1 (by rfl) ⟨1592387, by rfl⟩ : syracuseStep 2123183 = 3184775) B3184775
theorem B3184781 : Blo 2121435 3184781 := bbase (se 3 (by rfl) ⟨597146, by rfl⟩ : syracuseStep 3184781 = 1194293) (by norm_num)
theorem B2123187 : Blo 2121435 2123187 := bstep (se 1 (by rfl) ⟨1592390, by rfl⟩ : syracuseStep 2123187 = 3184781) B3184781
theorem B4777181 : Blo 2121435 4777181 := bbase (se 3 (by rfl) ⟨895721, by rfl⟩ : syracuseStep 4777181 = 1791443) (by norm_num)
theorem B3184787 : Blo 2121435 3184787 := bstep (se 1 (by rfl) ⟨2388590, by rfl⟩ : syracuseStep 3184787 = 4777181) B4777181
theorem B2123191 : Blo 2121435 2123191 := bstep (se 1 (by rfl) ⟨1592393, by rfl⟩ : syracuseStep 2123191 = 3184787) B3184787
theorem B3582893 : Blo 2121435 3582893 := bbase (se 3 (by rfl) ⟨671792, by rfl⟩ : syracuseStep 3582893 = 1343585) (by norm_num)
theorem B2388595 : Blo 2121435 2388595 := bstep (se 1 (by rfl) ⟨1791446, by rfl⟩ : syracuseStep 2388595 = 3582893) B3582893
theorem B3184793 : Blo 2121435 3184793 := bstep (se 2 (by rfl) ⟨1194297, by rfl⟩ : syracuseStep 3184793 = 2388595) B2388595
theorem B2123195 : Blo 2121435 2123195 := bstep (se 1 (by rfl) ⟨1592396, by rfl⟩ : syracuseStep 2123195 = 3184793) B3184793
theorem B2723837 : Blo 2121435 2723837 := bbase (se 3 (by rfl) ⟨510719, by rfl⟩ : syracuseStep 2723837 = 1021439) (by norm_num)
theorem B29054261 : Blo 2121435 29054261 := bstep (se 5 (by rfl) ⟨1361918, by rfl⟩ : syracuseStep 29054261 = 2723837) B2723837
theorem B77478029 : Blo 2121435 77478029 := bstep (se 3 (by rfl) ⟨14527130, by rfl⟩ : syracuseStep 77478029 = 29054261) B29054261
theorem B51652019 : Blo 2121435 51652019 := bstep (se 1 (by rfl) ⟨38739014, by rfl⟩ : syracuseStep 51652019 = 77478029) B77478029
theorem B137738717 : Blo 2121435 137738717 := bstep (se 3 (by rfl) ⟨25826009, by rfl⟩ : syracuseStep 137738717 = 51652019) B51652019
theorem B91825811 : Blo 2121435 91825811 := bstep (se 1 (by rfl) ⟨68869358, by rfl⟩ : syracuseStep 91825811 = 137738717) B137738717
theorem B61217207 : Blo 2121435 61217207 := bstep (se 1 (by rfl) ⟨45912905, by rfl⟩ : syracuseStep 61217207 = 91825811) B91825811
theorem B40811471 : Blo 2121435 40811471 := bstep (se 1 (by rfl) ⟨30608603, by rfl⟩ : syracuseStep 40811471 = 61217207) B61217207
theorem B27207647 : Blo 2121435 27207647 := bstep (se 1 (by rfl) ⟨20405735, by rfl⟩ : syracuseStep 27207647 = 40811471) B40811471
theorem B18138431 : Blo 2121435 18138431 := bstep (se 1 (by rfl) ⟨13603823, by rfl⟩ : syracuseStep 18138431 = 27207647) B27207647
theorem B12092287 : Blo 2121435 12092287 := bstep (se 1 (by rfl) ⟨9069215, by rfl⟩ : syracuseStep 12092287 = 18138431) B18138431
theorem B16123049 : Blo 2121435 16123049 := bstep (se 2 (by rfl) ⟨6046143, by rfl⟩ : syracuseStep 16123049 = 12092287) B12092287
theorem B10748699 : Blo 2121435 10748699 := bstep (se 1 (by rfl) ⟨8061524, by rfl⟩ : syracuseStep 10748699 = 16123049) B16123049
theorem B7165799 : Blo 2121435 7165799 := bstep (se 1 (by rfl) ⟨5374349, by rfl⟩ : syracuseStep 7165799 = 10748699) B10748699
theorem B4777199 : Blo 2121435 4777199 := bstep (se 1 (by rfl) ⟨3582899, by rfl⟩ : syracuseStep 4777199 = 7165799) B7165799
theorem B3184799 : Blo 2121435 3184799 := bstep (se 1 (by rfl) ⟨2388599, by rfl⟩ : syracuseStep 3184799 = 4777199) B4777199
theorem B2123199 : Blo 2121435 2123199 := bstep (se 1 (by rfl) ⟨1592399, by rfl⟩ : syracuseStep 2123199 = 3184799) B3184799
theorem B3184805 : Blo 2121435 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B2123203 : Blo 2121435 2123203 := bstep (se 1 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 2123203 = 3184805) B3184805
theorem B2687185 : Blo 2121435 2687185 := bbase (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) (by norm_num)
theorem B3582913 : Blo 2121435 3582913 := bstep (se 2 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 3582913 = 2687185) B2687185
theorem B4777217 : Blo 2121435 4777217 := bstep (se 2 (by rfl) ⟨1791456, by rfl⟩ : syracuseStep 4777217 = 3582913) B3582913
theorem B3184811 : Blo 2121435 3184811 := bstep (se 1 (by rfl) ⟨2388608, by rfl⟩ : syracuseStep 3184811 = 4777217) B4777217
theorem B2123207 : Blo 2121435 2123207 := bstep (se 1 (by rfl) ⟨1592405, by rfl⟩ : syracuseStep 2123207 = 3184811) B3184811
theorem B2388613 : Blo 2121435 2388613 := bbase (se 4 (by rfl) ⟨223932, by rfl⟩ : syracuseStep 2388613 = 447865) (by norm_num)
theorem B3184817 : Blo 2121435 3184817 := bstep (se 2 (by rfl) ⟨1194306, by rfl⟩ : syracuseStep 3184817 = 2388613) B2388613
theorem B2123211 : Blo 2121435 2123211 := bstep (se 1 (by rfl) ⟨1592408, by rfl⟩ : syracuseStep 2123211 = 3184817) B3184817
theorem B2550737 : Blo 2121435 2550737 := bbase (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) (by norm_num)
theorem B6801965 : Blo 2121435 6801965 := bstep (se 3 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 6801965 = 2550737) B2550737
theorem B4534643 : Blo 2121435 4534643 := bstep (se 1 (by rfl) ⟨3400982, by rfl⟩ : syracuseStep 4534643 = 6801965) B6801965
theorem B3023095 : Blo 2121435 3023095 := bstep (se 1 (by rfl) ⟨2267321, by rfl⟩ : syracuseStep 3023095 = 4534643) B4534643
theorem B4030793 : Blo 2121435 4030793 := bstep (se 2 (by rfl) ⟨1511547, by rfl⟩ : syracuseStep 4030793 = 3023095) B3023095
theorem B2687195 : Blo 2121435 2687195 := bstep (se 1 (by rfl) ⟨2015396, by rfl⟩ : syracuseStep 2687195 = 4030793) B4030793
theorem B7165853 : Blo 2121435 7165853 := bstep (se 3 (by rfl) ⟨1343597, by rfl⟩ : syracuseStep 7165853 = 2687195) B2687195
theorem B4777235 : Blo 2121435 4777235 := bstep (se 1 (by rfl) ⟨3582926, by rfl⟩ : syracuseStep 4777235 = 7165853) B7165853
theorem B3184823 : Blo 2121435 3184823 := bstep (se 1 (by rfl) ⟨2388617, by rfl⟩ : syracuseStep 3184823 = 4777235) B4777235
theorem B2123215 : Blo 2121435 2123215 := bstep (se 1 (by rfl) ⟨1592411, by rfl⟩ : syracuseStep 2123215 = 3184823) B3184823
theorem B3184829 : Blo 2121435 3184829 := bbase (se 3 (by rfl) ⟨597155, by rfl⟩ : syracuseStep 3184829 = 1194311) (by norm_num)
theorem B2123219 : Blo 2121435 2123219 := bstep (se 1 (by rfl) ⟨1592414, by rfl⟩ : syracuseStep 2123219 = 3184829) B3184829
theorem B4777253 : Blo 2121435 4777253 := bbase (se 4 (by rfl) ⟨447867, by rfl⟩ : syracuseStep 4777253 = 895735) (by norm_num)
theorem B3184835 : Blo 2121435 3184835 := bstep (se 1 (by rfl) ⟨2388626, by rfl⟩ : syracuseStep 3184835 = 4777253) B4777253
theorem B2123223 : Blo 2121435 2123223 := bstep (se 1 (by rfl) ⟨1592417, by rfl⟩ : syracuseStep 2123223 = 3184835) B3184835
theorem B5374421 : Blo 2121435 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B3582947 : Blo 2121435 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B2388631 : Blo 2121435 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B3184841 : Blo 2121435 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B2123227 : Blo 2121435 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B6894821 : Blo 2121435 6894821 := bbase (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) (by norm_num)
theorem B4596547 : Blo 2121435 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B6128729 : Blo 2121435 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B4085819 : Blo 2121435 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B2723879 : Blo 2121435 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B7263677 : Blo 2121435 7263677 := bstep (se 3 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 7263677 = 2723879) B2723879
theorem B4842451 : Blo 2121435 4842451 := bstep (se 1 (by rfl) ⟨3631838, by rfl⟩ : syracuseStep 4842451 = 7263677) B7263677
theorem B6456601 : Blo 2121435 6456601 := bstep (se 2 (by rfl) ⟨2421225, by rfl⟩ : syracuseStep 6456601 = 4842451) B4842451
theorem B34435205 : Blo 2121435 34435205 := bstep (se 4 (by rfl) ⟨3228300, by rfl⟩ : syracuseStep 34435205 = 6456601) B6456601
theorem B22956803 : Blo 2121435 22956803 := bstep (se 1 (by rfl) ⟨17217602, by rfl⟩ : syracuseStep 22956803 = 34435205) B34435205
theorem B15304535 : Blo 2121435 15304535 := bstep (se 1 (by rfl) ⟨11478401, by rfl⟩ : syracuseStep 15304535 = 22956803) B22956803
theorem B10203023 : Blo 2121435 10203023 := bstep (se 1 (by rfl) ⟨7652267, by rfl⟩ : syracuseStep 10203023 = 15304535) B15304535
theorem B6802015 : Blo 2121435 6802015 := bstep (se 1 (by rfl) ⟨5101511, by rfl⟩ : syracuseStep 6802015 = 10203023) B10203023
theorem B9069353 : Blo 2121435 9069353 := bstep (se 2 (by rfl) ⟨3401007, by rfl⟩ : syracuseStep 9069353 = 6802015) B6802015
theorem B6046235 : Blo 2121435 6046235 := bstep (se 1 (by rfl) ⟨4534676, by rfl⟩ : syracuseStep 6046235 = 9069353) B9069353
theorem B4030823 : Blo 2121435 4030823 := bstep (se 1 (by rfl) ⟨3023117, by rfl⟩ : syracuseStep 4030823 = 6046235) B6046235
theorem B10748861 : Blo 2121435 10748861 := bstep (se 3 (by rfl) ⟨2015411, by rfl⟩ : syracuseStep 10748861 = 4030823) B4030823
theorem B7165907 : Blo 2121435 7165907 := bstep (se 1 (by rfl) ⟨5374430, by rfl⟩ : syracuseStep 7165907 = 10748861) B10748861
theorem B4777271 : Blo 2121435 4777271 := bstep (se 1 (by rfl) ⟨3582953, by rfl⟩ : syracuseStep 4777271 = 7165907) B7165907
theorem B3184847 : Blo 2121435 3184847 := bstep (se 1 (by rfl) ⟨2388635, by rfl⟩ : syracuseStep 3184847 = 4777271) B4777271
theorem B2123231 : Blo 2121435 2123231 := bstep (se 1 (by rfl) ⟨1592423, by rfl⟩ : syracuseStep 2123231 = 3184847) B3184847
theorem B3184853 : Blo 2121435 3184853 := bbase (se 7 (by rfl) ⟨37322, by rfl⟩ : syracuseStep 3184853 = 74645) (by norm_num)
theorem B2123235 : Blo 2121435 2123235 := bstep (se 1 (by rfl) ⟨1592426, by rfl⟩ : syracuseStep 2123235 = 3184853) B3184853
theorem B3401021 : Blo 2121435 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B2267347 : Blo 2121435 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B3023129 : Blo 2121435 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B8061677 : Blo 2121435 8061677 := bstep (se 3 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 8061677 = 3023129) B3023129
theorem B5374451 : Blo 2121435 5374451 := bstep (se 1 (by rfl) ⟨4030838, by rfl⟩ : syracuseStep 5374451 = 8061677) B8061677
theorem B3582967 : Blo 2121435 3582967 := bstep (se 1 (by rfl) ⟨2687225, by rfl⟩ : syracuseStep 3582967 = 5374451) B5374451
theorem B4777289 : Blo 2121435 4777289 := bstep (se 2 (by rfl) ⟨1791483, by rfl⟩ : syracuseStep 4777289 = 3582967) B3582967
theorem B3184859 : Blo 2121435 3184859 := bstep (se 1 (by rfl) ⟨2388644, by rfl⟩ : syracuseStep 3184859 = 4777289) B4777289
theorem B2123239 : Blo 2121435 2123239 := bstep (se 1 (by rfl) ⟨1592429, by rfl⟩ : syracuseStep 2123239 = 3184859) B3184859
theorem B2388649 : Blo 2121435 2388649 := bbase (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) (by norm_num)
theorem B3184865 : Blo 2121435 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B2123243 : Blo 2121435 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B2152217 : Blo 2121435 2152217 := bbase (se 2 (by rfl) ⟨807081, by rfl⟩ : syracuseStep 2152217 = 1614163) (by norm_num)
theorem B5739245 : Blo 2121435 5739245 := bstep (se 3 (by rfl) ⟨1076108, by rfl⟩ : syracuseStep 5739245 = 2152217) B2152217
theorem B3826163 : Blo 2121435 3826163 := bstep (se 1 (by rfl) ⟨2869622, by rfl⟩ : syracuseStep 3826163 = 5739245) B5739245
theorem B2550775 : Blo 2121435 2550775 := bstep (se 1 (by rfl) ⟨1913081, by rfl⟩ : syracuseStep 2550775 = 3826163) B3826163
theorem B3401033 : Blo 2121435 3401033 := bstep (se 2 (by rfl) ⟨1275387, by rfl⟩ : syracuseStep 3401033 = 2550775) B2550775
theorem B9069421 : Blo 2121435 9069421 := bstep (se 3 (by rfl) ⟨1700516, by rfl⟩ : syracuseStep 9069421 = 3401033) B3401033
theorem B12092561 : Blo 2121435 12092561 := bstep (se 2 (by rfl) ⟨4534710, by rfl⟩ : syracuseStep 12092561 = 9069421) B9069421
theorem B8061707 : Blo 2121435 8061707 := bstep (se 1 (by rfl) ⟨6046280, by rfl⟩ : syracuseStep 8061707 = 12092561) B12092561
theorem B5374471 : Blo 2121435 5374471 := bstep (se 1 (by rfl) ⟨4030853, by rfl⟩ : syracuseStep 5374471 = 8061707) B8061707
theorem B7165961 : Blo 2121435 7165961 := bstep (se 2 (by rfl) ⟨2687235, by rfl⟩ : syracuseStep 7165961 = 5374471) B5374471
theorem B4777307 : Blo 2121435 4777307 := bstep (se 1 (by rfl) ⟨3582980, by rfl⟩ : syracuseStep 4777307 = 7165961) B7165961
theorem B3184871 : Blo 2121435 3184871 := bstep (se 1 (by rfl) ⟨2388653, by rfl⟩ : syracuseStep 3184871 = 4777307) B4777307
theorem B2123247 : Blo 2121435 2123247 := bstep (se 1 (by rfl) ⟨1592435, by rfl⟩ : syracuseStep 2123247 = 3184871) B3184871
theorem B3184877 : Blo 2121435 3184877 := bbase (se 3 (by rfl) ⟨597164, by rfl⟩ : syracuseStep 3184877 = 1194329) (by norm_num)
theorem B2123251 : Blo 2121435 2123251 := bstep (se 1 (by rfl) ⟨1592438, by rfl⟩ : syracuseStep 2123251 = 3184877) B3184877
theorem B4777325 : Blo 2121435 4777325 := bbase (se 3 (by rfl) ⟨895748, by rfl⟩ : syracuseStep 4777325 = 1791497) (by norm_num)
theorem B3184883 : Blo 2121435 3184883 := bstep (se 1 (by rfl) ⟨2388662, by rfl⟩ : syracuseStep 3184883 = 4777325) B4777325
theorem B2123255 : Blo 2121435 2123255 := bstep (se 1 (by rfl) ⟨1592441, by rfl⟩ : syracuseStep 2123255 = 3184883) B3184883
theorem B4030877 : Blo 2121435 4030877 := bbase (se 3 (by rfl) ⟨755789, by rfl⟩ : syracuseStep 4030877 = 1511579) (by norm_num)
theorem B2687251 : Blo 2121435 2687251 := bstep (se 1 (by rfl) ⟨2015438, by rfl⟩ : syracuseStep 2687251 = 4030877) B4030877
theorem B3583001 : Blo 2121435 3583001 := bstep (se 2 (by rfl) ⟨1343625, by rfl⟩ : syracuseStep 3583001 = 2687251) B2687251
theorem B2388667 : Blo 2121435 2388667 := bstep (se 1 (by rfl) ⟨1791500, by rfl⟩ : syracuseStep 2388667 = 3583001) B3583001
theorem B3184889 : Blo 2121435 3184889 := bstep (se 2 (by rfl) ⟨1194333, by rfl⟩ : syracuseStep 3184889 = 2388667) B2388667
theorem B2123259 : Blo 2121435 2123259 := bstep (se 1 (by rfl) ⟨1592444, by rfl⟩ : syracuseStep 2123259 = 3184889) B3184889
theorem B2620873 : Blo 2121435 2620873 := bbase (se 2 (by rfl) ⟨982827, by rfl⟩ : syracuseStep 2620873 = 1965655) (by norm_num)
theorem B3494497 : Blo 2121435 3494497 := bstep (se 2 (by rfl) ⟨1310436, by rfl⟩ : syracuseStep 3494497 = 2620873) B2620873
theorem B4659329 : Blo 2121435 4659329 := bstep (se 2 (by rfl) ⟨1747248, by rfl⟩ : syracuseStep 4659329 = 3494497) B3494497
theorem B3106219 : Blo 2121435 3106219 := bstep (se 1 (by rfl) ⟨2329664, by rfl⟩ : syracuseStep 3106219 = 4659329) B4659329
theorem B4141625 : Blo 2121435 4141625 := bstep (se 2 (by rfl) ⟨1553109, by rfl⟩ : syracuseStep 4141625 = 3106219) B3106219
theorem B11044333 : Blo 2121435 11044333 := bstep (se 3 (by rfl) ⟨2070812, by rfl⟩ : syracuseStep 11044333 = 4141625) B4141625
theorem B58903109 : Blo 2121435 58903109 := bstep (se 4 (by rfl) ⟨5522166, by rfl⟩ : syracuseStep 58903109 = 11044333) B11044333
theorem B39268739 : Blo 2121435 39268739 := bstep (se 1 (by rfl) ⟨29451554, by rfl⟩ : syracuseStep 39268739 = 58903109) B58903109
theorem B104716637 : Blo 2121435 104716637 := bstep (se 3 (by rfl) ⟨19634369, by rfl⟩ : syracuseStep 104716637 = 39268739) B39268739
theorem B69811091 : Blo 2121435 69811091 := bstep (se 1 (by rfl) ⟨52358318, by rfl⟩ : syracuseStep 69811091 = 104716637) B104716637
theorem B46540727 : Blo 2121435 46540727 := bstep (se 1 (by rfl) ⟨34905545, by rfl⟩ : syracuseStep 46540727 = 69811091) B69811091
theorem B31027151 : Blo 2121435 31027151 := bstep (se 1 (by rfl) ⟨23270363, by rfl⟩ : syracuseStep 31027151 = 46540727) B46540727
theorem B20684767 : Blo 2121435 20684767 := bstep (se 1 (by rfl) ⟨15513575, by rfl⟩ : syracuseStep 20684767 = 31027151) B31027151
theorem B27579689 : Blo 2121435 27579689 := bstep (se 2 (by rfl) ⟨10342383, by rfl⟩ : syracuseStep 27579689 = 20684767) B20684767
theorem B18386459 : Blo 2121435 18386459 := bstep (se 1 (by rfl) ⟨13789844, by rfl⟩ : syracuseStep 18386459 = 27579689) B27579689
theorem B12257639 : Blo 2121435 12257639 := bstep (se 1 (by rfl) ⟨9193229, by rfl⟩ : syracuseStep 12257639 = 18386459) B18386459
theorem B8171759 : Blo 2121435 8171759 := bstep (se 1 (by rfl) ⟨6128819, by rfl⟩ : syracuseStep 8171759 = 12257639) B12257639
theorem B5447839 : Blo 2121435 5447839 := bstep (se 1 (by rfl) ⟨4085879, by rfl⟩ : syracuseStep 5447839 = 8171759) B8171759
theorem B7263785 : Blo 2121435 7263785 := bstep (se 2 (by rfl) ⟨2723919, by rfl⟩ : syracuseStep 7263785 = 5447839) B5447839
theorem B4842523 : Blo 2121435 4842523 := bstep (se 1 (by rfl) ⟨3631892, by rfl⟩ : syracuseStep 4842523 = 7263785) B7263785
theorem B25826789 : Blo 2121435 25826789 := bstep (se 4 (by rfl) ⟨2421261, by rfl⟩ : syracuseStep 25826789 = 4842523) B4842523
theorem B17217859 : Blo 2121435 17217859 := bstep (se 1 (by rfl) ⟨12913394, by rfl⟩ : syracuseStep 17217859 = 25826789) B25826789
theorem B22957145 : Blo 2121435 22957145 := bstep (se 2 (by rfl) ⟨8608929, by rfl⟩ : syracuseStep 22957145 = 17217859) B17217859
theorem B15304763 : Blo 2121435 15304763 := bstep (se 1 (by rfl) ⟨11478572, by rfl⟩ : syracuseStep 15304763 = 22957145) B22957145
theorem B10203175 : Blo 2121435 10203175 := bstep (se 1 (by rfl) ⟨7652381, by rfl⟩ : syracuseStep 10203175 = 15304763) B15304763
theorem B54416933 : Blo 2121435 54416933 := bstep (se 4 (by rfl) ⟨5101587, by rfl⟩ : syracuseStep 54416933 = 10203175) B10203175
theorem B36277955 : Blo 2121435 36277955 := bstep (se 1 (by rfl) ⟨27208466, by rfl⟩ : syracuseStep 36277955 = 54416933) B54416933
theorem B24185303 : Blo 2121435 24185303 := bstep (se 1 (by rfl) ⟨18138977, by rfl⟩ : syracuseStep 24185303 = 36277955) B36277955
theorem B16123535 : Blo 2121435 16123535 := bstep (se 1 (by rfl) ⟨12092651, by rfl⟩ : syracuseStep 16123535 = 24185303) B24185303
theorem B10749023 : Blo 2121435 10749023 := bstep (se 1 (by rfl) ⟨8061767, by rfl⟩ : syracuseStep 10749023 = 16123535) B16123535
theorem B7166015 : Blo 2121435 7166015 := bstep (se 1 (by rfl) ⟨5374511, by rfl⟩ : syracuseStep 7166015 = 10749023) B10749023
theorem B4777343 : Blo 2121435 4777343 := bstep (se 1 (by rfl) ⟨3583007, by rfl⟩ : syracuseStep 4777343 = 7166015) B7166015
theorem B3184895 : Blo 2121435 3184895 := bstep (se 1 (by rfl) ⟨2388671, by rfl⟩ : syracuseStep 3184895 = 4777343) B4777343
theorem B2123263 : Blo 2121435 2123263 := bstep (se 1 (by rfl) ⟨1592447, by rfl⟩ : syracuseStep 2123263 = 3184895) B3184895
theorem B3184901 : Blo 2121435 3184901 := bbase (se 4 (by rfl) ⟨298584, by rfl⟩ : syracuseStep 3184901 = 597169) (by norm_num)
theorem B2123267 : Blo 2121435 2123267 := bstep (se 1 (by rfl) ⟨1592450, by rfl⟩ : syracuseStep 2123267 = 3184901) B3184901
theorem B3583021 : Blo 2121435 3583021 := bbase (se 3 (by rfl) ⟨671816, by rfl⟩ : syracuseStep 3583021 = 1343633) (by norm_num)
theorem B4777361 : Blo 2121435 4777361 := bstep (se 2 (by rfl) ⟨1791510, by rfl⟩ : syracuseStep 4777361 = 3583021) B3583021
theorem B3184907 : Blo 2121435 3184907 := bstep (se 1 (by rfl) ⟨2388680, by rfl⟩ : syracuseStep 3184907 = 4777361) B4777361
theorem B2123271 : Blo 2121435 2123271 := bstep (se 1 (by rfl) ⟨1592453, by rfl⟩ : syracuseStep 2123271 = 3184907) B3184907
theorem B2388685 : Blo 2121435 2388685 := bbase (se 3 (by rfl) ⟨447878, by rfl⟩ : syracuseStep 2388685 = 895757) (by norm_num)
theorem B3184913 : Blo 2121435 3184913 := bstep (se 2 (by rfl) ⟨1194342, by rfl⟩ : syracuseStep 3184913 = 2388685) B2388685
theorem B2123275 : Blo 2121435 2123275 := bstep (se 1 (by rfl) ⟨1592456, by rfl⟩ : syracuseStep 2123275 = 3184913) B3184913
theorem B7166069 : Blo 2121435 7166069 := bbase (se 5 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 7166069 = 671819) (by norm_num)
theorem B4777379 : Blo 2121435 4777379 := bstep (se 1 (by rfl) ⟨3583034, by rfl⟩ : syracuseStep 4777379 = 7166069) B7166069
theorem B3184919 : Blo 2121435 3184919 := bstep (se 1 (by rfl) ⟨2388689, by rfl⟩ : syracuseStep 3184919 = 4777379) B4777379
theorem B2123279 : Blo 2121435 2123279 := bstep (se 1 (by rfl) ⟨1592459, by rfl⟩ : syracuseStep 2123279 = 3184919) B3184919
theorem B3184925 : Blo 2121435 3184925 := bbase (se 3 (by rfl) ⟨597173, by rfl⟩ : syracuseStep 3184925 = 1194347) (by norm_num)
theorem B2123283 : Blo 2121435 2123283 := bstep (se 1 (by rfl) ⟨1592462, by rfl⟩ : syracuseStep 2123283 = 3184925) B3184925
theorem B4777397 : Blo 2121435 4777397 := bbase (se 5 (by rfl) ⟨223940, by rfl⟩ : syracuseStep 4777397 = 447881) (by norm_num)
theorem B3184931 : Blo 2121435 3184931 := bstep (se 1 (by rfl) ⟨2388698, by rfl⟩ : syracuseStep 3184931 = 4777397) B4777397
theorem B2123287 : Blo 2121435 2123287 := bstep (se 1 (by rfl) ⟨1592465, by rfl⟩ : syracuseStep 2123287 = 3184931) B3184931
theorem B4534805 : Blo 2121435 4534805 := bbase (se 6 (by rfl) ⟨106284, by rfl⟩ : syracuseStep 4534805 = 212569) (by norm_num)
theorem B12092813 : Blo 2121435 12092813 := bstep (se 3 (by rfl) ⟨2267402, by rfl⟩ : syracuseStep 12092813 = 4534805) B4534805
theorem B8061875 : Blo 2121435 8061875 := bstep (se 1 (by rfl) ⟨6046406, by rfl⟩ : syracuseStep 8061875 = 12092813) B12092813
theorem B5374583 : Blo 2121435 5374583 := bstep (se 1 (by rfl) ⟨4030937, by rfl⟩ : syracuseStep 5374583 = 8061875) B8061875
theorem B3583055 : Blo 2121435 3583055 := bstep (se 1 (by rfl) ⟨2687291, by rfl⟩ : syracuseStep 3583055 = 5374583) B5374583
theorem B2388703 : Blo 2121435 2388703 := bstep (se 1 (by rfl) ⟨1791527, by rfl⟩ : syracuseStep 2388703 = 3583055) B3583055
theorem B3184937 : Blo 2121435 3184937 := bstep (se 2 (by rfl) ⟨1194351, by rfl⟩ : syracuseStep 3184937 = 2388703) B2388703
theorem B2123291 : Blo 2121435 2123291 := bstep (se 1 (by rfl) ⟨1592468, by rfl⟩ : syracuseStep 2123291 = 3184937) B3184937
theorem B4534813 : Blo 2121435 4534813 := bbase (se 3 (by rfl) ⟨850277, by rfl⟩ : syracuseStep 4534813 = 1700555) (by norm_num)
theorem B6046417 : Blo 2121435 6046417 := bstep (se 2 (by rfl) ⟨2267406, by rfl⟩ : syracuseStep 6046417 = 4534813) B4534813
theorem B8061889 : Blo 2121435 8061889 := bstep (se 2 (by rfl) ⟨3023208, by rfl⟩ : syracuseStep 8061889 = 6046417) B6046417
theorem B10749185 : Blo 2121435 10749185 := bstep (se 2 (by rfl) ⟨4030944, by rfl⟩ : syracuseStep 10749185 = 8061889) B8061889
theorem B7166123 : Blo 2121435 7166123 := bstep (se 1 (by rfl) ⟨5374592, by rfl⟩ : syracuseStep 7166123 = 10749185) B10749185
theorem B4777415 : Blo 2121435 4777415 := bstep (se 1 (by rfl) ⟨3583061, by rfl⟩ : syracuseStep 4777415 = 7166123) B7166123
theorem B3184943 : Blo 2121435 3184943 := bstep (se 1 (by rfl) ⟨2388707, by rfl⟩ : syracuseStep 3184943 = 4777415) B4777415
theorem B2123295 : Blo 2121435 2123295 := bstep (se 1 (by rfl) ⟨1592471, by rfl⟩ : syracuseStep 2123295 = 3184943) B3184943
theorem B3184949 : Blo 2121435 3184949 := bbase (se 5 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 3184949 = 298589) (by norm_num)
theorem B2123299 : Blo 2121435 2123299 := bstep (se 1 (by rfl) ⟨1592474, by rfl⟩ : syracuseStep 2123299 = 3184949) B3184949
theorem B5374613 : Blo 2121435 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B3583075 : Blo 2121435 3583075 := bstep (se 1 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 3583075 = 5374613) B5374613
theorem B4777433 : Blo 2121435 4777433 := bstep (se 2 (by rfl) ⟨1791537, by rfl⟩ : syracuseStep 4777433 = 3583075) B3583075
theorem B3184955 : Blo 2121435 3184955 := bstep (se 1 (by rfl) ⟨2388716, by rfl⟩ : syracuseStep 3184955 = 4777433) B4777433
theorem B2123303 : Blo 2121435 2123303 := bstep (se 1 (by rfl) ⟨1592477, by rfl⟩ : syracuseStep 2123303 = 3184955) B3184955
theorem B2388721 : Blo 2121435 2388721 := bbase (se 2 (by rfl) ⟨895770, by rfl⟩ : syracuseStep 2388721 = 1791541) (by norm_num)
theorem B3184961 : Blo 2121435 3184961 := bstep (se 2 (by rfl) ⟨1194360, by rfl⟩ : syracuseStep 3184961 = 2388721) B2388721
theorem B2123307 : Blo 2121435 2123307 := bstep (se 1 (by rfl) ⟨1592480, by rfl⟩ : syracuseStep 2123307 = 3184961) B3184961
theorem B2908861 : Blo 2121435 2908861 := bbase (se 3 (by rfl) ⟨545411, by rfl⟩ : syracuseStep 2908861 = 1090823) (by norm_num)
theorem B15513925 : Blo 2121435 15513925 := bstep (se 4 (by rfl) ⟨1454430, by rfl⟩ : syracuseStep 15513925 = 2908861) B2908861
theorem B20685233 : Blo 2121435 20685233 := bstep (se 2 (by rfl) ⟨7756962, by rfl⟩ : syracuseStep 20685233 = 15513925) B15513925
theorem B55160621 : Blo 2121435 55160621 := bstep (se 3 (by rfl) ⟨10342616, by rfl⟩ : syracuseStep 55160621 = 20685233) B20685233
theorem B36773747 : Blo 2121435 36773747 := bstep (se 1 (by rfl) ⟨27580310, by rfl⟩ : syracuseStep 36773747 = 55160621) B55160621
theorem B24515831 : Blo 2121435 24515831 := bstep (se 1 (by rfl) ⟨18386873, by rfl⟩ : syracuseStep 24515831 = 36773747) B36773747
theorem B16343887 : Blo 2121435 16343887 := bstep (se 1 (by rfl) ⟨12257915, by rfl⟩ : syracuseStep 16343887 = 24515831) B24515831
theorem B21791849 : Blo 2121435 21791849 := bstep (se 2 (by rfl) ⟨8171943, by rfl⟩ : syracuseStep 21791849 = 16343887) B16343887
theorem B58111597 : Blo 2121435 58111597 := bstep (se 3 (by rfl) ⟨10895924, by rfl⟩ : syracuseStep 58111597 = 21791849) B21791849
theorem B77482129 : Blo 2121435 77482129 := bstep (se 2 (by rfl) ⟨29055798, by rfl⟩ : syracuseStep 77482129 = 58111597) B58111597
theorem B103309505 : Blo 2121435 103309505 := bstep (se 2 (by rfl) ⟨38741064, by rfl⟩ : syracuseStep 103309505 = 77482129) B77482129
theorem B68873003 : Blo 2121435 68873003 := bstep (se 1 (by rfl) ⟨51654752, by rfl⟩ : syracuseStep 68873003 = 103309505) B103309505
theorem B45915335 : Blo 2121435 45915335 := bstep (se 1 (by rfl) ⟨34436501, by rfl⟩ : syracuseStep 45915335 = 68873003) B68873003
theorem B30610223 : Blo 2121435 30610223 := bstep (se 1 (by rfl) ⟨22957667, by rfl⟩ : syracuseStep 30610223 = 45915335) B45915335
theorem B20406815 : Blo 2121435 20406815 := bstep (se 1 (by rfl) ⟨15305111, by rfl⟩ : syracuseStep 20406815 = 30610223) B30610223
theorem B13604543 : Blo 2121435 13604543 := bstep (se 1 (by rfl) ⟨10203407, by rfl⟩ : syracuseStep 13604543 = 20406815) B20406815
theorem B9069695 : Blo 2121435 9069695 := bstep (se 1 (by rfl) ⟨6802271, by rfl⟩ : syracuseStep 9069695 = 13604543) B13604543
theorem B6046463 : Blo 2121435 6046463 := bstep (se 1 (by rfl) ⟨4534847, by rfl⟩ : syracuseStep 6046463 = 9069695) B9069695
theorem B4030975 : Blo 2121435 4030975 := bstep (se 1 (by rfl) ⟨3023231, by rfl⟩ : syracuseStep 4030975 = 6046463) B6046463
theorem B5374633 : Blo 2121435 5374633 := bstep (se 2 (by rfl) ⟨2015487, by rfl⟩ : syracuseStep 5374633 = 4030975) B4030975
theorem B7166177 : Blo 2121435 7166177 := bstep (se 2 (by rfl) ⟨2687316, by rfl⟩ : syracuseStep 7166177 = 5374633) B5374633
theorem B4777451 : Blo 2121435 4777451 := bstep (se 1 (by rfl) ⟨3583088, by rfl⟩ : syracuseStep 4777451 = 7166177) B7166177
theorem B3184967 : Blo 2121435 3184967 := bstep (se 1 (by rfl) ⟨2388725, by rfl⟩ : syracuseStep 3184967 = 4777451) B4777451
theorem B2123311 : Blo 2121435 2123311 := bstep (se 1 (by rfl) ⟨1592483, by rfl⟩ : syracuseStep 2123311 = 3184967) B3184967
theorem B3184973 : Blo 2121435 3184973 := bbase (se 3 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 3184973 = 1194365) (by norm_num)
theorem B2123315 : Blo 2121435 2123315 := bstep (se 1 (by rfl) ⟨1592486, by rfl⟩ : syracuseStep 2123315 = 3184973) B3184973
theorem B4777469 : Blo 2121435 4777469 := bbase (se 3 (by rfl) ⟨895775, by rfl⟩ : syracuseStep 4777469 = 1791551) (by norm_num)
theorem B3184979 : Blo 2121435 3184979 := bstep (se 1 (by rfl) ⟨2388734, by rfl⟩ : syracuseStep 3184979 = 4777469) B4777469
theorem B2123319 : Blo 2121435 2123319 := bstep (se 1 (by rfl) ⟨1592489, by rfl⟩ : syracuseStep 2123319 = 3184979) B3184979
theorem B3583109 : Blo 2121435 3583109 := bbase (se 4 (by rfl) ⟨335916, by rfl⟩ : syracuseStep 3583109 = 671833) (by norm_num)
theorem B2388739 : Blo 2121435 2388739 := bstep (se 1 (by rfl) ⟨1791554, by rfl⟩ : syracuseStep 2388739 = 3583109) B3583109
theorem B3184985 : Blo 2121435 3184985 := bstep (se 2 (by rfl) ⟨1194369, by rfl⟩ : syracuseStep 3184985 = 2388739) B2388739
theorem B2123323 : Blo 2121435 2123323 := bstep (se 1 (by rfl) ⟨1592492, by rfl⟩ : syracuseStep 2123323 = 3184985) B3184985
theorem B16124021 : Blo 2121435 16124021 := bbase (se 5 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 16124021 = 1511627) (by norm_num)
theorem B10749347 : Blo 2121435 10749347 := bstep (se 1 (by rfl) ⟨8062010, by rfl⟩ : syracuseStep 10749347 = 16124021) B16124021
theorem B7166231 : Blo 2121435 7166231 := bstep (se 1 (by rfl) ⟨5374673, by rfl⟩ : syracuseStep 7166231 = 10749347) B10749347
theorem B4777487 : Blo 2121435 4777487 := bstep (se 1 (by rfl) ⟨3583115, by rfl⟩ : syracuseStep 4777487 = 7166231) B7166231
theorem B3184991 : Blo 2121435 3184991 := bstep (se 1 (by rfl) ⟨2388743, by rfl⟩ : syracuseStep 3184991 = 4777487) B4777487
theorem B2123327 : Blo 2121435 2123327 := bstep (se 1 (by rfl) ⟨1592495, by rfl⟩ : syracuseStep 2123327 = 3184991) B3184991
theorem B3184997 : Blo 2121435 3184997 := bbase (se 4 (by rfl) ⟨298593, by rfl⟩ : syracuseStep 3184997 = 597187) (by norm_num)
theorem B2123331 : Blo 2121435 2123331 := bstep (se 1 (by rfl) ⟨1592498, by rfl⟩ : syracuseStep 2123331 = 3184997) B3184997
theorem B4031021 : Blo 2121435 4031021 := bbase (se 3 (by rfl) ⟨755816, by rfl⟩ : syracuseStep 4031021 = 1511633) (by norm_num)
theorem B2687347 : Blo 2121435 2687347 := bstep (se 1 (by rfl) ⟨2015510, by rfl⟩ : syracuseStep 2687347 = 4031021) B4031021
theorem B3583129 : Blo 2121435 3583129 := bstep (se 2 (by rfl) ⟨1343673, by rfl⟩ : syracuseStep 3583129 = 2687347) B2687347
theorem B4777505 : Blo 2121435 4777505 := bstep (se 2 (by rfl) ⟨1791564, by rfl⟩ : syracuseStep 4777505 = 3583129) B3583129
theorem B3185003 : Blo 2121435 3185003 := bstep (se 1 (by rfl) ⟨2388752, by rfl⟩ : syracuseStep 3185003 = 4777505) B4777505
theorem B2123335 : Blo 2121435 2123335 := bstep (se 1 (by rfl) ⟨1592501, by rfl⟩ : syracuseStep 2123335 = 3185003) B3185003
theorem B2388757 : Blo 2121435 2388757 := bbase (se 6 (by rfl) ⟨55986, by rfl⟩ : syracuseStep 2388757 = 111973) (by norm_num)
theorem B3185009 : Blo 2121435 3185009 := bstep (se 2 (by rfl) ⟨1194378, by rfl⟩ : syracuseStep 3185009 = 2388757) B2388757
theorem B2123339 : Blo 2121435 2123339 := bstep (se 1 (by rfl) ⟨1592504, by rfl⟩ : syracuseStep 2123339 = 3185009) B3185009
theorem B2687357 : Blo 2121435 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B7166285 : Blo 2121435 7166285 := bstep (se 3 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 7166285 = 2687357) B2687357
theorem B4777523 : Blo 2121435 4777523 := bstep (se 1 (by rfl) ⟨3583142, by rfl⟩ : syracuseStep 4777523 = 7166285) B7166285
theorem B3185015 : Blo 2121435 3185015 := bstep (se 1 (by rfl) ⟨2388761, by rfl⟩ : syracuseStep 3185015 = 4777523) B4777523
theorem B2123343 : Blo 2121435 2123343 := bstep (se 1 (by rfl) ⟨1592507, by rfl⟩ : syracuseStep 2123343 = 3185015) B3185015
theorem B3185021 : Blo 2121435 3185021 := bbase (se 3 (by rfl) ⟨597191, by rfl⟩ : syracuseStep 3185021 = 1194383) (by norm_num)
theorem B2123347 : Blo 2121435 2123347 := bstep (se 1 (by rfl) ⟨1592510, by rfl⟩ : syracuseStep 2123347 = 3185021) B3185021
theorem B4777541 : Blo 2121435 4777541 := bbase (se 4 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 4777541 = 895789) (by norm_num)
theorem B3185027 : Blo 2121435 3185027 := bstep (se 1 (by rfl) ⟨2388770, by rfl⟩ : syracuseStep 3185027 = 4777541) B4777541
theorem B2123351 : Blo 2121435 2123351 := bstep (se 1 (by rfl) ⟨1592513, by rfl⟩ : syracuseStep 2123351 = 3185027) B3185027
theorem B3632053 : Blo 2121435 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B4842737 : Blo 2121435 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3228491 : Blo 2121435 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B2152327 : Blo 2121435 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B2869769 : Blo 2121435 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B7652717 : Blo 2121435 7652717 := bstep (se 3 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 7652717 = 2869769) B2869769
theorem B5101811 : Blo 2121435 5101811 := bstep (se 1 (by rfl) ⟨3826358, by rfl⟩ : syracuseStep 5101811 = 7652717) B7652717
theorem B3401207 : Blo 2121435 3401207 := bstep (se 1 (by rfl) ⟨2550905, by rfl⟩ : syracuseStep 3401207 = 5101811) B5101811
theorem B2267471 : Blo 2121435 2267471 := bstep (se 1 (by rfl) ⟨1700603, by rfl⟩ : syracuseStep 2267471 = 3401207) B3401207
theorem B6046589 : Blo 2121435 6046589 := bstep (se 3 (by rfl) ⟨1133735, by rfl⟩ : syracuseStep 6046589 = 2267471) B2267471
theorem B4031059 : Blo 2121435 4031059 := bstep (se 1 (by rfl) ⟨3023294, by rfl⟩ : syracuseStep 4031059 = 6046589) B6046589
theorem B5374745 : Blo 2121435 5374745 := bstep (se 2 (by rfl) ⟨2015529, by rfl⟩ : syracuseStep 5374745 = 4031059) B4031059
theorem B3583163 : Blo 2121435 3583163 := bstep (se 1 (by rfl) ⟨2687372, by rfl⟩ : syracuseStep 3583163 = 5374745) B5374745
theorem B2388775 : Blo 2121435 2388775 := bstep (se 1 (by rfl) ⟨1791581, by rfl⟩ : syracuseStep 2388775 = 3583163) B3583163
theorem B3185033 : Blo 2121435 3185033 := bstep (se 2 (by rfl) ⟨1194387, by rfl⟩ : syracuseStep 3185033 = 2388775) B2388775
theorem B2123355 : Blo 2121435 2123355 := bstep (se 1 (by rfl) ⟨1592516, by rfl⟩ : syracuseStep 2123355 = 3185033) B3185033
theorem B10749509 : Blo 2121435 10749509 := bbase (se 4 (by rfl) ⟨1007766, by rfl⟩ : syracuseStep 10749509 = 2015533) (by norm_num)
theorem B7166339 : Blo 2121435 7166339 := bstep (se 1 (by rfl) ⟨5374754, by rfl⟩ : syracuseStep 7166339 = 10749509) B10749509
theorem B4777559 : Blo 2121435 4777559 := bstep (se 1 (by rfl) ⟨3583169, by rfl⟩ : syracuseStep 4777559 = 7166339) B7166339
theorem B3185039 : Blo 2121435 3185039 := bstep (se 1 (by rfl) ⟨2388779, by rfl⟩ : syracuseStep 3185039 = 4777559) B4777559
theorem B2123359 : Blo 2121435 2123359 := bstep (se 1 (by rfl) ⟨1592519, by rfl⟩ : syracuseStep 2123359 = 3185039) B3185039
theorem B3185045 : Blo 2121435 3185045 := bbase (se 6 (by rfl) ⟨74649, by rfl⟩ : syracuseStep 3185045 = 149299) (by norm_num)
theorem B2123363 : Blo 2121435 2123363 := bstep (se 1 (by rfl) ⟨1592522, by rfl⟩ : syracuseStep 2123363 = 3185045) B3185045
theorem B4304677 : Blo 2121435 4304677 := bbase (se 4 (by rfl) ⟨403563, by rfl⟩ : syracuseStep 4304677 = 807127) (by norm_num)
theorem B5739569 : Blo 2121435 5739569 := bstep (se 2 (by rfl) ⟨2152338, by rfl⟩ : syracuseStep 5739569 = 4304677) B4304677
theorem B3826379 : Blo 2121435 3826379 := bstep (se 1 (by rfl) ⟨2869784, by rfl⟩ : syracuseStep 3826379 = 5739569) B5739569
theorem B10203677 : Blo 2121435 10203677 := bstep (se 3 (by rfl) ⟨1913189, by rfl⟩ : syracuseStep 10203677 = 3826379) B3826379
theorem B6802451 : Blo 2121435 6802451 := bstep (se 1 (by rfl) ⟨5101838, by rfl⟩ : syracuseStep 6802451 = 10203677) B10203677
theorem B4534967 : Blo 2121435 4534967 := bstep (se 1 (by rfl) ⟨3401225, by rfl⟩ : syracuseStep 4534967 = 6802451) B6802451
theorem B12093245 : Blo 2121435 12093245 := bstep (se 3 (by rfl) ⟨2267483, by rfl⟩ : syracuseStep 12093245 = 4534967) B4534967
theorem B8062163 : Blo 2121435 8062163 := bstep (se 1 (by rfl) ⟨6046622, by rfl⟩ : syracuseStep 8062163 = 12093245) B12093245
theorem B5374775 : Blo 2121435 5374775 := bstep (se 1 (by rfl) ⟨4031081, by rfl⟩ : syracuseStep 5374775 = 8062163) B8062163
theorem B3583183 : Blo 2121435 3583183 := bstep (se 1 (by rfl) ⟨2687387, by rfl⟩ : syracuseStep 3583183 = 5374775) B5374775
theorem B4777577 : Blo 2121435 4777577 := bstep (se 2 (by rfl) ⟨1791591, by rfl⟩ : syracuseStep 4777577 = 3583183) B3583183
theorem B3185051 : Blo 2121435 3185051 := bstep (se 1 (by rfl) ⟨2388788, by rfl⟩ : syracuseStep 3185051 = 4777577) B4777577
theorem B2123367 : Blo 2121435 2123367 := bstep (se 1 (by rfl) ⟨1592525, by rfl⟩ : syracuseStep 2123367 = 3185051) B3185051
theorem B2388793 : Blo 2121435 2388793 := bbase (se 2 (by rfl) ⟨895797, by rfl⟩ : syracuseStep 2388793 = 1791595) (by norm_num)
theorem B3185057 : Blo 2121435 3185057 := bstep (se 2 (by rfl) ⟨1194396, by rfl⟩ : syracuseStep 3185057 = 2388793) B2388793
theorem B2123371 : Blo 2121435 2123371 := bstep (se 1 (by rfl) ⟨1592528, by rfl⟩ : syracuseStep 2123371 = 3185057) B3185057
theorem B6046645 : Blo 2121435 6046645 := bbase (se 5 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 6046645 = 566873) (by norm_num)
theorem B8062193 : Blo 2121435 8062193 := bstep (se 2 (by rfl) ⟨3023322, by rfl⟩ : syracuseStep 8062193 = 6046645) B6046645
theorem B5374795 : Blo 2121435 5374795 := bstep (se 1 (by rfl) ⟨4031096, by rfl⟩ : syracuseStep 5374795 = 8062193) B8062193
theorem B7166393 : Blo 2121435 7166393 := bstep (se 2 (by rfl) ⟨2687397, by rfl⟩ : syracuseStep 7166393 = 5374795) B5374795
theorem B4777595 : Blo 2121435 4777595 := bstep (se 1 (by rfl) ⟨3583196, by rfl⟩ : syracuseStep 4777595 = 7166393) B7166393
theorem B3185063 : Blo 2121435 3185063 := bstep (se 1 (by rfl) ⟨2388797, by rfl⟩ : syracuseStep 3185063 = 4777595) B4777595
theorem B2123375 : Blo 2121435 2123375 := bstep (se 1 (by rfl) ⟨1592531, by rfl⟩ : syracuseStep 2123375 = 3185063) B3185063
theorem B3185069 : Blo 2121435 3185069 := bbase (se 3 (by rfl) ⟨597200, by rfl⟩ : syracuseStep 3185069 = 1194401) (by norm_num)
theorem B2123379 : Blo 2121435 2123379 := bstep (se 1 (by rfl) ⟨1592534, by rfl⟩ : syracuseStep 2123379 = 3185069) B3185069
theorem B4777613 : Blo 2121435 4777613 := bbase (se 3 (by rfl) ⟨895802, by rfl⟩ : syracuseStep 4777613 = 1791605) (by norm_num)
theorem B3185075 : Blo 2121435 3185075 := bstep (se 1 (by rfl) ⟨2388806, by rfl⟩ : syracuseStep 3185075 = 4777613) B4777613
theorem B2123383 : Blo 2121435 2123383 := bstep (se 1 (by rfl) ⟨1592537, by rfl⟩ : syracuseStep 2123383 = 3185075) B3185075
theorem B2687413 : Blo 2121435 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B3583217 : Blo 2121435 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B2388811 : Blo 2121435 2388811 := bstep (se 1 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 2388811 = 3583217) B3583217
theorem B3185081 : Blo 2121435 3185081 := bstep (se 2 (by rfl) ⟨1194405, by rfl⟩ : syracuseStep 3185081 = 2388811) B2388811
theorem B2123387 : Blo 2121435 2123387 := bstep (se 1 (by rfl) ⟨1592540, by rfl⟩ : syracuseStep 2123387 = 3185081) B3185081
theorem B6989413 : Blo 2121435 6989413 := bbase (se 4 (by rfl) ⟨655257, by rfl⟩ : syracuseStep 6989413 = 1310515) (by norm_num)
theorem B9319217 : Blo 2121435 9319217 := bstep (se 2 (by rfl) ⟨3494706, by rfl⟩ : syracuseStep 9319217 = 6989413) B6989413
theorem B24851245 : Blo 2121435 24851245 := bstep (se 3 (by rfl) ⟨4659608, by rfl⟩ : syracuseStep 24851245 = 9319217) B9319217
theorem B33134993 : Blo 2121435 33134993 := bstep (se 2 (by rfl) ⟨12425622, by rfl⟩ : syracuseStep 33134993 = 24851245) B24851245
theorem B22089995 : Blo 2121435 22089995 := bstep (se 1 (by rfl) ⟨16567496, by rfl⟩ : syracuseStep 22089995 = 33134993) B33134993
theorem B14726663 : Blo 2121435 14726663 := bstep (se 1 (by rfl) ⟨11044997, by rfl⟩ : syracuseStep 14726663 = 22089995) B22089995
theorem B9817775 : Blo 2121435 9817775 := bstep (se 1 (by rfl) ⟨7363331, by rfl⟩ : syracuseStep 9817775 = 14726663) B14726663
theorem B6545183 : Blo 2121435 6545183 := bstep (se 1 (by rfl) ⟨4908887, by rfl⟩ : syracuseStep 6545183 = 9817775) B9817775
theorem B17453821 : Blo 2121435 17453821 := bstep (se 3 (by rfl) ⟨3272591, by rfl⟩ : syracuseStep 17453821 = 6545183) B6545183
theorem B23271761 : Blo 2121435 23271761 := bstep (se 2 (by rfl) ⟨8726910, by rfl⟩ : syracuseStep 23271761 = 17453821) B17453821
theorem B15514507 : Blo 2121435 15514507 := bstep (se 1 (by rfl) ⟨11635880, by rfl⟩ : syracuseStep 15514507 = 23271761) B23271761
theorem B82744037 : Blo 2121435 82744037 := bstep (se 4 (by rfl) ⟨7757253, by rfl⟩ : syracuseStep 82744037 = 15514507) B15514507
theorem B55162691 : Blo 2121435 55162691 := bstep (se 1 (by rfl) ⟨41372018, by rfl⟩ : syracuseStep 55162691 = 82744037) B82744037
theorem B36775127 : Blo 2121435 36775127 := bstep (se 1 (by rfl) ⟨27581345, by rfl⟩ : syracuseStep 36775127 = 55162691) B55162691
theorem B24516751 : Blo 2121435 24516751 := bstep (se 1 (by rfl) ⟨18387563, by rfl⟩ : syracuseStep 24516751 = 36775127) B36775127
theorem B32689001 : Blo 2121435 32689001 := bstep (se 2 (by rfl) ⟨12258375, by rfl⟩ : syracuseStep 32689001 = 24516751) B24516751
theorem B21792667 : Blo 2121435 21792667 := bstep (se 1 (by rfl) ⟨16344500, by rfl⟩ : syracuseStep 21792667 = 32689001) B32689001
theorem B29056889 : Blo 2121435 29056889 := bstep (se 2 (by rfl) ⟨10896333, by rfl⟩ : syracuseStep 29056889 = 21792667) B21792667
theorem B19371259 : Blo 2121435 19371259 := bstep (se 1 (by rfl) ⟨14528444, by rfl⟩ : syracuseStep 19371259 = 29056889) B29056889
theorem B25828345 : Blo 2121435 25828345 := bstep (se 2 (by rfl) ⟨9685629, by rfl⟩ : syracuseStep 25828345 = 19371259) B19371259
theorem B34437793 : Blo 2121435 34437793 := bstep (se 2 (by rfl) ⟨12914172, by rfl⟩ : syracuseStep 34437793 = 25828345) B25828345
theorem B45917057 : Blo 2121435 45917057 := bstep (se 2 (by rfl) ⟨17218896, by rfl⟩ : syracuseStep 45917057 = 34437793) B34437793
theorem B30611371 : Blo 2121435 30611371 := bstep (se 1 (by rfl) ⟨22958528, by rfl⟩ : syracuseStep 30611371 = 45917057) B45917057
theorem B40815161 : Blo 2121435 40815161 := bstep (se 2 (by rfl) ⟨15305685, by rfl⟩ : syracuseStep 40815161 = 30611371) B30611371
theorem B27210107 : Blo 2121435 27210107 := bstep (se 1 (by rfl) ⟨20407580, by rfl⟩ : syracuseStep 27210107 = 40815161) B40815161
theorem B18140071 : Blo 2121435 18140071 := bstep (se 1 (by rfl) ⟨13605053, by rfl⟩ : syracuseStep 18140071 = 27210107) B27210107
theorem B24186761 : Blo 2121435 24186761 := bstep (se 2 (by rfl) ⟨9070035, by rfl⟩ : syracuseStep 24186761 = 18140071) B18140071
theorem B16124507 : Blo 2121435 16124507 := bstep (se 1 (by rfl) ⟨12093380, by rfl⟩ : syracuseStep 16124507 = 24186761) B24186761
theorem B10749671 : Blo 2121435 10749671 := bstep (se 1 (by rfl) ⟨8062253, by rfl⟩ : syracuseStep 10749671 = 16124507) B16124507
theorem B7166447 : Blo 2121435 7166447 := bstep (se 1 (by rfl) ⟨5374835, by rfl⟩ : syracuseStep 7166447 = 10749671) B10749671
theorem B4777631 : Blo 2121435 4777631 := bstep (se 1 (by rfl) ⟨3583223, by rfl⟩ : syracuseStep 4777631 = 7166447) B7166447
theorem B3185087 : Blo 2121435 3185087 := bstep (se 1 (by rfl) ⟨2388815, by rfl⟩ : syracuseStep 3185087 = 4777631) B4777631
theorem B2123391 : Blo 2121435 2123391 := bstep (se 1 (by rfl) ⟨1592543, by rfl⟩ : syracuseStep 2123391 = 3185087) B3185087
theorem B3185093 : Blo 2121435 3185093 := bbase (se 4 (by rfl) ⟨298602, by rfl⟩ : syracuseStep 3185093 = 597205) (by norm_num)
theorem B2123395 : Blo 2121435 2123395 := bstep (se 1 (by rfl) ⟨1592546, by rfl⟩ : syracuseStep 2123395 = 3185093) B3185093
theorem B3583237 : Blo 2121435 3583237 := bbase (se 4 (by rfl) ⟨335928, by rfl⟩ : syracuseStep 3583237 = 671857) (by norm_num)
theorem B4777649 : Blo 2121435 4777649 := bstep (se 2 (by rfl) ⟨1791618, by rfl⟩ : syracuseStep 4777649 = 3583237) B3583237
theorem B3185099 : Blo 2121435 3185099 := bstep (se 1 (by rfl) ⟨2388824, by rfl⟩ : syracuseStep 3185099 = 4777649) B4777649
theorem B2123399 : Blo 2121435 2123399 := bstep (se 1 (by rfl) ⟨1592549, by rfl⟩ : syracuseStep 2123399 = 3185099) B3185099
theorem B2388829 : Blo 2121435 2388829 := bbase (se 3 (by rfl) ⟨447905, by rfl⟩ : syracuseStep 2388829 = 895811) (by norm_num)
theorem B3185105 : Blo 2121435 3185105 := bstep (se 2 (by rfl) ⟨1194414, by rfl⟩ : syracuseStep 3185105 = 2388829) B2388829
theorem B2123403 : Blo 2121435 2123403 := bstep (se 1 (by rfl) ⟨1592552, by rfl⟩ : syracuseStep 2123403 = 3185105) B3185105
theorem B7166501 : Blo 2121435 7166501 := bbase (se 4 (by rfl) ⟨671859, by rfl⟩ : syracuseStep 7166501 = 1343719) (by norm_num)
theorem B4777667 : Blo 2121435 4777667 := bstep (se 1 (by rfl) ⟨3583250, by rfl⟩ : syracuseStep 4777667 = 7166501) B7166501
theorem B3185111 : Blo 2121435 3185111 := bstep (se 1 (by rfl) ⟨2388833, by rfl⟩ : syracuseStep 3185111 = 4777667) B4777667
theorem B2123407 : Blo 2121435 2123407 := bstep (se 1 (by rfl) ⟨1592555, by rfl⟩ : syracuseStep 2123407 = 3185111) B3185111
theorem B3185117 : Blo 2121435 3185117 := bbase (se 3 (by rfl) ⟨597209, by rfl⟩ : syracuseStep 3185117 = 1194419) (by norm_num)
theorem B2123411 : Blo 2121435 2123411 := bstep (se 1 (by rfl) ⟨1592558, by rfl⟩ : syracuseStep 2123411 = 3185117) B3185117
theorem B4777685 : Blo 2121435 4777685 := bbase (se 7 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 4777685 = 111977) (by norm_num)
theorem B3185123 : Blo 2121435 3185123 := bstep (se 1 (by rfl) ⟨2388842, by rfl⟩ : syracuseStep 3185123 = 4777685) B4777685
theorem B2123415 : Blo 2121435 2123415 := bstep (se 1 (by rfl) ⟨1592561, by rfl⟩ : syracuseStep 2123415 = 3185123) B3185123
theorem B3401309 : Blo 2121435 3401309 := bbase (se 3 (by rfl) ⟨637745, by rfl⟩ : syracuseStep 3401309 = 1275491) (by norm_num)
theorem B9070157 : Blo 2121435 9070157 := bstep (se 3 (by rfl) ⟨1700654, by rfl⟩ : syracuseStep 9070157 = 3401309) B3401309
theorem B6046771 : Blo 2121435 6046771 := bstep (se 1 (by rfl) ⟨4535078, by rfl⟩ : syracuseStep 6046771 = 9070157) B9070157
theorem B8062361 : Blo 2121435 8062361 := bstep (se 2 (by rfl) ⟨3023385, by rfl⟩ : syracuseStep 8062361 = 6046771) B6046771
theorem B5374907 : Blo 2121435 5374907 := bstep (se 1 (by rfl) ⟨4031180, by rfl⟩ : syracuseStep 5374907 = 8062361) B8062361
theorem B3583271 : Blo 2121435 3583271 := bstep (se 1 (by rfl) ⟨2687453, by rfl⟩ : syracuseStep 3583271 = 5374907) B5374907
theorem B2388847 : Blo 2121435 2388847 := bstep (se 1 (by rfl) ⟨1791635, by rfl⟩ : syracuseStep 2388847 = 3583271) B3583271
theorem B3185129 : Blo 2121435 3185129 := bstep (se 2 (by rfl) ⟨1194423, by rfl⟩ : syracuseStep 3185129 = 2388847) B2388847
theorem B2123419 : Blo 2121435 2123419 := bstep (se 1 (by rfl) ⟨1592564, by rfl⟩ : syracuseStep 2123419 = 3185129) B3185129
theorem B2724125 : Blo 2121435 2724125 := bbase (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) (by norm_num)
theorem B7264333 : Blo 2121435 7264333 := bstep (se 3 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 7264333 = 2724125) B2724125
theorem B9685777 : Blo 2121435 9685777 := bstep (se 2 (by rfl) ⟨3632166, by rfl⟩ : syracuseStep 9685777 = 7264333) B7264333
theorem B12914369 : Blo 2121435 12914369 := bstep (se 2 (by rfl) ⟨4842888, by rfl⟩ : syracuseStep 12914369 = 9685777) B9685777
theorem B8609579 : Blo 2121435 8609579 := bstep (se 1 (by rfl) ⟨6457184, by rfl⟩ : syracuseStep 8609579 = 12914369) B12914369
theorem B5739719 : Blo 2121435 5739719 := bstep (se 1 (by rfl) ⟨4304789, by rfl⟩ : syracuseStep 5739719 = 8609579) B8609579
theorem B15305917 : Blo 2121435 15305917 := bstep (se 3 (by rfl) ⟨2869859, by rfl⟩ : syracuseStep 15305917 = 5739719) B5739719
theorem B20407889 : Blo 2121435 20407889 := bstep (se 2 (by rfl) ⟨7652958, by rfl⟩ : syracuseStep 20407889 = 15305917) B15305917
theorem B13605259 : Blo 2121435 13605259 := bstep (se 1 (by rfl) ⟨10203944, by rfl⟩ : syracuseStep 13605259 = 20407889) B20407889
theorem B18140345 : Blo 2121435 18140345 := bstep (se 2 (by rfl) ⟨6802629, by rfl⟩ : syracuseStep 18140345 = 13605259) B13605259
theorem B12093563 : Blo 2121435 12093563 := bstep (se 1 (by rfl) ⟨9070172, by rfl⟩ : syracuseStep 12093563 = 18140345) B18140345
theorem B8062375 : Blo 2121435 8062375 := bstep (se 1 (by rfl) ⟨6046781, by rfl⟩ : syracuseStep 8062375 = 12093563) B12093563
theorem B10749833 : Blo 2121435 10749833 := bstep (se 2 (by rfl) ⟨4031187, by rfl⟩ : syracuseStep 10749833 = 8062375) B8062375
theorem B7166555 : Blo 2121435 7166555 := bstep (se 1 (by rfl) ⟨5374916, by rfl⟩ : syracuseStep 7166555 = 10749833) B10749833
theorem B4777703 : Blo 2121435 4777703 := bstep (se 1 (by rfl) ⟨3583277, by rfl⟩ : syracuseStep 4777703 = 7166555) B7166555
theorem B3185135 : Blo 2121435 3185135 := bstep (se 1 (by rfl) ⟨2388851, by rfl⟩ : syracuseStep 3185135 = 4777703) B4777703
theorem B2123423 : Blo 2121435 2123423 := bstep (se 1 (by rfl) ⟨1592567, by rfl⟩ : syracuseStep 2123423 = 3185135) B3185135
theorem B3185141 : Blo 2121435 3185141 := bbase (se 5 (by rfl) ⟨149303, by rfl⟩ : syracuseStep 3185141 = 298607) (by norm_num)
theorem B2123427 : Blo 2121435 2123427 := bstep (se 1 (by rfl) ⟨1592570, by rfl⟩ : syracuseStep 2123427 = 3185141) B3185141
theorem B6046805 : Blo 2121435 6046805 := bbase (se 8 (by rfl) ⟨35430, by rfl⟩ : syracuseStep 6046805 = 70861) (by norm_num)
theorem B4031203 : Blo 2121435 4031203 := bstep (se 1 (by rfl) ⟨3023402, by rfl⟩ : syracuseStep 4031203 = 6046805) B6046805
theorem B5374937 : Blo 2121435 5374937 := bstep (se 2 (by rfl) ⟨2015601, by rfl⟩ : syracuseStep 5374937 = 4031203) B4031203
theorem B3583291 : Blo 2121435 3583291 := bstep (se 1 (by rfl) ⟨2687468, by rfl⟩ : syracuseStep 3583291 = 5374937) B5374937
theorem B4777721 : Blo 2121435 4777721 := bstep (se 2 (by rfl) ⟨1791645, by rfl⟩ : syracuseStep 4777721 = 3583291) B3583291
theorem B3185147 : Blo 2121435 3185147 := bstep (se 1 (by rfl) ⟨2388860, by rfl⟩ : syracuseStep 3185147 = 4777721) B4777721
theorem B2123431 : Blo 2121435 2123431 := bstep (se 1 (by rfl) ⟨1592573, by rfl⟩ : syracuseStep 2123431 = 3185147) B3185147
theorem B2388865 : Blo 2121435 2388865 := bbase (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) (by norm_num)
theorem B3185153 : Blo 2121435 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B2123435 : Blo 2121435 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem C0 (j : ℕ) (h1 : 530358 ≤ j) (h2 : j ≤ 530858) : Blo 2121435 (4 * j + 3) := by
  interval_cases j
  · exact B2121435
  · exact B2121439
  · exact B2121443
  · exact B2121447
  · exact B2121451
  · exact B2121455
  · exact B2121459
  · exact B2121463
  · exact B2121467
  · exact B2121471
  · exact B2121475
  · exact B2121479
  · exact B2121483
  · exact B2121487
  · exact B2121491
  · exact B2121495
  · exact B2121499
  · exact B2121503
  · exact B2121507
  · exact B2121511
  · exact B2121515
  · exact B2121519
  · exact B2121523
  · exact B2121527
  · exact B2121531
  · exact B2121535
  · exact B2121539
  · exact B2121543
  · exact B2121547
  · exact B2121551
  · exact B2121555
  · exact B2121559
  · exact B2121563
  · exact B2121567
  · exact B2121571
  · exact B2121575
  · exact B2121579
  · exact B2121583
  · exact B2121587
  · exact B2121591
  · exact B2121595
  · exact B2121599
  · exact B2121603
  · exact B2121607
  · exact B2121611
  · exact B2121615
  · exact B2121619
  · exact B2121623
  · exact B2121627
  · exact B2121631
  · exact B2121635
  · exact B2121639
  · exact B2121643
  · exact B2121647
  · exact B2121651
  · exact B2121655
  · exact B2121659
  · exact B2121663
  · exact B2121667
  · exact B2121671
  · exact B2121675
  · exact B2121679
  · exact B2121683
  · exact B2121687
  · exact B2121691
  · exact B2121695
  · exact B2121699
  · exact B2121703
  · exact B2121707
  · exact B2121711
  · exact B2121715
  · exact B2121719
  · exact B2121723
  · exact B2121727
  · exact B2121731
  · exact B2121735
  · exact B2121739
  · exact B2121743
  · exact B2121747
  · exact B2121751
  · exact B2121755
  · exact B2121759
  · exact B2121763
  · exact B2121767
  · exact B2121771
  · exact B2121775
  · exact B2121779
  · exact B2121783
  · exact B2121787
  · exact B2121791
  · exact B2121795
  · exact B2121799
  · exact B2121803
  · exact B2121807
  · exact B2121811
  · exact B2121815
  · exact B2121819
  · exact B2121823
  · exact B2121827
  · exact B2121831
  · exact B2121835
  · exact B2121839
  · exact B2121843
  · exact B2121847
  · exact B2121851
  · exact B2121855
  · exact B2121859
  · exact B2121863
  · exact B2121867
  · exact B2121871
  · exact B2121875
  · exact B2121879
  · exact B2121883
  · exact B2121887
  · exact B2121891
  · exact B2121895
  · exact B2121899
  · exact B2121903
  · exact B2121907
  · exact B2121911
  · exact B2121915
  · exact B2121919
  · exact B2121923
  · exact B2121927
  · exact B2121931
  · exact B2121935
  · exact B2121939
  · exact B2121943
  · exact B2121947
  · exact B2121951
  · exact B2121955
  · exact B2121959
  · exact B2121963
  · exact B2121967
  · exact B2121971
  · exact B2121975
  · exact B2121979
  · exact B2121983
  · exact B2121987
  · exact B2121991
  · exact B2121995
  · exact B2121999
  · exact B2122003
  · exact B2122007
  · exact B2122011
  · exact B2122015
  · exact B2122019
  · exact B2122023
  · exact B2122027
  · exact B2122031
  · exact B2122035
  · exact B2122039
  · exact B2122043
  · exact B2122047
  · exact B2122051
  · exact B2122055
  · exact B2122059
  · exact B2122063
  · exact B2122067
  · exact B2122071
  · exact B2122075
  · exact B2122079
  · exact B2122083
  · exact B2122087
  · exact B2122091
  · exact B2122095
  · exact B2122099
  · exact B2122103
  · exact B2122107
  · exact B2122111
  · exact B2122115
  · exact B2122119
  · exact B2122123
  · exact B2122127
  · exact B2122131
  · exact B2122135
  · exact B2122139
  · exact B2122143
  · exact B2122147
  · exact B2122151
  · exact B2122155
  · exact B2122159
  · exact B2122163
  · exact B2122167
  · exact B2122171
  · exact B2122175
  · exact B2122179
  · exact B2122183
  · exact B2122187
  · exact B2122191
  · exact B2122195
  · exact B2122199
  · exact B2122203
  · exact B2122207
  · exact B2122211
  · exact B2122215
  · exact B2122219
  · exact B2122223
  · exact B2122227
  · exact B2122231
  · exact B2122235
  · exact B2122239
  · exact B2122243
  · exact B2122247
  · exact B2122251
  · exact B2122255
  · exact B2122259
  · exact B2122263
  · exact B2122267
  · exact B2122271
  · exact B2122275
  · exact B2122279
  · exact B2122283
  · exact B2122287
  · exact B2122291
  · exact B2122295
  · exact B2122299
  · exact B2122303
  · exact B2122307
  · exact B2122311
  · exact B2122315
  · exact B2122319
  · exact B2122323
  · exact B2122327
  · exact B2122331
  · exact B2122335
  · exact B2122339
  · exact B2122343
  · exact B2122347
  · exact B2122351
  · exact B2122355
  · exact B2122359
  · exact B2122363
  · exact B2122367
  · exact B2122371
  · exact B2122375
  · exact B2122379
  · exact B2122383
  · exact B2122387
  · exact B2122391
  · exact B2122395
  · exact B2122399
  · exact B2122403
  · exact B2122407
  · exact B2122411
  · exact B2122415
  · exact B2122419
  · exact B2122423
  · exact B2122427
  · exact B2122431
  · exact B2122435
  · exact B2122439
  · exact B2122443
  · exact B2122447
  · exact B2122451
  · exact B2122455
  · exact B2122459
  · exact B2122463
  · exact B2122467
  · exact B2122471
  · exact B2122475
  · exact B2122479
  · exact B2122483
  · exact B2122487
  · exact B2122491
  · exact B2122495
  · exact B2122499
  · exact B2122503
  · exact B2122507
  · exact B2122511
  · exact B2122515
  · exact B2122519
  · exact B2122523
  · exact B2122527
  · exact B2122531
  · exact B2122535
  · exact B2122539
  · exact B2122543
  · exact B2122547
  · exact B2122551
  · exact B2122555
  · exact B2122559
  · exact B2122563
  · exact B2122567
  · exact B2122571
  · exact B2122575
  · exact B2122579
  · exact B2122583
  · exact B2122587
  · exact B2122591
  · exact B2122595
  · exact B2122599
  · exact B2122603
  · exact B2122607
  · exact B2122611
  · exact B2122615
  · exact B2122619
  · exact B2122623
  · exact B2122627
  · exact B2122631
  · exact B2122635
  · exact B2122639
  · exact B2122643
  · exact B2122647
  · exact B2122651
  · exact B2122655
  · exact B2122659
  · exact B2122663
  · exact B2122667
  · exact B2122671
  · exact B2122675
  · exact B2122679
  · exact B2122683
  · exact B2122687
  · exact B2122691
  · exact B2122695
  · exact B2122699
  · exact B2122703
  · exact B2122707
  · exact B2122711
  · exact B2122715
  · exact B2122719
  · exact B2122723
  · exact B2122727
  · exact B2122731
  · exact B2122735
  · exact B2122739
  · exact B2122743
  · exact B2122747
  · exact B2122751
  · exact B2122755
  · exact B2122759
  · exact B2122763
  · exact B2122767
  · exact B2122771
  · exact B2122775
  · exact B2122779
  · exact B2122783
  · exact B2122787
  · exact B2122791
  · exact B2122795
  · exact B2122799
  · exact B2122803
  · exact B2122807
  · exact B2122811
  · exact B2122815
  · exact B2122819
  · exact B2122823
  · exact B2122827
  · exact B2122831
  · exact B2122835
  · exact B2122839
  · exact B2122843
  · exact B2122847
  · exact B2122851
  · exact B2122855
  · exact B2122859
  · exact B2122863
  · exact B2122867
  · exact B2122871
  · exact B2122875
  · exact B2122879
  · exact B2122883
  · exact B2122887
  · exact B2122891
  · exact B2122895
  · exact B2122899
  · exact B2122903
  · exact B2122907
  · exact B2122911
  · exact B2122915
  · exact B2122919
  · exact B2122923
  · exact B2122927
  · exact B2122931
  · exact B2122935
  · exact B2122939
  · exact B2122943
  · exact B2122947
  · exact B2122951
  · exact B2122955
  · exact B2122959
  · exact B2122963
  · exact B2122967
  · exact B2122971
  · exact B2122975
  · exact B2122979
  · exact B2122983
  · exact B2122987
  · exact B2122991
  · exact B2122995
  · exact B2122999
  · exact B2123003
  · exact B2123007
  · exact B2123011
  · exact B2123015
  · exact B2123019
  · exact B2123023
  · exact B2123027
  · exact B2123031
  · exact B2123035
  · exact B2123039
  · exact B2123043
  · exact B2123047
  · exact B2123051
  · exact B2123055
  · exact B2123059
  · exact B2123063
  · exact B2123067
  · exact B2123071
  · exact B2123075
  · exact B2123079
  · exact B2123083
  · exact B2123087
  · exact B2123091
  · exact B2123095
  · exact B2123099
  · exact B2123103
  · exact B2123107
  · exact B2123111
  · exact B2123115
  · exact B2123119
  · exact B2123123
  · exact B2123127
  · exact B2123131
  · exact B2123135
  · exact B2123139
  · exact B2123143
  · exact B2123147
  · exact B2123151
  · exact B2123155
  · exact B2123159
  · exact B2123163
  · exact B2123167
  · exact B2123171
  · exact B2123175
  · exact B2123179
  · exact B2123183
  · exact B2123187
  · exact B2123191
  · exact B2123195
  · exact B2123199
  · exact B2123203
  · exact B2123207
  · exact B2123211
  · exact B2123215
  · exact B2123219
  · exact B2123223
  · exact B2123227
  · exact B2123231
  · exact B2123235
  · exact B2123239
  · exact B2123243
  · exact B2123247
  · exact B2123251
  · exact B2123255
  · exact B2123259
  · exact B2123263
  · exact B2123267
  · exact B2123271
  · exact B2123275
  · exact B2123279
  · exact B2123283
  · exact B2123287
  · exact B2123291
  · exact B2123295
  · exact B2123299
  · exact B2123303
  · exact B2123307
  · exact B2123311
  · exact B2123315
  · exact B2123319
  · exact B2123323
  · exact B2123327
  · exact B2123331
  · exact B2123335
  · exact B2123339
  · exact B2123343
  · exact B2123347
  · exact B2123351
  · exact B2123355
  · exact B2123359
  · exact B2123363
  · exact B2123367
  · exact B2123371
  · exact B2123375
  · exact B2123379
  · exact B2123383
  · exact B2123387
  · exact B2123391
  · exact B2123395
  · exact B2123399
  · exact B2123403
  · exact B2123407
  · exact B2123411
  · exact B2123415
  · exact B2123419
  · exact B2123423
  · exact B2123427
  · exact B2123431
  · exact B2123435
theorem solution (m : ℕ) (hlo : 2121435 ≤ m) (hhi : m ≤ 2123435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 530358 ≤ j := by omega
    have hj2 : j ≤ 530858 := by omega
    have hb : Blo 2121435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
