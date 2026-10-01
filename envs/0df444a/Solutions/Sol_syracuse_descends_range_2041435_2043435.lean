-- Prove2me | solution 1 for syracuse_descends_range_2041435_2043435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:16.542487+00:00
-- url     : https://prove2.me/submissions/0428d007-049a-4e44-bd3d-967d91087f6f

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

theorem B4904981 : Blo 2041435 4904981 := bbase (se 6 (by rfl) ⟨114960, by rfl⟩ : syracuseStep 4904981 = 229921) (by norm_num)
theorem B3269987 : Blo 2041435 3269987 := bstep (se 1 (by rfl) ⟨2452490, by rfl⟩ : syracuseStep 3269987 = 4904981) B4904981
theorem B2179991 : Blo 2041435 2179991 := bstep (se 1 (by rfl) ⟨1634993, by rfl⟩ : syracuseStep 2179991 = 3269987) B3269987
theorem B5813309 : Blo 2041435 5813309 := bstep (se 3 (by rfl) ⟨1089995, by rfl⟩ : syracuseStep 5813309 = 2179991) B2179991
theorem B3875539 : Blo 2041435 3875539 := bstep (se 1 (by rfl) ⟨2906654, by rfl⟩ : syracuseStep 3875539 = 5813309) B5813309
theorem B5167385 : Blo 2041435 5167385 := bstep (se 2 (by rfl) ⟨1937769, by rfl⟩ : syracuseStep 5167385 = 3875539) B3875539
theorem B3444923 : Blo 2041435 3444923 := bstep (se 1 (by rfl) ⟨2583692, by rfl⟩ : syracuseStep 3444923 = 5167385) B5167385
theorem B2296615 : Blo 2041435 2296615 := bstep (se 1 (by rfl) ⟨1722461, by rfl⟩ : syracuseStep 2296615 = 3444923) B3444923
theorem B3062153 : Blo 2041435 3062153 := bstep (se 2 (by rfl) ⟨1148307, by rfl⟩ : syracuseStep 3062153 = 2296615) B2296615
theorem B2041435 : Blo 2041435 2041435 := bstep (se 1 (by rfl) ⟨1531076, by rfl⟩ : syracuseStep 2041435 = 3062153) B3062153
theorem B10334789 : Blo 2041435 10334789 := bbase (se 4 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 10334789 = 1937773) (by norm_num)
theorem B6889859 : Blo 2041435 6889859 := bstep (se 1 (by rfl) ⟨5167394, by rfl⟩ : syracuseStep 6889859 = 10334789) B10334789
theorem B4593239 : Blo 2041435 4593239 := bstep (se 1 (by rfl) ⟨3444929, by rfl⟩ : syracuseStep 4593239 = 6889859) B6889859
theorem B3062159 : Blo 2041435 3062159 := bstep (se 1 (by rfl) ⟨2296619, by rfl⟩ : syracuseStep 3062159 = 4593239) B4593239
theorem B2041439 : Blo 2041435 2041439 := bstep (se 1 (by rfl) ⟨1531079, by rfl⟩ : syracuseStep 2041439 = 3062159) B3062159
theorem B3062165 : Blo 2041435 3062165 := bbase (se 6 (by rfl) ⟨71769, by rfl⟩ : syracuseStep 3062165 = 143539) (by norm_num)
theorem B2041443 : Blo 2041435 2041443 := bstep (se 1 (by rfl) ⟨1531082, by rfl⟩ : syracuseStep 2041443 = 3062165) B3062165
theorem B3314621 : Blo 2041435 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B8838989 : Blo 2041435 8838989 := bstep (se 3 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 8838989 = 3314621) B3314621
theorem B5892659 : Blo 2041435 5892659 := bstep (se 1 (by rfl) ⟨4419494, by rfl⟩ : syracuseStep 5892659 = 8838989) B8838989
theorem B3928439 : Blo 2041435 3928439 := bstep (se 1 (by rfl) ⟨2946329, by rfl⟩ : syracuseStep 3928439 = 5892659) B5892659
theorem B10475837 : Blo 2041435 10475837 := bstep (se 3 (by rfl) ⟨1964219, by rfl⟩ : syracuseStep 10475837 = 3928439) B3928439
theorem B6983891 : Blo 2041435 6983891 := bstep (se 1 (by rfl) ⟨5237918, by rfl⟩ : syracuseStep 6983891 = 10475837) B10475837
theorem B4655927 : Blo 2041435 4655927 := bstep (se 1 (by rfl) ⟨3491945, by rfl⟩ : syracuseStep 4655927 = 6983891) B6983891
theorem B12415805 : Blo 2041435 12415805 := bstep (se 3 (by rfl) ⟨2327963, by rfl⟩ : syracuseStep 12415805 = 4655927) B4655927
theorem B8277203 : Blo 2041435 8277203 := bstep (se 1 (by rfl) ⟨6207902, by rfl⟩ : syracuseStep 8277203 = 12415805) B12415805
theorem B5518135 : Blo 2041435 5518135 := bstep (se 1 (by rfl) ⟨4138601, by rfl⟩ : syracuseStep 5518135 = 8277203) B8277203
theorem B7357513 : Blo 2041435 7357513 := bstep (se 2 (by rfl) ⟨2759067, by rfl⟩ : syracuseStep 7357513 = 5518135) B5518135
theorem B9810017 : Blo 2041435 9810017 := bstep (se 2 (by rfl) ⟨3678756, by rfl⟩ : syracuseStep 9810017 = 7357513) B7357513
theorem B6540011 : Blo 2041435 6540011 := bstep (se 1 (by rfl) ⟨4905008, by rfl⟩ : syracuseStep 6540011 = 9810017) B9810017
theorem B4360007 : Blo 2041435 4360007 := bstep (se 1 (by rfl) ⟨3270005, by rfl⟩ : syracuseStep 4360007 = 6540011) B6540011
theorem B11626685 : Blo 2041435 11626685 := bstep (se 3 (by rfl) ⟨2180003, by rfl⟩ : syracuseStep 11626685 = 4360007) B4360007
theorem B7751123 : Blo 2041435 7751123 := bstep (se 1 (by rfl) ⟨5813342, by rfl⟩ : syracuseStep 7751123 = 11626685) B11626685
theorem B5167415 : Blo 2041435 5167415 := bstep (se 1 (by rfl) ⟨3875561, by rfl⟩ : syracuseStep 5167415 = 7751123) B7751123
theorem B3444943 : Blo 2041435 3444943 := bstep (se 1 (by rfl) ⟨2583707, by rfl⟩ : syracuseStep 3444943 = 5167415) B5167415
theorem B4593257 : Blo 2041435 4593257 := bstep (se 2 (by rfl) ⟨1722471, by rfl⟩ : syracuseStep 4593257 = 3444943) B3444943
theorem B3062171 : Blo 2041435 3062171 := bstep (se 1 (by rfl) ⟨2296628, by rfl⟩ : syracuseStep 3062171 = 4593257) B4593257
theorem B2041447 : Blo 2041435 2041447 := bstep (se 1 (by rfl) ⟨1531085, by rfl⟩ : syracuseStep 2041447 = 3062171) B3062171
theorem B2296633 : Blo 2041435 2296633 := bbase (se 2 (by rfl) ⟨861237, by rfl⟩ : syracuseStep 2296633 = 1722475) (by norm_num)
theorem B3062177 : Blo 2041435 3062177 := bstep (se 2 (by rfl) ⟨1148316, by rfl⟩ : syracuseStep 3062177 = 2296633) B2296633
theorem B2041451 : Blo 2041435 2041451 := bstep (se 1 (by rfl) ⟨1531088, by rfl⟩ : syracuseStep 2041451 = 3062177) B3062177
theorem B5813365 : Blo 2041435 5813365 := bbase (se 5 (by rfl) ⟨272501, by rfl⟩ : syracuseStep 5813365 = 545003) (by norm_num)
theorem B7751153 : Blo 2041435 7751153 := bstep (se 2 (by rfl) ⟨2906682, by rfl⟩ : syracuseStep 7751153 = 5813365) B5813365
theorem B5167435 : Blo 2041435 5167435 := bstep (se 1 (by rfl) ⟨3875576, by rfl⟩ : syracuseStep 5167435 = 7751153) B7751153
theorem B6889913 : Blo 2041435 6889913 := bstep (se 2 (by rfl) ⟨2583717, by rfl⟩ : syracuseStep 6889913 = 5167435) B5167435
theorem B4593275 : Blo 2041435 4593275 := bstep (se 1 (by rfl) ⟨3444956, by rfl⟩ : syracuseStep 4593275 = 6889913) B6889913
theorem B3062183 : Blo 2041435 3062183 := bstep (se 1 (by rfl) ⟨2296637, by rfl⟩ : syracuseStep 3062183 = 4593275) B4593275
theorem B2041455 : Blo 2041435 2041455 := bstep (se 1 (by rfl) ⟨1531091, by rfl⟩ : syracuseStep 2041455 = 3062183) B3062183
theorem B3062189 : Blo 2041435 3062189 := bbase (se 3 (by rfl) ⟨574160, by rfl⟩ : syracuseStep 3062189 = 1148321) (by norm_num)
theorem B2041459 : Blo 2041435 2041459 := bstep (se 1 (by rfl) ⟨1531094, by rfl⟩ : syracuseStep 2041459 = 3062189) B3062189
theorem B4593293 : Blo 2041435 4593293 := bbase (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) (by norm_num)
theorem B3062195 : Blo 2041435 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B2041463 : Blo 2041435 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B2583733 : Blo 2041435 2583733 := bbase (se 5 (by rfl) ⟨121112, by rfl⟩ : syracuseStep 2583733 = 242225) (by norm_num)
theorem B3444977 : Blo 2041435 3444977 := bstep (se 2 (by rfl) ⟨1291866, by rfl⟩ : syracuseStep 3444977 = 2583733) B2583733
theorem B2296651 : Blo 2041435 2296651 := bstep (se 1 (by rfl) ⟨1722488, by rfl⟩ : syracuseStep 2296651 = 3444977) B3444977
theorem B3062201 : Blo 2041435 3062201 := bstep (se 2 (by rfl) ⟨1148325, by rfl⟩ : syracuseStep 3062201 = 2296651) B2296651
theorem B2041467 : Blo 2041435 2041467 := bstep (se 1 (by rfl) ⟨1531100, by rfl⟩ : syracuseStep 2041467 = 3062201) B3062201
theorem B24831893 : Blo 2041435 24831893 := bbase (se 6 (by rfl) ⟨581997, by rfl⟩ : syracuseStep 24831893 = 1163995) (by norm_num)
theorem B66218381 : Blo 2041435 66218381 := bstep (se 3 (by rfl) ⟨12415946, by rfl⟩ : syracuseStep 66218381 = 24831893) B24831893
theorem B44145587 : Blo 2041435 44145587 := bstep (se 1 (by rfl) ⟨33109190, by rfl⟩ : syracuseStep 44145587 = 66218381) B66218381
theorem B29430391 : Blo 2041435 29430391 := bstep (se 1 (by rfl) ⟨22072793, by rfl⟩ : syracuseStep 29430391 = 44145587) B44145587
theorem B39240521 : Blo 2041435 39240521 := bstep (se 2 (by rfl) ⟨14715195, by rfl⟩ : syracuseStep 39240521 = 29430391) B29430391
theorem B26160347 : Blo 2041435 26160347 := bstep (se 1 (by rfl) ⟨19620260, by rfl⟩ : syracuseStep 26160347 = 39240521) B39240521
theorem B17440231 : Blo 2041435 17440231 := bstep (se 1 (by rfl) ⟨13080173, by rfl⟩ : syracuseStep 17440231 = 26160347) B26160347
theorem B23253641 : Blo 2041435 23253641 := bstep (se 2 (by rfl) ⟨8720115, by rfl⟩ : syracuseStep 23253641 = 17440231) B17440231
theorem B15502427 : Blo 2041435 15502427 := bstep (se 1 (by rfl) ⟨11626820, by rfl⟩ : syracuseStep 15502427 = 23253641) B23253641
theorem B10334951 : Blo 2041435 10334951 := bstep (se 1 (by rfl) ⟨7751213, by rfl⟩ : syracuseStep 10334951 = 15502427) B15502427
theorem B6889967 : Blo 2041435 6889967 := bstep (se 1 (by rfl) ⟨5167475, by rfl⟩ : syracuseStep 6889967 = 10334951) B10334951
theorem B4593311 : Blo 2041435 4593311 := bstep (se 1 (by rfl) ⟨3444983, by rfl⟩ : syracuseStep 4593311 = 6889967) B6889967
theorem B3062207 : Blo 2041435 3062207 := bstep (se 1 (by rfl) ⟨2296655, by rfl⟩ : syracuseStep 3062207 = 4593311) B4593311
theorem B2041471 : Blo 2041435 2041471 := bstep (se 1 (by rfl) ⟨1531103, by rfl⟩ : syracuseStep 2041471 = 3062207) B3062207
theorem B3062213 : Blo 2041435 3062213 := bbase (se 4 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 3062213 = 574165) (by norm_num)
theorem B2041475 : Blo 2041435 2041475 := bstep (se 1 (by rfl) ⟨1531106, by rfl⟩ : syracuseStep 2041475 = 3062213) B3062213
theorem B3444997 : Blo 2041435 3444997 := bbase (se 4 (by rfl) ⟨322968, by rfl⟩ : syracuseStep 3444997 = 645937) (by norm_num)
theorem B4593329 : Blo 2041435 4593329 := bstep (se 2 (by rfl) ⟨1722498, by rfl⟩ : syracuseStep 4593329 = 3444997) B3444997
theorem B3062219 : Blo 2041435 3062219 := bstep (se 1 (by rfl) ⟨2296664, by rfl⟩ : syracuseStep 3062219 = 4593329) B4593329
theorem B2041479 : Blo 2041435 2041479 := bstep (se 1 (by rfl) ⟨1531109, by rfl⟩ : syracuseStep 2041479 = 3062219) B3062219
theorem B2296669 : Blo 2041435 2296669 := bbase (se 3 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 2296669 = 861251) (by norm_num)
theorem B3062225 : Blo 2041435 3062225 := bstep (se 2 (by rfl) ⟨1148334, by rfl⟩ : syracuseStep 3062225 = 2296669) B2296669
theorem B2041483 : Blo 2041435 2041483 := bstep (se 1 (by rfl) ⟨1531112, by rfl⟩ : syracuseStep 2041483 = 3062225) B3062225
theorem B6890021 : Blo 2041435 6890021 := bbase (se 4 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 6890021 = 1291879) (by norm_num)
theorem B4593347 : Blo 2041435 4593347 := bstep (se 1 (by rfl) ⟨3445010, by rfl⟩ : syracuseStep 4593347 = 6890021) B6890021
theorem B3062231 : Blo 2041435 3062231 := bstep (se 1 (by rfl) ⟨2296673, by rfl⟩ : syracuseStep 3062231 = 4593347) B4593347
theorem B2041487 : Blo 2041435 2041487 := bstep (se 1 (by rfl) ⟨1531115, by rfl⟩ : syracuseStep 2041487 = 3062231) B3062231
theorem B3062237 : Blo 2041435 3062237 := bbase (se 3 (by rfl) ⟨574169, by rfl⟩ : syracuseStep 3062237 = 1148339) (by norm_num)
theorem B2041491 : Blo 2041435 2041491 := bstep (se 1 (by rfl) ⟨1531118, by rfl⟩ : syracuseStep 2041491 = 3062237) B3062237
theorem B4593365 : Blo 2041435 4593365 := bbase (se 7 (by rfl) ⟨53828, by rfl⟩ : syracuseStep 4593365 = 107657) (by norm_num)
theorem B3062243 : Blo 2041435 3062243 := bstep (se 1 (by rfl) ⟨2296682, by rfl⟩ : syracuseStep 3062243 = 4593365) B4593365
theorem B2041495 : Blo 2041435 2041495 := bstep (se 1 (by rfl) ⟨1531121, by rfl⟩ : syracuseStep 2041495 = 3062243) B3062243
theorem B5518277 : Blo 2041435 5518277 := bbase (se 4 (by rfl) ⟨517338, by rfl⟩ : syracuseStep 5518277 = 1034677) (by norm_num)
theorem B3678851 : Blo 2041435 3678851 := bstep (se 1 (by rfl) ⟨2759138, by rfl⟩ : syracuseStep 3678851 = 5518277) B5518277
theorem B2452567 : Blo 2041435 2452567 := bstep (se 1 (by rfl) ⟨1839425, by rfl⟩ : syracuseStep 2452567 = 3678851) B3678851
theorem B3270089 : Blo 2041435 3270089 := bstep (se 2 (by rfl) ⟨1226283, by rfl⟩ : syracuseStep 3270089 = 2452567) B2452567
theorem B8720237 : Blo 2041435 8720237 := bstep (se 3 (by rfl) ⟨1635044, by rfl⟩ : syracuseStep 8720237 = 3270089) B3270089
theorem B5813491 : Blo 2041435 5813491 := bstep (se 1 (by rfl) ⟨4360118, by rfl⟩ : syracuseStep 5813491 = 8720237) B8720237
theorem B7751321 : Blo 2041435 7751321 := bstep (se 2 (by rfl) ⟨2906745, by rfl⟩ : syracuseStep 7751321 = 5813491) B5813491
theorem B5167547 : Blo 2041435 5167547 := bstep (se 1 (by rfl) ⟨3875660, by rfl⟩ : syracuseStep 5167547 = 7751321) B7751321
theorem B3445031 : Blo 2041435 3445031 := bstep (se 1 (by rfl) ⟨2583773, by rfl⟩ : syracuseStep 3445031 = 5167547) B5167547
theorem B2296687 : Blo 2041435 2296687 := bstep (se 1 (by rfl) ⟨1722515, by rfl⟩ : syracuseStep 2296687 = 3445031) B3445031
theorem B3062249 : Blo 2041435 3062249 := bstep (se 2 (by rfl) ⟨1148343, by rfl⟩ : syracuseStep 3062249 = 2296687) B2296687
theorem B2041499 : Blo 2041435 2041499 := bstep (se 1 (by rfl) ⟨1531124, by rfl⟩ : syracuseStep 2041499 = 3062249) B3062249
theorem B2069357 : Blo 2041435 2069357 := bbase (se 3 (by rfl) ⟨388004, by rfl⟩ : syracuseStep 2069357 = 776009) (by norm_num)
theorem B22073141 : Blo 2041435 22073141 := bstep (se 5 (by rfl) ⟨1034678, by rfl⟩ : syracuseStep 22073141 = 2069357) B2069357
theorem B14715427 : Blo 2041435 14715427 := bstep (se 1 (by rfl) ⟨11036570, by rfl⟩ : syracuseStep 14715427 = 22073141) B22073141
theorem B19620569 : Blo 2041435 19620569 := bstep (se 2 (by rfl) ⟨7357713, by rfl⟩ : syracuseStep 19620569 = 14715427) B14715427
theorem B13080379 : Blo 2041435 13080379 := bstep (se 1 (by rfl) ⟨9810284, by rfl⟩ : syracuseStep 13080379 = 19620569) B19620569
theorem B17440505 : Blo 2041435 17440505 := bstep (se 2 (by rfl) ⟨6540189, by rfl⟩ : syracuseStep 17440505 = 13080379) B13080379
theorem B11627003 : Blo 2041435 11627003 := bstep (se 1 (by rfl) ⟨8720252, by rfl⟩ : syracuseStep 11627003 = 17440505) B17440505
theorem B7751335 : Blo 2041435 7751335 := bstep (se 1 (by rfl) ⟨5813501, by rfl⟩ : syracuseStep 7751335 = 11627003) B11627003
theorem B10335113 : Blo 2041435 10335113 := bstep (se 2 (by rfl) ⟨3875667, by rfl⟩ : syracuseStep 10335113 = 7751335) B7751335
theorem B6890075 : Blo 2041435 6890075 := bstep (se 1 (by rfl) ⟨5167556, by rfl⟩ : syracuseStep 6890075 = 10335113) B10335113
theorem B4593383 : Blo 2041435 4593383 := bstep (se 1 (by rfl) ⟨3445037, by rfl⟩ : syracuseStep 4593383 = 6890075) B6890075
theorem B3062255 : Blo 2041435 3062255 := bstep (se 1 (by rfl) ⟨2296691, by rfl⟩ : syracuseStep 3062255 = 4593383) B4593383
theorem B2041503 : Blo 2041435 2041503 := bstep (se 1 (by rfl) ⟨1531127, by rfl⟩ : syracuseStep 2041503 = 3062255) B3062255
theorem B3062261 : Blo 2041435 3062261 := bbase (se 5 (by rfl) ⟨143543, by rfl⟩ : syracuseStep 3062261 = 287087) (by norm_num)
theorem B2041507 : Blo 2041435 2041507 := bstep (se 1 (by rfl) ⟨1531130, by rfl⟩ : syracuseStep 2041507 = 3062261) B3062261
theorem B5813525 : Blo 2041435 5813525 := bbase (se 6 (by rfl) ⟨136254, by rfl⟩ : syracuseStep 5813525 = 272509) (by norm_num)
theorem B3875683 : Blo 2041435 3875683 := bstep (se 1 (by rfl) ⟨2906762, by rfl⟩ : syracuseStep 3875683 = 5813525) B5813525
theorem B5167577 : Blo 2041435 5167577 := bstep (se 2 (by rfl) ⟨1937841, by rfl⟩ : syracuseStep 5167577 = 3875683) B3875683
theorem B3445051 : Blo 2041435 3445051 := bstep (se 1 (by rfl) ⟨2583788, by rfl⟩ : syracuseStep 3445051 = 5167577) B5167577
theorem B4593401 : Blo 2041435 4593401 := bstep (se 2 (by rfl) ⟨1722525, by rfl⟩ : syracuseStep 4593401 = 3445051) B3445051
theorem B3062267 : Blo 2041435 3062267 := bstep (se 1 (by rfl) ⟨2296700, by rfl⟩ : syracuseStep 3062267 = 4593401) B4593401
theorem B2041511 : Blo 2041435 2041511 := bstep (se 1 (by rfl) ⟨1531133, by rfl⟩ : syracuseStep 2041511 = 3062267) B3062267
theorem B2296705 : Blo 2041435 2296705 := bbase (se 2 (by rfl) ⟨861264, by rfl⟩ : syracuseStep 2296705 = 1722529) (by norm_num)
theorem B3062273 : Blo 2041435 3062273 := bstep (se 2 (by rfl) ⟨1148352, by rfl⟩ : syracuseStep 3062273 = 2296705) B2296705
theorem B2041515 : Blo 2041435 2041515 := bstep (se 1 (by rfl) ⟨1531136, by rfl⟩ : syracuseStep 2041515 = 3062273) B3062273
theorem B5167597 : Blo 2041435 5167597 := bbase (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) (by norm_num)
theorem B6890129 : Blo 2041435 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B4593419 : Blo 2041435 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B3062279 : Blo 2041435 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B2041519 : Blo 2041435 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B3062285 : Blo 2041435 3062285 := bbase (se 3 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 3062285 = 1148357) (by norm_num)
theorem B2041523 : Blo 2041435 2041523 := bstep (se 1 (by rfl) ⟨1531142, by rfl⟩ : syracuseStep 2041523 = 3062285) B3062285
theorem B4593437 : Blo 2041435 4593437 := bbase (se 3 (by rfl) ⟨861269, by rfl⟩ : syracuseStep 4593437 = 1722539) (by norm_num)
theorem B3062291 : Blo 2041435 3062291 := bstep (se 1 (by rfl) ⟨2296718, by rfl⟩ : syracuseStep 3062291 = 4593437) B4593437
theorem B2041527 : Blo 2041435 2041527 := bstep (se 1 (by rfl) ⟨1531145, by rfl⟩ : syracuseStep 2041527 = 3062291) B3062291
theorem B3445085 : Blo 2041435 3445085 := bbase (se 3 (by rfl) ⟨645953, by rfl⟩ : syracuseStep 3445085 = 1291907) (by norm_num)
theorem B2296723 : Blo 2041435 2296723 := bstep (se 1 (by rfl) ⟨1722542, by rfl⟩ : syracuseStep 2296723 = 3445085) B3445085
theorem B3062297 : Blo 2041435 3062297 := bstep (se 2 (by rfl) ⟨1148361, by rfl⟩ : syracuseStep 3062297 = 2296723) B2296723
theorem B2041531 : Blo 2041435 2041531 := bstep (se 1 (by rfl) ⟨1531148, by rfl⟩ : syracuseStep 2041531 = 3062297) B3062297
theorem B8720389 : Blo 2041435 8720389 := bbase (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) (by norm_num)
theorem B11627185 : Blo 2041435 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B15502913 : Blo 2041435 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B10335275 : Blo 2041435 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B6890183 : Blo 2041435 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B4593455 : Blo 2041435 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B3062303 : Blo 2041435 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B2041535 : Blo 2041435 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B3062309 : Blo 2041435 3062309 := bbase (se 4 (by rfl) ⟨287091, by rfl⟩ : syracuseStep 3062309 = 574183) (by norm_num)
theorem B2041539 : Blo 2041435 2041539 := bstep (se 1 (by rfl) ⟨1531154, by rfl⟩ : syracuseStep 2041539 = 3062309) B3062309
theorem B2583829 : Blo 2041435 2583829 := bbase (se 6 (by rfl) ⟨60558, by rfl⟩ : syracuseStep 2583829 = 121117) (by norm_num)
theorem B3445105 : Blo 2041435 3445105 := bstep (se 2 (by rfl) ⟨1291914, by rfl⟩ : syracuseStep 3445105 = 2583829) B2583829
theorem B4593473 : Blo 2041435 4593473 := bstep (se 2 (by rfl) ⟨1722552, by rfl⟩ : syracuseStep 4593473 = 3445105) B3445105
theorem B3062315 : Blo 2041435 3062315 := bstep (se 1 (by rfl) ⟨2296736, by rfl⟩ : syracuseStep 3062315 = 4593473) B4593473
theorem B2041543 : Blo 2041435 2041543 := bstep (se 1 (by rfl) ⟨1531157, by rfl⟩ : syracuseStep 2041543 = 3062315) B3062315
theorem B2296741 : Blo 2041435 2296741 := bbase (se 4 (by rfl) ⟨215319, by rfl⟩ : syracuseStep 2296741 = 430639) (by norm_num)
theorem B3062321 : Blo 2041435 3062321 := bstep (se 2 (by rfl) ⟨1148370, by rfl⟩ : syracuseStep 3062321 = 2296741) B2296741
theorem B2041547 : Blo 2041435 2041547 := bstep (se 1 (by rfl) ⟨1531160, by rfl⟩ : syracuseStep 2041547 = 3062321) B3062321
theorem B9810517 : Blo 2041435 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B13080689 : Blo 2041435 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B8720459 : Blo 2041435 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B5813639 : Blo 2041435 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B3875759 : Blo 2041435 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B2583839 : Blo 2041435 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B6890237 : Blo 2041435 6890237 := bstep (se 3 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 6890237 = 2583839) B2583839
theorem B4593491 : Blo 2041435 4593491 := bstep (se 1 (by rfl) ⟨3445118, by rfl⟩ : syracuseStep 4593491 = 6890237) B6890237
theorem B3062327 : Blo 2041435 3062327 := bstep (se 1 (by rfl) ⟨2296745, by rfl⟩ : syracuseStep 3062327 = 4593491) B4593491
theorem B2041551 : Blo 2041435 2041551 := bstep (se 1 (by rfl) ⟨1531163, by rfl⟩ : syracuseStep 2041551 = 3062327) B3062327
theorem B3062333 : Blo 2041435 3062333 := bbase (se 3 (by rfl) ⟨574187, by rfl⟩ : syracuseStep 3062333 = 1148375) (by norm_num)
theorem B2041555 : Blo 2041435 2041555 := bstep (se 1 (by rfl) ⟨1531166, by rfl⟩ : syracuseStep 2041555 = 3062333) B3062333
theorem B4593509 : Blo 2041435 4593509 := bbase (se 4 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 4593509 = 861283) (by norm_num)
theorem B3062339 : Blo 2041435 3062339 := bstep (se 1 (by rfl) ⟨2296754, by rfl⟩ : syracuseStep 3062339 = 4593509) B4593509
theorem B2041559 : Blo 2041435 2041559 := bstep (se 1 (by rfl) ⟨1531169, by rfl⟩ : syracuseStep 2041559 = 3062339) B3062339
theorem B5167709 : Blo 2041435 5167709 := bbase (se 3 (by rfl) ⟨968945, by rfl⟩ : syracuseStep 5167709 = 1937891) (by norm_num)
theorem B3445139 : Blo 2041435 3445139 := bstep (se 1 (by rfl) ⟨2583854, by rfl⟩ : syracuseStep 3445139 = 5167709) B5167709
theorem B2296759 : Blo 2041435 2296759 := bstep (se 1 (by rfl) ⟨1722569, by rfl⟩ : syracuseStep 2296759 = 3445139) B3445139
theorem B3062345 : Blo 2041435 3062345 := bstep (se 2 (by rfl) ⟨1148379, by rfl⟩ : syracuseStep 3062345 = 2296759) B2296759
theorem B2041563 : Blo 2041435 2041563 := bstep (se 1 (by rfl) ⟨1531172, by rfl⟩ : syracuseStep 2041563 = 3062345) B3062345
theorem B3875789 : Blo 2041435 3875789 := bbase (se 3 (by rfl) ⟨726710, by rfl⟩ : syracuseStep 3875789 = 1453421) (by norm_num)
theorem B10335437 : Blo 2041435 10335437 := bstep (se 3 (by rfl) ⟨1937894, by rfl⟩ : syracuseStep 10335437 = 3875789) B3875789
theorem B6890291 : Blo 2041435 6890291 := bstep (se 1 (by rfl) ⟨5167718, by rfl⟩ : syracuseStep 6890291 = 10335437) B10335437
theorem B4593527 : Blo 2041435 4593527 := bstep (se 1 (by rfl) ⟨3445145, by rfl⟩ : syracuseStep 4593527 = 6890291) B6890291
theorem B3062351 : Blo 2041435 3062351 := bstep (se 1 (by rfl) ⟨2296763, by rfl⟩ : syracuseStep 3062351 = 4593527) B4593527
theorem B2041567 : Blo 2041435 2041567 := bstep (se 1 (by rfl) ⟨1531175, by rfl⟩ : syracuseStep 2041567 = 3062351) B3062351
theorem B3062357 : Blo 2041435 3062357 := bbase (se 8 (by rfl) ⟨17943, by rfl⟩ : syracuseStep 3062357 = 35887) (by norm_num)
theorem B2041571 : Blo 2041435 2041571 := bstep (se 1 (by rfl) ⟨1531178, by rfl⟩ : syracuseStep 2041571 = 3062357) B3062357
theorem B6540421 : Blo 2041435 6540421 := bbase (se 4 (by rfl) ⟨613164, by rfl⟩ : syracuseStep 6540421 = 1226329) (by norm_num)
theorem B8720561 : Blo 2041435 8720561 := bstep (se 2 (by rfl) ⟨3270210, by rfl⟩ : syracuseStep 8720561 = 6540421) B6540421
theorem B5813707 : Blo 2041435 5813707 := bstep (se 1 (by rfl) ⟨4360280, by rfl⟩ : syracuseStep 5813707 = 8720561) B8720561
theorem B7751609 : Blo 2041435 7751609 := bstep (se 2 (by rfl) ⟨2906853, by rfl⟩ : syracuseStep 7751609 = 5813707) B5813707
theorem B5167739 : Blo 2041435 5167739 := bstep (se 1 (by rfl) ⟨3875804, by rfl⟩ : syracuseStep 5167739 = 7751609) B7751609
theorem B3445159 : Blo 2041435 3445159 := bstep (se 1 (by rfl) ⟨2583869, by rfl⟩ : syracuseStep 3445159 = 5167739) B5167739
theorem B4593545 : Blo 2041435 4593545 := bstep (se 2 (by rfl) ⟨1722579, by rfl⟩ : syracuseStep 4593545 = 3445159) B3445159
theorem B3062363 : Blo 2041435 3062363 := bstep (se 1 (by rfl) ⟨2296772, by rfl⟩ : syracuseStep 3062363 = 4593545) B4593545
theorem B2041575 : Blo 2041435 2041575 := bstep (se 1 (by rfl) ⟨1531181, by rfl⟩ : syracuseStep 2041575 = 3062363) B3062363
theorem B2296777 : Blo 2041435 2296777 := bbase (se 2 (by rfl) ⟨861291, by rfl⟩ : syracuseStep 2296777 = 1722583) (by norm_num)
theorem B3062369 : Blo 2041435 3062369 := bstep (se 2 (by rfl) ⟨1148388, by rfl⟩ : syracuseStep 3062369 = 2296777) B2296777
theorem B2041579 : Blo 2041435 2041579 := bstep (se 1 (by rfl) ⟨1531184, by rfl⟩ : syracuseStep 2041579 = 3062369) B3062369
theorem B4138877 : Blo 2041435 4138877 := bbase (se 3 (by rfl) ⟨776039, by rfl⟩ : syracuseStep 4138877 = 1552079) (by norm_num)
theorem B11037005 : Blo 2041435 11037005 := bstep (se 3 (by rfl) ⟨2069438, by rfl⟩ : syracuseStep 11037005 = 4138877) B4138877
theorem B7358003 : Blo 2041435 7358003 := bstep (se 1 (by rfl) ⟨5518502, by rfl⟩ : syracuseStep 7358003 = 11037005) B11037005
theorem B4905335 : Blo 2041435 4905335 := bstep (se 1 (by rfl) ⟨3679001, by rfl⟩ : syracuseStep 4905335 = 7358003) B7358003
theorem B3270223 : Blo 2041435 3270223 := bstep (se 1 (by rfl) ⟨2452667, by rfl⟩ : syracuseStep 3270223 = 4905335) B4905335
theorem B17441189 : Blo 2041435 17441189 := bstep (se 4 (by rfl) ⟨1635111, by rfl⟩ : syracuseStep 17441189 = 3270223) B3270223
theorem B11627459 : Blo 2041435 11627459 := bstep (se 1 (by rfl) ⟨8720594, by rfl⟩ : syracuseStep 11627459 = 17441189) B17441189
theorem B7751639 : Blo 2041435 7751639 := bstep (se 1 (by rfl) ⟨5813729, by rfl⟩ : syracuseStep 7751639 = 11627459) B11627459
theorem B5167759 : Blo 2041435 5167759 := bstep (se 1 (by rfl) ⟨3875819, by rfl⟩ : syracuseStep 5167759 = 7751639) B7751639
theorem B6890345 : Blo 2041435 6890345 := bstep (se 2 (by rfl) ⟨2583879, by rfl⟩ : syracuseStep 6890345 = 5167759) B5167759
theorem B4593563 : Blo 2041435 4593563 := bstep (se 1 (by rfl) ⟨3445172, by rfl⟩ : syracuseStep 4593563 = 6890345) B6890345
theorem B3062375 : Blo 2041435 3062375 := bstep (se 1 (by rfl) ⟨2296781, by rfl⟩ : syracuseStep 3062375 = 4593563) B4593563
theorem B2041583 : Blo 2041435 2041583 := bstep (se 1 (by rfl) ⟨1531187, by rfl⟩ : syracuseStep 2041583 = 3062375) B3062375
theorem B3062381 : Blo 2041435 3062381 := bbase (se 3 (by rfl) ⟨574196, by rfl⟩ : syracuseStep 3062381 = 1148393) (by norm_num)
theorem B2041587 : Blo 2041435 2041587 := bstep (se 1 (by rfl) ⟨1531190, by rfl⟩ : syracuseStep 2041587 = 3062381) B3062381
theorem B4593581 : Blo 2041435 4593581 := bbase (se 3 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 4593581 = 1722593) (by norm_num)
theorem B3062387 : Blo 2041435 3062387 := bstep (se 1 (by rfl) ⟨2296790, by rfl⟩ : syracuseStep 3062387 = 4593581) B4593581
theorem B2041591 : Blo 2041435 2041591 := bstep (se 1 (by rfl) ⟨1531193, by rfl⟩ : syracuseStep 2041591 = 3062387) B3062387
theorem B5813765 : Blo 2041435 5813765 := bbase (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) (by norm_num)
theorem B3875843 : Blo 2041435 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B2583895 : Blo 2041435 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B3445193 : Blo 2041435 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B2296795 : Blo 2041435 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B3062393 : Blo 2041435 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B2041595 : Blo 2041435 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B7857461 : Blo 2041435 7857461 := bbase (se 5 (by rfl) ⟨368318, by rfl⟩ : syracuseStep 7857461 = 736637) (by norm_num)
theorem B5238307 : Blo 2041435 5238307 := bstep (se 1 (by rfl) ⟨3928730, by rfl⟩ : syracuseStep 5238307 = 7857461) B7857461
theorem B6984409 : Blo 2041435 6984409 := bstep (se 2 (by rfl) ⟨2619153, by rfl⟩ : syracuseStep 6984409 = 5238307) B5238307
theorem B9312545 : Blo 2041435 9312545 := bstep (se 2 (by rfl) ⟨3492204, by rfl⟩ : syracuseStep 9312545 = 6984409) B6984409
theorem B6208363 : Blo 2041435 6208363 := bstep (se 1 (by rfl) ⟨4656272, by rfl⟩ : syracuseStep 6208363 = 9312545) B9312545
theorem B8277817 : Blo 2041435 8277817 := bstep (se 2 (by rfl) ⟨3104181, by rfl⟩ : syracuseStep 8277817 = 6208363) B6208363
theorem B11037089 : Blo 2041435 11037089 := bstep (se 2 (by rfl) ⟨4138908, by rfl⟩ : syracuseStep 11037089 = 8277817) B8277817
theorem B7358059 : Blo 2041435 7358059 := bstep (se 1 (by rfl) ⟨5518544, by rfl⟩ : syracuseStep 7358059 = 11037089) B11037089
theorem B39242981 : Blo 2041435 39242981 := bstep (se 4 (by rfl) ⟨3679029, by rfl⟩ : syracuseStep 39242981 = 7358059) B7358059
theorem B26161987 : Blo 2041435 26161987 := bstep (se 1 (by rfl) ⟨19621490, by rfl⟩ : syracuseStep 26161987 = 39242981) B39242981
theorem B34882649 : Blo 2041435 34882649 := bstep (se 2 (by rfl) ⟨13080993, by rfl⟩ : syracuseStep 34882649 = 26161987) B26161987
theorem B23255099 : Blo 2041435 23255099 := bstep (se 1 (by rfl) ⟨17441324, by rfl⟩ : syracuseStep 23255099 = 34882649) B34882649
theorem B15503399 : Blo 2041435 15503399 := bstep (se 1 (by rfl) ⟨11627549, by rfl⟩ : syracuseStep 15503399 = 23255099) B23255099
theorem B10335599 : Blo 2041435 10335599 := bstep (se 1 (by rfl) ⟨7751699, by rfl⟩ : syracuseStep 10335599 = 15503399) B15503399
theorem B6890399 : Blo 2041435 6890399 := bstep (se 1 (by rfl) ⟨5167799, by rfl⟩ : syracuseStep 6890399 = 10335599) B10335599
theorem B4593599 : Blo 2041435 4593599 := bstep (se 1 (by rfl) ⟨3445199, by rfl⟩ : syracuseStep 4593599 = 6890399) B6890399
theorem B3062399 : Blo 2041435 3062399 := bstep (se 1 (by rfl) ⟨2296799, by rfl⟩ : syracuseStep 3062399 = 4593599) B4593599
theorem B2041599 : Blo 2041435 2041599 := bstep (se 1 (by rfl) ⟨1531199, by rfl⟩ : syracuseStep 2041599 = 3062399) B3062399
theorem B3062405 : Blo 2041435 3062405 := bbase (se 4 (by rfl) ⟨287100, by rfl⟩ : syracuseStep 3062405 = 574201) (by norm_num)
theorem B2041603 : Blo 2041435 2041603 := bstep (se 1 (by rfl) ⟨1531202, by rfl⟩ : syracuseStep 2041603 = 3062405) B3062405
theorem B3445213 : Blo 2041435 3445213 := bbase (se 3 (by rfl) ⟨645977, by rfl⟩ : syracuseStep 3445213 = 1291955) (by norm_num)
theorem B4593617 : Blo 2041435 4593617 := bstep (se 2 (by rfl) ⟨1722606, by rfl⟩ : syracuseStep 4593617 = 3445213) B3445213
theorem B3062411 : Blo 2041435 3062411 := bstep (se 1 (by rfl) ⟨2296808, by rfl⟩ : syracuseStep 3062411 = 4593617) B4593617
theorem B2041607 : Blo 2041435 2041607 := bstep (se 1 (by rfl) ⟨1531205, by rfl⟩ : syracuseStep 2041607 = 3062411) B3062411
theorem B2296813 : Blo 2041435 2296813 := bbase (se 3 (by rfl) ⟨430652, by rfl⟩ : syracuseStep 2296813 = 861305) (by norm_num)
theorem B3062417 : Blo 2041435 3062417 := bstep (se 2 (by rfl) ⟨1148406, by rfl⟩ : syracuseStep 3062417 = 2296813) B2296813
theorem B2041611 : Blo 2041435 2041611 := bstep (se 1 (by rfl) ⟨1531208, by rfl⟩ : syracuseStep 2041611 = 3062417) B3062417
theorem B6890453 : Blo 2041435 6890453 := bbase (se 7 (by rfl) ⟨80747, by rfl⟩ : syracuseStep 6890453 = 161495) (by norm_num)
theorem B4593635 : Blo 2041435 4593635 := bstep (se 1 (by rfl) ⟨3445226, by rfl⟩ : syracuseStep 4593635 = 6890453) B6890453
theorem B3062423 : Blo 2041435 3062423 := bstep (se 1 (by rfl) ⟨2296817, by rfl⟩ : syracuseStep 3062423 = 4593635) B4593635
theorem B2041615 : Blo 2041435 2041615 := bstep (se 1 (by rfl) ⟨1531211, by rfl⟩ : syracuseStep 2041615 = 3062423) B3062423
theorem B3062429 : Blo 2041435 3062429 := bbase (se 3 (by rfl) ⟨574205, by rfl⟩ : syracuseStep 3062429 = 1148411) (by norm_num)
theorem B2041619 : Blo 2041435 2041619 := bstep (se 1 (by rfl) ⟨1531214, by rfl⟩ : syracuseStep 2041619 = 3062429) B3062429
theorem B4593653 : Blo 2041435 4593653 := bbase (se 5 (by rfl) ⟨215327, by rfl⟩ : syracuseStep 4593653 = 430655) (by norm_num)
theorem B3062435 : Blo 2041435 3062435 := bstep (se 1 (by rfl) ⟨2296826, by rfl⟩ : syracuseStep 3062435 = 4593653) B4593653
theorem B2041623 : Blo 2041435 2041623 := bstep (se 1 (by rfl) ⟨1531217, by rfl⟩ : syracuseStep 2041623 = 3062435) B3062435
theorem B3729277 : Blo 2041435 3729277 := bbase (se 3 (by rfl) ⟨699239, by rfl⟩ : syracuseStep 3729277 = 1398479) (by norm_num)
theorem B4972369 : Blo 2041435 4972369 := bstep (se 2 (by rfl) ⟨1864638, by rfl⟩ : syracuseStep 4972369 = 3729277) B3729277
theorem B6629825 : Blo 2041435 6629825 := bstep (se 2 (by rfl) ⟨2486184, by rfl⟩ : syracuseStep 6629825 = 4972369) B4972369
theorem B4419883 : Blo 2041435 4419883 := bstep (se 1 (by rfl) ⟨3314912, by rfl⟩ : syracuseStep 4419883 = 6629825) B6629825
theorem B5893177 : Blo 2041435 5893177 := bstep (se 2 (by rfl) ⟨2209941, by rfl⟩ : syracuseStep 5893177 = 4419883) B4419883
theorem B7857569 : Blo 2041435 7857569 := bstep (se 2 (by rfl) ⟨2946588, by rfl⟩ : syracuseStep 7857569 = 5893177) B5893177
theorem B5238379 : Blo 2041435 5238379 := bstep (se 1 (by rfl) ⟨3928784, by rfl⟩ : syracuseStep 5238379 = 7857569) B7857569
theorem B6984505 : Blo 2041435 6984505 := bstep (se 2 (by rfl) ⟨2619189, by rfl⟩ : syracuseStep 6984505 = 5238379) B5238379
theorem B37250693 : Blo 2041435 37250693 := bstep (se 4 (by rfl) ⟨3492252, by rfl⟩ : syracuseStep 37250693 = 6984505) B6984505
theorem B24833795 : Blo 2041435 24833795 := bstep (se 1 (by rfl) ⟨18625346, by rfl⟩ : syracuseStep 24833795 = 37250693) B37250693
theorem B66223453 : Blo 2041435 66223453 := bstep (se 3 (by rfl) ⟨12416897, by rfl⟩ : syracuseStep 66223453 = 24833795) B24833795
theorem B88297937 : Blo 2041435 88297937 := bstep (se 2 (by rfl) ⟨33111726, by rfl⟩ : syracuseStep 88297937 = 66223453) B66223453
theorem B58865291 : Blo 2041435 58865291 := bstep (se 1 (by rfl) ⟨44148968, by rfl⟩ : syracuseStep 58865291 = 88297937) B88297937
theorem B39243527 : Blo 2041435 39243527 := bstep (se 1 (by rfl) ⟨29432645, by rfl⟩ : syracuseStep 39243527 = 58865291) B58865291
theorem B26162351 : Blo 2041435 26162351 := bstep (se 1 (by rfl) ⟨19621763, by rfl⟩ : syracuseStep 26162351 = 39243527) B39243527
theorem B17441567 : Blo 2041435 17441567 := bstep (se 1 (by rfl) ⟨13081175, by rfl⟩ : syracuseStep 17441567 = 26162351) B26162351
theorem B11627711 : Blo 2041435 11627711 := bstep (se 1 (by rfl) ⟨8720783, by rfl⟩ : syracuseStep 11627711 = 17441567) B17441567
theorem B7751807 : Blo 2041435 7751807 := bstep (se 1 (by rfl) ⟨5813855, by rfl⟩ : syracuseStep 7751807 = 11627711) B11627711
theorem B5167871 : Blo 2041435 5167871 := bstep (se 1 (by rfl) ⟨3875903, by rfl⟩ : syracuseStep 5167871 = 7751807) B7751807
theorem B3445247 : Blo 2041435 3445247 := bstep (se 1 (by rfl) ⟨2583935, by rfl⟩ : syracuseStep 3445247 = 5167871) B5167871
theorem B2296831 : Blo 2041435 2296831 := bstep (se 1 (by rfl) ⟨1722623, by rfl⟩ : syracuseStep 2296831 = 3445247) B3445247
theorem B3062441 : Blo 2041435 3062441 := bstep (se 2 (by rfl) ⟨1148415, by rfl⟩ : syracuseStep 3062441 = 2296831) B2296831
theorem B2041627 : Blo 2041435 2041627 := bstep (se 1 (by rfl) ⟨1531220, by rfl⟩ : syracuseStep 2041627 = 3062441) B3062441
theorem B2906933 : Blo 2041435 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B7751821 : Blo 2041435 7751821 := bstep (se 3 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 7751821 = 2906933) B2906933
theorem B10335761 : Blo 2041435 10335761 := bstep (se 2 (by rfl) ⟨3875910, by rfl⟩ : syracuseStep 10335761 = 7751821) B7751821
theorem B6890507 : Blo 2041435 6890507 := bstep (se 1 (by rfl) ⟨5167880, by rfl⟩ : syracuseStep 6890507 = 10335761) B10335761
theorem B4593671 : Blo 2041435 4593671 := bstep (se 1 (by rfl) ⟨3445253, by rfl⟩ : syracuseStep 4593671 = 6890507) B6890507
theorem B3062447 : Blo 2041435 3062447 := bstep (se 1 (by rfl) ⟨2296835, by rfl⟩ : syracuseStep 3062447 = 4593671) B4593671
theorem B2041631 : Blo 2041435 2041631 := bstep (se 1 (by rfl) ⟨1531223, by rfl⟩ : syracuseStep 2041631 = 3062447) B3062447
theorem B3062453 : Blo 2041435 3062453 := bbase (se 5 (by rfl) ⟨143552, by rfl⟩ : syracuseStep 3062453 = 287105) (by norm_num)
theorem B2041635 : Blo 2041435 2041635 := bstep (se 1 (by rfl) ⟨1531226, by rfl⟩ : syracuseStep 2041635 = 3062453) B3062453
theorem B5167901 : Blo 2041435 5167901 := bbase (se 3 (by rfl) ⟨968981, by rfl⟩ : syracuseStep 5167901 = 1937963) (by norm_num)
theorem B3445267 : Blo 2041435 3445267 := bstep (se 1 (by rfl) ⟨2583950, by rfl⟩ : syracuseStep 3445267 = 5167901) B5167901
theorem B4593689 : Blo 2041435 4593689 := bstep (se 2 (by rfl) ⟨1722633, by rfl⟩ : syracuseStep 4593689 = 3445267) B3445267
theorem B3062459 : Blo 2041435 3062459 := bstep (se 1 (by rfl) ⟨2296844, by rfl⟩ : syracuseStep 3062459 = 4593689) B4593689
theorem B2041639 : Blo 2041435 2041639 := bstep (se 1 (by rfl) ⟨1531229, by rfl⟩ : syracuseStep 2041639 = 3062459) B3062459
theorem B2296849 : Blo 2041435 2296849 := bbase (se 2 (by rfl) ⟨861318, by rfl⟩ : syracuseStep 2296849 = 1722637) (by norm_num)
theorem B3062465 : Blo 2041435 3062465 := bstep (se 2 (by rfl) ⟨1148424, by rfl⟩ : syracuseStep 3062465 = 2296849) B2296849
theorem B2041643 : Blo 2041435 2041643 := bstep (se 1 (by rfl) ⟨1531232, by rfl⟩ : syracuseStep 2041643 = 3062465) B3062465
theorem B3875941 : Blo 2041435 3875941 := bbase (se 4 (by rfl) ⟨363369, by rfl⟩ : syracuseStep 3875941 = 726739) (by norm_num)
theorem B5167921 : Blo 2041435 5167921 := bstep (se 2 (by rfl) ⟨1937970, by rfl⟩ : syracuseStep 5167921 = 3875941) B3875941
theorem B6890561 : Blo 2041435 6890561 := bstep (se 2 (by rfl) ⟨2583960, by rfl⟩ : syracuseStep 6890561 = 5167921) B5167921
theorem B4593707 : Blo 2041435 4593707 := bstep (se 1 (by rfl) ⟨3445280, by rfl⟩ : syracuseStep 4593707 = 6890561) B6890561
theorem B3062471 : Blo 2041435 3062471 := bstep (se 1 (by rfl) ⟨2296853, by rfl⟩ : syracuseStep 3062471 = 4593707) B4593707
theorem B2041647 : Blo 2041435 2041647 := bstep (se 1 (by rfl) ⟨1531235, by rfl⟩ : syracuseStep 2041647 = 3062471) B3062471
theorem B3062477 : Blo 2041435 3062477 := bbase (se 3 (by rfl) ⟨574214, by rfl⟩ : syracuseStep 3062477 = 1148429) (by norm_num)
theorem B2041651 : Blo 2041435 2041651 := bstep (se 1 (by rfl) ⟨1531238, by rfl⟩ : syracuseStep 2041651 = 3062477) B3062477
theorem B4593725 : Blo 2041435 4593725 := bbase (se 3 (by rfl) ⟨861323, by rfl⟩ : syracuseStep 4593725 = 1722647) (by norm_num)
theorem B3062483 : Blo 2041435 3062483 := bstep (se 1 (by rfl) ⟨2296862, by rfl⟩ : syracuseStep 3062483 = 4593725) B4593725
theorem B2041655 : Blo 2041435 2041655 := bstep (se 1 (by rfl) ⟨1531241, by rfl⟩ : syracuseStep 2041655 = 3062483) B3062483
theorem B3445301 : Blo 2041435 3445301 := bbase (se 5 (by rfl) ⟨161498, by rfl⟩ : syracuseStep 3445301 = 322997) (by norm_num)
theorem B2296867 : Blo 2041435 2296867 := bstep (se 1 (by rfl) ⟨1722650, by rfl⟩ : syracuseStep 2296867 = 3445301) B3445301
theorem B3062489 : Blo 2041435 3062489 := bstep (se 2 (by rfl) ⟨1148433, by rfl⟩ : syracuseStep 3062489 = 2296867) B2296867
theorem B2041659 : Blo 2041435 2041659 := bstep (se 1 (by rfl) ⟨1531244, by rfl⟩ : syracuseStep 2041659 = 3062489) B3062489
theorem B5813957 : Blo 2041435 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B15503885 : Blo 2041435 15503885 := bstep (se 3 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 15503885 = 5813957) B5813957
theorem B10335923 : Blo 2041435 10335923 := bstep (se 1 (by rfl) ⟨7751942, by rfl⟩ : syracuseStep 10335923 = 15503885) B15503885
theorem B6890615 : Blo 2041435 6890615 := bstep (se 1 (by rfl) ⟨5167961, by rfl⟩ : syracuseStep 6890615 = 10335923) B10335923
theorem B4593743 : Blo 2041435 4593743 := bstep (se 1 (by rfl) ⟨3445307, by rfl⟩ : syracuseStep 4593743 = 6890615) B6890615
theorem B3062495 : Blo 2041435 3062495 := bstep (se 1 (by rfl) ⟨2296871, by rfl⟩ : syracuseStep 3062495 = 4593743) B4593743
theorem B2041663 : Blo 2041435 2041663 := bstep (se 1 (by rfl) ⟨1531247, by rfl⟩ : syracuseStep 2041663 = 3062495) B3062495
theorem B3062501 : Blo 2041435 3062501 := bbase (se 4 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 3062501 = 574219) (by norm_num)
theorem B2041667 : Blo 2041435 2041667 := bstep (se 1 (by rfl) ⟨1531250, by rfl⟩ : syracuseStep 2041667 = 3062501) B3062501
theorem B3270365 : Blo 2041435 3270365 := bbase (se 3 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 3270365 = 1226387) (by norm_num)
theorem B2180243 : Blo 2041435 2180243 := bstep (se 1 (by rfl) ⟨1635182, by rfl⟩ : syracuseStep 2180243 = 3270365) B3270365
theorem B5813981 : Blo 2041435 5813981 := bstep (se 3 (by rfl) ⟨1090121, by rfl⟩ : syracuseStep 5813981 = 2180243) B2180243
theorem B3875987 : Blo 2041435 3875987 := bstep (se 1 (by rfl) ⟨2906990, by rfl⟩ : syracuseStep 3875987 = 5813981) B5813981
theorem B2583991 : Blo 2041435 2583991 := bstep (se 1 (by rfl) ⟨1937993, by rfl⟩ : syracuseStep 2583991 = 3875987) B3875987
theorem B3445321 : Blo 2041435 3445321 := bstep (se 2 (by rfl) ⟨1291995, by rfl⟩ : syracuseStep 3445321 = 2583991) B2583991
theorem B4593761 : Blo 2041435 4593761 := bstep (se 2 (by rfl) ⟨1722660, by rfl⟩ : syracuseStep 4593761 = 3445321) B3445321
theorem B3062507 : Blo 2041435 3062507 := bstep (se 1 (by rfl) ⟨2296880, by rfl⟩ : syracuseStep 3062507 = 4593761) B4593761
theorem B2041671 : Blo 2041435 2041671 := bstep (se 1 (by rfl) ⟨1531253, by rfl⟩ : syracuseStep 2041671 = 3062507) B3062507
theorem B2296885 : Blo 2041435 2296885 := bbase (se 5 (by rfl) ⟨107666, by rfl⟩ : syracuseStep 2296885 = 215333) (by norm_num)
theorem B3062513 : Blo 2041435 3062513 := bstep (se 2 (by rfl) ⟨1148442, by rfl⟩ : syracuseStep 3062513 = 2296885) B2296885
theorem B2041675 : Blo 2041435 2041675 := bstep (se 1 (by rfl) ⟨1531256, by rfl⟩ : syracuseStep 2041675 = 3062513) B3062513
theorem B2584001 : Blo 2041435 2584001 := bbase (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) (by norm_num)
theorem B6890669 : Blo 2041435 6890669 := bstep (se 3 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 6890669 = 2584001) B2584001
theorem B4593779 : Blo 2041435 4593779 := bstep (se 1 (by rfl) ⟨3445334, by rfl⟩ : syracuseStep 4593779 = 6890669) B6890669
theorem B3062519 : Blo 2041435 3062519 := bstep (se 1 (by rfl) ⟨2296889, by rfl⟩ : syracuseStep 3062519 = 4593779) B4593779
theorem B2041679 : Blo 2041435 2041679 := bstep (se 1 (by rfl) ⟨1531259, by rfl⟩ : syracuseStep 2041679 = 3062519) B3062519
theorem B3062525 : Blo 2041435 3062525 := bbase (se 3 (by rfl) ⟨574223, by rfl⟩ : syracuseStep 3062525 = 1148447) (by norm_num)
theorem B2041683 : Blo 2041435 2041683 := bstep (se 1 (by rfl) ⟨1531262, by rfl⟩ : syracuseStep 2041683 = 3062525) B3062525
theorem B4593797 : Blo 2041435 4593797 := bbase (se 4 (by rfl) ⟨430668, by rfl⟩ : syracuseStep 4593797 = 861337) (by norm_num)
theorem B3062531 : Blo 2041435 3062531 := bstep (se 1 (by rfl) ⟨2296898, by rfl⟩ : syracuseStep 3062531 = 4593797) B4593797
theorem B2041687 : Blo 2041435 2041687 := bstep (se 1 (by rfl) ⟨1531265, by rfl⟩ : syracuseStep 2041687 = 3062531) B3062531
theorem B3270397 : Blo 2041435 3270397 := bbase (se 3 (by rfl) ⟨613199, by rfl⟩ : syracuseStep 3270397 = 1226399) (by norm_num)
theorem B4360529 : Blo 2041435 4360529 := bstep (se 2 (by rfl) ⟨1635198, by rfl⟩ : syracuseStep 4360529 = 3270397) B3270397
theorem B2907019 : Blo 2041435 2907019 := bstep (se 1 (by rfl) ⟨2180264, by rfl⟩ : syracuseStep 2907019 = 4360529) B4360529
theorem B3876025 : Blo 2041435 3876025 := bstep (se 2 (by rfl) ⟨1453509, by rfl⟩ : syracuseStep 3876025 = 2907019) B2907019
theorem B5168033 : Blo 2041435 5168033 := bstep (se 2 (by rfl) ⟨1938012, by rfl⟩ : syracuseStep 5168033 = 3876025) B3876025
theorem B3445355 : Blo 2041435 3445355 := bstep (se 1 (by rfl) ⟨2584016, by rfl⟩ : syracuseStep 3445355 = 5168033) B5168033
theorem B2296903 : Blo 2041435 2296903 := bstep (se 1 (by rfl) ⟨1722677, by rfl⟩ : syracuseStep 2296903 = 3445355) B3445355
theorem B3062537 : Blo 2041435 3062537 := bstep (se 2 (by rfl) ⟨1148451, by rfl⟩ : syracuseStep 3062537 = 2296903) B2296903
theorem B2041691 : Blo 2041435 2041691 := bstep (se 1 (by rfl) ⟨1531268, by rfl⟩ : syracuseStep 2041691 = 3062537) B3062537
theorem B10336085 : Blo 2041435 10336085 := bbase (se 9 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 10336085 = 60563) (by norm_num)
theorem B6890723 : Blo 2041435 6890723 := bstep (se 1 (by rfl) ⟨5168042, by rfl⟩ : syracuseStep 6890723 = 10336085) B10336085
theorem B4593815 : Blo 2041435 4593815 := bstep (se 1 (by rfl) ⟨3445361, by rfl⟩ : syracuseStep 4593815 = 6890723) B6890723
theorem B3062543 : Blo 2041435 3062543 := bstep (se 1 (by rfl) ⟨2296907, by rfl⟩ : syracuseStep 3062543 = 4593815) B4593815
theorem B2041695 : Blo 2041435 2041695 := bstep (se 1 (by rfl) ⟨1531271, by rfl⟩ : syracuseStep 2041695 = 3062543) B3062543
theorem B3062549 : Blo 2041435 3062549 := bbase (se 6 (by rfl) ⟨71778, by rfl⟩ : syracuseStep 3062549 = 143557) (by norm_num)
theorem B2041699 : Blo 2041435 2041699 := bstep (se 1 (by rfl) ⟨1531274, by rfl⟩ : syracuseStep 2041699 = 3062549) B3062549
theorem B2797061 : Blo 2041435 2797061 := bbase (se 4 (by rfl) ⟨262224, by rfl⟩ : syracuseStep 2797061 = 524449) (by norm_num)
theorem B29835317 : Blo 2041435 29835317 := bstep (se 5 (by rfl) ⟨1398530, by rfl⟩ : syracuseStep 29835317 = 2797061) B2797061
theorem B19890211 : Blo 2041435 19890211 := bstep (se 1 (by rfl) ⟨14917658, by rfl⟩ : syracuseStep 19890211 = 29835317) B29835317
theorem B26520281 : Blo 2041435 26520281 := bstep (se 2 (by rfl) ⟨9945105, by rfl⟩ : syracuseStep 26520281 = 19890211) B19890211
theorem B17680187 : Blo 2041435 17680187 := bstep (se 1 (by rfl) ⟨13260140, by rfl⟩ : syracuseStep 17680187 = 26520281) B26520281
theorem B11786791 : Blo 2041435 11786791 := bstep (se 1 (by rfl) ⟨8840093, by rfl⟩ : syracuseStep 11786791 = 17680187) B17680187
theorem B15715721 : Blo 2041435 15715721 := bstep (se 2 (by rfl) ⟨5893395, by rfl⟩ : syracuseStep 15715721 = 11786791) B11786791
theorem B41908589 : Blo 2041435 41908589 := bstep (se 3 (by rfl) ⟨7857860, by rfl⟩ : syracuseStep 41908589 = 15715721) B15715721
theorem B27939059 : Blo 2041435 27939059 := bstep (se 1 (by rfl) ⟨20954294, by rfl⟩ : syracuseStep 27939059 = 41908589) B41908589
theorem B18626039 : Blo 2041435 18626039 := bstep (se 1 (by rfl) ⟨13969529, by rfl⟩ : syracuseStep 18626039 = 27939059) B27939059
theorem B12417359 : Blo 2041435 12417359 := bstep (se 1 (by rfl) ⟨9313019, by rfl⟩ : syracuseStep 12417359 = 18626039) B18626039
theorem B33112957 : Blo 2041435 33112957 := bstep (se 3 (by rfl) ⟨6208679, by rfl⟩ : syracuseStep 33112957 = 12417359) B12417359
theorem B44150609 : Blo 2041435 44150609 := bstep (se 2 (by rfl) ⟨16556478, by rfl⟩ : syracuseStep 44150609 = 33112957) B33112957
theorem B29433739 : Blo 2041435 29433739 := bstep (se 1 (by rfl) ⟨22075304, by rfl⟩ : syracuseStep 29433739 = 44150609) B44150609
theorem B39244985 : Blo 2041435 39244985 := bstep (se 2 (by rfl) ⟨14716869, by rfl⟩ : syracuseStep 39244985 = 29433739) B29433739
theorem B26163323 : Blo 2041435 26163323 := bstep (se 1 (by rfl) ⟨19622492, by rfl⟩ : syracuseStep 26163323 = 39244985) B39244985
theorem B17442215 : Blo 2041435 17442215 := bstep (se 1 (by rfl) ⟨13081661, by rfl⟩ : syracuseStep 17442215 = 26163323) B26163323
theorem B11628143 : Blo 2041435 11628143 := bstep (se 1 (by rfl) ⟨8721107, by rfl⟩ : syracuseStep 11628143 = 17442215) B17442215
theorem B7752095 : Blo 2041435 7752095 := bstep (se 1 (by rfl) ⟨5814071, by rfl⟩ : syracuseStep 7752095 = 11628143) B11628143
theorem B5168063 : Blo 2041435 5168063 := bstep (se 1 (by rfl) ⟨3876047, by rfl⟩ : syracuseStep 5168063 = 7752095) B7752095
theorem B3445375 : Blo 2041435 3445375 := bstep (se 1 (by rfl) ⟨2584031, by rfl⟩ : syracuseStep 3445375 = 5168063) B5168063
theorem B4593833 : Blo 2041435 4593833 := bstep (se 2 (by rfl) ⟨1722687, by rfl⟩ : syracuseStep 4593833 = 3445375) B3445375
theorem B3062555 : Blo 2041435 3062555 := bstep (se 1 (by rfl) ⟨2296916, by rfl⟩ : syracuseStep 3062555 = 4593833) B4593833
theorem B2041703 : Blo 2041435 2041703 := bstep (se 1 (by rfl) ⟨1531277, by rfl⟩ : syracuseStep 2041703 = 3062555) B3062555
theorem B2296921 : Blo 2041435 2296921 := bbase (se 2 (by rfl) ⟨861345, by rfl⟩ : syracuseStep 2296921 = 1722691) (by norm_num)
theorem B3062561 : Blo 2041435 3062561 := bstep (se 2 (by rfl) ⟨1148460, by rfl⟩ : syracuseStep 3062561 = 2296921) B2296921
theorem B2041707 : Blo 2041435 2041707 := bstep (se 1 (by rfl) ⟨1531280, by rfl⟩ : syracuseStep 2041707 = 3062561) B3062561
theorem B2328265 : Blo 2041435 2328265 := bbase (se 2 (by rfl) ⟨873099, by rfl⟩ : syracuseStep 2328265 = 1746199) (by norm_num)
theorem B3104353 : Blo 2041435 3104353 := bstep (se 2 (by rfl) ⟨1164132, by rfl⟩ : syracuseStep 3104353 = 2328265) B2328265
theorem B4139137 : Blo 2041435 4139137 := bstep (se 2 (by rfl) ⟨1552176, by rfl⟩ : syracuseStep 4139137 = 3104353) B3104353
theorem B5518849 : Blo 2041435 5518849 := bstep (se 2 (by rfl) ⟨2069568, by rfl⟩ : syracuseStep 5518849 = 4139137) B4139137
theorem B7358465 : Blo 2041435 7358465 := bstep (se 2 (by rfl) ⟨2759424, by rfl⟩ : syracuseStep 7358465 = 5518849) B5518849
theorem B4905643 : Blo 2041435 4905643 := bstep (se 1 (by rfl) ⟨3679232, by rfl⟩ : syracuseStep 4905643 = 7358465) B7358465
theorem B6540857 : Blo 2041435 6540857 := bstep (se 2 (by rfl) ⟨2452821, by rfl⟩ : syracuseStep 6540857 = 4905643) B4905643
theorem B4360571 : Blo 2041435 4360571 := bstep (se 1 (by rfl) ⟨3270428, by rfl⟩ : syracuseStep 4360571 = 6540857) B6540857
theorem B2907047 : Blo 2041435 2907047 := bstep (se 1 (by rfl) ⟨2180285, by rfl⟩ : syracuseStep 2907047 = 4360571) B4360571
theorem B7752125 : Blo 2041435 7752125 := bstep (se 3 (by rfl) ⟨1453523, by rfl⟩ : syracuseStep 7752125 = 2907047) B2907047
theorem B5168083 : Blo 2041435 5168083 := bstep (se 1 (by rfl) ⟨3876062, by rfl⟩ : syracuseStep 5168083 = 7752125) B7752125
theorem B6890777 : Blo 2041435 6890777 := bstep (se 2 (by rfl) ⟨2584041, by rfl⟩ : syracuseStep 6890777 = 5168083) B5168083
theorem B4593851 : Blo 2041435 4593851 := bstep (se 1 (by rfl) ⟨3445388, by rfl⟩ : syracuseStep 4593851 = 6890777) B6890777
theorem B3062567 : Blo 2041435 3062567 := bstep (se 1 (by rfl) ⟨2296925, by rfl⟩ : syracuseStep 3062567 = 4593851) B4593851
theorem B2041711 : Blo 2041435 2041711 := bstep (se 1 (by rfl) ⟨1531283, by rfl⟩ : syracuseStep 2041711 = 3062567) B3062567
theorem B3062573 : Blo 2041435 3062573 := bbase (se 3 (by rfl) ⟨574232, by rfl⟩ : syracuseStep 3062573 = 1148465) (by norm_num)
theorem B2041715 : Blo 2041435 2041715 := bstep (se 1 (by rfl) ⟨1531286, by rfl⟩ : syracuseStep 2041715 = 3062573) B3062573
theorem B4593869 : Blo 2041435 4593869 := bbase (se 3 (by rfl) ⟨861350, by rfl⟩ : syracuseStep 4593869 = 1722701) (by norm_num)
theorem B3062579 : Blo 2041435 3062579 := bstep (se 1 (by rfl) ⟨2296934, by rfl⟩ : syracuseStep 3062579 = 4593869) B4593869
theorem B2041719 : Blo 2041435 2041719 := bstep (se 1 (by rfl) ⟨1531289, by rfl⟩ : syracuseStep 2041719 = 3062579) B3062579
theorem B2584057 : Blo 2041435 2584057 := bbase (se 2 (by rfl) ⟨969021, by rfl⟩ : syracuseStep 2584057 = 1938043) (by norm_num)
theorem B3445409 : Blo 2041435 3445409 := bstep (se 2 (by rfl) ⟨1292028, by rfl⟩ : syracuseStep 3445409 = 2584057) B2584057
theorem B2296939 : Blo 2041435 2296939 := bstep (se 1 (by rfl) ⟨1722704, by rfl⟩ : syracuseStep 2296939 = 3445409) B3445409
theorem B3062585 : Blo 2041435 3062585 := bstep (se 2 (by rfl) ⟨1148469, by rfl⟩ : syracuseStep 3062585 = 2296939) B2296939
theorem B2041723 : Blo 2041435 2041723 := bstep (se 1 (by rfl) ⟨1531292, by rfl⟩ : syracuseStep 2041723 = 3062585) B3062585
theorem B4656565 : Blo 2041435 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B6208753 : Blo 2041435 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B8278337 : Blo 2041435 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B5518891 : Blo 2041435 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B7358521 : Blo 2041435 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B9811361 : Blo 2041435 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B6540907 : Blo 2041435 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B8721209 : Blo 2041435 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B23256557 : Blo 2041435 23256557 := bstep (se 3 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 23256557 = 8721209) B8721209
theorem B15504371 : Blo 2041435 15504371 := bstep (se 1 (by rfl) ⟨11628278, by rfl⟩ : syracuseStep 15504371 = 23256557) B23256557
theorem B10336247 : Blo 2041435 10336247 := bstep (se 1 (by rfl) ⟨7752185, by rfl⟩ : syracuseStep 10336247 = 15504371) B15504371
theorem B6890831 : Blo 2041435 6890831 := bstep (se 1 (by rfl) ⟨5168123, by rfl⟩ : syracuseStep 6890831 = 10336247) B10336247
theorem B4593887 : Blo 2041435 4593887 := bstep (se 1 (by rfl) ⟨3445415, by rfl⟩ : syracuseStep 4593887 = 6890831) B6890831
theorem B3062591 : Blo 2041435 3062591 := bstep (se 1 (by rfl) ⟨2296943, by rfl⟩ : syracuseStep 3062591 = 4593887) B4593887
theorem B2041727 : Blo 2041435 2041727 := bstep (se 1 (by rfl) ⟨1531295, by rfl⟩ : syracuseStep 2041727 = 3062591) B3062591
theorem B3062597 : Blo 2041435 3062597 := bbase (se 4 (by rfl) ⟨287118, by rfl⟩ : syracuseStep 3062597 = 574237) (by norm_num)
theorem B2041731 : Blo 2041435 2041731 := bstep (se 1 (by rfl) ⟨1531298, by rfl⟩ : syracuseStep 2041731 = 3062597) B3062597
theorem B3445429 : Blo 2041435 3445429 := bbase (se 5 (by rfl) ⟨161504, by rfl⟩ : syracuseStep 3445429 = 323009) (by norm_num)
theorem B4593905 : Blo 2041435 4593905 := bstep (se 2 (by rfl) ⟨1722714, by rfl⟩ : syracuseStep 4593905 = 3445429) B3445429
theorem B3062603 : Blo 2041435 3062603 := bstep (se 1 (by rfl) ⟨2296952, by rfl⟩ : syracuseStep 3062603 = 4593905) B4593905
theorem B2041735 : Blo 2041435 2041735 := bstep (se 1 (by rfl) ⟨1531301, by rfl⟩ : syracuseStep 2041735 = 3062603) B3062603
theorem B2296957 : Blo 2041435 2296957 := bbase (se 3 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 2296957 = 861359) (by norm_num)
theorem B3062609 : Blo 2041435 3062609 := bstep (se 2 (by rfl) ⟨1148478, by rfl⟩ : syracuseStep 3062609 = 2296957) B2296957
theorem B2041739 : Blo 2041435 2041739 := bstep (se 1 (by rfl) ⟨1531304, by rfl⟩ : syracuseStep 2041739 = 3062609) B3062609
theorem B6890885 : Blo 2041435 6890885 := bbase (se 4 (by rfl) ⟨646020, by rfl⟩ : syracuseStep 6890885 = 1292041) (by norm_num)
theorem B4593923 : Blo 2041435 4593923 := bstep (se 1 (by rfl) ⟨3445442, by rfl⟩ : syracuseStep 4593923 = 6890885) B6890885
theorem B3062615 : Blo 2041435 3062615 := bstep (se 1 (by rfl) ⟨2296961, by rfl⟩ : syracuseStep 3062615 = 4593923) B4593923
theorem B2041743 : Blo 2041435 2041743 := bstep (se 1 (by rfl) ⟨1531307, by rfl⟩ : syracuseStep 2041743 = 3062615) B3062615
theorem B3062621 : Blo 2041435 3062621 := bbase (se 3 (by rfl) ⟨574241, by rfl⟩ : syracuseStep 3062621 = 1148483) (by norm_num)
theorem B2041747 : Blo 2041435 2041747 := bstep (se 1 (by rfl) ⟨1531310, by rfl⟩ : syracuseStep 2041747 = 3062621) B3062621
theorem B4593941 : Blo 2041435 4593941 := bbase (se 6 (by rfl) ⟨107670, by rfl⟩ : syracuseStep 4593941 = 215341) (by norm_num)
theorem B3062627 : Blo 2041435 3062627 := bstep (se 1 (by rfl) ⟨2296970, by rfl⟩ : syracuseStep 3062627 = 4593941) B4593941
theorem B2041751 : Blo 2041435 2041751 := bstep (se 1 (by rfl) ⟨1531313, by rfl⟩ : syracuseStep 2041751 = 3062627) B3062627
theorem B7752293 : Blo 2041435 7752293 := bbase (se 4 (by rfl) ⟨726777, by rfl⟩ : syracuseStep 7752293 = 1453555) (by norm_num)
theorem B5168195 : Blo 2041435 5168195 := bstep (se 1 (by rfl) ⟨3876146, by rfl⟩ : syracuseStep 5168195 = 7752293) B7752293
theorem B3445463 : Blo 2041435 3445463 := bstep (se 1 (by rfl) ⟨2584097, by rfl⟩ : syracuseStep 3445463 = 5168195) B5168195
theorem B2296975 : Blo 2041435 2296975 := bstep (se 1 (by rfl) ⟨1722731, by rfl⟩ : syracuseStep 2296975 = 3445463) B3445463
theorem B3062633 : Blo 2041435 3062633 := bstep (se 2 (by rfl) ⟨1148487, by rfl⟩ : syracuseStep 3062633 = 2296975) B2296975
theorem B2041755 : Blo 2041435 2041755 := bstep (se 1 (by rfl) ⟨1531316, by rfl⟩ : syracuseStep 2041755 = 3062633) B3062633
theorem B8278469 : Blo 2041435 8278469 := bbase (se 4 (by rfl) ⟨776106, by rfl⟩ : syracuseStep 8278469 = 1552213) (by norm_num)
theorem B5518979 : Blo 2041435 5518979 := bstep (se 1 (by rfl) ⟨4139234, by rfl⟩ : syracuseStep 5518979 = 8278469) B8278469
theorem B3679319 : Blo 2041435 3679319 := bstep (se 1 (by rfl) ⟨2759489, by rfl⟩ : syracuseStep 3679319 = 5518979) B5518979
theorem B2452879 : Blo 2041435 2452879 := bstep (se 1 (by rfl) ⟨1839659, by rfl⟩ : syracuseStep 2452879 = 3679319) B3679319
theorem B3270505 : Blo 2041435 3270505 := bstep (se 2 (by rfl) ⟨1226439, by rfl⟩ : syracuseStep 3270505 = 2452879) B2452879
theorem B4360673 : Blo 2041435 4360673 := bstep (se 2 (by rfl) ⟨1635252, by rfl⟩ : syracuseStep 4360673 = 3270505) B3270505
theorem B11628461 : Blo 2041435 11628461 := bstep (se 3 (by rfl) ⟨2180336, by rfl⟩ : syracuseStep 11628461 = 4360673) B4360673
theorem B7752307 : Blo 2041435 7752307 := bstep (se 1 (by rfl) ⟨5814230, by rfl⟩ : syracuseStep 7752307 = 11628461) B11628461
theorem B10336409 : Blo 2041435 10336409 := bstep (se 2 (by rfl) ⟨3876153, by rfl⟩ : syracuseStep 10336409 = 7752307) B7752307
theorem B6890939 : Blo 2041435 6890939 := bstep (se 1 (by rfl) ⟨5168204, by rfl⟩ : syracuseStep 6890939 = 10336409) B10336409
theorem B4593959 : Blo 2041435 4593959 := bstep (se 1 (by rfl) ⟨3445469, by rfl⟩ : syracuseStep 4593959 = 6890939) B6890939
theorem B3062639 : Blo 2041435 3062639 := bstep (se 1 (by rfl) ⟨2296979, by rfl⟩ : syracuseStep 3062639 = 4593959) B4593959
theorem B2041759 : Blo 2041435 2041759 := bstep (se 1 (by rfl) ⟨1531319, by rfl⟩ : syracuseStep 2041759 = 3062639) B3062639
theorem B3062645 : Blo 2041435 3062645 := bbase (se 5 (by rfl) ⟨143561, by rfl⟩ : syracuseStep 3062645 = 287123) (by norm_num)
theorem B2041763 : Blo 2041435 2041763 := bstep (se 1 (by rfl) ⟨1531322, by rfl⟩ : syracuseStep 2041763 = 3062645) B3062645
theorem B2452889 : Blo 2041435 2452889 := bbase (se 2 (by rfl) ⟨919833, by rfl⟩ : syracuseStep 2452889 = 1839667) (by norm_num)
theorem B6541037 : Blo 2041435 6541037 := bstep (se 3 (by rfl) ⟨1226444, by rfl⟩ : syracuseStep 6541037 = 2452889) B2452889
theorem B4360691 : Blo 2041435 4360691 := bstep (se 1 (by rfl) ⟨3270518, by rfl⟩ : syracuseStep 4360691 = 6541037) B6541037
theorem B2907127 : Blo 2041435 2907127 := bstep (se 1 (by rfl) ⟨2180345, by rfl⟩ : syracuseStep 2907127 = 4360691) B4360691
theorem B3876169 : Blo 2041435 3876169 := bstep (se 2 (by rfl) ⟨1453563, by rfl⟩ : syracuseStep 3876169 = 2907127) B2907127
theorem B5168225 : Blo 2041435 5168225 := bstep (se 2 (by rfl) ⟨1938084, by rfl⟩ : syracuseStep 5168225 = 3876169) B3876169
theorem B3445483 : Blo 2041435 3445483 := bstep (se 1 (by rfl) ⟨2584112, by rfl⟩ : syracuseStep 3445483 = 5168225) B5168225
theorem B4593977 : Blo 2041435 4593977 := bstep (se 2 (by rfl) ⟨1722741, by rfl⟩ : syracuseStep 4593977 = 3445483) B3445483
theorem B3062651 : Blo 2041435 3062651 := bstep (se 1 (by rfl) ⟨2296988, by rfl⟩ : syracuseStep 3062651 = 4593977) B4593977
theorem B2041767 : Blo 2041435 2041767 := bstep (se 1 (by rfl) ⟨1531325, by rfl⟩ : syracuseStep 2041767 = 3062651) B3062651
theorem B2296993 : Blo 2041435 2296993 := bbase (se 2 (by rfl) ⟨861372, by rfl⟩ : syracuseStep 2296993 = 1722745) (by norm_num)
theorem B3062657 : Blo 2041435 3062657 := bstep (se 2 (by rfl) ⟨1148496, by rfl⟩ : syracuseStep 3062657 = 2296993) B2296993
theorem B2041771 : Blo 2041435 2041771 := bstep (se 1 (by rfl) ⟨1531328, by rfl⟩ : syracuseStep 2041771 = 3062657) B3062657
theorem B5168245 : Blo 2041435 5168245 := bbase (se 5 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 5168245 = 484523) (by norm_num)
theorem B6890993 : Blo 2041435 6890993 := bstep (se 2 (by rfl) ⟨2584122, by rfl⟩ : syracuseStep 6890993 = 5168245) B5168245
theorem B4593995 : Blo 2041435 4593995 := bstep (se 1 (by rfl) ⟨3445496, by rfl⟩ : syracuseStep 4593995 = 6890993) B6890993
theorem B3062663 : Blo 2041435 3062663 := bstep (se 1 (by rfl) ⟨2296997, by rfl⟩ : syracuseStep 3062663 = 4593995) B4593995
theorem B2041775 : Blo 2041435 2041775 := bstep (se 1 (by rfl) ⟨1531331, by rfl⟩ : syracuseStep 2041775 = 3062663) B3062663
theorem B3062669 : Blo 2041435 3062669 := bbase (se 3 (by rfl) ⟨574250, by rfl⟩ : syracuseStep 3062669 = 1148501) (by norm_num)
theorem B2041779 : Blo 2041435 2041779 := bstep (se 1 (by rfl) ⟨1531334, by rfl⟩ : syracuseStep 2041779 = 3062669) B3062669
theorem B4594013 : Blo 2041435 4594013 := bbase (se 3 (by rfl) ⟨861377, by rfl⟩ : syracuseStep 4594013 = 1722755) (by norm_num)
theorem B3062675 : Blo 2041435 3062675 := bstep (se 1 (by rfl) ⟨2297006, by rfl⟩ : syracuseStep 3062675 = 4594013) B4594013
theorem B2041783 : Blo 2041435 2041783 := bstep (se 1 (by rfl) ⟨1531337, by rfl⟩ : syracuseStep 2041783 = 3062675) B3062675
theorem B3445517 : Blo 2041435 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2297011 : Blo 2041435 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B3062681 : Blo 2041435 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2041787 : Blo 2041435 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B17442965 : Blo 2041435 17442965 := bbase (se 6 (by rfl) ⟨408819, by rfl⟩ : syracuseStep 17442965 = 817639) (by norm_num)
theorem B11628643 : Blo 2041435 11628643 := bstep (se 1 (by rfl) ⟨8721482, by rfl⟩ : syracuseStep 11628643 = 17442965) B17442965
theorem B15504857 : Blo 2041435 15504857 := bstep (se 2 (by rfl) ⟨5814321, by rfl⟩ : syracuseStep 15504857 = 11628643) B11628643
theorem B10336571 : Blo 2041435 10336571 := bstep (se 1 (by rfl) ⟨7752428, by rfl⟩ : syracuseStep 10336571 = 15504857) B15504857
theorem B6891047 : Blo 2041435 6891047 := bstep (se 1 (by rfl) ⟨5168285, by rfl⟩ : syracuseStep 6891047 = 10336571) B10336571
theorem B4594031 : Blo 2041435 4594031 := bstep (se 1 (by rfl) ⟨3445523, by rfl⟩ : syracuseStep 4594031 = 6891047) B6891047
theorem B3062687 : Blo 2041435 3062687 := bstep (se 1 (by rfl) ⟨2297015, by rfl⟩ : syracuseStep 3062687 = 4594031) B4594031
theorem B2041791 : Blo 2041435 2041791 := bstep (se 1 (by rfl) ⟨1531343, by rfl⟩ : syracuseStep 2041791 = 3062687) B3062687
theorem B3062693 : Blo 2041435 3062693 := bbase (se 4 (by rfl) ⟨287127, by rfl⟩ : syracuseStep 3062693 = 574255) (by norm_num)
theorem B2041795 : Blo 2041435 2041795 := bstep (se 1 (by rfl) ⟨1531346, by rfl⟩ : syracuseStep 2041795 = 3062693) B3062693
theorem B2584153 : Blo 2041435 2584153 := bbase (se 2 (by rfl) ⟨969057, by rfl⟩ : syracuseStep 2584153 = 1938115) (by norm_num)
theorem B3445537 : Blo 2041435 3445537 := bstep (se 2 (by rfl) ⟨1292076, by rfl⟩ : syracuseStep 3445537 = 2584153) B2584153
theorem B4594049 : Blo 2041435 4594049 := bstep (se 2 (by rfl) ⟨1722768, by rfl⟩ : syracuseStep 4594049 = 3445537) B3445537
theorem B3062699 : Blo 2041435 3062699 := bstep (se 1 (by rfl) ⟨2297024, by rfl⟩ : syracuseStep 3062699 = 4594049) B4594049
theorem B2041799 : Blo 2041435 2041799 := bstep (se 1 (by rfl) ⟨1531349, by rfl⟩ : syracuseStep 2041799 = 3062699) B3062699
theorem B2297029 : Blo 2041435 2297029 := bbase (se 4 (by rfl) ⟨215346, by rfl⟩ : syracuseStep 2297029 = 430693) (by norm_num)
theorem B3062705 : Blo 2041435 3062705 := bstep (se 2 (by rfl) ⟨1148514, by rfl⟩ : syracuseStep 3062705 = 2297029) B2297029
theorem B2041803 : Blo 2041435 2041803 := bstep (se 1 (by rfl) ⟨1531352, by rfl⟩ : syracuseStep 2041803 = 3062705) B3062705
theorem B3876245 : Blo 2041435 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B2584163 : Blo 2041435 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B6891101 : Blo 2041435 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B4594067 : Blo 2041435 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B3062711 : Blo 2041435 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B2041807 : Blo 2041435 2041807 := bstep (se 1 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 2041807 = 3062711) B3062711
theorem B3062717 : Blo 2041435 3062717 := bbase (se 3 (by rfl) ⟨574259, by rfl⟩ : syracuseStep 3062717 = 1148519) (by norm_num)
theorem B2041811 : Blo 2041435 2041811 := bstep (se 1 (by rfl) ⟨1531358, by rfl⟩ : syracuseStep 2041811 = 3062717) B3062717
theorem B4594085 : Blo 2041435 4594085 := bbase (se 4 (by rfl) ⟨430695, by rfl⟩ : syracuseStep 4594085 = 861391) (by norm_num)
theorem B3062723 : Blo 2041435 3062723 := bstep (se 1 (by rfl) ⟨2297042, by rfl⟩ : syracuseStep 3062723 = 4594085) B4594085
theorem B2041815 : Blo 2041435 2041815 := bstep (se 1 (by rfl) ⟨1531361, by rfl⟩ : syracuseStep 2041815 = 3062723) B3062723
theorem B5168357 : Blo 2041435 5168357 := bbase (se 4 (by rfl) ⟨484533, by rfl⟩ : syracuseStep 5168357 = 969067) (by norm_num)
theorem B3445571 : Blo 2041435 3445571 := bstep (se 1 (by rfl) ⟨2584178, by rfl⟩ : syracuseStep 3445571 = 5168357) B5168357
theorem B2297047 : Blo 2041435 2297047 := bstep (se 1 (by rfl) ⟨1722785, by rfl⟩ : syracuseStep 2297047 = 3445571) B3445571
theorem B3062729 : Blo 2041435 3062729 := bstep (se 2 (by rfl) ⟨1148523, by rfl⟩ : syracuseStep 3062729 = 2297047) B2297047
theorem B2041819 : Blo 2041435 2041819 := bstep (se 1 (by rfl) ⟨1531364, by rfl⟩ : syracuseStep 2041819 = 3062729) B3062729
theorem B2180405 : Blo 2041435 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B5814413 : Blo 2041435 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B3876275 : Blo 2041435 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B10336733 : Blo 2041435 10336733 := bstep (se 3 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 10336733 = 3876275) B3876275
theorem B6891155 : Blo 2041435 6891155 := bstep (se 1 (by rfl) ⟨5168366, by rfl⟩ : syracuseStep 6891155 = 10336733) B10336733
theorem B4594103 : Blo 2041435 4594103 := bstep (se 1 (by rfl) ⟨3445577, by rfl⟩ : syracuseStep 4594103 = 6891155) B6891155
theorem B3062735 : Blo 2041435 3062735 := bstep (se 1 (by rfl) ⟨2297051, by rfl⟩ : syracuseStep 3062735 = 4594103) B4594103
theorem B2041823 : Blo 2041435 2041823 := bstep (se 1 (by rfl) ⟨1531367, by rfl⟩ : syracuseStep 2041823 = 3062735) B3062735
theorem B3062741 : Blo 2041435 3062741 := bbase (se 7 (by rfl) ⟨35891, by rfl⟩ : syracuseStep 3062741 = 71783) (by norm_num)
theorem B2041827 : Blo 2041435 2041827 := bstep (se 1 (by rfl) ⟨1531370, by rfl⟩ : syracuseStep 2041827 = 3062741) B3062741
theorem B7752581 : Blo 2041435 7752581 := bbase (se 4 (by rfl) ⟨726804, by rfl⟩ : syracuseStep 7752581 = 1453609) (by norm_num)
theorem B5168387 : Blo 2041435 5168387 := bstep (se 1 (by rfl) ⟨3876290, by rfl⟩ : syracuseStep 5168387 = 7752581) B7752581
theorem B3445591 : Blo 2041435 3445591 := bstep (se 1 (by rfl) ⟨2584193, by rfl⟩ : syracuseStep 3445591 = 5168387) B5168387
theorem B4594121 : Blo 2041435 4594121 := bstep (se 2 (by rfl) ⟨1722795, by rfl⟩ : syracuseStep 4594121 = 3445591) B3445591
theorem B3062747 : Blo 2041435 3062747 := bstep (se 1 (by rfl) ⟨2297060, by rfl⟩ : syracuseStep 3062747 = 4594121) B4594121
theorem B2041831 : Blo 2041435 2041831 := bstep (se 1 (by rfl) ⟨1531373, by rfl⟩ : syracuseStep 2041831 = 3062747) B3062747
theorem B2297065 : Blo 2041435 2297065 := bbase (se 2 (by rfl) ⟨861399, by rfl⟩ : syracuseStep 2297065 = 1722799) (by norm_num)
theorem B3062753 : Blo 2041435 3062753 := bstep (se 2 (by rfl) ⟨1148532, by rfl⟩ : syracuseStep 3062753 = 2297065) B2297065
theorem B2041835 : Blo 2041435 2041835 := bstep (se 1 (by rfl) ⟨1531376, by rfl⟩ : syracuseStep 2041835 = 3062753) B3062753
theorem B11628917 : Blo 2041435 11628917 := bbase (se 5 (by rfl) ⟨545105, by rfl⟩ : syracuseStep 11628917 = 1090211) (by norm_num)
theorem B7752611 : Blo 2041435 7752611 := bstep (se 1 (by rfl) ⟨5814458, by rfl⟩ : syracuseStep 7752611 = 11628917) B11628917
theorem B5168407 : Blo 2041435 5168407 := bstep (se 1 (by rfl) ⟨3876305, by rfl⟩ : syracuseStep 5168407 = 7752611) B7752611
theorem B6891209 : Blo 2041435 6891209 := bstep (se 2 (by rfl) ⟨2584203, by rfl⟩ : syracuseStep 6891209 = 5168407) B5168407
theorem B4594139 : Blo 2041435 4594139 := bstep (se 1 (by rfl) ⟨3445604, by rfl⟩ : syracuseStep 4594139 = 6891209) B6891209
theorem B3062759 : Blo 2041435 3062759 := bstep (se 1 (by rfl) ⟨2297069, by rfl⟩ : syracuseStep 3062759 = 4594139) B4594139
theorem B2041839 : Blo 2041435 2041839 := bstep (se 1 (by rfl) ⟨1531379, by rfl⟩ : syracuseStep 2041839 = 3062759) B3062759
theorem B3062765 : Blo 2041435 3062765 := bbase (se 3 (by rfl) ⟨574268, by rfl⟩ : syracuseStep 3062765 = 1148537) (by norm_num)
theorem B2041843 : Blo 2041435 2041843 := bstep (se 1 (by rfl) ⟨1531382, by rfl⟩ : syracuseStep 2041843 = 3062765) B3062765
theorem B4594157 : Blo 2041435 4594157 := bbase (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) (by norm_num)
theorem B3062771 : Blo 2041435 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B2041847 : Blo 2041435 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B13970549 : Blo 2041435 13970549 := bbase (se 5 (by rfl) ⟨654869, by rfl⟩ : syracuseStep 13970549 = 1309739) (by norm_num)
theorem B9313699 : Blo 2041435 9313699 := bstep (se 1 (by rfl) ⟨6985274, by rfl⟩ : syracuseStep 9313699 = 13970549) B13970549
theorem B12418265 : Blo 2041435 12418265 := bstep (se 2 (by rfl) ⟨4656849, by rfl⟩ : syracuseStep 12418265 = 9313699) B9313699
theorem B8278843 : Blo 2041435 8278843 := bstep (se 1 (by rfl) ⟨6209132, by rfl⟩ : syracuseStep 8278843 = 12418265) B12418265
theorem B11038457 : Blo 2041435 11038457 := bstep (se 2 (by rfl) ⟨4139421, by rfl⟩ : syracuseStep 11038457 = 8278843) B8278843
theorem B7358971 : Blo 2041435 7358971 := bstep (se 1 (by rfl) ⟨5519228, by rfl⟩ : syracuseStep 7358971 = 11038457) B11038457
theorem B9811961 : Blo 2041435 9811961 := bstep (se 2 (by rfl) ⟨3679485, by rfl⟩ : syracuseStep 9811961 = 7358971) B7358971
theorem B6541307 : Blo 2041435 6541307 := bstep (se 1 (by rfl) ⟨4905980, by rfl⟩ : syracuseStep 6541307 = 9811961) B9811961
theorem B4360871 : Blo 2041435 4360871 := bstep (se 1 (by rfl) ⟨3270653, by rfl⟩ : syracuseStep 4360871 = 6541307) B6541307
theorem B2907247 : Blo 2041435 2907247 := bstep (se 1 (by rfl) ⟨2180435, by rfl⟩ : syracuseStep 2907247 = 4360871) B4360871
theorem B3876329 : Blo 2041435 3876329 := bstep (se 2 (by rfl) ⟨1453623, by rfl⟩ : syracuseStep 3876329 = 2907247) B2907247
theorem B2584219 : Blo 2041435 2584219 := bstep (se 1 (by rfl) ⟨1938164, by rfl⟩ : syracuseStep 2584219 = 3876329) B3876329
theorem B3445625 : Blo 2041435 3445625 := bstep (se 2 (by rfl) ⟨1292109, by rfl⟩ : syracuseStep 3445625 = 2584219) B2584219
theorem B2297083 : Blo 2041435 2297083 := bstep (se 1 (by rfl) ⟨1722812, by rfl⟩ : syracuseStep 2297083 = 3445625) B3445625
theorem B3062777 : Blo 2041435 3062777 := bstep (se 2 (by rfl) ⟨1148541, by rfl⟩ : syracuseStep 3062777 = 2297083) B2297083
theorem B2041851 : Blo 2041435 2041851 := bstep (se 1 (by rfl) ⟨1531388, by rfl⟩ : syracuseStep 2041851 = 3062777) B3062777
theorem B9945845 : Blo 2041435 9945845 := bbase (se 5 (by rfl) ⟨466211, by rfl⟩ : syracuseStep 9945845 = 932423) (by norm_num)
theorem B6630563 : Blo 2041435 6630563 := bstep (se 1 (by rfl) ⟨4972922, by rfl⟩ : syracuseStep 6630563 = 9945845) B9945845
theorem B4420375 : Blo 2041435 4420375 := bstep (se 1 (by rfl) ⟨3315281, by rfl⟩ : syracuseStep 4420375 = 6630563) B6630563
theorem B23575333 : Blo 2041435 23575333 := bstep (se 4 (by rfl) ⟨2210187, by rfl⟩ : syracuseStep 23575333 = 4420375) B4420375
theorem B31433777 : Blo 2041435 31433777 := bstep (se 2 (by rfl) ⟨11787666, by rfl⟩ : syracuseStep 31433777 = 23575333) B23575333
theorem B20955851 : Blo 2041435 20955851 := bstep (se 1 (by rfl) ⟨15716888, by rfl⟩ : syracuseStep 20955851 = 31433777) B31433777
theorem B13970567 : Blo 2041435 13970567 := bstep (se 1 (by rfl) ⟨10477925, by rfl⟩ : syracuseStep 13970567 = 20955851) B20955851
theorem B37254845 : Blo 2041435 37254845 := bstep (se 3 (by rfl) ⟨6985283, by rfl⟩ : syracuseStep 37254845 = 13970567) B13970567
theorem B24836563 : Blo 2041435 24836563 := bstep (se 1 (by rfl) ⟨18627422, by rfl⟩ : syracuseStep 24836563 = 37254845) B37254845
theorem B132461669 : Blo 2041435 132461669 := bstep (se 4 (by rfl) ⟨12418281, by rfl⟩ : syracuseStep 132461669 = 24836563) B24836563
theorem B88307779 : Blo 2041435 88307779 := bstep (se 1 (by rfl) ⟨66230834, by rfl⟩ : syracuseStep 88307779 = 132461669) B132461669
theorem B117743705 : Blo 2041435 117743705 := bstep (se 2 (by rfl) ⟨44153889, by rfl⟩ : syracuseStep 117743705 = 88307779) B88307779
theorem B78495803 : Blo 2041435 78495803 := bstep (se 1 (by rfl) ⟨58871852, by rfl⟩ : syracuseStep 78495803 = 117743705) B117743705
theorem B52330535 : Blo 2041435 52330535 := bstep (se 1 (by rfl) ⟨39247901, by rfl⟩ : syracuseStep 52330535 = 78495803) B78495803
theorem B34887023 : Blo 2041435 34887023 := bstep (se 1 (by rfl) ⟨26165267, by rfl⟩ : syracuseStep 34887023 = 52330535) B52330535
theorem B23258015 : Blo 2041435 23258015 := bstep (se 1 (by rfl) ⟨17443511, by rfl⟩ : syracuseStep 23258015 = 34887023) B34887023
theorem B15505343 : Blo 2041435 15505343 := bstep (se 1 (by rfl) ⟨11629007, by rfl⟩ : syracuseStep 15505343 = 23258015) B23258015
theorem B10336895 : Blo 2041435 10336895 := bstep (se 1 (by rfl) ⟨7752671, by rfl⟩ : syracuseStep 10336895 = 15505343) B15505343
theorem B6891263 : Blo 2041435 6891263 := bstep (se 1 (by rfl) ⟨5168447, by rfl⟩ : syracuseStep 6891263 = 10336895) B10336895
theorem B4594175 : Blo 2041435 4594175 := bstep (se 1 (by rfl) ⟨3445631, by rfl⟩ : syracuseStep 4594175 = 6891263) B6891263
theorem B3062783 : Blo 2041435 3062783 := bstep (se 1 (by rfl) ⟨2297087, by rfl⟩ : syracuseStep 3062783 = 4594175) B4594175
theorem B2041855 : Blo 2041435 2041855 := bstep (se 1 (by rfl) ⟨1531391, by rfl⟩ : syracuseStep 2041855 = 3062783) B3062783
theorem B3062789 : Blo 2041435 3062789 := bbase (se 4 (by rfl) ⟨287136, by rfl⟩ : syracuseStep 3062789 = 574273) (by norm_num)
theorem B2041859 : Blo 2041435 2041859 := bstep (se 1 (by rfl) ⟨1531394, by rfl⟩ : syracuseStep 2041859 = 3062789) B3062789
theorem B3445645 : Blo 2041435 3445645 := bbase (se 3 (by rfl) ⟨646058, by rfl⟩ : syracuseStep 3445645 = 1292117) (by norm_num)
theorem B4594193 : Blo 2041435 4594193 := bstep (se 2 (by rfl) ⟨1722822, by rfl⟩ : syracuseStep 4594193 = 3445645) B3445645
theorem B3062795 : Blo 2041435 3062795 := bstep (se 1 (by rfl) ⟨2297096, by rfl⟩ : syracuseStep 3062795 = 4594193) B4594193
theorem B2041863 : Blo 2041435 2041863 := bstep (se 1 (by rfl) ⟨1531397, by rfl⟩ : syracuseStep 2041863 = 3062795) B3062795
theorem B2297101 : Blo 2041435 2297101 := bbase (se 3 (by rfl) ⟨430706, by rfl⟩ : syracuseStep 2297101 = 861413) (by norm_num)
theorem B3062801 : Blo 2041435 3062801 := bstep (se 2 (by rfl) ⟨1148550, by rfl⟩ : syracuseStep 3062801 = 2297101) B2297101
theorem B2041867 : Blo 2041435 2041867 := bstep (se 1 (by rfl) ⟨1531400, by rfl⟩ : syracuseStep 2041867 = 3062801) B3062801
theorem B6891317 : Blo 2041435 6891317 := bbase (se 5 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 6891317 = 646061) (by norm_num)
theorem B4594211 : Blo 2041435 4594211 := bstep (se 1 (by rfl) ⟨3445658, by rfl⟩ : syracuseStep 4594211 = 6891317) B6891317
theorem B3062807 : Blo 2041435 3062807 := bstep (se 1 (by rfl) ⟨2297105, by rfl⟩ : syracuseStep 3062807 = 4594211) B4594211
theorem B2041871 : Blo 2041435 2041871 := bstep (se 1 (by rfl) ⟨1531403, by rfl⟩ : syracuseStep 2041871 = 3062807) B3062807
theorem B3062813 : Blo 2041435 3062813 := bbase (se 3 (by rfl) ⟨574277, by rfl⟩ : syracuseStep 3062813 = 1148555) (by norm_num)
theorem B2041875 : Blo 2041435 2041875 := bstep (se 1 (by rfl) ⟨1531406, by rfl⟩ : syracuseStep 2041875 = 3062813) B3062813
theorem B4594229 : Blo 2041435 4594229 := bbase (se 5 (by rfl) ⟨215354, by rfl⟩ : syracuseStep 4594229 = 430709) (by norm_num)
theorem B3062819 : Blo 2041435 3062819 := bstep (se 1 (by rfl) ⟨2297114, by rfl⟩ : syracuseStep 3062819 = 4594229) B4594229
theorem B2041879 : Blo 2041435 2041879 := bstep (se 1 (by rfl) ⟨1531409, by rfl⟩ : syracuseStep 2041879 = 3062819) B3062819
theorem B8721877 : Blo 2041435 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B11629169 : Blo 2041435 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B7752779 : Blo 2041435 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B5168519 : Blo 2041435 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B3445679 : Blo 2041435 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B2297119 : Blo 2041435 2297119 := bstep (se 1 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 2297119 = 3445679) B3445679
theorem B3062825 : Blo 2041435 3062825 := bstep (se 2 (by rfl) ⟨1148559, by rfl⟩ : syracuseStep 3062825 = 2297119) B2297119
theorem B2041883 : Blo 2041435 2041883 := bstep (se 1 (by rfl) ⟨1531412, by rfl⟩ : syracuseStep 2041883 = 3062825) B3062825
theorem B8721893 : Blo 2041435 8721893 := bbase (se 4 (by rfl) ⟨817677, by rfl⟩ : syracuseStep 8721893 = 1635355) (by norm_num)
theorem B5814595 : Blo 2041435 5814595 := bstep (se 1 (by rfl) ⟨4360946, by rfl⟩ : syracuseStep 5814595 = 8721893) B8721893
theorem B7752793 : Blo 2041435 7752793 := bstep (se 2 (by rfl) ⟨2907297, by rfl⟩ : syracuseStep 7752793 = 5814595) B5814595
theorem B10337057 : Blo 2041435 10337057 := bstep (se 2 (by rfl) ⟨3876396, by rfl⟩ : syracuseStep 10337057 = 7752793) B7752793
theorem B6891371 : Blo 2041435 6891371 := bstep (se 1 (by rfl) ⟨5168528, by rfl⟩ : syracuseStep 6891371 = 10337057) B10337057
theorem B4594247 : Blo 2041435 4594247 := bstep (se 1 (by rfl) ⟨3445685, by rfl⟩ : syracuseStep 4594247 = 6891371) B6891371
theorem B3062831 : Blo 2041435 3062831 := bstep (se 1 (by rfl) ⟨2297123, by rfl⟩ : syracuseStep 3062831 = 4594247) B4594247
theorem B2041887 : Blo 2041435 2041887 := bstep (se 1 (by rfl) ⟨1531415, by rfl⟩ : syracuseStep 2041887 = 3062831) B3062831
theorem B3062837 : Blo 2041435 3062837 := bbase (se 5 (by rfl) ⟨143570, by rfl⟩ : syracuseStep 3062837 = 287141) (by norm_num)
theorem B2041891 : Blo 2041435 2041891 := bstep (se 1 (by rfl) ⟨1531418, by rfl⟩ : syracuseStep 2041891 = 3062837) B3062837
theorem B5168549 : Blo 2041435 5168549 := bbase (se 4 (by rfl) ⟨484551, by rfl⟩ : syracuseStep 5168549 = 969103) (by norm_num)
theorem B3445699 : Blo 2041435 3445699 := bstep (se 1 (by rfl) ⟨2584274, by rfl⟩ : syracuseStep 3445699 = 5168549) B5168549
theorem B4594265 : Blo 2041435 4594265 := bstep (se 2 (by rfl) ⟨1722849, by rfl⟩ : syracuseStep 4594265 = 3445699) B3445699
theorem B3062843 : Blo 2041435 3062843 := bstep (se 1 (by rfl) ⟨2297132, by rfl⟩ : syracuseStep 3062843 = 4594265) B4594265
theorem B2041895 : Blo 2041435 2041895 := bstep (se 1 (by rfl) ⟨1531421, by rfl⟩ : syracuseStep 2041895 = 3062843) B3062843
theorem B2297137 : Blo 2041435 2297137 := bbase (se 2 (by rfl) ⟨861426, by rfl⟩ : syracuseStep 2297137 = 1722853) (by norm_num)
theorem B3062849 : Blo 2041435 3062849 := bstep (se 2 (by rfl) ⟨1148568, by rfl⟩ : syracuseStep 3062849 = 2297137) B2297137
theorem B2041899 : Blo 2041435 2041899 := bstep (se 1 (by rfl) ⟨1531424, by rfl⟩ : syracuseStep 2041899 = 3062849) B3062849
theorem B4360981 : Blo 2041435 4360981 := bbase (se 6 (by rfl) ⟨102210, by rfl⟩ : syracuseStep 4360981 = 204421) (by norm_num)
theorem B5814641 : Blo 2041435 5814641 := bstep (se 2 (by rfl) ⟨2180490, by rfl⟩ : syracuseStep 5814641 = 4360981) B4360981
theorem B3876427 : Blo 2041435 3876427 := bstep (se 1 (by rfl) ⟨2907320, by rfl⟩ : syracuseStep 3876427 = 5814641) B5814641
theorem B5168569 : Blo 2041435 5168569 := bstep (se 2 (by rfl) ⟨1938213, by rfl⟩ : syracuseStep 5168569 = 3876427) B3876427
theorem B6891425 : Blo 2041435 6891425 := bstep (se 2 (by rfl) ⟨2584284, by rfl⟩ : syracuseStep 6891425 = 5168569) B5168569
theorem B4594283 : Blo 2041435 4594283 := bstep (se 1 (by rfl) ⟨3445712, by rfl⟩ : syracuseStep 4594283 = 6891425) B6891425
theorem B3062855 : Blo 2041435 3062855 := bstep (se 1 (by rfl) ⟨2297141, by rfl⟩ : syracuseStep 3062855 = 4594283) B4594283
theorem B2041903 : Blo 2041435 2041903 := bstep (se 1 (by rfl) ⟨1531427, by rfl⟩ : syracuseStep 2041903 = 3062855) B3062855
theorem B3062861 : Blo 2041435 3062861 := bbase (se 3 (by rfl) ⟨574286, by rfl⟩ : syracuseStep 3062861 = 1148573) (by norm_num)
theorem B2041907 : Blo 2041435 2041907 := bstep (se 1 (by rfl) ⟨1531430, by rfl⟩ : syracuseStep 2041907 = 3062861) B3062861
theorem B4594301 : Blo 2041435 4594301 := bbase (se 3 (by rfl) ⟨861431, by rfl⟩ : syracuseStep 4594301 = 1722863) (by norm_num)
theorem B3062867 : Blo 2041435 3062867 := bstep (se 1 (by rfl) ⟨2297150, by rfl⟩ : syracuseStep 3062867 = 4594301) B4594301
theorem B2041911 : Blo 2041435 2041911 := bstep (se 1 (by rfl) ⟨1531433, by rfl⟩ : syracuseStep 2041911 = 3062867) B3062867
theorem B3445733 : Blo 2041435 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B2297155 : Blo 2041435 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B3062873 : Blo 2041435 3062873 := bstep (se 2 (by rfl) ⟨1148577, by rfl⟩ : syracuseStep 3062873 = 2297155) B2297155
theorem B2041915 : Blo 2041435 2041915 := bstep (se 1 (by rfl) ⟨1531436, by rfl⟩ : syracuseStep 2041915 = 3062873) B3062873
theorem B3104669 : Blo 2041435 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B8279117 : Blo 2041435 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B5519411 : Blo 2041435 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3679607 : Blo 2041435 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B9812285 : Blo 2041435 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B6541523 : Blo 2041435 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B4361015 : Blo 2041435 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B2907343 : Blo 2041435 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B15505829 : Blo 2041435 15505829 := bstep (se 4 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 15505829 = 2907343) B2907343
theorem B10337219 : Blo 2041435 10337219 := bstep (se 1 (by rfl) ⟨7752914, by rfl⟩ : syracuseStep 10337219 = 15505829) B15505829
theorem B6891479 : Blo 2041435 6891479 := bstep (se 1 (by rfl) ⟨5168609, by rfl⟩ : syracuseStep 6891479 = 10337219) B10337219
theorem B4594319 : Blo 2041435 4594319 := bstep (se 1 (by rfl) ⟨3445739, by rfl⟩ : syracuseStep 4594319 = 6891479) B6891479
theorem B3062879 : Blo 2041435 3062879 := bstep (se 1 (by rfl) ⟨2297159, by rfl⟩ : syracuseStep 3062879 = 4594319) B4594319
theorem B2041919 : Blo 2041435 2041919 := bstep (se 1 (by rfl) ⟨1531439, by rfl⟩ : syracuseStep 2041919 = 3062879) B3062879
theorem B3062885 : Blo 2041435 3062885 := bbase (se 4 (by rfl) ⟨287145, by rfl⟩ : syracuseStep 3062885 = 574291) (by norm_num)
theorem B2041923 : Blo 2041435 2041923 := bstep (se 1 (by rfl) ⟨1531442, by rfl⟩ : syracuseStep 2041923 = 3062885) B3062885
theorem B2759717 : Blo 2041435 2759717 := bbase (se 4 (by rfl) ⟨258723, by rfl⟩ : syracuseStep 2759717 = 517447) (by norm_num)
theorem B7359245 : Blo 2041435 7359245 := bstep (se 3 (by rfl) ⟨1379858, by rfl⟩ : syracuseStep 7359245 = 2759717) B2759717
theorem B4906163 : Blo 2041435 4906163 := bstep (se 1 (by rfl) ⟨3679622, by rfl⟩ : syracuseStep 4906163 = 7359245) B7359245
theorem B3270775 : Blo 2041435 3270775 := bstep (se 1 (by rfl) ⟨2453081, by rfl⟩ : syracuseStep 3270775 = 4906163) B4906163
theorem B4361033 : Blo 2041435 4361033 := bstep (se 2 (by rfl) ⟨1635387, by rfl⟩ : syracuseStep 4361033 = 3270775) B3270775
theorem B2907355 : Blo 2041435 2907355 := bstep (se 1 (by rfl) ⟨2180516, by rfl⟩ : syracuseStep 2907355 = 4361033) B4361033
theorem B3876473 : Blo 2041435 3876473 := bstep (se 2 (by rfl) ⟨1453677, by rfl⟩ : syracuseStep 3876473 = 2907355) B2907355
theorem B2584315 : Blo 2041435 2584315 := bstep (se 1 (by rfl) ⟨1938236, by rfl⟩ : syracuseStep 2584315 = 3876473) B3876473
theorem B3445753 : Blo 2041435 3445753 := bstep (se 2 (by rfl) ⟨1292157, by rfl⟩ : syracuseStep 3445753 = 2584315) B2584315
theorem B4594337 : Blo 2041435 4594337 := bstep (se 2 (by rfl) ⟨1722876, by rfl⟩ : syracuseStep 4594337 = 3445753) B3445753
theorem B3062891 : Blo 2041435 3062891 := bstep (se 1 (by rfl) ⟨2297168, by rfl⟩ : syracuseStep 3062891 = 4594337) B4594337
theorem B2041927 : Blo 2041435 2041927 := bstep (se 1 (by rfl) ⟨1531445, by rfl⟩ : syracuseStep 2041927 = 3062891) B3062891
theorem B2297173 : Blo 2041435 2297173 := bbase (se 11 (by rfl) ⟨1682, by rfl⟩ : syracuseStep 2297173 = 3365) (by norm_num)
theorem B3062897 : Blo 2041435 3062897 := bstep (se 2 (by rfl) ⟨1148586, by rfl⟩ : syracuseStep 3062897 = 2297173) B2297173
theorem B2041931 : Blo 2041435 2041931 := bstep (se 1 (by rfl) ⟨1531448, by rfl⟩ : syracuseStep 2041931 = 3062897) B3062897
theorem B2584325 : Blo 2041435 2584325 := bbase (se 4 (by rfl) ⟨242280, by rfl⟩ : syracuseStep 2584325 = 484561) (by norm_num)
theorem B6891533 : Blo 2041435 6891533 := bstep (se 3 (by rfl) ⟨1292162, by rfl⟩ : syracuseStep 6891533 = 2584325) B2584325
theorem B4594355 : Blo 2041435 4594355 := bstep (se 1 (by rfl) ⟨3445766, by rfl⟩ : syracuseStep 4594355 = 6891533) B6891533
theorem B3062903 : Blo 2041435 3062903 := bstep (se 1 (by rfl) ⟨2297177, by rfl⟩ : syracuseStep 3062903 = 4594355) B4594355
theorem B2041935 : Blo 2041435 2041935 := bstep (se 1 (by rfl) ⟨1531451, by rfl⟩ : syracuseStep 2041935 = 3062903) B3062903
theorem B3062909 : Blo 2041435 3062909 := bbase (se 3 (by rfl) ⟨574295, by rfl⟩ : syracuseStep 3062909 = 1148591) (by norm_num)
theorem B2041939 : Blo 2041435 2041939 := bstep (se 1 (by rfl) ⟨1531454, by rfl⟩ : syracuseStep 2041939 = 3062909) B3062909
theorem B4594373 : Blo 2041435 4594373 := bbase (se 4 (by rfl) ⟨430722, by rfl⟩ : syracuseStep 4594373 = 861445) (by norm_num)
theorem B3062915 : Blo 2041435 3062915 := bstep (se 1 (by rfl) ⟨2297186, by rfl⟩ : syracuseStep 3062915 = 4594373) B4594373
theorem B2041943 : Blo 2041435 2041943 := bstep (se 1 (by rfl) ⟨1531457, by rfl⟩ : syracuseStep 2041943 = 3062915) B3062915
theorem B5894101 : Blo 2041435 5894101 := bbase (se 7 (by rfl) ⟨69071, by rfl⟩ : syracuseStep 5894101 = 138143) (by norm_num)
theorem B7858801 : Blo 2041435 7858801 := bstep (se 2 (by rfl) ⟨2947050, by rfl⟩ : syracuseStep 7858801 = 5894101) B5894101
theorem B41913605 : Blo 2041435 41913605 := bstep (se 4 (by rfl) ⟨3929400, by rfl⟩ : syracuseStep 41913605 = 7858801) B7858801
theorem B27942403 : Blo 2041435 27942403 := bstep (se 1 (by rfl) ⟨20956802, by rfl⟩ : syracuseStep 27942403 = 41913605) B41913605
theorem B37256537 : Blo 2041435 37256537 := bstep (se 2 (by rfl) ⟨13971201, by rfl⟩ : syracuseStep 37256537 = 27942403) B27942403
theorem B24837691 : Blo 2041435 24837691 := bstep (se 1 (by rfl) ⟨18628268, by rfl⟩ : syracuseStep 24837691 = 37256537) B37256537
theorem B33116921 : Blo 2041435 33116921 := bstep (se 2 (by rfl) ⟨12418845, by rfl⟩ : syracuseStep 33116921 = 24837691) B24837691
theorem B22077947 : Blo 2041435 22077947 := bstep (se 1 (by rfl) ⟨16558460, by rfl⟩ : syracuseStep 22077947 = 33116921) B33116921
theorem B14718631 : Blo 2041435 14718631 := bstep (se 1 (by rfl) ⟨11038973, by rfl⟩ : syracuseStep 14718631 = 22077947) B22077947
theorem B19624841 : Blo 2041435 19624841 := bstep (se 2 (by rfl) ⟨7359315, by rfl⟩ : syracuseStep 19624841 = 14718631) B14718631
theorem B13083227 : Blo 2041435 13083227 := bstep (se 1 (by rfl) ⟨9812420, by rfl⟩ : syracuseStep 13083227 = 19624841) B19624841
theorem B8722151 : Blo 2041435 8722151 := bstep (se 1 (by rfl) ⟨6541613, by rfl⟩ : syracuseStep 8722151 = 13083227) B13083227
theorem B5814767 : Blo 2041435 5814767 := bstep (se 1 (by rfl) ⟨4361075, by rfl⟩ : syracuseStep 5814767 = 8722151) B8722151
theorem B3876511 : Blo 2041435 3876511 := bstep (se 1 (by rfl) ⟨2907383, by rfl⟩ : syracuseStep 3876511 = 5814767) B5814767
theorem B5168681 : Blo 2041435 5168681 := bstep (se 2 (by rfl) ⟨1938255, by rfl⟩ : syracuseStep 5168681 = 3876511) B3876511
theorem B3445787 : Blo 2041435 3445787 := bstep (se 1 (by rfl) ⟨2584340, by rfl⟩ : syracuseStep 3445787 = 5168681) B5168681
theorem B2297191 : Blo 2041435 2297191 := bstep (se 1 (by rfl) ⟨1722893, by rfl⟩ : syracuseStep 2297191 = 3445787) B3445787
theorem B3062921 : Blo 2041435 3062921 := bstep (se 2 (by rfl) ⟨1148595, by rfl⟩ : syracuseStep 3062921 = 2297191) B2297191
theorem B2041947 : Blo 2041435 2041947 := bstep (se 1 (by rfl) ⟨1531460, by rfl⟩ : syracuseStep 2041947 = 3062921) B3062921
theorem B10337381 : Blo 2041435 10337381 := bbase (se 4 (by rfl) ⟨969129, by rfl⟩ : syracuseStep 10337381 = 1938259) (by norm_num)
theorem B6891587 : Blo 2041435 6891587 := bstep (se 1 (by rfl) ⟨5168690, by rfl⟩ : syracuseStep 6891587 = 10337381) B10337381
theorem B4594391 : Blo 2041435 4594391 := bstep (se 1 (by rfl) ⟨3445793, by rfl⟩ : syracuseStep 4594391 = 6891587) B6891587
theorem B3062927 : Blo 2041435 3062927 := bstep (se 1 (by rfl) ⟨2297195, by rfl⟩ : syracuseStep 3062927 = 4594391) B4594391
theorem B2041951 : Blo 2041435 2041951 := bstep (se 1 (by rfl) ⟨1531463, by rfl⟩ : syracuseStep 2041951 = 3062927) B3062927
theorem B3062933 : Blo 2041435 3062933 := bbase (se 6 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 3062933 = 143575) (by norm_num)
theorem B2041955 : Blo 2041435 2041955 := bstep (se 1 (by rfl) ⟨1531466, by rfl⟩ : syracuseStep 2041955 = 3062933) B3062933
theorem B5748533 : Blo 2041435 5748533 := bbase (se 5 (by rfl) ⟨269462, by rfl⟩ : syracuseStep 5748533 = 538925) (by norm_num)
theorem B3832355 : Blo 2041435 3832355 := bstep (se 1 (by rfl) ⟨2874266, by rfl⟩ : syracuseStep 3832355 = 5748533) B5748533
theorem B2554903 : Blo 2041435 2554903 := bstep (se 1 (by rfl) ⟨1916177, by rfl⟩ : syracuseStep 2554903 = 3832355) B3832355
theorem B3406537 : Blo 2041435 3406537 := bstep (se 2 (by rfl) ⟨1277451, by rfl⟩ : syracuseStep 3406537 = 2554903) B2554903
theorem B4542049 : Blo 2041435 4542049 := bstep (se 2 (by rfl) ⟨1703268, by rfl⟩ : syracuseStep 4542049 = 3406537) B3406537
theorem B6056065 : Blo 2041435 6056065 := bstep (se 2 (by rfl) ⟨2271024, by rfl⟩ : syracuseStep 6056065 = 4542049) B4542049
theorem B32299013 : Blo 2041435 32299013 := bstep (se 4 (by rfl) ⟨3028032, by rfl⟩ : syracuseStep 32299013 = 6056065) B6056065
theorem B21532675 : Blo 2041435 21532675 := bstep (se 1 (by rfl) ⟨16149506, by rfl⟩ : syracuseStep 21532675 = 32299013) B32299013
theorem B28710233 : Blo 2041435 28710233 := bstep (se 2 (by rfl) ⟨10766337, by rfl⟩ : syracuseStep 28710233 = 21532675) B21532675
theorem B19140155 : Blo 2041435 19140155 := bstep (se 1 (by rfl) ⟨14355116, by rfl⟩ : syracuseStep 19140155 = 28710233) B28710233
theorem B12760103 : Blo 2041435 12760103 := bstep (se 1 (by rfl) ⟨9570077, by rfl⟩ : syracuseStep 12760103 = 19140155) B19140155
theorem B34026941 : Blo 2041435 34026941 := bstep (se 3 (by rfl) ⟨6380051, by rfl⟩ : syracuseStep 34026941 = 12760103) B12760103
theorem B22684627 : Blo 2041435 22684627 := bstep (se 1 (by rfl) ⟨17013470, by rfl⟩ : syracuseStep 22684627 = 34026941) B34026941
theorem B30246169 : Blo 2041435 30246169 := bstep (se 2 (by rfl) ⟨11342313, by rfl⟩ : syracuseStep 30246169 = 22684627) B22684627
theorem B40328225 : Blo 2041435 40328225 := bstep (se 2 (by rfl) ⟨15123084, by rfl⟩ : syracuseStep 40328225 = 30246169) B30246169
theorem B26885483 : Blo 2041435 26885483 := bstep (se 1 (by rfl) ⟨20164112, by rfl⟩ : syracuseStep 26885483 = 40328225) B40328225
theorem B17923655 : Blo 2041435 17923655 := bstep (se 1 (by rfl) ⟨13442741, by rfl⟩ : syracuseStep 17923655 = 26885483) B26885483
theorem B11949103 : Blo 2041435 11949103 := bstep (se 1 (by rfl) ⟨8961827, by rfl⟩ : syracuseStep 11949103 = 17923655) B17923655
theorem B15932137 : Blo 2041435 15932137 := bstep (se 2 (by rfl) ⟨5974551, by rfl⟩ : syracuseStep 15932137 = 11949103) B11949103
theorem B21242849 : Blo 2041435 21242849 := bstep (se 2 (by rfl) ⟨7966068, by rfl⟩ : syracuseStep 21242849 = 15932137) B15932137
theorem B226590389 : Blo 2041435 226590389 := bstep (se 5 (by rfl) ⟨10621424, by rfl⟩ : syracuseStep 226590389 = 21242849) B21242849
theorem B151060259 : Blo 2041435 151060259 := bstep (se 1 (by rfl) ⟨113295194, by rfl⟩ : syracuseStep 151060259 = 226590389) B226590389
theorem B402827357 : Blo 2041435 402827357 := bstep (se 3 (by rfl) ⟨75530129, by rfl⟩ : syracuseStep 402827357 = 151060259) B151060259
theorem B268551571 : Blo 2041435 268551571 := bstep (se 1 (by rfl) ⟨201413678, by rfl⟩ : syracuseStep 268551571 = 402827357) B402827357
theorem B358068761 : Blo 2041435 358068761 := bstep (se 2 (by rfl) ⟨134275785, by rfl⟩ : syracuseStep 358068761 = 268551571) B268551571
theorem B238712507 : Blo 2041435 238712507 := bstep (se 1 (by rfl) ⟨179034380, by rfl⟩ : syracuseStep 238712507 = 358068761) B358068761
theorem B159141671 : Blo 2041435 159141671 := bstep (se 1 (by rfl) ⟨119356253, by rfl⟩ : syracuseStep 159141671 = 238712507) B238712507
theorem B106094447 : Blo 2041435 106094447 := bstep (se 1 (by rfl) ⟨79570835, by rfl⟩ : syracuseStep 106094447 = 159141671) B159141671
theorem B70729631 : Blo 2041435 70729631 := bstep (se 1 (by rfl) ⟨53047223, by rfl⟩ : syracuseStep 70729631 = 106094447) B106094447
theorem B47153087 : Blo 2041435 47153087 := bstep (se 1 (by rfl) ⟨35364815, by rfl⟩ : syracuseStep 47153087 = 70729631) B70729631
theorem B31435391 : Blo 2041435 31435391 := bstep (se 1 (by rfl) ⟨23576543, by rfl⟩ : syracuseStep 31435391 = 47153087) B47153087
theorem B20956927 : Blo 2041435 20956927 := bstep (se 1 (by rfl) ⟨15717695, by rfl⟩ : syracuseStep 20956927 = 31435391) B31435391
theorem B27942569 : Blo 2041435 27942569 := bstep (se 2 (by rfl) ⟨10478463, by rfl⟩ : syracuseStep 27942569 = 20956927) B20956927
theorem B18628379 : Blo 2041435 18628379 := bstep (se 1 (by rfl) ⟨13971284, by rfl⟩ : syracuseStep 18628379 = 27942569) B27942569
theorem B12418919 : Blo 2041435 12418919 := bstep (se 1 (by rfl) ⟨9314189, by rfl⟩ : syracuseStep 12418919 = 18628379) B18628379
theorem B8279279 : Blo 2041435 8279279 := bstep (se 1 (by rfl) ⟨6209459, by rfl⟩ : syracuseStep 8279279 = 12418919) B12418919
theorem B5519519 : Blo 2041435 5519519 := bstep (se 1 (by rfl) ⟨4139639, by rfl⟩ : syracuseStep 5519519 = 8279279) B8279279
theorem B3679679 : Blo 2041435 3679679 := bstep (se 1 (by rfl) ⟨2759759, by rfl⟩ : syracuseStep 3679679 = 5519519) B5519519
theorem B9812477 : Blo 2041435 9812477 := bstep (se 3 (by rfl) ⟨1839839, by rfl⟩ : syracuseStep 9812477 = 3679679) B3679679
theorem B6541651 : Blo 2041435 6541651 := bstep (se 1 (by rfl) ⟨4906238, by rfl⟩ : syracuseStep 6541651 = 9812477) B9812477
theorem B8722201 : Blo 2041435 8722201 := bstep (se 2 (by rfl) ⟨3270825, by rfl⟩ : syracuseStep 8722201 = 6541651) B6541651
theorem B11629601 : Blo 2041435 11629601 := bstep (se 2 (by rfl) ⟨4361100, by rfl⟩ : syracuseStep 11629601 = 8722201) B8722201
theorem B7753067 : Blo 2041435 7753067 := bstep (se 1 (by rfl) ⟨5814800, by rfl⟩ : syracuseStep 7753067 = 11629601) B11629601
theorem B5168711 : Blo 2041435 5168711 := bstep (se 1 (by rfl) ⟨3876533, by rfl⟩ : syracuseStep 5168711 = 7753067) B7753067
theorem B3445807 : Blo 2041435 3445807 := bstep (se 1 (by rfl) ⟨2584355, by rfl⟩ : syracuseStep 3445807 = 5168711) B5168711
theorem B4594409 : Blo 2041435 4594409 := bstep (se 2 (by rfl) ⟨1722903, by rfl⟩ : syracuseStep 4594409 = 3445807) B3445807
theorem B3062939 : Blo 2041435 3062939 := bstep (se 1 (by rfl) ⟨2297204, by rfl⟩ : syracuseStep 3062939 = 4594409) B4594409
theorem B2041959 : Blo 2041435 2041959 := bstep (se 1 (by rfl) ⟨1531469, by rfl⟩ : syracuseStep 2041959 = 3062939) B3062939
theorem B2297209 : Blo 2041435 2297209 := bbase (se 2 (by rfl) ⟨861453, by rfl⟩ : syracuseStep 2297209 = 1722907) (by norm_num)
theorem B3062945 : Blo 2041435 3062945 := bstep (se 2 (by rfl) ⟨1148604, by rfl⟩ : syracuseStep 3062945 = 2297209) B2297209
theorem B2041963 : Blo 2041435 2041963 := bstep (se 1 (by rfl) ⟨1531472, by rfl⟩ : syracuseStep 2041963 = 3062945) B3062945
theorem B14718773 : Blo 2041435 14718773 := bbase (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) (by norm_num)
theorem B9812515 : Blo 2041435 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B13083353 : Blo 2041435 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B8722235 : Blo 2041435 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B5814823 : Blo 2041435 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B7753097 : Blo 2041435 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B5168731 : Blo 2041435 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B6891641 : Blo 2041435 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B4594427 : Blo 2041435 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B3062951 : Blo 2041435 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B2041967 : Blo 2041435 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B3062957 : Blo 2041435 3062957 := bbase (se 3 (by rfl) ⟨574304, by rfl⟩ : syracuseStep 3062957 = 1148609) (by norm_num)
theorem B2041971 : Blo 2041435 2041971 := bstep (se 1 (by rfl) ⟨1531478, by rfl⟩ : syracuseStep 2041971 = 3062957) B3062957
theorem B4594445 : Blo 2041435 4594445 := bbase (se 3 (by rfl) ⟨861458, by rfl⟩ : syracuseStep 4594445 = 1722917) (by norm_num)
theorem B3062963 : Blo 2041435 3062963 := bstep (se 1 (by rfl) ⟨2297222, by rfl⟩ : syracuseStep 3062963 = 4594445) B4594445
theorem B2041975 : Blo 2041435 2041975 := bstep (se 1 (by rfl) ⟨1531481, by rfl⟩ : syracuseStep 2041975 = 3062963) B3062963
theorem B2584381 : Blo 2041435 2584381 := bbase (se 3 (by rfl) ⟨484571, by rfl⟩ : syracuseStep 2584381 = 969143) (by norm_num)
theorem B3445841 : Blo 2041435 3445841 := bstep (se 2 (by rfl) ⟨1292190, by rfl⟩ : syracuseStep 3445841 = 2584381) B2584381
theorem B2297227 : Blo 2041435 2297227 := bstep (se 1 (by rfl) ⟨1722920, by rfl⟩ : syracuseStep 2297227 = 3445841) B3445841
theorem B3062969 : Blo 2041435 3062969 := bstep (se 2 (by rfl) ⟨1148613, by rfl⟩ : syracuseStep 3062969 = 2297227) B2297227
theorem B2041979 : Blo 2041435 2041979 := bstep (se 1 (by rfl) ⟨1531484, by rfl⟩ : syracuseStep 2041979 = 3062969) B3062969
theorem B3147125 : Blo 2041435 3147125 := bbase (se 5 (by rfl) ⟨147521, by rfl⟩ : syracuseStep 3147125 = 295043) (by norm_num)
theorem B8392333 : Blo 2041435 8392333 := bstep (se 3 (by rfl) ⟨1573562, by rfl⟩ : syracuseStep 8392333 = 3147125) B3147125
theorem B11189777 : Blo 2041435 11189777 := bstep (se 2 (by rfl) ⟨4196166, by rfl⟩ : syracuseStep 11189777 = 8392333) B8392333
theorem B119357621 : Blo 2041435 119357621 := bstep (se 5 (by rfl) ⟨5594888, by rfl⟩ : syracuseStep 119357621 = 11189777) B11189777
theorem B79571747 : Blo 2041435 79571747 := bstep (se 1 (by rfl) ⟨59678810, by rfl⟩ : syracuseStep 79571747 = 119357621) B119357621
theorem B53047831 : Blo 2041435 53047831 := bstep (se 1 (by rfl) ⟨39785873, by rfl⟩ : syracuseStep 53047831 = 79571747) B79571747
theorem B70730441 : Blo 2041435 70730441 := bstep (se 2 (by rfl) ⟨26523915, by rfl⟩ : syracuseStep 70730441 = 53047831) B53047831
theorem B47153627 : Blo 2041435 47153627 := bstep (se 1 (by rfl) ⟨35365220, by rfl⟩ : syracuseStep 47153627 = 70730441) B70730441
theorem B31435751 : Blo 2041435 31435751 := bstep (se 1 (by rfl) ⟨23576813, by rfl⟩ : syracuseStep 31435751 = 47153627) B47153627
theorem B20957167 : Blo 2041435 20957167 := bstep (se 1 (by rfl) ⟨15717875, by rfl⟩ : syracuseStep 20957167 = 31435751) B31435751
theorem B27942889 : Blo 2041435 27942889 := bstep (se 2 (by rfl) ⟨10478583, by rfl⟩ : syracuseStep 27942889 = 20957167) B20957167
theorem B37257185 : Blo 2041435 37257185 := bstep (se 2 (by rfl) ⟨13971444, by rfl⟩ : syracuseStep 37257185 = 27942889) B27942889
theorem B24838123 : Blo 2041435 24838123 := bstep (se 1 (by rfl) ⟨18628592, by rfl⟩ : syracuseStep 24838123 = 37257185) B37257185
theorem B33117497 : Blo 2041435 33117497 := bstep (se 2 (by rfl) ⟨12419061, by rfl⟩ : syracuseStep 33117497 = 24838123) B24838123
theorem B22078331 : Blo 2041435 22078331 := bstep (se 1 (by rfl) ⟨16558748, by rfl⟩ : syracuseStep 22078331 = 33117497) B33117497
theorem B14718887 : Blo 2041435 14718887 := bstep (se 1 (by rfl) ⟨11039165, by rfl⟩ : syracuseStep 14718887 = 22078331) B22078331
theorem B9812591 : Blo 2041435 9812591 := bstep (se 1 (by rfl) ⟨7359443, by rfl⟩ : syracuseStep 9812591 = 14718887) B14718887
theorem B6541727 : Blo 2041435 6541727 := bstep (se 1 (by rfl) ⟨4906295, by rfl⟩ : syracuseStep 6541727 = 9812591) B9812591
theorem B17444605 : Blo 2041435 17444605 := bstep (se 3 (by rfl) ⟨3270863, by rfl⟩ : syracuseStep 17444605 = 6541727) B6541727
theorem B23259473 : Blo 2041435 23259473 := bstep (se 2 (by rfl) ⟨8722302, by rfl⟩ : syracuseStep 23259473 = 17444605) B17444605
theorem B15506315 : Blo 2041435 15506315 := bstep (se 1 (by rfl) ⟨11629736, by rfl⟩ : syracuseStep 15506315 = 23259473) B23259473
theorem B10337543 : Blo 2041435 10337543 := bstep (se 1 (by rfl) ⟨7753157, by rfl⟩ : syracuseStep 10337543 = 15506315) B15506315
theorem B6891695 : Blo 2041435 6891695 := bstep (se 1 (by rfl) ⟨5168771, by rfl⟩ : syracuseStep 6891695 = 10337543) B10337543
theorem B4594463 : Blo 2041435 4594463 := bstep (se 1 (by rfl) ⟨3445847, by rfl⟩ : syracuseStep 4594463 = 6891695) B6891695
theorem B3062975 : Blo 2041435 3062975 := bstep (se 1 (by rfl) ⟨2297231, by rfl⟩ : syracuseStep 3062975 = 4594463) B4594463
theorem B2041983 : Blo 2041435 2041983 := bstep (se 1 (by rfl) ⟨1531487, by rfl⟩ : syracuseStep 2041983 = 3062975) B3062975
theorem B3062981 : Blo 2041435 3062981 := bbase (se 4 (by rfl) ⟨287154, by rfl⟩ : syracuseStep 3062981 = 574309) (by norm_num)
theorem B2041987 : Blo 2041435 2041987 := bstep (se 1 (by rfl) ⟨1531490, by rfl⟩ : syracuseStep 2041987 = 3062981) B3062981
theorem B3445861 : Blo 2041435 3445861 := bbase (se 4 (by rfl) ⟨323049, by rfl⟩ : syracuseStep 3445861 = 646099) (by norm_num)
theorem B4594481 : Blo 2041435 4594481 := bstep (se 2 (by rfl) ⟨1722930, by rfl⟩ : syracuseStep 4594481 = 3445861) B3445861
theorem B3062987 : Blo 2041435 3062987 := bstep (se 1 (by rfl) ⟨2297240, by rfl⟩ : syracuseStep 3062987 = 4594481) B4594481
theorem B2041991 : Blo 2041435 2041991 := bstep (se 1 (by rfl) ⟨1531493, by rfl⟩ : syracuseStep 2041991 = 3062987) B3062987
theorem B2297245 : Blo 2041435 2297245 := bbase (se 3 (by rfl) ⟨430733, by rfl⟩ : syracuseStep 2297245 = 861467) (by norm_num)
theorem B3062993 : Blo 2041435 3062993 := bstep (se 2 (by rfl) ⟨1148622, by rfl⟩ : syracuseStep 3062993 = 2297245) B2297245
theorem B2041995 : Blo 2041435 2041995 := bstep (se 1 (by rfl) ⟨1531496, by rfl⟩ : syracuseStep 2041995 = 3062993) B3062993
theorem B6891749 : Blo 2041435 6891749 := bbase (se 4 (by rfl) ⟨646101, by rfl⟩ : syracuseStep 6891749 = 1292203) (by norm_num)
theorem B4594499 : Blo 2041435 4594499 := bstep (se 1 (by rfl) ⟨3445874, by rfl⟩ : syracuseStep 4594499 = 6891749) B6891749
theorem B3062999 : Blo 2041435 3062999 := bstep (se 1 (by rfl) ⟨2297249, by rfl⟩ : syracuseStep 3062999 = 4594499) B4594499
theorem B2041999 : Blo 2041435 2041999 := bstep (se 1 (by rfl) ⟨1531499, by rfl⟩ : syracuseStep 2041999 = 3062999) B3062999
theorem B3063005 : Blo 2041435 3063005 := bbase (se 3 (by rfl) ⟨574313, by rfl⟩ : syracuseStep 3063005 = 1148627) (by norm_num)
theorem B2042003 : Blo 2041435 2042003 := bstep (se 1 (by rfl) ⟨1531502, by rfl⟩ : syracuseStep 2042003 = 3063005) B3063005
theorem B4594517 : Blo 2041435 4594517 := bbase (se 9 (by rfl) ⟨13460, by rfl⟩ : syracuseStep 4594517 = 26921) (by norm_num)
theorem B3063011 : Blo 2041435 3063011 := bstep (se 1 (by rfl) ⟨2297258, by rfl⟩ : syracuseStep 3063011 = 4594517) B4594517
theorem B2042007 : Blo 2041435 2042007 := bstep (se 1 (by rfl) ⟨1531505, by rfl⟩ : syracuseStep 2042007 = 3063011) B3063011
theorem B5814949 : Blo 2041435 5814949 := bbase (se 4 (by rfl) ⟨545151, by rfl⟩ : syracuseStep 5814949 = 1090303) (by norm_num)
theorem B7753265 : Blo 2041435 7753265 := bstep (se 2 (by rfl) ⟨2907474, by rfl⟩ : syracuseStep 7753265 = 5814949) B5814949
theorem B5168843 : Blo 2041435 5168843 := bstep (se 1 (by rfl) ⟨3876632, by rfl⟩ : syracuseStep 5168843 = 7753265) B7753265
theorem B3445895 : Blo 2041435 3445895 := bstep (se 1 (by rfl) ⟨2584421, by rfl⟩ : syracuseStep 3445895 = 5168843) B5168843
theorem B2297263 : Blo 2041435 2297263 := bstep (se 1 (by rfl) ⟨1722947, by rfl⟩ : syracuseStep 2297263 = 3445895) B3445895
theorem B3063017 : Blo 2041435 3063017 := bstep (se 2 (by rfl) ⟨1148631, by rfl⟩ : syracuseStep 3063017 = 2297263) B2297263
theorem B2042011 : Blo 2041435 2042011 := bstep (se 1 (by rfl) ⟨1531508, by rfl⟩ : syracuseStep 2042011 = 3063017) B3063017
theorem B5519669 : Blo 2041435 5519669 := bbase (se 5 (by rfl) ⟨258734, by rfl⟩ : syracuseStep 5519669 = 517469) (by norm_num)
theorem B58876469 : Blo 2041435 58876469 := bstep (se 5 (by rfl) ⟨2759834, by rfl⟩ : syracuseStep 58876469 = 5519669) B5519669
theorem B39250979 : Blo 2041435 39250979 := bstep (se 1 (by rfl) ⟨29438234, by rfl⟩ : syracuseStep 39250979 = 58876469) B58876469
theorem B26167319 : Blo 2041435 26167319 := bstep (se 1 (by rfl) ⟨19625489, by rfl⟩ : syracuseStep 26167319 = 39250979) B39250979
theorem B17444879 : Blo 2041435 17444879 := bstep (se 1 (by rfl) ⟨13083659, by rfl⟩ : syracuseStep 17444879 = 26167319) B26167319
theorem B11629919 : Blo 2041435 11629919 := bstep (se 1 (by rfl) ⟨8722439, by rfl⟩ : syracuseStep 11629919 = 17444879) B17444879
theorem B7753279 : Blo 2041435 7753279 := bstep (se 1 (by rfl) ⟨5814959, by rfl⟩ : syracuseStep 7753279 = 11629919) B11629919
theorem B10337705 : Blo 2041435 10337705 := bstep (se 2 (by rfl) ⟨3876639, by rfl⟩ : syracuseStep 10337705 = 7753279) B7753279
theorem B6891803 : Blo 2041435 6891803 := bstep (se 1 (by rfl) ⟨5168852, by rfl⟩ : syracuseStep 6891803 = 10337705) B10337705
theorem B4594535 : Blo 2041435 4594535 := bstep (se 1 (by rfl) ⟨3445901, by rfl⟩ : syracuseStep 4594535 = 6891803) B6891803
theorem B3063023 : Blo 2041435 3063023 := bstep (se 1 (by rfl) ⟨2297267, by rfl⟩ : syracuseStep 3063023 = 4594535) B4594535
theorem B2042015 : Blo 2041435 2042015 := bstep (se 1 (by rfl) ⟨1531511, by rfl⟩ : syracuseStep 2042015 = 3063023) B3063023
theorem B3063029 : Blo 2041435 3063029 := bbase (se 5 (by rfl) ⟨143579, by rfl⟩ : syracuseStep 3063029 = 287159) (by norm_num)
theorem B2042019 : Blo 2041435 2042019 := bstep (se 1 (by rfl) ⟨1531514, by rfl⟩ : syracuseStep 2042019 = 3063029) B3063029
theorem B7359589 : Blo 2041435 7359589 := bbase (se 4 (by rfl) ⟨689961, by rfl⟩ : syracuseStep 7359589 = 1379923) (by norm_num)
theorem B9812785 : Blo 2041435 9812785 := bstep (se 2 (by rfl) ⟨3679794, by rfl⟩ : syracuseStep 9812785 = 7359589) B7359589
theorem B13083713 : Blo 2041435 13083713 := bstep (se 2 (by rfl) ⟨4906392, by rfl⟩ : syracuseStep 13083713 = 9812785) B9812785
theorem B8722475 : Blo 2041435 8722475 := bstep (se 1 (by rfl) ⟨6541856, by rfl⟩ : syracuseStep 8722475 = 13083713) B13083713
theorem B5814983 : Blo 2041435 5814983 := bstep (se 1 (by rfl) ⟨4361237, by rfl⟩ : syracuseStep 5814983 = 8722475) B8722475
theorem B3876655 : Blo 2041435 3876655 := bstep (se 1 (by rfl) ⟨2907491, by rfl⟩ : syracuseStep 3876655 = 5814983) B5814983
theorem B5168873 : Blo 2041435 5168873 := bstep (se 2 (by rfl) ⟨1938327, by rfl⟩ : syracuseStep 5168873 = 3876655) B3876655
theorem B3445915 : Blo 2041435 3445915 := bstep (se 1 (by rfl) ⟨2584436, by rfl⟩ : syracuseStep 3445915 = 5168873) B5168873
theorem B4594553 : Blo 2041435 4594553 := bstep (se 2 (by rfl) ⟨1722957, by rfl⟩ : syracuseStep 4594553 = 3445915) B3445915
theorem B3063035 : Blo 2041435 3063035 := bstep (se 1 (by rfl) ⟨2297276, by rfl⟩ : syracuseStep 3063035 = 4594553) B4594553
theorem B2042023 : Blo 2041435 2042023 := bstep (se 1 (by rfl) ⟨1531517, by rfl⟩ : syracuseStep 2042023 = 3063035) B3063035
theorem B2297281 : Blo 2041435 2297281 := bbase (se 2 (by rfl) ⟨861480, by rfl⟩ : syracuseStep 2297281 = 1722961) (by norm_num)
theorem B3063041 : Blo 2041435 3063041 := bstep (se 2 (by rfl) ⟨1148640, by rfl⟩ : syracuseStep 3063041 = 2297281) B2297281
theorem B2042027 : Blo 2041435 2042027 := bstep (se 1 (by rfl) ⟨1531520, by rfl⟩ : syracuseStep 2042027 = 3063041) B3063041
theorem B5168893 : Blo 2041435 5168893 := bbase (se 3 (by rfl) ⟨969167, by rfl⟩ : syracuseStep 5168893 = 1938335) (by norm_num)
theorem B6891857 : Blo 2041435 6891857 := bstep (se 2 (by rfl) ⟨2584446, by rfl⟩ : syracuseStep 6891857 = 5168893) B5168893
theorem B4594571 : Blo 2041435 4594571 := bstep (se 1 (by rfl) ⟨3445928, by rfl⟩ : syracuseStep 4594571 = 6891857) B6891857
theorem B3063047 : Blo 2041435 3063047 := bstep (se 1 (by rfl) ⟨2297285, by rfl⟩ : syracuseStep 3063047 = 4594571) B4594571
theorem B2042031 : Blo 2041435 2042031 := bstep (se 1 (by rfl) ⟨1531523, by rfl⟩ : syracuseStep 2042031 = 3063047) B3063047
theorem B3063053 : Blo 2041435 3063053 := bbase (se 3 (by rfl) ⟨574322, by rfl⟩ : syracuseStep 3063053 = 1148645) (by norm_num)
theorem B2042035 : Blo 2041435 2042035 := bstep (se 1 (by rfl) ⟨1531526, by rfl⟩ : syracuseStep 2042035 = 3063053) B3063053
theorem B4594589 : Blo 2041435 4594589 := bbase (se 3 (by rfl) ⟨861485, by rfl⟩ : syracuseStep 4594589 = 1722971) (by norm_num)
theorem B3063059 : Blo 2041435 3063059 := bstep (se 1 (by rfl) ⟨2297294, by rfl⟩ : syracuseStep 3063059 = 4594589) B4594589
theorem B2042039 : Blo 2041435 2042039 := bstep (se 1 (by rfl) ⟨1531529, by rfl⟩ : syracuseStep 2042039 = 3063059) B3063059
theorem B3445949 : Blo 2041435 3445949 := bbase (se 3 (by rfl) ⟨646115, by rfl⟩ : syracuseStep 3445949 = 1292231) (by norm_num)
theorem B2297299 : Blo 2041435 2297299 := bstep (se 1 (by rfl) ⟨1722974, by rfl⟩ : syracuseStep 2297299 = 3445949) B3445949
theorem B3063065 : Blo 2041435 3063065 := bstep (se 2 (by rfl) ⟨1148649, by rfl⟩ : syracuseStep 3063065 = 2297299) B2297299
theorem B2042043 : Blo 2041435 2042043 := bstep (se 1 (by rfl) ⟨1531532, by rfl⟩ : syracuseStep 2042043 = 3063065) B3063065
theorem B11630101 : Blo 2041435 11630101 := bbase (se 6 (by rfl) ⟨272580, by rfl⟩ : syracuseStep 11630101 = 545161) (by norm_num)
theorem B15506801 : Blo 2041435 15506801 := bstep (se 2 (by rfl) ⟨5815050, by rfl⟩ : syracuseStep 15506801 = 11630101) B11630101
theorem B10337867 : Blo 2041435 10337867 := bstep (se 1 (by rfl) ⟨7753400, by rfl⟩ : syracuseStep 10337867 = 15506801) B15506801
theorem B6891911 : Blo 2041435 6891911 := bstep (se 1 (by rfl) ⟨5168933, by rfl⟩ : syracuseStep 6891911 = 10337867) B10337867
theorem B4594607 : Blo 2041435 4594607 := bstep (se 1 (by rfl) ⟨3445955, by rfl⟩ : syracuseStep 4594607 = 6891911) B6891911
theorem B3063071 : Blo 2041435 3063071 := bstep (se 1 (by rfl) ⟨2297303, by rfl⟩ : syracuseStep 3063071 = 4594607) B4594607
theorem B2042047 : Blo 2041435 2042047 := bstep (se 1 (by rfl) ⟨1531535, by rfl⟩ : syracuseStep 2042047 = 3063071) B3063071
theorem B3063077 : Blo 2041435 3063077 := bbase (se 4 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 3063077 = 574327) (by norm_num)
theorem B2042051 : Blo 2041435 2042051 := bstep (se 1 (by rfl) ⟨1531538, by rfl⟩ : syracuseStep 2042051 = 3063077) B3063077
theorem B2584477 : Blo 2041435 2584477 := bbase (se 3 (by rfl) ⟨484589, by rfl⟩ : syracuseStep 2584477 = 969179) (by norm_num)
theorem B3445969 : Blo 2041435 3445969 := bstep (se 2 (by rfl) ⟨1292238, by rfl⟩ : syracuseStep 3445969 = 2584477) B2584477
theorem B4594625 : Blo 2041435 4594625 := bstep (se 2 (by rfl) ⟨1722984, by rfl⟩ : syracuseStep 4594625 = 3445969) B3445969
theorem B3063083 : Blo 2041435 3063083 := bstep (se 1 (by rfl) ⟨2297312, by rfl⟩ : syracuseStep 3063083 = 4594625) B4594625
theorem B2042055 : Blo 2041435 2042055 := bstep (se 1 (by rfl) ⟨1531541, by rfl⟩ : syracuseStep 2042055 = 3063083) B3063083
theorem B2297317 : Blo 2041435 2297317 := bbase (se 4 (by rfl) ⟨215373, by rfl⟩ : syracuseStep 2297317 = 430747) (by norm_num)
theorem B3063089 : Blo 2041435 3063089 := bstep (se 2 (by rfl) ⟨1148658, by rfl⟩ : syracuseStep 3063089 = 2297317) B2297317
theorem B2042059 : Blo 2041435 2042059 := bstep (se 1 (by rfl) ⟨1531544, by rfl⟩ : syracuseStep 2042059 = 3063089) B3063089
theorem B4657333 : Blo 2041435 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B6209777 : Blo 2041435 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B4139851 : Blo 2041435 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B5519801 : Blo 2041435 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B3679867 : Blo 2041435 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B4906489 : Blo 2041435 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B6541985 : Blo 2041435 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B4361323 : Blo 2041435 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B5815097 : Blo 2041435 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B3876731 : Blo 2041435 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B2584487 : Blo 2041435 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B6891965 : Blo 2041435 6891965 := bstep (se 3 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 6891965 = 2584487) B2584487
theorem B4594643 : Blo 2041435 4594643 := bstep (se 1 (by rfl) ⟨3445982, by rfl⟩ : syracuseStep 4594643 = 6891965) B6891965
theorem B3063095 : Blo 2041435 3063095 := bstep (se 1 (by rfl) ⟨2297321, by rfl⟩ : syracuseStep 3063095 = 4594643) B4594643
theorem B2042063 : Blo 2041435 2042063 := bstep (se 1 (by rfl) ⟨1531547, by rfl⟩ : syracuseStep 2042063 = 3063095) B3063095
theorem B3063101 : Blo 2041435 3063101 := bbase (se 3 (by rfl) ⟨574331, by rfl⟩ : syracuseStep 3063101 = 1148663) (by norm_num)
theorem B2042067 : Blo 2041435 2042067 := bstep (se 1 (by rfl) ⟨1531550, by rfl⟩ : syracuseStep 2042067 = 3063101) B3063101
theorem B4594661 : Blo 2041435 4594661 := bbase (se 4 (by rfl) ⟨430749, by rfl⟩ : syracuseStep 4594661 = 861499) (by norm_num)
theorem B3063107 : Blo 2041435 3063107 := bstep (se 1 (by rfl) ⟨2297330, by rfl⟩ : syracuseStep 3063107 = 4594661) B4594661
theorem B2042071 : Blo 2041435 2042071 := bstep (se 1 (by rfl) ⟨1531553, by rfl⟩ : syracuseStep 2042071 = 3063107) B3063107
theorem B5169005 : Blo 2041435 5169005 := bbase (se 3 (by rfl) ⟨969188, by rfl⟩ : syracuseStep 5169005 = 1938377) (by norm_num)
theorem B3446003 : Blo 2041435 3446003 := bstep (se 1 (by rfl) ⟨2584502, by rfl⟩ : syracuseStep 3446003 = 5169005) B5169005
theorem B2297335 : Blo 2041435 2297335 := bstep (se 1 (by rfl) ⟨1723001, by rfl⟩ : syracuseStep 2297335 = 3446003) B3446003
theorem B3063113 : Blo 2041435 3063113 := bstep (se 2 (by rfl) ⟨1148667, by rfl⟩ : syracuseStep 3063113 = 2297335) B2297335
theorem B2042075 : Blo 2041435 2042075 := bstep (se 1 (by rfl) ⟨1531556, by rfl⟩ : syracuseStep 2042075 = 3063113) B3063113
theorem B4361357 : Blo 2041435 4361357 := bbase (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) (by norm_num)
theorem B2907571 : Blo 2041435 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B3876761 : Blo 2041435 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B10338029 : Blo 2041435 10338029 := bstep (se 3 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 10338029 = 3876761) B3876761
theorem B6892019 : Blo 2041435 6892019 := bstep (se 1 (by rfl) ⟨5169014, by rfl⟩ : syracuseStep 6892019 = 10338029) B10338029
theorem B4594679 : Blo 2041435 4594679 := bstep (se 1 (by rfl) ⟨3446009, by rfl⟩ : syracuseStep 4594679 = 6892019) B6892019
theorem B3063119 : Blo 2041435 3063119 := bstep (se 1 (by rfl) ⟨2297339, by rfl⟩ : syracuseStep 3063119 = 4594679) B4594679
theorem B2042079 : Blo 2041435 2042079 := bstep (se 1 (by rfl) ⟨1531559, by rfl⟩ : syracuseStep 2042079 = 3063119) B3063119
theorem B3063125 : Blo 2041435 3063125 := bbase (se 11 (by rfl) ⟨2243, by rfl⟩ : syracuseStep 3063125 = 4487) (by norm_num)
theorem B2042083 : Blo 2041435 2042083 := bstep (se 1 (by rfl) ⟨1531562, by rfl⟩ : syracuseStep 2042083 = 3063125) B3063125
theorem B2759933 : Blo 2041435 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B7359821 : Blo 2041435 7359821 := bstep (se 3 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 7359821 = 2759933) B2759933
theorem B4906547 : Blo 2041435 4906547 := bstep (se 1 (by rfl) ⟨3679910, by rfl⟩ : syracuseStep 4906547 = 7359821) B7359821
theorem B3271031 : Blo 2041435 3271031 := bstep (se 1 (by rfl) ⟨2453273, by rfl⟩ : syracuseStep 3271031 = 4906547) B4906547
theorem B2180687 : Blo 2041435 2180687 := bstep (se 1 (by rfl) ⟨1635515, by rfl⟩ : syracuseStep 2180687 = 3271031) B3271031
theorem B5815165 : Blo 2041435 5815165 := bstep (se 3 (by rfl) ⟨1090343, by rfl⟩ : syracuseStep 5815165 = 2180687) B2180687
theorem B7753553 : Blo 2041435 7753553 := bstep (se 2 (by rfl) ⟨2907582, by rfl⟩ : syracuseStep 7753553 = 5815165) B5815165
theorem B5169035 : Blo 2041435 5169035 := bstep (se 1 (by rfl) ⟨3876776, by rfl⟩ : syracuseStep 5169035 = 7753553) B7753553
theorem B3446023 : Blo 2041435 3446023 := bstep (se 1 (by rfl) ⟨2584517, by rfl⟩ : syracuseStep 3446023 = 5169035) B5169035
theorem B4594697 : Blo 2041435 4594697 := bstep (se 2 (by rfl) ⟨1723011, by rfl⟩ : syracuseStep 4594697 = 3446023) B3446023
theorem B3063131 : Blo 2041435 3063131 := bstep (se 1 (by rfl) ⟨2297348, by rfl⟩ : syracuseStep 3063131 = 4594697) B4594697
theorem B2042087 : Blo 2041435 2042087 := bstep (se 1 (by rfl) ⟨1531565, by rfl⟩ : syracuseStep 2042087 = 3063131) B3063131
theorem B2297353 : Blo 2041435 2297353 := bbase (se 2 (by rfl) ⟨861507, by rfl⟩ : syracuseStep 2297353 = 1723015) (by norm_num)
theorem B3063137 : Blo 2041435 3063137 := bstep (se 2 (by rfl) ⟨1148676, by rfl⟩ : syracuseStep 3063137 = 2297353) B2297353
theorem B2042091 : Blo 2041435 2042091 := bstep (se 1 (by rfl) ⟨1531568, by rfl⟩ : syracuseStep 2042091 = 3063137) B3063137
theorem B9441893 : Blo 2041435 9441893 := bbase (se 4 (by rfl) ⟨885177, by rfl⟩ : syracuseStep 9441893 = 1770355) (by norm_num)
theorem B25178381 : Blo 2041435 25178381 := bstep (se 3 (by rfl) ⟨4720946, by rfl⟩ : syracuseStep 25178381 = 9441893) B9441893
theorem B16785587 : Blo 2041435 16785587 := bstep (se 1 (by rfl) ⟨12589190, by rfl⟩ : syracuseStep 16785587 = 25178381) B25178381
theorem B44761565 : Blo 2041435 44761565 := bstep (se 3 (by rfl) ⟨8392793, by rfl⟩ : syracuseStep 44761565 = 16785587) B16785587
theorem B29841043 : Blo 2041435 29841043 := bstep (se 1 (by rfl) ⟨22380782, by rfl⟩ : syracuseStep 29841043 = 44761565) B44761565
theorem B39788057 : Blo 2041435 39788057 := bstep (se 2 (by rfl) ⟨14920521, by rfl⟩ : syracuseStep 39788057 = 29841043) B29841043
theorem B106101485 : Blo 2041435 106101485 := bstep (se 3 (by rfl) ⟨19894028, by rfl⟩ : syracuseStep 106101485 = 39788057) B39788057
theorem B70734323 : Blo 2041435 70734323 := bstep (se 1 (by rfl) ⟨53050742, by rfl⟩ : syracuseStep 70734323 = 106101485) B106101485
theorem B47156215 : Blo 2041435 47156215 := bstep (se 1 (by rfl) ⟨35367161, by rfl⟩ : syracuseStep 47156215 = 70734323) B70734323
theorem B62874953 : Blo 2041435 62874953 := bstep (se 2 (by rfl) ⟨23578107, by rfl⟩ : syracuseStep 62874953 = 47156215) B47156215
theorem B41916635 : Blo 2041435 41916635 := bstep (se 1 (by rfl) ⟨31437476, by rfl⟩ : syracuseStep 41916635 = 62874953) B62874953
theorem B27944423 : Blo 2041435 27944423 := bstep (se 1 (by rfl) ⟨20958317, by rfl⟩ : syracuseStep 27944423 = 41916635) B41916635
theorem B18629615 : Blo 2041435 18629615 := bstep (se 1 (by rfl) ⟨13972211, by rfl⟩ : syracuseStep 18629615 = 27944423) B27944423
theorem B12419743 : Blo 2041435 12419743 := bstep (se 1 (by rfl) ⟨9314807, by rfl⟩ : syracuseStep 12419743 = 18629615) B18629615
theorem B16559657 : Blo 2041435 16559657 := bstep (se 2 (by rfl) ⟨6209871, by rfl⟩ : syracuseStep 16559657 = 12419743) B12419743
theorem B11039771 : Blo 2041435 11039771 := bstep (se 1 (by rfl) ⟨8279828, by rfl⟩ : syracuseStep 11039771 = 16559657) B16559657
theorem B29439389 : Blo 2041435 29439389 := bstep (se 3 (by rfl) ⟨5519885, by rfl⟩ : syracuseStep 29439389 = 11039771) B11039771
theorem B19626259 : Blo 2041435 19626259 := bstep (se 1 (by rfl) ⟨14719694, by rfl⟩ : syracuseStep 19626259 = 29439389) B29439389
theorem B26168345 : Blo 2041435 26168345 := bstep (se 2 (by rfl) ⟨9813129, by rfl⟩ : syracuseStep 26168345 = 19626259) B19626259
theorem B17445563 : Blo 2041435 17445563 := bstep (se 1 (by rfl) ⟨13084172, by rfl⟩ : syracuseStep 17445563 = 26168345) B26168345
theorem B11630375 : Blo 2041435 11630375 := bstep (se 1 (by rfl) ⟨8722781, by rfl⟩ : syracuseStep 11630375 = 17445563) B17445563
theorem B7753583 : Blo 2041435 7753583 := bstep (se 1 (by rfl) ⟨5815187, by rfl⟩ : syracuseStep 7753583 = 11630375) B11630375
theorem B5169055 : Blo 2041435 5169055 := bstep (se 1 (by rfl) ⟨3876791, by rfl⟩ : syracuseStep 5169055 = 7753583) B7753583
theorem B6892073 : Blo 2041435 6892073 := bstep (se 2 (by rfl) ⟨2584527, by rfl⟩ : syracuseStep 6892073 = 5169055) B5169055
theorem B4594715 : Blo 2041435 4594715 := bstep (se 1 (by rfl) ⟨3446036, by rfl⟩ : syracuseStep 4594715 = 6892073) B6892073
theorem B3063143 : Blo 2041435 3063143 := bstep (se 1 (by rfl) ⟨2297357, by rfl⟩ : syracuseStep 3063143 = 4594715) B4594715
theorem B2042095 : Blo 2041435 2042095 := bstep (se 1 (by rfl) ⟨1531571, by rfl⟩ : syracuseStep 2042095 = 3063143) B3063143
theorem B3063149 : Blo 2041435 3063149 := bbase (se 3 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 3063149 = 1148681) (by norm_num)
theorem B2042099 : Blo 2041435 2042099 := bstep (se 1 (by rfl) ⟨1531574, by rfl⟩ : syracuseStep 2042099 = 3063149) B3063149
theorem B4594733 : Blo 2041435 4594733 := bbase (se 3 (by rfl) ⟨861512, by rfl⟩ : syracuseStep 4594733 = 1723025) (by norm_num)
theorem B3063155 : Blo 2041435 3063155 := bstep (se 1 (by rfl) ⟨2297366, by rfl⟩ : syracuseStep 3063155 = 4594733) B4594733
theorem B2042103 : Blo 2041435 2042103 := bstep (se 1 (by rfl) ⟨1531577, by rfl⟩ : syracuseStep 2042103 = 3063155) B3063155
theorem B7359893 : Blo 2041435 7359893 := bbase (se 6 (by rfl) ⟨172497, by rfl⟩ : syracuseStep 7359893 = 344995) (by norm_num)
theorem B4906595 : Blo 2041435 4906595 := bstep (se 1 (by rfl) ⟨3679946, by rfl⟩ : syracuseStep 4906595 = 7359893) B7359893
theorem B13084253 : Blo 2041435 13084253 := bstep (se 3 (by rfl) ⟨2453297, by rfl⟩ : syracuseStep 13084253 = 4906595) B4906595
theorem B8722835 : Blo 2041435 8722835 := bstep (se 1 (by rfl) ⟨6542126, by rfl⟩ : syracuseStep 8722835 = 13084253) B13084253
theorem B5815223 : Blo 2041435 5815223 := bstep (se 1 (by rfl) ⟨4361417, by rfl⟩ : syracuseStep 5815223 = 8722835) B8722835
theorem B3876815 : Blo 2041435 3876815 := bstep (se 1 (by rfl) ⟨2907611, by rfl⟩ : syracuseStep 3876815 = 5815223) B5815223
theorem B2584543 : Blo 2041435 2584543 := bstep (se 1 (by rfl) ⟨1938407, by rfl⟩ : syracuseStep 2584543 = 3876815) B3876815
theorem B3446057 : Blo 2041435 3446057 := bstep (se 2 (by rfl) ⟨1292271, by rfl⟩ : syracuseStep 3446057 = 2584543) B2584543
theorem B2297371 : Blo 2041435 2297371 := bstep (se 1 (by rfl) ⟨1723028, by rfl⟩ : syracuseStep 2297371 = 3446057) B3446057
theorem B3063161 : Blo 2041435 3063161 := bstep (se 2 (by rfl) ⟨1148685, by rfl⟩ : syracuseStep 3063161 = 2297371) B2297371
theorem B2042107 : Blo 2041435 2042107 := bstep (se 1 (by rfl) ⟨1531580, by rfl⟩ : syracuseStep 2042107 = 3063161) B3063161
theorem B3929717 : Blo 2041435 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2619811 : Blo 2041435 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B3493081 : Blo 2041435 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B4657441 : Blo 2041435 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B6209921 : Blo 2041435 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B4139947 : Blo 2041435 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B5519929 : Blo 2041435 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B7359905 : Blo 2041435 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B4906603 : Blo 2041435 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B6542137 : Blo 2041435 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B34891397 : Blo 2041435 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B23260931 : Blo 2041435 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B15507287 : Blo 2041435 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B10338191 : Blo 2041435 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B6892127 : Blo 2041435 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B4594751 : Blo 2041435 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B3063167 : Blo 2041435 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B2042111 : Blo 2041435 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B3063173 : Blo 2041435 3063173 := bbase (se 4 (by rfl) ⟨287172, by rfl⟩ : syracuseStep 3063173 = 574345) (by norm_num)
theorem B2042115 : Blo 2041435 2042115 := bstep (se 1 (by rfl) ⟨1531586, by rfl⟩ : syracuseStep 2042115 = 3063173) B3063173
theorem B3446077 : Blo 2041435 3446077 := bbase (se 3 (by rfl) ⟨646139, by rfl⟩ : syracuseStep 3446077 = 1292279) (by norm_num)
theorem B4594769 : Blo 2041435 4594769 := bstep (se 2 (by rfl) ⟨1723038, by rfl⟩ : syracuseStep 4594769 = 3446077) B3446077
theorem B3063179 : Blo 2041435 3063179 := bstep (se 1 (by rfl) ⟨2297384, by rfl⟩ : syracuseStep 3063179 = 4594769) B4594769
theorem B2042119 : Blo 2041435 2042119 := bstep (se 1 (by rfl) ⟨1531589, by rfl⟩ : syracuseStep 2042119 = 3063179) B3063179
theorem B2297389 : Blo 2041435 2297389 := bbase (se 3 (by rfl) ⟨430760, by rfl⟩ : syracuseStep 2297389 = 861521) (by norm_num)
theorem B3063185 : Blo 2041435 3063185 := bstep (se 2 (by rfl) ⟨1148694, by rfl⟩ : syracuseStep 3063185 = 2297389) B2297389
theorem B2042123 : Blo 2041435 2042123 := bstep (se 1 (by rfl) ⟨1531592, by rfl⟩ : syracuseStep 2042123 = 3063185) B3063185
theorem B6892181 : Blo 2041435 6892181 := bbase (se 6 (by rfl) ⟨161535, by rfl⟩ : syracuseStep 6892181 = 323071) (by norm_num)
theorem B4594787 : Blo 2041435 4594787 := bstep (se 1 (by rfl) ⟨3446090, by rfl⟩ : syracuseStep 4594787 = 6892181) B6892181
theorem B3063191 : Blo 2041435 3063191 := bstep (se 1 (by rfl) ⟨2297393, by rfl⟩ : syracuseStep 3063191 = 4594787) B4594787
theorem B2042127 : Blo 2041435 2042127 := bstep (se 1 (by rfl) ⟨1531595, by rfl⟩ : syracuseStep 2042127 = 3063191) B3063191
theorem B3063197 : Blo 2041435 3063197 := bbase (se 3 (by rfl) ⟨574349, by rfl⟩ : syracuseStep 3063197 = 1148699) (by norm_num)
theorem B2042131 : Blo 2041435 2042131 := bstep (se 1 (by rfl) ⟨1531598, by rfl⟩ : syracuseStep 2042131 = 3063197) B3063197
theorem B4594805 : Blo 2041435 4594805 := bbase (se 5 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 4594805 = 430763) (by norm_num)
theorem B3063203 : Blo 2041435 3063203 := bstep (se 1 (by rfl) ⟨2297402, by rfl⟩ : syracuseStep 3063203 = 4594805) B4594805
theorem B2042135 : Blo 2041435 2042135 := bstep (se 1 (by rfl) ⟨1531601, by rfl⟩ : syracuseStep 2042135 = 3063203) B3063203
theorem B17445941 : Blo 2041435 17445941 := bbase (se 5 (by rfl) ⟨817778, by rfl⟩ : syracuseStep 17445941 = 1635557) (by norm_num)
theorem B11630627 : Blo 2041435 11630627 := bstep (se 1 (by rfl) ⟨8722970, by rfl⟩ : syracuseStep 11630627 = 17445941) B17445941
theorem B7753751 : Blo 2041435 7753751 := bstep (se 1 (by rfl) ⟨5815313, by rfl⟩ : syracuseStep 7753751 = 11630627) B11630627
theorem B5169167 : Blo 2041435 5169167 := bstep (se 1 (by rfl) ⟨3876875, by rfl⟩ : syracuseStep 5169167 = 7753751) B7753751
theorem B3446111 : Blo 2041435 3446111 := bstep (se 1 (by rfl) ⟨2584583, by rfl⟩ : syracuseStep 3446111 = 5169167) B5169167
theorem B2297407 : Blo 2041435 2297407 := bstep (se 1 (by rfl) ⟨1723055, by rfl⟩ : syracuseStep 2297407 = 3446111) B3446111
theorem B3063209 : Blo 2041435 3063209 := bstep (se 2 (by rfl) ⟨1148703, by rfl⟩ : syracuseStep 3063209 = 2297407) B2297407
theorem B2042139 : Blo 2041435 2042139 := bstep (se 1 (by rfl) ⟨1531604, by rfl⟩ : syracuseStep 2042139 = 3063209) B3063209
theorem B7753765 : Blo 2041435 7753765 := bbase (se 4 (by rfl) ⟨726915, by rfl⟩ : syracuseStep 7753765 = 1453831) (by norm_num)
theorem B10338353 : Blo 2041435 10338353 := bstep (se 2 (by rfl) ⟨3876882, by rfl⟩ : syracuseStep 10338353 = 7753765) B7753765
theorem B6892235 : Blo 2041435 6892235 := bstep (se 1 (by rfl) ⟨5169176, by rfl⟩ : syracuseStep 6892235 = 10338353) B10338353
theorem B4594823 : Blo 2041435 4594823 := bstep (se 1 (by rfl) ⟨3446117, by rfl⟩ : syracuseStep 4594823 = 6892235) B6892235
theorem B3063215 : Blo 2041435 3063215 := bstep (se 1 (by rfl) ⟨2297411, by rfl⟩ : syracuseStep 3063215 = 4594823) B4594823
theorem B2042143 : Blo 2041435 2042143 := bstep (se 1 (by rfl) ⟨1531607, by rfl⟩ : syracuseStep 2042143 = 3063215) B3063215
theorem B3063221 : Blo 2041435 3063221 := bbase (se 5 (by rfl) ⟨143588, by rfl⟩ : syracuseStep 3063221 = 287177) (by norm_num)
theorem B2042147 : Blo 2041435 2042147 := bstep (se 1 (by rfl) ⟨1531610, by rfl⟩ : syracuseStep 2042147 = 3063221) B3063221
theorem B5169197 : Blo 2041435 5169197 := bbase (se 3 (by rfl) ⟨969224, by rfl⟩ : syracuseStep 5169197 = 1938449) (by norm_num)
theorem B3446131 : Blo 2041435 3446131 := bstep (se 1 (by rfl) ⟨2584598, by rfl⟩ : syracuseStep 3446131 = 5169197) B5169197
theorem B4594841 : Blo 2041435 4594841 := bstep (se 2 (by rfl) ⟨1723065, by rfl⟩ : syracuseStep 4594841 = 3446131) B3446131
theorem B3063227 : Blo 2041435 3063227 := bstep (se 1 (by rfl) ⟨2297420, by rfl⟩ : syracuseStep 3063227 = 4594841) B4594841
theorem B2042151 : Blo 2041435 2042151 := bstep (se 1 (by rfl) ⟨1531613, by rfl⟩ : syracuseStep 2042151 = 3063227) B3063227
theorem B2297425 : Blo 2041435 2297425 := bbase (se 2 (by rfl) ⟨861534, by rfl⟩ : syracuseStep 2297425 = 1723069) (by norm_num)
theorem B3063233 : Blo 2041435 3063233 := bstep (se 2 (by rfl) ⟨1148712, by rfl⟩ : syracuseStep 3063233 = 2297425) B2297425
theorem B2042155 : Blo 2041435 2042155 := bstep (se 1 (by rfl) ⟨1531616, by rfl⟩ : syracuseStep 2042155 = 3063233) B3063233
theorem B2907685 : Blo 2041435 2907685 := bbase (se 4 (by rfl) ⟨272595, by rfl⟩ : syracuseStep 2907685 = 545191) (by norm_num)
theorem B3876913 : Blo 2041435 3876913 := bstep (se 2 (by rfl) ⟨1453842, by rfl⟩ : syracuseStep 3876913 = 2907685) B2907685
theorem B5169217 : Blo 2041435 5169217 := bstep (se 2 (by rfl) ⟨1938456, by rfl⟩ : syracuseStep 5169217 = 3876913) B3876913
theorem B6892289 : Blo 2041435 6892289 := bstep (se 2 (by rfl) ⟨2584608, by rfl⟩ : syracuseStep 6892289 = 5169217) B5169217
theorem B4594859 : Blo 2041435 4594859 := bstep (se 1 (by rfl) ⟨3446144, by rfl⟩ : syracuseStep 4594859 = 6892289) B6892289
theorem B3063239 : Blo 2041435 3063239 := bstep (se 1 (by rfl) ⟨2297429, by rfl⟩ : syracuseStep 3063239 = 4594859) B4594859
theorem B2042159 : Blo 2041435 2042159 := bstep (se 1 (by rfl) ⟨1531619, by rfl⟩ : syracuseStep 2042159 = 3063239) B3063239
theorem B3063245 : Blo 2041435 3063245 := bbase (se 3 (by rfl) ⟨574358, by rfl⟩ : syracuseStep 3063245 = 1148717) (by norm_num)
theorem B2042163 : Blo 2041435 2042163 := bstep (se 1 (by rfl) ⟨1531622, by rfl⟩ : syracuseStep 2042163 = 3063245) B3063245
theorem B4594877 : Blo 2041435 4594877 := bbase (se 3 (by rfl) ⟨861539, by rfl⟩ : syracuseStep 4594877 = 1723079) (by norm_num)
theorem B3063251 : Blo 2041435 3063251 := bstep (se 1 (by rfl) ⟨2297438, by rfl⟩ : syracuseStep 3063251 = 4594877) B4594877
theorem B2042167 : Blo 2041435 2042167 := bstep (se 1 (by rfl) ⟨1531625, by rfl⟩ : syracuseStep 2042167 = 3063251) B3063251
theorem B3446165 : Blo 2041435 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B2297443 : Blo 2041435 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B3063257 : Blo 2041435 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B2042171 : Blo 2041435 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B4906757 : Blo 2041435 4906757 := bbase (se 4 (by rfl) ⟨460008, by rfl⟩ : syracuseStep 4906757 = 920017) (by norm_num)
theorem B13084685 : Blo 2041435 13084685 := bstep (se 3 (by rfl) ⟨2453378, by rfl⟩ : syracuseStep 13084685 = 4906757) B4906757
theorem B8723123 : Blo 2041435 8723123 := bstep (se 1 (by rfl) ⟨6542342, by rfl⟩ : syracuseStep 8723123 = 13084685) B13084685
theorem B5815415 : Blo 2041435 5815415 := bstep (se 1 (by rfl) ⟨4361561, by rfl⟩ : syracuseStep 5815415 = 8723123) B8723123
theorem B15507773 : Blo 2041435 15507773 := bstep (se 3 (by rfl) ⟨2907707, by rfl⟩ : syracuseStep 15507773 = 5815415) B5815415
theorem B10338515 : Blo 2041435 10338515 := bstep (se 1 (by rfl) ⟨7753886, by rfl⟩ : syracuseStep 10338515 = 15507773) B15507773
theorem B6892343 : Blo 2041435 6892343 := bstep (se 1 (by rfl) ⟨5169257, by rfl⟩ : syracuseStep 6892343 = 10338515) B10338515
theorem B4594895 : Blo 2041435 4594895 := bstep (se 1 (by rfl) ⟨3446171, by rfl⟩ : syracuseStep 4594895 = 6892343) B6892343
theorem B3063263 : Blo 2041435 3063263 := bstep (se 1 (by rfl) ⟨2297447, by rfl⟩ : syracuseStep 3063263 = 4594895) B4594895
theorem B2042175 : Blo 2041435 2042175 := bstep (se 1 (by rfl) ⟨1531631, by rfl⟩ : syracuseStep 2042175 = 3063263) B3063263
theorem B3063269 : Blo 2041435 3063269 := bbase (se 4 (by rfl) ⟨287181, by rfl⟩ : syracuseStep 3063269 = 574363) (by norm_num)
theorem B2042179 : Blo 2041435 2042179 := bstep (se 1 (by rfl) ⟨1531634, by rfl⟩ : syracuseStep 2042179 = 3063269) B3063269
theorem B3147437 : Blo 2041435 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B8393165 : Blo 2041435 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B5595443 : Blo 2041435 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B3730295 : Blo 2041435 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B2486863 : Blo 2041435 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B3315817 : Blo 2041435 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B4421089 : Blo 2041435 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B5894785 : Blo 2041435 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B7859713 : Blo 2041435 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B10479617 : Blo 2041435 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B6986411 : Blo 2041435 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B4657607 : Blo 2041435 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B3105071 : Blo 2041435 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B2070047 : Blo 2041435 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B5520125 : Blo 2041435 5520125 := bstep (se 3 (by rfl) ⟨1035023, by rfl⟩ : syracuseStep 5520125 = 2070047) B2070047
theorem B3680083 : Blo 2041435 3680083 := bstep (se 1 (by rfl) ⟨2760062, by rfl⟩ : syracuseStep 3680083 = 5520125) B5520125
theorem B19627109 : Blo 2041435 19627109 := bstep (se 4 (by rfl) ⟨1840041, by rfl⟩ : syracuseStep 19627109 = 3680083) B3680083
theorem B13084739 : Blo 2041435 13084739 := bstep (se 1 (by rfl) ⟨9813554, by rfl⟩ : syracuseStep 13084739 = 19627109) B19627109
theorem B8723159 : Blo 2041435 8723159 := bstep (se 1 (by rfl) ⟨6542369, by rfl⟩ : syracuseStep 8723159 = 13084739) B13084739
theorem B5815439 : Blo 2041435 5815439 := bstep (se 1 (by rfl) ⟨4361579, by rfl⟩ : syracuseStep 5815439 = 8723159) B8723159
theorem B3876959 : Blo 2041435 3876959 := bstep (se 1 (by rfl) ⟨2907719, by rfl⟩ : syracuseStep 3876959 = 5815439) B5815439
theorem B2584639 : Blo 2041435 2584639 := bstep (se 1 (by rfl) ⟨1938479, by rfl⟩ : syracuseStep 2584639 = 3876959) B3876959
theorem B3446185 : Blo 2041435 3446185 := bstep (se 2 (by rfl) ⟨1292319, by rfl⟩ : syracuseStep 3446185 = 2584639) B2584639
theorem B4594913 : Blo 2041435 4594913 := bstep (se 2 (by rfl) ⟨1723092, by rfl⟩ : syracuseStep 4594913 = 3446185) B3446185
theorem B3063275 : Blo 2041435 3063275 := bstep (se 1 (by rfl) ⟨2297456, by rfl⟩ : syracuseStep 3063275 = 4594913) B4594913
theorem B2042183 : Blo 2041435 2042183 := bstep (se 1 (by rfl) ⟨1531637, by rfl⟩ : syracuseStep 2042183 = 3063275) B3063275
theorem B2297461 : Blo 2041435 2297461 := bbase (se 5 (by rfl) ⟨107693, by rfl⟩ : syracuseStep 2297461 = 215387) (by norm_num)
theorem B3063281 : Blo 2041435 3063281 := bstep (se 2 (by rfl) ⟨1148730, by rfl⟩ : syracuseStep 3063281 = 2297461) B2297461
theorem B2042187 : Blo 2041435 2042187 := bstep (se 1 (by rfl) ⟨1531640, by rfl⟩ : syracuseStep 2042187 = 3063281) B3063281
theorem B2584649 : Blo 2041435 2584649 := bbase (se 2 (by rfl) ⟨969243, by rfl⟩ : syracuseStep 2584649 = 1938487) (by norm_num)
theorem B6892397 : Blo 2041435 6892397 := bstep (se 3 (by rfl) ⟨1292324, by rfl⟩ : syracuseStep 6892397 = 2584649) B2584649
theorem B4594931 : Blo 2041435 4594931 := bstep (se 1 (by rfl) ⟨3446198, by rfl⟩ : syracuseStep 4594931 = 6892397) B6892397
theorem B3063287 : Blo 2041435 3063287 := bstep (se 1 (by rfl) ⟨2297465, by rfl⟩ : syracuseStep 3063287 = 4594931) B4594931
theorem B2042191 : Blo 2041435 2042191 := bstep (se 1 (by rfl) ⟨1531643, by rfl⟩ : syracuseStep 2042191 = 3063287) B3063287
theorem B3063293 : Blo 2041435 3063293 := bbase (se 3 (by rfl) ⟨574367, by rfl⟩ : syracuseStep 3063293 = 1148735) (by norm_num)
theorem B2042195 : Blo 2041435 2042195 := bstep (se 1 (by rfl) ⟨1531646, by rfl⟩ : syracuseStep 2042195 = 3063293) B3063293
theorem B4594949 : Blo 2041435 4594949 := bbase (se 4 (by rfl) ⟨430776, by rfl⟩ : syracuseStep 4594949 = 861553) (by norm_num)
theorem B3063299 : Blo 2041435 3063299 := bstep (se 1 (by rfl) ⟨2297474, by rfl⟩ : syracuseStep 3063299 = 4594949) B4594949
theorem B2042199 : Blo 2041435 2042199 := bstep (se 1 (by rfl) ⟨1531649, by rfl⟩ : syracuseStep 2042199 = 3063299) B3063299
theorem B3876997 : Blo 2041435 3876997 := bbase (se 4 (by rfl) ⟨363468, by rfl⟩ : syracuseStep 3876997 = 726937) (by norm_num)
theorem B5169329 : Blo 2041435 5169329 := bstep (se 2 (by rfl) ⟨1938498, by rfl⟩ : syracuseStep 5169329 = 3876997) B3876997
theorem B3446219 : Blo 2041435 3446219 := bstep (se 1 (by rfl) ⟨2584664, by rfl⟩ : syracuseStep 3446219 = 5169329) B5169329
theorem B2297479 : Blo 2041435 2297479 := bstep (se 1 (by rfl) ⟨1723109, by rfl⟩ : syracuseStep 2297479 = 3446219) B3446219
theorem B3063305 : Blo 2041435 3063305 := bstep (se 2 (by rfl) ⟨1148739, by rfl⟩ : syracuseStep 3063305 = 2297479) B2297479
theorem B2042203 : Blo 2041435 2042203 := bstep (se 1 (by rfl) ⟨1531652, by rfl⟩ : syracuseStep 2042203 = 3063305) B3063305
theorem B10338677 : Blo 2041435 10338677 := bbase (se 5 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 10338677 = 969251) (by norm_num)
theorem B6892451 : Blo 2041435 6892451 := bstep (se 1 (by rfl) ⟨5169338, by rfl⟩ : syracuseStep 6892451 = 10338677) B10338677
theorem B4594967 : Blo 2041435 4594967 := bstep (se 1 (by rfl) ⟨3446225, by rfl⟩ : syracuseStep 4594967 = 6892451) B6892451
theorem B3063311 : Blo 2041435 3063311 := bstep (se 1 (by rfl) ⟨2297483, by rfl⟩ : syracuseStep 3063311 = 4594967) B4594967
theorem B2042207 : Blo 2041435 2042207 := bstep (se 1 (by rfl) ⟨1531655, by rfl⟩ : syracuseStep 2042207 = 3063311) B3063311
theorem B3063317 : Blo 2041435 3063317 := bbase (se 6 (by rfl) ⟨71796, by rfl⟩ : syracuseStep 3063317 = 143593) (by norm_num)
theorem B2042211 : Blo 2041435 2042211 := bstep (se 1 (by rfl) ⟨1531658, by rfl⟩ : syracuseStep 2042211 = 3063317) B3063317
theorem B15719669 : Blo 2041435 15719669 := bbase (se 5 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 15719669 = 1473719) (by norm_num)
theorem B10479779 : Blo 2041435 10479779 := bstep (se 1 (by rfl) ⟨7859834, by rfl⟩ : syracuseStep 10479779 = 15719669) B15719669
theorem B6986519 : Blo 2041435 6986519 := bstep (se 1 (by rfl) ⟨5239889, by rfl⟩ : syracuseStep 6986519 = 10479779) B10479779
theorem B4657679 : Blo 2041435 4657679 := bstep (se 1 (by rfl) ⟨3493259, by rfl⟩ : syracuseStep 4657679 = 6986519) B6986519
theorem B3105119 : Blo 2041435 3105119 := bstep (se 1 (by rfl) ⟨2328839, by rfl⟩ : syracuseStep 3105119 = 4657679) B4657679
theorem B2070079 : Blo 2041435 2070079 := bstep (se 1 (by rfl) ⟨1552559, by rfl⟩ : syracuseStep 2070079 = 3105119) B3105119
theorem B11040421 : Blo 2041435 11040421 := bstep (se 4 (by rfl) ⟨1035039, by rfl⟩ : syracuseStep 11040421 = 2070079) B2070079
theorem B14720561 : Blo 2041435 14720561 := bstep (se 2 (by rfl) ⟨5520210, by rfl⟩ : syracuseStep 14720561 = 11040421) B11040421
theorem B9813707 : Blo 2041435 9813707 := bstep (se 1 (by rfl) ⟨7360280, by rfl⟩ : syracuseStep 9813707 = 14720561) B14720561
theorem B6542471 : Blo 2041435 6542471 := bstep (se 1 (by rfl) ⟨4906853, by rfl⟩ : syracuseStep 6542471 = 9813707) B9813707
theorem B17446589 : Blo 2041435 17446589 := bstep (se 3 (by rfl) ⟨3271235, by rfl⟩ : syracuseStep 17446589 = 6542471) B6542471
theorem B11631059 : Blo 2041435 11631059 := bstep (se 1 (by rfl) ⟨8723294, by rfl⟩ : syracuseStep 11631059 = 17446589) B17446589
theorem B7754039 : Blo 2041435 7754039 := bstep (se 1 (by rfl) ⟨5815529, by rfl⟩ : syracuseStep 7754039 = 11631059) B11631059
theorem B5169359 : Blo 2041435 5169359 := bstep (se 1 (by rfl) ⟨3877019, by rfl⟩ : syracuseStep 5169359 = 7754039) B7754039
theorem B3446239 : Blo 2041435 3446239 := bstep (se 1 (by rfl) ⟨2584679, by rfl⟩ : syracuseStep 3446239 = 5169359) B5169359
theorem B4594985 : Blo 2041435 4594985 := bstep (se 2 (by rfl) ⟨1723119, by rfl⟩ : syracuseStep 4594985 = 3446239) B3446239
theorem B3063323 : Blo 2041435 3063323 := bstep (se 1 (by rfl) ⟨2297492, by rfl⟩ : syracuseStep 3063323 = 4594985) B4594985
theorem B2042215 : Blo 2041435 2042215 := bstep (se 1 (by rfl) ⟨1531661, by rfl⟩ : syracuseStep 2042215 = 3063323) B3063323
theorem B2297497 : Blo 2041435 2297497 := bbase (se 2 (by rfl) ⟨861561, by rfl⟩ : syracuseStep 2297497 = 1723123) (by norm_num)
theorem B3063329 : Blo 2041435 3063329 := bstep (se 2 (by rfl) ⟨1148748, by rfl⟩ : syracuseStep 3063329 = 2297497) B2297497
theorem B2042219 : Blo 2041435 2042219 := bstep (se 1 (by rfl) ⟨1531664, by rfl⟩ : syracuseStep 2042219 = 3063329) B3063329
theorem B7754069 : Blo 2041435 7754069 := bbase (se 10 (by rfl) ⟨11358, by rfl⟩ : syracuseStep 7754069 = 22717) (by norm_num)
theorem B5169379 : Blo 2041435 5169379 := bstep (se 1 (by rfl) ⟨3877034, by rfl⟩ : syracuseStep 5169379 = 7754069) B7754069
theorem B6892505 : Blo 2041435 6892505 := bstep (se 2 (by rfl) ⟨2584689, by rfl⟩ : syracuseStep 6892505 = 5169379) B5169379
theorem B4595003 : Blo 2041435 4595003 := bstep (se 1 (by rfl) ⟨3446252, by rfl⟩ : syracuseStep 4595003 = 6892505) B6892505
theorem B3063335 : Blo 2041435 3063335 := bstep (se 1 (by rfl) ⟨2297501, by rfl⟩ : syracuseStep 3063335 = 4595003) B4595003
theorem B2042223 : Blo 2041435 2042223 := bstep (se 1 (by rfl) ⟨1531667, by rfl⟩ : syracuseStep 2042223 = 3063335) B3063335
theorem B3063341 : Blo 2041435 3063341 := bbase (se 3 (by rfl) ⟨574376, by rfl⟩ : syracuseStep 3063341 = 1148753) (by norm_num)
theorem B2042227 : Blo 2041435 2042227 := bstep (se 1 (by rfl) ⟨1531670, by rfl⟩ : syracuseStep 2042227 = 3063341) B3063341
theorem B4595021 : Blo 2041435 4595021 := bbase (se 3 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 4595021 = 1723133) (by norm_num)
theorem B3063347 : Blo 2041435 3063347 := bstep (se 1 (by rfl) ⟨2297510, by rfl⟩ : syracuseStep 3063347 = 4595021) B4595021
theorem B2042231 : Blo 2041435 2042231 := bstep (se 1 (by rfl) ⟨1531673, by rfl⟩ : syracuseStep 2042231 = 3063347) B3063347
theorem B2584705 : Blo 2041435 2584705 := bbase (se 2 (by rfl) ⟨969264, by rfl⟩ : syracuseStep 2584705 = 1938529) (by norm_num)
theorem B3446273 : Blo 2041435 3446273 := bstep (se 2 (by rfl) ⟨1292352, by rfl⟩ : syracuseStep 3446273 = 2584705) B2584705
theorem B2297515 : Blo 2041435 2297515 := bstep (se 1 (by rfl) ⟨1723136, by rfl⟩ : syracuseStep 2297515 = 3446273) B3446273
theorem B3063353 : Blo 2041435 3063353 := bstep (se 2 (by rfl) ⟨1148757, by rfl⟩ : syracuseStep 3063353 = 2297515) B2297515
theorem B2042235 : Blo 2041435 2042235 := bstep (se 1 (by rfl) ⟨1531676, by rfl⟩ : syracuseStep 2042235 = 3063353) B3063353
theorem B2180849 : Blo 2041435 2180849 := bbase (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) (by norm_num)
theorem B23262389 : Blo 2041435 23262389 := bstep (se 5 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 23262389 = 2180849) B2180849
theorem B15508259 : Blo 2041435 15508259 := bstep (se 1 (by rfl) ⟨11631194, by rfl⟩ : syracuseStep 15508259 = 23262389) B23262389
theorem B10338839 : Blo 2041435 10338839 := bstep (se 1 (by rfl) ⟨7754129, by rfl⟩ : syracuseStep 10338839 = 15508259) B15508259
theorem B6892559 : Blo 2041435 6892559 := bstep (se 1 (by rfl) ⟨5169419, by rfl⟩ : syracuseStep 6892559 = 10338839) B10338839
theorem B4595039 : Blo 2041435 4595039 := bstep (se 1 (by rfl) ⟨3446279, by rfl⟩ : syracuseStep 4595039 = 6892559) B6892559
theorem B3063359 : Blo 2041435 3063359 := bstep (se 1 (by rfl) ⟨2297519, by rfl⟩ : syracuseStep 3063359 = 4595039) B4595039
theorem B2042239 : Blo 2041435 2042239 := bstep (se 1 (by rfl) ⟨1531679, by rfl⟩ : syracuseStep 2042239 = 3063359) B3063359
theorem B3063365 : Blo 2041435 3063365 := bbase (se 4 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 3063365 = 574381) (by norm_num)
theorem B2042243 : Blo 2041435 2042243 := bstep (se 1 (by rfl) ⟨1531682, by rfl⟩ : syracuseStep 2042243 = 3063365) B3063365
theorem B3446293 : Blo 2041435 3446293 := bbase (se 6 (by rfl) ⟨80772, by rfl⟩ : syracuseStep 3446293 = 161545) (by norm_num)
theorem B4595057 : Blo 2041435 4595057 := bstep (se 2 (by rfl) ⟨1723146, by rfl⟩ : syracuseStep 4595057 = 3446293) B3446293
theorem B3063371 : Blo 2041435 3063371 := bstep (se 1 (by rfl) ⟨2297528, by rfl⟩ : syracuseStep 3063371 = 4595057) B4595057
theorem B2042247 : Blo 2041435 2042247 := bstep (se 1 (by rfl) ⟨1531685, by rfl⟩ : syracuseStep 2042247 = 3063371) B3063371
theorem B2297533 : Blo 2041435 2297533 := bbase (se 3 (by rfl) ⟨430787, by rfl⟩ : syracuseStep 2297533 = 861575) (by norm_num)
theorem B3063377 : Blo 2041435 3063377 := bstep (se 2 (by rfl) ⟨1148766, by rfl⟩ : syracuseStep 3063377 = 2297533) B2297533
theorem B2042251 : Blo 2041435 2042251 := bstep (se 1 (by rfl) ⟨1531688, by rfl⟩ : syracuseStep 2042251 = 3063377) B3063377
theorem B6892613 : Blo 2041435 6892613 := bbase (se 4 (by rfl) ⟨646182, by rfl⟩ : syracuseStep 6892613 = 1292365) (by norm_num)
theorem B4595075 : Blo 2041435 4595075 := bstep (se 1 (by rfl) ⟨3446306, by rfl⟩ : syracuseStep 4595075 = 6892613) B6892613
theorem B3063383 : Blo 2041435 3063383 := bstep (se 1 (by rfl) ⟨2297537, by rfl⟩ : syracuseStep 3063383 = 4595075) B4595075
theorem B2042255 : Blo 2041435 2042255 := bstep (se 1 (by rfl) ⟨1531691, by rfl⟩ : syracuseStep 2042255 = 3063383) B3063383
theorem B3063389 : Blo 2041435 3063389 := bbase (se 3 (by rfl) ⟨574385, by rfl⟩ : syracuseStep 3063389 = 1148771) (by norm_num)
theorem B2042259 : Blo 2041435 2042259 := bstep (se 1 (by rfl) ⟨1531694, by rfl⟩ : syracuseStep 2042259 = 3063389) B3063389
theorem B4595093 : Blo 2041435 4595093 := bbase (se 6 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 4595093 = 215395) (by norm_num)
theorem B3063395 : Blo 2041435 3063395 := bstep (se 1 (by rfl) ⟨2297546, by rfl⟩ : syracuseStep 3063395 = 4595093) B4595093
theorem B2042263 : Blo 2041435 2042263 := bstep (se 1 (by rfl) ⟨1531697, by rfl⟩ : syracuseStep 2042263 = 3063395) B3063395
theorem B2486965 : Blo 2041435 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B3315953 : Blo 2041435 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B2210635 : Blo 2041435 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B2947513 : Blo 2041435 2947513 := bstep (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) B2210635
theorem B3930017 : Blo 2041435 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B10480045 : Blo 2041435 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B13973393 : Blo 2041435 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B9315595 : Blo 2041435 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B12420793 : Blo 2041435 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B16561057 : Blo 2041435 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B22081409 : Blo 2041435 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B14720939 : Blo 2041435 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B9813959 : Blo 2041435 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B6542639 : Blo 2041435 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B4361759 : Blo 2041435 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B2907839 : Blo 2041435 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B7754237 : Blo 2041435 7754237 := bstep (se 3 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 7754237 = 2907839) B2907839
theorem B5169491 : Blo 2041435 5169491 := bstep (se 1 (by rfl) ⟨3877118, by rfl⟩ : syracuseStep 5169491 = 7754237) B7754237
theorem B3446327 : Blo 2041435 3446327 := bstep (se 1 (by rfl) ⟨2584745, by rfl⟩ : syracuseStep 3446327 = 5169491) B5169491
theorem B2297551 : Blo 2041435 2297551 := bstep (se 1 (by rfl) ⟨1723163, by rfl⟩ : syracuseStep 2297551 = 3446327) B3446327
theorem B3063401 : Blo 2041435 3063401 := bstep (se 2 (by rfl) ⟨1148775, by rfl⟩ : syracuseStep 3063401 = 2297551) B2297551
theorem B2042267 : Blo 2041435 2042267 := bstep (se 1 (by rfl) ⟨1531700, by rfl⟩ : syracuseStep 2042267 = 3063401) B3063401
theorem B3271325 : Blo 2041435 3271325 := bbase (se 3 (by rfl) ⟨613373, by rfl⟩ : syracuseStep 3271325 = 1226747) (by norm_num)
theorem B8723533 : Blo 2041435 8723533 := bstep (se 3 (by rfl) ⟨1635662, by rfl⟩ : syracuseStep 8723533 = 3271325) B3271325
theorem B11631377 : Blo 2041435 11631377 := bstep (se 2 (by rfl) ⟨4361766, by rfl⟩ : syracuseStep 11631377 = 8723533) B8723533
theorem B7754251 : Blo 2041435 7754251 := bstep (se 1 (by rfl) ⟨5815688, by rfl⟩ : syracuseStep 7754251 = 11631377) B11631377
theorem B10339001 : Blo 2041435 10339001 := bstep (se 2 (by rfl) ⟨3877125, by rfl⟩ : syracuseStep 10339001 = 7754251) B7754251
theorem B6892667 : Blo 2041435 6892667 := bstep (se 1 (by rfl) ⟨5169500, by rfl⟩ : syracuseStep 6892667 = 10339001) B10339001
theorem B4595111 : Blo 2041435 4595111 := bstep (se 1 (by rfl) ⟨3446333, by rfl⟩ : syracuseStep 4595111 = 6892667) B6892667
theorem B3063407 : Blo 2041435 3063407 := bstep (se 1 (by rfl) ⟨2297555, by rfl⟩ : syracuseStep 3063407 = 4595111) B4595111
theorem B2042271 : Blo 2041435 2042271 := bstep (se 1 (by rfl) ⟨1531703, by rfl⟩ : syracuseStep 2042271 = 3063407) B3063407
theorem B3063413 : Blo 2041435 3063413 := bbase (se 5 (by rfl) ⟨143597, by rfl⟩ : syracuseStep 3063413 = 287195) (by norm_num)
theorem B2042275 : Blo 2041435 2042275 := bstep (se 1 (by rfl) ⟨1531706, by rfl⟩ : syracuseStep 2042275 = 3063413) B3063413
theorem B3877141 : Blo 2041435 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B5169521 : Blo 2041435 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B3446347 : Blo 2041435 3446347 := bstep (se 1 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 3446347 = 5169521) B5169521
theorem B4595129 : Blo 2041435 4595129 := bstep (se 2 (by rfl) ⟨1723173, by rfl⟩ : syracuseStep 4595129 = 3446347) B3446347
theorem B3063419 : Blo 2041435 3063419 := bstep (se 1 (by rfl) ⟨2297564, by rfl⟩ : syracuseStep 3063419 = 4595129) B4595129
theorem B2042279 : Blo 2041435 2042279 := bstep (se 1 (by rfl) ⟨1531709, by rfl⟩ : syracuseStep 2042279 = 3063419) B3063419
theorem B2297569 : Blo 2041435 2297569 := bbase (se 2 (by rfl) ⟨861588, by rfl⟩ : syracuseStep 2297569 = 1723177) (by norm_num)
theorem B3063425 : Blo 2041435 3063425 := bstep (se 2 (by rfl) ⟨1148784, by rfl⟩ : syracuseStep 3063425 = 2297569) B2297569
theorem B2042283 : Blo 2041435 2042283 := bstep (se 1 (by rfl) ⟨1531712, by rfl⟩ : syracuseStep 2042283 = 3063425) B3063425
theorem B5169541 : Blo 2041435 5169541 := bbase (se 4 (by rfl) ⟨484644, by rfl⟩ : syracuseStep 5169541 = 969289) (by norm_num)
theorem B6892721 : Blo 2041435 6892721 := bstep (se 2 (by rfl) ⟨2584770, by rfl⟩ : syracuseStep 6892721 = 5169541) B5169541
theorem B4595147 : Blo 2041435 4595147 := bstep (se 1 (by rfl) ⟨3446360, by rfl⟩ : syracuseStep 4595147 = 6892721) B6892721
theorem B3063431 : Blo 2041435 3063431 := bstep (se 1 (by rfl) ⟨2297573, by rfl⟩ : syracuseStep 3063431 = 4595147) B4595147
theorem B2042287 : Blo 2041435 2042287 := bstep (se 1 (by rfl) ⟨1531715, by rfl⟩ : syracuseStep 2042287 = 3063431) B3063431
theorem B3063437 : Blo 2041435 3063437 := bbase (se 3 (by rfl) ⟨574394, by rfl⟩ : syracuseStep 3063437 = 1148789) (by norm_num)
theorem B2042291 : Blo 2041435 2042291 := bstep (se 1 (by rfl) ⟨1531718, by rfl⟩ : syracuseStep 2042291 = 3063437) B3063437
theorem B4595165 : Blo 2041435 4595165 := bbase (se 3 (by rfl) ⟨861593, by rfl⟩ : syracuseStep 4595165 = 1723187) (by norm_num)
theorem B3063443 : Blo 2041435 3063443 := bstep (se 1 (by rfl) ⟨2297582, by rfl⟩ : syracuseStep 3063443 = 4595165) B4595165
theorem B2042295 : Blo 2041435 2042295 := bstep (se 1 (by rfl) ⟨1531721, by rfl⟩ : syracuseStep 2042295 = 3063443) B3063443
theorem B3446381 : Blo 2041435 3446381 := bbase (se 3 (by rfl) ⟨646196, by rfl⟩ : syracuseStep 3446381 = 1292393) (by norm_num)
theorem B2297587 : Blo 2041435 2297587 := bstep (se 1 (by rfl) ⟨1723190, by rfl⟩ : syracuseStep 2297587 = 3446381) B3446381
theorem B3063449 : Blo 2041435 3063449 := bstep (se 2 (by rfl) ⟨1148793, by rfl⟩ : syracuseStep 3063449 = 2297587) B2297587
theorem B2042299 : Blo 2041435 2042299 := bstep (se 1 (by rfl) ⟨1531724, by rfl⟩ : syracuseStep 2042299 = 3063449) B3063449
theorem B3885293 : Blo 2041435 3885293 := bbase (se 3 (by rfl) ⟨728492, by rfl⟩ : syracuseStep 3885293 = 1456985) (by norm_num)
theorem B10360781 : Blo 2041435 10360781 := bstep (se 3 (by rfl) ⟨1942646, by rfl⟩ : syracuseStep 10360781 = 3885293) B3885293
theorem B6907187 : Blo 2041435 6907187 := bstep (se 1 (by rfl) ⟨5180390, by rfl⟩ : syracuseStep 6907187 = 10360781) B10360781
theorem B18419165 : Blo 2041435 18419165 := bstep (se 3 (by rfl) ⟨3453593, by rfl⟩ : syracuseStep 18419165 = 6907187) B6907187
theorem B12279443 : Blo 2041435 12279443 := bstep (se 1 (by rfl) ⟨9209582, by rfl⟩ : syracuseStep 12279443 = 18419165) B18419165
theorem B32745181 : Blo 2041435 32745181 := bstep (se 3 (by rfl) ⟨6139721, by rfl⟩ : syracuseStep 32745181 = 12279443) B12279443
theorem B43660241 : Blo 2041435 43660241 := bstep (se 2 (by rfl) ⟨16372590, by rfl⟩ : syracuseStep 43660241 = 32745181) B32745181
theorem B29106827 : Blo 2041435 29106827 := bstep (se 1 (by rfl) ⟨21830120, by rfl⟩ : syracuseStep 29106827 = 43660241) B43660241
theorem B19404551 : Blo 2041435 19404551 := bstep (se 1 (by rfl) ⟨14553413, by rfl⟩ : syracuseStep 19404551 = 29106827) B29106827
theorem B12936367 : Blo 2041435 12936367 := bstep (se 1 (by rfl) ⟨9702275, by rfl⟩ : syracuseStep 12936367 = 19404551) B19404551
theorem B68993957 : Blo 2041435 68993957 := bstep (se 4 (by rfl) ⟨6468183, by rfl⟩ : syracuseStep 68993957 = 12936367) B12936367
theorem B45995971 : Blo 2041435 45995971 := bstep (se 1 (by rfl) ⟨34496978, by rfl⟩ : syracuseStep 45995971 = 68993957) B68993957
theorem B61327961 : Blo 2041435 61327961 := bstep (se 2 (by rfl) ⟨22997985, by rfl⟩ : syracuseStep 61327961 = 45995971) B45995971
theorem B40885307 : Blo 2041435 40885307 := bstep (se 1 (by rfl) ⟨30663980, by rfl⟩ : syracuseStep 40885307 = 61327961) B61327961
theorem B27256871 : Blo 2041435 27256871 := bstep (se 1 (by rfl) ⟨20442653, by rfl⟩ : syracuseStep 27256871 = 40885307) B40885307
theorem B72684989 : Blo 2041435 72684989 := bstep (se 3 (by rfl) ⟨13628435, by rfl⟩ : syracuseStep 72684989 = 27256871) B27256871
theorem B48456659 : Blo 2041435 48456659 := bstep (se 1 (by rfl) ⟨36342494, by rfl⟩ : syracuseStep 48456659 = 72684989) B72684989
theorem B32304439 : Blo 2041435 32304439 := bstep (se 1 (by rfl) ⟨24228329, by rfl⟩ : syracuseStep 32304439 = 48456659) B48456659
theorem B172290341 : Blo 2041435 172290341 := bstep (se 4 (by rfl) ⟨16152219, by rfl⟩ : syracuseStep 172290341 = 32304439) B32304439
theorem B114860227 : Blo 2041435 114860227 := bstep (se 1 (by rfl) ⟨86145170, by rfl⟩ : syracuseStep 114860227 = 172290341) B172290341
theorem B153146969 : Blo 2041435 153146969 := bstep (se 2 (by rfl) ⟨57430113, by rfl⟩ : syracuseStep 153146969 = 114860227) B114860227
theorem B102097979 : Blo 2041435 102097979 := bstep (se 1 (by rfl) ⟨76573484, by rfl⟩ : syracuseStep 102097979 = 153146969) B153146969
theorem B68065319 : Blo 2041435 68065319 := bstep (se 1 (by rfl) ⟨51048989, by rfl⟩ : syracuseStep 68065319 = 102097979) B102097979
theorem B181507517 : Blo 2041435 181507517 := bstep (se 3 (by rfl) ⟨34032659, by rfl⟩ : syracuseStep 181507517 = 68065319) B68065319
theorem B121005011 : Blo 2041435 121005011 := bstep (se 1 (by rfl) ⟨90753758, by rfl⟩ : syracuseStep 121005011 = 181507517) B181507517
theorem B80670007 : Blo 2041435 80670007 := bstep (se 1 (by rfl) ⟨60502505, by rfl⟩ : syracuseStep 80670007 = 121005011) B121005011
theorem B107560009 : Blo 2041435 107560009 := bstep (se 2 (by rfl) ⟨40335003, by rfl⟩ : syracuseStep 107560009 = 80670007) B80670007
theorem B143413345 : Blo 2041435 143413345 := bstep (se 2 (by rfl) ⟨53780004, by rfl⟩ : syracuseStep 143413345 = 107560009) B107560009
theorem B191217793 : Blo 2041435 191217793 := bstep (se 2 (by rfl) ⟨71706672, by rfl⟩ : syracuseStep 191217793 = 143413345) B143413345
theorem B254957057 : Blo 2041435 254957057 := bstep (se 2 (by rfl) ⟨95608896, by rfl⟩ : syracuseStep 254957057 = 191217793) B191217793
theorem B169971371 : Blo 2041435 169971371 := bstep (se 1 (by rfl) ⟨127478528, by rfl⟩ : syracuseStep 169971371 = 254957057) B254957057
theorem B113314247 : Blo 2041435 113314247 := bstep (se 1 (by rfl) ⟨84985685, by rfl⟩ : syracuseStep 113314247 = 169971371) B169971371
theorem B75542831 : Blo 2041435 75542831 := bstep (se 1 (by rfl) ⟨56657123, by rfl⟩ : syracuseStep 75542831 = 113314247) B113314247
theorem B50361887 : Blo 2041435 50361887 := bstep (se 1 (by rfl) ⟨37771415, by rfl⟩ : syracuseStep 50361887 = 75542831) B75542831
theorem B33574591 : Blo 2041435 33574591 := bstep (se 1 (by rfl) ⟨25180943, by rfl⟩ : syracuseStep 33574591 = 50361887) B50361887
theorem B44766121 : Blo 2041435 44766121 := bstep (se 2 (by rfl) ⟨16787295, by rfl⟩ : syracuseStep 44766121 = 33574591) B33574591
theorem B59688161 : Blo 2041435 59688161 := bstep (se 2 (by rfl) ⟨22383060, by rfl⟩ : syracuseStep 59688161 = 44766121) B44766121
theorem B39792107 : Blo 2041435 39792107 := bstep (se 1 (by rfl) ⟨29844080, by rfl⟩ : syracuseStep 39792107 = 59688161) B59688161
theorem B26528071 : Blo 2041435 26528071 := bstep (se 1 (by rfl) ⟨19896053, by rfl⟩ : syracuseStep 26528071 = 39792107) B39792107
theorem B35370761 : Blo 2041435 35370761 := bstep (se 2 (by rfl) ⟨13264035, by rfl⟩ : syracuseStep 35370761 = 26528071) B26528071
theorem B94322029 : Blo 2041435 94322029 := bstep (se 3 (by rfl) ⟨17685380, by rfl⟩ : syracuseStep 94322029 = 35370761) B35370761
theorem B125762705 : Blo 2041435 125762705 := bstep (se 2 (by rfl) ⟨47161014, by rfl⟩ : syracuseStep 125762705 = 94322029) B94322029
theorem B83841803 : Blo 2041435 83841803 := bstep (se 1 (by rfl) ⟨62881352, by rfl⟩ : syracuseStep 83841803 = 125762705) B125762705
theorem B55894535 : Blo 2041435 55894535 := bstep (se 1 (by rfl) ⟨41920901, by rfl⟩ : syracuseStep 55894535 = 83841803) B83841803
theorem B37263023 : Blo 2041435 37263023 := bstep (se 1 (by rfl) ⟨27947267, by rfl⟩ : syracuseStep 37263023 = 55894535) B55894535
theorem B24842015 : Blo 2041435 24842015 := bstep (se 1 (by rfl) ⟨18631511, by rfl⟩ : syracuseStep 24842015 = 37263023) B37263023
theorem B16561343 : Blo 2041435 16561343 := bstep (se 1 (by rfl) ⟨12421007, by rfl⟩ : syracuseStep 16561343 = 24842015) B24842015
theorem B11040895 : Blo 2041435 11040895 := bstep (se 1 (by rfl) ⟨8280671, by rfl⟩ : syracuseStep 11040895 = 16561343) B16561343
theorem B14721193 : Blo 2041435 14721193 := bstep (se 2 (by rfl) ⟨5520447, by rfl⟩ : syracuseStep 14721193 = 11040895) B11040895
theorem B19628257 : Blo 2041435 19628257 := bstep (se 2 (by rfl) ⟨7360596, by rfl⟩ : syracuseStep 19628257 = 14721193) B14721193
theorem B26171009 : Blo 2041435 26171009 := bstep (se 2 (by rfl) ⟨9814128, by rfl⟩ : syracuseStep 26171009 = 19628257) B19628257
theorem B17447339 : Blo 2041435 17447339 := bstep (se 1 (by rfl) ⟨13085504, by rfl⟩ : syracuseStep 17447339 = 26171009) B26171009
theorem B11631559 : Blo 2041435 11631559 := bstep (se 1 (by rfl) ⟨8723669, by rfl⟩ : syracuseStep 11631559 = 17447339) B17447339
theorem B15508745 : Blo 2041435 15508745 := bstep (se 2 (by rfl) ⟨5815779, by rfl⟩ : syracuseStep 15508745 = 11631559) B11631559
theorem B10339163 : Blo 2041435 10339163 := bstep (se 1 (by rfl) ⟨7754372, by rfl⟩ : syracuseStep 10339163 = 15508745) B15508745
theorem B6892775 : Blo 2041435 6892775 := bstep (se 1 (by rfl) ⟨5169581, by rfl⟩ : syracuseStep 6892775 = 10339163) B10339163
theorem B4595183 : Blo 2041435 4595183 := bstep (se 1 (by rfl) ⟨3446387, by rfl⟩ : syracuseStep 4595183 = 6892775) B6892775
theorem B3063455 : Blo 2041435 3063455 := bstep (se 1 (by rfl) ⟨2297591, by rfl⟩ : syracuseStep 3063455 = 4595183) B4595183
theorem B2042303 : Blo 2041435 2042303 := bstep (se 1 (by rfl) ⟨1531727, by rfl⟩ : syracuseStep 2042303 = 3063455) B3063455
theorem B3063461 : Blo 2041435 3063461 := bbase (se 4 (by rfl) ⟨287199, by rfl⟩ : syracuseStep 3063461 = 574399) (by norm_num)
theorem B2042307 : Blo 2041435 2042307 := bstep (se 1 (by rfl) ⟨1531730, by rfl⟩ : syracuseStep 2042307 = 3063461) B3063461
theorem B2584801 : Blo 2041435 2584801 := bbase (se 2 (by rfl) ⟨969300, by rfl⟩ : syracuseStep 2584801 = 1938601) (by norm_num)
theorem B3446401 : Blo 2041435 3446401 := bstep (se 2 (by rfl) ⟨1292400, by rfl⟩ : syracuseStep 3446401 = 2584801) B2584801
theorem B4595201 : Blo 2041435 4595201 := bstep (se 2 (by rfl) ⟨1723200, by rfl⟩ : syracuseStep 4595201 = 3446401) B3446401
theorem B3063467 : Blo 2041435 3063467 := bstep (se 1 (by rfl) ⟨2297600, by rfl⟩ : syracuseStep 3063467 = 4595201) B4595201
theorem B2042311 : Blo 2041435 2042311 := bstep (se 1 (by rfl) ⟨1531733, by rfl⟩ : syracuseStep 2042311 = 3063467) B3063467
theorem B2297605 : Blo 2041435 2297605 := bbase (se 4 (by rfl) ⟨215400, by rfl⟩ : syracuseStep 2297605 = 430801) (by norm_num)
theorem B3063473 : Blo 2041435 3063473 := bstep (se 2 (by rfl) ⟨1148802, by rfl⟩ : syracuseStep 3063473 = 2297605) B2297605
theorem B2042315 : Blo 2041435 2042315 := bstep (se 1 (by rfl) ⟨1531736, by rfl⟩ : syracuseStep 2042315 = 3063473) B3063473
theorem B2487029 : Blo 2041435 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B26528309 : Blo 2041435 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B17685539 : Blo 2041435 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B11790359 : Blo 2041435 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B7860239 : Blo 2041435 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B5240159 : Blo 2041435 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B3493439 : Blo 2041435 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B2328959 : Blo 2041435 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B6210557 : Blo 2041435 6210557 := bstep (se 3 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 6210557 = 2328959) B2328959
theorem B4140371 : Blo 2041435 4140371 := bstep (se 1 (by rfl) ⟨3105278, by rfl⟩ : syracuseStep 4140371 = 6210557) B6210557
theorem B2760247 : Blo 2041435 2760247 := bstep (se 1 (by rfl) ⟨2070185, by rfl⟩ : syracuseStep 2760247 = 4140371) B4140371
theorem B3680329 : Blo 2041435 3680329 := bstep (se 2 (by rfl) ⟨1380123, by rfl⟩ : syracuseStep 3680329 = 2760247) B2760247
theorem B4907105 : Blo 2041435 4907105 := bstep (se 2 (by rfl) ⟨1840164, by rfl⟩ : syracuseStep 4907105 = 3680329) B3680329
theorem B3271403 : Blo 2041435 3271403 := bstep (se 1 (by rfl) ⟨2453552, by rfl⟩ : syracuseStep 3271403 = 4907105) B4907105
theorem B2180935 : Blo 2041435 2180935 := bstep (se 1 (by rfl) ⟨1635701, by rfl⟩ : syracuseStep 2180935 = 3271403) B3271403
theorem B2907913 : Blo 2041435 2907913 := bstep (se 2 (by rfl) ⟨1090467, by rfl⟩ : syracuseStep 2907913 = 2180935) B2180935
theorem B3877217 : Blo 2041435 3877217 := bstep (se 2 (by rfl) ⟨1453956, by rfl⟩ : syracuseStep 3877217 = 2907913) B2907913
theorem B2584811 : Blo 2041435 2584811 := bstep (se 1 (by rfl) ⟨1938608, by rfl⟩ : syracuseStep 2584811 = 3877217) B3877217
theorem B6892829 : Blo 2041435 6892829 := bstep (se 3 (by rfl) ⟨1292405, by rfl⟩ : syracuseStep 6892829 = 2584811) B2584811
theorem B4595219 : Blo 2041435 4595219 := bstep (se 1 (by rfl) ⟨3446414, by rfl⟩ : syracuseStep 4595219 = 6892829) B6892829
theorem B3063479 : Blo 2041435 3063479 := bstep (se 1 (by rfl) ⟨2297609, by rfl⟩ : syracuseStep 3063479 = 4595219) B4595219
theorem B2042319 : Blo 2041435 2042319 := bstep (se 1 (by rfl) ⟨1531739, by rfl⟩ : syracuseStep 2042319 = 3063479) B3063479
theorem B3063485 : Blo 2041435 3063485 := bbase (se 3 (by rfl) ⟨574403, by rfl⟩ : syracuseStep 3063485 = 1148807) (by norm_num)
theorem B2042323 : Blo 2041435 2042323 := bstep (se 1 (by rfl) ⟨1531742, by rfl⟩ : syracuseStep 2042323 = 3063485) B3063485
theorem B4595237 : Blo 2041435 4595237 := bbase (se 4 (by rfl) ⟨430803, by rfl⟩ : syracuseStep 4595237 = 861607) (by norm_num)
theorem B3063491 : Blo 2041435 3063491 := bstep (se 1 (by rfl) ⟨2297618, by rfl⟩ : syracuseStep 3063491 = 4595237) B4595237
theorem B2042327 : Blo 2041435 2042327 := bstep (se 1 (by rfl) ⟨1531745, by rfl⟩ : syracuseStep 2042327 = 3063491) B3063491
theorem B5169653 : Blo 2041435 5169653 := bbase (se 5 (by rfl) ⟨242327, by rfl⟩ : syracuseStep 5169653 = 484655) (by norm_num)
theorem B3446435 : Blo 2041435 3446435 := bstep (se 1 (by rfl) ⟨2584826, by rfl⟩ : syracuseStep 3446435 = 5169653) B5169653
theorem B2297623 : Blo 2041435 2297623 := bstep (se 1 (by rfl) ⟨1723217, by rfl⟩ : syracuseStep 2297623 = 3446435) B3446435
theorem B3063497 : Blo 2041435 3063497 := bstep (se 2 (by rfl) ⟨1148811, by rfl⟩ : syracuseStep 3063497 = 2297623) B2297623
theorem B2042331 : Blo 2041435 2042331 := bstep (se 1 (by rfl) ⟨1531748, by rfl⟩ : syracuseStep 2042331 = 3063497) B3063497
theorem B3105301 : Blo 2041435 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B4140401 : Blo 2041435 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B44164277 : Blo 2041435 44164277 := bstep (se 5 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 44164277 = 4140401) B4140401
theorem B29442851 : Blo 2041435 29442851 := bstep (se 1 (by rfl) ⟨22082138, by rfl⟩ : syracuseStep 29442851 = 44164277) B44164277
theorem B19628567 : Blo 2041435 19628567 := bstep (se 1 (by rfl) ⟨14721425, by rfl⟩ : syracuseStep 19628567 = 29442851) B29442851
theorem B13085711 : Blo 2041435 13085711 := bstep (se 1 (by rfl) ⟨9814283, by rfl⟩ : syracuseStep 13085711 = 19628567) B19628567
theorem B8723807 : Blo 2041435 8723807 := bstep (se 1 (by rfl) ⟨6542855, by rfl⟩ : syracuseStep 8723807 = 13085711) B13085711
theorem B5815871 : Blo 2041435 5815871 := bstep (se 1 (by rfl) ⟨4361903, by rfl⟩ : syracuseStep 5815871 = 8723807) B8723807
theorem B3877247 : Blo 2041435 3877247 := bstep (se 1 (by rfl) ⟨2907935, by rfl⟩ : syracuseStep 3877247 = 5815871) B5815871
theorem B10339325 : Blo 2041435 10339325 := bstep (se 3 (by rfl) ⟨1938623, by rfl⟩ : syracuseStep 10339325 = 3877247) B3877247
theorem B6892883 : Blo 2041435 6892883 := bstep (se 1 (by rfl) ⟨5169662, by rfl⟩ : syracuseStep 6892883 = 10339325) B10339325
theorem B4595255 : Blo 2041435 4595255 := bstep (se 1 (by rfl) ⟨3446441, by rfl⟩ : syracuseStep 4595255 = 6892883) B6892883
theorem B3063503 : Blo 2041435 3063503 := bstep (se 1 (by rfl) ⟨2297627, by rfl⟩ : syracuseStep 3063503 = 4595255) B4595255
theorem B2042335 : Blo 2041435 2042335 := bstep (se 1 (by rfl) ⟨1531751, by rfl⟩ : syracuseStep 2042335 = 3063503) B3063503
theorem B3063509 : Blo 2041435 3063509 := bbase (se 7 (by rfl) ⟨35900, by rfl⟩ : syracuseStep 3063509 = 71801) (by norm_num)
theorem B2042339 : Blo 2041435 2042339 := bstep (se 1 (by rfl) ⟨1531754, by rfl⟩ : syracuseStep 2042339 = 3063509) B3063509
theorem B2453581 : Blo 2041435 2453581 := bbase (se 3 (by rfl) ⟨460046, by rfl⟩ : syracuseStep 2453581 = 920093) (by norm_num)
theorem B3271441 : Blo 2041435 3271441 := bstep (se 2 (by rfl) ⟨1226790, by rfl⟩ : syracuseStep 3271441 = 2453581) B2453581
theorem B4361921 : Blo 2041435 4361921 := bstep (se 2 (by rfl) ⟨1635720, by rfl⟩ : syracuseStep 4361921 = 3271441) B3271441
theorem B2907947 : Blo 2041435 2907947 := bstep (se 1 (by rfl) ⟨2180960, by rfl⟩ : syracuseStep 2907947 = 4361921) B4361921
theorem B7754525 : Blo 2041435 7754525 := bstep (se 3 (by rfl) ⟨1453973, by rfl⟩ : syracuseStep 7754525 = 2907947) B2907947
theorem B5169683 : Blo 2041435 5169683 := bstep (se 1 (by rfl) ⟨3877262, by rfl⟩ : syracuseStep 5169683 = 7754525) B7754525
theorem B3446455 : Blo 2041435 3446455 := bstep (se 1 (by rfl) ⟨2584841, by rfl⟩ : syracuseStep 3446455 = 5169683) B5169683
theorem B4595273 : Blo 2041435 4595273 := bstep (se 2 (by rfl) ⟨1723227, by rfl⟩ : syracuseStep 4595273 = 3446455) B3446455
theorem B3063515 : Blo 2041435 3063515 := bstep (se 1 (by rfl) ⟨2297636, by rfl⟩ : syracuseStep 3063515 = 4595273) B4595273
theorem B2042343 : Blo 2041435 2042343 := bstep (se 1 (by rfl) ⟨1531757, by rfl⟩ : syracuseStep 2042343 = 3063515) B3063515
theorem B2297641 : Blo 2041435 2297641 := bbase (se 2 (by rfl) ⟨861615, by rfl⟩ : syracuseStep 2297641 = 1723231) (by norm_num)
theorem B3063521 : Blo 2041435 3063521 := bstep (se 2 (by rfl) ⟨1148820, by rfl⟩ : syracuseStep 3063521 = 2297641) B2297641
theorem B2042347 : Blo 2041435 2042347 := bstep (se 1 (by rfl) ⟨1531760, by rfl⟩ : syracuseStep 2042347 = 3063521) B3063521
theorem B13085813 : Blo 2041435 13085813 := bbase (se 5 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 13085813 = 1226795) (by norm_num)
theorem B8723875 : Blo 2041435 8723875 := bstep (se 1 (by rfl) ⟨6542906, by rfl⟩ : syracuseStep 8723875 = 13085813) B13085813
theorem B11631833 : Blo 2041435 11631833 := bstep (se 2 (by rfl) ⟨4361937, by rfl⟩ : syracuseStep 11631833 = 8723875) B8723875
theorem B7754555 : Blo 2041435 7754555 := bstep (se 1 (by rfl) ⟨5815916, by rfl⟩ : syracuseStep 7754555 = 11631833) B11631833
theorem B5169703 : Blo 2041435 5169703 := bstep (se 1 (by rfl) ⟨3877277, by rfl⟩ : syracuseStep 5169703 = 7754555) B7754555
theorem B6892937 : Blo 2041435 6892937 := bstep (se 2 (by rfl) ⟨2584851, by rfl⟩ : syracuseStep 6892937 = 5169703) B5169703
theorem B4595291 : Blo 2041435 4595291 := bstep (se 1 (by rfl) ⟨3446468, by rfl⟩ : syracuseStep 4595291 = 6892937) B6892937
theorem B3063527 : Blo 2041435 3063527 := bstep (se 1 (by rfl) ⟨2297645, by rfl⟩ : syracuseStep 3063527 = 4595291) B4595291
theorem B2042351 : Blo 2041435 2042351 := bstep (se 1 (by rfl) ⟨1531763, by rfl⟩ : syracuseStep 2042351 = 3063527) B3063527
theorem B3063533 : Blo 2041435 3063533 := bbase (se 3 (by rfl) ⟨574412, by rfl⟩ : syracuseStep 3063533 = 1148825) (by norm_num)
theorem B2042355 : Blo 2041435 2042355 := bstep (se 1 (by rfl) ⟨1531766, by rfl⟩ : syracuseStep 2042355 = 3063533) B3063533
theorem B4595309 : Blo 2041435 4595309 := bbase (se 3 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 4595309 = 1723241) (by norm_num)
theorem B3063539 : Blo 2041435 3063539 := bstep (se 1 (by rfl) ⟨2297654, by rfl⟩ : syracuseStep 3063539 = 4595309) B4595309
theorem B2042359 : Blo 2041435 2042359 := bstep (se 1 (by rfl) ⟨1531769, by rfl⟩ : syracuseStep 2042359 = 3063539) B3063539
theorem B3877301 : Blo 2041435 3877301 := bbase (se 5 (by rfl) ⟨181748, by rfl⟩ : syracuseStep 3877301 = 363497) (by norm_num)
theorem B2584867 : Blo 2041435 2584867 := bstep (se 1 (by rfl) ⟨1938650, by rfl⟩ : syracuseStep 2584867 = 3877301) B3877301
theorem B3446489 : Blo 2041435 3446489 := bstep (se 2 (by rfl) ⟨1292433, by rfl⟩ : syracuseStep 3446489 = 2584867) B2584867
theorem B2297659 : Blo 2041435 2297659 := bstep (se 1 (by rfl) ⟨1723244, by rfl⟩ : syracuseStep 2297659 = 3446489) B3446489
theorem B3063545 : Blo 2041435 3063545 := bstep (se 2 (by rfl) ⟨1148829, by rfl⟩ : syracuseStep 3063545 = 2297659) B2297659
theorem B2042363 : Blo 2041435 2042363 := bstep (se 1 (by rfl) ⟨1531772, by rfl⟩ : syracuseStep 2042363 = 3063545) B3063545
theorem B5595941 : Blo 2041435 5595941 := bbase (se 4 (by rfl) ⟨524619, by rfl⟩ : syracuseStep 5595941 = 1049239) (by norm_num)
theorem B3730627 : Blo 2041435 3730627 := bstep (se 1 (by rfl) ⟨2797970, by rfl⟩ : syracuseStep 3730627 = 5595941) B5595941
theorem B19896677 : Blo 2041435 19896677 := bstep (se 4 (by rfl) ⟨1865313, by rfl⟩ : syracuseStep 19896677 = 3730627) B3730627
theorem B13264451 : Blo 2041435 13264451 := bstep (se 1 (by rfl) ⟨9948338, by rfl⟩ : syracuseStep 13264451 = 19896677) B19896677
theorem B8842967 : Blo 2041435 8842967 := bstep (se 1 (by rfl) ⟨6632225, by rfl⟩ : syracuseStep 8842967 = 13264451) B13264451
theorem B5895311 : Blo 2041435 5895311 := bstep (se 1 (by rfl) ⟨4421483, by rfl⟩ : syracuseStep 5895311 = 8842967) B8842967
theorem B62883317 : Blo 2041435 62883317 := bstep (se 5 (by rfl) ⟨2947655, by rfl⟩ : syracuseStep 62883317 = 5895311) B5895311
theorem B41922211 : Blo 2041435 41922211 := bstep (se 1 (by rfl) ⟨31441658, by rfl⟩ : syracuseStep 41922211 = 62883317) B62883317
theorem B55896281 : Blo 2041435 55896281 := bstep (se 2 (by rfl) ⟨20961105, by rfl⟩ : syracuseStep 55896281 = 41922211) B41922211
theorem B37264187 : Blo 2041435 37264187 := bstep (se 1 (by rfl) ⟨27948140, by rfl⟩ : syracuseStep 37264187 = 55896281) B55896281
theorem B24842791 : Blo 2041435 24842791 := bstep (se 1 (by rfl) ⟨18632093, by rfl⟩ : syracuseStep 24842791 = 37264187) B37264187
theorem B132494885 : Blo 2041435 132494885 := bstep (se 4 (by rfl) ⟨12421395, by rfl⟩ : syracuseStep 132494885 = 24842791) B24842791
theorem B88329923 : Blo 2041435 88329923 := bstep (se 1 (by rfl) ⟨66247442, by rfl⟩ : syracuseStep 88329923 = 132494885) B132494885
theorem B58886615 : Blo 2041435 58886615 := bstep (se 1 (by rfl) ⟨44164961, by rfl⟩ : syracuseStep 58886615 = 88329923) B88329923
theorem B39257743 : Blo 2041435 39257743 := bstep (se 1 (by rfl) ⟨29443307, by rfl⟩ : syracuseStep 39257743 = 58886615) B58886615
theorem B52343657 : Blo 2041435 52343657 := bstep (se 2 (by rfl) ⟨19628871, by rfl⟩ : syracuseStep 52343657 = 39257743) B39257743
theorem B34895771 : Blo 2041435 34895771 := bstep (se 1 (by rfl) ⟨26171828, by rfl⟩ : syracuseStep 34895771 = 52343657) B52343657
theorem B23263847 : Blo 2041435 23263847 := bstep (se 1 (by rfl) ⟨17447885, by rfl⟩ : syracuseStep 23263847 = 34895771) B34895771
theorem B15509231 : Blo 2041435 15509231 := bstep (se 1 (by rfl) ⟨11631923, by rfl⟩ : syracuseStep 15509231 = 23263847) B23263847
theorem B10339487 : Blo 2041435 10339487 := bstep (se 1 (by rfl) ⟨7754615, by rfl⟩ : syracuseStep 10339487 = 15509231) B15509231
theorem B6892991 : Blo 2041435 6892991 := bstep (se 1 (by rfl) ⟨5169743, by rfl⟩ : syracuseStep 6892991 = 10339487) B10339487
theorem B4595327 : Blo 2041435 4595327 := bstep (se 1 (by rfl) ⟨3446495, by rfl⟩ : syracuseStep 4595327 = 6892991) B6892991
theorem B3063551 : Blo 2041435 3063551 := bstep (se 1 (by rfl) ⟨2297663, by rfl⟩ : syracuseStep 3063551 = 4595327) B4595327
theorem B2042367 : Blo 2041435 2042367 := bstep (se 1 (by rfl) ⟨1531775, by rfl⟩ : syracuseStep 2042367 = 3063551) B3063551
theorem B3063557 : Blo 2041435 3063557 := bbase (se 4 (by rfl) ⟨287208, by rfl⟩ : syracuseStep 3063557 = 574417) (by norm_num)
theorem B2042371 : Blo 2041435 2042371 := bstep (se 1 (by rfl) ⟨1531778, by rfl⟩ : syracuseStep 2042371 = 3063557) B3063557
theorem B3446509 : Blo 2041435 3446509 := bbase (se 3 (by rfl) ⟨646220, by rfl⟩ : syracuseStep 3446509 = 1292441) (by norm_num)
theorem B4595345 : Blo 2041435 4595345 := bstep (se 2 (by rfl) ⟨1723254, by rfl⟩ : syracuseStep 4595345 = 3446509) B3446509
theorem B3063563 : Blo 2041435 3063563 := bstep (se 1 (by rfl) ⟨2297672, by rfl⟩ : syracuseStep 3063563 = 4595345) B4595345
theorem B2042375 : Blo 2041435 2042375 := bstep (se 1 (by rfl) ⟨1531781, by rfl⟩ : syracuseStep 2042375 = 3063563) B3063563
theorem B2297677 : Blo 2041435 2297677 := bbase (se 3 (by rfl) ⟨430814, by rfl⟩ : syracuseStep 2297677 = 861629) (by norm_num)
theorem B3063569 : Blo 2041435 3063569 := bstep (se 2 (by rfl) ⟨1148838, by rfl⟩ : syracuseStep 3063569 = 2297677) B2297677
theorem B2042379 : Blo 2041435 2042379 := bstep (se 1 (by rfl) ⟨1531784, by rfl⟩ : syracuseStep 2042379 = 3063569) B3063569
theorem B6893045 : Blo 2041435 6893045 := bbase (se 5 (by rfl) ⟨323111, by rfl⟩ : syracuseStep 6893045 = 646223) (by norm_num)
theorem B4595363 : Blo 2041435 4595363 := bstep (se 1 (by rfl) ⟨3446522, by rfl⟩ : syracuseStep 4595363 = 6893045) B6893045
theorem B3063575 : Blo 2041435 3063575 := bstep (se 1 (by rfl) ⟨2297681, by rfl⟩ : syracuseStep 3063575 = 4595363) B4595363
theorem B2042383 : Blo 2041435 2042383 := bstep (se 1 (by rfl) ⟨1531787, by rfl⟩ : syracuseStep 2042383 = 3063575) B3063575
theorem B3063581 : Blo 2041435 3063581 := bbase (se 3 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 3063581 = 1148843) (by norm_num)
theorem B2042387 : Blo 2041435 2042387 := bstep (se 1 (by rfl) ⟨1531790, by rfl⟩ : syracuseStep 2042387 = 3063581) B3063581
theorem B4595381 : Blo 2041435 4595381 := bbase (se 5 (by rfl) ⟨215408, by rfl⟩ : syracuseStep 4595381 = 430817) (by norm_num)
theorem B3063587 : Blo 2041435 3063587 := bstep (se 1 (by rfl) ⟨2297690, by rfl⟩ : syracuseStep 3063587 = 4595381) B4595381
theorem B2042391 : Blo 2041435 2042391 := bstep (se 1 (by rfl) ⟨1531793, by rfl⟩ : syracuseStep 2042391 = 3063587) B3063587
theorem B11632085 : Blo 2041435 11632085 := bbase (se 7 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 11632085 = 272627) (by norm_num)
theorem B7754723 : Blo 2041435 7754723 := bstep (se 1 (by rfl) ⟨5816042, by rfl⟩ : syracuseStep 7754723 = 11632085) B11632085
theorem B5169815 : Blo 2041435 5169815 := bstep (se 1 (by rfl) ⟨3877361, by rfl⟩ : syracuseStep 5169815 = 7754723) B7754723
theorem B3446543 : Blo 2041435 3446543 := bstep (se 1 (by rfl) ⟨2584907, by rfl⟩ : syracuseStep 3446543 = 5169815) B5169815
theorem B2297695 : Blo 2041435 2297695 := bstep (se 1 (by rfl) ⟨1723271, by rfl⟩ : syracuseStep 2297695 = 3446543) B3446543
theorem B3063593 : Blo 2041435 3063593 := bstep (se 2 (by rfl) ⟨1148847, by rfl⟩ : syracuseStep 3063593 = 2297695) B2297695
theorem B2042395 : Blo 2041435 2042395 := bstep (se 1 (by rfl) ⟨1531796, by rfl⟩ : syracuseStep 2042395 = 3063593) B3063593
theorem B5816053 : Blo 2041435 5816053 := bbase (se 5 (by rfl) ⟨272627, by rfl⟩ : syracuseStep 5816053 = 545255) (by norm_num)
theorem B7754737 : Blo 2041435 7754737 := bstep (se 2 (by rfl) ⟨2908026, by rfl⟩ : syracuseStep 7754737 = 5816053) B5816053
theorem B10339649 : Blo 2041435 10339649 := bstep (se 2 (by rfl) ⟨3877368, by rfl⟩ : syracuseStep 10339649 = 7754737) B7754737
theorem B6893099 : Blo 2041435 6893099 := bstep (se 1 (by rfl) ⟨5169824, by rfl⟩ : syracuseStep 6893099 = 10339649) B10339649
theorem B4595399 : Blo 2041435 4595399 := bstep (se 1 (by rfl) ⟨3446549, by rfl⟩ : syracuseStep 4595399 = 6893099) B6893099
theorem B3063599 : Blo 2041435 3063599 := bstep (se 1 (by rfl) ⟨2297699, by rfl⟩ : syracuseStep 3063599 = 4595399) B4595399
theorem B2042399 : Blo 2041435 2042399 := bstep (se 1 (by rfl) ⟨1531799, by rfl⟩ : syracuseStep 2042399 = 3063599) B3063599
theorem B3063605 : Blo 2041435 3063605 := bbase (se 5 (by rfl) ⟨143606, by rfl⟩ : syracuseStep 3063605 = 287213) (by norm_num)
theorem B2042403 : Blo 2041435 2042403 := bstep (se 1 (by rfl) ⟨1531802, by rfl⟩ : syracuseStep 2042403 = 3063605) B3063605
theorem B5169845 : Blo 2041435 5169845 := bbase (se 5 (by rfl) ⟨242336, by rfl⟩ : syracuseStep 5169845 = 484673) (by norm_num)
theorem B3446563 : Blo 2041435 3446563 := bstep (se 1 (by rfl) ⟨2584922, by rfl⟩ : syracuseStep 3446563 = 5169845) B5169845
theorem B4595417 : Blo 2041435 4595417 := bstep (se 2 (by rfl) ⟨1723281, by rfl⟩ : syracuseStep 4595417 = 3446563) B3446563
theorem B3063611 : Blo 2041435 3063611 := bstep (se 1 (by rfl) ⟨2297708, by rfl⟩ : syracuseStep 3063611 = 4595417) B4595417
theorem B2042407 : Blo 2041435 2042407 := bstep (se 1 (by rfl) ⟨1531805, by rfl⟩ : syracuseStep 2042407 = 3063611) B3063611
theorem B2297713 : Blo 2041435 2297713 := bbase (se 2 (by rfl) ⟨861642, by rfl⟩ : syracuseStep 2297713 = 1723285) (by norm_num)
theorem B3063617 : Blo 2041435 3063617 := bstep (se 2 (by rfl) ⟨1148856, by rfl⟩ : syracuseStep 3063617 = 2297713) B2297713
theorem B2042411 : Blo 2041435 2042411 := bstep (se 1 (by rfl) ⟨1531808, by rfl⟩ : syracuseStep 2042411 = 3063617) B3063617
theorem B8724149 : Blo 2041435 8724149 := bbase (se 5 (by rfl) ⟨408944, by rfl⟩ : syracuseStep 8724149 = 817889) (by norm_num)
theorem B5816099 : Blo 2041435 5816099 := bstep (se 1 (by rfl) ⟨4362074, by rfl⟩ : syracuseStep 5816099 = 8724149) B8724149
theorem B3877399 : Blo 2041435 3877399 := bstep (se 1 (by rfl) ⟨2908049, by rfl⟩ : syracuseStep 3877399 = 5816099) B5816099
theorem B5169865 : Blo 2041435 5169865 := bstep (se 2 (by rfl) ⟨1938699, by rfl⟩ : syracuseStep 5169865 = 3877399) B3877399
theorem B6893153 : Blo 2041435 6893153 := bstep (se 2 (by rfl) ⟨2584932, by rfl⟩ : syracuseStep 6893153 = 5169865) B5169865
theorem B4595435 : Blo 2041435 4595435 := bstep (se 1 (by rfl) ⟨3446576, by rfl⟩ : syracuseStep 4595435 = 6893153) B6893153
theorem B3063623 : Blo 2041435 3063623 := bstep (se 1 (by rfl) ⟨2297717, by rfl⟩ : syracuseStep 3063623 = 4595435) B4595435
theorem B2042415 : Blo 2041435 2042415 := bstep (se 1 (by rfl) ⟨1531811, by rfl⟩ : syracuseStep 2042415 = 3063623) B3063623
theorem B3063629 : Blo 2041435 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B2042419 : Blo 2041435 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B4595453 : Blo 2041435 4595453 := bbase (se 3 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 4595453 = 1723295) (by norm_num)
theorem B3063635 : Blo 2041435 3063635 := bstep (se 1 (by rfl) ⟨2297726, by rfl⟩ : syracuseStep 3063635 = 4595453) B4595453
theorem B2042423 : Blo 2041435 2042423 := bstep (se 1 (by rfl) ⟨1531817, by rfl⟩ : syracuseStep 2042423 = 3063635) B3063635
theorem B3446597 : Blo 2041435 3446597 := bbase (se 4 (by rfl) ⟨323118, by rfl⟩ : syracuseStep 3446597 = 646237) (by norm_num)
theorem B2297731 : Blo 2041435 2297731 := bstep (se 1 (by rfl) ⟨1723298, by rfl⟩ : syracuseStep 2297731 = 3446597) B3446597
theorem B3063641 : Blo 2041435 3063641 := bstep (se 2 (by rfl) ⟨1148865, by rfl⟩ : syracuseStep 3063641 = 2297731) B2297731
theorem B2042427 : Blo 2041435 2042427 := bstep (se 1 (by rfl) ⟨1531820, by rfl⟩ : syracuseStep 2042427 = 3063641) B3063641
theorem B15509717 : Blo 2041435 15509717 := bbase (se 7 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 15509717 = 363509) (by norm_num)
theorem B10339811 : Blo 2041435 10339811 := bstep (se 1 (by rfl) ⟨7754858, by rfl⟩ : syracuseStep 10339811 = 15509717) B15509717
theorem B6893207 : Blo 2041435 6893207 := bstep (se 1 (by rfl) ⟨5169905, by rfl⟩ : syracuseStep 6893207 = 10339811) B10339811
theorem B4595471 : Blo 2041435 4595471 := bstep (se 1 (by rfl) ⟨3446603, by rfl⟩ : syracuseStep 4595471 = 6893207) B6893207
theorem B3063647 : Blo 2041435 3063647 := bstep (se 1 (by rfl) ⟨2297735, by rfl⟩ : syracuseStep 3063647 = 4595471) B4595471
theorem B2042431 : Blo 2041435 2042431 := bstep (se 1 (by rfl) ⟨1531823, by rfl⟩ : syracuseStep 2042431 = 3063647) B3063647
theorem B3063653 : Blo 2041435 3063653 := bbase (se 4 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 3063653 = 574435) (by norm_num)
theorem B2042435 : Blo 2041435 2042435 := bstep (se 1 (by rfl) ⟨1531826, by rfl⟩ : syracuseStep 2042435 = 3063653) B3063653
theorem B3877445 : Blo 2041435 3877445 := bbase (se 4 (by rfl) ⟨363510, by rfl⟩ : syracuseStep 3877445 = 727021) (by norm_num)
theorem B2584963 : Blo 2041435 2584963 := bstep (se 1 (by rfl) ⟨1938722, by rfl⟩ : syracuseStep 2584963 = 3877445) B3877445
theorem B3446617 : Blo 2041435 3446617 := bstep (se 2 (by rfl) ⟨1292481, by rfl⟩ : syracuseStep 3446617 = 2584963) B2584963
theorem B4595489 : Blo 2041435 4595489 := bstep (se 2 (by rfl) ⟨1723308, by rfl⟩ : syracuseStep 4595489 = 3446617) B3446617
theorem B3063659 : Blo 2041435 3063659 := bstep (se 1 (by rfl) ⟨2297744, by rfl⟩ : syracuseStep 3063659 = 4595489) B4595489
theorem B2042439 : Blo 2041435 2042439 := bstep (se 1 (by rfl) ⟨1531829, by rfl⟩ : syracuseStep 2042439 = 3063659) B3063659
theorem B2297749 : Blo 2041435 2297749 := bbase (se 6 (by rfl) ⟨53853, by rfl⟩ : syracuseStep 2297749 = 107707) (by norm_num)
theorem B3063665 : Blo 2041435 3063665 := bstep (se 2 (by rfl) ⟨1148874, by rfl⟩ : syracuseStep 3063665 = 2297749) B2297749
theorem B2042443 : Blo 2041435 2042443 := bstep (se 1 (by rfl) ⟨1531832, by rfl⟩ : syracuseStep 2042443 = 3063665) B3063665
theorem B2584973 : Blo 2041435 2584973 := bbase (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) (by norm_num)
theorem B6893261 : Blo 2041435 6893261 := bstep (se 3 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 6893261 = 2584973) B2584973
theorem B4595507 : Blo 2041435 4595507 := bstep (se 1 (by rfl) ⟨3446630, by rfl⟩ : syracuseStep 4595507 = 6893261) B6893261
theorem B3063671 : Blo 2041435 3063671 := bstep (se 1 (by rfl) ⟨2297753, by rfl⟩ : syracuseStep 3063671 = 4595507) B4595507
theorem B2042447 : Blo 2041435 2042447 := bstep (se 1 (by rfl) ⟨1531835, by rfl⟩ : syracuseStep 2042447 = 3063671) B3063671
theorem B3063677 : Blo 2041435 3063677 := bbase (se 3 (by rfl) ⟨574439, by rfl⟩ : syracuseStep 3063677 = 1148879) (by norm_num)
theorem B2042451 : Blo 2041435 2042451 := bstep (se 1 (by rfl) ⟨1531838, by rfl⟩ : syracuseStep 2042451 = 3063677) B3063677
theorem B4595525 : Blo 2041435 4595525 := bbase (se 4 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 4595525 = 861661) (by norm_num)
theorem B3063683 : Blo 2041435 3063683 := bstep (se 1 (by rfl) ⟨2297762, by rfl⟩ : syracuseStep 3063683 = 4595525) B4595525
theorem B2042455 : Blo 2041435 2042455 := bstep (se 1 (by rfl) ⟨1531841, by rfl⟩ : syracuseStep 2042455 = 3063683) B3063683
theorem B3680581 : Blo 2041435 3680581 := bbase (se 4 (by rfl) ⟨345054, by rfl⟩ : syracuseStep 3680581 = 690109) (by norm_num)
theorem B4907441 : Blo 2041435 4907441 := bstep (se 2 (by rfl) ⟨1840290, by rfl⟩ : syracuseStep 4907441 = 3680581) B3680581
theorem B3271627 : Blo 2041435 3271627 := bstep (se 1 (by rfl) ⟨2453720, by rfl⟩ : syracuseStep 3271627 = 4907441) B4907441
theorem B4362169 : Blo 2041435 4362169 := bstep (se 2 (by rfl) ⟨1635813, by rfl⟩ : syracuseStep 4362169 = 3271627) B3271627
theorem B5816225 : Blo 2041435 5816225 := bstep (se 2 (by rfl) ⟨2181084, by rfl⟩ : syracuseStep 5816225 = 4362169) B4362169
theorem B3877483 : Blo 2041435 3877483 := bstep (se 1 (by rfl) ⟨2908112, by rfl⟩ : syracuseStep 3877483 = 5816225) B5816225
theorem B5169977 : Blo 2041435 5169977 := bstep (se 2 (by rfl) ⟨1938741, by rfl⟩ : syracuseStep 5169977 = 3877483) B3877483
theorem B3446651 : Blo 2041435 3446651 := bstep (se 1 (by rfl) ⟨2584988, by rfl⟩ : syracuseStep 3446651 = 5169977) B5169977
theorem B2297767 : Blo 2041435 2297767 := bstep (se 1 (by rfl) ⟨1723325, by rfl⟩ : syracuseStep 2297767 = 3446651) B3446651
theorem B3063689 : Blo 2041435 3063689 := bstep (se 2 (by rfl) ⟨1148883, by rfl⟩ : syracuseStep 3063689 = 2297767) B2297767
theorem B2042459 : Blo 2041435 2042459 := bstep (se 1 (by rfl) ⟨1531844, by rfl⟩ : syracuseStep 2042459 = 3063689) B3063689
theorem B10339973 : Blo 2041435 10339973 := bbase (se 4 (by rfl) ⟨969372, by rfl⟩ : syracuseStep 10339973 = 1938745) (by norm_num)
theorem B6893315 : Blo 2041435 6893315 := bstep (se 1 (by rfl) ⟨5169986, by rfl⟩ : syracuseStep 6893315 = 10339973) B10339973
theorem B4595543 : Blo 2041435 4595543 := bstep (se 1 (by rfl) ⟨3446657, by rfl⟩ : syracuseStep 4595543 = 6893315) B6893315
theorem B3063695 : Blo 2041435 3063695 := bstep (se 1 (by rfl) ⟨2297771, by rfl⟩ : syracuseStep 3063695 = 4595543) B4595543
theorem B2042463 : Blo 2041435 2042463 := bstep (se 1 (by rfl) ⟨1531847, by rfl⟩ : syracuseStep 2042463 = 3063695) B3063695
theorem B3063701 : Blo 2041435 3063701 := bbase (se 6 (by rfl) ⟨71805, by rfl⟩ : syracuseStep 3063701 = 143611) (by norm_num)
theorem B2042467 : Blo 2041435 2042467 := bstep (se 1 (by rfl) ⟨1531850, by rfl⟩ : syracuseStep 2042467 = 3063701) B3063701
theorem B2181097 : Blo 2041435 2181097 := bbase (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) (by norm_num)
theorem B11632517 : Blo 2041435 11632517 := bstep (se 4 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 11632517 = 2181097) B2181097
theorem B7755011 : Blo 2041435 7755011 := bstep (se 1 (by rfl) ⟨5816258, by rfl⟩ : syracuseStep 7755011 = 11632517) B11632517
theorem B5170007 : Blo 2041435 5170007 := bstep (se 1 (by rfl) ⟨3877505, by rfl⟩ : syracuseStep 5170007 = 7755011) B7755011
theorem B3446671 : Blo 2041435 3446671 := bstep (se 1 (by rfl) ⟨2585003, by rfl⟩ : syracuseStep 3446671 = 5170007) B5170007
theorem B4595561 : Blo 2041435 4595561 := bstep (se 2 (by rfl) ⟨1723335, by rfl⟩ : syracuseStep 4595561 = 3446671) B3446671
theorem B3063707 : Blo 2041435 3063707 := bstep (se 1 (by rfl) ⟨2297780, by rfl⟩ : syracuseStep 3063707 = 4595561) B4595561
theorem B2042471 : Blo 2041435 2042471 := bstep (se 1 (by rfl) ⟨1531853, by rfl⟩ : syracuseStep 2042471 = 3063707) B3063707
theorem B2297785 : Blo 2041435 2297785 := bbase (se 2 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 2297785 = 1723339) (by norm_num)
theorem B3063713 : Blo 2041435 3063713 := bstep (se 2 (by rfl) ⟨1148892, by rfl⟩ : syracuseStep 3063713 = 2297785) B2297785
theorem B2042475 : Blo 2041435 2042475 := bstep (se 1 (by rfl) ⟨1531856, by rfl⟩ : syracuseStep 2042475 = 3063713) B3063713
theorem B6543317 : Blo 2041435 6543317 := bbase (se 7 (by rfl) ⟨76679, by rfl⟩ : syracuseStep 6543317 = 153359) (by norm_num)
theorem B4362211 : Blo 2041435 4362211 := bstep (se 1 (by rfl) ⟨3271658, by rfl⟩ : syracuseStep 4362211 = 6543317) B6543317
theorem B5816281 : Blo 2041435 5816281 := bstep (se 2 (by rfl) ⟨2181105, by rfl⟩ : syracuseStep 5816281 = 4362211) B4362211
theorem B7755041 : Blo 2041435 7755041 := bstep (se 2 (by rfl) ⟨2908140, by rfl⟩ : syracuseStep 7755041 = 5816281) B5816281
theorem B5170027 : Blo 2041435 5170027 := bstep (se 1 (by rfl) ⟨3877520, by rfl⟩ : syracuseStep 5170027 = 7755041) B7755041
theorem B6893369 : Blo 2041435 6893369 := bstep (se 2 (by rfl) ⟨2585013, by rfl⟩ : syracuseStep 6893369 = 5170027) B5170027
theorem B4595579 : Blo 2041435 4595579 := bstep (se 1 (by rfl) ⟨3446684, by rfl⟩ : syracuseStep 4595579 = 6893369) B6893369
theorem B3063719 : Blo 2041435 3063719 := bstep (se 1 (by rfl) ⟨2297789, by rfl⟩ : syracuseStep 3063719 = 4595579) B4595579
theorem B2042479 : Blo 2041435 2042479 := bstep (se 1 (by rfl) ⟨1531859, by rfl⟩ : syracuseStep 2042479 = 3063719) B3063719
theorem B3063725 : Blo 2041435 3063725 := bbase (se 3 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 3063725 = 1148897) (by norm_num)
theorem B2042483 : Blo 2041435 2042483 := bstep (se 1 (by rfl) ⟨1531862, by rfl⟩ : syracuseStep 2042483 = 3063725) B3063725
theorem B4595597 : Blo 2041435 4595597 := bbase (se 3 (by rfl) ⟨861674, by rfl⟩ : syracuseStep 4595597 = 1723349) (by norm_num)
theorem B3063731 : Blo 2041435 3063731 := bstep (se 1 (by rfl) ⟨2297798, by rfl⟩ : syracuseStep 3063731 = 4595597) B4595597
theorem B2042487 : Blo 2041435 2042487 := bstep (se 1 (by rfl) ⟨1531865, by rfl⟩ : syracuseStep 2042487 = 3063731) B3063731
theorem B2585029 : Blo 2041435 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B3446705 : Blo 2041435 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B2297803 : Blo 2041435 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B3063737 : Blo 2041435 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B2042491 : Blo 2041435 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B4140725 : Blo 2041435 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B11041933 : Blo 2041435 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B14722577 : Blo 2041435 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B9815051 : Blo 2041435 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B26173469 : Blo 2041435 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B17448979 : Blo 2041435 17448979 := bstep (se 1 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 17448979 = 26173469) B26173469
theorem B23265305 : Blo 2041435 23265305 := bstep (se 2 (by rfl) ⟨8724489, by rfl⟩ : syracuseStep 23265305 = 17448979) B17448979
theorem B15510203 : Blo 2041435 15510203 := bstep (se 1 (by rfl) ⟨11632652, by rfl⟩ : syracuseStep 15510203 = 23265305) B23265305
theorem B10340135 : Blo 2041435 10340135 := bstep (se 1 (by rfl) ⟨7755101, by rfl⟩ : syracuseStep 10340135 = 15510203) B15510203
theorem B6893423 : Blo 2041435 6893423 := bstep (se 1 (by rfl) ⟨5170067, by rfl⟩ : syracuseStep 6893423 = 10340135) B10340135
theorem B4595615 : Blo 2041435 4595615 := bstep (se 1 (by rfl) ⟨3446711, by rfl⟩ : syracuseStep 4595615 = 6893423) B6893423
theorem B3063743 : Blo 2041435 3063743 := bstep (se 1 (by rfl) ⟨2297807, by rfl⟩ : syracuseStep 3063743 = 4595615) B4595615
theorem B2042495 : Blo 2041435 2042495 := bstep (se 1 (by rfl) ⟨1531871, by rfl⟩ : syracuseStep 2042495 = 3063743) B3063743
theorem B3063749 : Blo 2041435 3063749 := bbase (se 4 (by rfl) ⟨287226, by rfl⟩ : syracuseStep 3063749 = 574453) (by norm_num)
theorem B2042499 : Blo 2041435 2042499 := bstep (se 1 (by rfl) ⟨1531874, by rfl⟩ : syracuseStep 2042499 = 3063749) B3063749
theorem B3446725 : Blo 2041435 3446725 := bbase (se 4 (by rfl) ⟨323130, by rfl⟩ : syracuseStep 3446725 = 646261) (by norm_num)
theorem B4595633 : Blo 2041435 4595633 := bstep (se 2 (by rfl) ⟨1723362, by rfl⟩ : syracuseStep 4595633 = 3446725) B3446725
theorem B3063755 : Blo 2041435 3063755 := bstep (se 1 (by rfl) ⟨2297816, by rfl⟩ : syracuseStep 3063755 = 4595633) B4595633
theorem B2042503 : Blo 2041435 2042503 := bstep (se 1 (by rfl) ⟨1531877, by rfl⟩ : syracuseStep 2042503 = 3063755) B3063755
theorem B2297821 : Blo 2041435 2297821 := bbase (se 3 (by rfl) ⟨430841, by rfl⟩ : syracuseStep 2297821 = 861683) (by norm_num)
theorem B3063761 : Blo 2041435 3063761 := bstep (se 2 (by rfl) ⟨1148910, by rfl⟩ : syracuseStep 3063761 = 2297821) B2297821
theorem B2042507 : Blo 2041435 2042507 := bstep (se 1 (by rfl) ⟨1531880, by rfl⟩ : syracuseStep 2042507 = 3063761) B3063761
theorem B6893477 : Blo 2041435 6893477 := bbase (se 4 (by rfl) ⟨646263, by rfl⟩ : syracuseStep 6893477 = 1292527) (by norm_num)
theorem B4595651 : Blo 2041435 4595651 := bstep (se 1 (by rfl) ⟨3446738, by rfl⟩ : syracuseStep 4595651 = 6893477) B6893477
theorem B3063767 : Blo 2041435 3063767 := bstep (se 1 (by rfl) ⟨2297825, by rfl⟩ : syracuseStep 3063767 = 4595651) B4595651
theorem B2042511 : Blo 2041435 2042511 := bstep (se 1 (by rfl) ⟨1531883, by rfl⟩ : syracuseStep 2042511 = 3063767) B3063767
theorem B3063773 : Blo 2041435 3063773 := bbase (se 3 (by rfl) ⟨574457, by rfl⟩ : syracuseStep 3063773 = 1148915) (by norm_num)
theorem B2042515 : Blo 2041435 2042515 := bstep (se 1 (by rfl) ⟨1531886, by rfl⟩ : syracuseStep 2042515 = 3063773) B3063773
theorem B4595669 : Blo 2041435 4595669 := bbase (se 7 (by rfl) ⟨53855, by rfl⟩ : syracuseStep 4595669 = 107711) (by norm_num)
theorem B3063779 : Blo 2041435 3063779 := bstep (se 1 (by rfl) ⟨2297834, by rfl⟩ : syracuseStep 3063779 = 4595669) B4595669
theorem B2042519 : Blo 2041435 2042519 := bstep (se 1 (by rfl) ⟨1531889, by rfl⟩ : syracuseStep 2042519 = 3063779) B3063779
theorem B2453797 : Blo 2041435 2453797 := bbase (se 4 (by rfl) ⟨230043, by rfl⟩ : syracuseStep 2453797 = 460087) (by norm_num)
theorem B13086917 : Blo 2041435 13086917 := bstep (se 4 (by rfl) ⟨1226898, by rfl⟩ : syracuseStep 13086917 = 2453797) B2453797
theorem B8724611 : Blo 2041435 8724611 := bstep (se 1 (by rfl) ⟨6543458, by rfl⟩ : syracuseStep 8724611 = 13086917) B13086917
theorem B5816407 : Blo 2041435 5816407 := bstep (se 1 (by rfl) ⟨4362305, by rfl⟩ : syracuseStep 5816407 = 8724611) B8724611
theorem B7755209 : Blo 2041435 7755209 := bstep (se 2 (by rfl) ⟨2908203, by rfl⟩ : syracuseStep 7755209 = 5816407) B5816407
theorem B5170139 : Blo 2041435 5170139 := bstep (se 1 (by rfl) ⟨3877604, by rfl⟩ : syracuseStep 5170139 = 7755209) B7755209
theorem B3446759 : Blo 2041435 3446759 := bstep (se 1 (by rfl) ⟨2585069, by rfl⟩ : syracuseStep 3446759 = 5170139) B5170139
theorem B2297839 : Blo 2041435 2297839 := bstep (se 1 (by rfl) ⟨1723379, by rfl⟩ : syracuseStep 2297839 = 3446759) B3446759
theorem B3063785 : Blo 2041435 3063785 := bstep (se 2 (by rfl) ⟨1148919, by rfl⟩ : syracuseStep 3063785 = 2297839) B2297839
theorem B2042523 : Blo 2041435 2042523 := bstep (se 1 (by rfl) ⟨1531892, by rfl⟩ : syracuseStep 2042523 = 3063785) B3063785
theorem B2620345 : Blo 2041435 2620345 := bbase (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) (by norm_num)
theorem B3493793 : Blo 2041435 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B9316781 : Blo 2041435 9316781 := bstep (se 3 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 9316781 = 3493793) B3493793
theorem B6211187 : Blo 2041435 6211187 := bstep (se 1 (by rfl) ⟨4658390, by rfl⟩ : syracuseStep 6211187 = 9316781) B9316781
theorem B4140791 : Blo 2041435 4140791 := bstep (se 1 (by rfl) ⟨3105593, by rfl⟩ : syracuseStep 4140791 = 6211187) B6211187
theorem B2760527 : Blo 2041435 2760527 := bstep (se 1 (by rfl) ⟨2070395, by rfl⟩ : syracuseStep 2760527 = 4140791) B4140791
theorem B7361405 : Blo 2041435 7361405 := bstep (se 3 (by rfl) ⟨1380263, by rfl⟩ : syracuseStep 7361405 = 2760527) B2760527
theorem B4907603 : Blo 2041435 4907603 := bstep (se 1 (by rfl) ⟨3680702, by rfl⟩ : syracuseStep 4907603 = 7361405) B7361405
theorem B3271735 : Blo 2041435 3271735 := bstep (se 1 (by rfl) ⟨2453801, by rfl⟩ : syracuseStep 3271735 = 4907603) B4907603
theorem B17449253 : Blo 2041435 17449253 := bstep (se 4 (by rfl) ⟨1635867, by rfl⟩ : syracuseStep 17449253 = 3271735) B3271735
theorem B11632835 : Blo 2041435 11632835 := bstep (se 1 (by rfl) ⟨8724626, by rfl⟩ : syracuseStep 11632835 = 17449253) B17449253
theorem B7755223 : Blo 2041435 7755223 := bstep (se 1 (by rfl) ⟨5816417, by rfl⟩ : syracuseStep 7755223 = 11632835) B11632835
theorem B10340297 : Blo 2041435 10340297 := bstep (se 2 (by rfl) ⟨3877611, by rfl⟩ : syracuseStep 10340297 = 7755223) B7755223
theorem B6893531 : Blo 2041435 6893531 := bstep (se 1 (by rfl) ⟨5170148, by rfl⟩ : syracuseStep 6893531 = 10340297) B10340297
theorem B4595687 : Blo 2041435 4595687 := bstep (se 1 (by rfl) ⟨3446765, by rfl⟩ : syracuseStep 4595687 = 6893531) B6893531
theorem B3063791 : Blo 2041435 3063791 := bstep (se 1 (by rfl) ⟨2297843, by rfl⟩ : syracuseStep 3063791 = 4595687) B4595687
theorem B2042527 : Blo 2041435 2042527 := bstep (se 1 (by rfl) ⟨1531895, by rfl⟩ : syracuseStep 2042527 = 3063791) B3063791
theorem B3063797 : Blo 2041435 3063797 := bbase (se 5 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 3063797 = 287231) (by norm_num)
theorem B2042531 : Blo 2041435 2042531 := bstep (se 1 (by rfl) ⟨1531898, by rfl⟩ : syracuseStep 2042531 = 3063797) B3063797
theorem B3930533 : Blo 2041435 3930533 := bbase (se 4 (by rfl) ⟨368487, by rfl⟩ : syracuseStep 3930533 = 736975) (by norm_num)
theorem B2620355 : Blo 2041435 2620355 := bstep (se 1 (by rfl) ⟨1965266, by rfl⟩ : syracuseStep 2620355 = 3930533) B3930533
theorem B27950453 : Blo 2041435 27950453 := bstep (se 5 (by rfl) ⟨1310177, by rfl⟩ : syracuseStep 27950453 = 2620355) B2620355
theorem B18633635 : Blo 2041435 18633635 := bstep (se 1 (by rfl) ⟨13975226, by rfl⟩ : syracuseStep 18633635 = 27950453) B27950453
theorem B12422423 : Blo 2041435 12422423 := bstep (se 1 (by rfl) ⟨9316817, by rfl⟩ : syracuseStep 12422423 = 18633635) B18633635
theorem B8281615 : Blo 2041435 8281615 := bstep (se 1 (by rfl) ⟨6211211, by rfl⟩ : syracuseStep 8281615 = 12422423) B12422423
theorem B11042153 : Blo 2041435 11042153 := bstep (se 2 (by rfl) ⟨4140807, by rfl⟩ : syracuseStep 11042153 = 8281615) B8281615
theorem B7361435 : Blo 2041435 7361435 := bstep (se 1 (by rfl) ⟨5521076, by rfl⟩ : syracuseStep 7361435 = 11042153) B11042153
theorem B4907623 : Blo 2041435 4907623 := bstep (se 1 (by rfl) ⟨3680717, by rfl⟩ : syracuseStep 4907623 = 7361435) B7361435
theorem B6543497 : Blo 2041435 6543497 := bstep (se 2 (by rfl) ⟨2453811, by rfl⟩ : syracuseStep 6543497 = 4907623) B4907623
theorem B4362331 : Blo 2041435 4362331 := bstep (se 1 (by rfl) ⟨3271748, by rfl⟩ : syracuseStep 4362331 = 6543497) B6543497
theorem B5816441 : Blo 2041435 5816441 := bstep (se 2 (by rfl) ⟨2181165, by rfl⟩ : syracuseStep 5816441 = 4362331) B4362331
theorem B3877627 : Blo 2041435 3877627 := bstep (se 1 (by rfl) ⟨2908220, by rfl⟩ : syracuseStep 3877627 = 5816441) B5816441
theorem B5170169 : Blo 2041435 5170169 := bstep (se 2 (by rfl) ⟨1938813, by rfl⟩ : syracuseStep 5170169 = 3877627) B3877627
theorem B3446779 : Blo 2041435 3446779 := bstep (se 1 (by rfl) ⟨2585084, by rfl⟩ : syracuseStep 3446779 = 5170169) B5170169
theorem B4595705 : Blo 2041435 4595705 := bstep (se 2 (by rfl) ⟨1723389, by rfl⟩ : syracuseStep 4595705 = 3446779) B3446779
theorem B3063803 : Blo 2041435 3063803 := bstep (se 1 (by rfl) ⟨2297852, by rfl⟩ : syracuseStep 3063803 = 4595705) B4595705
theorem B2042535 : Blo 2041435 2042535 := bstep (se 1 (by rfl) ⟨1531901, by rfl⟩ : syracuseStep 2042535 = 3063803) B3063803
theorem B2297857 : Blo 2041435 2297857 := bbase (se 2 (by rfl) ⟨861696, by rfl⟩ : syracuseStep 2297857 = 1723393) (by norm_num)
theorem B3063809 : Blo 2041435 3063809 := bstep (se 2 (by rfl) ⟨1148928, by rfl⟩ : syracuseStep 3063809 = 2297857) B2297857
theorem B2042539 : Blo 2041435 2042539 := bstep (se 1 (by rfl) ⟨1531904, by rfl⟩ : syracuseStep 2042539 = 3063809) B3063809
theorem B5170189 : Blo 2041435 5170189 := bbase (se 3 (by rfl) ⟨969410, by rfl⟩ : syracuseStep 5170189 = 1938821) (by norm_num)
theorem B6893585 : Blo 2041435 6893585 := bstep (se 2 (by rfl) ⟨2585094, by rfl⟩ : syracuseStep 6893585 = 5170189) B5170189
theorem B4595723 : Blo 2041435 4595723 := bstep (se 1 (by rfl) ⟨3446792, by rfl⟩ : syracuseStep 4595723 = 6893585) B6893585
theorem B3063815 : Blo 2041435 3063815 := bstep (se 1 (by rfl) ⟨2297861, by rfl⟩ : syracuseStep 3063815 = 4595723) B4595723
theorem B2042543 : Blo 2041435 2042543 := bstep (se 1 (by rfl) ⟨1531907, by rfl⟩ : syracuseStep 2042543 = 3063815) B3063815
theorem B3063821 : Blo 2041435 3063821 := bbase (se 3 (by rfl) ⟨574466, by rfl⟩ : syracuseStep 3063821 = 1148933) (by norm_num)
theorem B2042547 : Blo 2041435 2042547 := bstep (se 1 (by rfl) ⟨1531910, by rfl⟩ : syracuseStep 2042547 = 3063821) B3063821
theorem B4595741 : Blo 2041435 4595741 := bbase (se 3 (by rfl) ⟨861701, by rfl⟩ : syracuseStep 4595741 = 1723403) (by norm_num)
theorem B3063827 : Blo 2041435 3063827 := bstep (se 1 (by rfl) ⟨2297870, by rfl⟩ : syracuseStep 3063827 = 4595741) B4595741
theorem B2042551 : Blo 2041435 2042551 := bstep (se 1 (by rfl) ⟨1531913, by rfl⟩ : syracuseStep 2042551 = 3063827) B3063827
theorem B3446813 : Blo 2041435 3446813 := bbase (se 3 (by rfl) ⟨646277, by rfl⟩ : syracuseStep 3446813 = 1292555) (by norm_num)
theorem B2297875 : Blo 2041435 2297875 := bstep (se 1 (by rfl) ⟨1723406, by rfl⟩ : syracuseStep 2297875 = 3446813) B3446813
theorem B3063833 : Blo 2041435 3063833 := bstep (se 2 (by rfl) ⟨1148937, by rfl⟩ : syracuseStep 3063833 = 2297875) B2297875
theorem B2042555 : Blo 2041435 2042555 := bstep (se 1 (by rfl) ⟨1531916, by rfl⟩ : syracuseStep 2042555 = 3063833) B3063833
theorem B2947933 : Blo 2041435 2947933 := bbase (se 3 (by rfl) ⟨552737, by rfl⟩ : syracuseStep 2947933 = 1105475) (by norm_num)
theorem B15722309 : Blo 2041435 15722309 := bstep (se 4 (by rfl) ⟨1473966, by rfl⟩ : syracuseStep 15722309 = 2947933) B2947933
theorem B41926157 : Blo 2041435 41926157 := bstep (se 3 (by rfl) ⟨7861154, by rfl⟩ : syracuseStep 41926157 = 15722309) B15722309
theorem B27950771 : Blo 2041435 27950771 := bstep (se 1 (by rfl) ⟨20963078, by rfl⟩ : syracuseStep 27950771 = 41926157) B41926157
theorem B74535389 : Blo 2041435 74535389 := bstep (se 3 (by rfl) ⟨13975385, by rfl⟩ : syracuseStep 74535389 = 27950771) B27950771
theorem B49690259 : Blo 2041435 49690259 := bstep (se 1 (by rfl) ⟨37267694, by rfl⟩ : syracuseStep 49690259 = 74535389) B74535389
theorem B33126839 : Blo 2041435 33126839 := bstep (se 1 (by rfl) ⟨24845129, by rfl⟩ : syracuseStep 33126839 = 49690259) B49690259
theorem B22084559 : Blo 2041435 22084559 := bstep (se 1 (by rfl) ⟨16563419, by rfl⟩ : syracuseStep 22084559 = 33126839) B33126839
theorem B14723039 : Blo 2041435 14723039 := bstep (se 1 (by rfl) ⟨11042279, by rfl⟩ : syracuseStep 14723039 = 22084559) B22084559
theorem B9815359 : Blo 2041435 9815359 := bstep (se 1 (by rfl) ⟨7361519, by rfl⟩ : syracuseStep 9815359 = 14723039) B14723039
theorem B13087145 : Blo 2041435 13087145 := bstep (se 2 (by rfl) ⟨4907679, by rfl⟩ : syracuseStep 13087145 = 9815359) B9815359
theorem B8724763 : Blo 2041435 8724763 := bstep (se 1 (by rfl) ⟨6543572, by rfl⟩ : syracuseStep 8724763 = 13087145) B13087145
theorem B11633017 : Blo 2041435 11633017 := bstep (se 2 (by rfl) ⟨4362381, by rfl⟩ : syracuseStep 11633017 = 8724763) B8724763
theorem B15510689 : Blo 2041435 15510689 := bstep (se 2 (by rfl) ⟨5816508, by rfl⟩ : syracuseStep 15510689 = 11633017) B11633017
theorem B10340459 : Blo 2041435 10340459 := bstep (se 1 (by rfl) ⟨7755344, by rfl⟩ : syracuseStep 10340459 = 15510689) B15510689
theorem B6893639 : Blo 2041435 6893639 := bstep (se 1 (by rfl) ⟨5170229, by rfl⟩ : syracuseStep 6893639 = 10340459) B10340459
theorem B4595759 : Blo 2041435 4595759 := bstep (se 1 (by rfl) ⟨3446819, by rfl⟩ : syracuseStep 4595759 = 6893639) B6893639
theorem B3063839 : Blo 2041435 3063839 := bstep (se 1 (by rfl) ⟨2297879, by rfl⟩ : syracuseStep 3063839 = 4595759) B4595759
theorem B2042559 : Blo 2041435 2042559 := bstep (se 1 (by rfl) ⟨1531919, by rfl⟩ : syracuseStep 2042559 = 3063839) B3063839
theorem B3063845 : Blo 2041435 3063845 := bbase (se 4 (by rfl) ⟨287235, by rfl⟩ : syracuseStep 3063845 = 574471) (by norm_num)
theorem B2042563 : Blo 2041435 2042563 := bstep (se 1 (by rfl) ⟨1531922, by rfl⟩ : syracuseStep 2042563 = 3063845) B3063845
theorem B2585125 : Blo 2041435 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B3446833 : Blo 2041435 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B4595777 : Blo 2041435 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B3063851 : Blo 2041435 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B2042567 : Blo 2041435 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B2297893 : Blo 2041435 2297893 := bbase (se 4 (by rfl) ⟨215427, by rfl⟩ : syracuseStep 2297893 = 430855) (by norm_num)
theorem B3063857 : Blo 2041435 3063857 := bstep (se 2 (by rfl) ⟨1148946, by rfl⟩ : syracuseStep 3063857 = 2297893) B2297893
theorem B2042571 : Blo 2041435 2042571 := bstep (se 1 (by rfl) ⟨1531928, by rfl⟩ : syracuseStep 2042571 = 3063857) B3063857
theorem B6211333 : Blo 2041435 6211333 := bbase (se 4 (by rfl) ⟨582312, by rfl⟩ : syracuseStep 6211333 = 1164625) (by norm_num)
theorem B8281777 : Blo 2041435 8281777 := bstep (se 2 (by rfl) ⟨3105666, by rfl⟩ : syracuseStep 8281777 = 6211333) B6211333
theorem B11042369 : Blo 2041435 11042369 := bstep (se 2 (by rfl) ⟨4140888, by rfl⟩ : syracuseStep 11042369 = 8281777) B8281777
theorem B7361579 : Blo 2041435 7361579 := bstep (se 1 (by rfl) ⟨5521184, by rfl⟩ : syracuseStep 7361579 = 11042369) B11042369
theorem B4907719 : Blo 2041435 4907719 := bstep (se 1 (by rfl) ⟨3680789, by rfl⟩ : syracuseStep 4907719 = 7361579) B7361579
theorem B6543625 : Blo 2041435 6543625 := bstep (se 2 (by rfl) ⟨2453859, by rfl⟩ : syracuseStep 6543625 = 4907719) B4907719
theorem B8724833 : Blo 2041435 8724833 := bstep (se 2 (by rfl) ⟨3271812, by rfl⟩ : syracuseStep 8724833 = 6543625) B6543625
theorem B5816555 : Blo 2041435 5816555 := bstep (se 1 (by rfl) ⟨4362416, by rfl⟩ : syracuseStep 5816555 = 8724833) B8724833
theorem B3877703 : Blo 2041435 3877703 := bstep (se 1 (by rfl) ⟨2908277, by rfl⟩ : syracuseStep 3877703 = 5816555) B5816555
theorem B2585135 : Blo 2041435 2585135 := bstep (se 1 (by rfl) ⟨1938851, by rfl⟩ : syracuseStep 2585135 = 3877703) B3877703
theorem B6893693 : Blo 2041435 6893693 := bstep (se 3 (by rfl) ⟨1292567, by rfl⟩ : syracuseStep 6893693 = 2585135) B2585135
theorem B4595795 : Blo 2041435 4595795 := bstep (se 1 (by rfl) ⟨3446846, by rfl⟩ : syracuseStep 4595795 = 6893693) B6893693
theorem B3063863 : Blo 2041435 3063863 := bstep (se 1 (by rfl) ⟨2297897, by rfl⟩ : syracuseStep 3063863 = 4595795) B4595795
theorem B2042575 : Blo 2041435 2042575 := bstep (se 1 (by rfl) ⟨1531931, by rfl⟩ : syracuseStep 2042575 = 3063863) B3063863
theorem B3063869 : Blo 2041435 3063869 := bbase (se 3 (by rfl) ⟨574475, by rfl⟩ : syracuseStep 3063869 = 1148951) (by norm_num)
theorem B2042579 : Blo 2041435 2042579 := bstep (se 1 (by rfl) ⟨1531934, by rfl⟩ : syracuseStep 2042579 = 3063869) B3063869
theorem B4595813 : Blo 2041435 4595813 := bbase (se 4 (by rfl) ⟨430857, by rfl⟩ : syracuseStep 4595813 = 861715) (by norm_num)
theorem B3063875 : Blo 2041435 3063875 := bstep (se 1 (by rfl) ⟨2297906, by rfl⟩ : syracuseStep 3063875 = 4595813) B4595813
theorem B2042583 : Blo 2041435 2042583 := bstep (se 1 (by rfl) ⟨1531937, by rfl⟩ : syracuseStep 2042583 = 3063875) B3063875
theorem B5170301 : Blo 2041435 5170301 := bbase (se 3 (by rfl) ⟨969431, by rfl⟩ : syracuseStep 5170301 = 1938863) (by norm_num)
theorem B3446867 : Blo 2041435 3446867 := bstep (se 1 (by rfl) ⟨2585150, by rfl⟩ : syracuseStep 3446867 = 5170301) B5170301
theorem B2297911 : Blo 2041435 2297911 := bstep (se 1 (by rfl) ⟨1723433, by rfl⟩ : syracuseStep 2297911 = 3446867) B3446867
theorem B3063881 : Blo 2041435 3063881 := bstep (se 2 (by rfl) ⟨1148955, by rfl⟩ : syracuseStep 3063881 = 2297911) B2297911
theorem B2042587 : Blo 2041435 2042587 := bstep (se 1 (by rfl) ⟨1531940, by rfl⟩ : syracuseStep 2042587 = 3063881) B3063881
theorem B3877733 : Blo 2041435 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B10340621 : Blo 2041435 10340621 := bstep (se 3 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 10340621 = 3877733) B3877733
theorem B6893747 : Blo 2041435 6893747 := bstep (se 1 (by rfl) ⟨5170310, by rfl⟩ : syracuseStep 6893747 = 10340621) B10340621
theorem B4595831 : Blo 2041435 4595831 := bstep (se 1 (by rfl) ⟨3446873, by rfl⟩ : syracuseStep 4595831 = 6893747) B6893747
theorem B3063887 : Blo 2041435 3063887 := bstep (se 1 (by rfl) ⟨2297915, by rfl⟩ : syracuseStep 3063887 = 4595831) B4595831
theorem B2042591 : Blo 2041435 2042591 := bstep (se 1 (by rfl) ⟨1531943, by rfl⟩ : syracuseStep 2042591 = 3063887) B3063887
theorem B3063893 : Blo 2041435 3063893 := bbase (se 8 (by rfl) ⟨17952, by rfl⟩ : syracuseStep 3063893 = 35905) (by norm_num)
theorem B2042595 : Blo 2041435 2042595 := bstep (se 1 (by rfl) ⟨1531946, by rfl⟩ : syracuseStep 2042595 = 3063893) B3063893
theorem B2329277 : Blo 2041435 2329277 := bbase (se 3 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 2329277 = 873479) (by norm_num)
theorem B6211405 : Blo 2041435 6211405 := bstep (se 3 (by rfl) ⟨1164638, by rfl⟩ : syracuseStep 6211405 = 2329277) B2329277
theorem B8281873 : Blo 2041435 8281873 := bstep (se 2 (by rfl) ⟨3105702, by rfl⟩ : syracuseStep 8281873 = 6211405) B6211405
theorem B11042497 : Blo 2041435 11042497 := bstep (se 2 (by rfl) ⟨4140936, by rfl⟩ : syracuseStep 11042497 = 8281873) B8281873
theorem B14723329 : Blo 2041435 14723329 := bstep (se 2 (by rfl) ⟨5521248, by rfl⟩ : syracuseStep 14723329 = 11042497) B11042497
theorem B19631105 : Blo 2041435 19631105 := bstep (se 2 (by rfl) ⟨7361664, by rfl⟩ : syracuseStep 19631105 = 14723329) B14723329
theorem B13087403 : Blo 2041435 13087403 := bstep (se 1 (by rfl) ⟨9815552, by rfl⟩ : syracuseStep 13087403 = 19631105) B19631105
theorem B8724935 : Blo 2041435 8724935 := bstep (se 1 (by rfl) ⟨6543701, by rfl⟩ : syracuseStep 8724935 = 13087403) B13087403
theorem B5816623 : Blo 2041435 5816623 := bstep (se 1 (by rfl) ⟨4362467, by rfl⟩ : syracuseStep 5816623 = 8724935) B8724935
theorem B7755497 : Blo 2041435 7755497 := bstep (se 2 (by rfl) ⟨2908311, by rfl⟩ : syracuseStep 7755497 = 5816623) B5816623
theorem B5170331 : Blo 2041435 5170331 := bstep (se 1 (by rfl) ⟨3877748, by rfl⟩ : syracuseStep 5170331 = 7755497) B7755497
theorem B3446887 : Blo 2041435 3446887 := bstep (se 1 (by rfl) ⟨2585165, by rfl⟩ : syracuseStep 3446887 = 5170331) B5170331
theorem B4595849 : Blo 2041435 4595849 := bstep (se 2 (by rfl) ⟨1723443, by rfl⟩ : syracuseStep 4595849 = 3446887) B3446887
theorem B3063899 : Blo 2041435 3063899 := bstep (se 1 (by rfl) ⟨2297924, by rfl⟩ : syracuseStep 3063899 = 4595849) B4595849
theorem B2042599 : Blo 2041435 2042599 := bstep (se 1 (by rfl) ⟨1531949, by rfl⟩ : syracuseStep 2042599 = 3063899) B3063899
theorem B2297929 : Blo 2041435 2297929 := bbase (se 2 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 2297929 = 1723447) (by norm_num)
theorem B3063905 : Blo 2041435 3063905 := bstep (se 2 (by rfl) ⟨1148964, by rfl⟩ : syracuseStep 3063905 = 2297929) B2297929
theorem B2042603 : Blo 2041435 2042603 := bstep (se 1 (by rfl) ⟨1531952, by rfl⟩ : syracuseStep 2042603 = 3063905) B3063905
theorem B4658573 : Blo 2041435 4658573 := bbase (se 3 (by rfl) ⟨873482, by rfl⟩ : syracuseStep 4658573 = 1746965) (by norm_num)
theorem B3105715 : Blo 2041435 3105715 := bstep (se 1 (by rfl) ⟨2329286, by rfl⟩ : syracuseStep 3105715 = 4658573) B4658573
theorem B4140953 : Blo 2041435 4140953 := bstep (se 2 (by rfl) ⟨1552857, by rfl⟩ : syracuseStep 4140953 = 3105715) B3105715
theorem B2760635 : Blo 2041435 2760635 := bstep (se 1 (by rfl) ⟨2070476, by rfl⟩ : syracuseStep 2760635 = 4140953) B4140953
theorem B7361693 : Blo 2041435 7361693 := bstep (se 3 (by rfl) ⟨1380317, by rfl⟩ : syracuseStep 7361693 = 2760635) B2760635
theorem B4907795 : Blo 2041435 4907795 := bstep (se 1 (by rfl) ⟨3680846, by rfl⟩ : syracuseStep 4907795 = 7361693) B7361693
theorem B13087453 : Blo 2041435 13087453 := bstep (se 3 (by rfl) ⟨2453897, by rfl⟩ : syracuseStep 13087453 = 4907795) B4907795
theorem B17449937 : Blo 2041435 17449937 := bstep (se 2 (by rfl) ⟨6543726, by rfl⟩ : syracuseStep 17449937 = 13087453) B13087453
theorem B11633291 : Blo 2041435 11633291 := bstep (se 1 (by rfl) ⟨8724968, by rfl⟩ : syracuseStep 11633291 = 17449937) B17449937
theorem B7755527 : Blo 2041435 7755527 := bstep (se 1 (by rfl) ⟨5816645, by rfl⟩ : syracuseStep 7755527 = 11633291) B11633291
theorem B5170351 : Blo 2041435 5170351 := bstep (se 1 (by rfl) ⟨3877763, by rfl⟩ : syracuseStep 5170351 = 7755527) B7755527
theorem B6893801 : Blo 2041435 6893801 := bstep (se 2 (by rfl) ⟨2585175, by rfl⟩ : syracuseStep 6893801 = 5170351) B5170351
theorem B4595867 : Blo 2041435 4595867 := bstep (se 1 (by rfl) ⟨3446900, by rfl⟩ : syracuseStep 4595867 = 6893801) B6893801
theorem B3063911 : Blo 2041435 3063911 := bstep (se 1 (by rfl) ⟨2297933, by rfl⟩ : syracuseStep 3063911 = 4595867) B4595867
theorem B2042607 : Blo 2041435 2042607 := bstep (se 1 (by rfl) ⟨1531955, by rfl⟩ : syracuseStep 2042607 = 3063911) B3063911
theorem B3063917 : Blo 2041435 3063917 := bbase (se 3 (by rfl) ⟨574484, by rfl⟩ : syracuseStep 3063917 = 1148969) (by norm_num)
theorem B2042611 : Blo 2041435 2042611 := bstep (se 1 (by rfl) ⟨1531958, by rfl⟩ : syracuseStep 2042611 = 3063917) B3063917
theorem B4595885 : Blo 2041435 4595885 := bbase (se 3 (by rfl) ⟨861728, by rfl⟩ : syracuseStep 4595885 = 1723457) (by norm_num)
theorem B3063923 : Blo 2041435 3063923 := bstep (se 1 (by rfl) ⟨2297942, by rfl⟩ : syracuseStep 3063923 = 4595885) B4595885
theorem B2042615 : Blo 2041435 2042615 := bstep (se 1 (by rfl) ⟨1531961, by rfl⟩ : syracuseStep 2042615 = 3063923) B3063923
theorem B14723477 : Blo 2041435 14723477 := bbase (se 6 (by rfl) ⟨345081, by rfl⟩ : syracuseStep 14723477 = 690163) (by norm_num)
theorem B9815651 : Blo 2041435 9815651 := bstep (se 1 (by rfl) ⟨7361738, by rfl⟩ : syracuseStep 9815651 = 14723477) B14723477
theorem B6543767 : Blo 2041435 6543767 := bstep (se 1 (by rfl) ⟨4907825, by rfl⟩ : syracuseStep 6543767 = 9815651) B9815651
theorem B4362511 : Blo 2041435 4362511 := bstep (se 1 (by rfl) ⟨3271883, by rfl⟩ : syracuseStep 4362511 = 6543767) B6543767
theorem B5816681 : Blo 2041435 5816681 := bstep (se 2 (by rfl) ⟨2181255, by rfl⟩ : syracuseStep 5816681 = 4362511) B4362511
theorem B3877787 : Blo 2041435 3877787 := bstep (se 1 (by rfl) ⟨2908340, by rfl⟩ : syracuseStep 3877787 = 5816681) B5816681
theorem B2585191 : Blo 2041435 2585191 := bstep (se 1 (by rfl) ⟨1938893, by rfl⟩ : syracuseStep 2585191 = 3877787) B3877787
theorem B3446921 : Blo 2041435 3446921 := bstep (se 2 (by rfl) ⟨1292595, by rfl⟩ : syracuseStep 3446921 = 2585191) B2585191
theorem B2297947 : Blo 2041435 2297947 := bstep (se 1 (by rfl) ⟨1723460, by rfl⟩ : syracuseStep 2297947 = 3446921) B3446921
theorem B3063929 : Blo 2041435 3063929 := bstep (se 2 (by rfl) ⟨1148973, by rfl⟩ : syracuseStep 3063929 = 2297947) B2297947
theorem B2042619 : Blo 2041435 2042619 := bstep (se 1 (by rfl) ⟨1531964, by rfl⟩ : syracuseStep 2042619 = 3063929) B3063929
theorem B3493957 : Blo 2041435 3493957 := bbase (se 4 (by rfl) ⟨327558, by rfl⟩ : syracuseStep 3493957 = 655117) (by norm_num)
theorem B4658609 : Blo 2041435 4658609 := bstep (se 2 (by rfl) ⟨1746978, by rfl⟩ : syracuseStep 4658609 = 3493957) B3493957
theorem B3105739 : Blo 2041435 3105739 := bstep (se 1 (by rfl) ⟨2329304, by rfl⟩ : syracuseStep 3105739 = 4658609) B4658609
theorem B4140985 : Blo 2041435 4140985 := bstep (se 2 (by rfl) ⟨1552869, by rfl⟩ : syracuseStep 4140985 = 3105739) B3105739
theorem B5521313 : Blo 2041435 5521313 := bstep (se 2 (by rfl) ⟨2070492, by rfl⟩ : syracuseStep 5521313 = 4140985) B4140985
theorem B3680875 : Blo 2041435 3680875 := bstep (se 1 (by rfl) ⟨2760656, by rfl⟩ : syracuseStep 3680875 = 5521313) B5521313
theorem B4907833 : Blo 2041435 4907833 := bstep (se 2 (by rfl) ⟨1840437, by rfl⟩ : syracuseStep 4907833 = 3680875) B3680875
theorem B26175109 : Blo 2041435 26175109 := bstep (se 4 (by rfl) ⟨2453916, by rfl⟩ : syracuseStep 26175109 = 4907833) B4907833
theorem B34900145 : Blo 2041435 34900145 := bstep (se 2 (by rfl) ⟨13087554, by rfl⟩ : syracuseStep 34900145 = 26175109) B26175109
theorem B23266763 : Blo 2041435 23266763 := bstep (se 1 (by rfl) ⟨17450072, by rfl⟩ : syracuseStep 23266763 = 34900145) B34900145
theorem B15511175 : Blo 2041435 15511175 := bstep (se 1 (by rfl) ⟨11633381, by rfl⟩ : syracuseStep 15511175 = 23266763) B23266763
theorem B10340783 : Blo 2041435 10340783 := bstep (se 1 (by rfl) ⟨7755587, by rfl⟩ : syracuseStep 10340783 = 15511175) B15511175
theorem B6893855 : Blo 2041435 6893855 := bstep (se 1 (by rfl) ⟨5170391, by rfl⟩ : syracuseStep 6893855 = 10340783) B10340783
theorem B4595903 : Blo 2041435 4595903 := bstep (se 1 (by rfl) ⟨3446927, by rfl⟩ : syracuseStep 4595903 = 6893855) B6893855
theorem B3063935 : Blo 2041435 3063935 := bstep (se 1 (by rfl) ⟨2297951, by rfl⟩ : syracuseStep 3063935 = 4595903) B4595903
theorem B2042623 : Blo 2041435 2042623 := bstep (se 1 (by rfl) ⟨1531967, by rfl⟩ : syracuseStep 2042623 = 3063935) B3063935
theorem B3063941 : Blo 2041435 3063941 := bbase (se 4 (by rfl) ⟨287244, by rfl⟩ : syracuseStep 3063941 = 574489) (by norm_num)
theorem B2042627 : Blo 2041435 2042627 := bstep (se 1 (by rfl) ⟨1531970, by rfl⟩ : syracuseStep 2042627 = 3063941) B3063941
theorem B3446941 : Blo 2041435 3446941 := bbase (se 3 (by rfl) ⟨646301, by rfl⟩ : syracuseStep 3446941 = 1292603) (by norm_num)
theorem B4595921 : Blo 2041435 4595921 := bstep (se 2 (by rfl) ⟨1723470, by rfl⟩ : syracuseStep 4595921 = 3446941) B3446941
theorem B3063947 : Blo 2041435 3063947 := bstep (se 1 (by rfl) ⟨2297960, by rfl⟩ : syracuseStep 3063947 = 4595921) B4595921
theorem B2042631 : Blo 2041435 2042631 := bstep (se 1 (by rfl) ⟨1531973, by rfl⟩ : syracuseStep 2042631 = 3063947) B3063947
theorem B2297965 : Blo 2041435 2297965 := bbase (se 3 (by rfl) ⟨430868, by rfl⟩ : syracuseStep 2297965 = 861737) (by norm_num)
theorem B3063953 : Blo 2041435 3063953 := bstep (se 2 (by rfl) ⟨1148982, by rfl⟩ : syracuseStep 3063953 = 2297965) B2297965
theorem B2042635 : Blo 2041435 2042635 := bstep (se 1 (by rfl) ⟨1531976, by rfl⟩ : syracuseStep 2042635 = 3063953) B3063953
theorem B6893909 : Blo 2041435 6893909 := bbase (se 10 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 6893909 = 20197) (by norm_num)
theorem B4595939 : Blo 2041435 4595939 := bstep (se 1 (by rfl) ⟨3446954, by rfl⟩ : syracuseStep 4595939 = 6893909) B6893909
theorem B3063959 : Blo 2041435 3063959 := bstep (se 1 (by rfl) ⟨2297969, by rfl⟩ : syracuseStep 3063959 = 4595939) B4595939
theorem B2042639 : Blo 2041435 2042639 := bstep (se 1 (by rfl) ⟨1531979, by rfl⟩ : syracuseStep 2042639 = 3063959) B3063959
theorem B3063965 : Blo 2041435 3063965 := bbase (se 3 (by rfl) ⟨574493, by rfl⟩ : syracuseStep 3063965 = 1148987) (by norm_num)
theorem B2042643 : Blo 2041435 2042643 := bstep (se 1 (by rfl) ⟨1531982, by rfl⟩ : syracuseStep 2042643 = 3063965) B3063965
theorem B4595957 : Blo 2041435 4595957 := bbase (se 5 (by rfl) ⟨215435, by rfl⟩ : syracuseStep 4595957 = 430871) (by norm_num)
theorem B3063971 : Blo 2041435 3063971 := bstep (se 1 (by rfl) ⟨2297978, by rfl⟩ : syracuseStep 3063971 = 4595957) B4595957
theorem B2042647 : Blo 2041435 2042647 := bstep (se 1 (by rfl) ⟨1531985, by rfl⟩ : syracuseStep 2042647 = 3063971) B3063971
theorem B19631605 : Blo 2041435 19631605 := bbase (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) (by norm_num)
theorem B26175473 : Blo 2041435 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B17450315 : Blo 2041435 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B11633543 : Blo 2041435 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B7755695 : Blo 2041435 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B5170463 : Blo 2041435 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B3446975 : Blo 2041435 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B2297983 : Blo 2041435 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B3063977 : Blo 2041435 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B2042651 : Blo 2041435 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B8282101 : Blo 2041435 8282101 := bbase (se 5 (by rfl) ⟨388223, by rfl⟩ : syracuseStep 8282101 = 776447) (by norm_num)
theorem B11042801 : Blo 2041435 11042801 := bstep (se 2 (by rfl) ⟨4141050, by rfl⟩ : syracuseStep 11042801 = 8282101) B8282101
theorem B7361867 : Blo 2041435 7361867 := bstep (se 1 (by rfl) ⟨5521400, by rfl⟩ : syracuseStep 7361867 = 11042801) B11042801
theorem B4907911 : Blo 2041435 4907911 := bstep (se 1 (by rfl) ⟨3680933, by rfl⟩ : syracuseStep 4907911 = 7361867) B7361867
theorem B6543881 : Blo 2041435 6543881 := bstep (se 2 (by rfl) ⟨2453955, by rfl⟩ : syracuseStep 6543881 = 4907911) B4907911
theorem B4362587 : Blo 2041435 4362587 := bstep (se 1 (by rfl) ⟨3271940, by rfl⟩ : syracuseStep 4362587 = 6543881) B6543881
theorem B2908391 : Blo 2041435 2908391 := bstep (se 1 (by rfl) ⟨2181293, by rfl⟩ : syracuseStep 2908391 = 4362587) B4362587
theorem B7755709 : Blo 2041435 7755709 := bstep (se 3 (by rfl) ⟨1454195, by rfl⟩ : syracuseStep 7755709 = 2908391) B2908391
theorem B10340945 : Blo 2041435 10340945 := bstep (se 2 (by rfl) ⟨3877854, by rfl⟩ : syracuseStep 10340945 = 7755709) B7755709
theorem B6893963 : Blo 2041435 6893963 := bstep (se 1 (by rfl) ⟨5170472, by rfl⟩ : syracuseStep 6893963 = 10340945) B10340945
theorem B4595975 : Blo 2041435 4595975 := bstep (se 1 (by rfl) ⟨3446981, by rfl⟩ : syracuseStep 4595975 = 6893963) B6893963
theorem B3063983 : Blo 2041435 3063983 := bstep (se 1 (by rfl) ⟨2297987, by rfl⟩ : syracuseStep 3063983 = 4595975) B4595975
theorem B2042655 : Blo 2041435 2042655 := bstep (se 1 (by rfl) ⟨1531991, by rfl⟩ : syracuseStep 2042655 = 3063983) B3063983
theorem B3063989 : Blo 2041435 3063989 := bbase (se 5 (by rfl) ⟨143624, by rfl⟩ : syracuseStep 3063989 = 287249) (by norm_num)
theorem B2042659 : Blo 2041435 2042659 := bstep (se 1 (by rfl) ⟨1531994, by rfl⟩ : syracuseStep 2042659 = 3063989) B3063989
theorem B5170493 : Blo 2041435 5170493 := bbase (se 3 (by rfl) ⟨969467, by rfl⟩ : syracuseStep 5170493 = 1938935) (by norm_num)
theorem B3446995 : Blo 2041435 3446995 := bstep (se 1 (by rfl) ⟨2585246, by rfl⟩ : syracuseStep 3446995 = 5170493) B5170493
theorem B4595993 : Blo 2041435 4595993 := bstep (se 2 (by rfl) ⟨1723497, by rfl⟩ : syracuseStep 4595993 = 3446995) B3446995
theorem B3063995 : Blo 2041435 3063995 := bstep (se 1 (by rfl) ⟨2297996, by rfl⟩ : syracuseStep 3063995 = 4595993) B4595993
theorem B2042663 : Blo 2041435 2042663 := bstep (se 1 (by rfl) ⟨1531997, by rfl⟩ : syracuseStep 2042663 = 3063995) B3063995
theorem B2298001 : Blo 2041435 2298001 := bbase (se 2 (by rfl) ⟨861750, by rfl⟩ : syracuseStep 2298001 = 1723501) (by norm_num)
theorem B3064001 : Blo 2041435 3064001 := bstep (se 2 (by rfl) ⟨1149000, by rfl⟩ : syracuseStep 3064001 = 2298001) B2298001
theorem B2042667 : Blo 2041435 2042667 := bstep (se 1 (by rfl) ⟨1532000, by rfl⟩ : syracuseStep 2042667 = 3064001) B3064001
theorem B3877885 : Blo 2041435 3877885 := bbase (se 3 (by rfl) ⟨727103, by rfl⟩ : syracuseStep 3877885 = 1454207) (by norm_num)
theorem B5170513 : Blo 2041435 5170513 := bstep (se 2 (by rfl) ⟨1938942, by rfl⟩ : syracuseStep 5170513 = 3877885) B3877885
theorem B6894017 : Blo 2041435 6894017 := bstep (se 2 (by rfl) ⟨2585256, by rfl⟩ : syracuseStep 6894017 = 5170513) B5170513
theorem B4596011 : Blo 2041435 4596011 := bstep (se 1 (by rfl) ⟨3447008, by rfl⟩ : syracuseStep 4596011 = 6894017) B6894017
theorem B3064007 : Blo 2041435 3064007 := bstep (se 1 (by rfl) ⟨2298005, by rfl⟩ : syracuseStep 3064007 = 4596011) B4596011
theorem B2042671 : Blo 2041435 2042671 := bstep (se 1 (by rfl) ⟨1532003, by rfl⟩ : syracuseStep 2042671 = 3064007) B3064007
theorem B3064013 : Blo 2041435 3064013 := bbase (se 3 (by rfl) ⟨574502, by rfl⟩ : syracuseStep 3064013 = 1149005) (by norm_num)
theorem B2042675 : Blo 2041435 2042675 := bstep (se 1 (by rfl) ⟨1532006, by rfl⟩ : syracuseStep 2042675 = 3064013) B3064013
theorem B4596029 : Blo 2041435 4596029 := bbase (se 3 (by rfl) ⟨861755, by rfl⟩ : syracuseStep 4596029 = 1723511) (by norm_num)
theorem B3064019 : Blo 2041435 3064019 := bstep (se 1 (by rfl) ⟨2298014, by rfl⟩ : syracuseStep 3064019 = 4596029) B4596029
theorem B2042679 : Blo 2041435 2042679 := bstep (se 1 (by rfl) ⟨1532009, by rfl⟩ : syracuseStep 2042679 = 3064019) B3064019
theorem B3447029 : Blo 2041435 3447029 := bbase (se 5 (by rfl) ⟨161579, by rfl⟩ : syracuseStep 3447029 = 323159) (by norm_num)
theorem B2298019 : Blo 2041435 2298019 := bstep (se 1 (by rfl) ⟨1723514, by rfl⟩ : syracuseStep 2298019 = 3447029) B3447029
theorem B3064025 : Blo 2041435 3064025 := bstep (se 2 (by rfl) ⟨1149009, by rfl⟩ : syracuseStep 3064025 = 2298019) B2298019
theorem B2042683 : Blo 2041435 2042683 := bstep (se 1 (by rfl) ⟨1532012, by rfl⟩ : syracuseStep 2042683 = 3064025) B3064025
theorem B3731213 : Blo 2041435 3731213 := bbase (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) (by norm_num)
theorem B2487475 : Blo 2041435 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B3316633 : Blo 2041435 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B17688709 : Blo 2041435 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B23584945 : Blo 2041435 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B31446593 : Blo 2041435 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B20964395 : Blo 2041435 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B13976263 : Blo 2041435 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B18635017 : Blo 2041435 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B24846689 : Blo 2041435 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B16564459 : Blo 2041435 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B22085945 : Blo 2041435 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B14723963 : Blo 2041435 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B9815975 : Blo 2041435 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B6543983 : Blo 2041435 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B4362655 : Blo 2041435 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B5816873 : Blo 2041435 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B15511661 : Blo 2041435 15511661 := bstep (se 3 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 15511661 = 5816873) B5816873
theorem B10341107 : Blo 2041435 10341107 := bstep (se 1 (by rfl) ⟨7755830, by rfl⟩ : syracuseStep 10341107 = 15511661) B15511661
theorem B6894071 : Blo 2041435 6894071 := bstep (se 1 (by rfl) ⟨5170553, by rfl⟩ : syracuseStep 6894071 = 10341107) B10341107
theorem B4596047 : Blo 2041435 4596047 := bstep (se 1 (by rfl) ⟨3447035, by rfl⟩ : syracuseStep 4596047 = 6894071) B6894071
theorem B3064031 : Blo 2041435 3064031 := bstep (se 1 (by rfl) ⟨2298023, by rfl⟩ : syracuseStep 3064031 = 4596047) B4596047
theorem B2042687 : Blo 2041435 2042687 := bstep (se 1 (by rfl) ⟨1532015, by rfl⟩ : syracuseStep 2042687 = 3064031) B3064031
theorem B3064037 : Blo 2041435 3064037 := bbase (se 4 (by rfl) ⟨287253, by rfl⟩ : syracuseStep 3064037 = 574507) (by norm_num)
theorem B2042691 : Blo 2041435 2042691 := bstep (se 1 (by rfl) ⟨1532018, by rfl⟩ : syracuseStep 2042691 = 3064037) B3064037
theorem B3272005 : Blo 2041435 3272005 := bbase (se 4 (by rfl) ⟨306750, by rfl⟩ : syracuseStep 3272005 = 613501) (by norm_num)
theorem B4362673 : Blo 2041435 4362673 := bstep (se 2 (by rfl) ⟨1636002, by rfl⟩ : syracuseStep 4362673 = 3272005) B3272005
theorem B5816897 : Blo 2041435 5816897 := bstep (se 2 (by rfl) ⟨2181336, by rfl⟩ : syracuseStep 5816897 = 4362673) B4362673
theorem B3877931 : Blo 2041435 3877931 := bstep (se 1 (by rfl) ⟨2908448, by rfl⟩ : syracuseStep 3877931 = 5816897) B5816897
theorem B2585287 : Blo 2041435 2585287 := bstep (se 1 (by rfl) ⟨1938965, by rfl⟩ : syracuseStep 2585287 = 3877931) B3877931
theorem B3447049 : Blo 2041435 3447049 := bstep (se 2 (by rfl) ⟨1292643, by rfl⟩ : syracuseStep 3447049 = 2585287) B2585287
theorem B4596065 : Blo 2041435 4596065 := bstep (se 2 (by rfl) ⟨1723524, by rfl⟩ : syracuseStep 4596065 = 3447049) B3447049
theorem B3064043 : Blo 2041435 3064043 := bstep (se 1 (by rfl) ⟨2298032, by rfl⟩ : syracuseStep 3064043 = 4596065) B4596065
theorem B2042695 : Blo 2041435 2042695 := bstep (se 1 (by rfl) ⟨1532021, by rfl⟩ : syracuseStep 2042695 = 3064043) B3064043
theorem B2298037 : Blo 2041435 2298037 := bbase (se 5 (by rfl) ⟨107720, by rfl⟩ : syracuseStep 2298037 = 215441) (by norm_num)
theorem B3064049 : Blo 2041435 3064049 := bstep (se 2 (by rfl) ⟨1149018, by rfl⟩ : syracuseStep 3064049 = 2298037) B2298037
theorem B2042699 : Blo 2041435 2042699 := bstep (se 1 (by rfl) ⟨1532024, by rfl⟩ : syracuseStep 2042699 = 3064049) B3064049
theorem B2585297 : Blo 2041435 2585297 := bbase (se 2 (by rfl) ⟨969486, by rfl⟩ : syracuseStep 2585297 = 1938973) (by norm_num)
theorem B6894125 : Blo 2041435 6894125 := bstep (se 3 (by rfl) ⟨1292648, by rfl⟩ : syracuseStep 6894125 = 2585297) B2585297
theorem B4596083 : Blo 2041435 4596083 := bstep (se 1 (by rfl) ⟨3447062, by rfl⟩ : syracuseStep 4596083 = 6894125) B6894125
theorem B3064055 : Blo 2041435 3064055 := bstep (se 1 (by rfl) ⟨2298041, by rfl⟩ : syracuseStep 3064055 = 4596083) B4596083
theorem B2042703 : Blo 2041435 2042703 := bstep (se 1 (by rfl) ⟨1532027, by rfl⟩ : syracuseStep 2042703 = 3064055) B3064055
theorem B3064061 : Blo 2041435 3064061 := bbase (se 3 (by rfl) ⟨574511, by rfl⟩ : syracuseStep 3064061 = 1149023) (by norm_num)
theorem B2042707 : Blo 2041435 2042707 := bstep (se 1 (by rfl) ⟨1532030, by rfl⟩ : syracuseStep 2042707 = 3064061) B3064061
theorem B4596101 : Blo 2041435 4596101 := bbase (se 4 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 4596101 = 861769) (by norm_num)
theorem B3064067 : Blo 2041435 3064067 := bstep (se 1 (by rfl) ⟨2298050, by rfl⟩ : syracuseStep 3064067 = 4596101) B4596101
theorem B2042711 : Blo 2041435 2042711 := bstep (se 1 (by rfl) ⟨1532033, by rfl⟩ : syracuseStep 2042711 = 3064067) B3064067
theorem B2908477 : Blo 2041435 2908477 := bbase (se 3 (by rfl) ⟨545339, by rfl⟩ : syracuseStep 2908477 = 1090679) (by norm_num)
theorem B3877969 : Blo 2041435 3877969 := bstep (se 2 (by rfl) ⟨1454238, by rfl⟩ : syracuseStep 3877969 = 2908477) B2908477
theorem B5170625 : Blo 2041435 5170625 := bstep (se 2 (by rfl) ⟨1938984, by rfl⟩ : syracuseStep 5170625 = 3877969) B3877969
theorem B3447083 : Blo 2041435 3447083 := bstep (se 1 (by rfl) ⟨2585312, by rfl⟩ : syracuseStep 3447083 = 5170625) B5170625
theorem B2298055 : Blo 2041435 2298055 := bstep (se 1 (by rfl) ⟨1723541, by rfl⟩ : syracuseStep 2298055 = 3447083) B3447083
theorem B3064073 : Blo 2041435 3064073 := bstep (se 2 (by rfl) ⟨1149027, by rfl⟩ : syracuseStep 3064073 = 2298055) B2298055
theorem B2042715 : Blo 2041435 2042715 := bstep (se 1 (by rfl) ⟨1532036, by rfl⟩ : syracuseStep 2042715 = 3064073) B3064073
theorem B10341269 : Blo 2041435 10341269 := bbase (se 6 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 10341269 = 484747) (by norm_num)
theorem B6894179 : Blo 2041435 6894179 := bstep (se 1 (by rfl) ⟨5170634, by rfl⟩ : syracuseStep 6894179 = 10341269) B10341269
theorem B4596119 : Blo 2041435 4596119 := bstep (se 1 (by rfl) ⟨3447089, by rfl⟩ : syracuseStep 4596119 = 6894179) B6894179
theorem B3064079 : Blo 2041435 3064079 := bstep (se 1 (by rfl) ⟨2298059, by rfl⟩ : syracuseStep 3064079 = 4596119) B4596119
theorem B2042719 : Blo 2041435 2042719 := bstep (se 1 (by rfl) ⟨1532039, by rfl⟩ : syracuseStep 2042719 = 3064079) B3064079
theorem B3064085 : Blo 2041435 3064085 := bbase (se 6 (by rfl) ⟨71814, by rfl⟩ : syracuseStep 3064085 = 143629) (by norm_num)
theorem B2042723 : Blo 2041435 2042723 := bstep (se 1 (by rfl) ⟨1532042, by rfl⟩ : syracuseStep 2042723 = 3064085) B3064085
theorem B2590733 : Blo 2041435 2590733 := bbase (se 3 (by rfl) ⟨485762, by rfl⟩ : syracuseStep 2590733 = 971525) (by norm_num)
theorem B6908621 : Blo 2041435 6908621 := bstep (se 3 (by rfl) ⟨1295366, by rfl⟩ : syracuseStep 6908621 = 2590733) B2590733
theorem B18422989 : Blo 2041435 18422989 := bstep (se 3 (by rfl) ⟨3454310, by rfl⟩ : syracuseStep 18422989 = 6908621) B6908621
theorem B393023765 : Blo 2041435 393023765 := bstep (se 6 (by rfl) ⟨9211494, by rfl⟩ : syracuseStep 393023765 = 18422989) B18422989
theorem B262015843 : Blo 2041435 262015843 := bstep (se 1 (by rfl) ⟨196511882, by rfl⟩ : syracuseStep 262015843 = 393023765) B393023765
theorem B349354457 : Blo 2041435 349354457 := bstep (se 2 (by rfl) ⟨131007921, by rfl⟩ : syracuseStep 349354457 = 262015843) B262015843
theorem B232902971 : Blo 2041435 232902971 := bstep (se 1 (by rfl) ⟨174677228, by rfl⟩ : syracuseStep 232902971 = 349354457) B349354457
theorem B155268647 : Blo 2041435 155268647 := bstep (se 1 (by rfl) ⟨116451485, by rfl⟩ : syracuseStep 155268647 = 232902971) B232902971
theorem B103512431 : Blo 2041435 103512431 := bstep (se 1 (by rfl) ⟨77634323, by rfl⟩ : syracuseStep 103512431 = 155268647) B155268647
theorem B69008287 : Blo 2041435 69008287 := bstep (se 1 (by rfl) ⟨51756215, by rfl⟩ : syracuseStep 69008287 = 103512431) B103512431
theorem B92011049 : Blo 2041435 92011049 := bstep (se 2 (by rfl) ⟨34504143, by rfl⟩ : syracuseStep 92011049 = 69008287) B69008287
theorem B61340699 : Blo 2041435 61340699 := bstep (se 1 (by rfl) ⟨46005524, by rfl⟩ : syracuseStep 61340699 = 92011049) B92011049
theorem B163575197 : Blo 2041435 163575197 := bstep (se 3 (by rfl) ⟨30670349, by rfl⟩ : syracuseStep 163575197 = 61340699) B61340699
theorem B109050131 : Blo 2041435 109050131 := bstep (se 1 (by rfl) ⟨81787598, by rfl⟩ : syracuseStep 109050131 = 163575197) B163575197
theorem B72700087 : Blo 2041435 72700087 := bstep (se 1 (by rfl) ⟨54525065, by rfl⟩ : syracuseStep 72700087 = 109050131) B109050131
theorem B96933449 : Blo 2041435 96933449 := bstep (se 2 (by rfl) ⟨36350043, by rfl⟩ : syracuseStep 96933449 = 72700087) B72700087
theorem B64622299 : Blo 2041435 64622299 := bstep (se 1 (by rfl) ⟨48466724, by rfl⟩ : syracuseStep 64622299 = 96933449) B96933449
theorem B86163065 : Blo 2041435 86163065 := bstep (se 2 (by rfl) ⟨32311149, by rfl⟩ : syracuseStep 86163065 = 64622299) B64622299
theorem B57442043 : Blo 2041435 57442043 := bstep (se 1 (by rfl) ⟨43081532, by rfl⟩ : syracuseStep 57442043 = 86163065) B86163065
theorem B38294695 : Blo 2041435 38294695 := bstep (se 1 (by rfl) ⟨28721021, by rfl⟩ : syracuseStep 38294695 = 57442043) B57442043
theorem B51059593 : Blo 2041435 51059593 := bstep (se 2 (by rfl) ⟨19147347, by rfl⟩ : syracuseStep 51059593 = 38294695) B38294695
theorem B68079457 : Blo 2041435 68079457 := bstep (se 2 (by rfl) ⟨25529796, by rfl⟩ : syracuseStep 68079457 = 51059593) B51059593
theorem B90772609 : Blo 2041435 90772609 := bstep (se 2 (by rfl) ⟨34039728, by rfl⟩ : syracuseStep 90772609 = 68079457) B68079457
theorem B121030145 : Blo 2041435 121030145 := bstep (se 2 (by rfl) ⟨45386304, by rfl⟩ : syracuseStep 121030145 = 90772609) B90772609
theorem B80686763 : Blo 2041435 80686763 := bstep (se 1 (by rfl) ⟨60515072, by rfl⟩ : syracuseStep 80686763 = 121030145) B121030145
theorem B53791175 : Blo 2041435 53791175 := bstep (se 1 (by rfl) ⟨40343381, by rfl⟩ : syracuseStep 53791175 = 80686763) B80686763
theorem B143443133 : Blo 2041435 143443133 := bstep (se 3 (by rfl) ⟨26895587, by rfl⟩ : syracuseStep 143443133 = 53791175) B53791175
theorem B95628755 : Blo 2041435 95628755 := bstep (se 1 (by rfl) ⟨71721566, by rfl⟩ : syracuseStep 95628755 = 143443133) B143443133
theorem B63752503 : Blo 2041435 63752503 := bstep (se 1 (by rfl) ⟨47814377, by rfl⟩ : syracuseStep 63752503 = 95628755) B95628755
theorem B85003337 : Blo 2041435 85003337 := bstep (se 2 (by rfl) ⟨31876251, by rfl⟩ : syracuseStep 85003337 = 63752503) B63752503
theorem B56668891 : Blo 2041435 56668891 := bstep (se 1 (by rfl) ⟨42501668, by rfl⟩ : syracuseStep 56668891 = 85003337) B85003337
theorem B75558521 : Blo 2041435 75558521 := bstep (se 2 (by rfl) ⟨28334445, by rfl⟩ : syracuseStep 75558521 = 56668891) B56668891
theorem B201489389 : Blo 2041435 201489389 := bstep (se 3 (by rfl) ⟨37779260, by rfl⟩ : syracuseStep 201489389 = 75558521) B75558521
theorem B134326259 : Blo 2041435 134326259 := bstep (se 1 (by rfl) ⟨100744694, by rfl⟩ : syracuseStep 134326259 = 201489389) B201489389
theorem B89550839 : Blo 2041435 89550839 := bstep (se 1 (by rfl) ⟨67163129, by rfl⟩ : syracuseStep 89550839 = 134326259) B134326259
theorem B59700559 : Blo 2041435 59700559 := bstep (se 1 (by rfl) ⟨44775419, by rfl⟩ : syracuseStep 59700559 = 89550839) B89550839
theorem B79600745 : Blo 2041435 79600745 := bstep (se 2 (by rfl) ⟨29850279, by rfl⟩ : syracuseStep 79600745 = 59700559) B59700559
theorem B53067163 : Blo 2041435 53067163 := bstep (se 1 (by rfl) ⟨39800372, by rfl⟩ : syracuseStep 53067163 = 79600745) B79600745
theorem B70756217 : Blo 2041435 70756217 := bstep (se 2 (by rfl) ⟨26533581, by rfl⟩ : syracuseStep 70756217 = 53067163) B53067163
theorem B47170811 : Blo 2041435 47170811 := bstep (se 1 (by rfl) ⟨35378108, by rfl⟩ : syracuseStep 47170811 = 70756217) B70756217
theorem B31447207 : Blo 2041435 31447207 := bstep (se 1 (by rfl) ⟨23585405, by rfl⟩ : syracuseStep 31447207 = 47170811) B47170811
theorem B41929609 : Blo 2041435 41929609 := bstep (se 2 (by rfl) ⟨15723603, by rfl⟩ : syracuseStep 41929609 = 31447207) B31447207
theorem B55906145 : Blo 2041435 55906145 := bstep (se 2 (by rfl) ⟨20964804, by rfl⟩ : syracuseStep 55906145 = 41929609) B41929609
theorem B37270763 : Blo 2041435 37270763 := bstep (se 1 (by rfl) ⟨27953072, by rfl⟩ : syracuseStep 37270763 = 55906145) B55906145
theorem B24847175 : Blo 2041435 24847175 := bstep (se 1 (by rfl) ⟨18635381, by rfl⟩ : syracuseStep 24847175 = 37270763) B37270763
theorem B16564783 : Blo 2041435 16564783 := bstep (se 1 (by rfl) ⟨12423587, by rfl⟩ : syracuseStep 16564783 = 24847175) B24847175
theorem B22086377 : Blo 2041435 22086377 := bstep (se 2 (by rfl) ⟨8282391, by rfl⟩ : syracuseStep 22086377 = 16564783) B16564783
theorem B14724251 : Blo 2041435 14724251 := bstep (se 1 (by rfl) ⟨11043188, by rfl⟩ : syracuseStep 14724251 = 22086377) B22086377
theorem B9816167 : Blo 2041435 9816167 := bstep (se 1 (by rfl) ⟨7362125, by rfl⟩ : syracuseStep 9816167 = 14724251) B14724251
theorem B26176445 : Blo 2041435 26176445 := bstep (se 3 (by rfl) ⟨4908083, by rfl⟩ : syracuseStep 26176445 = 9816167) B9816167
theorem B17450963 : Blo 2041435 17450963 := bstep (se 1 (by rfl) ⟨13088222, by rfl⟩ : syracuseStep 17450963 = 26176445) B26176445
theorem B11633975 : Blo 2041435 11633975 := bstep (se 1 (by rfl) ⟨8725481, by rfl⟩ : syracuseStep 11633975 = 17450963) B17450963
theorem B7755983 : Blo 2041435 7755983 := bstep (se 1 (by rfl) ⟨5816987, by rfl⟩ : syracuseStep 7755983 = 11633975) B11633975
theorem B5170655 : Blo 2041435 5170655 := bstep (se 1 (by rfl) ⟨3877991, by rfl⟩ : syracuseStep 5170655 = 7755983) B7755983
theorem B3447103 : Blo 2041435 3447103 := bstep (se 1 (by rfl) ⟨2585327, by rfl⟩ : syracuseStep 3447103 = 5170655) B5170655
theorem B4596137 : Blo 2041435 4596137 := bstep (se 2 (by rfl) ⟨1723551, by rfl⟩ : syracuseStep 4596137 = 3447103) B3447103
theorem B3064091 : Blo 2041435 3064091 := bstep (se 1 (by rfl) ⟨2298068, by rfl⟩ : syracuseStep 3064091 = 4596137) B4596137
theorem B2042727 : Blo 2041435 2042727 := bstep (se 1 (by rfl) ⟨1532045, by rfl⟩ : syracuseStep 2042727 = 3064091) B3064091
theorem B2298073 : Blo 2041435 2298073 := bbase (se 2 (by rfl) ⟨861777, by rfl⟩ : syracuseStep 2298073 = 1723555) (by norm_num)
theorem B3064097 : Blo 2041435 3064097 := bstep (se 2 (by rfl) ⟨1149036, by rfl⟩ : syracuseStep 3064097 = 2298073) B2298073
theorem B2042731 : Blo 2041435 2042731 := bstep (se 1 (by rfl) ⟨1532048, by rfl⟩ : syracuseStep 2042731 = 3064097) B3064097
theorem B3272069 : Blo 2041435 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B2181379 : Blo 2041435 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B2908505 : Blo 2041435 2908505 := bstep (se 2 (by rfl) ⟨1090689, by rfl⟩ : syracuseStep 2908505 = 2181379) B2181379
theorem B7756013 : Blo 2041435 7756013 := bstep (se 3 (by rfl) ⟨1454252, by rfl⟩ : syracuseStep 7756013 = 2908505) B2908505
theorem B5170675 : Blo 2041435 5170675 := bstep (se 1 (by rfl) ⟨3878006, by rfl⟩ : syracuseStep 5170675 = 7756013) B7756013
theorem B6894233 : Blo 2041435 6894233 := bstep (se 2 (by rfl) ⟨2585337, by rfl⟩ : syracuseStep 6894233 = 5170675) B5170675
theorem B4596155 : Blo 2041435 4596155 := bstep (se 1 (by rfl) ⟨3447116, by rfl⟩ : syracuseStep 4596155 = 6894233) B6894233
theorem B3064103 : Blo 2041435 3064103 := bstep (se 1 (by rfl) ⟨2298077, by rfl⟩ : syracuseStep 3064103 = 4596155) B4596155
theorem B2042735 : Blo 2041435 2042735 := bstep (se 1 (by rfl) ⟨1532051, by rfl⟩ : syracuseStep 2042735 = 3064103) B3064103
theorem B3064109 : Blo 2041435 3064109 := bbase (se 3 (by rfl) ⟨574520, by rfl⟩ : syracuseStep 3064109 = 1149041) (by norm_num)
theorem B2042739 : Blo 2041435 2042739 := bstep (se 1 (by rfl) ⟨1532054, by rfl⟩ : syracuseStep 2042739 = 3064109) B3064109
theorem B4596173 : Blo 2041435 4596173 := bbase (se 3 (by rfl) ⟨861782, by rfl⟩ : syracuseStep 4596173 = 1723565) (by norm_num)
theorem B3064115 : Blo 2041435 3064115 := bstep (se 1 (by rfl) ⟨2298086, by rfl⟩ : syracuseStep 3064115 = 4596173) B4596173
theorem B2042743 : Blo 2041435 2042743 := bstep (se 1 (by rfl) ⟨1532057, by rfl⟩ : syracuseStep 2042743 = 3064115) B3064115
theorem B2585353 : Blo 2041435 2585353 := bbase (se 2 (by rfl) ⟨969507, by rfl⟩ : syracuseStep 2585353 = 1939015) (by norm_num)
theorem B3447137 : Blo 2041435 3447137 := bstep (se 2 (by rfl) ⟨1292676, by rfl⟩ : syracuseStep 3447137 = 2585353) B2585353
theorem B2298091 : Blo 2041435 2298091 := bstep (se 1 (by rfl) ⟨1723568, by rfl⟩ : syracuseStep 2298091 = 3447137) B3447137
theorem B3064121 : Blo 2041435 3064121 := bstep (se 2 (by rfl) ⟨1149045, by rfl⟩ : syracuseStep 3064121 = 2298091) B2298091
theorem B2042747 : Blo 2041435 2042747 := bstep (se 1 (by rfl) ⟨1532060, by rfl⟩ : syracuseStep 2042747 = 3064121) B3064121
theorem B11043317 : Blo 2041435 11043317 := bbase (se 5 (by rfl) ⟨517655, by rfl⟩ : syracuseStep 11043317 = 1035311) (by norm_num)
theorem B29448845 : Blo 2041435 29448845 := bstep (se 3 (by rfl) ⟨5521658, by rfl⟩ : syracuseStep 29448845 = 11043317) B11043317
theorem B19632563 : Blo 2041435 19632563 := bstep (se 1 (by rfl) ⟨14724422, by rfl⟩ : syracuseStep 19632563 = 29448845) B29448845
theorem B13088375 : Blo 2041435 13088375 := bstep (se 1 (by rfl) ⟨9816281, by rfl⟩ : syracuseStep 13088375 = 19632563) B19632563
theorem B8725583 : Blo 2041435 8725583 := bstep (se 1 (by rfl) ⟨6544187, by rfl⟩ : syracuseStep 8725583 = 13088375) B13088375
theorem B23268221 : Blo 2041435 23268221 := bstep (se 3 (by rfl) ⟨4362791, by rfl⟩ : syracuseStep 23268221 = 8725583) B8725583
theorem B15512147 : Blo 2041435 15512147 := bstep (se 1 (by rfl) ⟨11634110, by rfl⟩ : syracuseStep 15512147 = 23268221) B23268221
theorem B10341431 : Blo 2041435 10341431 := bstep (se 1 (by rfl) ⟨7756073, by rfl⟩ : syracuseStep 10341431 = 15512147) B15512147
theorem B6894287 : Blo 2041435 6894287 := bstep (se 1 (by rfl) ⟨5170715, by rfl⟩ : syracuseStep 6894287 = 10341431) B10341431
theorem B4596191 : Blo 2041435 4596191 := bstep (se 1 (by rfl) ⟨3447143, by rfl⟩ : syracuseStep 4596191 = 6894287) B6894287
theorem B3064127 : Blo 2041435 3064127 := bstep (se 1 (by rfl) ⟨2298095, by rfl⟩ : syracuseStep 3064127 = 4596191) B4596191
theorem B2042751 : Blo 2041435 2042751 := bstep (se 1 (by rfl) ⟨1532063, by rfl⟩ : syracuseStep 2042751 = 3064127) B3064127
theorem B3064133 : Blo 2041435 3064133 := bbase (se 4 (by rfl) ⟨287262, by rfl⟩ : syracuseStep 3064133 = 574525) (by norm_num)
theorem B2042755 : Blo 2041435 2042755 := bstep (se 1 (by rfl) ⟨1532066, by rfl⟩ : syracuseStep 2042755 = 3064133) B3064133
theorem B3447157 : Blo 2041435 3447157 := bbase (se 5 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 3447157 = 323171) (by norm_num)
theorem B4596209 : Blo 2041435 4596209 := bstep (se 2 (by rfl) ⟨1723578, by rfl⟩ : syracuseStep 4596209 = 3447157) B3447157
theorem B3064139 : Blo 2041435 3064139 := bstep (se 1 (by rfl) ⟨2298104, by rfl⟩ : syracuseStep 3064139 = 4596209) B4596209
theorem B2042759 : Blo 2041435 2042759 := bstep (se 1 (by rfl) ⟨1532069, by rfl⟩ : syracuseStep 2042759 = 3064139) B3064139
theorem B2298109 : Blo 2041435 2298109 := bbase (se 3 (by rfl) ⟨430895, by rfl⟩ : syracuseStep 2298109 = 861791) (by norm_num)
theorem B3064145 : Blo 2041435 3064145 := bstep (se 2 (by rfl) ⟨1149054, by rfl⟩ : syracuseStep 3064145 = 2298109) B2298109
theorem B2042763 : Blo 2041435 2042763 := bstep (se 1 (by rfl) ⟨1532072, by rfl⟩ : syracuseStep 2042763 = 3064145) B3064145
theorem B6894341 : Blo 2041435 6894341 := bbase (se 4 (by rfl) ⟨646344, by rfl⟩ : syracuseStep 6894341 = 1292689) (by norm_num)
theorem B4596227 : Blo 2041435 4596227 := bstep (se 1 (by rfl) ⟨3447170, by rfl⟩ : syracuseStep 4596227 = 6894341) B6894341
theorem B3064151 : Blo 2041435 3064151 := bstep (se 1 (by rfl) ⟨2298113, by rfl⟩ : syracuseStep 3064151 = 4596227) B4596227
theorem B2042767 : Blo 2041435 2042767 := bstep (se 1 (by rfl) ⟨1532075, by rfl⟩ : syracuseStep 2042767 = 3064151) B3064151
theorem B3064157 : Blo 2041435 3064157 := bbase (se 3 (by rfl) ⟨574529, by rfl⟩ : syracuseStep 3064157 = 1149059) (by norm_num)
theorem B2042771 : Blo 2041435 2042771 := bstep (se 1 (by rfl) ⟨1532078, by rfl⟩ : syracuseStep 2042771 = 3064157) B3064157
theorem B4596245 : Blo 2041435 4596245 := bbase (se 6 (by rfl) ⟨107724, by rfl⟩ : syracuseStep 4596245 = 215449) (by norm_num)
theorem B3064163 : Blo 2041435 3064163 := bstep (se 1 (by rfl) ⟨2298122, by rfl⟩ : syracuseStep 3064163 = 4596245) B4596245
theorem B2042775 : Blo 2041435 2042775 := bstep (se 1 (by rfl) ⟨1532081, by rfl⟩ : syracuseStep 2042775 = 3064163) B3064163
theorem B7756181 : Blo 2041435 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B5170787 : Blo 2041435 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B3447191 : Blo 2041435 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B2298127 : Blo 2041435 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B3064169 : Blo 2041435 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B2042779 : Blo 2041435 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B11634293 : Blo 2041435 11634293 := bbase (se 5 (by rfl) ⟨545357, by rfl⟩ : syracuseStep 11634293 = 1090715) (by norm_num)
theorem B7756195 : Blo 2041435 7756195 := bstep (se 1 (by rfl) ⟨5817146, by rfl⟩ : syracuseStep 7756195 = 11634293) B11634293
theorem B10341593 : Blo 2041435 10341593 := bstep (se 2 (by rfl) ⟨3878097, by rfl⟩ : syracuseStep 10341593 = 7756195) B7756195
theorem B6894395 : Blo 2041435 6894395 := bstep (se 1 (by rfl) ⟨5170796, by rfl⟩ : syracuseStep 6894395 = 10341593) B10341593
theorem B4596263 : Blo 2041435 4596263 := bstep (se 1 (by rfl) ⟨3447197, by rfl⟩ : syracuseStep 4596263 = 6894395) B6894395
theorem B3064175 : Blo 2041435 3064175 := bstep (se 1 (by rfl) ⟨2298131, by rfl⟩ : syracuseStep 3064175 = 4596263) B4596263
theorem B2042783 : Blo 2041435 2042783 := bstep (se 1 (by rfl) ⟨1532087, by rfl⟩ : syracuseStep 2042783 = 3064175) B3064175
theorem B3064181 : Blo 2041435 3064181 := bbase (se 5 (by rfl) ⟨143633, by rfl⟩ : syracuseStep 3064181 = 287267) (by norm_num)
theorem B2042787 : Blo 2041435 2042787 := bstep (se 1 (by rfl) ⟨1532090, by rfl⟩ : syracuseStep 2042787 = 3064181) B3064181
theorem B13976981 : Blo 2041435 13976981 := bbase (se 6 (by rfl) ⟨327585, by rfl⟩ : syracuseStep 13976981 = 655171) (by norm_num)
theorem B9317987 : Blo 2041435 9317987 := bstep (se 1 (by rfl) ⟨6988490, by rfl⟩ : syracuseStep 9317987 = 13976981) B13976981
theorem B6211991 : Blo 2041435 6211991 := bstep (se 1 (by rfl) ⟨4658993, by rfl⟩ : syracuseStep 6211991 = 9317987) B9317987
theorem B16565309 : Blo 2041435 16565309 := bstep (se 3 (by rfl) ⟨3105995, by rfl⟩ : syracuseStep 16565309 = 6211991) B6211991
theorem B11043539 : Blo 2041435 11043539 := bstep (se 1 (by rfl) ⟨8282654, by rfl⟩ : syracuseStep 11043539 = 16565309) B16565309
theorem B7362359 : Blo 2041435 7362359 := bstep (se 1 (by rfl) ⟨5521769, by rfl⟩ : syracuseStep 7362359 = 11043539) B11043539
theorem B4908239 : Blo 2041435 4908239 := bstep (se 1 (by rfl) ⟨3681179, by rfl⟩ : syracuseStep 4908239 = 7362359) B7362359
theorem B3272159 : Blo 2041435 3272159 := bstep (se 1 (by rfl) ⟨2454119, by rfl⟩ : syracuseStep 3272159 = 4908239) B4908239
theorem B2181439 : Blo 2041435 2181439 := bstep (se 1 (by rfl) ⟨1636079, by rfl⟩ : syracuseStep 2181439 = 3272159) B3272159
theorem B2908585 : Blo 2041435 2908585 := bstep (se 2 (by rfl) ⟨1090719, by rfl⟩ : syracuseStep 2908585 = 2181439) B2181439
theorem B3878113 : Blo 2041435 3878113 := bstep (se 2 (by rfl) ⟨1454292, by rfl⟩ : syracuseStep 3878113 = 2908585) B2908585
theorem B5170817 : Blo 2041435 5170817 := bstep (se 2 (by rfl) ⟨1939056, by rfl⟩ : syracuseStep 5170817 = 3878113) B3878113
theorem B3447211 : Blo 2041435 3447211 := bstep (se 1 (by rfl) ⟨2585408, by rfl⟩ : syracuseStep 3447211 = 5170817) B5170817
theorem B4596281 : Blo 2041435 4596281 := bstep (se 2 (by rfl) ⟨1723605, by rfl⟩ : syracuseStep 4596281 = 3447211) B3447211
theorem B3064187 : Blo 2041435 3064187 := bstep (se 1 (by rfl) ⟨2298140, by rfl⟩ : syracuseStep 3064187 = 4596281) B4596281
theorem B2042791 : Blo 2041435 2042791 := bstep (se 1 (by rfl) ⟨1532093, by rfl⟩ : syracuseStep 2042791 = 3064187) B3064187
theorem B2298145 : Blo 2041435 2298145 := bbase (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) (by norm_num)
theorem B3064193 : Blo 2041435 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B2042795 : Blo 2041435 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B5170837 : Blo 2041435 5170837 := bbase (se 6 (by rfl) ⟨121191, by rfl⟩ : syracuseStep 5170837 = 242383) (by norm_num)
theorem B6894449 : Blo 2041435 6894449 := bstep (se 2 (by rfl) ⟨2585418, by rfl⟩ : syracuseStep 6894449 = 5170837) B5170837
theorem B4596299 : Blo 2041435 4596299 := bstep (se 1 (by rfl) ⟨3447224, by rfl⟩ : syracuseStep 4596299 = 6894449) B6894449
theorem B3064199 : Blo 2041435 3064199 := bstep (se 1 (by rfl) ⟨2298149, by rfl⟩ : syracuseStep 3064199 = 4596299) B4596299
theorem B2042799 : Blo 2041435 2042799 := bstep (se 1 (by rfl) ⟨1532099, by rfl⟩ : syracuseStep 2042799 = 3064199) B3064199
theorem B3064205 : Blo 2041435 3064205 := bbase (se 3 (by rfl) ⟨574538, by rfl⟩ : syracuseStep 3064205 = 1149077) (by norm_num)
theorem B2042803 : Blo 2041435 2042803 := bstep (se 1 (by rfl) ⟨1532102, by rfl⟩ : syracuseStep 2042803 = 3064205) B3064205
theorem B4596317 : Blo 2041435 4596317 := bbase (se 3 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 4596317 = 1723619) (by norm_num)
theorem B3064211 : Blo 2041435 3064211 := bstep (se 1 (by rfl) ⟨2298158, by rfl⟩ : syracuseStep 3064211 = 4596317) B4596317
theorem B2042807 : Blo 2041435 2042807 := bstep (se 1 (by rfl) ⟨1532105, by rfl⟩ : syracuseStep 2042807 = 3064211) B3064211
theorem B3447245 : Blo 2041435 3447245 := bbase (se 3 (by rfl) ⟨646358, by rfl⟩ : syracuseStep 3447245 = 1292717) (by norm_num)
theorem B2298163 : Blo 2041435 2298163 := bstep (se 1 (by rfl) ⟨1723622, by rfl⟩ : syracuseStep 2298163 = 3447245) B3447245
theorem B3064217 : Blo 2041435 3064217 := bstep (se 2 (by rfl) ⟨1149081, by rfl⟩ : syracuseStep 3064217 = 2298163) B2298163
theorem B2042811 : Blo 2041435 2042811 := bstep (se 1 (by rfl) ⟨1532108, by rfl⟩ : syracuseStep 2042811 = 3064217) B3064217
theorem B3681221 : Blo 2041435 3681221 := bbase (se 4 (by rfl) ⟨345114, by rfl⟩ : syracuseStep 3681221 = 690229) (by norm_num)
theorem B9816589 : Blo 2041435 9816589 := bstep (se 3 (by rfl) ⟨1840610, by rfl⟩ : syracuseStep 9816589 = 3681221) B3681221
theorem B13088785 : Blo 2041435 13088785 := bstep (se 2 (by rfl) ⟨4908294, by rfl⟩ : syracuseStep 13088785 = 9816589) B9816589
theorem B17451713 : Blo 2041435 17451713 := bstep (se 2 (by rfl) ⟨6544392, by rfl⟩ : syracuseStep 17451713 = 13088785) B13088785
theorem B11634475 : Blo 2041435 11634475 := bstep (se 1 (by rfl) ⟨8725856, by rfl⟩ : syracuseStep 11634475 = 17451713) B17451713
theorem B15512633 : Blo 2041435 15512633 := bstep (se 2 (by rfl) ⟨5817237, by rfl⟩ : syracuseStep 15512633 = 11634475) B11634475
theorem B10341755 : Blo 2041435 10341755 := bstep (se 1 (by rfl) ⟨7756316, by rfl⟩ : syracuseStep 10341755 = 15512633) B15512633
theorem B6894503 : Blo 2041435 6894503 := bstep (se 1 (by rfl) ⟨5170877, by rfl⟩ : syracuseStep 6894503 = 10341755) B10341755
theorem B4596335 : Blo 2041435 4596335 := bstep (se 1 (by rfl) ⟨3447251, by rfl⟩ : syracuseStep 4596335 = 6894503) B6894503
theorem B3064223 : Blo 2041435 3064223 := bstep (se 1 (by rfl) ⟨2298167, by rfl⟩ : syracuseStep 3064223 = 4596335) B4596335
theorem B2042815 : Blo 2041435 2042815 := bstep (se 1 (by rfl) ⟨1532111, by rfl⟩ : syracuseStep 2042815 = 3064223) B3064223
theorem B3064229 : Blo 2041435 3064229 := bbase (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) (by norm_num)
theorem B2042819 : Blo 2041435 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B2585449 : Blo 2041435 2585449 := bbase (se 2 (by rfl) ⟨969543, by rfl⟩ : syracuseStep 2585449 = 1939087) (by norm_num)
theorem B3447265 : Blo 2041435 3447265 := bstep (se 2 (by rfl) ⟨1292724, by rfl⟩ : syracuseStep 3447265 = 2585449) B2585449
theorem B4596353 : Blo 2041435 4596353 := bstep (se 2 (by rfl) ⟨1723632, by rfl⟩ : syracuseStep 4596353 = 3447265) B3447265
theorem B3064235 : Blo 2041435 3064235 := bstep (se 1 (by rfl) ⟨2298176, by rfl⟩ : syracuseStep 3064235 = 4596353) B4596353
theorem B2042823 : Blo 2041435 2042823 := bstep (se 1 (by rfl) ⟨1532117, by rfl⟩ : syracuseStep 2042823 = 3064235) B3064235
theorem B2298181 : Blo 2041435 2298181 := bbase (se 4 (by rfl) ⟨215454, by rfl⟩ : syracuseStep 2298181 = 430909) (by norm_num)
theorem B3064241 : Blo 2041435 3064241 := bstep (se 2 (by rfl) ⟨1149090, by rfl⟩ : syracuseStep 3064241 = 2298181) B2298181
theorem B2042827 : Blo 2041435 2042827 := bstep (se 1 (by rfl) ⟨1532120, by rfl⟩ : syracuseStep 2042827 = 3064241) B3064241
theorem B3878189 : Blo 2041435 3878189 := bbase (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) (by norm_num)
theorem B2585459 : Blo 2041435 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B6894557 : Blo 2041435 6894557 := bstep (se 3 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 6894557 = 2585459) B2585459
theorem B4596371 : Blo 2041435 4596371 := bstep (se 1 (by rfl) ⟨3447278, by rfl⟩ : syracuseStep 4596371 = 6894557) B6894557
theorem B3064247 : Blo 2041435 3064247 := bstep (se 1 (by rfl) ⟨2298185, by rfl⟩ : syracuseStep 3064247 = 4596371) B4596371
theorem B2042831 : Blo 2041435 2042831 := bstep (se 1 (by rfl) ⟨1532123, by rfl⟩ : syracuseStep 2042831 = 3064247) B3064247
theorem B3064253 : Blo 2041435 3064253 := bbase (se 3 (by rfl) ⟨574547, by rfl⟩ : syracuseStep 3064253 = 1149095) (by norm_num)
theorem B2042835 : Blo 2041435 2042835 := bstep (se 1 (by rfl) ⟨1532126, by rfl⟩ : syracuseStep 2042835 = 3064253) B3064253
theorem B4596389 : Blo 2041435 4596389 := bbase (se 4 (by rfl) ⟨430911, by rfl⟩ : syracuseStep 4596389 = 861823) (by norm_num)
theorem B3064259 : Blo 2041435 3064259 := bstep (se 1 (by rfl) ⟨2298194, by rfl⟩ : syracuseStep 3064259 = 4596389) B4596389
theorem B2042839 : Blo 2041435 2042839 := bstep (se 1 (by rfl) ⟨1532129, by rfl⟩ : syracuseStep 2042839 = 3064259) B3064259
theorem B5170949 : Blo 2041435 5170949 := bbase (se 4 (by rfl) ⟨484776, by rfl⟩ : syracuseStep 5170949 = 969553) (by norm_num)
theorem B3447299 : Blo 2041435 3447299 := bstep (se 1 (by rfl) ⟨2585474, by rfl⟩ : syracuseStep 3447299 = 5170949) B5170949
theorem B2298199 : Blo 2041435 2298199 := bstep (se 1 (by rfl) ⟨1723649, by rfl⟩ : syracuseStep 2298199 = 3447299) B3447299
theorem B3064265 : Blo 2041435 3064265 := bstep (se 2 (by rfl) ⟨1149099, by rfl⟩ : syracuseStep 3064265 = 2298199) B2298199
theorem B2042843 : Blo 2041435 2042843 := bstep (se 1 (by rfl) ⟨1532132, by rfl⟩ : syracuseStep 2042843 = 3064265) B3064265
theorem B4362997 : Blo 2041435 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B5817329 : Blo 2041435 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B3878219 : Blo 2041435 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B10341917 : Blo 2041435 10341917 := bstep (se 3 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 10341917 = 3878219) B3878219
theorem B6894611 : Blo 2041435 6894611 := bstep (se 1 (by rfl) ⟨5170958, by rfl⟩ : syracuseStep 6894611 = 10341917) B10341917
theorem B4596407 : Blo 2041435 4596407 := bstep (se 1 (by rfl) ⟨3447305, by rfl⟩ : syracuseStep 4596407 = 6894611) B6894611
theorem B3064271 : Blo 2041435 3064271 := bstep (se 1 (by rfl) ⟨2298203, by rfl⟩ : syracuseStep 3064271 = 4596407) B4596407
theorem B2042847 : Blo 2041435 2042847 := bstep (se 1 (by rfl) ⟨1532135, by rfl⟩ : syracuseStep 2042847 = 3064271) B3064271
theorem B3064277 : Blo 2041435 3064277 := bbase (se 7 (by rfl) ⟨35909, by rfl⟩ : syracuseStep 3064277 = 71819) (by norm_num)
theorem B2042851 : Blo 2041435 2042851 := bstep (se 1 (by rfl) ⟨1532138, by rfl⟩ : syracuseStep 2042851 = 3064277) B3064277
theorem B7756469 : Blo 2041435 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B5170979 : Blo 2041435 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B3447319 : Blo 2041435 3447319 := bstep (se 1 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 3447319 = 5170979) B5170979
theorem B4596425 : Blo 2041435 4596425 := bstep (se 2 (by rfl) ⟨1723659, by rfl⟩ : syracuseStep 4596425 = 3447319) B3447319
theorem B3064283 : Blo 2041435 3064283 := bstep (se 1 (by rfl) ⟨2298212, by rfl⟩ : syracuseStep 3064283 = 4596425) B4596425
theorem B2042855 : Blo 2041435 2042855 := bstep (se 1 (by rfl) ⟨1532141, by rfl⟩ : syracuseStep 2042855 = 3064283) B3064283
theorem B2298217 : Blo 2041435 2298217 := bbase (se 2 (by rfl) ⟨861831, by rfl⟩ : syracuseStep 2298217 = 1723663) (by norm_num)
theorem B3064289 : Blo 2041435 3064289 := bstep (se 2 (by rfl) ⟨1149108, by rfl⟩ : syracuseStep 3064289 = 2298217) B2298217
theorem B2042859 : Blo 2041435 2042859 := bstep (se 1 (by rfl) ⟨1532144, by rfl⟩ : syracuseStep 2042859 = 3064289) B3064289
theorem B9816821 : Blo 2041435 9816821 := bbase (se 5 (by rfl) ⟨460163, by rfl⟩ : syracuseStep 9816821 = 920327) (by norm_num)
theorem B6544547 : Blo 2041435 6544547 := bstep (se 1 (by rfl) ⟨4908410, by rfl⟩ : syracuseStep 6544547 = 9816821) B9816821
theorem B4363031 : Blo 2041435 4363031 := bstep (se 1 (by rfl) ⟨3272273, by rfl⟩ : syracuseStep 4363031 = 6544547) B6544547
theorem B11634749 : Blo 2041435 11634749 := bstep (se 3 (by rfl) ⟨2181515, by rfl⟩ : syracuseStep 11634749 = 4363031) B4363031
theorem B7756499 : Blo 2041435 7756499 := bstep (se 1 (by rfl) ⟨5817374, by rfl⟩ : syracuseStep 7756499 = 11634749) B11634749
theorem B5170999 : Blo 2041435 5170999 := bstep (se 1 (by rfl) ⟨3878249, by rfl⟩ : syracuseStep 5170999 = 7756499) B7756499
theorem B6894665 : Blo 2041435 6894665 := bstep (se 2 (by rfl) ⟨2585499, by rfl⟩ : syracuseStep 6894665 = 5170999) B5170999
theorem B4596443 : Blo 2041435 4596443 := bstep (se 1 (by rfl) ⟨3447332, by rfl⟩ : syracuseStep 4596443 = 6894665) B6894665
theorem B3064295 : Blo 2041435 3064295 := bstep (se 1 (by rfl) ⟨2298221, by rfl⟩ : syracuseStep 3064295 = 4596443) B4596443
theorem B2042863 : Blo 2041435 2042863 := bstep (se 1 (by rfl) ⟨1532147, by rfl⟩ : syracuseStep 2042863 = 3064295) B3064295
theorem B3064301 : Blo 2041435 3064301 := bbase (se 3 (by rfl) ⟨574556, by rfl⟩ : syracuseStep 3064301 = 1149113) (by norm_num)
theorem B2042867 : Blo 2041435 2042867 := bstep (se 1 (by rfl) ⟨1532150, by rfl⟩ : syracuseStep 2042867 = 3064301) B3064301
theorem B4596461 : Blo 2041435 4596461 := bbase (se 3 (by rfl) ⟨861836, by rfl⟩ : syracuseStep 4596461 = 1723673) (by norm_num)
theorem B3064307 : Blo 2041435 3064307 := bstep (se 1 (by rfl) ⟨2298230, by rfl⟩ : syracuseStep 3064307 = 4596461) B4596461
theorem B2042871 : Blo 2041435 2042871 := bstep (se 1 (by rfl) ⟨1532153, by rfl⟩ : syracuseStep 2042871 = 3064307) B3064307
theorem B2181529 : Blo 2041435 2181529 := bbase (se 2 (by rfl) ⟨818073, by rfl⟩ : syracuseStep 2181529 = 1636147) (by norm_num)
theorem B2908705 : Blo 2041435 2908705 := bstep (se 2 (by rfl) ⟨1090764, by rfl⟩ : syracuseStep 2908705 = 2181529) B2181529
theorem B3878273 : Blo 2041435 3878273 := bstep (se 2 (by rfl) ⟨1454352, by rfl⟩ : syracuseStep 3878273 = 2908705) B2908705
theorem B2585515 : Blo 2041435 2585515 := bstep (se 1 (by rfl) ⟨1939136, by rfl⟩ : syracuseStep 2585515 = 3878273) B3878273
theorem B3447353 : Blo 2041435 3447353 := bstep (se 2 (by rfl) ⟨1292757, by rfl⟩ : syracuseStep 3447353 = 2585515) B2585515
theorem B2298235 : Blo 2041435 2298235 := bstep (se 1 (by rfl) ⟨1723676, by rfl⟩ : syracuseStep 2298235 = 3447353) B3447353
theorem B3064313 : Blo 2041435 3064313 := bstep (se 2 (by rfl) ⟨1149117, by rfl⟩ : syracuseStep 3064313 = 2298235) B2298235
theorem B2042875 : Blo 2041435 2042875 := bstep (se 1 (by rfl) ⟨1532156, by rfl⟩ : syracuseStep 2042875 = 3064313) B3064313
theorem B5896789 : Blo 2041435 5896789 := bbase (se 8 (by rfl) ⟨34551, by rfl⟩ : syracuseStep 5896789 = 69103) (by norm_num)
theorem B31449541 : Blo 2041435 31449541 := bstep (se 4 (by rfl) ⟨2948394, by rfl⟩ : syracuseStep 31449541 = 5896789) B5896789
theorem B41932721 : Blo 2041435 41932721 := bstep (se 2 (by rfl) ⟨15724770, by rfl⟩ : syracuseStep 41932721 = 31449541) B31449541
theorem B27955147 : Blo 2041435 27955147 := bstep (se 1 (by rfl) ⟨20966360, by rfl⟩ : syracuseStep 27955147 = 41932721) B41932721
theorem B37273529 : Blo 2041435 37273529 := bstep (se 2 (by rfl) ⟨13977573, by rfl⟩ : syracuseStep 37273529 = 27955147) B27955147
theorem B24849019 : Blo 2041435 24849019 := bstep (se 1 (by rfl) ⟨18636764, by rfl⟩ : syracuseStep 24849019 = 37273529) B37273529
theorem B33132025 : Blo 2041435 33132025 := bstep (se 2 (by rfl) ⟨12424509, by rfl⟩ : syracuseStep 33132025 = 24849019) B24849019
theorem B44176033 : Blo 2041435 44176033 := bstep (se 2 (by rfl) ⟨16566012, by rfl⟩ : syracuseStep 44176033 = 33132025) B33132025
theorem B58901377 : Blo 2041435 58901377 := bstep (se 2 (by rfl) ⟨22088016, by rfl⟩ : syracuseStep 58901377 = 44176033) B44176033
theorem B78535169 : Blo 2041435 78535169 := bstep (se 2 (by rfl) ⟨29450688, by rfl⟩ : syracuseStep 78535169 = 58901377) B58901377
theorem B52356779 : Blo 2041435 52356779 := bstep (se 1 (by rfl) ⟨39267584, by rfl⟩ : syracuseStep 52356779 = 78535169) B78535169
theorem B34904519 : Blo 2041435 34904519 := bstep (se 1 (by rfl) ⟨26178389, by rfl⟩ : syracuseStep 34904519 = 52356779) B52356779
theorem B23269679 : Blo 2041435 23269679 := bstep (se 1 (by rfl) ⟨17452259, by rfl⟩ : syracuseStep 23269679 = 34904519) B34904519
theorem B15513119 : Blo 2041435 15513119 := bstep (se 1 (by rfl) ⟨11634839, by rfl⟩ : syracuseStep 15513119 = 23269679) B23269679
theorem B10342079 : Blo 2041435 10342079 := bstep (se 1 (by rfl) ⟨7756559, by rfl⟩ : syracuseStep 10342079 = 15513119) B15513119
theorem B6894719 : Blo 2041435 6894719 := bstep (se 1 (by rfl) ⟨5171039, by rfl⟩ : syracuseStep 6894719 = 10342079) B10342079
theorem B4596479 : Blo 2041435 4596479 := bstep (se 1 (by rfl) ⟨3447359, by rfl⟩ : syracuseStep 4596479 = 6894719) B6894719
theorem B3064319 : Blo 2041435 3064319 := bstep (se 1 (by rfl) ⟨2298239, by rfl⟩ : syracuseStep 3064319 = 4596479) B4596479
theorem B2042879 : Blo 2041435 2042879 := bstep (se 1 (by rfl) ⟨1532159, by rfl⟩ : syracuseStep 2042879 = 3064319) B3064319
theorem B3064325 : Blo 2041435 3064325 := bbase (se 4 (by rfl) ⟨287280, by rfl⟩ : syracuseStep 3064325 = 574561) (by norm_num)
theorem B2042883 : Blo 2041435 2042883 := bstep (se 1 (by rfl) ⟨1532162, by rfl⟩ : syracuseStep 2042883 = 3064325) B3064325
theorem B3447373 : Blo 2041435 3447373 := bbase (se 3 (by rfl) ⟨646382, by rfl⟩ : syracuseStep 3447373 = 1292765) (by norm_num)
theorem B4596497 : Blo 2041435 4596497 := bstep (se 2 (by rfl) ⟨1723686, by rfl⟩ : syracuseStep 4596497 = 3447373) B3447373
theorem B3064331 : Blo 2041435 3064331 := bstep (se 1 (by rfl) ⟨2298248, by rfl⟩ : syracuseStep 3064331 = 4596497) B4596497
theorem B2042887 : Blo 2041435 2042887 := bstep (se 1 (by rfl) ⟨1532165, by rfl⟩ : syracuseStep 2042887 = 3064331) B3064331
theorem B2298253 : Blo 2041435 2298253 := bbase (se 3 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 2298253 = 861845) (by norm_num)
theorem B3064337 : Blo 2041435 3064337 := bstep (se 2 (by rfl) ⟨1149126, by rfl⟩ : syracuseStep 3064337 = 2298253) B2298253
theorem B2042891 : Blo 2041435 2042891 := bstep (se 1 (by rfl) ⟨1532168, by rfl⟩ : syracuseStep 2042891 = 3064337) B3064337
theorem B6894773 : Blo 2041435 6894773 := bbase (se 5 (by rfl) ⟨323192, by rfl⟩ : syracuseStep 6894773 = 646385) (by norm_num)
theorem B4596515 : Blo 2041435 4596515 := bstep (se 1 (by rfl) ⟨3447386, by rfl⟩ : syracuseStep 4596515 = 6894773) B6894773
theorem B3064343 : Blo 2041435 3064343 := bstep (se 1 (by rfl) ⟨2298257, by rfl⟩ : syracuseStep 3064343 = 4596515) B4596515
theorem B2042895 : Blo 2041435 2042895 := bstep (se 1 (by rfl) ⟨1532171, by rfl⟩ : syracuseStep 2042895 = 3064343) B3064343
theorem B3064349 : Blo 2041435 3064349 := bbase (se 3 (by rfl) ⟨574565, by rfl⟩ : syracuseStep 3064349 = 1149131) (by norm_num)
theorem B2042899 : Blo 2041435 2042899 := bstep (se 1 (by rfl) ⟨1532174, by rfl⟩ : syracuseStep 2042899 = 3064349) B3064349
theorem B4596533 : Blo 2041435 4596533 := bbase (se 5 (by rfl) ⟨215462, by rfl⟩ : syracuseStep 4596533 = 430925) (by norm_num)
theorem B3064355 : Blo 2041435 3064355 := bstep (se 1 (by rfl) ⟨2298266, by rfl⟩ : syracuseStep 3064355 = 4596533) B4596533
theorem B2042903 : Blo 2041435 2042903 := bstep (se 1 (by rfl) ⟨1532177, by rfl⟩ : syracuseStep 2042903 = 3064355) B3064355
theorem B2948437 : Blo 2041435 2948437 := bbase (se 11 (by rfl) ⟨2159, by rfl⟩ : syracuseStep 2948437 = 4319) (by norm_num)
theorem B3931249 : Blo 2041435 3931249 := bstep (se 2 (by rfl) ⟨1474218, by rfl⟩ : syracuseStep 3931249 = 2948437) B2948437
theorem B5241665 : Blo 2041435 5241665 := bstep (se 2 (by rfl) ⟨1965624, by rfl⟩ : syracuseStep 5241665 = 3931249) B3931249
theorem B3494443 : Blo 2041435 3494443 := bstep (se 1 (by rfl) ⟨2620832, by rfl⟩ : syracuseStep 3494443 = 5241665) B5241665
theorem B4659257 : Blo 2041435 4659257 := bstep (se 2 (by rfl) ⟨1747221, by rfl⟩ : syracuseStep 4659257 = 3494443) B3494443
theorem B3106171 : Blo 2041435 3106171 := bstep (se 1 (by rfl) ⟨2329628, by rfl⟩ : syracuseStep 3106171 = 4659257) B4659257
theorem B16566245 : Blo 2041435 16566245 := bstep (se 4 (by rfl) ⟨1553085, by rfl⟩ : syracuseStep 16566245 = 3106171) B3106171
theorem B11044163 : Blo 2041435 11044163 := bstep (se 1 (by rfl) ⟨8283122, by rfl⟩ : syracuseStep 11044163 = 16566245) B16566245
theorem B7362775 : Blo 2041435 7362775 := bstep (se 1 (by rfl) ⟨5522081, by rfl⟩ : syracuseStep 7362775 = 11044163) B11044163
theorem B9817033 : Blo 2041435 9817033 := bstep (se 2 (by rfl) ⟨3681387, by rfl⟩ : syracuseStep 9817033 = 7362775) B7362775
theorem B13089377 : Blo 2041435 13089377 := bstep (se 2 (by rfl) ⟨4908516, by rfl⟩ : syracuseStep 13089377 = 9817033) B9817033
theorem B8726251 : Blo 2041435 8726251 := bstep (se 1 (by rfl) ⟨6544688, by rfl⟩ : syracuseStep 8726251 = 13089377) B13089377
theorem B11635001 : Blo 2041435 11635001 := bstep (se 2 (by rfl) ⟨4363125, by rfl⟩ : syracuseStep 11635001 = 8726251) B8726251
theorem B7756667 : Blo 2041435 7756667 := bstep (se 1 (by rfl) ⟨5817500, by rfl⟩ : syracuseStep 7756667 = 11635001) B11635001
theorem B5171111 : Blo 2041435 5171111 := bstep (se 1 (by rfl) ⟨3878333, by rfl⟩ : syracuseStep 5171111 = 7756667) B7756667
theorem B3447407 : Blo 2041435 3447407 := bstep (se 1 (by rfl) ⟨2585555, by rfl⟩ : syracuseStep 3447407 = 5171111) B5171111
theorem B2298271 : Blo 2041435 2298271 := bstep (se 1 (by rfl) ⟨1723703, by rfl⟩ : syracuseStep 2298271 = 3447407) B3447407
theorem B3064361 : Blo 2041435 3064361 := bstep (se 2 (by rfl) ⟨1149135, by rfl⟩ : syracuseStep 3064361 = 2298271) B2298271
theorem B2042907 : Blo 2041435 2042907 := bstep (se 1 (by rfl) ⟨1532180, by rfl⟩ : syracuseStep 2042907 = 3064361) B3064361
theorem B2620837 : Blo 2041435 2620837 := bbase (se 4 (by rfl) ⟨245703, by rfl⟩ : syracuseStep 2620837 = 491407) (by norm_num)
theorem B3494449 : Blo 2041435 3494449 := bstep (se 2 (by rfl) ⟨1310418, by rfl⟩ : syracuseStep 3494449 = 2620837) B2620837
theorem B4659265 : Blo 2041435 4659265 := bstep (se 2 (by rfl) ⟨1747224, by rfl⟩ : syracuseStep 4659265 = 3494449) B3494449
theorem B24849413 : Blo 2041435 24849413 := bstep (se 4 (by rfl) ⟨2329632, by rfl⟩ : syracuseStep 24849413 = 4659265) B4659265
theorem B16566275 : Blo 2041435 16566275 := bstep (se 1 (by rfl) ⟨12424706, by rfl⟩ : syracuseStep 16566275 = 24849413) B24849413
theorem B11044183 : Blo 2041435 11044183 := bstep (se 1 (by rfl) ⟨8283137, by rfl⟩ : syracuseStep 11044183 = 16566275) B16566275
theorem B14725577 : Blo 2041435 14725577 := bstep (se 2 (by rfl) ⟨5522091, by rfl⟩ : syracuseStep 14725577 = 11044183) B11044183
theorem B9817051 : Blo 2041435 9817051 := bstep (se 1 (by rfl) ⟨7362788, by rfl⟩ : syracuseStep 9817051 = 14725577) B14725577
theorem B13089401 : Blo 2041435 13089401 := bstep (se 2 (by rfl) ⟨4908525, by rfl⟩ : syracuseStep 13089401 = 9817051) B9817051
theorem B8726267 : Blo 2041435 8726267 := bstep (se 1 (by rfl) ⟨6544700, by rfl⟩ : syracuseStep 8726267 = 13089401) B13089401
theorem B5817511 : Blo 2041435 5817511 := bstep (se 1 (by rfl) ⟨4363133, by rfl⟩ : syracuseStep 5817511 = 8726267) B8726267
theorem B7756681 : Blo 2041435 7756681 := bstep (se 2 (by rfl) ⟨2908755, by rfl⟩ : syracuseStep 7756681 = 5817511) B5817511
theorem B10342241 : Blo 2041435 10342241 := bstep (se 2 (by rfl) ⟨3878340, by rfl⟩ : syracuseStep 10342241 = 7756681) B7756681
theorem B6894827 : Blo 2041435 6894827 := bstep (se 1 (by rfl) ⟨5171120, by rfl⟩ : syracuseStep 6894827 = 10342241) B10342241
theorem B4596551 : Blo 2041435 4596551 := bstep (se 1 (by rfl) ⟨3447413, by rfl⟩ : syracuseStep 4596551 = 6894827) B6894827
theorem B3064367 : Blo 2041435 3064367 := bstep (se 1 (by rfl) ⟨2298275, by rfl⟩ : syracuseStep 3064367 = 4596551) B4596551
theorem B2042911 : Blo 2041435 2042911 := bstep (se 1 (by rfl) ⟨1532183, by rfl⟩ : syracuseStep 2042911 = 3064367) B3064367
theorem B3064373 : Blo 2041435 3064373 := bbase (se 5 (by rfl) ⟨143642, by rfl⟩ : syracuseStep 3064373 = 287285) (by norm_num)
theorem B2042915 : Blo 2041435 2042915 := bstep (se 1 (by rfl) ⟨1532186, by rfl⟩ : syracuseStep 2042915 = 3064373) B3064373
theorem B5171141 : Blo 2041435 5171141 := bbase (se 4 (by rfl) ⟨484794, by rfl⟩ : syracuseStep 5171141 = 969589) (by norm_num)
theorem B3447427 : Blo 2041435 3447427 := bstep (se 1 (by rfl) ⟨2585570, by rfl⟩ : syracuseStep 3447427 = 5171141) B5171141
theorem B4596569 : Blo 2041435 4596569 := bstep (se 2 (by rfl) ⟨1723713, by rfl⟩ : syracuseStep 4596569 = 3447427) B3447427
theorem B3064379 : Blo 2041435 3064379 := bstep (se 1 (by rfl) ⟨2298284, by rfl⟩ : syracuseStep 3064379 = 4596569) B4596569
theorem B2042919 : Blo 2041435 2042919 := bstep (se 1 (by rfl) ⟨1532189, by rfl⟩ : syracuseStep 2042919 = 3064379) B3064379
theorem B2298289 : Blo 2041435 2298289 := bbase (se 2 (by rfl) ⟨861858, by rfl⟩ : syracuseStep 2298289 = 1723717) (by norm_num)
theorem B3064385 : Blo 2041435 3064385 := bstep (se 2 (by rfl) ⟨1149144, by rfl⟩ : syracuseStep 3064385 = 2298289) B2298289
theorem B2042923 : Blo 2041435 2042923 := bstep (se 1 (by rfl) ⟨1532192, by rfl⟩ : syracuseStep 2042923 = 3064385) B3064385
theorem B5817557 : Blo 2041435 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B3878371 : Blo 2041435 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B5171161 : Blo 2041435 5171161 := bstep (se 2 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 5171161 = 3878371) B3878371
theorem B6894881 : Blo 2041435 6894881 := bstep (se 2 (by rfl) ⟨2585580, by rfl⟩ : syracuseStep 6894881 = 5171161) B5171161
theorem B4596587 : Blo 2041435 4596587 := bstep (se 1 (by rfl) ⟨3447440, by rfl⟩ : syracuseStep 4596587 = 6894881) B6894881
theorem B3064391 : Blo 2041435 3064391 := bstep (se 1 (by rfl) ⟨2298293, by rfl⟩ : syracuseStep 3064391 = 4596587) B4596587
theorem B2042927 : Blo 2041435 2042927 := bstep (se 1 (by rfl) ⟨1532195, by rfl⟩ : syracuseStep 2042927 = 3064391) B3064391
theorem B3064397 : Blo 2041435 3064397 := bbase (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) (by norm_num)
theorem B2042931 : Blo 2041435 2042931 := bstep (se 1 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 2042931 = 3064397) B3064397
theorem B4596605 : Blo 2041435 4596605 := bbase (se 3 (by rfl) ⟨861863, by rfl⟩ : syracuseStep 4596605 = 1723727) (by norm_num)
theorem B3064403 : Blo 2041435 3064403 := bstep (se 1 (by rfl) ⟨2298302, by rfl⟩ : syracuseStep 3064403 = 4596605) B4596605
theorem B2042935 : Blo 2041435 2042935 := bstep (se 1 (by rfl) ⟨1532201, by rfl⟩ : syracuseStep 2042935 = 3064403) B3064403
theorem B3447461 : Blo 2041435 3447461 := bbase (se 4 (by rfl) ⟨323199, by rfl⟩ : syracuseStep 3447461 = 646399) (by norm_num)
theorem B2298307 : Blo 2041435 2298307 := bstep (se 1 (by rfl) ⟨1723730, by rfl⟩ : syracuseStep 2298307 = 3447461) B3447461
theorem B3064409 : Blo 2041435 3064409 := bstep (se 2 (by rfl) ⟨1149153, by rfl⟩ : syracuseStep 3064409 = 2298307) B2298307
theorem B2042939 : Blo 2041435 2042939 := bstep (se 1 (by rfl) ⟨1532204, by rfl⟩ : syracuseStep 2042939 = 3064409) B3064409
theorem B2181601 : Blo 2041435 2181601 := bbase (se 2 (by rfl) ⟨818100, by rfl⟩ : syracuseStep 2181601 = 1636201) (by norm_num)
theorem B2908801 : Blo 2041435 2908801 := bstep (se 2 (by rfl) ⟨1090800, by rfl⟩ : syracuseStep 2908801 = 2181601) B2181601
theorem B15513605 : Blo 2041435 15513605 := bstep (se 4 (by rfl) ⟨1454400, by rfl⟩ : syracuseStep 15513605 = 2908801) B2908801
theorem B10342403 : Blo 2041435 10342403 := bstep (se 1 (by rfl) ⟨7756802, by rfl⟩ : syracuseStep 10342403 = 15513605) B15513605
theorem B6894935 : Blo 2041435 6894935 := bstep (se 1 (by rfl) ⟨5171201, by rfl⟩ : syracuseStep 6894935 = 10342403) B10342403
theorem B4596623 : Blo 2041435 4596623 := bstep (se 1 (by rfl) ⟨3447467, by rfl⟩ : syracuseStep 4596623 = 6894935) B6894935
theorem B3064415 : Blo 2041435 3064415 := bstep (se 1 (by rfl) ⟨2298311, by rfl⟩ : syracuseStep 3064415 = 4596623) B4596623
theorem B2042943 : Blo 2041435 2042943 := bstep (se 1 (by rfl) ⟨1532207, by rfl⟩ : syracuseStep 2042943 = 3064415) B3064415
theorem B3064421 : Blo 2041435 3064421 := bbase (se 4 (by rfl) ⟨287289, by rfl⟩ : syracuseStep 3064421 = 574579) (by norm_num)
theorem B2042947 : Blo 2041435 2042947 := bstep (se 1 (by rfl) ⟨1532210, by rfl⟩ : syracuseStep 2042947 = 3064421) B3064421
theorem B2908813 : Blo 2041435 2908813 := bbase (se 3 (by rfl) ⟨545402, by rfl⟩ : syracuseStep 2908813 = 1090805) (by norm_num)
theorem B3878417 : Blo 2041435 3878417 := bstep (se 2 (by rfl) ⟨1454406, by rfl⟩ : syracuseStep 3878417 = 2908813) B2908813
theorem B2585611 : Blo 2041435 2585611 := bstep (se 1 (by rfl) ⟨1939208, by rfl⟩ : syracuseStep 2585611 = 3878417) B3878417
theorem B3447481 : Blo 2041435 3447481 := bstep (se 2 (by rfl) ⟨1292805, by rfl⟩ : syracuseStep 3447481 = 2585611) B2585611
theorem B4596641 : Blo 2041435 4596641 := bstep (se 2 (by rfl) ⟨1723740, by rfl⟩ : syracuseStep 4596641 = 3447481) B3447481
theorem B3064427 : Blo 2041435 3064427 := bstep (se 1 (by rfl) ⟨2298320, by rfl⟩ : syracuseStep 3064427 = 4596641) B4596641
theorem B2042951 : Blo 2041435 2042951 := bstep (se 1 (by rfl) ⟨1532213, by rfl⟩ : syracuseStep 2042951 = 3064427) B3064427
theorem B2298325 : Blo 2041435 2298325 := bbase (se 7 (by rfl) ⟨26933, by rfl⟩ : syracuseStep 2298325 = 53867) (by norm_num)
theorem B3064433 : Blo 2041435 3064433 := bstep (se 2 (by rfl) ⟨1149162, by rfl⟩ : syracuseStep 3064433 = 2298325) B2298325
theorem B2042955 : Blo 2041435 2042955 := bstep (se 1 (by rfl) ⟨1532216, by rfl⟩ : syracuseStep 2042955 = 3064433) B3064433
theorem B2585621 : Blo 2041435 2585621 := bbase (se 6 (by rfl) ⟨60600, by rfl⟩ : syracuseStep 2585621 = 121201) (by norm_num)
theorem B6894989 : Blo 2041435 6894989 := bstep (se 3 (by rfl) ⟨1292810, by rfl⟩ : syracuseStep 6894989 = 2585621) B2585621
theorem B4596659 : Blo 2041435 4596659 := bstep (se 1 (by rfl) ⟨3447494, by rfl⟩ : syracuseStep 4596659 = 6894989) B6894989
theorem B3064439 : Blo 2041435 3064439 := bstep (se 1 (by rfl) ⟨2298329, by rfl⟩ : syracuseStep 3064439 = 4596659) B4596659
theorem B2042959 : Blo 2041435 2042959 := bstep (se 1 (by rfl) ⟨1532219, by rfl⟩ : syracuseStep 2042959 = 3064439) B3064439
theorem B3064445 : Blo 2041435 3064445 := bbase (se 3 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 3064445 = 1149167) (by norm_num)
theorem B2042963 : Blo 2041435 2042963 := bstep (se 1 (by rfl) ⟨1532222, by rfl⟩ : syracuseStep 2042963 = 3064445) B3064445
theorem B4596677 : Blo 2041435 4596677 := bbase (se 4 (by rfl) ⟨430938, by rfl⟩ : syracuseStep 4596677 = 861877) (by norm_num)
theorem B3064451 : Blo 2041435 3064451 := bstep (se 1 (by rfl) ⟨2298338, by rfl⟩ : syracuseStep 3064451 = 4596677) B4596677
theorem B2042967 : Blo 2041435 2042967 := bstep (se 1 (by rfl) ⟨1532225, by rfl⟩ : syracuseStep 2042967 = 3064451) B3064451
theorem B18891893 : Blo 2041435 18891893 := bbase (se 5 (by rfl) ⟨885557, by rfl⟩ : syracuseStep 18891893 = 1771115) (by norm_num)
theorem B50378381 : Blo 2041435 50378381 := bstep (se 3 (by rfl) ⟨9445946, by rfl⟩ : syracuseStep 50378381 = 18891893) B18891893
theorem B33585587 : Blo 2041435 33585587 := bstep (se 1 (by rfl) ⟨25189190, by rfl⟩ : syracuseStep 33585587 = 50378381) B50378381
theorem B22390391 : Blo 2041435 22390391 := bstep (se 1 (by rfl) ⟨16792793, by rfl⟩ : syracuseStep 22390391 = 33585587) B33585587
theorem B59707709 : Blo 2041435 59707709 := bstep (se 3 (by rfl) ⟨11195195, by rfl⟩ : syracuseStep 59707709 = 22390391) B22390391
theorem B39805139 : Blo 2041435 39805139 := bstep (se 1 (by rfl) ⟨29853854, by rfl⟩ : syracuseStep 39805139 = 59707709) B59707709
theorem B106147037 : Blo 2041435 106147037 := bstep (se 3 (by rfl) ⟨19902569, by rfl⟩ : syracuseStep 106147037 = 39805139) B39805139
theorem B70764691 : Blo 2041435 70764691 := bstep (se 1 (by rfl) ⟨53073518, by rfl⟩ : syracuseStep 70764691 = 106147037) B106147037
theorem B94352921 : Blo 2041435 94352921 := bstep (se 2 (by rfl) ⟨35382345, by rfl⟩ : syracuseStep 94352921 = 70764691) B70764691
theorem B62901947 : Blo 2041435 62901947 := bstep (se 1 (by rfl) ⟨47176460, by rfl⟩ : syracuseStep 62901947 = 94352921) B94352921
theorem B41934631 : Blo 2041435 41934631 := bstep (se 1 (by rfl) ⟨31450973, by rfl⟩ : syracuseStep 41934631 = 62901947) B62901947
theorem B55912841 : Blo 2041435 55912841 := bstep (se 2 (by rfl) ⟨20967315, by rfl⟩ : syracuseStep 55912841 = 41934631) B41934631
theorem B37275227 : Blo 2041435 37275227 := bstep (se 1 (by rfl) ⟨27956420, by rfl⟩ : syracuseStep 37275227 = 55912841) B55912841
theorem B24850151 : Blo 2041435 24850151 := bstep (se 1 (by rfl) ⟨18637613, by rfl⟩ : syracuseStep 24850151 = 37275227) B37275227
theorem B16566767 : Blo 2041435 16566767 := bstep (se 1 (by rfl) ⟨12425075, by rfl⟩ : syracuseStep 16566767 = 24850151) B24850151
theorem B11044511 : Blo 2041435 11044511 := bstep (se 1 (by rfl) ⟨8283383, by rfl⟩ : syracuseStep 11044511 = 16566767) B16566767
theorem B7363007 : Blo 2041435 7363007 := bstep (se 1 (by rfl) ⟨5522255, by rfl⟩ : syracuseStep 7363007 = 11044511) B11044511
theorem B4908671 : Blo 2041435 4908671 := bstep (se 1 (by rfl) ⟨3681503, by rfl⟩ : syracuseStep 4908671 = 7363007) B7363007
theorem B3272447 : Blo 2041435 3272447 := bstep (se 1 (by rfl) ⟨2454335, by rfl⟩ : syracuseStep 3272447 = 4908671) B4908671
theorem B8726525 : Blo 2041435 8726525 := bstep (se 3 (by rfl) ⟨1636223, by rfl⟩ : syracuseStep 8726525 = 3272447) B3272447
theorem B5817683 : Blo 2041435 5817683 := bstep (se 1 (by rfl) ⟨4363262, by rfl⟩ : syracuseStep 5817683 = 8726525) B8726525
theorem B3878455 : Blo 2041435 3878455 := bstep (se 1 (by rfl) ⟨2908841, by rfl⟩ : syracuseStep 3878455 = 5817683) B5817683
theorem B5171273 : Blo 2041435 5171273 := bstep (se 2 (by rfl) ⟨1939227, by rfl⟩ : syracuseStep 5171273 = 3878455) B3878455
theorem B3447515 : Blo 2041435 3447515 := bstep (se 1 (by rfl) ⟨2585636, by rfl⟩ : syracuseStep 3447515 = 5171273) B5171273
theorem B2298343 : Blo 2041435 2298343 := bstep (se 1 (by rfl) ⟨1723757, by rfl⟩ : syracuseStep 2298343 = 3447515) B3447515
theorem B3064457 : Blo 2041435 3064457 := bstep (se 2 (by rfl) ⟨1149171, by rfl⟩ : syracuseStep 3064457 = 2298343) B2298343
theorem B2042971 : Blo 2041435 2042971 := bstep (se 1 (by rfl) ⟨1532228, by rfl⟩ : syracuseStep 2042971 = 3064457) B3064457
theorem B10342565 : Blo 2041435 10342565 := bbase (se 4 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 10342565 = 1939231) (by norm_num)
theorem B6895043 : Blo 2041435 6895043 := bstep (se 1 (by rfl) ⟨5171282, by rfl⟩ : syracuseStep 6895043 = 10342565) B10342565
theorem B4596695 : Blo 2041435 4596695 := bstep (se 1 (by rfl) ⟨3447521, by rfl⟩ : syracuseStep 4596695 = 6895043) B6895043
theorem B3064463 : Blo 2041435 3064463 := bstep (se 1 (by rfl) ⟨2298347, by rfl⟩ : syracuseStep 3064463 = 4596695) B4596695
theorem B2042975 : Blo 2041435 2042975 := bstep (se 1 (by rfl) ⟨1532231, by rfl⟩ : syracuseStep 2042975 = 3064463) B3064463
theorem B3064469 : Blo 2041435 3064469 := bbase (se 6 (by rfl) ⟨71823, by rfl⟩ : syracuseStep 3064469 = 143647) (by norm_num)
theorem B2042979 : Blo 2041435 2042979 := bstep (se 1 (by rfl) ⟨1532234, by rfl⟩ : syracuseStep 2042979 = 3064469) B3064469
theorem B18637717 : Blo 2041435 18637717 := bbase (se 6 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 18637717 = 873643) (by norm_num)
theorem B24850289 : Blo 2041435 24850289 := bstep (se 2 (by rfl) ⟨9318858, by rfl⟩ : syracuseStep 24850289 = 18637717) B18637717
theorem B16566859 : Blo 2041435 16566859 := bstep (se 1 (by rfl) ⟨12425144, by rfl⟩ : syracuseStep 16566859 = 24850289) B24850289
theorem B22089145 : Blo 2041435 22089145 := bstep (se 2 (by rfl) ⟨8283429, by rfl⟩ : syracuseStep 22089145 = 16566859) B16566859
theorem B29452193 : Blo 2041435 29452193 := bstep (se 2 (by rfl) ⟨11044572, by rfl⟩ : syracuseStep 29452193 = 22089145) B22089145
theorem B19634795 : Blo 2041435 19634795 := bstep (se 1 (by rfl) ⟨14726096, by rfl⟩ : syracuseStep 19634795 = 29452193) B29452193
theorem B13089863 : Blo 2041435 13089863 := bstep (se 1 (by rfl) ⟨9817397, by rfl⟩ : syracuseStep 13089863 = 19634795) B19634795
theorem B8726575 : Blo 2041435 8726575 := bstep (se 1 (by rfl) ⟨6544931, by rfl⟩ : syracuseStep 8726575 = 13089863) B13089863
theorem B11635433 : Blo 2041435 11635433 := bstep (se 2 (by rfl) ⟨4363287, by rfl⟩ : syracuseStep 11635433 = 8726575) B8726575
theorem B7756955 : Blo 2041435 7756955 := bstep (se 1 (by rfl) ⟨5817716, by rfl⟩ : syracuseStep 7756955 = 11635433) B11635433
theorem B5171303 : Blo 2041435 5171303 := bstep (se 1 (by rfl) ⟨3878477, by rfl⟩ : syracuseStep 5171303 = 7756955) B7756955
theorem B3447535 : Blo 2041435 3447535 := bstep (se 1 (by rfl) ⟨2585651, by rfl⟩ : syracuseStep 3447535 = 5171303) B5171303
theorem B4596713 : Blo 2041435 4596713 := bstep (se 2 (by rfl) ⟨1723767, by rfl⟩ : syracuseStep 4596713 = 3447535) B3447535
theorem B3064475 : Blo 2041435 3064475 := bstep (se 1 (by rfl) ⟨2298356, by rfl⟩ : syracuseStep 3064475 = 4596713) B4596713
theorem B2042983 : Blo 2041435 2042983 := bstep (se 1 (by rfl) ⟨1532237, by rfl⟩ : syracuseStep 2042983 = 3064475) B3064475
theorem B2298361 : Blo 2041435 2298361 := bbase (se 2 (by rfl) ⟨861885, by rfl⟩ : syracuseStep 2298361 = 1723771) (by norm_num)
theorem B3064481 : Blo 2041435 3064481 := bstep (se 2 (by rfl) ⟨1149180, by rfl⟩ : syracuseStep 3064481 = 2298361) B2298361
theorem B2042987 : Blo 2041435 2042987 := bstep (se 1 (by rfl) ⟨1532240, by rfl⟩ : syracuseStep 2042987 = 3064481) B3064481
theorem B5522309 : Blo 2041435 5522309 := bbase (se 4 (by rfl) ⟨517716, by rfl⟩ : syracuseStep 5522309 = 1035433) (by norm_num)
theorem B3681539 : Blo 2041435 3681539 := bstep (se 1 (by rfl) ⟨2761154, by rfl⟩ : syracuseStep 3681539 = 5522309) B5522309
theorem B2454359 : Blo 2041435 2454359 := bstep (se 1 (by rfl) ⟨1840769, by rfl⟩ : syracuseStep 2454359 = 3681539) B3681539
theorem B6544957 : Blo 2041435 6544957 := bstep (se 3 (by rfl) ⟨1227179, by rfl⟩ : syracuseStep 6544957 = 2454359) B2454359
theorem B8726609 : Blo 2041435 8726609 := bstep (se 2 (by rfl) ⟨3272478, by rfl⟩ : syracuseStep 8726609 = 6544957) B6544957
theorem B5817739 : Blo 2041435 5817739 := bstep (se 1 (by rfl) ⟨4363304, by rfl⟩ : syracuseStep 5817739 = 8726609) B8726609
theorem B7756985 : Blo 2041435 7756985 := bstep (se 2 (by rfl) ⟨2908869, by rfl⟩ : syracuseStep 7756985 = 5817739) B5817739
theorem B5171323 : Blo 2041435 5171323 := bstep (se 1 (by rfl) ⟨3878492, by rfl⟩ : syracuseStep 5171323 = 7756985) B7756985
theorem B6895097 : Blo 2041435 6895097 := bstep (se 2 (by rfl) ⟨2585661, by rfl⟩ : syracuseStep 6895097 = 5171323) B5171323
theorem B4596731 : Blo 2041435 4596731 := bstep (se 1 (by rfl) ⟨3447548, by rfl⟩ : syracuseStep 4596731 = 6895097) B6895097
theorem B3064487 : Blo 2041435 3064487 := bstep (se 1 (by rfl) ⟨2298365, by rfl⟩ : syracuseStep 3064487 = 4596731) B4596731
theorem B2042991 : Blo 2041435 2042991 := bstep (se 1 (by rfl) ⟨1532243, by rfl⟩ : syracuseStep 2042991 = 3064487) B3064487
theorem B3064493 : Blo 2041435 3064493 := bbase (se 3 (by rfl) ⟨574592, by rfl⟩ : syracuseStep 3064493 = 1149185) (by norm_num)
theorem B2042995 : Blo 2041435 2042995 := bstep (se 1 (by rfl) ⟨1532246, by rfl⟩ : syracuseStep 2042995 = 3064493) B3064493
theorem B4596749 : Blo 2041435 4596749 := bbase (se 3 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 4596749 = 1723781) (by norm_num)
theorem B3064499 : Blo 2041435 3064499 := bstep (se 1 (by rfl) ⟨2298374, by rfl⟩ : syracuseStep 3064499 = 4596749) B4596749
theorem B2042999 : Blo 2041435 2042999 := bstep (se 1 (by rfl) ⟨1532249, by rfl⟩ : syracuseStep 2042999 = 3064499) B3064499
theorem B2585677 : Blo 2041435 2585677 := bbase (se 3 (by rfl) ⟨484814, by rfl⟩ : syracuseStep 2585677 = 969629) (by norm_num)
theorem B3447569 : Blo 2041435 3447569 := bstep (se 2 (by rfl) ⟨1292838, by rfl⟩ : syracuseStep 3447569 = 2585677) B2585677
theorem B2298379 : Blo 2041435 2298379 := bstep (se 1 (by rfl) ⟨1723784, by rfl⟩ : syracuseStep 2298379 = 3447569) B3447569
theorem B3064505 : Blo 2041435 3064505 := bstep (se 2 (by rfl) ⟨1149189, by rfl⟩ : syracuseStep 3064505 = 2298379) B2298379
theorem B2043003 : Blo 2041435 2043003 := bstep (se 1 (by rfl) ⟨1532252, by rfl⟩ : syracuseStep 2043003 = 3064505) B3064505
theorem B2766949 : Blo 2041435 2766949 := bbase (se 4 (by rfl) ⟨259401, by rfl⟩ : syracuseStep 2766949 = 518803) (by norm_num)
theorem B14757061 : Blo 2041435 14757061 := bstep (se 4 (by rfl) ⟨1383474, by rfl⟩ : syracuseStep 14757061 = 2766949) B2766949
theorem B19676081 : Blo 2041435 19676081 := bstep (se 2 (by rfl) ⟨7378530, by rfl⟩ : syracuseStep 19676081 = 14757061) B14757061
theorem B13117387 : Blo 2041435 13117387 := bstep (se 1 (by rfl) ⟨9838040, by rfl⟩ : syracuseStep 13117387 = 19676081) B19676081
theorem B17489849 : Blo 2041435 17489849 := bstep (se 2 (by rfl) ⟨6558693, by rfl⟩ : syracuseStep 17489849 = 13117387) B13117387
theorem B46639597 : Blo 2041435 46639597 := bstep (se 3 (by rfl) ⟨8744924, by rfl⟩ : syracuseStep 46639597 = 17489849) B17489849
theorem B62186129 : Blo 2041435 62186129 := bstep (se 2 (by rfl) ⟨23319798, by rfl⟩ : syracuseStep 62186129 = 46639597) B46639597
theorem B41457419 : Blo 2041435 41457419 := bstep (se 1 (by rfl) ⟨31093064, by rfl⟩ : syracuseStep 41457419 = 62186129) B62186129
theorem B27638279 : Blo 2041435 27638279 := bstep (se 1 (by rfl) ⟨20728709, by rfl⟩ : syracuseStep 27638279 = 41457419) B41457419
theorem B18425519 : Blo 2041435 18425519 := bstep (se 1 (by rfl) ⟨13819139, by rfl⟩ : syracuseStep 18425519 = 27638279) B27638279
theorem B12283679 : Blo 2041435 12283679 := bstep (se 1 (by rfl) ⟨9212759, by rfl⟩ : syracuseStep 12283679 = 18425519) B18425519
theorem B8189119 : Blo 2041435 8189119 := bstep (se 1 (by rfl) ⟨6141839, by rfl⟩ : syracuseStep 8189119 = 12283679) B12283679
theorem B43675301 : Blo 2041435 43675301 := bstep (se 4 (by rfl) ⟨4094559, by rfl⟩ : syracuseStep 43675301 = 8189119) B8189119
theorem B116467469 : Blo 2041435 116467469 := bstep (se 3 (by rfl) ⟨21837650, by rfl⟩ : syracuseStep 116467469 = 43675301) B43675301
theorem B77644979 : Blo 2041435 77644979 := bstep (se 1 (by rfl) ⟨58233734, by rfl⟩ : syracuseStep 77644979 = 116467469) B116467469
theorem B51763319 : Blo 2041435 51763319 := bstep (se 1 (by rfl) ⟨38822489, by rfl⟩ : syracuseStep 51763319 = 77644979) B77644979
theorem B34508879 : Blo 2041435 34508879 := bstep (se 1 (by rfl) ⟨25881659, by rfl⟩ : syracuseStep 34508879 = 51763319) B51763319
theorem B23005919 : Blo 2041435 23005919 := bstep (se 1 (by rfl) ⟨17254439, by rfl⟩ : syracuseStep 23005919 = 34508879) B34508879
theorem B61349117 : Blo 2041435 61349117 := bstep (se 3 (by rfl) ⟨11502959, by rfl⟩ : syracuseStep 61349117 = 23005919) B23005919
theorem B163597645 : Blo 2041435 163597645 := bstep (se 3 (by rfl) ⟨30674558, by rfl⟩ : syracuseStep 163597645 = 61349117) B61349117
theorem B218130193 : Blo 2041435 218130193 := bstep (se 2 (by rfl) ⟨81798822, by rfl⟩ : syracuseStep 218130193 = 163597645) B163597645
theorem B290840257 : Blo 2041435 290840257 := bstep (se 2 (by rfl) ⟨109065096, by rfl⟩ : syracuseStep 290840257 = 218130193) B218130193
theorem B387787009 : Blo 2041435 387787009 := bstep (se 2 (by rfl) ⟨145420128, by rfl⟩ : syracuseStep 387787009 = 290840257) B290840257
theorem B517049345 : Blo 2041435 517049345 := bstep (se 2 (by rfl) ⟨193893504, by rfl⟩ : syracuseStep 517049345 = 387787009) B387787009
theorem B344699563 : Blo 2041435 344699563 := bstep (se 1 (by rfl) ⟨258524672, by rfl⟩ : syracuseStep 344699563 = 517049345) B517049345
theorem B459599417 : Blo 2041435 459599417 := bstep (se 2 (by rfl) ⟨172349781, by rfl⟩ : syracuseStep 459599417 = 344699563) B344699563
theorem B306399611 : Blo 2041435 306399611 := bstep (se 1 (by rfl) ⟨229799708, by rfl⟩ : syracuseStep 306399611 = 459599417) B459599417
theorem B817065629 : Blo 2041435 817065629 := bstep (se 3 (by rfl) ⟨153199805, by rfl⟩ : syracuseStep 817065629 = 306399611) B306399611
theorem B544710419 : Blo 2041435 544710419 := bstep (se 1 (by rfl) ⟨408532814, by rfl⟩ : syracuseStep 544710419 = 817065629) B817065629
theorem B363140279 : Blo 2041435 363140279 := bstep (se 1 (by rfl) ⟨272355209, by rfl⟩ : syracuseStep 363140279 = 544710419) B544710419
theorem B242093519 : Blo 2041435 242093519 := bstep (se 1 (by rfl) ⟨181570139, by rfl⟩ : syracuseStep 242093519 = 363140279) B363140279
theorem B161395679 : Blo 2041435 161395679 := bstep (se 1 (by rfl) ⟨121046759, by rfl⟩ : syracuseStep 161395679 = 242093519) B242093519
theorem B107597119 : Blo 2041435 107597119 := bstep (se 1 (by rfl) ⟨80697839, by rfl⟩ : syracuseStep 107597119 = 161395679) B161395679
theorem B143462825 : Blo 2041435 143462825 := bstep (se 2 (by rfl) ⟨53798559, by rfl⟩ : syracuseStep 143462825 = 107597119) B107597119
theorem B95641883 : Blo 2041435 95641883 := bstep (se 1 (by rfl) ⟨71731412, by rfl⟩ : syracuseStep 95641883 = 143462825) B143462825
theorem B63761255 : Blo 2041435 63761255 := bstep (se 1 (by rfl) ⟨47820941, by rfl⟩ : syracuseStep 63761255 = 95641883) B95641883
theorem B42507503 : Blo 2041435 42507503 := bstep (se 1 (by rfl) ⟨31880627, by rfl⟩ : syracuseStep 42507503 = 63761255) B63761255
theorem B28338335 : Blo 2041435 28338335 := bstep (se 1 (by rfl) ⟨21253751, by rfl⟩ : syracuseStep 28338335 = 42507503) B42507503
theorem B18892223 : Blo 2041435 18892223 := bstep (se 1 (by rfl) ⟨14169167, by rfl⟩ : syracuseStep 18892223 = 28338335) B28338335
theorem B12594815 : Blo 2041435 12594815 := bstep (se 1 (by rfl) ⟨9446111, by rfl⟩ : syracuseStep 12594815 = 18892223) B18892223
theorem B8396543 : Blo 2041435 8396543 := bstep (se 1 (by rfl) ⟨6297407, by rfl⟩ : syracuseStep 8396543 = 12594815) B12594815
theorem B5597695 : Blo 2041435 5597695 := bstep (se 1 (by rfl) ⟨4198271, by rfl⟩ : syracuseStep 5597695 = 8396543) B8396543
theorem B7463593 : Blo 2041435 7463593 := bstep (se 2 (by rfl) ⟨2798847, by rfl⟩ : syracuseStep 7463593 = 5597695) B5597695
theorem B39805829 : Blo 2041435 39805829 := bstep (se 4 (by rfl) ⟨3731796, by rfl⟩ : syracuseStep 39805829 = 7463593) B7463593
theorem B26537219 : Blo 2041435 26537219 := bstep (se 1 (by rfl) ⟨19902914, by rfl⟩ : syracuseStep 26537219 = 39805829) B39805829
theorem B17691479 : Blo 2041435 17691479 := bstep (se 1 (by rfl) ⟨13268609, by rfl⟩ : syracuseStep 17691479 = 26537219) B26537219
theorem B11794319 : Blo 2041435 11794319 := bstep (se 1 (by rfl) ⟨8845739, by rfl⟩ : syracuseStep 11794319 = 17691479) B17691479
theorem B7862879 : Blo 2041435 7862879 := bstep (se 1 (by rfl) ⟨5897159, by rfl⟩ : syracuseStep 7862879 = 11794319) B11794319
theorem B5241919 : Blo 2041435 5241919 := bstep (se 1 (by rfl) ⟨3931439, by rfl⟩ : syracuseStep 5241919 = 7862879) B7862879
theorem B6989225 : Blo 2041435 6989225 := bstep (se 2 (by rfl) ⟨2620959, by rfl⟩ : syracuseStep 6989225 = 5241919) B5241919
theorem B18637933 : Blo 2041435 18637933 := bstep (se 3 (by rfl) ⟨3494612, by rfl⟩ : syracuseStep 18637933 = 6989225) B6989225
theorem B24850577 : Blo 2041435 24850577 := bstep (se 2 (by rfl) ⟨9318966, by rfl⟩ : syracuseStep 24850577 = 18637933) B18637933
theorem B66268205 : Blo 2041435 66268205 := bstep (se 3 (by rfl) ⟨12425288, by rfl⟩ : syracuseStep 66268205 = 24850577) B24850577
theorem B44178803 : Blo 2041435 44178803 := bstep (se 1 (by rfl) ⟨33134102, by rfl⟩ : syracuseStep 44178803 = 66268205) B66268205
theorem B29452535 : Blo 2041435 29452535 := bstep (se 1 (by rfl) ⟨22089401, by rfl⟩ : syracuseStep 29452535 = 44178803) B44178803
theorem B19635023 : Blo 2041435 19635023 := bstep (se 1 (by rfl) ⟨14726267, by rfl⟩ : syracuseStep 19635023 = 29452535) B29452535
theorem B13090015 : Blo 2041435 13090015 := bstep (se 1 (by rfl) ⟨9817511, by rfl⟩ : syracuseStep 13090015 = 19635023) B19635023
theorem B17453353 : Blo 2041435 17453353 := bstep (se 2 (by rfl) ⟨6545007, by rfl⟩ : syracuseStep 17453353 = 13090015) B13090015
theorem B23271137 : Blo 2041435 23271137 := bstep (se 2 (by rfl) ⟨8726676, by rfl⟩ : syracuseStep 23271137 = 17453353) B17453353
theorem B15514091 : Blo 2041435 15514091 := bstep (se 1 (by rfl) ⟨11635568, by rfl⟩ : syracuseStep 15514091 = 23271137) B23271137
theorem B10342727 : Blo 2041435 10342727 := bstep (se 1 (by rfl) ⟨7757045, by rfl⟩ : syracuseStep 10342727 = 15514091) B15514091
theorem B6895151 : Blo 2041435 6895151 := bstep (se 1 (by rfl) ⟨5171363, by rfl⟩ : syracuseStep 6895151 = 10342727) B10342727
theorem B4596767 : Blo 2041435 4596767 := bstep (se 1 (by rfl) ⟨3447575, by rfl⟩ : syracuseStep 4596767 = 6895151) B6895151
theorem B3064511 : Blo 2041435 3064511 := bstep (se 1 (by rfl) ⟨2298383, by rfl⟩ : syracuseStep 3064511 = 4596767) B4596767
theorem B2043007 : Blo 2041435 2043007 := bstep (se 1 (by rfl) ⟨1532255, by rfl⟩ : syracuseStep 2043007 = 3064511) B3064511
theorem B3064517 : Blo 2041435 3064517 := bbase (se 4 (by rfl) ⟨287298, by rfl⟩ : syracuseStep 3064517 = 574597) (by norm_num)
theorem B2043011 : Blo 2041435 2043011 := bstep (se 1 (by rfl) ⟨1532258, by rfl⟩ : syracuseStep 2043011 = 3064517) B3064517
theorem B3447589 : Blo 2041435 3447589 := bbase (se 4 (by rfl) ⟨323211, by rfl⟩ : syracuseStep 3447589 = 646423) (by norm_num)
theorem B4596785 : Blo 2041435 4596785 := bstep (se 2 (by rfl) ⟨1723794, by rfl⟩ : syracuseStep 4596785 = 3447589) B3447589
theorem B3064523 : Blo 2041435 3064523 := bstep (se 1 (by rfl) ⟨2298392, by rfl⟩ : syracuseStep 3064523 = 4596785) B4596785
theorem B2043015 : Blo 2041435 2043015 := bstep (se 1 (by rfl) ⟨1532261, by rfl⟩ : syracuseStep 2043015 = 3064523) B3064523
theorem B2298397 : Blo 2041435 2298397 := bbase (se 3 (by rfl) ⟨430949, by rfl⟩ : syracuseStep 2298397 = 861899) (by norm_num)
theorem B3064529 : Blo 2041435 3064529 := bstep (se 2 (by rfl) ⟨1149198, by rfl⟩ : syracuseStep 3064529 = 2298397) B2298397
theorem B2043019 : Blo 2041435 2043019 := bstep (se 1 (by rfl) ⟨1532264, by rfl⟩ : syracuseStep 2043019 = 3064529) B3064529
theorem B6895205 : Blo 2041435 6895205 := bbase (se 4 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 6895205 = 1292851) (by norm_num)
theorem B4596803 : Blo 2041435 4596803 := bstep (se 1 (by rfl) ⟨3447602, by rfl⟩ : syracuseStep 4596803 = 6895205) B6895205
theorem B3064535 : Blo 2041435 3064535 := bstep (se 1 (by rfl) ⟨2298401, by rfl⟩ : syracuseStep 3064535 = 4596803) B4596803
theorem B2043023 : Blo 2041435 2043023 := bstep (se 1 (by rfl) ⟨1532267, by rfl⟩ : syracuseStep 2043023 = 3064535) B3064535
theorem B3064541 : Blo 2041435 3064541 := bbase (se 3 (by rfl) ⟨574601, by rfl⟩ : syracuseStep 3064541 = 1149203) (by norm_num)
theorem B2043027 : Blo 2041435 2043027 := bstep (se 1 (by rfl) ⟨1532270, by rfl⟩ : syracuseStep 2043027 = 3064541) B3064541
theorem B4596821 : Blo 2041435 4596821 := bbase (se 8 (by rfl) ⟨26934, by rfl⟩ : syracuseStep 4596821 = 53869) (by norm_num)
theorem B3064547 : Blo 2041435 3064547 := bstep (se 1 (by rfl) ⟨2298410, by rfl⟩ : syracuseStep 3064547 = 4596821) B4596821
theorem B2043031 : Blo 2041435 2043031 := bstep (se 1 (by rfl) ⟨1532273, by rfl⟩ : syracuseStep 2043031 = 3064547) B3064547
theorem B7363237 : Blo 2041435 7363237 := bbase (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) (by norm_num)
theorem B9817649 : Blo 2041435 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B6545099 : Blo 2041435 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B4363399 : Blo 2041435 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B5817865 : Blo 2041435 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B7757153 : Blo 2041435 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B5171435 : Blo 2041435 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B3447623 : Blo 2041435 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B2298415 : Blo 2041435 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B3064553 : Blo 2041435 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B2043035 : Blo 2041435 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B5522437 : Blo 2041435 5522437 := bbase (se 4 (by rfl) ⟨517728, by rfl⟩ : syracuseStep 5522437 = 1035457) (by norm_num)
theorem B29452997 : Blo 2041435 29452997 := bstep (se 4 (by rfl) ⟨2761218, by rfl⟩ : syracuseStep 29452997 = 5522437) B5522437
theorem B19635331 : Blo 2041435 19635331 := bstep (se 1 (by rfl) ⟨14726498, by rfl⟩ : syracuseStep 19635331 = 29452997) B29452997
theorem B26180441 : Blo 2041435 26180441 := bstep (se 2 (by rfl) ⟨9817665, by rfl⟩ : syracuseStep 26180441 = 19635331) B19635331
theorem B17453627 : Blo 2041435 17453627 := bstep (se 1 (by rfl) ⟨13090220, by rfl⟩ : syracuseStep 17453627 = 26180441) B26180441
theorem B11635751 : Blo 2041435 11635751 := bstep (se 1 (by rfl) ⟨8726813, by rfl⟩ : syracuseStep 11635751 = 17453627) B17453627
theorem B7757167 : Blo 2041435 7757167 := bstep (se 1 (by rfl) ⟨5817875, by rfl⟩ : syracuseStep 7757167 = 11635751) B11635751
theorem B10342889 : Blo 2041435 10342889 := bstep (se 2 (by rfl) ⟨3878583, by rfl⟩ : syracuseStep 10342889 = 7757167) B7757167
theorem B6895259 : Blo 2041435 6895259 := bstep (se 1 (by rfl) ⟨5171444, by rfl⟩ : syracuseStep 6895259 = 10342889) B10342889
theorem B4596839 : Blo 2041435 4596839 := bstep (se 1 (by rfl) ⟨3447629, by rfl⟩ : syracuseStep 4596839 = 6895259) B6895259
theorem B3064559 : Blo 2041435 3064559 := bstep (se 1 (by rfl) ⟨2298419, by rfl⟩ : syracuseStep 3064559 = 4596839) B4596839
theorem B2043039 : Blo 2041435 2043039 := bstep (se 1 (by rfl) ⟨1532279, by rfl⟩ : syracuseStep 2043039 = 3064559) B3064559
theorem B3064565 : Blo 2041435 3064565 := bbase (se 5 (by rfl) ⟨143651, by rfl⟩ : syracuseStep 3064565 = 287303) (by norm_num)
theorem B2043043 : Blo 2041435 2043043 := bstep (se 1 (by rfl) ⟨1532282, by rfl⟩ : syracuseStep 2043043 = 3064565) B3064565
theorem B4908853 : Blo 2041435 4908853 := bbase (se 5 (by rfl) ⟨230102, by rfl⟩ : syracuseStep 4908853 = 460205) (by norm_num)
theorem B6545137 : Blo 2041435 6545137 := bstep (se 2 (by rfl) ⟨2454426, by rfl⟩ : syracuseStep 6545137 = 4908853) B4908853
theorem B8726849 : Blo 2041435 8726849 := bstep (se 2 (by rfl) ⟨3272568, by rfl⟩ : syracuseStep 8726849 = 6545137) B6545137
theorem B5817899 : Blo 2041435 5817899 := bstep (se 1 (by rfl) ⟨4363424, by rfl⟩ : syracuseStep 5817899 = 8726849) B8726849
theorem B3878599 : Blo 2041435 3878599 := bstep (se 1 (by rfl) ⟨2908949, by rfl⟩ : syracuseStep 3878599 = 5817899) B5817899
theorem B5171465 : Blo 2041435 5171465 := bstep (se 2 (by rfl) ⟨1939299, by rfl⟩ : syracuseStep 5171465 = 3878599) B3878599
theorem B3447643 : Blo 2041435 3447643 := bstep (se 1 (by rfl) ⟨2585732, by rfl⟩ : syracuseStep 3447643 = 5171465) B5171465
theorem B4596857 : Blo 2041435 4596857 := bstep (se 2 (by rfl) ⟨1723821, by rfl⟩ : syracuseStep 4596857 = 3447643) B3447643
theorem B3064571 : Blo 2041435 3064571 := bstep (se 1 (by rfl) ⟨2298428, by rfl⟩ : syracuseStep 3064571 = 4596857) B4596857
theorem B2043047 : Blo 2041435 2043047 := bstep (se 1 (by rfl) ⟨1532285, by rfl⟩ : syracuseStep 2043047 = 3064571) B3064571
theorem B2298433 : Blo 2041435 2298433 := bbase (se 2 (by rfl) ⟨861912, by rfl⟩ : syracuseStep 2298433 = 1723825) (by norm_num)
theorem B3064577 : Blo 2041435 3064577 := bstep (se 2 (by rfl) ⟨1149216, by rfl⟩ : syracuseStep 3064577 = 2298433) B2298433
theorem B2043051 : Blo 2041435 2043051 := bstep (se 1 (by rfl) ⟨1532288, by rfl⟩ : syracuseStep 2043051 = 3064577) B3064577
theorem B5171485 : Blo 2041435 5171485 := bbase (se 3 (by rfl) ⟨969653, by rfl⟩ : syracuseStep 5171485 = 1939307) (by norm_num)
theorem B6895313 : Blo 2041435 6895313 := bstep (se 2 (by rfl) ⟨2585742, by rfl⟩ : syracuseStep 6895313 = 5171485) B5171485
theorem B4596875 : Blo 2041435 4596875 := bstep (se 1 (by rfl) ⟨3447656, by rfl⟩ : syracuseStep 4596875 = 6895313) B6895313
theorem B3064583 : Blo 2041435 3064583 := bstep (se 1 (by rfl) ⟨2298437, by rfl⟩ : syracuseStep 3064583 = 4596875) B4596875
theorem B2043055 : Blo 2041435 2043055 := bstep (se 1 (by rfl) ⟨1532291, by rfl⟩ : syracuseStep 2043055 = 3064583) B3064583
theorem B3064589 : Blo 2041435 3064589 := bbase (se 3 (by rfl) ⟨574610, by rfl⟩ : syracuseStep 3064589 = 1149221) (by norm_num)
theorem B2043059 : Blo 2041435 2043059 := bstep (se 1 (by rfl) ⟨1532294, by rfl⟩ : syracuseStep 2043059 = 3064589) B3064589
theorem B4596893 : Blo 2041435 4596893 := bbase (se 3 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 4596893 = 1723835) (by norm_num)
theorem B3064595 : Blo 2041435 3064595 := bstep (se 1 (by rfl) ⟨2298446, by rfl⟩ : syracuseStep 3064595 = 4596893) B4596893
theorem B2043063 : Blo 2041435 2043063 := bstep (se 1 (by rfl) ⟨1532297, by rfl⟩ : syracuseStep 2043063 = 3064595) B3064595
theorem B3447677 : Blo 2041435 3447677 := bbase (se 3 (by rfl) ⟨646439, by rfl⟩ : syracuseStep 3447677 = 1292879) (by norm_num)
theorem B2298451 : Blo 2041435 2298451 := bstep (se 1 (by rfl) ⟨1723838, by rfl⟩ : syracuseStep 2298451 = 3447677) B3447677
theorem B3064601 : Blo 2041435 3064601 := bstep (se 2 (by rfl) ⟨1149225, by rfl⟩ : syracuseStep 3064601 = 2298451) B2298451
theorem B2043067 : Blo 2041435 2043067 := bstep (se 1 (by rfl) ⟨1532300, by rfl⟩ : syracuseStep 2043067 = 3064601) B3064601
theorem B3106421 : Blo 2041435 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2070947 : Blo 2041435 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B5522525 : Blo 2041435 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B3681683 : Blo 2041435 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B2454455 : Blo 2041435 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B6545213 : Blo 2041435 6545213 := bstep (se 3 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 6545213 = 2454455) B2454455
theorem B4363475 : Blo 2041435 4363475 := bstep (se 1 (by rfl) ⟨3272606, by rfl⟩ : syracuseStep 4363475 = 6545213) B6545213
theorem B11635933 : Blo 2041435 11635933 := bstep (se 3 (by rfl) ⟨2181737, by rfl⟩ : syracuseStep 11635933 = 4363475) B4363475
theorem B15514577 : Blo 2041435 15514577 := bstep (se 2 (by rfl) ⟨5817966, by rfl⟩ : syracuseStep 15514577 = 11635933) B11635933
theorem B10343051 : Blo 2041435 10343051 := bstep (se 1 (by rfl) ⟨7757288, by rfl⟩ : syracuseStep 10343051 = 15514577) B15514577
theorem B6895367 : Blo 2041435 6895367 := bstep (se 1 (by rfl) ⟨5171525, by rfl⟩ : syracuseStep 6895367 = 10343051) B10343051
theorem B4596911 : Blo 2041435 4596911 := bstep (se 1 (by rfl) ⟨3447683, by rfl⟩ : syracuseStep 4596911 = 6895367) B6895367
theorem B3064607 : Blo 2041435 3064607 := bstep (se 1 (by rfl) ⟨2298455, by rfl⟩ : syracuseStep 3064607 = 4596911) B4596911
theorem B2043071 : Blo 2041435 2043071 := bstep (se 1 (by rfl) ⟨1532303, by rfl⟩ : syracuseStep 2043071 = 3064607) B3064607
theorem B3064613 : Blo 2041435 3064613 := bbase (se 4 (by rfl) ⟨287307, by rfl⟩ : syracuseStep 3064613 = 574615) (by norm_num)
theorem B2043075 : Blo 2041435 2043075 := bstep (se 1 (by rfl) ⟨1532306, by rfl⟩ : syracuseStep 2043075 = 3064613) B3064613
theorem B2585773 : Blo 2041435 2585773 := bbase (se 3 (by rfl) ⟨484832, by rfl⟩ : syracuseStep 2585773 = 969665) (by norm_num)
theorem B3447697 : Blo 2041435 3447697 := bstep (se 2 (by rfl) ⟨1292886, by rfl⟩ : syracuseStep 3447697 = 2585773) B2585773
theorem B4596929 : Blo 2041435 4596929 := bstep (se 2 (by rfl) ⟨1723848, by rfl⟩ : syracuseStep 4596929 = 3447697) B3447697
theorem B3064619 : Blo 2041435 3064619 := bstep (se 1 (by rfl) ⟨2298464, by rfl⟩ : syracuseStep 3064619 = 4596929) B4596929
theorem B2043079 : Blo 2041435 2043079 := bstep (se 1 (by rfl) ⟨1532309, by rfl⟩ : syracuseStep 2043079 = 3064619) B3064619
theorem B2298469 : Blo 2041435 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B3064625 : Blo 2041435 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B2043083 : Blo 2041435 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B2761285 : Blo 2041435 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B3681713 : Blo 2041435 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B2454475 : Blo 2041435 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B3272633 : Blo 2041435 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B2181755 : Blo 2041435 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B5818013 : Blo 2041435 5818013 := bstep (se 3 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 5818013 = 2181755) B2181755
theorem B3878675 : Blo 2041435 3878675 := bstep (se 1 (by rfl) ⟨2909006, by rfl⟩ : syracuseStep 3878675 = 5818013) B5818013
theorem B2585783 : Blo 2041435 2585783 := bstep (se 1 (by rfl) ⟨1939337, by rfl⟩ : syracuseStep 2585783 = 3878675) B3878675
theorem B6895421 : Blo 2041435 6895421 := bstep (se 3 (by rfl) ⟨1292891, by rfl⟩ : syracuseStep 6895421 = 2585783) B2585783
theorem B4596947 : Blo 2041435 4596947 := bstep (se 1 (by rfl) ⟨3447710, by rfl⟩ : syracuseStep 4596947 = 6895421) B6895421
theorem B3064631 : Blo 2041435 3064631 := bstep (se 1 (by rfl) ⟨2298473, by rfl⟩ : syracuseStep 3064631 = 4596947) B4596947
theorem B2043087 : Blo 2041435 2043087 := bstep (se 1 (by rfl) ⟨1532315, by rfl⟩ : syracuseStep 2043087 = 3064631) B3064631
theorem B3064637 : Blo 2041435 3064637 := bbase (se 3 (by rfl) ⟨574619, by rfl⟩ : syracuseStep 3064637 = 1149239) (by norm_num)
theorem B2043091 : Blo 2041435 2043091 := bstep (se 1 (by rfl) ⟨1532318, by rfl⟩ : syracuseStep 2043091 = 3064637) B3064637
theorem B4596965 : Blo 2041435 4596965 := bbase (se 4 (by rfl) ⟨430965, by rfl⟩ : syracuseStep 4596965 = 861931) (by norm_num)
theorem B3064643 : Blo 2041435 3064643 := bstep (se 1 (by rfl) ⟨2298482, by rfl⟩ : syracuseStep 3064643 = 4596965) B4596965
theorem B2043095 : Blo 2041435 2043095 := bstep (se 1 (by rfl) ⟨1532321, by rfl⟩ : syracuseStep 2043095 = 3064643) B3064643
theorem B5171597 : Blo 2041435 5171597 := bbase (se 3 (by rfl) ⟨969674, by rfl⟩ : syracuseStep 5171597 = 1939349) (by norm_num)
theorem B3447731 : Blo 2041435 3447731 := bstep (se 1 (by rfl) ⟨2585798, by rfl⟩ : syracuseStep 3447731 = 5171597) B5171597
theorem B2298487 : Blo 2041435 2298487 := bstep (se 1 (by rfl) ⟨1723865, by rfl⟩ : syracuseStep 2298487 = 3447731) B3447731
theorem B3064649 : Blo 2041435 3064649 := bstep (se 2 (by rfl) ⟨1149243, by rfl⟩ : syracuseStep 3064649 = 2298487) B2298487
theorem B2043099 : Blo 2041435 2043099 := bstep (se 1 (by rfl) ⟨1532324, by rfl⟩ : syracuseStep 2043099 = 3064649) B3064649
theorem B2909029 : Blo 2041435 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B3878705 : Blo 2041435 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B10343213 : Blo 2041435 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B6895475 : Blo 2041435 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B4596983 : Blo 2041435 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B3064655 : Blo 2041435 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B2043103 : Blo 2041435 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B3064661 : Blo 2041435 3064661 := bbase (se 9 (by rfl) ⟨8978, by rfl⟩ : syracuseStep 3064661 = 17957) (by norm_num)
theorem B2043107 : Blo 2041435 2043107 := bstep (se 1 (by rfl) ⟨1532330, by rfl⟩ : syracuseStep 2043107 = 3064661) B3064661
theorem B9319445 : Blo 2041435 9319445 := bbase (se 6 (by rfl) ⟨218424, by rfl⟩ : syracuseStep 9319445 = 436849) (by norm_num)
theorem B6212963 : Blo 2041435 6212963 := bstep (se 1 (by rfl) ⟨4659722, by rfl⟩ : syracuseStep 6212963 = 9319445) B9319445
theorem B16567901 : Blo 2041435 16567901 := bstep (se 3 (by rfl) ⟨3106481, by rfl⟩ : syracuseStep 16567901 = 6212963) B6212963
theorem B11045267 : Blo 2041435 11045267 := bstep (se 1 (by rfl) ⟨8283950, by rfl⟩ : syracuseStep 11045267 = 16567901) B16567901
theorem B7363511 : Blo 2041435 7363511 := bstep (se 1 (by rfl) ⟨5522633, by rfl⟩ : syracuseStep 7363511 = 11045267) B11045267
theorem B4909007 : Blo 2041435 4909007 := bstep (se 1 (by rfl) ⟨3681755, by rfl⟩ : syracuseStep 4909007 = 7363511) B7363511
theorem B3272671 : Blo 2041435 3272671 := bstep (se 1 (by rfl) ⟨2454503, by rfl⟩ : syracuseStep 3272671 = 4909007) B4909007
theorem B4363561 : Blo 2041435 4363561 := bstep (se 2 (by rfl) ⟨1636335, by rfl⟩ : syracuseStep 4363561 = 3272671) B3272671
theorem B5818081 : Blo 2041435 5818081 := bstep (se 2 (by rfl) ⟨2181780, by rfl⟩ : syracuseStep 5818081 = 4363561) B4363561
theorem B7757441 : Blo 2041435 7757441 := bstep (se 2 (by rfl) ⟨2909040, by rfl⟩ : syracuseStep 7757441 = 5818081) B5818081
theorem B5171627 : Blo 2041435 5171627 := bstep (se 1 (by rfl) ⟨3878720, by rfl⟩ : syracuseStep 5171627 = 7757441) B7757441
theorem B3447751 : Blo 2041435 3447751 := bstep (se 1 (by rfl) ⟨2585813, by rfl⟩ : syracuseStep 3447751 = 5171627) B5171627
theorem B4597001 : Blo 2041435 4597001 := bstep (se 2 (by rfl) ⟨1723875, by rfl⟩ : syracuseStep 4597001 = 3447751) B3447751
theorem B3064667 : Blo 2041435 3064667 := bstep (se 1 (by rfl) ⟨2298500, by rfl⟩ : syracuseStep 3064667 = 4597001) B4597001
theorem B2043111 : Blo 2041435 2043111 := bstep (se 1 (by rfl) ⟨1532333, by rfl⟩ : syracuseStep 2043111 = 3064667) B3064667
theorem B2298505 : Blo 2041435 2298505 := bbase (se 2 (by rfl) ⟨861939, by rfl⟩ : syracuseStep 2298505 = 1723879) (by norm_num)
theorem B3064673 : Blo 2041435 3064673 := bstep (se 2 (by rfl) ⟨1149252, by rfl⟩ : syracuseStep 3064673 = 2298505) B2298505
theorem B2043115 : Blo 2041435 2043115 := bstep (se 1 (by rfl) ⟨1532336, by rfl⟩ : syracuseStep 2043115 = 3064673) B3064673
theorem B14169941 : Blo 2041435 14169941 := bbase (se 9 (by rfl) ⟨41513, by rfl⟩ : syracuseStep 14169941 = 83027) (by norm_num)
theorem B9446627 : Blo 2041435 9446627 := bstep (se 1 (by rfl) ⟨7084970, by rfl⟩ : syracuseStep 9446627 = 14169941) B14169941
theorem B25191005 : Blo 2041435 25191005 := bstep (se 3 (by rfl) ⟨4723313, by rfl⟩ : syracuseStep 25191005 = 9446627) B9446627
theorem B67176013 : Blo 2041435 67176013 := bstep (se 3 (by rfl) ⟨12595502, by rfl⟩ : syracuseStep 67176013 = 25191005) B25191005
theorem B89568017 : Blo 2041435 89568017 := bstep (se 2 (by rfl) ⟨33588006, by rfl⟩ : syracuseStep 89568017 = 67176013) B67176013
theorem B59712011 : Blo 2041435 59712011 := bstep (se 1 (by rfl) ⟨44784008, by rfl⟩ : syracuseStep 59712011 = 89568017) B89568017
theorem B39808007 : Blo 2041435 39808007 := bstep (se 1 (by rfl) ⟨29856005, by rfl⟩ : syracuseStep 39808007 = 59712011) B59712011
theorem B26538671 : Blo 2041435 26538671 := bstep (se 1 (by rfl) ⟨19904003, by rfl⟩ : syracuseStep 26538671 = 39808007) B39808007
theorem B17692447 : Blo 2041435 17692447 := bstep (se 1 (by rfl) ⟨13269335, by rfl⟩ : syracuseStep 17692447 = 26538671) B26538671
theorem B23589929 : Blo 2041435 23589929 := bstep (se 2 (by rfl) ⟨8846223, by rfl⟩ : syracuseStep 23589929 = 17692447) B17692447
theorem B15726619 : Blo 2041435 15726619 := bstep (se 1 (by rfl) ⟨11794964, by rfl⟩ : syracuseStep 15726619 = 23589929) B23589929
theorem B83875301 : Blo 2041435 83875301 := bstep (se 4 (by rfl) ⟨7863309, by rfl⟩ : syracuseStep 83875301 = 15726619) B15726619
theorem B55916867 : Blo 2041435 55916867 := bstep (se 1 (by rfl) ⟨41937650, by rfl⟩ : syracuseStep 55916867 = 83875301) B83875301
theorem B37277911 : Blo 2041435 37277911 := bstep (se 1 (by rfl) ⟨27958433, by rfl⟩ : syracuseStep 37277911 = 55916867) B55916867
theorem B49703881 : Blo 2041435 49703881 := bstep (se 2 (by rfl) ⟨18638955, by rfl⟩ : syracuseStep 49703881 = 37277911) B37277911
theorem B66271841 : Blo 2041435 66271841 := bstep (se 2 (by rfl) ⟨24851940, by rfl⟩ : syracuseStep 66271841 = 49703881) B49703881
theorem B44181227 : Blo 2041435 44181227 := bstep (se 1 (by rfl) ⟨33135920, by rfl⟩ : syracuseStep 44181227 = 66271841) B66271841
theorem B29454151 : Blo 2041435 29454151 := bstep (se 1 (by rfl) ⟨22090613, by rfl⟩ : syracuseStep 29454151 = 44181227) B44181227
theorem B39272201 : Blo 2041435 39272201 := bstep (se 2 (by rfl) ⟨14727075, by rfl⟩ : syracuseStep 39272201 = 29454151) B29454151
theorem B26181467 : Blo 2041435 26181467 := bstep (se 1 (by rfl) ⟨19636100, by rfl⟩ : syracuseStep 26181467 = 39272201) B39272201
theorem B17454311 : Blo 2041435 17454311 := bstep (se 1 (by rfl) ⟨13090733, by rfl⟩ : syracuseStep 17454311 = 26181467) B26181467
theorem B11636207 : Blo 2041435 11636207 := bstep (se 1 (by rfl) ⟨8727155, by rfl⟩ : syracuseStep 11636207 = 17454311) B17454311
theorem B7757471 : Blo 2041435 7757471 := bstep (se 1 (by rfl) ⟨5818103, by rfl⟩ : syracuseStep 7757471 = 11636207) B11636207
theorem B5171647 : Blo 2041435 5171647 := bstep (se 1 (by rfl) ⟨3878735, by rfl⟩ : syracuseStep 5171647 = 7757471) B7757471
theorem B6895529 : Blo 2041435 6895529 := bstep (se 2 (by rfl) ⟨2585823, by rfl⟩ : syracuseStep 6895529 = 5171647) B5171647
theorem B4597019 : Blo 2041435 4597019 := bstep (se 1 (by rfl) ⟨3447764, by rfl⟩ : syracuseStep 4597019 = 6895529) B6895529
theorem B3064679 : Blo 2041435 3064679 := bstep (se 1 (by rfl) ⟨2298509, by rfl⟩ : syracuseStep 3064679 = 4597019) B4597019
theorem B2043119 : Blo 2041435 2043119 := bstep (se 1 (by rfl) ⟨1532339, by rfl⟩ : syracuseStep 2043119 = 3064679) B3064679
theorem B3064685 : Blo 2041435 3064685 := bbase (se 3 (by rfl) ⟨574628, by rfl⟩ : syracuseStep 3064685 = 1149257) (by norm_num)
theorem B2043123 : Blo 2041435 2043123 := bstep (se 1 (by rfl) ⟨1532342, by rfl⟩ : syracuseStep 2043123 = 3064685) B3064685
theorem B4597037 : Blo 2041435 4597037 := bbase (se 3 (by rfl) ⟨861944, by rfl⟩ : syracuseStep 4597037 = 1723889) (by norm_num)
theorem B3064691 : Blo 2041435 3064691 := bstep (se 1 (by rfl) ⟨2298518, by rfl⟩ : syracuseStep 3064691 = 4597037) B4597037
theorem B2043127 : Blo 2041435 2043127 := bstep (se 1 (by rfl) ⟨1532345, by rfl⟩ : syracuseStep 2043127 = 3064691) B3064691
theorem B6383717 : Blo 2041435 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B4255811 : Blo 2041435 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B2837207 : Blo 2041435 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B7565885 : Blo 2041435 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B5043923 : Blo 2041435 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B3362615 : Blo 2041435 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B2241743 : Blo 2041435 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B5977981 : Blo 2041435 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B31882565 : Blo 2041435 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B21255043 : Blo 2041435 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B28340057 : Blo 2041435 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B18893371 : Blo 2041435 18893371 := bstep (se 1 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 18893371 = 28340057) B28340057
theorem B25191161 : Blo 2041435 25191161 := bstep (se 2 (by rfl) ⟨9446685, by rfl⟩ : syracuseStep 25191161 = 18893371) B18893371
theorem B16794107 : Blo 2041435 16794107 := bstep (se 1 (by rfl) ⟨12595580, by rfl⟩ : syracuseStep 16794107 = 25191161) B25191161
theorem B11196071 : Blo 2041435 11196071 := bstep (se 1 (by rfl) ⟨8397053, by rfl⟩ : syracuseStep 11196071 = 16794107) B16794107
theorem B477699029 : Blo 2041435 477699029 := bstep (se 7 (by rfl) ⟨5598035, by rfl⟩ : syracuseStep 477699029 = 11196071) B11196071
theorem B318466019 : Blo 2041435 318466019 := bstep (se 1 (by rfl) ⟨238849514, by rfl⟩ : syracuseStep 318466019 = 477699029) B477699029
theorem B849242717 : Blo 2041435 849242717 := bstep (se 3 (by rfl) ⟨159233009, by rfl⟩ : syracuseStep 849242717 = 318466019) B318466019
theorem B566161811 : Blo 2041435 566161811 := bstep (se 1 (by rfl) ⟨424621358, by rfl⟩ : syracuseStep 566161811 = 849242717) B849242717
theorem B377441207 : Blo 2041435 377441207 := bstep (se 1 (by rfl) ⟨283080905, by rfl⟩ : syracuseStep 377441207 = 566161811) B566161811
theorem B251627471 : Blo 2041435 251627471 := bstep (se 1 (by rfl) ⟨188720603, by rfl⟩ : syracuseStep 251627471 = 377441207) B377441207
theorem B167751647 : Blo 2041435 167751647 := bstep (se 1 (by rfl) ⟨125813735, by rfl⟩ : syracuseStep 167751647 = 251627471) B251627471
theorem B111834431 : Blo 2041435 111834431 := bstep (se 1 (by rfl) ⟨83875823, by rfl⟩ : syracuseStep 111834431 = 167751647) B167751647
theorem B74556287 : Blo 2041435 74556287 := bstep (se 1 (by rfl) ⟨55917215, by rfl⟩ : syracuseStep 74556287 = 111834431) B111834431
theorem B49704191 : Blo 2041435 49704191 := bstep (se 1 (by rfl) ⟨37278143, by rfl⟩ : syracuseStep 49704191 = 74556287) B74556287
theorem B33136127 : Blo 2041435 33136127 := bstep (se 1 (by rfl) ⟨24852095, by rfl⟩ : syracuseStep 33136127 = 49704191) B49704191
theorem B22090751 : Blo 2041435 22090751 := bstep (se 1 (by rfl) ⟨16568063, by rfl⟩ : syracuseStep 22090751 = 33136127) B33136127
theorem B14727167 : Blo 2041435 14727167 := bstep (se 1 (by rfl) ⟨11045375, by rfl⟩ : syracuseStep 14727167 = 22090751) B22090751
theorem B9818111 : Blo 2041435 9818111 := bstep (se 1 (by rfl) ⟨7363583, by rfl⟩ : syracuseStep 9818111 = 14727167) B14727167
theorem B6545407 : Blo 2041435 6545407 := bstep (se 1 (by rfl) ⟨4909055, by rfl⟩ : syracuseStep 6545407 = 9818111) B9818111
theorem B8727209 : Blo 2041435 8727209 := bstep (se 2 (by rfl) ⟨3272703, by rfl⟩ : syracuseStep 8727209 = 6545407) B6545407
theorem B5818139 : Blo 2041435 5818139 := bstep (se 1 (by rfl) ⟨4363604, by rfl⟩ : syracuseStep 5818139 = 8727209) B8727209
theorem B3878759 : Blo 2041435 3878759 := bstep (se 1 (by rfl) ⟨2909069, by rfl⟩ : syracuseStep 3878759 = 5818139) B5818139
theorem B2585839 : Blo 2041435 2585839 := bstep (se 1 (by rfl) ⟨1939379, by rfl⟩ : syracuseStep 2585839 = 3878759) B3878759
theorem B3447785 : Blo 2041435 3447785 := bstep (se 2 (by rfl) ⟨1292919, by rfl⟩ : syracuseStep 3447785 = 2585839) B2585839
theorem B2298523 : Blo 2041435 2298523 := bstep (se 1 (by rfl) ⟨1723892, by rfl⟩ : syracuseStep 2298523 = 3447785) B3447785
theorem B3064697 : Blo 2041435 3064697 := bstep (se 2 (by rfl) ⟨1149261, by rfl⟩ : syracuseStep 3064697 = 2298523) B2298523
theorem B2043131 : Blo 2041435 2043131 := bstep (se 1 (by rfl) ⟨1532348, by rfl⟩ : syracuseStep 2043131 = 3064697) B3064697
theorem B3106517 : Blo 2041435 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B8284045 : Blo 2041435 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B11045393 : Blo 2041435 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B7363595 : Blo 2041435 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B19636253 : Blo 2041435 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B13090835 : Blo 2041435 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B34908893 : Blo 2041435 34908893 := bstep (se 3 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 34908893 = 13090835) B13090835
theorem B23272595 : Blo 2041435 23272595 := bstep (se 1 (by rfl) ⟨17454446, by rfl⟩ : syracuseStep 23272595 = 34908893) B34908893
theorem B15515063 : Blo 2041435 15515063 := bstep (se 1 (by rfl) ⟨11636297, by rfl⟩ : syracuseStep 15515063 = 23272595) B23272595
theorem B10343375 : Blo 2041435 10343375 := bstep (se 1 (by rfl) ⟨7757531, by rfl⟩ : syracuseStep 10343375 = 15515063) B15515063
theorem B6895583 : Blo 2041435 6895583 := bstep (se 1 (by rfl) ⟨5171687, by rfl⟩ : syracuseStep 6895583 = 10343375) B10343375
theorem B4597055 : Blo 2041435 4597055 := bstep (se 1 (by rfl) ⟨3447791, by rfl⟩ : syracuseStep 4597055 = 6895583) B6895583
theorem B3064703 : Blo 2041435 3064703 := bstep (se 1 (by rfl) ⟨2298527, by rfl⟩ : syracuseStep 3064703 = 4597055) B4597055
theorem B2043135 : Blo 2041435 2043135 := bstep (se 1 (by rfl) ⟨1532351, by rfl⟩ : syracuseStep 2043135 = 3064703) B3064703
theorem B3064709 : Blo 2041435 3064709 := bbase (se 4 (by rfl) ⟨287316, by rfl⟩ : syracuseStep 3064709 = 574633) (by norm_num)
theorem B2043139 : Blo 2041435 2043139 := bstep (se 1 (by rfl) ⟨1532354, by rfl⟩ : syracuseStep 2043139 = 3064709) B3064709
theorem B3447805 : Blo 2041435 3447805 := bbase (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) (by norm_num)
theorem B4597073 : Blo 2041435 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B3064715 : Blo 2041435 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B2043143 : Blo 2041435 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B2298541 : Blo 2041435 2298541 := bbase (se 3 (by rfl) ⟨430976, by rfl⟩ : syracuseStep 2298541 = 861953) (by norm_num)
theorem B3064721 : Blo 2041435 3064721 := bstep (se 2 (by rfl) ⟨1149270, by rfl⟩ : syracuseStep 3064721 = 2298541) B2298541
theorem B2043147 : Blo 2041435 2043147 := bstep (se 1 (by rfl) ⟨1532360, by rfl⟩ : syracuseStep 2043147 = 3064721) B3064721
theorem B6895637 : Blo 2041435 6895637 := bbase (se 6 (by rfl) ⟨161616, by rfl⟩ : syracuseStep 6895637 = 323233) (by norm_num)
theorem B4597091 : Blo 2041435 4597091 := bstep (se 1 (by rfl) ⟨3447818, by rfl⟩ : syracuseStep 4597091 = 6895637) B6895637
theorem B3064727 : Blo 2041435 3064727 := bstep (se 1 (by rfl) ⟨2298545, by rfl⟩ : syracuseStep 3064727 = 4597091) B4597091
theorem B2043151 : Blo 2041435 2043151 := bstep (se 1 (by rfl) ⟨1532363, by rfl⟩ : syracuseStep 2043151 = 3064727) B3064727
theorem B3064733 : Blo 2041435 3064733 := bbase (se 3 (by rfl) ⟨574637, by rfl⟩ : syracuseStep 3064733 = 1149275) (by norm_num)
theorem B2043155 : Blo 2041435 2043155 := bstep (se 1 (by rfl) ⟨1532366, by rfl⟩ : syracuseStep 2043155 = 3064733) B3064733
theorem B4597109 : Blo 2041435 4597109 := bbase (se 5 (by rfl) ⟨215489, by rfl⟩ : syracuseStep 4597109 = 430979) (by norm_num)
theorem B3064739 : Blo 2041435 3064739 := bstep (se 1 (by rfl) ⟨2298554, by rfl⟩ : syracuseStep 3064739 = 4597109) B4597109
theorem B2043159 : Blo 2041435 2043159 := bstep (se 1 (by rfl) ⟨1532369, by rfl⟩ : syracuseStep 2043159 = 3064739) B3064739
theorem B22091093 : Blo 2041435 22091093 := bbase (se 14 (by rfl) ⟨2022, by rfl⟩ : syracuseStep 22091093 = 4045) (by norm_num)
theorem B14727395 : Blo 2041435 14727395 := bstep (se 1 (by rfl) ⟨11045546, by rfl⟩ : syracuseStep 14727395 = 22091093) B22091093
theorem B9818263 : Blo 2041435 9818263 := bstep (se 1 (by rfl) ⟨7363697, by rfl⟩ : syracuseStep 9818263 = 14727395) B14727395
theorem B13091017 : Blo 2041435 13091017 := bstep (se 2 (by rfl) ⟨4909131, by rfl⟩ : syracuseStep 13091017 = 9818263) B9818263
theorem B17454689 : Blo 2041435 17454689 := bstep (se 2 (by rfl) ⟨6545508, by rfl⟩ : syracuseStep 17454689 = 13091017) B13091017
theorem B11636459 : Blo 2041435 11636459 := bstep (se 1 (by rfl) ⟨8727344, by rfl⟩ : syracuseStep 11636459 = 17454689) B17454689
theorem B7757639 : Blo 2041435 7757639 := bstep (se 1 (by rfl) ⟨5818229, by rfl⟩ : syracuseStep 7757639 = 11636459) B11636459
theorem B5171759 : Blo 2041435 5171759 := bstep (se 1 (by rfl) ⟨3878819, by rfl⟩ : syracuseStep 5171759 = 7757639) B7757639
theorem B3447839 : Blo 2041435 3447839 := bstep (se 1 (by rfl) ⟨2585879, by rfl⟩ : syracuseStep 3447839 = 5171759) B5171759
theorem B2298559 : Blo 2041435 2298559 := bstep (se 1 (by rfl) ⟨1723919, by rfl⟩ : syracuseStep 2298559 = 3447839) B3447839
theorem B3064745 : Blo 2041435 3064745 := bstep (se 2 (by rfl) ⟨1149279, by rfl⟩ : syracuseStep 3064745 = 2298559) B2298559
theorem B2043163 : Blo 2041435 2043163 := bstep (se 1 (by rfl) ⟨1532372, by rfl⟩ : syracuseStep 2043163 = 3064745) B3064745
theorem B7757653 : Blo 2041435 7757653 := bbase (se 9 (by rfl) ⟨22727, by rfl⟩ : syracuseStep 7757653 = 45455) (by norm_num)
theorem B10343537 : Blo 2041435 10343537 := bstep (se 2 (by rfl) ⟨3878826, by rfl⟩ : syracuseStep 10343537 = 7757653) B7757653
theorem B6895691 : Blo 2041435 6895691 := bstep (se 1 (by rfl) ⟨5171768, by rfl⟩ : syracuseStep 6895691 = 10343537) B10343537
theorem B4597127 : Blo 2041435 4597127 := bstep (se 1 (by rfl) ⟨3447845, by rfl⟩ : syracuseStep 4597127 = 6895691) B6895691
theorem B3064751 : Blo 2041435 3064751 := bstep (se 1 (by rfl) ⟨2298563, by rfl⟩ : syracuseStep 3064751 = 4597127) B4597127
theorem B2043167 : Blo 2041435 2043167 := bstep (se 1 (by rfl) ⟨1532375, by rfl⟩ : syracuseStep 2043167 = 3064751) B3064751
theorem B3064757 : Blo 2041435 3064757 := bbase (se 5 (by rfl) ⟨143660, by rfl⟩ : syracuseStep 3064757 = 287321) (by norm_num)
theorem B2043171 : Blo 2041435 2043171 := bstep (se 1 (by rfl) ⟨1532378, by rfl⟩ : syracuseStep 2043171 = 3064757) B3064757
theorem B5171789 : Blo 2041435 5171789 := bbase (se 3 (by rfl) ⟨969710, by rfl⟩ : syracuseStep 5171789 = 1939421) (by norm_num)
theorem B3447859 : Blo 2041435 3447859 := bstep (se 1 (by rfl) ⟨2585894, by rfl⟩ : syracuseStep 3447859 = 5171789) B5171789
theorem B4597145 : Blo 2041435 4597145 := bstep (se 2 (by rfl) ⟨1723929, by rfl⟩ : syracuseStep 4597145 = 3447859) B3447859
theorem B3064763 : Blo 2041435 3064763 := bstep (se 1 (by rfl) ⟨2298572, by rfl⟩ : syracuseStep 3064763 = 4597145) B4597145
theorem B2043175 : Blo 2041435 2043175 := bstep (se 1 (by rfl) ⟨1532381, by rfl⟩ : syracuseStep 2043175 = 3064763) B3064763
theorem B2298577 : Blo 2041435 2298577 := bbase (se 2 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 2298577 = 1723933) (by norm_num)
theorem B3064769 : Blo 2041435 3064769 := bstep (se 2 (by rfl) ⟨1149288, by rfl⟩ : syracuseStep 3064769 = 2298577) B2298577
theorem B2043179 : Blo 2041435 2043179 := bstep (se 1 (by rfl) ⟨1532384, by rfl⟩ : syracuseStep 2043179 = 3064769) B3064769
theorem B6545573 : Blo 2041435 6545573 := bbase (se 4 (by rfl) ⟨613647, by rfl⟩ : syracuseStep 6545573 = 1227295) (by norm_num)
theorem B4363715 : Blo 2041435 4363715 := bstep (se 1 (by rfl) ⟨3272786, by rfl⟩ : syracuseStep 4363715 = 6545573) B6545573
theorem B2909143 : Blo 2041435 2909143 := bstep (se 1 (by rfl) ⟨2181857, by rfl⟩ : syracuseStep 2909143 = 4363715) B4363715
theorem B3878857 : Blo 2041435 3878857 := bstep (se 2 (by rfl) ⟨1454571, by rfl⟩ : syracuseStep 3878857 = 2909143) B2909143
theorem B5171809 : Blo 2041435 5171809 := bstep (se 2 (by rfl) ⟨1939428, by rfl⟩ : syracuseStep 5171809 = 3878857) B3878857
theorem B6895745 : Blo 2041435 6895745 := bstep (se 2 (by rfl) ⟨2585904, by rfl⟩ : syracuseStep 6895745 = 5171809) B5171809
theorem B4597163 : Blo 2041435 4597163 := bstep (se 1 (by rfl) ⟨3447872, by rfl⟩ : syracuseStep 4597163 = 6895745) B6895745
theorem B3064775 : Blo 2041435 3064775 := bstep (se 1 (by rfl) ⟨2298581, by rfl⟩ : syracuseStep 3064775 = 4597163) B4597163
theorem B2043183 : Blo 2041435 2043183 := bstep (se 1 (by rfl) ⟨1532387, by rfl⟩ : syracuseStep 2043183 = 3064775) B3064775
theorem B3064781 : Blo 2041435 3064781 := bbase (se 3 (by rfl) ⟨574646, by rfl⟩ : syracuseStep 3064781 = 1149293) (by norm_num)
theorem B2043187 : Blo 2041435 2043187 := bstep (se 1 (by rfl) ⟨1532390, by rfl⟩ : syracuseStep 2043187 = 3064781) B3064781
theorem B4597181 : Blo 2041435 4597181 := bbase (se 3 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 4597181 = 1723943) (by norm_num)
theorem B3064787 : Blo 2041435 3064787 := bstep (se 1 (by rfl) ⟨2298590, by rfl⟩ : syracuseStep 3064787 = 4597181) B4597181
theorem B2043191 : Blo 2041435 2043191 := bstep (se 1 (by rfl) ⟨1532393, by rfl⟩ : syracuseStep 2043191 = 3064787) B3064787
theorem B3447893 : Blo 2041435 3447893 := bbase (se 8 (by rfl) ⟨20202, by rfl⟩ : syracuseStep 3447893 = 40405) (by norm_num)
theorem B2298595 : Blo 2041435 2298595 := bstep (se 1 (by rfl) ⟨1723946, by rfl⟩ : syracuseStep 2298595 = 3447893) B3447893
theorem B3064793 : Blo 2041435 3064793 := bstep (se 2 (by rfl) ⟨1149297, by rfl⟩ : syracuseStep 3064793 = 2298595) B2298595
theorem B2043195 : Blo 2041435 2043195 := bstep (se 1 (by rfl) ⟨1532396, by rfl⟩ : syracuseStep 2043195 = 3064793) B3064793
theorem B5897717 : Blo 2041435 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B3931811 : Blo 2041435 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B2621207 : Blo 2041435 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B6989885 : Blo 2041435 6989885 := bstep (se 3 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 6989885 = 2621207) B2621207
theorem B4659923 : Blo 2041435 4659923 := bstep (se 1 (by rfl) ⟨3494942, by rfl⟩ : syracuseStep 4659923 = 6989885) B6989885
theorem B3106615 : Blo 2041435 3106615 := bstep (se 1 (by rfl) ⟨2329961, by rfl⟩ : syracuseStep 3106615 = 4659923) B4659923
theorem B4142153 : Blo 2041435 4142153 := bstep (se 2 (by rfl) ⟨1553307, by rfl⟩ : syracuseStep 4142153 = 3106615) B3106615
theorem B2761435 : Blo 2041435 2761435 := bstep (se 1 (by rfl) ⟨2071076, by rfl⟩ : syracuseStep 2761435 = 4142153) B4142153
theorem B14727653 : Blo 2041435 14727653 := bstep (se 4 (by rfl) ⟨1380717, by rfl⟩ : syracuseStep 14727653 = 2761435) B2761435
theorem B9818435 : Blo 2041435 9818435 := bstep (se 1 (by rfl) ⟨7363826, by rfl⟩ : syracuseStep 9818435 = 14727653) B14727653
theorem B6545623 : Blo 2041435 6545623 := bstep (se 1 (by rfl) ⟨4909217, by rfl⟩ : syracuseStep 6545623 = 9818435) B9818435
theorem B8727497 : Blo 2041435 8727497 := bstep (se 2 (by rfl) ⟨3272811, by rfl⟩ : syracuseStep 8727497 = 6545623) B6545623
theorem B5818331 : Blo 2041435 5818331 := bstep (se 1 (by rfl) ⟨4363748, by rfl⟩ : syracuseStep 5818331 = 8727497) B8727497
theorem B15515549 : Blo 2041435 15515549 := bstep (se 3 (by rfl) ⟨2909165, by rfl⟩ : syracuseStep 15515549 = 5818331) B5818331
theorem B10343699 : Blo 2041435 10343699 := bstep (se 1 (by rfl) ⟨7757774, by rfl⟩ : syracuseStep 10343699 = 15515549) B15515549
theorem B6895799 : Blo 2041435 6895799 := bstep (se 1 (by rfl) ⟨5171849, by rfl⟩ : syracuseStep 6895799 = 10343699) B10343699
theorem B4597199 : Blo 2041435 4597199 := bstep (se 1 (by rfl) ⟨3447899, by rfl⟩ : syracuseStep 4597199 = 6895799) B6895799
theorem B3064799 : Blo 2041435 3064799 := bstep (se 1 (by rfl) ⟨2298599, by rfl⟩ : syracuseStep 3064799 = 4597199) B4597199
theorem B2043199 : Blo 2041435 2043199 := bstep (se 1 (by rfl) ⟨1532399, by rfl⟩ : syracuseStep 2043199 = 3064799) B3064799
theorem B3064805 : Blo 2041435 3064805 := bbase (se 4 (by rfl) ⟨287325, by rfl⟩ : syracuseStep 3064805 = 574651) (by norm_num)
theorem B2043203 : Blo 2041435 2043203 := bstep (se 1 (by rfl) ⟨1532402, by rfl⟩ : syracuseStep 2043203 = 3064805) B3064805
theorem B2656981 : Blo 2041435 2656981 := bbase (se 7 (by rfl) ⟨31136, by rfl⟩ : syracuseStep 2656981 = 62273) (by norm_num)
theorem B3542641 : Blo 2041435 3542641 := bstep (se 2 (by rfl) ⟨1328490, by rfl⟩ : syracuseStep 3542641 = 2656981) B2656981
theorem B75576341 : Blo 2041435 75576341 := bstep (se 6 (by rfl) ⟨1771320, by rfl⟩ : syracuseStep 75576341 = 3542641) B3542641
theorem B50384227 : Blo 2041435 50384227 := bstep (se 1 (by rfl) ⟨37788170, by rfl⟩ : syracuseStep 50384227 = 75576341) B75576341
theorem B67178969 : Blo 2041435 67178969 := bstep (se 2 (by rfl) ⟨25192113, by rfl⟩ : syracuseStep 67178969 = 50384227) B50384227
theorem B44785979 : Blo 2041435 44785979 := bstep (se 1 (by rfl) ⟨33589484, by rfl⟩ : syracuseStep 44785979 = 67178969) B67178969
theorem B29857319 : Blo 2041435 29857319 := bstep (se 1 (by rfl) ⟨22392989, by rfl⟩ : syracuseStep 29857319 = 44785979) B44785979
theorem B19904879 : Blo 2041435 19904879 := bstep (se 1 (by rfl) ⟨14928659, by rfl⟩ : syracuseStep 19904879 = 29857319) B29857319
theorem B13269919 : Blo 2041435 13269919 := bstep (se 1 (by rfl) ⟨9952439, by rfl⟩ : syracuseStep 13269919 = 19904879) B19904879
theorem B17693225 : Blo 2041435 17693225 := bstep (se 2 (by rfl) ⟨6634959, by rfl⟩ : syracuseStep 17693225 = 13269919) B13269919
theorem B11795483 : Blo 2041435 11795483 := bstep (se 1 (by rfl) ⟨8846612, by rfl⟩ : syracuseStep 11795483 = 17693225) B17693225
theorem B7863655 : Blo 2041435 7863655 := bstep (se 1 (by rfl) ⟨5897741, by rfl⟩ : syracuseStep 7863655 = 11795483) B11795483
theorem B10484873 : Blo 2041435 10484873 := bstep (se 2 (by rfl) ⟨3931827, by rfl⟩ : syracuseStep 10484873 = 7863655) B7863655
theorem B6989915 : Blo 2041435 6989915 := bstep (se 1 (by rfl) ⟨5242436, by rfl⟩ : syracuseStep 6989915 = 10484873) B10484873
theorem B4659943 : Blo 2041435 4659943 := bstep (se 1 (by rfl) ⟨3494957, by rfl⟩ : syracuseStep 4659943 = 6989915) B6989915
theorem B6213257 : Blo 2041435 6213257 := bstep (se 2 (by rfl) ⟨2329971, by rfl⟩ : syracuseStep 6213257 = 4659943) B4659943
theorem B4142171 : Blo 2041435 4142171 := bstep (se 1 (by rfl) ⟨3106628, by rfl⟩ : syracuseStep 4142171 = 6213257) B6213257
theorem B2761447 : Blo 2041435 2761447 := bstep (se 1 (by rfl) ⟨2071085, by rfl⟩ : syracuseStep 2761447 = 4142171) B4142171
theorem B3681929 : Blo 2041435 3681929 := bstep (se 2 (by rfl) ⟨1380723, by rfl⟩ : syracuseStep 3681929 = 2761447) B2761447
theorem B2454619 : Blo 2041435 2454619 := bstep (se 1 (by rfl) ⟨1840964, by rfl⟩ : syracuseStep 2454619 = 3681929) B3681929
theorem B3272825 : Blo 2041435 3272825 := bstep (se 2 (by rfl) ⟨1227309, by rfl⟩ : syracuseStep 3272825 = 2454619) B2454619
theorem B8727533 : Blo 2041435 8727533 := bstep (se 3 (by rfl) ⟨1636412, by rfl⟩ : syracuseStep 8727533 = 3272825) B3272825
theorem B5818355 : Blo 2041435 5818355 := bstep (se 1 (by rfl) ⟨4363766, by rfl⟩ : syracuseStep 5818355 = 8727533) B8727533
theorem B3878903 : Blo 2041435 3878903 := bstep (se 1 (by rfl) ⟨2909177, by rfl⟩ : syracuseStep 3878903 = 5818355) B5818355
theorem B2585935 : Blo 2041435 2585935 := bstep (se 1 (by rfl) ⟨1939451, by rfl⟩ : syracuseStep 2585935 = 3878903) B3878903
theorem B3447913 : Blo 2041435 3447913 := bstep (se 2 (by rfl) ⟨1292967, by rfl⟩ : syracuseStep 3447913 = 2585935) B2585935
theorem B4597217 : Blo 2041435 4597217 := bstep (se 2 (by rfl) ⟨1723956, by rfl⟩ : syracuseStep 4597217 = 3447913) B3447913
theorem B3064811 : Blo 2041435 3064811 := bstep (se 1 (by rfl) ⟨2298608, by rfl⟩ : syracuseStep 3064811 = 4597217) B4597217
theorem B2043207 : Blo 2041435 2043207 := bstep (se 1 (by rfl) ⟨1532405, by rfl⟩ : syracuseStep 2043207 = 3064811) B3064811
theorem B2298613 : Blo 2041435 2298613 := bbase (se 5 (by rfl) ⟨107747, by rfl⟩ : syracuseStep 2298613 = 215495) (by norm_num)
theorem B3064817 : Blo 2041435 3064817 := bstep (se 2 (by rfl) ⟨1149306, by rfl⟩ : syracuseStep 3064817 = 2298613) B2298613
theorem B2043211 : Blo 2041435 2043211 := bstep (se 1 (by rfl) ⟨1532408, by rfl⟩ : syracuseStep 2043211 = 3064817) B3064817
theorem B2585945 : Blo 2041435 2585945 := bbase (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) (by norm_num)
theorem B6895853 : Blo 2041435 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B4597235 : Blo 2041435 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B3064823 : Blo 2041435 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B2043215 : Blo 2041435 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B3064829 : Blo 2041435 3064829 := bbase (se 3 (by rfl) ⟨574655, by rfl⟩ : syracuseStep 3064829 = 1149311) (by norm_num)
theorem B2043219 : Blo 2041435 2043219 := bstep (se 1 (by rfl) ⟨1532414, by rfl⟩ : syracuseStep 2043219 = 3064829) B3064829
theorem B4597253 : Blo 2041435 4597253 := bbase (se 4 (by rfl) ⟨430992, by rfl⟩ : syracuseStep 4597253 = 861985) (by norm_num)
theorem B3064835 : Blo 2041435 3064835 := bstep (se 1 (by rfl) ⟨2298626, by rfl⟩ : syracuseStep 3064835 = 4597253) B4597253
theorem B2043223 : Blo 2041435 2043223 := bstep (se 1 (by rfl) ⟨1532417, by rfl⟩ : syracuseStep 2043223 = 3064835) B3064835
theorem B3878941 : Blo 2041435 3878941 := bbase (se 3 (by rfl) ⟨727301, by rfl⟩ : syracuseStep 3878941 = 1454603) (by norm_num)
theorem B5171921 : Blo 2041435 5171921 := bstep (se 2 (by rfl) ⟨1939470, by rfl⟩ : syracuseStep 5171921 = 3878941) B3878941
theorem B3447947 : Blo 2041435 3447947 := bstep (se 1 (by rfl) ⟨2585960, by rfl⟩ : syracuseStep 3447947 = 5171921) B5171921
theorem B2298631 : Blo 2041435 2298631 := bstep (se 1 (by rfl) ⟨1723973, by rfl⟩ : syracuseStep 2298631 = 3447947) B3447947
theorem B3064841 : Blo 2041435 3064841 := bstep (se 2 (by rfl) ⟨1149315, by rfl⟩ : syracuseStep 3064841 = 2298631) B2298631
theorem B2043227 : Blo 2041435 2043227 := bstep (se 1 (by rfl) ⟨1532420, by rfl⟩ : syracuseStep 2043227 = 3064841) B3064841
theorem B10343861 : Blo 2041435 10343861 := bbase (se 5 (by rfl) ⟨484868, by rfl⟩ : syracuseStep 10343861 = 969737) (by norm_num)
theorem B6895907 : Blo 2041435 6895907 := bstep (se 1 (by rfl) ⟨5171930, by rfl⟩ : syracuseStep 6895907 = 10343861) B10343861
theorem B4597271 : Blo 2041435 4597271 := bstep (se 1 (by rfl) ⟨3447953, by rfl⟩ : syracuseStep 4597271 = 6895907) B6895907
theorem B3064847 : Blo 2041435 3064847 := bstep (se 1 (by rfl) ⟨2298635, by rfl⟩ : syracuseStep 3064847 = 4597271) B4597271
theorem B2043231 : Blo 2041435 2043231 := bstep (se 1 (by rfl) ⟨1532423, by rfl⟩ : syracuseStep 2043231 = 3064847) B3064847
theorem B3064853 : Blo 2041435 3064853 := bbase (se 6 (by rfl) ⟨71832, by rfl⟩ : syracuseStep 3064853 = 143665) (by norm_num)
theorem B2043235 : Blo 2041435 2043235 := bstep (se 1 (by rfl) ⟨1532426, by rfl⟩ : syracuseStep 2043235 = 3064853) B3064853
theorem B4660013 : Blo 2041435 4660013 := bbase (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) (by norm_num)
theorem B12426701 : Blo 2041435 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B33137869 : Blo 2041435 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B44183825 : Blo 2041435 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B29455883 : Blo 2041435 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B19637255 : Blo 2041435 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B13091503 : Blo 2041435 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B17455337 : Blo 2041435 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B11636891 : Blo 2041435 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B7757927 : Blo 2041435 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B5171951 : Blo 2041435 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B3447967 : Blo 2041435 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B4597289 : Blo 2041435 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B3064859 : Blo 2041435 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B2043239 : Blo 2041435 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B2298649 : Blo 2041435 2298649 := bbase (se 2 (by rfl) ⟨861993, by rfl⟩ : syracuseStep 2298649 = 1723987) (by norm_num)
theorem B3064865 : Blo 2041435 3064865 := bstep (se 2 (by rfl) ⟨1149324, by rfl⟩ : syracuseStep 3064865 = 2298649) B2298649
theorem B2043243 : Blo 2041435 2043243 := bstep (se 1 (by rfl) ⟨1532432, by rfl⟩ : syracuseStep 2043243 = 3064865) B3064865
theorem B7757957 : Blo 2041435 7757957 := bbase (se 4 (by rfl) ⟨727308, by rfl⟩ : syracuseStep 7757957 = 1454617) (by norm_num)
theorem B5171971 : Blo 2041435 5171971 := bstep (se 1 (by rfl) ⟨3878978, by rfl⟩ : syracuseStep 5171971 = 7757957) B7757957
theorem B6895961 : Blo 2041435 6895961 := bstep (se 2 (by rfl) ⟨2585985, by rfl⟩ : syracuseStep 6895961 = 5171971) B5171971
theorem B4597307 : Blo 2041435 4597307 := bstep (se 1 (by rfl) ⟨3447980, by rfl⟩ : syracuseStep 4597307 = 6895961) B6895961
theorem B3064871 : Blo 2041435 3064871 := bstep (se 1 (by rfl) ⟨2298653, by rfl⟩ : syracuseStep 3064871 = 4597307) B4597307
theorem B2043247 : Blo 2041435 2043247 := bstep (se 1 (by rfl) ⟨1532435, by rfl⟩ : syracuseStep 2043247 = 3064871) B3064871
theorem B3064877 : Blo 2041435 3064877 := bbase (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) (by norm_num)
theorem B2043251 : Blo 2041435 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B4597325 : Blo 2041435 4597325 := bbase (se 3 (by rfl) ⟨861998, by rfl⟩ : syracuseStep 4597325 = 1723997) (by norm_num)
theorem B3064883 : Blo 2041435 3064883 := bstep (se 1 (by rfl) ⟨2298662, by rfl⟩ : syracuseStep 3064883 = 4597325) B4597325
theorem B2043255 : Blo 2041435 2043255 := bstep (se 1 (by rfl) ⟨1532441, by rfl⟩ : syracuseStep 2043255 = 3064883) B3064883
theorem B2586001 : Blo 2041435 2586001 := bbase (se 2 (by rfl) ⟨969750, by rfl⟩ : syracuseStep 2586001 = 1939501) (by norm_num)
theorem B3448001 : Blo 2041435 3448001 := bstep (se 2 (by rfl) ⟨1293000, by rfl⟩ : syracuseStep 3448001 = 2586001) B2586001
theorem B2298667 : Blo 2041435 2298667 := bstep (se 1 (by rfl) ⟨1724000, by rfl⟩ : syracuseStep 2298667 = 3448001) B3448001
theorem B3064889 : Blo 2041435 3064889 := bstep (se 2 (by rfl) ⟨1149333, by rfl⟩ : syracuseStep 3064889 = 2298667) B2298667
theorem B2043259 : Blo 2041435 2043259 := bstep (se 1 (by rfl) ⟨1532444, by rfl⟩ : syracuseStep 2043259 = 3064889) B3064889
theorem B4363885 : Blo 2041435 4363885 := bbase (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) (by norm_num)
theorem B23274053 : Blo 2041435 23274053 := bstep (se 4 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 23274053 = 4363885) B4363885
theorem B15516035 : Blo 2041435 15516035 := bstep (se 1 (by rfl) ⟨11637026, by rfl⟩ : syracuseStep 15516035 = 23274053) B23274053
theorem B10344023 : Blo 2041435 10344023 := bstep (se 1 (by rfl) ⟨7758017, by rfl⟩ : syracuseStep 10344023 = 15516035) B15516035
theorem B6896015 : Blo 2041435 6896015 := bstep (se 1 (by rfl) ⟨5172011, by rfl⟩ : syracuseStep 6896015 = 10344023) B10344023
theorem B4597343 : Blo 2041435 4597343 := bstep (se 1 (by rfl) ⟨3448007, by rfl⟩ : syracuseStep 4597343 = 6896015) B6896015
theorem B3064895 : Blo 2041435 3064895 := bstep (se 1 (by rfl) ⟨2298671, by rfl⟩ : syracuseStep 3064895 = 4597343) B4597343
theorem B2043263 : Blo 2041435 2043263 := bstep (se 1 (by rfl) ⟨1532447, by rfl⟩ : syracuseStep 2043263 = 3064895) B3064895
theorem B3064901 : Blo 2041435 3064901 := bbase (se 4 (by rfl) ⟨287334, by rfl⟩ : syracuseStep 3064901 = 574669) (by norm_num)
theorem B2043267 : Blo 2041435 2043267 := bstep (se 1 (by rfl) ⟨1532450, by rfl⟩ : syracuseStep 2043267 = 3064901) B3064901
theorem B3448021 : Blo 2041435 3448021 := bbase (se 7 (by rfl) ⟨40406, by rfl⟩ : syracuseStep 3448021 = 80813) (by norm_num)
theorem B4597361 : Blo 2041435 4597361 := bstep (se 2 (by rfl) ⟨1724010, by rfl⟩ : syracuseStep 4597361 = 3448021) B3448021
theorem B3064907 : Blo 2041435 3064907 := bstep (se 1 (by rfl) ⟨2298680, by rfl⟩ : syracuseStep 3064907 = 4597361) B4597361
theorem B2043271 : Blo 2041435 2043271 := bstep (se 1 (by rfl) ⟨1532453, by rfl⟩ : syracuseStep 2043271 = 3064907) B3064907
theorem B2298685 : Blo 2041435 2298685 := bbase (se 3 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 2298685 = 862007) (by norm_num)
theorem B3064913 : Blo 2041435 3064913 := bstep (se 2 (by rfl) ⟨1149342, by rfl⟩ : syracuseStep 3064913 = 2298685) B2298685
theorem B2043275 : Blo 2041435 2043275 := bstep (se 1 (by rfl) ⟨1532456, by rfl⟩ : syracuseStep 2043275 = 3064913) B3064913
theorem B6896069 : Blo 2041435 6896069 := bbase (se 4 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 6896069 = 1293013) (by norm_num)
theorem B4597379 : Blo 2041435 4597379 := bstep (se 1 (by rfl) ⟨3448034, by rfl⟩ : syracuseStep 4597379 = 6896069) B6896069
theorem B3064919 : Blo 2041435 3064919 := bstep (se 1 (by rfl) ⟨2298689, by rfl⟩ : syracuseStep 3064919 = 4597379) B4597379
theorem B2043279 : Blo 2041435 2043279 := bstep (se 1 (by rfl) ⟨1532459, by rfl⟩ : syracuseStep 2043279 = 3064919) B3064919
theorem B3064925 : Blo 2041435 3064925 := bbase (se 3 (by rfl) ⟨574673, by rfl⟩ : syracuseStep 3064925 = 1149347) (by norm_num)
theorem B2043283 : Blo 2041435 2043283 := bstep (se 1 (by rfl) ⟨1532462, by rfl⟩ : syracuseStep 2043283 = 3064925) B3064925
theorem B4597397 : Blo 2041435 4597397 := bbase (se 6 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 4597397 = 215503) (by norm_num)
theorem B3064931 : Blo 2041435 3064931 := bstep (se 1 (by rfl) ⟨2298698, by rfl⟩ : syracuseStep 3064931 = 4597397) B4597397
theorem B2043287 : Blo 2041435 2043287 := bstep (se 1 (by rfl) ⟨1532465, by rfl⟩ : syracuseStep 2043287 = 3064931) B3064931
theorem B2181973 : Blo 2041435 2181973 := bbase (se 9 (by rfl) ⟨6392, by rfl⟩ : syracuseStep 2181973 = 12785) (by norm_num)
theorem B2909297 : Blo 2041435 2909297 := bstep (se 2 (by rfl) ⟨1090986, by rfl⟩ : syracuseStep 2909297 = 2181973) B2181973
theorem B7758125 : Blo 2041435 7758125 := bstep (se 3 (by rfl) ⟨1454648, by rfl⟩ : syracuseStep 7758125 = 2909297) B2909297
theorem B5172083 : Blo 2041435 5172083 := bstep (se 1 (by rfl) ⟨3879062, by rfl⟩ : syracuseStep 5172083 = 7758125) B7758125
theorem B3448055 : Blo 2041435 3448055 := bstep (se 1 (by rfl) ⟨2586041, by rfl⟩ : syracuseStep 3448055 = 5172083) B5172083
theorem B2298703 : Blo 2041435 2298703 := bstep (se 1 (by rfl) ⟨1724027, by rfl⟩ : syracuseStep 2298703 = 3448055) B3448055
theorem B3064937 : Blo 2041435 3064937 := bstep (se 2 (by rfl) ⟨1149351, by rfl⟩ : syracuseStep 3064937 = 2298703) B2298703
theorem B2043291 : Blo 2041435 2043291 := bstep (se 1 (by rfl) ⟨1532468, by rfl⟩ : syracuseStep 2043291 = 3064937) B3064937
theorem B13091861 : Blo 2041435 13091861 := bbase (se 6 (by rfl) ⟨306840, by rfl⟩ : syracuseStep 13091861 = 613681) (by norm_num)
theorem B8727907 : Blo 2041435 8727907 := bstep (se 1 (by rfl) ⟨6545930, by rfl⟩ : syracuseStep 8727907 = 13091861) B13091861
theorem B11637209 : Blo 2041435 11637209 := bstep (se 2 (by rfl) ⟨4363953, by rfl⟩ : syracuseStep 11637209 = 8727907) B8727907
theorem B7758139 : Blo 2041435 7758139 := bstep (se 1 (by rfl) ⟨5818604, by rfl⟩ : syracuseStep 7758139 = 11637209) B11637209
theorem B10344185 : Blo 2041435 10344185 := bstep (se 2 (by rfl) ⟨3879069, by rfl⟩ : syracuseStep 10344185 = 7758139) B7758139
theorem B6896123 : Blo 2041435 6896123 := bstep (se 1 (by rfl) ⟨5172092, by rfl⟩ : syracuseStep 6896123 = 10344185) B10344185
theorem B4597415 : Blo 2041435 4597415 := bstep (se 1 (by rfl) ⟨3448061, by rfl⟩ : syracuseStep 4597415 = 6896123) B6896123
theorem B3064943 : Blo 2041435 3064943 := bstep (se 1 (by rfl) ⟨2298707, by rfl⟩ : syracuseStep 3064943 = 4597415) B4597415
theorem B2043295 : Blo 2041435 2043295 := bstep (se 1 (by rfl) ⟨1532471, by rfl⟩ : syracuseStep 2043295 = 3064943) B3064943
theorem B3064949 : Blo 2041435 3064949 := bbase (se 5 (by rfl) ⟨143669, by rfl⟩ : syracuseStep 3064949 = 287339) (by norm_num)
theorem B2043299 : Blo 2041435 2043299 := bstep (se 1 (by rfl) ⟨1532474, by rfl⟩ : syracuseStep 2043299 = 3064949) B3064949
theorem B3879085 : Blo 2041435 3879085 := bbase (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) (by norm_num)
theorem B5172113 : Blo 2041435 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B3448075 : Blo 2041435 3448075 := bstep (se 1 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 3448075 = 5172113) B5172113
theorem B4597433 : Blo 2041435 4597433 := bstep (se 2 (by rfl) ⟨1724037, by rfl⟩ : syracuseStep 4597433 = 3448075) B3448075
theorem B3064955 : Blo 2041435 3064955 := bstep (se 1 (by rfl) ⟨2298716, by rfl⟩ : syracuseStep 3064955 = 4597433) B4597433
theorem B2043303 : Blo 2041435 2043303 := bstep (se 1 (by rfl) ⟨1532477, by rfl⟩ : syracuseStep 2043303 = 3064955) B3064955
theorem B2298721 : Blo 2041435 2298721 := bbase (se 2 (by rfl) ⟨862020, by rfl⟩ : syracuseStep 2298721 = 1724041) (by norm_num)
theorem B3064961 : Blo 2041435 3064961 := bstep (se 2 (by rfl) ⟨1149360, by rfl⟩ : syracuseStep 3064961 = 2298721) B2298721
theorem B2043307 : Blo 2041435 2043307 := bstep (se 1 (by rfl) ⟨1532480, by rfl⟩ : syracuseStep 2043307 = 3064961) B3064961
theorem B5172133 : Blo 2041435 5172133 := bbase (se 4 (by rfl) ⟨484887, by rfl⟩ : syracuseStep 5172133 = 969775) (by norm_num)
theorem B6896177 : Blo 2041435 6896177 := bstep (se 2 (by rfl) ⟨2586066, by rfl⟩ : syracuseStep 6896177 = 5172133) B5172133
theorem B4597451 : Blo 2041435 4597451 := bstep (se 1 (by rfl) ⟨3448088, by rfl⟩ : syracuseStep 4597451 = 6896177) B6896177
theorem B3064967 : Blo 2041435 3064967 := bstep (se 1 (by rfl) ⟨2298725, by rfl⟩ : syracuseStep 3064967 = 4597451) B4597451
theorem B2043311 : Blo 2041435 2043311 := bstep (se 1 (by rfl) ⟨1532483, by rfl⟩ : syracuseStep 2043311 = 3064967) B3064967
theorem B3064973 : Blo 2041435 3064973 := bbase (se 3 (by rfl) ⟨574682, by rfl⟩ : syracuseStep 3064973 = 1149365) (by norm_num)
theorem B2043315 : Blo 2041435 2043315 := bstep (se 1 (by rfl) ⟨1532486, by rfl⟩ : syracuseStep 2043315 = 3064973) B3064973
theorem B4597469 : Blo 2041435 4597469 := bbase (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) (by norm_num)
theorem B3064979 : Blo 2041435 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B2043319 : Blo 2041435 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B3448109 : Blo 2041435 3448109 := bbase (se 3 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 3448109 = 1293041) (by norm_num)
theorem B2298739 : Blo 2041435 2298739 := bstep (se 1 (by rfl) ⟨1724054, by rfl⟩ : syracuseStep 2298739 = 3448109) B3448109
theorem B3064985 : Blo 2041435 3064985 := bstep (se 2 (by rfl) ⟨1149369, by rfl⟩ : syracuseStep 3064985 = 2298739) B2298739
theorem B2043323 : Blo 2041435 2043323 := bstep (se 1 (by rfl) ⟨1532492, by rfl⟩ : syracuseStep 2043323 = 3064985) B3064985
theorem B10773557 : Blo 2041435 10773557 := bbase (se 5 (by rfl) ⟨505010, by rfl⟩ : syracuseStep 10773557 = 1010021) (by norm_num)
theorem B7182371 : Blo 2041435 7182371 := bstep (se 1 (by rfl) ⟨5386778, by rfl⟩ : syracuseStep 7182371 = 10773557) B10773557
theorem B4788247 : Blo 2041435 4788247 := bstep (se 1 (by rfl) ⟨3591185, by rfl⟩ : syracuseStep 4788247 = 7182371) B7182371
theorem B6384329 : Blo 2041435 6384329 := bstep (se 2 (by rfl) ⟨2394123, by rfl⟩ : syracuseStep 6384329 = 4788247) B4788247
theorem B4256219 : Blo 2041435 4256219 := bstep (se 1 (by rfl) ⟨3192164, by rfl⟩ : syracuseStep 4256219 = 6384329) B6384329
theorem B2837479 : Blo 2041435 2837479 := bstep (se 1 (by rfl) ⟨2128109, by rfl⟩ : syracuseStep 2837479 = 4256219) B4256219
theorem B3783305 : Blo 2041435 3783305 := bstep (se 2 (by rfl) ⟨1418739, by rfl⟩ : syracuseStep 3783305 = 2837479) B2837479
theorem B10088813 : Blo 2041435 10088813 := bstep (se 3 (by rfl) ⟨1891652, by rfl⟩ : syracuseStep 10088813 = 3783305) B3783305
theorem B6725875 : Blo 2041435 6725875 := bstep (se 1 (by rfl) ⟨5044406, by rfl⟩ : syracuseStep 6725875 = 10088813) B10088813
theorem B8967833 : Blo 2041435 8967833 := bstep (se 2 (by rfl) ⟨3362937, by rfl⟩ : syracuseStep 8967833 = 6725875) B6725875
theorem B5978555 : Blo 2041435 5978555 := bstep (se 1 (by rfl) ⟨4483916, by rfl⟩ : syracuseStep 5978555 = 8967833) B8967833
theorem B3985703 : Blo 2041435 3985703 := bstep (se 1 (by rfl) ⟨2989277, by rfl⟩ : syracuseStep 3985703 = 5978555) B5978555
theorem B2657135 : Blo 2041435 2657135 := bstep (se 1 (by rfl) ⟨1992851, by rfl⟩ : syracuseStep 2657135 = 3985703) B3985703
theorem B7085693 : Blo 2041435 7085693 := bstep (se 3 (by rfl) ⟨1328567, by rfl⟩ : syracuseStep 7085693 = 2657135) B2657135
theorem B4723795 : Blo 2041435 4723795 := bstep (se 1 (by rfl) ⟨3542846, by rfl⟩ : syracuseStep 4723795 = 7085693) B7085693
theorem B6298393 : Blo 2041435 6298393 := bstep (se 2 (by rfl) ⟨2361897, by rfl⟩ : syracuseStep 6298393 = 4723795) B4723795
theorem B8397857 : Blo 2041435 8397857 := bstep (se 2 (by rfl) ⟨3149196, by rfl⟩ : syracuseStep 8397857 = 6298393) B6298393
theorem B22394285 : Blo 2041435 22394285 := bstep (se 3 (by rfl) ⟨4198928, by rfl⟩ : syracuseStep 22394285 = 8397857) B8397857
theorem B14929523 : Blo 2041435 14929523 := bstep (se 1 (by rfl) ⟨11197142, by rfl⟩ : syracuseStep 14929523 = 22394285) B22394285
theorem B9953015 : Blo 2041435 9953015 := bstep (se 1 (by rfl) ⟨7464761, by rfl⟩ : syracuseStep 9953015 = 14929523) B14929523
theorem B26541373 : Blo 2041435 26541373 := bstep (se 3 (by rfl) ⟨4976507, by rfl⟩ : syracuseStep 26541373 = 9953015) B9953015
theorem B35388497 : Blo 2041435 35388497 := bstep (se 2 (by rfl) ⟨13270686, by rfl⟩ : syracuseStep 35388497 = 26541373) B26541373
theorem B23592331 : Blo 2041435 23592331 := bstep (se 1 (by rfl) ⟨17694248, by rfl⟩ : syracuseStep 23592331 = 35388497) B35388497
theorem B31456441 : Blo 2041435 31456441 := bstep (se 2 (by rfl) ⟨11796165, by rfl⟩ : syracuseStep 31456441 = 23592331) B23592331
theorem B41941921 : Blo 2041435 41941921 := bstep (se 2 (by rfl) ⟨15728220, by rfl⟩ : syracuseStep 41941921 = 31456441) B31456441
theorem B55922561 : Blo 2041435 55922561 := bstep (se 2 (by rfl) ⟨20970960, by rfl⟩ : syracuseStep 55922561 = 41941921) B41941921
theorem B37281707 : Blo 2041435 37281707 := bstep (se 1 (by rfl) ⟨27961280, by rfl⟩ : syracuseStep 37281707 = 55922561) B55922561
theorem B24854471 : Blo 2041435 24854471 := bstep (se 1 (by rfl) ⟨18640853, by rfl⟩ : syracuseStep 24854471 = 37281707) B37281707
theorem B16569647 : Blo 2041435 16569647 := bstep (se 1 (by rfl) ⟨12427235, by rfl⟩ : syracuseStep 16569647 = 24854471) B24854471
theorem B11046431 : Blo 2041435 11046431 := bstep (se 1 (by rfl) ⟨8284823, by rfl⟩ : syracuseStep 11046431 = 16569647) B16569647
theorem B7364287 : Blo 2041435 7364287 := bstep (se 1 (by rfl) ⟨5523215, by rfl⟩ : syracuseStep 7364287 = 11046431) B11046431
theorem B39276197 : Blo 2041435 39276197 := bstep (se 4 (by rfl) ⟨3682143, by rfl⟩ : syracuseStep 39276197 = 7364287) B7364287
theorem B26184131 : Blo 2041435 26184131 := bstep (se 1 (by rfl) ⟨19638098, by rfl⟩ : syracuseStep 26184131 = 39276197) B39276197
theorem B17456087 : Blo 2041435 17456087 := bstep (se 1 (by rfl) ⟨13092065, by rfl⟩ : syracuseStep 17456087 = 26184131) B26184131
theorem B11637391 : Blo 2041435 11637391 := bstep (se 1 (by rfl) ⟨8728043, by rfl⟩ : syracuseStep 11637391 = 17456087) B17456087
theorem B15516521 : Blo 2041435 15516521 := bstep (se 2 (by rfl) ⟨5818695, by rfl⟩ : syracuseStep 15516521 = 11637391) B11637391
theorem B10344347 : Blo 2041435 10344347 := bstep (se 1 (by rfl) ⟨7758260, by rfl⟩ : syracuseStep 10344347 = 15516521) B15516521
theorem B6896231 : Blo 2041435 6896231 := bstep (se 1 (by rfl) ⟨5172173, by rfl⟩ : syracuseStep 6896231 = 10344347) B10344347
theorem B4597487 : Blo 2041435 4597487 := bstep (se 1 (by rfl) ⟨3448115, by rfl⟩ : syracuseStep 4597487 = 6896231) B6896231
theorem B3064991 : Blo 2041435 3064991 := bstep (se 1 (by rfl) ⟨2298743, by rfl⟩ : syracuseStep 3064991 = 4597487) B4597487
theorem B2043327 : Blo 2041435 2043327 := bstep (se 1 (by rfl) ⟨1532495, by rfl⟩ : syracuseStep 2043327 = 3064991) B3064991
theorem B3064997 : Blo 2041435 3064997 := bbase (se 4 (by rfl) ⟨287343, by rfl⟩ : syracuseStep 3064997 = 574687) (by norm_num)
theorem B2043331 : Blo 2041435 2043331 := bstep (se 1 (by rfl) ⟨1532498, by rfl⟩ : syracuseStep 2043331 = 3064997) B3064997
theorem B2586097 : Blo 2041435 2586097 := bbase (se 2 (by rfl) ⟨969786, by rfl⟩ : syracuseStep 2586097 = 1939573) (by norm_num)
theorem B3448129 : Blo 2041435 3448129 := bstep (se 2 (by rfl) ⟨1293048, by rfl⟩ : syracuseStep 3448129 = 2586097) B2586097
theorem B4597505 : Blo 2041435 4597505 := bstep (se 2 (by rfl) ⟨1724064, by rfl⟩ : syracuseStep 4597505 = 3448129) B3448129
theorem B3065003 : Blo 2041435 3065003 := bstep (se 1 (by rfl) ⟨2298752, by rfl⟩ : syracuseStep 3065003 = 4597505) B4597505
theorem B2043335 : Blo 2041435 2043335 := bstep (se 1 (by rfl) ⟨1532501, by rfl⟩ : syracuseStep 2043335 = 3065003) B3065003
theorem B2298757 : Blo 2041435 2298757 := bbase (se 4 (by rfl) ⟨215508, by rfl⟩ : syracuseStep 2298757 = 431017) (by norm_num)
theorem B3065009 : Blo 2041435 3065009 := bstep (se 2 (by rfl) ⟨1149378, by rfl⟩ : syracuseStep 3065009 = 2298757) B2298757
theorem B2043339 : Blo 2041435 2043339 := bstep (se 1 (by rfl) ⟨1532504, by rfl⟩ : syracuseStep 2043339 = 3065009) B3065009
theorem B4909565 : Blo 2041435 4909565 := bbase (se 3 (by rfl) ⟨920543, by rfl⟩ : syracuseStep 4909565 = 1841087) (by norm_num)
theorem B3273043 : Blo 2041435 3273043 := bstep (se 1 (by rfl) ⟨2454782, by rfl⟩ : syracuseStep 3273043 = 4909565) B4909565
theorem B4364057 : Blo 2041435 4364057 := bstep (se 2 (by rfl) ⟨1636521, by rfl⟩ : syracuseStep 4364057 = 3273043) B3273043
theorem B2909371 : Blo 2041435 2909371 := bstep (se 1 (by rfl) ⟨2182028, by rfl⟩ : syracuseStep 2909371 = 4364057) B4364057
theorem B3879161 : Blo 2041435 3879161 := bstep (se 2 (by rfl) ⟨1454685, by rfl⟩ : syracuseStep 3879161 = 2909371) B2909371
theorem B2586107 : Blo 2041435 2586107 := bstep (se 1 (by rfl) ⟨1939580, by rfl⟩ : syracuseStep 2586107 = 3879161) B3879161
theorem B6896285 : Blo 2041435 6896285 := bstep (se 3 (by rfl) ⟨1293053, by rfl⟩ : syracuseStep 6896285 = 2586107) B2586107
theorem B4597523 : Blo 2041435 4597523 := bstep (se 1 (by rfl) ⟨3448142, by rfl⟩ : syracuseStep 4597523 = 6896285) B6896285
theorem B3065015 : Blo 2041435 3065015 := bstep (se 1 (by rfl) ⟨2298761, by rfl⟩ : syracuseStep 3065015 = 4597523) B4597523
theorem B2043343 : Blo 2041435 2043343 := bstep (se 1 (by rfl) ⟨1532507, by rfl⟩ : syracuseStep 2043343 = 3065015) B3065015
theorem B3065021 : Blo 2041435 3065021 := bbase (se 3 (by rfl) ⟨574691, by rfl⟩ : syracuseStep 3065021 = 1149383) (by norm_num)
theorem B2043347 : Blo 2041435 2043347 := bstep (se 1 (by rfl) ⟨1532510, by rfl⟩ : syracuseStep 2043347 = 3065021) B3065021
theorem B4597541 : Blo 2041435 4597541 := bbase (se 4 (by rfl) ⟨431019, by rfl⟩ : syracuseStep 4597541 = 862039) (by norm_num)
theorem B3065027 : Blo 2041435 3065027 := bstep (se 1 (by rfl) ⟨2298770, by rfl⟩ : syracuseStep 3065027 = 4597541) B4597541
theorem B2043351 : Blo 2041435 2043351 := bstep (se 1 (by rfl) ⟨1532513, by rfl⟩ : syracuseStep 2043351 = 3065027) B3065027
theorem B5172245 : Blo 2041435 5172245 := bbase (se 6 (by rfl) ⟨121224, by rfl⟩ : syracuseStep 5172245 = 242449) (by norm_num)
theorem B3448163 : Blo 2041435 3448163 := bstep (se 1 (by rfl) ⟨2586122, by rfl⟩ : syracuseStep 3448163 = 5172245) B5172245
theorem B2298775 : Blo 2041435 2298775 := bstep (se 1 (by rfl) ⟨1724081, by rfl⟩ : syracuseStep 2298775 = 3448163) B3448163
theorem B3065033 : Blo 2041435 3065033 := bstep (se 2 (by rfl) ⟨1149387, by rfl⟩ : syracuseStep 3065033 = 2298775) B2298775
theorem B2043355 : Blo 2041435 2043355 := bstep (se 1 (by rfl) ⟨1532516, by rfl⟩ : syracuseStep 2043355 = 3065033) B3065033
theorem B8728181 : Blo 2041435 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B5818787 : Blo 2041435 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B3879191 : Blo 2041435 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B10344509 : Blo 2041435 10344509 := bstep (se 3 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 10344509 = 3879191) B3879191
theorem B6896339 : Blo 2041435 6896339 := bstep (se 1 (by rfl) ⟨5172254, by rfl⟩ : syracuseStep 6896339 = 10344509) B10344509
theorem B4597559 : Blo 2041435 4597559 := bstep (se 1 (by rfl) ⟨3448169, by rfl⟩ : syracuseStep 4597559 = 6896339) B6896339
theorem B3065039 : Blo 2041435 3065039 := bstep (se 1 (by rfl) ⟨2298779, by rfl⟩ : syracuseStep 3065039 = 4597559) B4597559
theorem B2043359 : Blo 2041435 2043359 := bstep (se 1 (by rfl) ⟨1532519, by rfl⟩ : syracuseStep 2043359 = 3065039) B3065039
theorem B3065045 : Blo 2041435 3065045 := bbase (se 7 (by rfl) ⟨35918, by rfl⟩ : syracuseStep 3065045 = 71837) (by norm_num)
theorem B2043363 : Blo 2041435 2043363 := bstep (se 1 (by rfl) ⟨1532522, by rfl⟩ : syracuseStep 2043363 = 3065045) B3065045
theorem B2909405 : Blo 2041435 2909405 := bbase (se 3 (by rfl) ⟨545513, by rfl⟩ : syracuseStep 2909405 = 1091027) (by norm_num)
theorem B7758413 : Blo 2041435 7758413 := bstep (se 3 (by rfl) ⟨1454702, by rfl⟩ : syracuseStep 7758413 = 2909405) B2909405
theorem B5172275 : Blo 2041435 5172275 := bstep (se 1 (by rfl) ⟨3879206, by rfl⟩ : syracuseStep 5172275 = 7758413) B7758413
theorem B3448183 : Blo 2041435 3448183 := bstep (se 1 (by rfl) ⟨2586137, by rfl⟩ : syracuseStep 3448183 = 5172275) B5172275
theorem B4597577 : Blo 2041435 4597577 := bstep (se 2 (by rfl) ⟨1724091, by rfl⟩ : syracuseStep 4597577 = 3448183) B3448183
theorem B3065051 : Blo 2041435 3065051 := bstep (se 1 (by rfl) ⟨2298788, by rfl⟩ : syracuseStep 3065051 = 4597577) B4597577
theorem B2043367 : Blo 2041435 2043367 := bstep (se 1 (by rfl) ⟨1532525, by rfl⟩ : syracuseStep 2043367 = 3065051) B3065051
theorem B2298793 : Blo 2041435 2298793 := bbase (se 2 (by rfl) ⟨862047, by rfl⟩ : syracuseStep 2298793 = 1724095) (by norm_num)
theorem B3065057 : Blo 2041435 3065057 := bstep (se 2 (by rfl) ⟨1149396, by rfl⟩ : syracuseStep 3065057 = 2298793) B2298793
theorem B2043371 : Blo 2041435 2043371 := bstep (se 1 (by rfl) ⟨1532528, by rfl⟩ : syracuseStep 2043371 = 3065057) B3065057
theorem B4660325 : Blo 2041435 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B3106883 : Blo 2041435 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B2071255 : Blo 2041435 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B2761673 : Blo 2041435 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B7364461 : Blo 2041435 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B9819281 : Blo 2041435 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B6546187 : Blo 2041435 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B8728249 : Blo 2041435 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B11637665 : Blo 2041435 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B7758443 : Blo 2041435 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B5172295 : Blo 2041435 5172295 := bstep (se 1 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 5172295 = 7758443) B7758443
theorem B6896393 : Blo 2041435 6896393 := bstep (se 2 (by rfl) ⟨2586147, by rfl⟩ : syracuseStep 6896393 = 5172295) B5172295
theorem B4597595 : Blo 2041435 4597595 := bstep (se 1 (by rfl) ⟨3448196, by rfl⟩ : syracuseStep 4597595 = 6896393) B6896393
theorem B3065063 : Blo 2041435 3065063 := bstep (se 1 (by rfl) ⟨2298797, by rfl⟩ : syracuseStep 3065063 = 4597595) B4597595
theorem B2043375 : Blo 2041435 2043375 := bstep (se 1 (by rfl) ⟨1532531, by rfl⟩ : syracuseStep 2043375 = 3065063) B3065063
theorem B3065069 : Blo 2041435 3065069 := bbase (se 3 (by rfl) ⟨574700, by rfl⟩ : syracuseStep 3065069 = 1149401) (by norm_num)
theorem B2043379 : Blo 2041435 2043379 := bstep (se 1 (by rfl) ⟨1532534, by rfl⟩ : syracuseStep 2043379 = 3065069) B3065069
theorem B4597613 : Blo 2041435 4597613 := bbase (se 3 (by rfl) ⟨862052, by rfl⟩ : syracuseStep 4597613 = 1724105) (by norm_num)
theorem B3065075 : Blo 2041435 3065075 := bstep (se 1 (by rfl) ⟨2298806, by rfl⟩ : syracuseStep 3065075 = 4597613) B4597613
theorem B2043383 : Blo 2041435 2043383 := bstep (se 1 (by rfl) ⟨1532537, by rfl⟩ : syracuseStep 2043383 = 3065075) B3065075
theorem B3879245 : Blo 2041435 3879245 := bbase (se 3 (by rfl) ⟨727358, by rfl⟩ : syracuseStep 3879245 = 1454717) (by norm_num)
theorem B2586163 : Blo 2041435 2586163 := bstep (se 1 (by rfl) ⟨1939622, by rfl⟩ : syracuseStep 2586163 = 3879245) B3879245
theorem B3448217 : Blo 2041435 3448217 := bstep (se 2 (by rfl) ⟨1293081, by rfl⟩ : syracuseStep 3448217 = 2586163) B2586163
theorem B2298811 : Blo 2041435 2298811 := bstep (se 1 (by rfl) ⟨1724108, by rfl⟩ : syracuseStep 2298811 = 3448217) B3448217
theorem B3065081 : Blo 2041435 3065081 := bstep (se 2 (by rfl) ⟨1149405, by rfl⟩ : syracuseStep 3065081 = 2298811) B2298811
theorem B2043387 : Blo 2041435 2043387 := bstep (se 1 (by rfl) ⟨1532540, by rfl⟩ : syracuseStep 2043387 = 3065081) B3065081
theorem B16570165 : Blo 2041435 16570165 := bbase (se 5 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 16570165 = 1553453) (by norm_num)
theorem B22093553 : Blo 2041435 22093553 := bstep (se 2 (by rfl) ⟨8285082, by rfl⟩ : syracuseStep 22093553 = 16570165) B16570165
theorem B14729035 : Blo 2041435 14729035 := bstep (se 1 (by rfl) ⟨11046776, by rfl⟩ : syracuseStep 14729035 = 22093553) B22093553
theorem B19638713 : Blo 2041435 19638713 := bstep (se 2 (by rfl) ⟨7364517, by rfl⟩ : syracuseStep 19638713 = 14729035) B14729035
theorem B52369901 : Blo 2041435 52369901 := bstep (se 3 (by rfl) ⟨9819356, by rfl⟩ : syracuseStep 52369901 = 19638713) B19638713
theorem B34913267 : Blo 2041435 34913267 := bstep (se 1 (by rfl) ⟨26184950, by rfl⟩ : syracuseStep 34913267 = 52369901) B52369901
theorem B23275511 : Blo 2041435 23275511 := bstep (se 1 (by rfl) ⟨17456633, by rfl⟩ : syracuseStep 23275511 = 34913267) B34913267
theorem B15517007 : Blo 2041435 15517007 := bstep (se 1 (by rfl) ⟨11637755, by rfl⟩ : syracuseStep 15517007 = 23275511) B23275511
theorem B10344671 : Blo 2041435 10344671 := bstep (se 1 (by rfl) ⟨7758503, by rfl⟩ : syracuseStep 10344671 = 15517007) B15517007
theorem B6896447 : Blo 2041435 6896447 := bstep (se 1 (by rfl) ⟨5172335, by rfl⟩ : syracuseStep 6896447 = 10344671) B10344671
theorem B4597631 : Blo 2041435 4597631 := bstep (se 1 (by rfl) ⟨3448223, by rfl⟩ : syracuseStep 4597631 = 6896447) B6896447
theorem B3065087 : Blo 2041435 3065087 := bstep (se 1 (by rfl) ⟨2298815, by rfl⟩ : syracuseStep 3065087 = 4597631) B4597631
theorem B2043391 : Blo 2041435 2043391 := bstep (se 1 (by rfl) ⟨1532543, by rfl⟩ : syracuseStep 2043391 = 3065087) B3065087
theorem B3065093 : Blo 2041435 3065093 := bbase (se 4 (by rfl) ⟨287352, by rfl⟩ : syracuseStep 3065093 = 574705) (by norm_num)
theorem B2043395 : Blo 2041435 2043395 := bstep (se 1 (by rfl) ⟨1532546, by rfl⟩ : syracuseStep 2043395 = 3065093) B3065093
theorem B3448237 : Blo 2041435 3448237 := bbase (se 3 (by rfl) ⟨646544, by rfl⟩ : syracuseStep 3448237 = 1293089) (by norm_num)
theorem B4597649 : Blo 2041435 4597649 := bstep (se 2 (by rfl) ⟨1724118, by rfl⟩ : syracuseStep 4597649 = 3448237) B3448237
theorem B3065099 : Blo 2041435 3065099 := bstep (se 1 (by rfl) ⟨2298824, by rfl⟩ : syracuseStep 3065099 = 4597649) B4597649
theorem B2043399 : Blo 2041435 2043399 := bstep (se 1 (by rfl) ⟨1532549, by rfl⟩ : syracuseStep 2043399 = 3065099) B3065099
theorem B2298829 : Blo 2041435 2298829 := bbase (se 3 (by rfl) ⟨431030, by rfl⟩ : syracuseStep 2298829 = 862061) (by norm_num)
theorem B3065105 : Blo 2041435 3065105 := bstep (se 2 (by rfl) ⟨1149414, by rfl⟩ : syracuseStep 3065105 = 2298829) B2298829
theorem B2043403 : Blo 2041435 2043403 := bstep (se 1 (by rfl) ⟨1532552, by rfl⟩ : syracuseStep 2043403 = 3065105) B3065105
theorem B6896501 : Blo 2041435 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B4597667 : Blo 2041435 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B3065111 : Blo 2041435 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B2043407 : Blo 2041435 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B3065117 : Blo 2041435 3065117 := bbase (se 3 (by rfl) ⟨574709, by rfl⟩ : syracuseStep 3065117 = 1149419) (by norm_num)
theorem B2043411 : Blo 2041435 2043411 := bstep (se 1 (by rfl) ⟨1532558, by rfl⟩ : syracuseStep 2043411 = 3065117) B3065117
theorem B4597685 : Blo 2041435 4597685 := bbase (se 5 (by rfl) ⟨215516, by rfl⟩ : syracuseStep 4597685 = 431033) (by norm_num)
theorem B3065123 : Blo 2041435 3065123 := bstep (se 1 (by rfl) ⟨2298842, by rfl⟩ : syracuseStep 3065123 = 4597685) B4597685
theorem B2043415 : Blo 2041435 2043415 := bstep (se 1 (by rfl) ⟨1532561, by rfl⟩ : syracuseStep 2043415 = 3065123) B3065123
theorem B2761733 : Blo 2041435 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B7364621 : Blo 2041435 7364621 := bstep (se 3 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 7364621 = 2761733) B2761733
theorem B4909747 : Blo 2041435 4909747 := bstep (se 1 (by rfl) ⟨3682310, by rfl⟩ : syracuseStep 4909747 = 7364621) B7364621
theorem B6546329 : Blo 2041435 6546329 := bstep (se 2 (by rfl) ⟨2454873, by rfl⟩ : syracuseStep 6546329 = 4909747) B4909747
theorem B4364219 : Blo 2041435 4364219 := bstep (se 1 (by rfl) ⟨3273164, by rfl⟩ : syracuseStep 4364219 = 6546329) B6546329
theorem B11637917 : Blo 2041435 11637917 := bstep (se 3 (by rfl) ⟨2182109, by rfl⟩ : syracuseStep 11637917 = 4364219) B4364219
theorem B7758611 : Blo 2041435 7758611 := bstep (se 1 (by rfl) ⟨5818958, by rfl⟩ : syracuseStep 7758611 = 11637917) B11637917
theorem B5172407 : Blo 2041435 5172407 := bstep (se 1 (by rfl) ⟨3879305, by rfl⟩ : syracuseStep 5172407 = 7758611) B7758611
theorem B3448271 : Blo 2041435 3448271 := bstep (se 1 (by rfl) ⟨2586203, by rfl⟩ : syracuseStep 3448271 = 5172407) B5172407
theorem B2298847 : Blo 2041435 2298847 := bstep (se 1 (by rfl) ⟨1724135, by rfl⟩ : syracuseStep 2298847 = 3448271) B3448271
theorem B3065129 : Blo 2041435 3065129 := bstep (se 2 (by rfl) ⟨1149423, by rfl⟩ : syracuseStep 3065129 = 2298847) B2298847
theorem B2043419 : Blo 2041435 2043419 := bstep (se 1 (by rfl) ⟨1532564, by rfl⟩ : syracuseStep 2043419 = 3065129) B3065129
theorem B6546341 : Blo 2041435 6546341 := bbase (se 4 (by rfl) ⟨613719, by rfl⟩ : syracuseStep 6546341 = 1227439) (by norm_num)
theorem B4364227 : Blo 2041435 4364227 := bstep (se 1 (by rfl) ⟨3273170, by rfl⟩ : syracuseStep 4364227 = 6546341) B6546341
theorem B5818969 : Blo 2041435 5818969 := bstep (se 2 (by rfl) ⟨2182113, by rfl⟩ : syracuseStep 5818969 = 4364227) B4364227
theorem B7758625 : Blo 2041435 7758625 := bstep (se 2 (by rfl) ⟨2909484, by rfl⟩ : syracuseStep 7758625 = 5818969) B5818969
theorem B10344833 : Blo 2041435 10344833 := bstep (se 2 (by rfl) ⟨3879312, by rfl⟩ : syracuseStep 10344833 = 7758625) B7758625
theorem B6896555 : Blo 2041435 6896555 := bstep (se 1 (by rfl) ⟨5172416, by rfl⟩ : syracuseStep 6896555 = 10344833) B10344833
theorem B4597703 : Blo 2041435 4597703 := bstep (se 1 (by rfl) ⟨3448277, by rfl⟩ : syracuseStep 4597703 = 6896555) B6896555
theorem B3065135 : Blo 2041435 3065135 := bstep (se 1 (by rfl) ⟨2298851, by rfl⟩ : syracuseStep 3065135 = 4597703) B4597703
theorem B2043423 : Blo 2041435 2043423 := bstep (se 1 (by rfl) ⟨1532567, by rfl⟩ : syracuseStep 2043423 = 3065135) B3065135
theorem B3065141 : Blo 2041435 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B2043427 : Blo 2041435 2043427 := bstep (se 1 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 2043427 = 3065141) B3065141
theorem B5172437 : Blo 2041435 5172437 := bbase (se 7 (by rfl) ⟨60614, by rfl⟩ : syracuseStep 5172437 = 121229) (by norm_num)
theorem B3448291 : Blo 2041435 3448291 := bstep (se 1 (by rfl) ⟨2586218, by rfl⟩ : syracuseStep 3448291 = 5172437) B5172437
theorem B4597721 : Blo 2041435 4597721 := bstep (se 2 (by rfl) ⟨1724145, by rfl⟩ : syracuseStep 4597721 = 3448291) B3448291
theorem B3065147 : Blo 2041435 3065147 := bstep (se 1 (by rfl) ⟨2298860, by rfl⟩ : syracuseStep 3065147 = 4597721) B4597721
theorem B2043431 : Blo 2041435 2043431 := bstep (se 1 (by rfl) ⟨1532573, by rfl⟩ : syracuseStep 2043431 = 3065147) B3065147
theorem B2298865 : Blo 2041435 2298865 := bbase (se 2 (by rfl) ⟨862074, by rfl⟩ : syracuseStep 2298865 = 1724149) (by norm_num)
theorem B3065153 : Blo 2041435 3065153 := bstep (se 2 (by rfl) ⟨1149432, by rfl⟩ : syracuseStep 3065153 = 2298865) B2298865
theorem B2043435 : Blo 2041435 2043435 := bstep (se 1 (by rfl) ⟨1532576, by rfl⟩ : syracuseStep 2043435 = 3065153) B3065153
theorem C0 (j : ℕ) (h1 : 510358 ≤ j) (h2 : j ≤ 510858) : Blo 2041435 (4 * j + 3) := by
  interval_cases j
  · exact B2041435
  · exact B2041439
  · exact B2041443
  · exact B2041447
  · exact B2041451
  · exact B2041455
  · exact B2041459
  · exact B2041463
  · exact B2041467
  · exact B2041471
  · exact B2041475
  · exact B2041479
  · exact B2041483
  · exact B2041487
  · exact B2041491
  · exact B2041495
  · exact B2041499
  · exact B2041503
  · exact B2041507
  · exact B2041511
  · exact B2041515
  · exact B2041519
  · exact B2041523
  · exact B2041527
  · exact B2041531
  · exact B2041535
  · exact B2041539
  · exact B2041543
  · exact B2041547
  · exact B2041551
  · exact B2041555
  · exact B2041559
  · exact B2041563
  · exact B2041567
  · exact B2041571
  · exact B2041575
  · exact B2041579
  · exact B2041583
  · exact B2041587
  · exact B2041591
  · exact B2041595
  · exact B2041599
  · exact B2041603
  · exact B2041607
  · exact B2041611
  · exact B2041615
  · exact B2041619
  · exact B2041623
  · exact B2041627
  · exact B2041631
  · exact B2041635
  · exact B2041639
  · exact B2041643
  · exact B2041647
  · exact B2041651
  · exact B2041655
  · exact B2041659
  · exact B2041663
  · exact B2041667
  · exact B2041671
  · exact B2041675
  · exact B2041679
  · exact B2041683
  · exact B2041687
  · exact B2041691
  · exact B2041695
  · exact B2041699
  · exact B2041703
  · exact B2041707
  · exact B2041711
  · exact B2041715
  · exact B2041719
  · exact B2041723
  · exact B2041727
  · exact B2041731
  · exact B2041735
  · exact B2041739
  · exact B2041743
  · exact B2041747
  · exact B2041751
  · exact B2041755
  · exact B2041759
  · exact B2041763
  · exact B2041767
  · exact B2041771
  · exact B2041775
  · exact B2041779
  · exact B2041783
  · exact B2041787
  · exact B2041791
  · exact B2041795
  · exact B2041799
  · exact B2041803
  · exact B2041807
  · exact B2041811
  · exact B2041815
  · exact B2041819
  · exact B2041823
  · exact B2041827
  · exact B2041831
  · exact B2041835
  · exact B2041839
  · exact B2041843
  · exact B2041847
  · exact B2041851
  · exact B2041855
  · exact B2041859
  · exact B2041863
  · exact B2041867
  · exact B2041871
  · exact B2041875
  · exact B2041879
  · exact B2041883
  · exact B2041887
  · exact B2041891
  · exact B2041895
  · exact B2041899
  · exact B2041903
  · exact B2041907
  · exact B2041911
  · exact B2041915
  · exact B2041919
  · exact B2041923
  · exact B2041927
  · exact B2041931
  · exact B2041935
  · exact B2041939
  · exact B2041943
  · exact B2041947
  · exact B2041951
  · exact B2041955
  · exact B2041959
  · exact B2041963
  · exact B2041967
  · exact B2041971
  · exact B2041975
  · exact B2041979
  · exact B2041983
  · exact B2041987
  · exact B2041991
  · exact B2041995
  · exact B2041999
  · exact B2042003
  · exact B2042007
  · exact B2042011
  · exact B2042015
  · exact B2042019
  · exact B2042023
  · exact B2042027
  · exact B2042031
  · exact B2042035
  · exact B2042039
  · exact B2042043
  · exact B2042047
  · exact B2042051
  · exact B2042055
  · exact B2042059
  · exact B2042063
  · exact B2042067
  · exact B2042071
  · exact B2042075
  · exact B2042079
  · exact B2042083
  · exact B2042087
  · exact B2042091
  · exact B2042095
  · exact B2042099
  · exact B2042103
  · exact B2042107
  · exact B2042111
  · exact B2042115
  · exact B2042119
  · exact B2042123
  · exact B2042127
  · exact B2042131
  · exact B2042135
  · exact B2042139
  · exact B2042143
  · exact B2042147
  · exact B2042151
  · exact B2042155
  · exact B2042159
  · exact B2042163
  · exact B2042167
  · exact B2042171
  · exact B2042175
  · exact B2042179
  · exact B2042183
  · exact B2042187
  · exact B2042191
  · exact B2042195
  · exact B2042199
  · exact B2042203
  · exact B2042207
  · exact B2042211
  · exact B2042215
  · exact B2042219
  · exact B2042223
  · exact B2042227
  · exact B2042231
  · exact B2042235
  · exact B2042239
  · exact B2042243
  · exact B2042247
  · exact B2042251
  · exact B2042255
  · exact B2042259
  · exact B2042263
  · exact B2042267
  · exact B2042271
  · exact B2042275
  · exact B2042279
  · exact B2042283
  · exact B2042287
  · exact B2042291
  · exact B2042295
  · exact B2042299
  · exact B2042303
  · exact B2042307
  · exact B2042311
  · exact B2042315
  · exact B2042319
  · exact B2042323
  · exact B2042327
  · exact B2042331
  · exact B2042335
  · exact B2042339
  · exact B2042343
  · exact B2042347
  · exact B2042351
  · exact B2042355
  · exact B2042359
  · exact B2042363
  · exact B2042367
  · exact B2042371
  · exact B2042375
  · exact B2042379
  · exact B2042383
  · exact B2042387
  · exact B2042391
  · exact B2042395
  · exact B2042399
  · exact B2042403
  · exact B2042407
  · exact B2042411
  · exact B2042415
  · exact B2042419
  · exact B2042423
  · exact B2042427
  · exact B2042431
  · exact B2042435
  · exact B2042439
  · exact B2042443
  · exact B2042447
  · exact B2042451
  · exact B2042455
  · exact B2042459
  · exact B2042463
  · exact B2042467
  · exact B2042471
  · exact B2042475
  · exact B2042479
  · exact B2042483
  · exact B2042487
  · exact B2042491
  · exact B2042495
  · exact B2042499
  · exact B2042503
  · exact B2042507
  · exact B2042511
  · exact B2042515
  · exact B2042519
  · exact B2042523
  · exact B2042527
  · exact B2042531
  · exact B2042535
  · exact B2042539
  · exact B2042543
  · exact B2042547
  · exact B2042551
  · exact B2042555
  · exact B2042559
  · exact B2042563
  · exact B2042567
  · exact B2042571
  · exact B2042575
  · exact B2042579
  · exact B2042583
  · exact B2042587
  · exact B2042591
  · exact B2042595
  · exact B2042599
  · exact B2042603
  · exact B2042607
  · exact B2042611
  · exact B2042615
  · exact B2042619
  · exact B2042623
  · exact B2042627
  · exact B2042631
  · exact B2042635
  · exact B2042639
  · exact B2042643
  · exact B2042647
  · exact B2042651
  · exact B2042655
  · exact B2042659
  · exact B2042663
  · exact B2042667
  · exact B2042671
  · exact B2042675
  · exact B2042679
  · exact B2042683
  · exact B2042687
  · exact B2042691
  · exact B2042695
  · exact B2042699
  · exact B2042703
  · exact B2042707
  · exact B2042711
  · exact B2042715
  · exact B2042719
  · exact B2042723
  · exact B2042727
  · exact B2042731
  · exact B2042735
  · exact B2042739
  · exact B2042743
  · exact B2042747
  · exact B2042751
  · exact B2042755
  · exact B2042759
  · exact B2042763
  · exact B2042767
  · exact B2042771
  · exact B2042775
  · exact B2042779
  · exact B2042783
  · exact B2042787
  · exact B2042791
  · exact B2042795
  · exact B2042799
  · exact B2042803
  · exact B2042807
  · exact B2042811
  · exact B2042815
  · exact B2042819
  · exact B2042823
  · exact B2042827
  · exact B2042831
  · exact B2042835
  · exact B2042839
  · exact B2042843
  · exact B2042847
  · exact B2042851
  · exact B2042855
  · exact B2042859
  · exact B2042863
  · exact B2042867
  · exact B2042871
  · exact B2042875
  · exact B2042879
  · exact B2042883
  · exact B2042887
  · exact B2042891
  · exact B2042895
  · exact B2042899
  · exact B2042903
  · exact B2042907
  · exact B2042911
  · exact B2042915
  · exact B2042919
  · exact B2042923
  · exact B2042927
  · exact B2042931
  · exact B2042935
  · exact B2042939
  · exact B2042943
  · exact B2042947
  · exact B2042951
  · exact B2042955
  · exact B2042959
  · exact B2042963
  · exact B2042967
  · exact B2042971
  · exact B2042975
  · exact B2042979
  · exact B2042983
  · exact B2042987
  · exact B2042991
  · exact B2042995
  · exact B2042999
  · exact B2043003
  · exact B2043007
  · exact B2043011
  · exact B2043015
  · exact B2043019
  · exact B2043023
  · exact B2043027
  · exact B2043031
  · exact B2043035
  · exact B2043039
  · exact B2043043
  · exact B2043047
  · exact B2043051
  · exact B2043055
  · exact B2043059
  · exact B2043063
  · exact B2043067
  · exact B2043071
  · exact B2043075
  · exact B2043079
  · exact B2043083
  · exact B2043087
  · exact B2043091
  · exact B2043095
  · exact B2043099
  · exact B2043103
  · exact B2043107
  · exact B2043111
  · exact B2043115
  · exact B2043119
  · exact B2043123
  · exact B2043127
  · exact B2043131
  · exact B2043135
  · exact B2043139
  · exact B2043143
  · exact B2043147
  · exact B2043151
  · exact B2043155
  · exact B2043159
  · exact B2043163
  · exact B2043167
  · exact B2043171
  · exact B2043175
  · exact B2043179
  · exact B2043183
  · exact B2043187
  · exact B2043191
  · exact B2043195
  · exact B2043199
  · exact B2043203
  · exact B2043207
  · exact B2043211
  · exact B2043215
  · exact B2043219
  · exact B2043223
  · exact B2043227
  · exact B2043231
  · exact B2043235
  · exact B2043239
  · exact B2043243
  · exact B2043247
  · exact B2043251
  · exact B2043255
  · exact B2043259
  · exact B2043263
  · exact B2043267
  · exact B2043271
  · exact B2043275
  · exact B2043279
  · exact B2043283
  · exact B2043287
  · exact B2043291
  · exact B2043295
  · exact B2043299
  · exact B2043303
  · exact B2043307
  · exact B2043311
  · exact B2043315
  · exact B2043319
  · exact B2043323
  · exact B2043327
  · exact B2043331
  · exact B2043335
  · exact B2043339
  · exact B2043343
  · exact B2043347
  · exact B2043351
  · exact B2043355
  · exact B2043359
  · exact B2043363
  · exact B2043367
  · exact B2043371
  · exact B2043375
  · exact B2043379
  · exact B2043383
  · exact B2043387
  · exact B2043391
  · exact B2043395
  · exact B2043399
  · exact B2043403
  · exact B2043407
  · exact B2043411
  · exact B2043415
  · exact B2043419
  · exact B2043423
  · exact B2043427
  · exact B2043431
  · exact B2043435
theorem solution (m : ℕ) (hlo : 2041435 ≤ m) (hhi : m ≤ 2043435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 510358 ≤ j := by omega
    have hj2 : j ≤ 510858 := by omega
    have hb : Blo 2041435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
