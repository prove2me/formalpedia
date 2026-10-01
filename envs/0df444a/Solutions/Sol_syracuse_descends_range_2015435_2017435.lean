-- Prove2me | solution 1 for syracuse_descends_range_2015435_2017435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:46.853663+00:00
-- url     : https://prove2.me/submissions/68cc607e-c3d6-4691-8302-768654805de7

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

theorem B2267365 : Blo 2015435 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B3023153 : Blo 2015435 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B2015435 : Blo 2015435 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem B4304461 : Blo 2015435 4304461 := bbase (se 3 (by rfl) ⟨807086, by rfl⟩ : syracuseStep 4304461 = 1614173) (by norm_num)
theorem B5739281 : Blo 2015435 5739281 := bstep (se 2 (by rfl) ⟨2152230, by rfl⟩ : syracuseStep 5739281 = 4304461) B4304461
theorem B3826187 : Blo 2015435 3826187 := bstep (se 1 (by rfl) ⟨2869640, by rfl⟩ : syracuseStep 3826187 = 5739281) B5739281
theorem B2550791 : Blo 2015435 2550791 := bstep (se 1 (by rfl) ⟨1913093, by rfl⟩ : syracuseStep 2550791 = 3826187) B3826187
theorem B6802109 : Blo 2015435 6802109 := bstep (se 3 (by rfl) ⟨1275395, by rfl⟩ : syracuseStep 6802109 = 2550791) B2550791
theorem B4534739 : Blo 2015435 4534739 := bstep (se 1 (by rfl) ⟨3401054, by rfl⟩ : syracuseStep 4534739 = 6802109) B6802109
theorem B3023159 : Blo 2015435 3023159 := bstep (se 1 (by rfl) ⟨2267369, by rfl⟩ : syracuseStep 3023159 = 4534739) B4534739
theorem B2015439 : Blo 2015435 2015439 := bstep (se 1 (by rfl) ⟨1511579, by rfl⟩ : syracuseStep 2015439 = 3023159) B3023159
theorem B3023165 : Blo 2015435 3023165 := bbase (se 3 (by rfl) ⟨566843, by rfl⟩ : syracuseStep 3023165 = 1133687) (by norm_num)
theorem B2015443 : Blo 2015435 2015443 := bstep (se 1 (by rfl) ⟨1511582, by rfl⟩ : syracuseStep 2015443 = 3023165) B3023165
theorem B4534757 : Blo 2015435 4534757 := bbase (se 4 (by rfl) ⟨425133, by rfl⟩ : syracuseStep 4534757 = 850267) (by norm_num)
theorem B3023171 : Blo 2015435 3023171 := bstep (se 1 (by rfl) ⟨2267378, by rfl⟩ : syracuseStep 3023171 = 4534757) B4534757
theorem B2015447 : Blo 2015435 2015447 := bstep (se 1 (by rfl) ⟨1511585, by rfl⟩ : syracuseStep 2015447 = 3023171) B3023171
theorem B5101613 : Blo 2015435 5101613 := bbase (se 3 (by rfl) ⟨956552, by rfl⟩ : syracuseStep 5101613 = 1913105) (by norm_num)
theorem B3401075 : Blo 2015435 3401075 := bstep (se 1 (by rfl) ⟨2550806, by rfl⟩ : syracuseStep 3401075 = 5101613) B5101613
theorem B2267383 : Blo 2015435 2267383 := bstep (se 1 (by rfl) ⟨1700537, by rfl⟩ : syracuseStep 2267383 = 3401075) B3401075
theorem B3023177 : Blo 2015435 3023177 := bstep (se 2 (by rfl) ⟨1133691, by rfl⟩ : syracuseStep 3023177 = 2267383) B2267383
theorem B2015451 : Blo 2015435 2015451 := bstep (se 1 (by rfl) ⟨1511588, by rfl⟩ : syracuseStep 2015451 = 3023177) B3023177
theorem B6544837 : Blo 2015435 6544837 := bbase (se 4 (by rfl) ⟨613578, by rfl⟩ : syracuseStep 6544837 = 1227157) (by norm_num)
theorem B8726449 : Blo 2015435 8726449 := bstep (se 2 (by rfl) ⟨3272418, by rfl⟩ : syracuseStep 8726449 = 6544837) B6544837
theorem B11635265 : Blo 2015435 11635265 := bstep (se 2 (by rfl) ⟨4363224, by rfl⟩ : syracuseStep 11635265 = 8726449) B8726449
theorem B7756843 : Blo 2015435 7756843 := bstep (se 1 (by rfl) ⟨5817632, by rfl⟩ : syracuseStep 7756843 = 11635265) B11635265
theorem B10342457 : Blo 2015435 10342457 := bstep (se 2 (by rfl) ⟨3878421, by rfl⟩ : syracuseStep 10342457 = 7756843) B7756843
theorem B6894971 : Blo 2015435 6894971 := bstep (se 1 (by rfl) ⟨5171228, by rfl⟩ : syracuseStep 6894971 = 10342457) B10342457
theorem B4596647 : Blo 2015435 4596647 := bstep (se 1 (by rfl) ⟨3447485, by rfl⟩ : syracuseStep 4596647 = 6894971) B6894971
theorem B12257725 : Blo 2015435 12257725 := bstep (se 3 (by rfl) ⟨2298323, by rfl⟩ : syracuseStep 12257725 = 4596647) B4596647
theorem B16343633 : Blo 2015435 16343633 := bstep (se 2 (by rfl) ⟨6128862, by rfl⟩ : syracuseStep 16343633 = 12257725) B12257725
theorem B10895755 : Blo 2015435 10895755 := bstep (se 1 (by rfl) ⟨8171816, by rfl⟩ : syracuseStep 10895755 = 16343633) B16343633
theorem B14527673 : Blo 2015435 14527673 := bstep (se 2 (by rfl) ⟨5447877, by rfl⟩ : syracuseStep 14527673 = 10895755) B10895755
theorem B9685115 : Blo 2015435 9685115 := bstep (se 1 (by rfl) ⟨7263836, by rfl⟩ : syracuseStep 9685115 = 14527673) B14527673
theorem B6456743 : Blo 2015435 6456743 := bstep (se 1 (by rfl) ⟨4842557, by rfl⟩ : syracuseStep 6456743 = 9685115) B9685115
theorem B4304495 : Blo 2015435 4304495 := bstep (se 1 (by rfl) ⟨3228371, by rfl⟩ : syracuseStep 4304495 = 6456743) B6456743
theorem B2869663 : Blo 2015435 2869663 := bstep (se 1 (by rfl) ⟨2152247, by rfl⟩ : syracuseStep 2869663 = 4304495) B4304495
theorem B3826217 : Blo 2015435 3826217 := bstep (se 2 (by rfl) ⟨1434831, by rfl⟩ : syracuseStep 3826217 = 2869663) B2869663
theorem B10203245 : Blo 2015435 10203245 := bstep (se 3 (by rfl) ⟨1913108, by rfl⟩ : syracuseStep 10203245 = 3826217) B3826217
theorem B6802163 : Blo 2015435 6802163 := bstep (se 1 (by rfl) ⟨5101622, by rfl⟩ : syracuseStep 6802163 = 10203245) B10203245
theorem B4534775 : Blo 2015435 4534775 := bstep (se 1 (by rfl) ⟨3401081, by rfl⟩ : syracuseStep 4534775 = 6802163) B6802163
theorem B3023183 : Blo 2015435 3023183 := bstep (se 1 (by rfl) ⟨2267387, by rfl⟩ : syracuseStep 3023183 = 4534775) B4534775
theorem B2015455 : Blo 2015435 2015455 := bstep (se 1 (by rfl) ⟨1511591, by rfl⟩ : syracuseStep 2015455 = 3023183) B3023183
theorem B3023189 : Blo 2015435 3023189 := bbase (se 10 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 3023189 = 8857) (by norm_num)
theorem B2015459 : Blo 2015435 2015459 := bstep (se 1 (by rfl) ⟨1511594, by rfl⟩ : syracuseStep 2015459 = 3023189) B3023189
theorem B5739349 : Blo 2015435 5739349 := bbase (se 9 (by rfl) ⟨16814, by rfl⟩ : syracuseStep 5739349 = 33629) (by norm_num)
theorem B7652465 : Blo 2015435 7652465 := bstep (se 2 (by rfl) ⟨2869674, by rfl⟩ : syracuseStep 7652465 = 5739349) B5739349
theorem B5101643 : Blo 2015435 5101643 := bstep (se 1 (by rfl) ⟨3826232, by rfl⟩ : syracuseStep 5101643 = 7652465) B7652465
theorem B3401095 : Blo 2015435 3401095 := bstep (se 1 (by rfl) ⟨2550821, by rfl⟩ : syracuseStep 3401095 = 5101643) B5101643
theorem B4534793 : Blo 2015435 4534793 := bstep (se 2 (by rfl) ⟨1700547, by rfl⟩ : syracuseStep 4534793 = 3401095) B3401095
theorem B3023195 : Blo 2015435 3023195 := bstep (se 1 (by rfl) ⟨2267396, by rfl⟩ : syracuseStep 3023195 = 4534793) B4534793
theorem B2015463 : Blo 2015435 2015463 := bstep (se 1 (by rfl) ⟨1511597, by rfl⟩ : syracuseStep 2015463 = 3023195) B3023195
theorem B2267401 : Blo 2015435 2267401 := bbase (se 2 (by rfl) ⟨850275, by rfl⟩ : syracuseStep 2267401 = 1700551) (by norm_num)
theorem B3023201 : Blo 2015435 3023201 := bstep (se 2 (by rfl) ⟨1133700, by rfl⟩ : syracuseStep 3023201 = 2267401) B2267401
theorem B2015467 : Blo 2015435 2015467 := bstep (se 1 (by rfl) ⟨1511600, by rfl⟩ : syracuseStep 2015467 = 3023201) B3023201
theorem B7263893 : Blo 2015435 7263893 := bbase (se 6 (by rfl) ⟨170247, by rfl⟩ : syracuseStep 7263893 = 340495) (by norm_num)
theorem B4842595 : Blo 2015435 4842595 := bstep (se 1 (by rfl) ⟨3631946, by rfl⟩ : syracuseStep 4842595 = 7263893) B7263893
theorem B25827173 : Blo 2015435 25827173 := bstep (se 4 (by rfl) ⟨2421297, by rfl⟩ : syracuseStep 25827173 = 4842595) B4842595
theorem B17218115 : Blo 2015435 17218115 := bstep (se 1 (by rfl) ⟨12913586, by rfl⟩ : syracuseStep 17218115 = 25827173) B25827173
theorem B11478743 : Blo 2015435 11478743 := bstep (se 1 (by rfl) ⟨8609057, by rfl⟩ : syracuseStep 11478743 = 17218115) B17218115
theorem B7652495 : Blo 2015435 7652495 := bstep (se 1 (by rfl) ⟨5739371, by rfl⟩ : syracuseStep 7652495 = 11478743) B11478743
theorem B5101663 : Blo 2015435 5101663 := bstep (se 1 (by rfl) ⟨3826247, by rfl⟩ : syracuseStep 5101663 = 7652495) B7652495
theorem B6802217 : Blo 2015435 6802217 := bstep (se 2 (by rfl) ⟨2550831, by rfl⟩ : syracuseStep 6802217 = 5101663) B5101663
theorem B4534811 : Blo 2015435 4534811 := bstep (se 1 (by rfl) ⟨3401108, by rfl⟩ : syracuseStep 4534811 = 6802217) B6802217
theorem B3023207 : Blo 2015435 3023207 := bstep (se 1 (by rfl) ⟨2267405, by rfl⟩ : syracuseStep 3023207 = 4534811) B4534811
theorem B2015471 : Blo 2015435 2015471 := bstep (se 1 (by rfl) ⟨1511603, by rfl⟩ : syracuseStep 2015471 = 3023207) B3023207
theorem B3023213 : Blo 2015435 3023213 := bbase (se 3 (by rfl) ⟨566852, by rfl⟩ : syracuseStep 3023213 = 1133705) (by norm_num)
theorem B2015475 : Blo 2015435 2015475 := bstep (se 1 (by rfl) ⟨1511606, by rfl⟩ : syracuseStep 2015475 = 3023213) B3023213
theorem B4534829 : Blo 2015435 4534829 := bbase (se 3 (by rfl) ⟨850280, by rfl⟩ : syracuseStep 4534829 = 1700561) (by norm_num)
theorem B3023219 : Blo 2015435 3023219 := bstep (se 1 (by rfl) ⟨2267414, by rfl⟩ : syracuseStep 3023219 = 4534829) B4534829
theorem B2015479 : Blo 2015435 2015479 := bstep (se 1 (by rfl) ⟨1511609, by rfl⟩ : syracuseStep 2015479 = 3023219) B3023219
theorem B18637717 : Blo 2015435 18637717 := bbase (se 6 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 18637717 = 873643) (by norm_num)
theorem B24850289 : Blo 2015435 24850289 := bstep (se 2 (by rfl) ⟨9318858, by rfl⟩ : syracuseStep 24850289 = 18637717) B18637717
theorem B16566859 : Blo 2015435 16566859 := bstep (se 1 (by rfl) ⟨12425144, by rfl⟩ : syracuseStep 16566859 = 24850289) B24850289
theorem B22089145 : Blo 2015435 22089145 := bstep (se 2 (by rfl) ⟨8283429, by rfl⟩ : syracuseStep 22089145 = 16566859) B16566859
theorem B29452193 : Blo 2015435 29452193 := bstep (se 2 (by rfl) ⟨11044572, by rfl⟩ : syracuseStep 29452193 = 22089145) B22089145
theorem B19634795 : Blo 2015435 19634795 := bstep (se 1 (by rfl) ⟨14726096, by rfl⟩ : syracuseStep 19634795 = 29452193) B29452193
theorem B13089863 : Blo 2015435 13089863 := bstep (se 1 (by rfl) ⟨9817397, by rfl⟩ : syracuseStep 13089863 = 19634795) B19634795
theorem B8726575 : Blo 2015435 8726575 := bstep (se 1 (by rfl) ⟨6544931, by rfl⟩ : syracuseStep 8726575 = 13089863) B13089863
theorem B11635433 : Blo 2015435 11635433 := bstep (se 2 (by rfl) ⟨4363287, by rfl⟩ : syracuseStep 11635433 = 8726575) B8726575
theorem B7756955 : Blo 2015435 7756955 := bstep (se 1 (by rfl) ⟨5817716, by rfl⟩ : syracuseStep 7756955 = 11635433) B11635433
theorem B5171303 : Blo 2015435 5171303 := bstep (se 1 (by rfl) ⟨3878477, by rfl⟩ : syracuseStep 5171303 = 7756955) B7756955
theorem B3447535 : Blo 2015435 3447535 := bstep (se 1 (by rfl) ⟨2585651, by rfl⟩ : syracuseStep 3447535 = 5171303) B5171303
theorem B4596713 : Blo 2015435 4596713 := bstep (se 2 (by rfl) ⟨1723767, by rfl⟩ : syracuseStep 4596713 = 3447535) B3447535
theorem B3064475 : Blo 2015435 3064475 := bstep (se 1 (by rfl) ⟨2298356, by rfl⟩ : syracuseStep 3064475 = 4596713) B4596713
theorem B2042983 : Blo 2015435 2042983 := bstep (se 1 (by rfl) ⟨1532237, by rfl⟩ : syracuseStep 2042983 = 3064475) B3064475
theorem B2723977 : Blo 2015435 2723977 := bstep (se 2 (by rfl) ⟨1021491, by rfl⟩ : syracuseStep 2723977 = 2042983) B2042983
theorem B3631969 : Blo 2015435 3631969 := bstep (se 2 (by rfl) ⟨1361988, by rfl⟩ : syracuseStep 3631969 = 2723977) B2723977
theorem B19370501 : Blo 2015435 19370501 := bstep (se 4 (by rfl) ⟨1815984, by rfl⟩ : syracuseStep 19370501 = 3631969) B3631969
theorem B12913667 : Blo 2015435 12913667 := bstep (se 1 (by rfl) ⟨9685250, by rfl⟩ : syracuseStep 12913667 = 19370501) B19370501
theorem B8609111 : Blo 2015435 8609111 := bstep (se 1 (by rfl) ⟨6456833, by rfl⟩ : syracuseStep 8609111 = 12913667) B12913667
theorem B5739407 : Blo 2015435 5739407 := bstep (se 1 (by rfl) ⟨4304555, by rfl⟩ : syracuseStep 5739407 = 8609111) B8609111
theorem B3826271 : Blo 2015435 3826271 := bstep (se 1 (by rfl) ⟨2869703, by rfl⟩ : syracuseStep 3826271 = 5739407) B5739407
theorem B2550847 : Blo 2015435 2550847 := bstep (se 1 (by rfl) ⟨1913135, by rfl⟩ : syracuseStep 2550847 = 3826271) B3826271
theorem B3401129 : Blo 2015435 3401129 := bstep (se 2 (by rfl) ⟨1275423, by rfl⟩ : syracuseStep 3401129 = 2550847) B2550847
theorem B2267419 : Blo 2015435 2267419 := bstep (se 1 (by rfl) ⟨1700564, by rfl⟩ : syracuseStep 2267419 = 3401129) B3401129
theorem B3023225 : Blo 2015435 3023225 := bstep (se 2 (by rfl) ⟨1133709, by rfl⟩ : syracuseStep 3023225 = 2267419) B2267419
theorem B2015483 : Blo 2015435 2015483 := bstep (se 1 (by rfl) ⟨1511612, by rfl⟩ : syracuseStep 2015483 = 3023225) B3023225
theorem B34436501 : Blo 2015435 34436501 := bbase (se 6 (by rfl) ⟨807105, by rfl⟩ : syracuseStep 34436501 = 1614211) (by norm_num)
theorem B22957667 : Blo 2015435 22957667 := bstep (se 1 (by rfl) ⟨17218250, by rfl⟩ : syracuseStep 22957667 = 34436501) B34436501
theorem B15305111 : Blo 2015435 15305111 := bstep (se 1 (by rfl) ⟨11478833, by rfl⟩ : syracuseStep 15305111 = 22957667) B22957667
theorem B10203407 : Blo 2015435 10203407 := bstep (se 1 (by rfl) ⟨7652555, by rfl⟩ : syracuseStep 10203407 = 15305111) B15305111
theorem B6802271 : Blo 2015435 6802271 := bstep (se 1 (by rfl) ⟨5101703, by rfl⟩ : syracuseStep 6802271 = 10203407) B10203407
theorem B4534847 : Blo 2015435 4534847 := bstep (se 1 (by rfl) ⟨3401135, by rfl⟩ : syracuseStep 4534847 = 6802271) B6802271
theorem B3023231 : Blo 2015435 3023231 := bstep (se 1 (by rfl) ⟨2267423, by rfl⟩ : syracuseStep 3023231 = 4534847) B4534847
theorem B2015487 : Blo 2015435 2015487 := bstep (se 1 (by rfl) ⟨1511615, by rfl⟩ : syracuseStep 2015487 = 3023231) B3023231
theorem B3023237 : Blo 2015435 3023237 := bbase (se 4 (by rfl) ⟨283428, by rfl⟩ : syracuseStep 3023237 = 566857) (by norm_num)
theorem B2015491 : Blo 2015435 2015491 := bstep (se 1 (by rfl) ⟨1511618, by rfl⟩ : syracuseStep 2015491 = 3023237) B3023237
theorem B3401149 : Blo 2015435 3401149 := bbase (se 3 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 3401149 = 1275431) (by norm_num)
theorem B4534865 : Blo 2015435 4534865 := bstep (se 2 (by rfl) ⟨1700574, by rfl⟩ : syracuseStep 4534865 = 3401149) B3401149
theorem B3023243 : Blo 2015435 3023243 := bstep (se 1 (by rfl) ⟨2267432, by rfl⟩ : syracuseStep 3023243 = 4534865) B4534865
theorem B2015495 : Blo 2015435 2015495 := bstep (se 1 (by rfl) ⟨1511621, by rfl⟩ : syracuseStep 2015495 = 3023243) B3023243
theorem B2267437 : Blo 2015435 2267437 := bbase (se 3 (by rfl) ⟨425144, by rfl⟩ : syracuseStep 2267437 = 850289) (by norm_num)
theorem B3023249 : Blo 2015435 3023249 := bstep (se 2 (by rfl) ⟨1133718, by rfl⟩ : syracuseStep 3023249 = 2267437) B2267437
theorem B2015499 : Blo 2015435 2015499 := bstep (se 1 (by rfl) ⟨1511624, by rfl⟩ : syracuseStep 2015499 = 3023249) B3023249
theorem B6802325 : Blo 2015435 6802325 := bbase (se 6 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 6802325 = 318859) (by norm_num)
theorem B4534883 : Blo 2015435 4534883 := bstep (se 1 (by rfl) ⟨3401162, by rfl⟩ : syracuseStep 4534883 = 6802325) B6802325
theorem B3023255 : Blo 2015435 3023255 := bstep (se 1 (by rfl) ⟨2267441, by rfl⟩ : syracuseStep 3023255 = 4534883) B4534883
theorem B2015503 : Blo 2015435 2015503 := bstep (se 1 (by rfl) ⟨1511627, by rfl⟩ : syracuseStep 2015503 = 3023255) B3023255
theorem B3023261 : Blo 2015435 3023261 := bbase (se 3 (by rfl) ⟨566861, by rfl⟩ : syracuseStep 3023261 = 1133723) (by norm_num)
theorem B2015507 : Blo 2015435 2015507 := bstep (se 1 (by rfl) ⟨1511630, by rfl⟩ : syracuseStep 2015507 = 3023261) B3023261
theorem B4534901 : Blo 2015435 4534901 := bbase (se 5 (by rfl) ⟨212573, by rfl⟩ : syracuseStep 4534901 = 425147) (by norm_num)
theorem B3023267 : Blo 2015435 3023267 := bstep (se 1 (by rfl) ⟨2267450, by rfl⟩ : syracuseStep 3023267 = 4534901) B4534901
theorem B2015511 : Blo 2015435 2015511 := bstep (se 1 (by rfl) ⟨1511633, by rfl⟩ : syracuseStep 2015511 = 3023267) B3023267
theorem B4908773 : Blo 2015435 4908773 := bbase (se 4 (by rfl) ⟨460197, by rfl⟩ : syracuseStep 4908773 = 920395) (by norm_num)
theorem B13090061 : Blo 2015435 13090061 := bstep (se 3 (by rfl) ⟨2454386, by rfl⟩ : syracuseStep 13090061 = 4908773) B4908773
theorem B8726707 : Blo 2015435 8726707 := bstep (se 1 (by rfl) ⟨6545030, by rfl⟩ : syracuseStep 8726707 = 13090061) B13090061
theorem B46542437 : Blo 2015435 46542437 := bstep (se 4 (by rfl) ⟨4363353, by rfl⟩ : syracuseStep 46542437 = 8726707) B8726707
theorem B31028291 : Blo 2015435 31028291 := bstep (se 1 (by rfl) ⟨23271218, by rfl⟩ : syracuseStep 31028291 = 46542437) B46542437
theorem B20685527 : Blo 2015435 20685527 := bstep (se 1 (by rfl) ⟨15514145, by rfl⟩ : syracuseStep 20685527 = 31028291) B31028291
theorem B13790351 : Blo 2015435 13790351 := bstep (se 1 (by rfl) ⟨10342763, by rfl⟩ : syracuseStep 13790351 = 20685527) B20685527
theorem B36774269 : Blo 2015435 36774269 := bstep (se 3 (by rfl) ⟨6895175, by rfl⟩ : syracuseStep 36774269 = 13790351) B13790351
theorem B24516179 : Blo 2015435 24516179 := bstep (se 1 (by rfl) ⟨18387134, by rfl⟩ : syracuseStep 24516179 = 36774269) B36774269
theorem B16344119 : Blo 2015435 16344119 := bstep (se 1 (by rfl) ⟨12258089, by rfl⟩ : syracuseStep 16344119 = 24516179) B24516179
theorem B10896079 : Blo 2015435 10896079 := bstep (se 1 (by rfl) ⟨8172059, by rfl⟩ : syracuseStep 10896079 = 16344119) B16344119
theorem B14528105 : Blo 2015435 14528105 := bstep (se 2 (by rfl) ⟨5448039, by rfl⟩ : syracuseStep 14528105 = 10896079) B10896079
theorem B9685403 : Blo 2015435 9685403 := bstep (se 1 (by rfl) ⟨7264052, by rfl⟩ : syracuseStep 9685403 = 14528105) B14528105
theorem B6456935 : Blo 2015435 6456935 := bstep (se 1 (by rfl) ⟨4842701, by rfl⟩ : syracuseStep 6456935 = 9685403) B9685403
theorem B17218493 : Blo 2015435 17218493 := bstep (se 3 (by rfl) ⟨3228467, by rfl⟩ : syracuseStep 17218493 = 6456935) B6456935
theorem B11478995 : Blo 2015435 11478995 := bstep (se 1 (by rfl) ⟨8609246, by rfl⟩ : syracuseStep 11478995 = 17218493) B17218493
theorem B7652663 : Blo 2015435 7652663 := bstep (se 1 (by rfl) ⟨5739497, by rfl⟩ : syracuseStep 7652663 = 11478995) B11478995
theorem B5101775 : Blo 2015435 5101775 := bstep (se 1 (by rfl) ⟨3826331, by rfl⟩ : syracuseStep 5101775 = 7652663) B7652663
theorem B3401183 : Blo 2015435 3401183 := bstep (se 1 (by rfl) ⟨2550887, by rfl⟩ : syracuseStep 3401183 = 5101775) B5101775
theorem B2267455 : Blo 2015435 2267455 := bstep (se 1 (by rfl) ⟨1700591, by rfl⟩ : syracuseStep 2267455 = 3401183) B3401183
theorem B3023273 : Blo 2015435 3023273 := bstep (se 2 (by rfl) ⟨1133727, by rfl⟩ : syracuseStep 3023273 = 2267455) B2267455
theorem B2015515 : Blo 2015435 2015515 := bstep (se 1 (by rfl) ⟨1511636, by rfl⟩ : syracuseStep 2015515 = 3023273) B3023273
theorem B7652677 : Blo 2015435 7652677 := bbase (se 4 (by rfl) ⟨717438, by rfl⟩ : syracuseStep 7652677 = 1434877) (by norm_num)
theorem B10203569 : Blo 2015435 10203569 := bstep (se 2 (by rfl) ⟨3826338, by rfl⟩ : syracuseStep 10203569 = 7652677) B7652677
theorem B6802379 : Blo 2015435 6802379 := bstep (se 1 (by rfl) ⟨5101784, by rfl⟩ : syracuseStep 6802379 = 10203569) B10203569
theorem B4534919 : Blo 2015435 4534919 := bstep (se 1 (by rfl) ⟨3401189, by rfl⟩ : syracuseStep 4534919 = 6802379) B6802379
theorem B3023279 : Blo 2015435 3023279 := bstep (se 1 (by rfl) ⟨2267459, by rfl⟩ : syracuseStep 3023279 = 4534919) B4534919
theorem B2015519 : Blo 2015435 2015519 := bstep (se 1 (by rfl) ⟨1511639, by rfl⟩ : syracuseStep 2015519 = 3023279) B3023279
theorem B3023285 : Blo 2015435 3023285 := bbase (se 5 (by rfl) ⟨141716, by rfl⟩ : syracuseStep 3023285 = 283433) (by norm_num)
theorem B2015523 : Blo 2015435 2015523 := bstep (se 1 (by rfl) ⟨1511642, by rfl⟩ : syracuseStep 2015523 = 3023285) B3023285
theorem B5101805 : Blo 2015435 5101805 := bbase (se 3 (by rfl) ⟨956588, by rfl⟩ : syracuseStep 5101805 = 1913177) (by norm_num)
theorem B3401203 : Blo 2015435 3401203 := bstep (se 1 (by rfl) ⟨2550902, by rfl⟩ : syracuseStep 3401203 = 5101805) B5101805
theorem B4534937 : Blo 2015435 4534937 := bstep (se 2 (by rfl) ⟨1700601, by rfl⟩ : syracuseStep 4534937 = 3401203) B3401203
theorem B3023291 : Blo 2015435 3023291 := bstep (se 1 (by rfl) ⟨2267468, by rfl⟩ : syracuseStep 3023291 = 4534937) B4534937
theorem B2015527 : Blo 2015435 2015527 := bstep (se 1 (by rfl) ⟨1511645, by rfl⟩ : syracuseStep 2015527 = 3023291) B3023291
theorem B2267473 : Blo 2015435 2267473 := bbase (se 2 (by rfl) ⟨850302, by rfl⟩ : syracuseStep 2267473 = 1700605) (by norm_num)
theorem B3023297 : Blo 2015435 3023297 := bstep (se 2 (by rfl) ⟨1133736, by rfl⟩ : syracuseStep 3023297 = 2267473) B2267473
theorem B2015531 : Blo 2015435 2015531 := bstep (se 1 (by rfl) ⟨1511648, by rfl⟩ : syracuseStep 2015531 = 3023297) B3023297
theorem B2152333 : Blo 2015435 2152333 := bbase (se 3 (by rfl) ⟨403562, by rfl⟩ : syracuseStep 2152333 = 807125) (by norm_num)
theorem B2869777 : Blo 2015435 2869777 := bstep (se 2 (by rfl) ⟨1076166, by rfl⟩ : syracuseStep 2869777 = 2152333) B2152333
theorem B3826369 : Blo 2015435 3826369 := bstep (se 2 (by rfl) ⟨1434888, by rfl⟩ : syracuseStep 3826369 = 2869777) B2869777
theorem B5101825 : Blo 2015435 5101825 := bstep (se 2 (by rfl) ⟨1913184, by rfl⟩ : syracuseStep 5101825 = 3826369) B3826369
theorem B6802433 : Blo 2015435 6802433 := bstep (se 2 (by rfl) ⟨2550912, by rfl⟩ : syracuseStep 6802433 = 5101825) B5101825
theorem B4534955 : Blo 2015435 4534955 := bstep (se 1 (by rfl) ⟨3401216, by rfl⟩ : syracuseStep 4534955 = 6802433) B6802433
theorem B3023303 : Blo 2015435 3023303 := bstep (se 1 (by rfl) ⟨2267477, by rfl⟩ : syracuseStep 3023303 = 4534955) B4534955
theorem B2015535 : Blo 2015435 2015535 := bstep (se 1 (by rfl) ⟨1511651, by rfl⟩ : syracuseStep 2015535 = 3023303) B3023303
theorem B3023309 : Blo 2015435 3023309 := bbase (se 3 (by rfl) ⟨566870, by rfl⟩ : syracuseStep 3023309 = 1133741) (by norm_num)
theorem B2015539 : Blo 2015435 2015539 := bstep (se 1 (by rfl) ⟨1511654, by rfl⟩ : syracuseStep 2015539 = 3023309) B3023309
theorem B4534973 : Blo 2015435 4534973 := bbase (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) (by norm_num)
theorem B3023315 : Blo 2015435 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B2015543 : Blo 2015435 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B3401237 : Blo 2015435 3401237 := bbase (se 6 (by rfl) ⟨79716, by rfl⟩ : syracuseStep 3401237 = 159433) (by norm_num)
theorem B2267491 : Blo 2015435 2267491 := bstep (se 1 (by rfl) ⟨1700618, by rfl⟩ : syracuseStep 2267491 = 3401237) B3401237
theorem B3023321 : Blo 2015435 3023321 := bstep (se 2 (by rfl) ⟨1133745, by rfl⟩ : syracuseStep 3023321 = 2267491) B2267491
theorem B2015547 : Blo 2015435 2015547 := bstep (se 1 (by rfl) ⟨1511660, by rfl⟩ : syracuseStep 2015547 = 3023321) B3023321
theorem B7264181 : Blo 2015435 7264181 := bbase (se 5 (by rfl) ⟨340508, by rfl⟩ : syracuseStep 7264181 = 681017) (by norm_num)
theorem B19371149 : Blo 2015435 19371149 := bstep (se 3 (by rfl) ⟨3632090, by rfl⟩ : syracuseStep 19371149 = 7264181) B7264181
theorem B12914099 : Blo 2015435 12914099 := bstep (se 1 (by rfl) ⟨9685574, by rfl⟩ : syracuseStep 12914099 = 19371149) B19371149
theorem B8609399 : Blo 2015435 8609399 := bstep (se 1 (by rfl) ⟨6457049, by rfl⟩ : syracuseStep 8609399 = 12914099) B12914099
theorem B5739599 : Blo 2015435 5739599 := bstep (se 1 (by rfl) ⟨4304699, by rfl⟩ : syracuseStep 5739599 = 8609399) B8609399
theorem B15305597 : Blo 2015435 15305597 := bstep (se 3 (by rfl) ⟨2869799, by rfl⟩ : syracuseStep 15305597 = 5739599) B5739599
theorem B10203731 : Blo 2015435 10203731 := bstep (se 1 (by rfl) ⟨7652798, by rfl⟩ : syracuseStep 10203731 = 15305597) B15305597
theorem B6802487 : Blo 2015435 6802487 := bstep (se 1 (by rfl) ⟨5101865, by rfl⟩ : syracuseStep 6802487 = 10203731) B10203731
theorem B4534991 : Blo 2015435 4534991 := bstep (se 1 (by rfl) ⟨3401243, by rfl⟩ : syracuseStep 4534991 = 6802487) B6802487
theorem B3023327 : Blo 2015435 3023327 := bstep (se 1 (by rfl) ⟨2267495, by rfl⟩ : syracuseStep 3023327 = 4534991) B4534991
theorem B2015551 : Blo 2015435 2015551 := bstep (se 1 (by rfl) ⟨1511663, by rfl⟩ : syracuseStep 2015551 = 3023327) B3023327
theorem B3023333 : Blo 2015435 3023333 := bbase (se 4 (by rfl) ⟨283437, by rfl⟩ : syracuseStep 3023333 = 566875) (by norm_num)
theorem B2015555 : Blo 2015435 2015555 := bstep (se 1 (by rfl) ⟨1511666, by rfl⟩ : syracuseStep 2015555 = 3023333) B3023333
theorem B3494701 : Blo 2015435 3494701 := bbase (se 3 (by rfl) ⟨655256, by rfl⟩ : syracuseStep 3494701 = 1310513) (by norm_num)
theorem B18638405 : Blo 2015435 18638405 := bstep (se 4 (by rfl) ⟨1747350, by rfl⟩ : syracuseStep 18638405 = 3494701) B3494701
theorem B12425603 : Blo 2015435 12425603 := bstep (se 1 (by rfl) ⟨9319202, by rfl⟩ : syracuseStep 12425603 = 18638405) B18638405
theorem B33134941 : Blo 2015435 33134941 := bstep (se 3 (by rfl) ⟨6212801, by rfl⟩ : syracuseStep 33134941 = 12425603) B12425603
theorem B44179921 : Blo 2015435 44179921 := bstep (se 2 (by rfl) ⟨16567470, by rfl⟩ : syracuseStep 44179921 = 33134941) B33134941
theorem B58906561 : Blo 2015435 58906561 := bstep (se 2 (by rfl) ⟨22089960, by rfl⟩ : syracuseStep 58906561 = 44179921) B44179921
theorem B78542081 : Blo 2015435 78542081 := bstep (se 2 (by rfl) ⟨29453280, by rfl⟩ : syracuseStep 78542081 = 58906561) B58906561
theorem B52361387 : Blo 2015435 52361387 := bstep (se 1 (by rfl) ⟨39271040, by rfl⟩ : syracuseStep 52361387 = 78542081) B78542081
theorem B34907591 : Blo 2015435 34907591 := bstep (se 1 (by rfl) ⟨26180693, by rfl⟩ : syracuseStep 34907591 = 52361387) B52361387
theorem B23271727 : Blo 2015435 23271727 := bstep (se 1 (by rfl) ⟨17453795, by rfl⟩ : syracuseStep 23271727 = 34907591) B34907591
theorem B31028969 : Blo 2015435 31028969 := bstep (se 2 (by rfl) ⟨11635863, by rfl⟩ : syracuseStep 31028969 = 23271727) B23271727
theorem B20685979 : Blo 2015435 20685979 := bstep (se 1 (by rfl) ⟨15514484, by rfl⟩ : syracuseStep 20685979 = 31028969) B31028969
theorem B27581305 : Blo 2015435 27581305 := bstep (se 2 (by rfl) ⟨10342989, by rfl⟩ : syracuseStep 27581305 = 20685979) B20685979
theorem B36775073 : Blo 2015435 36775073 := bstep (se 2 (by rfl) ⟨13790652, by rfl⟩ : syracuseStep 36775073 = 27581305) B27581305
theorem B24516715 : Blo 2015435 24516715 := bstep (se 1 (by rfl) ⟨18387536, by rfl⟩ : syracuseStep 24516715 = 36775073) B36775073
theorem B32688953 : Blo 2015435 32688953 := bstep (se 2 (by rfl) ⟨12258357, by rfl⟩ : syracuseStep 32688953 = 24516715) B24516715
theorem B21792635 : Blo 2015435 21792635 := bstep (se 1 (by rfl) ⟨16344476, by rfl⟩ : syracuseStep 21792635 = 32688953) B32688953
theorem B14528423 : Blo 2015435 14528423 := bstep (se 1 (by rfl) ⟨10896317, by rfl⟩ : syracuseStep 14528423 = 21792635) B21792635
theorem B9685615 : Blo 2015435 9685615 := bstep (se 1 (by rfl) ⟨7264211, by rfl⟩ : syracuseStep 9685615 = 14528423) B14528423
theorem B12914153 : Blo 2015435 12914153 := bstep (se 2 (by rfl) ⟨4842807, by rfl⟩ : syracuseStep 12914153 = 9685615) B9685615
theorem B8609435 : Blo 2015435 8609435 := bstep (se 1 (by rfl) ⟨6457076, by rfl⟩ : syracuseStep 8609435 = 12914153) B12914153
theorem B5739623 : Blo 2015435 5739623 := bstep (se 1 (by rfl) ⟨4304717, by rfl⟩ : syracuseStep 5739623 = 8609435) B8609435
theorem B3826415 : Blo 2015435 3826415 := bstep (se 1 (by rfl) ⟨2869811, by rfl⟩ : syracuseStep 3826415 = 5739623) B5739623
theorem B2550943 : Blo 2015435 2550943 := bstep (se 1 (by rfl) ⟨1913207, by rfl⟩ : syracuseStep 2550943 = 3826415) B3826415
theorem B3401257 : Blo 2015435 3401257 := bstep (se 2 (by rfl) ⟨1275471, by rfl⟩ : syracuseStep 3401257 = 2550943) B2550943
theorem B4535009 : Blo 2015435 4535009 := bstep (se 2 (by rfl) ⟨1700628, by rfl⟩ : syracuseStep 4535009 = 3401257) B3401257
theorem B3023339 : Blo 2015435 3023339 := bstep (se 1 (by rfl) ⟨2267504, by rfl⟩ : syracuseStep 3023339 = 4535009) B4535009
theorem B2015559 : Blo 2015435 2015559 := bstep (se 1 (by rfl) ⟨1511669, by rfl⟩ : syracuseStep 2015559 = 3023339) B3023339
theorem B2267509 : Blo 2015435 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B3023345 : Blo 2015435 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B2015563 : Blo 2015435 2015563 := bstep (se 1 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 2015563 = 3023345) B3023345
theorem B2550953 : Blo 2015435 2550953 := bbase (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) (by norm_num)
theorem B6802541 : Blo 2015435 6802541 := bstep (se 3 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 6802541 = 2550953) B2550953
theorem B4535027 : Blo 2015435 4535027 := bstep (se 1 (by rfl) ⟨3401270, by rfl⟩ : syracuseStep 4535027 = 6802541) B6802541
theorem B3023351 : Blo 2015435 3023351 := bstep (se 1 (by rfl) ⟨2267513, by rfl⟩ : syracuseStep 3023351 = 4535027) B4535027
theorem B2015567 : Blo 2015435 2015567 := bstep (se 1 (by rfl) ⟨1511675, by rfl⟩ : syracuseStep 2015567 = 3023351) B3023351
theorem B3023357 : Blo 2015435 3023357 := bbase (se 3 (by rfl) ⟨566879, by rfl⟩ : syracuseStep 3023357 = 1133759) (by norm_num)
theorem B2015571 : Blo 2015435 2015571 := bstep (se 1 (by rfl) ⟨1511678, by rfl⟩ : syracuseStep 2015571 = 3023357) B3023357
theorem B4535045 : Blo 2015435 4535045 := bbase (se 4 (by rfl) ⟨425160, by rfl⟩ : syracuseStep 4535045 = 850321) (by norm_num)
theorem B3023363 : Blo 2015435 3023363 := bstep (se 1 (by rfl) ⟨2267522, by rfl⟩ : syracuseStep 3023363 = 4535045) B4535045
theorem B2015575 : Blo 2015435 2015575 := bstep (se 1 (by rfl) ⟨1511681, by rfl⟩ : syracuseStep 2015575 = 3023363) B3023363
theorem B3826453 : Blo 2015435 3826453 := bbase (se 6 (by rfl) ⟨89682, by rfl⟩ : syracuseStep 3826453 = 179365) (by norm_num)
theorem B5101937 : Blo 2015435 5101937 := bstep (se 2 (by rfl) ⟨1913226, by rfl⟩ : syracuseStep 5101937 = 3826453) B3826453
theorem B3401291 : Blo 2015435 3401291 := bstep (se 1 (by rfl) ⟨2550968, by rfl⟩ : syracuseStep 3401291 = 5101937) B5101937
theorem B2267527 : Blo 2015435 2267527 := bstep (se 1 (by rfl) ⟨1700645, by rfl⟩ : syracuseStep 2267527 = 3401291) B3401291
theorem B3023369 : Blo 2015435 3023369 := bstep (se 2 (by rfl) ⟨1133763, by rfl⟩ : syracuseStep 3023369 = 2267527) B2267527
theorem B2015579 : Blo 2015435 2015579 := bstep (se 1 (by rfl) ⟨1511684, by rfl⟩ : syracuseStep 2015579 = 3023369) B3023369
theorem B10203893 : Blo 2015435 10203893 := bbase (se 5 (by rfl) ⟨478307, by rfl⟩ : syracuseStep 10203893 = 956615) (by norm_num)
theorem B6802595 : Blo 2015435 6802595 := bstep (se 1 (by rfl) ⟨5101946, by rfl⟩ : syracuseStep 6802595 = 10203893) B10203893
theorem B4535063 : Blo 2015435 4535063 := bstep (se 1 (by rfl) ⟨3401297, by rfl⟩ : syracuseStep 4535063 = 6802595) B6802595
theorem B3023375 : Blo 2015435 3023375 := bstep (se 1 (by rfl) ⟨2267531, by rfl⟩ : syracuseStep 3023375 = 4535063) B4535063
theorem B2015583 : Blo 2015435 2015583 := bstep (se 1 (by rfl) ⟨1511687, by rfl⟩ : syracuseStep 2015583 = 3023375) B3023375
theorem B3023381 : Blo 2015435 3023381 := bbase (se 6 (by rfl) ⟨70860, by rfl⟩ : syracuseStep 3023381 = 141721) (by norm_num)
theorem B2015587 : Blo 2015435 2015587 := bstep (se 1 (by rfl) ⟨1511690, by rfl⟩ : syracuseStep 2015587 = 3023381) B3023381
theorem B3228589 : Blo 2015435 3228589 := bbase (se 3 (by rfl) ⟨605360, by rfl⟩ : syracuseStep 3228589 = 1210721) (by norm_num)
theorem B17219141 : Blo 2015435 17219141 := bstep (se 4 (by rfl) ⟨1614294, by rfl⟩ : syracuseStep 17219141 = 3228589) B3228589
theorem B11479427 : Blo 2015435 11479427 := bstep (se 1 (by rfl) ⟨8609570, by rfl⟩ : syracuseStep 11479427 = 17219141) B17219141
theorem B7652951 : Blo 2015435 7652951 := bstep (se 1 (by rfl) ⟨5739713, by rfl⟩ : syracuseStep 7652951 = 11479427) B11479427
theorem B5101967 : Blo 2015435 5101967 := bstep (se 1 (by rfl) ⟨3826475, by rfl⟩ : syracuseStep 5101967 = 7652951) B7652951
theorem B3401311 : Blo 2015435 3401311 := bstep (se 1 (by rfl) ⟨2550983, by rfl⟩ : syracuseStep 3401311 = 5101967) B5101967
theorem B4535081 : Blo 2015435 4535081 := bstep (se 2 (by rfl) ⟨1700655, by rfl⟩ : syracuseStep 4535081 = 3401311) B3401311
theorem B3023387 : Blo 2015435 3023387 := bstep (se 1 (by rfl) ⟨2267540, by rfl⟩ : syracuseStep 3023387 = 4535081) B4535081
theorem B2015591 : Blo 2015435 2015591 := bstep (se 1 (by rfl) ⟨1511693, by rfl⟩ : syracuseStep 2015591 = 3023387) B3023387
theorem B2267545 : Blo 2015435 2267545 := bbase (se 2 (by rfl) ⟨850329, by rfl⟩ : syracuseStep 2267545 = 1700659) (by norm_num)
theorem B3023393 : Blo 2015435 3023393 := bstep (se 2 (by rfl) ⟨1133772, by rfl⟩ : syracuseStep 3023393 = 2267545) B2267545
theorem B2015595 : Blo 2015435 2015595 := bstep (se 1 (by rfl) ⟨1511696, by rfl⟩ : syracuseStep 2015595 = 3023393) B3023393
theorem B7652981 : Blo 2015435 7652981 := bbase (se 5 (by rfl) ⟨358733, by rfl⟩ : syracuseStep 7652981 = 717467) (by norm_num)
theorem B5101987 : Blo 2015435 5101987 := bstep (se 1 (by rfl) ⟨3826490, by rfl⟩ : syracuseStep 5101987 = 7652981) B7652981
theorem B6802649 : Blo 2015435 6802649 := bstep (se 2 (by rfl) ⟨2550993, by rfl⟩ : syracuseStep 6802649 = 5101987) B5101987
theorem B4535099 : Blo 2015435 4535099 := bstep (se 1 (by rfl) ⟨3401324, by rfl⟩ : syracuseStep 4535099 = 6802649) B6802649
theorem B3023399 : Blo 2015435 3023399 := bstep (se 1 (by rfl) ⟨2267549, by rfl⟩ : syracuseStep 3023399 = 4535099) B4535099
theorem B2015599 : Blo 2015435 2015599 := bstep (se 1 (by rfl) ⟨1511699, by rfl⟩ : syracuseStep 2015599 = 3023399) B3023399
theorem B3023405 : Blo 2015435 3023405 := bbase (se 3 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 3023405 = 1133777) (by norm_num)
theorem B2015603 : Blo 2015435 2015603 := bstep (se 1 (by rfl) ⟨1511702, by rfl⟩ : syracuseStep 2015603 = 3023405) B3023405
theorem B4535117 : Blo 2015435 4535117 := bbase (se 3 (by rfl) ⟨850334, by rfl⟩ : syracuseStep 4535117 = 1700669) (by norm_num)
theorem B3023411 : Blo 2015435 3023411 := bstep (se 1 (by rfl) ⟨2267558, by rfl⟩ : syracuseStep 3023411 = 4535117) B4535117
theorem B2015607 : Blo 2015435 2015607 := bstep (se 1 (by rfl) ⟨1511705, by rfl⟩ : syracuseStep 2015607 = 3023411) B3023411
theorem B2551009 : Blo 2015435 2551009 := bbase (se 2 (by rfl) ⟨956628, by rfl⟩ : syracuseStep 2551009 = 1913257) (by norm_num)
theorem B3401345 : Blo 2015435 3401345 := bstep (se 2 (by rfl) ⟨1275504, by rfl⟩ : syracuseStep 3401345 = 2551009) B2551009
theorem B2267563 : Blo 2015435 2267563 := bstep (se 1 (by rfl) ⟨1700672, by rfl⟩ : syracuseStep 2267563 = 3401345) B3401345
theorem B3023417 : Blo 2015435 3023417 := bstep (se 2 (by rfl) ⟨1133781, by rfl⟩ : syracuseStep 3023417 = 2267563) B2267563
theorem B2015611 : Blo 2015435 2015611 := bstep (se 1 (by rfl) ⟨1511708, by rfl⟩ : syracuseStep 2015611 = 3023417) B3023417
theorem B22959125 : Blo 2015435 22959125 := bbase (se 6 (by rfl) ⟨538104, by rfl⟩ : syracuseStep 22959125 = 1076209) (by norm_num)
theorem B15306083 : Blo 2015435 15306083 := bstep (se 1 (by rfl) ⟨11479562, by rfl⟩ : syracuseStep 15306083 = 22959125) B22959125
theorem B10204055 : Blo 2015435 10204055 := bstep (se 1 (by rfl) ⟨7653041, by rfl⟩ : syracuseStep 10204055 = 15306083) B15306083
theorem B6802703 : Blo 2015435 6802703 := bstep (se 1 (by rfl) ⟨5102027, by rfl⟩ : syracuseStep 6802703 = 10204055) B10204055
theorem B4535135 : Blo 2015435 4535135 := bstep (se 1 (by rfl) ⟨3401351, by rfl⟩ : syracuseStep 4535135 = 6802703) B6802703
theorem B3023423 : Blo 2015435 3023423 := bstep (se 1 (by rfl) ⟨2267567, by rfl⟩ : syracuseStep 3023423 = 4535135) B4535135
theorem B2015615 : Blo 2015435 2015615 := bstep (se 1 (by rfl) ⟨1511711, by rfl⟩ : syracuseStep 2015615 = 3023423) B3023423
theorem B3023429 : Blo 2015435 3023429 := bbase (se 4 (by rfl) ⟨283446, by rfl⟩ : syracuseStep 3023429 = 566893) (by norm_num)
theorem B2015619 : Blo 2015435 2015619 := bstep (se 1 (by rfl) ⟨1511714, by rfl⟩ : syracuseStep 2015619 = 3023429) B3023429
theorem B3401365 : Blo 2015435 3401365 := bbase (se 6 (by rfl) ⟨79719, by rfl⟩ : syracuseStep 3401365 = 159439) (by norm_num)
theorem B4535153 : Blo 2015435 4535153 := bstep (se 2 (by rfl) ⟨1700682, by rfl⟩ : syracuseStep 4535153 = 3401365) B3401365
theorem B3023435 : Blo 2015435 3023435 := bstep (se 1 (by rfl) ⟨2267576, by rfl⟩ : syracuseStep 3023435 = 4535153) B4535153
theorem B2015623 : Blo 2015435 2015623 := bstep (se 1 (by rfl) ⟨1511717, by rfl⟩ : syracuseStep 2015623 = 3023435) B3023435
theorem B2267581 : Blo 2015435 2267581 := bbase (se 3 (by rfl) ⟨425171, by rfl⟩ : syracuseStep 2267581 = 850343) (by norm_num)
theorem B3023441 : Blo 2015435 3023441 := bstep (se 2 (by rfl) ⟨1133790, by rfl⟩ : syracuseStep 3023441 = 2267581) B2267581
theorem B2015627 : Blo 2015435 2015627 := bstep (se 1 (by rfl) ⟨1511720, by rfl⟩ : syracuseStep 2015627 = 3023441) B3023441
theorem B6802757 : Blo 2015435 6802757 := bbase (se 4 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 6802757 = 1275517) (by norm_num)
theorem B4535171 : Blo 2015435 4535171 := bstep (se 1 (by rfl) ⟨3401378, by rfl⟩ : syracuseStep 4535171 = 6802757) B6802757
theorem B3023447 : Blo 2015435 3023447 := bstep (se 1 (by rfl) ⟨2267585, by rfl⟩ : syracuseStep 3023447 = 4535171) B4535171
theorem B2015631 : Blo 2015435 2015631 := bstep (se 1 (by rfl) ⟨1511723, by rfl⟩ : syracuseStep 2015631 = 3023447) B3023447
theorem B3023453 : Blo 2015435 3023453 := bbase (se 3 (by rfl) ⟨566897, by rfl⟩ : syracuseStep 3023453 = 1133795) (by norm_num)
theorem B2015635 : Blo 2015435 2015635 := bstep (se 1 (by rfl) ⟨1511726, by rfl⟩ : syracuseStep 2015635 = 3023453) B3023453
theorem B4535189 : Blo 2015435 4535189 := bbase (se 6 (by rfl) ⟨106293, by rfl⟩ : syracuseStep 4535189 = 212587) (by norm_num)
theorem B3023459 : Blo 2015435 3023459 := bstep (se 1 (by rfl) ⟨2267594, by rfl⟩ : syracuseStep 3023459 = 4535189) B4535189
theorem B2015639 : Blo 2015435 2015639 := bstep (se 1 (by rfl) ⟨1511729, by rfl⟩ : syracuseStep 2015639 = 3023459) B3023459
theorem B2421505 : Blo 2015435 2421505 := bbase (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) (by norm_num)
theorem B3228673 : Blo 2015435 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B4304897 : Blo 2015435 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B2869931 : Blo 2015435 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B7653149 : Blo 2015435 7653149 := bstep (se 3 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 7653149 = 2869931) B2869931
theorem B5102099 : Blo 2015435 5102099 := bstep (se 1 (by rfl) ⟨3826574, by rfl⟩ : syracuseStep 5102099 = 7653149) B7653149
theorem B3401399 : Blo 2015435 3401399 := bstep (se 1 (by rfl) ⟨2551049, by rfl⟩ : syracuseStep 3401399 = 5102099) B5102099
theorem B2267599 : Blo 2015435 2267599 := bstep (se 1 (by rfl) ⟨1700699, by rfl⟩ : syracuseStep 2267599 = 3401399) B3401399
theorem B3023465 : Blo 2015435 3023465 := bstep (se 2 (by rfl) ⟨1133799, by rfl⟩ : syracuseStep 3023465 = 2267599) B2267599
theorem B2015643 : Blo 2015435 2015643 := bstep (se 1 (by rfl) ⟨1511732, by rfl⟩ : syracuseStep 2015643 = 3023465) B3023465
theorem B2421509 : Blo 2015435 2421509 := bbase (se 4 (by rfl) ⟨227016, by rfl⟩ : syracuseStep 2421509 = 454033) (by norm_num)
theorem B6457357 : Blo 2015435 6457357 := bstep (se 3 (by rfl) ⟨1210754, by rfl⟩ : syracuseStep 6457357 = 2421509) B2421509
theorem B8609809 : Blo 2015435 8609809 := bstep (se 2 (by rfl) ⟨3228678, by rfl⟩ : syracuseStep 8609809 = 6457357) B6457357
theorem B11479745 : Blo 2015435 11479745 := bstep (se 2 (by rfl) ⟨4304904, by rfl⟩ : syracuseStep 11479745 = 8609809) B8609809
theorem B7653163 : Blo 2015435 7653163 := bstep (se 1 (by rfl) ⟨5739872, by rfl⟩ : syracuseStep 7653163 = 11479745) B11479745
theorem B10204217 : Blo 2015435 10204217 := bstep (se 2 (by rfl) ⟨3826581, by rfl⟩ : syracuseStep 10204217 = 7653163) B7653163
theorem B6802811 : Blo 2015435 6802811 := bstep (se 1 (by rfl) ⟨5102108, by rfl⟩ : syracuseStep 6802811 = 10204217) B10204217
theorem B4535207 : Blo 2015435 4535207 := bstep (se 1 (by rfl) ⟨3401405, by rfl⟩ : syracuseStep 4535207 = 6802811) B6802811
theorem B3023471 : Blo 2015435 3023471 := bstep (se 1 (by rfl) ⟨2267603, by rfl⟩ : syracuseStep 3023471 = 4535207) B4535207
theorem B2015647 : Blo 2015435 2015647 := bstep (se 1 (by rfl) ⟨1511735, by rfl⟩ : syracuseStep 2015647 = 3023471) B3023471
theorem B3023477 : Blo 2015435 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B2015651 : Blo 2015435 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B3826597 : Blo 2015435 3826597 := bbase (se 4 (by rfl) ⟨358743, by rfl⟩ : syracuseStep 3826597 = 717487) (by norm_num)
theorem B5102129 : Blo 2015435 5102129 := bstep (se 2 (by rfl) ⟨1913298, by rfl⟩ : syracuseStep 5102129 = 3826597) B3826597
theorem B3401419 : Blo 2015435 3401419 := bstep (se 1 (by rfl) ⟨2551064, by rfl⟩ : syracuseStep 3401419 = 5102129) B5102129
theorem B4535225 : Blo 2015435 4535225 := bstep (se 2 (by rfl) ⟨1700709, by rfl⟩ : syracuseStep 4535225 = 3401419) B3401419
theorem B3023483 : Blo 2015435 3023483 := bstep (se 1 (by rfl) ⟨2267612, by rfl⟩ : syracuseStep 3023483 = 4535225) B4535225
theorem B2015655 : Blo 2015435 2015655 := bstep (se 1 (by rfl) ⟨1511741, by rfl⟩ : syracuseStep 2015655 = 3023483) B3023483
theorem B2267617 : Blo 2015435 2267617 := bbase (se 2 (by rfl) ⟨850356, by rfl⟩ : syracuseStep 2267617 = 1700713) (by norm_num)
theorem B3023489 : Blo 2015435 3023489 := bstep (se 2 (by rfl) ⟨1133808, by rfl⟩ : syracuseStep 3023489 = 2267617) B2267617
theorem B2015659 : Blo 2015435 2015659 := bstep (se 1 (by rfl) ⟨1511744, by rfl⟩ : syracuseStep 2015659 = 3023489) B3023489
theorem B5102149 : Blo 2015435 5102149 := bbase (se 4 (by rfl) ⟨478326, by rfl⟩ : syracuseStep 5102149 = 956653) (by norm_num)
theorem B6802865 : Blo 2015435 6802865 := bstep (se 2 (by rfl) ⟨2551074, by rfl⟩ : syracuseStep 6802865 = 5102149) B5102149
theorem B4535243 : Blo 2015435 4535243 := bstep (se 1 (by rfl) ⟨3401432, by rfl⟩ : syracuseStep 4535243 = 6802865) B6802865
theorem B3023495 : Blo 2015435 3023495 := bstep (se 1 (by rfl) ⟨2267621, by rfl⟩ : syracuseStep 3023495 = 4535243) B4535243
theorem B2015663 : Blo 2015435 2015663 := bstep (se 1 (by rfl) ⟨1511747, by rfl⟩ : syracuseStep 2015663 = 3023495) B3023495
theorem B3023501 : Blo 2015435 3023501 := bbase (se 3 (by rfl) ⟨566906, by rfl⟩ : syracuseStep 3023501 = 1133813) (by norm_num)
theorem B2015667 : Blo 2015435 2015667 := bstep (se 1 (by rfl) ⟨1511750, by rfl⟩ : syracuseStep 2015667 = 3023501) B3023501
theorem B4535261 : Blo 2015435 4535261 := bbase (se 3 (by rfl) ⟨850361, by rfl⟩ : syracuseStep 4535261 = 1700723) (by norm_num)
theorem B3023507 : Blo 2015435 3023507 := bstep (se 1 (by rfl) ⟨2267630, by rfl⟩ : syracuseStep 3023507 = 4535261) B4535261
theorem B2015671 : Blo 2015435 2015671 := bstep (se 1 (by rfl) ⟨1511753, by rfl⟩ : syracuseStep 2015671 = 3023507) B3023507
theorem B3401453 : Blo 2015435 3401453 := bbase (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) (by norm_num)
theorem B2267635 : Blo 2015435 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B3023513 : Blo 2015435 3023513 := bstep (se 2 (by rfl) ⟨1133817, by rfl⟩ : syracuseStep 3023513 = 2267635) B2267635
theorem B2015675 : Blo 2015435 2015675 := bstep (se 1 (by rfl) ⟨1511756, by rfl⟩ : syracuseStep 2015675 = 3023513) B3023513
theorem B2043181 : Blo 2015435 2043181 := bbase (se 3 (by rfl) ⟨383096, by rfl⟩ : syracuseStep 2043181 = 766193) (by norm_num)
theorem B2724241 : Blo 2015435 2724241 := bstep (se 2 (by rfl) ⟨1021590, by rfl⟩ : syracuseStep 2724241 = 2043181) B2043181
theorem B3632321 : Blo 2015435 3632321 := bstep (se 2 (by rfl) ⟨1362120, by rfl⟩ : syracuseStep 3632321 = 2724241) B2724241
theorem B9686189 : Blo 2015435 9686189 := bstep (se 3 (by rfl) ⟨1816160, by rfl⟩ : syracuseStep 9686189 = 3632321) B3632321
theorem B25829837 : Blo 2015435 25829837 := bstep (se 3 (by rfl) ⟨4843094, by rfl⟩ : syracuseStep 25829837 = 9686189) B9686189
theorem B17219891 : Blo 2015435 17219891 := bstep (se 1 (by rfl) ⟨12914918, by rfl⟩ : syracuseStep 17219891 = 25829837) B25829837
theorem B11479927 : Blo 2015435 11479927 := bstep (se 1 (by rfl) ⟨8609945, by rfl⟩ : syracuseStep 11479927 = 17219891) B17219891
theorem B15306569 : Blo 2015435 15306569 := bstep (se 2 (by rfl) ⟨5739963, by rfl⟩ : syracuseStep 15306569 = 11479927) B11479927
theorem B10204379 : Blo 2015435 10204379 := bstep (se 1 (by rfl) ⟨7653284, by rfl⟩ : syracuseStep 10204379 = 15306569) B15306569
theorem B6802919 : Blo 2015435 6802919 := bstep (se 1 (by rfl) ⟨5102189, by rfl⟩ : syracuseStep 6802919 = 10204379) B10204379
theorem B4535279 : Blo 2015435 4535279 := bstep (se 1 (by rfl) ⟨3401459, by rfl⟩ : syracuseStep 4535279 = 6802919) B6802919
theorem B3023519 : Blo 2015435 3023519 := bstep (se 1 (by rfl) ⟨2267639, by rfl⟩ : syracuseStep 3023519 = 4535279) B4535279
theorem B2015679 : Blo 2015435 2015679 := bstep (se 1 (by rfl) ⟨1511759, by rfl⟩ : syracuseStep 2015679 = 3023519) B3023519
theorem B3023525 : Blo 2015435 3023525 := bbase (se 4 (by rfl) ⟨283455, by rfl⟩ : syracuseStep 3023525 = 566911) (by norm_num)
theorem B2015683 : Blo 2015435 2015683 := bstep (se 1 (by rfl) ⟨1511762, by rfl⟩ : syracuseStep 2015683 = 3023525) B3023525
theorem B2551105 : Blo 2015435 2551105 := bbase (se 2 (by rfl) ⟨956664, by rfl⟩ : syracuseStep 2551105 = 1913329) (by norm_num)
theorem B3401473 : Blo 2015435 3401473 := bstep (se 2 (by rfl) ⟨1275552, by rfl⟩ : syracuseStep 3401473 = 2551105) B2551105
theorem B4535297 : Blo 2015435 4535297 := bstep (se 2 (by rfl) ⟨1700736, by rfl⟩ : syracuseStep 4535297 = 3401473) B3401473
theorem B3023531 : Blo 2015435 3023531 := bstep (se 1 (by rfl) ⟨2267648, by rfl⟩ : syracuseStep 3023531 = 4535297) B4535297
theorem B2015687 : Blo 2015435 2015687 := bstep (se 1 (by rfl) ⟨1511765, by rfl⟩ : syracuseStep 2015687 = 3023531) B3023531
theorem B2267653 : Blo 2015435 2267653 := bbase (se 4 (by rfl) ⟨212592, by rfl⟩ : syracuseStep 2267653 = 425185) (by norm_num)
theorem B3023537 : Blo 2015435 3023537 := bstep (se 2 (by rfl) ⟨1133826, by rfl⟩ : syracuseStep 3023537 = 2267653) B2267653
theorem B2015691 : Blo 2015435 2015691 := bstep (se 1 (by rfl) ⟨1511768, by rfl⟩ : syracuseStep 2015691 = 3023537) B3023537
theorem B2870005 : Blo 2015435 2870005 := bbase (se 5 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 2870005 = 269063) (by norm_num)
theorem B3826673 : Blo 2015435 3826673 := bstep (se 2 (by rfl) ⟨1435002, by rfl⟩ : syracuseStep 3826673 = 2870005) B2870005
theorem B2551115 : Blo 2015435 2551115 := bstep (se 1 (by rfl) ⟨1913336, by rfl⟩ : syracuseStep 2551115 = 3826673) B3826673
theorem B6802973 : Blo 2015435 6802973 := bstep (se 3 (by rfl) ⟨1275557, by rfl⟩ : syracuseStep 6802973 = 2551115) B2551115
theorem B4535315 : Blo 2015435 4535315 := bstep (se 1 (by rfl) ⟨3401486, by rfl⟩ : syracuseStep 4535315 = 6802973) B6802973
theorem B3023543 : Blo 2015435 3023543 := bstep (se 1 (by rfl) ⟨2267657, by rfl⟩ : syracuseStep 3023543 = 4535315) B4535315
theorem B2015695 : Blo 2015435 2015695 := bstep (se 1 (by rfl) ⟨1511771, by rfl⟩ : syracuseStep 2015695 = 3023543) B3023543
theorem B3023549 : Blo 2015435 3023549 := bbase (se 3 (by rfl) ⟨566915, by rfl⟩ : syracuseStep 3023549 = 1133831) (by norm_num)
theorem B2015699 : Blo 2015435 2015699 := bstep (se 1 (by rfl) ⟨1511774, by rfl⟩ : syracuseStep 2015699 = 3023549) B3023549
theorem B4535333 : Blo 2015435 4535333 := bbase (se 4 (by rfl) ⟨425187, by rfl⟩ : syracuseStep 4535333 = 850375) (by norm_num)
theorem B3023555 : Blo 2015435 3023555 := bstep (se 1 (by rfl) ⟨2267666, by rfl⟩ : syracuseStep 3023555 = 4535333) B4535333
theorem B2015703 : Blo 2015435 2015703 := bstep (se 1 (by rfl) ⟨1511777, by rfl⟩ : syracuseStep 2015703 = 3023555) B3023555
theorem B5102261 : Blo 2015435 5102261 := bbase (se 5 (by rfl) ⟨239168, by rfl⟩ : syracuseStep 5102261 = 478337) (by norm_num)
theorem B3401507 : Blo 2015435 3401507 := bstep (se 1 (by rfl) ⟨2551130, by rfl⟩ : syracuseStep 3401507 = 5102261) B5102261
theorem B2267671 : Blo 2015435 2267671 := bstep (se 1 (by rfl) ⟨1700753, by rfl⟩ : syracuseStep 2267671 = 3401507) B3401507
theorem B3023561 : Blo 2015435 3023561 := bstep (se 2 (by rfl) ⟨1133835, by rfl⟩ : syracuseStep 3023561 = 2267671) B2267671
theorem B2015707 : Blo 2015435 2015707 := bstep (se 1 (by rfl) ⟨1511780, by rfl⟩ : syracuseStep 2015707 = 3023561) B3023561
theorem B12915125 : Blo 2015435 12915125 := bbase (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) (by norm_num)
theorem B8610083 : Blo 2015435 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B5740055 : Blo 2015435 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B3826703 : Blo 2015435 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B10204541 : Blo 2015435 10204541 := bstep (se 3 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 10204541 = 3826703) B3826703
theorem B6803027 : Blo 2015435 6803027 := bstep (se 1 (by rfl) ⟨5102270, by rfl⟩ : syracuseStep 6803027 = 10204541) B10204541
theorem B4535351 : Blo 2015435 4535351 := bstep (se 1 (by rfl) ⟨3401513, by rfl⟩ : syracuseStep 4535351 = 6803027) B6803027
theorem B3023567 : Blo 2015435 3023567 := bstep (se 1 (by rfl) ⟨2267675, by rfl⟩ : syracuseStep 3023567 = 4535351) B4535351
theorem B2015711 : Blo 2015435 2015711 := bstep (se 1 (by rfl) ⟨1511783, by rfl⟩ : syracuseStep 2015711 = 3023567) B3023567
theorem B3023573 : Blo 2015435 3023573 := bbase (se 7 (by rfl) ⟨35432, by rfl⟩ : syracuseStep 3023573 = 70865) (by norm_num)
theorem B2015715 : Blo 2015435 2015715 := bstep (se 1 (by rfl) ⟨1511786, by rfl⟩ : syracuseStep 2015715 = 3023573) B3023573
theorem B6457589 : Blo 2015435 6457589 := bbase (se 5 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 6457589 = 605399) (by norm_num)
theorem B4305059 : Blo 2015435 4305059 := bstep (se 1 (by rfl) ⟨3228794, by rfl⟩ : syracuseStep 4305059 = 6457589) B6457589
theorem B2870039 : Blo 2015435 2870039 := bstep (se 1 (by rfl) ⟨2152529, by rfl⟩ : syracuseStep 2870039 = 4305059) B4305059
theorem B7653437 : Blo 2015435 7653437 := bstep (se 3 (by rfl) ⟨1435019, by rfl⟩ : syracuseStep 7653437 = 2870039) B2870039
theorem B5102291 : Blo 2015435 5102291 := bstep (se 1 (by rfl) ⟨3826718, by rfl⟩ : syracuseStep 5102291 = 7653437) B7653437
theorem B3401527 : Blo 2015435 3401527 := bstep (se 1 (by rfl) ⟨2551145, by rfl⟩ : syracuseStep 3401527 = 5102291) B5102291
theorem B4535369 : Blo 2015435 4535369 := bstep (se 2 (by rfl) ⟨1700763, by rfl⟩ : syracuseStep 4535369 = 3401527) B3401527
theorem B3023579 : Blo 2015435 3023579 := bstep (se 1 (by rfl) ⟨2267684, by rfl⟩ : syracuseStep 3023579 = 4535369) B4535369
theorem B2015719 : Blo 2015435 2015719 := bstep (se 1 (by rfl) ⟨1511789, by rfl⟩ : syracuseStep 2015719 = 3023579) B3023579
theorem B2267689 : Blo 2015435 2267689 := bbase (se 2 (by rfl) ⟨850383, by rfl⟩ : syracuseStep 2267689 = 1700767) (by norm_num)
theorem B3023585 : Blo 2015435 3023585 := bstep (se 2 (by rfl) ⟨1133844, by rfl⟩ : syracuseStep 3023585 = 2267689) B2267689
theorem B2015723 : Blo 2015435 2015723 := bstep (se 1 (by rfl) ⟨1511792, by rfl⟩ : syracuseStep 2015723 = 3023585) B3023585
theorem B4659989 : Blo 2015435 4659989 := bbase (se 6 (by rfl) ⟨109218, by rfl⟩ : syracuseStep 4659989 = 218437) (by norm_num)
theorem B12426637 : Blo 2015435 12426637 := bstep (se 3 (by rfl) ⟨2329994, by rfl⟩ : syracuseStep 12426637 = 4659989) B4659989
theorem B16568849 : Blo 2015435 16568849 := bstep (se 2 (by rfl) ⟨6213318, by rfl⟩ : syracuseStep 16568849 = 12426637) B12426637
theorem B11045899 : Blo 2015435 11045899 := bstep (se 1 (by rfl) ⟨8284424, by rfl⟩ : syracuseStep 11045899 = 16568849) B16568849
theorem B58911461 : Blo 2015435 58911461 := bstep (se 4 (by rfl) ⟨5522949, by rfl⟩ : syracuseStep 58911461 = 11045899) B11045899
theorem B39274307 : Blo 2015435 39274307 := bstep (se 1 (by rfl) ⟨29455730, by rfl⟩ : syracuseStep 39274307 = 58911461) B58911461
theorem B26182871 : Blo 2015435 26182871 := bstep (se 1 (by rfl) ⟨19637153, by rfl⟩ : syracuseStep 26182871 = 39274307) B39274307
theorem B17455247 : Blo 2015435 17455247 := bstep (se 1 (by rfl) ⟨13091435, by rfl⟩ : syracuseStep 17455247 = 26182871) B26182871
theorem B11636831 : Blo 2015435 11636831 := bstep (se 1 (by rfl) ⟨8727623, by rfl⟩ : syracuseStep 11636831 = 17455247) B17455247
theorem B31031549 : Blo 2015435 31031549 := bstep (se 3 (by rfl) ⟨5818415, by rfl⟩ : syracuseStep 31031549 = 11636831) B11636831
theorem B20687699 : Blo 2015435 20687699 := bstep (se 1 (by rfl) ⟨15515774, by rfl⟩ : syracuseStep 20687699 = 31031549) B31031549
theorem B13791799 : Blo 2015435 13791799 := bstep (se 1 (by rfl) ⟨10343849, by rfl⟩ : syracuseStep 13791799 = 20687699) B20687699
theorem B73556261 : Blo 2015435 73556261 := bstep (se 4 (by rfl) ⟨6895899, by rfl⟩ : syracuseStep 73556261 = 13791799) B13791799
theorem B49037507 : Blo 2015435 49037507 := bstep (se 1 (by rfl) ⟨36778130, by rfl⟩ : syracuseStep 49037507 = 73556261) B73556261
theorem B32691671 : Blo 2015435 32691671 := bstep (se 1 (by rfl) ⟨24518753, by rfl⟩ : syracuseStep 32691671 = 49037507) B49037507
theorem B21794447 : Blo 2015435 21794447 := bstep (se 1 (by rfl) ⟨16345835, by rfl⟩ : syracuseStep 21794447 = 32691671) B32691671
theorem B14529631 : Blo 2015435 14529631 := bstep (se 1 (by rfl) ⟨10897223, by rfl⟩ : syracuseStep 14529631 = 21794447) B21794447
theorem B19372841 : Blo 2015435 19372841 := bstep (se 2 (by rfl) ⟨7264815, by rfl⟩ : syracuseStep 19372841 = 14529631) B14529631
theorem B12915227 : Blo 2015435 12915227 := bstep (se 1 (by rfl) ⟨9686420, by rfl⟩ : syracuseStep 12915227 = 19372841) B19372841
theorem B8610151 : Blo 2015435 8610151 := bstep (se 1 (by rfl) ⟨6457613, by rfl⟩ : syracuseStep 8610151 = 12915227) B12915227
theorem B11480201 : Blo 2015435 11480201 := bstep (se 2 (by rfl) ⟨4305075, by rfl⟩ : syracuseStep 11480201 = 8610151) B8610151
theorem B7653467 : Blo 2015435 7653467 := bstep (se 1 (by rfl) ⟨5740100, by rfl⟩ : syracuseStep 7653467 = 11480201) B11480201
theorem B5102311 : Blo 2015435 5102311 := bstep (se 1 (by rfl) ⟨3826733, by rfl⟩ : syracuseStep 5102311 = 7653467) B7653467
theorem B6803081 : Blo 2015435 6803081 := bstep (se 2 (by rfl) ⟨2551155, by rfl⟩ : syracuseStep 6803081 = 5102311) B5102311
theorem B4535387 : Blo 2015435 4535387 := bstep (se 1 (by rfl) ⟨3401540, by rfl⟩ : syracuseStep 4535387 = 6803081) B6803081
theorem B3023591 : Blo 2015435 3023591 := bstep (se 1 (by rfl) ⟨2267693, by rfl⟩ : syracuseStep 3023591 = 4535387) B4535387
theorem B2015727 : Blo 2015435 2015727 := bstep (se 1 (by rfl) ⟨1511795, by rfl⟩ : syracuseStep 2015727 = 3023591) B3023591
theorem B3023597 : Blo 2015435 3023597 := bbase (se 3 (by rfl) ⟨566924, by rfl⟩ : syracuseStep 3023597 = 1133849) (by norm_num)
theorem B2015731 : Blo 2015435 2015731 := bstep (se 1 (by rfl) ⟨1511798, by rfl⟩ : syracuseStep 2015731 = 3023597) B3023597
theorem B4535405 : Blo 2015435 4535405 := bbase (se 3 (by rfl) ⟨850388, by rfl⟩ : syracuseStep 4535405 = 1700777) (by norm_num)
theorem B3023603 : Blo 2015435 3023603 := bstep (se 1 (by rfl) ⟨2267702, by rfl⟩ : syracuseStep 3023603 = 4535405) B4535405
theorem B2015735 : Blo 2015435 2015735 := bstep (se 1 (by rfl) ⟨1511801, by rfl⟩ : syracuseStep 2015735 = 3023603) B3023603
theorem B3826757 : Blo 2015435 3826757 := bbase (se 4 (by rfl) ⟨358758, by rfl⟩ : syracuseStep 3826757 = 717517) (by norm_num)
theorem B2551171 : Blo 2015435 2551171 := bstep (se 1 (by rfl) ⟨1913378, by rfl⟩ : syracuseStep 2551171 = 3826757) B3826757
theorem B3401561 : Blo 2015435 3401561 := bstep (se 2 (by rfl) ⟨1275585, by rfl⟩ : syracuseStep 3401561 = 2551171) B2551171
theorem B2267707 : Blo 2015435 2267707 := bstep (se 1 (by rfl) ⟨1700780, by rfl⟩ : syracuseStep 2267707 = 3401561) B3401561
theorem B3023609 : Blo 2015435 3023609 := bstep (se 2 (by rfl) ⟨1133853, by rfl⟩ : syracuseStep 3023609 = 2267707) B2267707
theorem B2015739 : Blo 2015435 2015739 := bstep (se 1 (by rfl) ⟨1511804, by rfl⟩ : syracuseStep 2015739 = 3023609) B3023609
theorem B20687861 : Blo 2015435 20687861 := bbase (se 5 (by rfl) ⟨969743, by rfl⟩ : syracuseStep 20687861 = 1939487) (by norm_num)
theorem B13791907 : Blo 2015435 13791907 := bstep (se 1 (by rfl) ⟨10343930, by rfl⟩ : syracuseStep 13791907 = 20687861) B20687861
theorem B18389209 : Blo 2015435 18389209 := bstep (se 2 (by rfl) ⟨6895953, by rfl⟩ : syracuseStep 18389209 = 13791907) B13791907
theorem B24518945 : Blo 2015435 24518945 := bstep (se 2 (by rfl) ⟨9194604, by rfl⟩ : syracuseStep 24518945 = 18389209) B18389209
theorem B16345963 : Blo 2015435 16345963 := bstep (se 1 (by rfl) ⟨12259472, by rfl⟩ : syracuseStep 16345963 = 24518945) B24518945
theorem B21794617 : Blo 2015435 21794617 := bstep (se 2 (by rfl) ⟨8172981, by rfl⟩ : syracuseStep 21794617 = 16345963) B16345963
theorem B29059489 : Blo 2015435 29059489 := bstep (se 2 (by rfl) ⟨10897308, by rfl⟩ : syracuseStep 29059489 = 21794617) B21794617
theorem B38745985 : Blo 2015435 38745985 := bstep (se 2 (by rfl) ⟨14529744, by rfl⟩ : syracuseStep 38745985 = 29059489) B29059489
theorem B51661313 : Blo 2015435 51661313 := bstep (se 2 (by rfl) ⟨19372992, by rfl⟩ : syracuseStep 51661313 = 38745985) B38745985
theorem B34440875 : Blo 2015435 34440875 := bstep (se 1 (by rfl) ⟨25830656, by rfl⟩ : syracuseStep 34440875 = 51661313) B51661313
theorem B22960583 : Blo 2015435 22960583 := bstep (se 1 (by rfl) ⟨17220437, by rfl⟩ : syracuseStep 22960583 = 34440875) B34440875
theorem B15307055 : Blo 2015435 15307055 := bstep (se 1 (by rfl) ⟨11480291, by rfl⟩ : syracuseStep 15307055 = 22960583) B22960583
theorem B10204703 : Blo 2015435 10204703 := bstep (se 1 (by rfl) ⟨7653527, by rfl⟩ : syracuseStep 10204703 = 15307055) B15307055
theorem B6803135 : Blo 2015435 6803135 := bstep (se 1 (by rfl) ⟨5102351, by rfl⟩ : syracuseStep 6803135 = 10204703) B10204703
theorem B4535423 : Blo 2015435 4535423 := bstep (se 1 (by rfl) ⟨3401567, by rfl⟩ : syracuseStep 4535423 = 6803135) B6803135
theorem B3023615 : Blo 2015435 3023615 := bstep (se 1 (by rfl) ⟨2267711, by rfl⟩ : syracuseStep 3023615 = 4535423) B4535423
theorem B2015743 : Blo 2015435 2015743 := bstep (se 1 (by rfl) ⟨1511807, by rfl⟩ : syracuseStep 2015743 = 3023615) B3023615
theorem B3023621 : Blo 2015435 3023621 := bbase (se 4 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 3023621 = 566929) (by norm_num)
theorem B2015747 : Blo 2015435 2015747 := bstep (se 1 (by rfl) ⟨1511810, by rfl⟩ : syracuseStep 2015747 = 3023621) B3023621
theorem B3401581 : Blo 2015435 3401581 := bbase (se 3 (by rfl) ⟨637796, by rfl⟩ : syracuseStep 3401581 = 1275593) (by norm_num)
theorem B4535441 : Blo 2015435 4535441 := bstep (se 2 (by rfl) ⟨1700790, by rfl⟩ : syracuseStep 4535441 = 3401581) B3401581
theorem B3023627 : Blo 2015435 3023627 := bstep (se 1 (by rfl) ⟨2267720, by rfl⟩ : syracuseStep 3023627 = 4535441) B4535441
theorem B2015751 : Blo 2015435 2015751 := bstep (se 1 (by rfl) ⟨1511813, by rfl⟩ : syracuseStep 2015751 = 3023627) B3023627
theorem B2267725 : Blo 2015435 2267725 := bbase (se 3 (by rfl) ⟨425198, by rfl⟩ : syracuseStep 2267725 = 850397) (by norm_num)
theorem B3023633 : Blo 2015435 3023633 := bstep (se 2 (by rfl) ⟨1133862, by rfl⟩ : syracuseStep 3023633 = 2267725) B2267725
theorem B2015755 : Blo 2015435 2015755 := bstep (se 1 (by rfl) ⟨1511816, by rfl⟩ : syracuseStep 2015755 = 3023633) B3023633
theorem B6803189 : Blo 2015435 6803189 := bbase (se 5 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 6803189 = 637799) (by norm_num)
theorem B4535459 : Blo 2015435 4535459 := bstep (se 1 (by rfl) ⟨3401594, by rfl⟩ : syracuseStep 4535459 = 6803189) B6803189
theorem B3023639 : Blo 2015435 3023639 := bstep (se 1 (by rfl) ⟨2267729, by rfl⟩ : syracuseStep 3023639 = 4535459) B4535459
theorem B2015759 : Blo 2015435 2015759 := bstep (se 1 (by rfl) ⟨1511819, by rfl⟩ : syracuseStep 2015759 = 3023639) B3023639
theorem B3023645 : Blo 2015435 3023645 := bbase (se 3 (by rfl) ⟨566933, by rfl⟩ : syracuseStep 3023645 = 1133867) (by norm_num)
theorem B2015763 : Blo 2015435 2015763 := bstep (se 1 (by rfl) ⟨1511822, by rfl⟩ : syracuseStep 2015763 = 3023645) B3023645
theorem B4535477 : Blo 2015435 4535477 := bbase (se 5 (by rfl) ⟨212600, by rfl⟩ : syracuseStep 4535477 = 425201) (by norm_num)
theorem B3023651 : Blo 2015435 3023651 := bstep (se 1 (by rfl) ⟨2267738, by rfl⟩ : syracuseStep 3023651 = 4535477) B4535477
theorem B2015767 : Blo 2015435 2015767 := bstep (se 1 (by rfl) ⟨1511825, by rfl⟩ : syracuseStep 2015767 = 3023651) B3023651
theorem B2152585 : Blo 2015435 2152585 := bbase (se 2 (by rfl) ⟨807219, by rfl⟩ : syracuseStep 2152585 = 1614439) (by norm_num)
theorem B11480453 : Blo 2015435 11480453 := bstep (se 4 (by rfl) ⟨1076292, by rfl⟩ : syracuseStep 11480453 = 2152585) B2152585
theorem B7653635 : Blo 2015435 7653635 := bstep (se 1 (by rfl) ⟨5740226, by rfl⟩ : syracuseStep 7653635 = 11480453) B11480453
theorem B5102423 : Blo 2015435 5102423 := bstep (se 1 (by rfl) ⟨3826817, by rfl⟩ : syracuseStep 5102423 = 7653635) B7653635
theorem B3401615 : Blo 2015435 3401615 := bstep (se 1 (by rfl) ⟨2551211, by rfl⟩ : syracuseStep 3401615 = 5102423) B5102423
theorem B2267743 : Blo 2015435 2267743 := bstep (se 1 (by rfl) ⟨1700807, by rfl⟩ : syracuseStep 2267743 = 3401615) B3401615
theorem B3023657 : Blo 2015435 3023657 := bstep (se 2 (by rfl) ⟨1133871, by rfl⟩ : syracuseStep 3023657 = 2267743) B2267743
theorem B2015771 : Blo 2015435 2015771 := bstep (se 1 (by rfl) ⟨1511828, by rfl⟩ : syracuseStep 2015771 = 3023657) B3023657
theorem B2152589 : Blo 2015435 2152589 := bbase (se 3 (by rfl) ⟨403610, by rfl⟩ : syracuseStep 2152589 = 807221) (by norm_num)
theorem B5740237 : Blo 2015435 5740237 := bstep (se 3 (by rfl) ⟨1076294, by rfl⟩ : syracuseStep 5740237 = 2152589) B2152589
theorem B7653649 : Blo 2015435 7653649 := bstep (se 2 (by rfl) ⟨2870118, by rfl⟩ : syracuseStep 7653649 = 5740237) B5740237
theorem B10204865 : Blo 2015435 10204865 := bstep (se 2 (by rfl) ⟨3826824, by rfl⟩ : syracuseStep 10204865 = 7653649) B7653649
theorem B6803243 : Blo 2015435 6803243 := bstep (se 1 (by rfl) ⟨5102432, by rfl⟩ : syracuseStep 6803243 = 10204865) B10204865
theorem B4535495 : Blo 2015435 4535495 := bstep (se 1 (by rfl) ⟨3401621, by rfl⟩ : syracuseStep 4535495 = 6803243) B6803243
theorem B3023663 : Blo 2015435 3023663 := bstep (se 1 (by rfl) ⟨2267747, by rfl⟩ : syracuseStep 3023663 = 4535495) B4535495
theorem B2015775 : Blo 2015435 2015775 := bstep (se 1 (by rfl) ⟨1511831, by rfl⟩ : syracuseStep 2015775 = 3023663) B3023663
theorem B3023669 : Blo 2015435 3023669 := bbase (se 5 (by rfl) ⟨141734, by rfl⟩ : syracuseStep 3023669 = 283469) (by norm_num)
theorem B2015779 : Blo 2015435 2015779 := bstep (se 1 (by rfl) ⟨1511834, by rfl⟩ : syracuseStep 2015779 = 3023669) B3023669
theorem B5102453 : Blo 2015435 5102453 := bbase (se 5 (by rfl) ⟨239177, by rfl⟩ : syracuseStep 5102453 = 478355) (by norm_num)
theorem B3401635 : Blo 2015435 3401635 := bstep (se 1 (by rfl) ⟨2551226, by rfl⟩ : syracuseStep 3401635 = 5102453) B5102453
theorem B4535513 : Blo 2015435 4535513 := bstep (se 2 (by rfl) ⟨1700817, by rfl⟩ : syracuseStep 4535513 = 3401635) B3401635
theorem B3023675 : Blo 2015435 3023675 := bstep (se 1 (by rfl) ⟨2267756, by rfl⟩ : syracuseStep 3023675 = 4535513) B4535513
theorem B2015783 : Blo 2015435 2015783 := bstep (se 1 (by rfl) ⟨1511837, by rfl⟩ : syracuseStep 2015783 = 3023675) B3023675
theorem B2267761 : Blo 2015435 2267761 := bbase (se 2 (by rfl) ⟨850410, by rfl⟩ : syracuseStep 2267761 = 1700821) (by norm_num)
theorem B3023681 : Blo 2015435 3023681 := bstep (se 2 (by rfl) ⟨1133880, by rfl⟩ : syracuseStep 3023681 = 2267761) B2267761
theorem B2015787 : Blo 2015435 2015787 := bstep (se 1 (by rfl) ⟨1511840, by rfl⟩ : syracuseStep 2015787 = 3023681) B3023681
theorem B16346357 : Blo 2015435 16346357 := bbase (se 5 (by rfl) ⟨766235, by rfl⟩ : syracuseStep 16346357 = 1532471) (by norm_num)
theorem B10897571 : Blo 2015435 10897571 := bstep (se 1 (by rfl) ⟨8173178, by rfl⟩ : syracuseStep 10897571 = 16346357) B16346357
theorem B7265047 : Blo 2015435 7265047 := bstep (se 1 (by rfl) ⟨5448785, by rfl⟩ : syracuseStep 7265047 = 10897571) B10897571
theorem B9686729 : Blo 2015435 9686729 := bstep (se 2 (by rfl) ⟨3632523, by rfl⟩ : syracuseStep 9686729 = 7265047) B7265047
theorem B6457819 : Blo 2015435 6457819 := bstep (se 1 (by rfl) ⟨4843364, by rfl⟩ : syracuseStep 6457819 = 9686729) B9686729
theorem B8610425 : Blo 2015435 8610425 := bstep (se 2 (by rfl) ⟨3228909, by rfl⟩ : syracuseStep 8610425 = 6457819) B6457819
theorem B5740283 : Blo 2015435 5740283 := bstep (se 1 (by rfl) ⟨4305212, by rfl⟩ : syracuseStep 5740283 = 8610425) B8610425
theorem B3826855 : Blo 2015435 3826855 := bstep (se 1 (by rfl) ⟨2870141, by rfl⟩ : syracuseStep 3826855 = 5740283) B5740283
theorem B5102473 : Blo 2015435 5102473 := bstep (se 2 (by rfl) ⟨1913427, by rfl⟩ : syracuseStep 5102473 = 3826855) B3826855
theorem B6803297 : Blo 2015435 6803297 := bstep (se 2 (by rfl) ⟨2551236, by rfl⟩ : syracuseStep 6803297 = 5102473) B5102473
theorem B4535531 : Blo 2015435 4535531 := bstep (se 1 (by rfl) ⟨3401648, by rfl⟩ : syracuseStep 4535531 = 6803297) B6803297
theorem B3023687 : Blo 2015435 3023687 := bstep (se 1 (by rfl) ⟨2267765, by rfl⟩ : syracuseStep 3023687 = 4535531) B4535531
theorem B2015791 : Blo 2015435 2015791 := bstep (se 1 (by rfl) ⟨1511843, by rfl⟩ : syracuseStep 2015791 = 3023687) B3023687
theorem B3023693 : Blo 2015435 3023693 := bbase (se 3 (by rfl) ⟨566942, by rfl⟩ : syracuseStep 3023693 = 1133885) (by norm_num)
theorem B2015795 : Blo 2015435 2015795 := bstep (se 1 (by rfl) ⟨1511846, by rfl⟩ : syracuseStep 2015795 = 3023693) B3023693
theorem B4535549 : Blo 2015435 4535549 := bbase (se 3 (by rfl) ⟨850415, by rfl⟩ : syracuseStep 4535549 = 1700831) (by norm_num)
theorem B3023699 : Blo 2015435 3023699 := bstep (se 1 (by rfl) ⟨2267774, by rfl⟩ : syracuseStep 3023699 = 4535549) B4535549
theorem B2015799 : Blo 2015435 2015799 := bstep (se 1 (by rfl) ⟨1511849, by rfl⟩ : syracuseStep 2015799 = 3023699) B3023699
theorem B3401669 : Blo 2015435 3401669 := bbase (se 4 (by rfl) ⟨318906, by rfl⟩ : syracuseStep 3401669 = 637813) (by norm_num)
theorem B2267779 : Blo 2015435 2267779 := bstep (se 1 (by rfl) ⟨1700834, by rfl⟩ : syracuseStep 2267779 = 3401669) B3401669
theorem B3023705 : Blo 2015435 3023705 := bstep (se 2 (by rfl) ⟨1133889, by rfl⟩ : syracuseStep 3023705 = 2267779) B2267779
theorem B2015803 : Blo 2015435 2015803 := bstep (se 1 (by rfl) ⟨1511852, by rfl⟩ : syracuseStep 2015803 = 3023705) B3023705
theorem B15307541 : Blo 2015435 15307541 := bbase (se 6 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 15307541 = 717541) (by norm_num)
theorem B10205027 : Blo 2015435 10205027 := bstep (se 1 (by rfl) ⟨7653770, by rfl⟩ : syracuseStep 10205027 = 15307541) B15307541
theorem B6803351 : Blo 2015435 6803351 := bstep (se 1 (by rfl) ⟨5102513, by rfl⟩ : syracuseStep 6803351 = 10205027) B10205027
theorem B4535567 : Blo 2015435 4535567 := bstep (se 1 (by rfl) ⟨3401675, by rfl⟩ : syracuseStep 4535567 = 6803351) B6803351
theorem B3023711 : Blo 2015435 3023711 := bstep (se 1 (by rfl) ⟨2267783, by rfl⟩ : syracuseStep 3023711 = 4535567) B4535567
theorem B2015807 : Blo 2015435 2015807 := bstep (se 1 (by rfl) ⟨1511855, by rfl⟩ : syracuseStep 2015807 = 3023711) B3023711
theorem B3023717 : Blo 2015435 3023717 := bbase (se 4 (by rfl) ⟨283473, by rfl⟩ : syracuseStep 3023717 = 566947) (by norm_num)
theorem B2015811 : Blo 2015435 2015811 := bstep (se 1 (by rfl) ⟨1511858, by rfl⟩ : syracuseStep 2015811 = 3023717) B3023717
theorem B3826901 : Blo 2015435 3826901 := bbase (se 7 (by rfl) ⟨44846, by rfl⟩ : syracuseStep 3826901 = 89693) (by norm_num)
theorem B2551267 : Blo 2015435 2551267 := bstep (se 1 (by rfl) ⟨1913450, by rfl⟩ : syracuseStep 2551267 = 3826901) B3826901
theorem B3401689 : Blo 2015435 3401689 := bstep (se 2 (by rfl) ⟨1275633, by rfl⟩ : syracuseStep 3401689 = 2551267) B2551267
theorem B4535585 : Blo 2015435 4535585 := bstep (se 2 (by rfl) ⟨1700844, by rfl⟩ : syracuseStep 4535585 = 3401689) B3401689
theorem B3023723 : Blo 2015435 3023723 := bstep (se 1 (by rfl) ⟨2267792, by rfl⟩ : syracuseStep 3023723 = 4535585) B4535585
theorem B2015815 : Blo 2015435 2015815 := bstep (se 1 (by rfl) ⟨1511861, by rfl⟩ : syracuseStep 2015815 = 3023723) B3023723
theorem B2267797 : Blo 2015435 2267797 := bbase (se 6 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 2267797 = 106303) (by norm_num)
theorem B3023729 : Blo 2015435 3023729 := bstep (se 2 (by rfl) ⟨1133898, by rfl⟩ : syracuseStep 3023729 = 2267797) B2267797
theorem B2015819 : Blo 2015435 2015819 := bstep (se 1 (by rfl) ⟨1511864, by rfl⟩ : syracuseStep 2015819 = 3023729) B3023729
theorem B2551277 : Blo 2015435 2551277 := bbase (se 3 (by rfl) ⟨478364, by rfl⟩ : syracuseStep 2551277 = 956729) (by norm_num)
theorem B6803405 : Blo 2015435 6803405 := bstep (se 3 (by rfl) ⟨1275638, by rfl⟩ : syracuseStep 6803405 = 2551277) B2551277
theorem B4535603 : Blo 2015435 4535603 := bstep (se 1 (by rfl) ⟨3401702, by rfl⟩ : syracuseStep 4535603 = 6803405) B6803405
theorem B3023735 : Blo 2015435 3023735 := bstep (se 1 (by rfl) ⟨2267801, by rfl⟩ : syracuseStep 3023735 = 4535603) B4535603
theorem B2015823 : Blo 2015435 2015823 := bstep (se 1 (by rfl) ⟨1511867, by rfl⟩ : syracuseStep 2015823 = 3023735) B3023735
theorem B3023741 : Blo 2015435 3023741 := bbase (se 3 (by rfl) ⟨566951, by rfl⟩ : syracuseStep 3023741 = 1133903) (by norm_num)
theorem B2015827 : Blo 2015435 2015827 := bstep (se 1 (by rfl) ⟨1511870, by rfl⟩ : syracuseStep 2015827 = 3023741) B3023741
theorem B4535621 : Blo 2015435 4535621 := bbase (se 4 (by rfl) ⟨425214, by rfl⟩ : syracuseStep 4535621 = 850429) (by norm_num)
theorem B3023747 : Blo 2015435 3023747 := bstep (se 1 (by rfl) ⟨2267810, by rfl⟩ : syracuseStep 3023747 = 4535621) B4535621
theorem B2015831 : Blo 2015435 2015831 := bstep (se 1 (by rfl) ⟨1511873, by rfl⟩ : syracuseStep 2015831 = 3023747) B3023747
theorem B9195029 : Blo 2015435 9195029 := bbase (se 6 (by rfl) ⟨215508, by rfl⟩ : syracuseStep 9195029 = 431017) (by norm_num)
theorem B6130019 : Blo 2015435 6130019 := bstep (se 1 (by rfl) ⟨4597514, by rfl⟩ : syracuseStep 6130019 = 9195029) B9195029
theorem B16346717 : Blo 2015435 16346717 := bstep (se 3 (by rfl) ⟨3065009, by rfl⟩ : syracuseStep 16346717 = 6130019) B6130019
theorem B10897811 : Blo 2015435 10897811 := bstep (se 1 (by rfl) ⟨8173358, by rfl⟩ : syracuseStep 10897811 = 16346717) B16346717
theorem B7265207 : Blo 2015435 7265207 := bstep (se 1 (by rfl) ⟨5448905, by rfl⟩ : syracuseStep 7265207 = 10897811) B10897811
theorem B4843471 : Blo 2015435 4843471 := bstep (se 1 (by rfl) ⟨3632603, by rfl⟩ : syracuseStep 4843471 = 7265207) B7265207
theorem B6457961 : Blo 2015435 6457961 := bstep (se 2 (by rfl) ⟨2421735, by rfl⟩ : syracuseStep 6457961 = 4843471) B4843471
theorem B4305307 : Blo 2015435 4305307 := bstep (se 1 (by rfl) ⟨3228980, by rfl⟩ : syracuseStep 4305307 = 6457961) B6457961
theorem B5740409 : Blo 2015435 5740409 := bstep (se 2 (by rfl) ⟨2152653, by rfl⟩ : syracuseStep 5740409 = 4305307) B4305307
theorem B3826939 : Blo 2015435 3826939 := bstep (se 1 (by rfl) ⟨2870204, by rfl⟩ : syracuseStep 3826939 = 5740409) B5740409
theorem B5102585 : Blo 2015435 5102585 := bstep (se 2 (by rfl) ⟨1913469, by rfl⟩ : syracuseStep 5102585 = 3826939) B3826939
theorem B3401723 : Blo 2015435 3401723 := bstep (se 1 (by rfl) ⟨2551292, by rfl⟩ : syracuseStep 3401723 = 5102585) B5102585
theorem B2267815 : Blo 2015435 2267815 := bstep (se 1 (by rfl) ⟨1700861, by rfl⟩ : syracuseStep 2267815 = 3401723) B3401723
theorem B3023753 : Blo 2015435 3023753 := bstep (se 2 (by rfl) ⟨1133907, by rfl⟩ : syracuseStep 3023753 = 2267815) B2267815
theorem B2015835 : Blo 2015435 2015835 := bstep (se 1 (by rfl) ⟨1511876, by rfl⟩ : syracuseStep 2015835 = 3023753) B3023753
theorem B10205189 : Blo 2015435 10205189 := bbase (se 4 (by rfl) ⟨956736, by rfl⟩ : syracuseStep 10205189 = 1913473) (by norm_num)
theorem B6803459 : Blo 2015435 6803459 := bstep (se 1 (by rfl) ⟨5102594, by rfl⟩ : syracuseStep 6803459 = 10205189) B10205189
theorem B4535639 : Blo 2015435 4535639 := bstep (se 1 (by rfl) ⟨3401729, by rfl⟩ : syracuseStep 4535639 = 6803459) B6803459
theorem B3023759 : Blo 2015435 3023759 := bstep (se 1 (by rfl) ⟨2267819, by rfl⟩ : syracuseStep 3023759 = 4535639) B4535639
theorem B2015839 : Blo 2015435 2015839 := bstep (se 1 (by rfl) ⟨1511879, by rfl⟩ : syracuseStep 2015839 = 3023759) B3023759
theorem B3023765 : Blo 2015435 3023765 := bbase (se 6 (by rfl) ⟨70869, by rfl⟩ : syracuseStep 3023765 = 141739) (by norm_num)
theorem B2015843 : Blo 2015435 2015843 := bstep (se 1 (by rfl) ⟨1511882, by rfl⟩ : syracuseStep 2015843 = 3023765) B3023765
theorem B11480885 : Blo 2015435 11480885 := bbase (se 5 (by rfl) ⟨538166, by rfl⟩ : syracuseStep 11480885 = 1076333) (by norm_num)
theorem B7653923 : Blo 2015435 7653923 := bstep (se 1 (by rfl) ⟨5740442, by rfl⟩ : syracuseStep 7653923 = 11480885) B11480885
theorem B5102615 : Blo 2015435 5102615 := bstep (se 1 (by rfl) ⟨3826961, by rfl⟩ : syracuseStep 5102615 = 7653923) B7653923
theorem B3401743 : Blo 2015435 3401743 := bstep (se 1 (by rfl) ⟨2551307, by rfl⟩ : syracuseStep 3401743 = 5102615) B5102615
theorem B4535657 : Blo 2015435 4535657 := bstep (se 2 (by rfl) ⟨1700871, by rfl⟩ : syracuseStep 4535657 = 3401743) B3401743
theorem B3023771 : Blo 2015435 3023771 := bstep (se 1 (by rfl) ⟨2267828, by rfl⟩ : syracuseStep 3023771 = 4535657) B4535657
theorem B2015847 : Blo 2015435 2015847 := bstep (se 1 (by rfl) ⟨1511885, by rfl⟩ : syracuseStep 2015847 = 3023771) B3023771
theorem B2267833 : Blo 2015435 2267833 := bbase (se 2 (by rfl) ⟨850437, by rfl⟩ : syracuseStep 2267833 = 1700875) (by norm_num)
theorem B3023777 : Blo 2015435 3023777 := bstep (se 2 (by rfl) ⟨1133916, by rfl⟩ : syracuseStep 3023777 = 2267833) B2267833
theorem B2015851 : Blo 2015435 2015851 := bstep (se 1 (by rfl) ⟨1511888, by rfl⟩ : syracuseStep 2015851 = 3023777) B3023777
theorem B4305349 : Blo 2015435 4305349 := bbase (se 4 (by rfl) ⟨403626, by rfl⟩ : syracuseStep 4305349 = 807253) (by norm_num)
theorem B5740465 : Blo 2015435 5740465 := bstep (se 2 (by rfl) ⟨2152674, by rfl⟩ : syracuseStep 5740465 = 4305349) B4305349
theorem B7653953 : Blo 2015435 7653953 := bstep (se 2 (by rfl) ⟨2870232, by rfl⟩ : syracuseStep 7653953 = 5740465) B5740465
theorem B5102635 : Blo 2015435 5102635 := bstep (se 1 (by rfl) ⟨3826976, by rfl⟩ : syracuseStep 5102635 = 7653953) B7653953
theorem B6803513 : Blo 2015435 6803513 := bstep (se 2 (by rfl) ⟨2551317, by rfl⟩ : syracuseStep 6803513 = 5102635) B5102635
theorem B4535675 : Blo 2015435 4535675 := bstep (se 1 (by rfl) ⟨3401756, by rfl⟩ : syracuseStep 4535675 = 6803513) B6803513
theorem B3023783 : Blo 2015435 3023783 := bstep (se 1 (by rfl) ⟨2267837, by rfl⟩ : syracuseStep 3023783 = 4535675) B4535675
theorem B2015855 : Blo 2015435 2015855 := bstep (se 1 (by rfl) ⟨1511891, by rfl⟩ : syracuseStep 2015855 = 3023783) B3023783
theorem B3023789 : Blo 2015435 3023789 := bbase (se 3 (by rfl) ⟨566960, by rfl⟩ : syracuseStep 3023789 = 1133921) (by norm_num)
theorem B2015859 : Blo 2015435 2015859 := bstep (se 1 (by rfl) ⟨1511894, by rfl⟩ : syracuseStep 2015859 = 3023789) B3023789
theorem B4535693 : Blo 2015435 4535693 := bbase (se 3 (by rfl) ⟨850442, by rfl⟩ : syracuseStep 4535693 = 1700885) (by norm_num)
theorem B3023795 : Blo 2015435 3023795 := bstep (se 1 (by rfl) ⟨2267846, by rfl⟩ : syracuseStep 3023795 = 4535693) B4535693
theorem B2015863 : Blo 2015435 2015863 := bstep (se 1 (by rfl) ⟨1511897, by rfl⟩ : syracuseStep 2015863 = 3023795) B3023795
theorem B2551333 : Blo 2015435 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B3401777 : Blo 2015435 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2267851 : Blo 2015435 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B3023801 : Blo 2015435 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B2015867 : Blo 2015435 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B9320645 : Blo 2015435 9320645 := bbase (se 4 (by rfl) ⟨873810, by rfl⟩ : syracuseStep 9320645 = 1747621) (by norm_num)
theorem B6213763 : Blo 2015435 6213763 := bstep (se 1 (by rfl) ⟨4660322, by rfl⟩ : syracuseStep 6213763 = 9320645) B9320645
theorem B8285017 : Blo 2015435 8285017 := bstep (se 2 (by rfl) ⟨3106881, by rfl⟩ : syracuseStep 8285017 = 6213763) B6213763
theorem B11046689 : Blo 2015435 11046689 := bstep (se 2 (by rfl) ⟨4142508, by rfl⟩ : syracuseStep 11046689 = 8285017) B8285017
theorem B7364459 : Blo 2015435 7364459 := bstep (se 1 (by rfl) ⟨5523344, by rfl⟩ : syracuseStep 7364459 = 11046689) B11046689
theorem B4909639 : Blo 2015435 4909639 := bstep (se 1 (by rfl) ⟨3682229, by rfl⟩ : syracuseStep 4909639 = 7364459) B7364459
theorem B6546185 : Blo 2015435 6546185 := bstep (se 2 (by rfl) ⟨2454819, by rfl⟩ : syracuseStep 6546185 = 4909639) B4909639
theorem B4364123 : Blo 2015435 4364123 := bstep (se 1 (by rfl) ⟨3273092, by rfl⟩ : syracuseStep 4364123 = 6546185) B6546185
theorem B46550645 : Blo 2015435 46550645 := bstep (se 5 (by rfl) ⟨2182061, by rfl⟩ : syracuseStep 46550645 = 4364123) B4364123
theorem B31033763 : Blo 2015435 31033763 := bstep (se 1 (by rfl) ⟨23275322, by rfl⟩ : syracuseStep 31033763 = 46550645) B46550645
theorem B20689175 : Blo 2015435 20689175 := bstep (se 1 (by rfl) ⟨15516881, by rfl⟩ : syracuseStep 20689175 = 31033763) B31033763
theorem B13792783 : Blo 2015435 13792783 := bstep (se 1 (by rfl) ⟨10344587, by rfl⟩ : syracuseStep 13792783 = 20689175) B20689175
theorem B18390377 : Blo 2015435 18390377 := bstep (se 2 (by rfl) ⟨6896391, by rfl⟩ : syracuseStep 18390377 = 13792783) B13792783
theorem B12260251 : Blo 2015435 12260251 := bstep (se 1 (by rfl) ⟨9195188, by rfl⟩ : syracuseStep 12260251 = 18390377) B18390377
theorem B65388005 : Blo 2015435 65388005 := bstep (se 4 (by rfl) ⟨6130125, by rfl⟩ : syracuseStep 65388005 = 12260251) B12260251
theorem B43592003 : Blo 2015435 43592003 := bstep (se 1 (by rfl) ⟨32694002, by rfl⟩ : syracuseStep 43592003 = 65388005) B65388005
theorem B29061335 : Blo 2015435 29061335 := bstep (se 1 (by rfl) ⟨21796001, by rfl⟩ : syracuseStep 29061335 = 43592003) B43592003
theorem B19374223 : Blo 2015435 19374223 := bstep (se 1 (by rfl) ⟨14530667, by rfl⟩ : syracuseStep 19374223 = 29061335) B29061335
theorem B25832297 : Blo 2015435 25832297 := bstep (se 2 (by rfl) ⟨9687111, by rfl⟩ : syracuseStep 25832297 = 19374223) B19374223
theorem B17221531 : Blo 2015435 17221531 := bstep (se 1 (by rfl) ⟨12916148, by rfl⟩ : syracuseStep 17221531 = 25832297) B25832297
theorem B22962041 : Blo 2015435 22962041 := bstep (se 2 (by rfl) ⟨8610765, by rfl⟩ : syracuseStep 22962041 = 17221531) B17221531
theorem B15308027 : Blo 2015435 15308027 := bstep (se 1 (by rfl) ⟨11481020, by rfl⟩ : syracuseStep 15308027 = 22962041) B22962041
theorem B10205351 : Blo 2015435 10205351 := bstep (se 1 (by rfl) ⟨7654013, by rfl⟩ : syracuseStep 10205351 = 15308027) B15308027
theorem B6803567 : Blo 2015435 6803567 := bstep (se 1 (by rfl) ⟨5102675, by rfl⟩ : syracuseStep 6803567 = 10205351) B10205351
theorem B4535711 : Blo 2015435 4535711 := bstep (se 1 (by rfl) ⟨3401783, by rfl⟩ : syracuseStep 4535711 = 6803567) B6803567
theorem B3023807 : Blo 2015435 3023807 := bstep (se 1 (by rfl) ⟨2267855, by rfl⟩ : syracuseStep 3023807 = 4535711) B4535711
theorem B2015871 : Blo 2015435 2015871 := bstep (se 1 (by rfl) ⟨1511903, by rfl⟩ : syracuseStep 2015871 = 3023807) B3023807
theorem B3023813 : Blo 2015435 3023813 := bbase (se 4 (by rfl) ⟨283482, by rfl⟩ : syracuseStep 3023813 = 566965) (by norm_num)
theorem B2015875 : Blo 2015435 2015875 := bstep (se 1 (by rfl) ⟨1511906, by rfl⟩ : syracuseStep 2015875 = 3023813) B3023813
theorem B3401797 : Blo 2015435 3401797 := bbase (se 4 (by rfl) ⟨318918, by rfl⟩ : syracuseStep 3401797 = 637837) (by norm_num)
theorem B4535729 : Blo 2015435 4535729 := bstep (se 2 (by rfl) ⟨1700898, by rfl⟩ : syracuseStep 4535729 = 3401797) B3401797
theorem B3023819 : Blo 2015435 3023819 := bstep (se 1 (by rfl) ⟨2267864, by rfl⟩ : syracuseStep 3023819 = 4535729) B4535729
theorem B2015879 : Blo 2015435 2015879 := bstep (se 1 (by rfl) ⟨1511909, by rfl⟩ : syracuseStep 2015879 = 3023819) B3023819
theorem B2267869 : Blo 2015435 2267869 := bbase (se 3 (by rfl) ⟨425225, by rfl⟩ : syracuseStep 2267869 = 850451) (by norm_num)
theorem B3023825 : Blo 2015435 3023825 := bstep (se 2 (by rfl) ⟨1133934, by rfl⟩ : syracuseStep 3023825 = 2267869) B2267869
theorem B2015883 : Blo 2015435 2015883 := bstep (se 1 (by rfl) ⟨1511912, by rfl⟩ : syracuseStep 2015883 = 3023825) B3023825
theorem B6803621 : Blo 2015435 6803621 := bbase (se 4 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 6803621 = 1275679) (by norm_num)
theorem B4535747 : Blo 2015435 4535747 := bstep (se 1 (by rfl) ⟨3401810, by rfl⟩ : syracuseStep 4535747 = 6803621) B6803621
theorem B3023831 : Blo 2015435 3023831 := bstep (se 1 (by rfl) ⟨2267873, by rfl⟩ : syracuseStep 3023831 = 4535747) B4535747
theorem B2015887 : Blo 2015435 2015887 := bstep (se 1 (by rfl) ⟨1511915, by rfl⟩ : syracuseStep 2015887 = 3023831) B3023831
theorem B3023837 : Blo 2015435 3023837 := bbase (se 3 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 3023837 = 1133939) (by norm_num)
theorem B2015891 : Blo 2015435 2015891 := bstep (se 1 (by rfl) ⟨1511918, by rfl⟩ : syracuseStep 2015891 = 3023837) B3023837
theorem B4535765 : Blo 2015435 4535765 := bbase (se 7 (by rfl) ⟨53153, by rfl⟩ : syracuseStep 4535765 = 106307) (by norm_num)
theorem B3023843 : Blo 2015435 3023843 := bstep (se 1 (by rfl) ⟨2267882, by rfl⟩ : syracuseStep 3023843 = 4535765) B4535765
theorem B2015895 : Blo 2015435 2015895 := bstep (se 1 (by rfl) ⟨1511921, by rfl⟩ : syracuseStep 2015895 = 3023843) B3023843
theorem B4909709 : Blo 2015435 4909709 := bbase (se 3 (by rfl) ⟨920570, by rfl⟩ : syracuseStep 4909709 = 1841141) (by norm_num)
theorem B3273139 : Blo 2015435 3273139 := bstep (se 1 (by rfl) ⟨2454854, by rfl⟩ : syracuseStep 3273139 = 4909709) B4909709
theorem B17456741 : Blo 2015435 17456741 := bstep (se 4 (by rfl) ⟨1636569, by rfl⟩ : syracuseStep 17456741 = 3273139) B3273139
theorem B11637827 : Blo 2015435 11637827 := bstep (se 1 (by rfl) ⟨8728370, by rfl⟩ : syracuseStep 11637827 = 17456741) B17456741
theorem B7758551 : Blo 2015435 7758551 := bstep (se 1 (by rfl) ⟨5818913, by rfl⟩ : syracuseStep 7758551 = 11637827) B11637827
theorem B20689469 : Blo 2015435 20689469 := bstep (se 3 (by rfl) ⟨3879275, by rfl⟩ : syracuseStep 20689469 = 7758551) B7758551
theorem B13792979 : Blo 2015435 13792979 := bstep (se 1 (by rfl) ⟨10344734, by rfl⟩ : syracuseStep 13792979 = 20689469) B20689469
theorem B9195319 : Blo 2015435 9195319 := bstep (se 1 (by rfl) ⟨6896489, by rfl⟩ : syracuseStep 9195319 = 13792979) B13792979
theorem B12260425 : Blo 2015435 12260425 := bstep (se 2 (by rfl) ⟨4597659, by rfl⟩ : syracuseStep 12260425 = 9195319) B9195319
theorem B16347233 : Blo 2015435 16347233 := bstep (se 2 (by rfl) ⟨6130212, by rfl⟩ : syracuseStep 16347233 = 12260425) B12260425
theorem B10898155 : Blo 2015435 10898155 := bstep (se 1 (by rfl) ⟨8173616, by rfl⟩ : syracuseStep 10898155 = 16347233) B16347233
theorem B14530873 : Blo 2015435 14530873 := bstep (se 2 (by rfl) ⟨5449077, by rfl⟩ : syracuseStep 14530873 = 10898155) B10898155
theorem B19374497 : Blo 2015435 19374497 := bstep (se 2 (by rfl) ⟨7265436, by rfl⟩ : syracuseStep 19374497 = 14530873) B14530873
theorem B12916331 : Blo 2015435 12916331 := bstep (se 1 (by rfl) ⟨9687248, by rfl⟩ : syracuseStep 12916331 = 19374497) B19374497
theorem B8610887 : Blo 2015435 8610887 := bstep (se 1 (by rfl) ⟨6458165, by rfl⟩ : syracuseStep 8610887 = 12916331) B12916331
theorem B5740591 : Blo 2015435 5740591 := bstep (se 1 (by rfl) ⟨4305443, by rfl⟩ : syracuseStep 5740591 = 8610887) B8610887
theorem B7654121 : Blo 2015435 7654121 := bstep (se 2 (by rfl) ⟨2870295, by rfl⟩ : syracuseStep 7654121 = 5740591) B5740591
theorem B5102747 : Blo 2015435 5102747 := bstep (se 1 (by rfl) ⟨3827060, by rfl⟩ : syracuseStep 5102747 = 7654121) B7654121
theorem B3401831 : Blo 2015435 3401831 := bstep (se 1 (by rfl) ⟨2551373, by rfl⟩ : syracuseStep 3401831 = 5102747) B5102747
theorem B2267887 : Blo 2015435 2267887 := bstep (se 1 (by rfl) ⟨1700915, by rfl⟩ : syracuseStep 2267887 = 3401831) B3401831
theorem B3023849 : Blo 2015435 3023849 := bstep (se 2 (by rfl) ⟨1133943, by rfl⟩ : syracuseStep 3023849 = 2267887) B2267887
theorem B2015899 : Blo 2015435 2015899 := bstep (se 1 (by rfl) ⟨1511924, by rfl⟩ : syracuseStep 2015899 = 3023849) B3023849
theorem B3632725 : Blo 2015435 3632725 := bbase (se 8 (by rfl) ⟨21285, by rfl⟩ : syracuseStep 3632725 = 42571) (by norm_num)
theorem B4843633 : Blo 2015435 4843633 := bstep (se 2 (by rfl) ⟨1816362, by rfl⟩ : syracuseStep 4843633 = 3632725) B3632725
theorem B6458177 : Blo 2015435 6458177 := bstep (se 2 (by rfl) ⟨2421816, by rfl⟩ : syracuseStep 6458177 = 4843633) B4843633
theorem B17221805 : Blo 2015435 17221805 := bstep (se 3 (by rfl) ⟨3229088, by rfl⟩ : syracuseStep 17221805 = 6458177) B6458177
theorem B11481203 : Blo 2015435 11481203 := bstep (se 1 (by rfl) ⟨8610902, by rfl⟩ : syracuseStep 11481203 = 17221805) B17221805
theorem B7654135 : Blo 2015435 7654135 := bstep (se 1 (by rfl) ⟨5740601, by rfl⟩ : syracuseStep 7654135 = 11481203) B11481203
theorem B10205513 : Blo 2015435 10205513 := bstep (se 2 (by rfl) ⟨3827067, by rfl⟩ : syracuseStep 10205513 = 7654135) B7654135
theorem B6803675 : Blo 2015435 6803675 := bstep (se 1 (by rfl) ⟨5102756, by rfl⟩ : syracuseStep 6803675 = 10205513) B10205513
theorem B4535783 : Blo 2015435 4535783 := bstep (se 1 (by rfl) ⟨3401837, by rfl⟩ : syracuseStep 4535783 = 6803675) B6803675
theorem B3023855 : Blo 2015435 3023855 := bstep (se 1 (by rfl) ⟨2267891, by rfl⟩ : syracuseStep 3023855 = 4535783) B4535783
theorem B2015903 : Blo 2015435 2015903 := bstep (se 1 (by rfl) ⟨1511927, by rfl⟩ : syracuseStep 2015903 = 3023855) B3023855
theorem B3023861 : Blo 2015435 3023861 := bbase (se 5 (by rfl) ⟨141743, by rfl⟩ : syracuseStep 3023861 = 283487) (by norm_num)
theorem B2015907 : Blo 2015435 2015907 := bstep (se 1 (by rfl) ⟨1511930, by rfl⟩ : syracuseStep 2015907 = 3023861) B3023861
theorem B4305469 : Blo 2015435 4305469 := bbase (se 3 (by rfl) ⟨807275, by rfl⟩ : syracuseStep 4305469 = 1614551) (by norm_num)
theorem B5740625 : Blo 2015435 5740625 := bstep (se 2 (by rfl) ⟨2152734, by rfl⟩ : syracuseStep 5740625 = 4305469) B4305469
theorem B3827083 : Blo 2015435 3827083 := bstep (se 1 (by rfl) ⟨2870312, by rfl⟩ : syracuseStep 3827083 = 5740625) B5740625
theorem B5102777 : Blo 2015435 5102777 := bstep (se 2 (by rfl) ⟨1913541, by rfl⟩ : syracuseStep 5102777 = 3827083) B3827083
theorem B3401851 : Blo 2015435 3401851 := bstep (se 1 (by rfl) ⟨2551388, by rfl⟩ : syracuseStep 3401851 = 5102777) B5102777
theorem B4535801 : Blo 2015435 4535801 := bstep (se 2 (by rfl) ⟨1700925, by rfl⟩ : syracuseStep 4535801 = 3401851) B3401851
theorem B3023867 : Blo 2015435 3023867 := bstep (se 1 (by rfl) ⟨2267900, by rfl⟩ : syracuseStep 3023867 = 4535801) B4535801
theorem B2015911 : Blo 2015435 2015911 := bstep (se 1 (by rfl) ⟨1511933, by rfl⟩ : syracuseStep 2015911 = 3023867) B3023867
theorem B2267905 : Blo 2015435 2267905 := bbase (se 2 (by rfl) ⟨850464, by rfl⟩ : syracuseStep 2267905 = 1700929) (by norm_num)
theorem B3023873 : Blo 2015435 3023873 := bstep (se 2 (by rfl) ⟨1133952, by rfl⟩ : syracuseStep 3023873 = 2267905) B2267905
theorem B2015915 : Blo 2015435 2015915 := bstep (se 1 (by rfl) ⟨1511936, by rfl⟩ : syracuseStep 2015915 = 3023873) B3023873
theorem B5102797 : Blo 2015435 5102797 := bbase (se 3 (by rfl) ⟨956774, by rfl⟩ : syracuseStep 5102797 = 1913549) (by norm_num)
theorem B6803729 : Blo 2015435 6803729 := bstep (se 2 (by rfl) ⟨2551398, by rfl⟩ : syracuseStep 6803729 = 5102797) B5102797
theorem B4535819 : Blo 2015435 4535819 := bstep (se 1 (by rfl) ⟨3401864, by rfl⟩ : syracuseStep 4535819 = 6803729) B6803729
theorem B3023879 : Blo 2015435 3023879 := bstep (se 1 (by rfl) ⟨2267909, by rfl⟩ : syracuseStep 3023879 = 4535819) B4535819
theorem B2015919 : Blo 2015435 2015919 := bstep (se 1 (by rfl) ⟨1511939, by rfl⟩ : syracuseStep 2015919 = 3023879) B3023879
theorem B3023885 : Blo 2015435 3023885 := bbase (se 3 (by rfl) ⟨566978, by rfl⟩ : syracuseStep 3023885 = 1133957) (by norm_num)
theorem B2015923 : Blo 2015435 2015923 := bstep (se 1 (by rfl) ⟨1511942, by rfl⟩ : syracuseStep 2015923 = 3023885) B3023885
theorem B4535837 : Blo 2015435 4535837 := bbase (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) (by norm_num)
theorem B3023891 : Blo 2015435 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B2015927 : Blo 2015435 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B3401885 : Blo 2015435 3401885 := bbase (se 3 (by rfl) ⟨637853, by rfl⟩ : syracuseStep 3401885 = 1275707) (by norm_num)
theorem B2267923 : Blo 2015435 2267923 := bstep (se 1 (by rfl) ⟨1700942, by rfl⟩ : syracuseStep 2267923 = 3401885) B3401885
theorem B3023897 : Blo 2015435 3023897 := bstep (se 2 (by rfl) ⟨1133961, by rfl⟩ : syracuseStep 3023897 = 2267923) B2267923
theorem B2015931 : Blo 2015435 2015931 := bstep (se 1 (by rfl) ⟨1511948, by rfl⟩ : syracuseStep 2015931 = 3023897) B3023897
theorem B10344917 : Blo 2015435 10344917 := bbase (se 7 (by rfl) ⟨121229, by rfl⟩ : syracuseStep 10344917 = 242459) (by norm_num)
theorem B6896611 : Blo 2015435 6896611 := bstep (se 1 (by rfl) ⟨5172458, by rfl⟩ : syracuseStep 6896611 = 10344917) B10344917
theorem B9195481 : Blo 2015435 9195481 := bstep (se 2 (by rfl) ⟨3448305, by rfl⟩ : syracuseStep 9195481 = 6896611) B6896611
theorem B12260641 : Blo 2015435 12260641 := bstep (se 2 (by rfl) ⟨4597740, by rfl⟩ : syracuseStep 12260641 = 9195481) B9195481
theorem B16347521 : Blo 2015435 16347521 := bstep (se 2 (by rfl) ⟨6130320, by rfl⟩ : syracuseStep 16347521 = 12260641) B12260641
theorem B43593389 : Blo 2015435 43593389 := bstep (se 3 (by rfl) ⟨8173760, by rfl⟩ : syracuseStep 43593389 = 16347521) B16347521
theorem B29062259 : Blo 2015435 29062259 := bstep (se 1 (by rfl) ⟨21796694, by rfl⟩ : syracuseStep 29062259 = 43593389) B43593389
theorem B19374839 : Blo 2015435 19374839 := bstep (se 1 (by rfl) ⟨14531129, by rfl⟩ : syracuseStep 19374839 = 29062259) B29062259
theorem B12916559 : Blo 2015435 12916559 := bstep (se 1 (by rfl) ⟨9687419, by rfl⟩ : syracuseStep 12916559 = 19374839) B19374839
theorem B8611039 : Blo 2015435 8611039 := bstep (se 1 (by rfl) ⟨6458279, by rfl⟩ : syracuseStep 8611039 = 12916559) B12916559
theorem B11481385 : Blo 2015435 11481385 := bstep (se 2 (by rfl) ⟨4305519, by rfl⟩ : syracuseStep 11481385 = 8611039) B8611039
theorem B15308513 : Blo 2015435 15308513 := bstep (se 2 (by rfl) ⟨5740692, by rfl⟩ : syracuseStep 15308513 = 11481385) B11481385
theorem B10205675 : Blo 2015435 10205675 := bstep (se 1 (by rfl) ⟨7654256, by rfl⟩ : syracuseStep 10205675 = 15308513) B15308513
theorem B6803783 : Blo 2015435 6803783 := bstep (se 1 (by rfl) ⟨5102837, by rfl⟩ : syracuseStep 6803783 = 10205675) B10205675
theorem B4535855 : Blo 2015435 4535855 := bstep (se 1 (by rfl) ⟨3401891, by rfl⟩ : syracuseStep 4535855 = 6803783) B6803783
theorem B3023903 : Blo 2015435 3023903 := bstep (se 1 (by rfl) ⟨2267927, by rfl⟩ : syracuseStep 3023903 = 4535855) B4535855
theorem B2015935 : Blo 2015435 2015935 := bstep (se 1 (by rfl) ⟨1511951, by rfl⟩ : syracuseStep 2015935 = 3023903) B3023903
theorem B3023909 : Blo 2015435 3023909 := bbase (se 4 (by rfl) ⟨283491, by rfl⟩ : syracuseStep 3023909 = 566983) (by norm_num)
theorem B2015939 : Blo 2015435 2015939 := bstep (se 1 (by rfl) ⟨1511954, by rfl⟩ : syracuseStep 2015939 = 3023909) B3023909
theorem B2551429 : Blo 2015435 2551429 := bbase (se 4 (by rfl) ⟨239196, by rfl⟩ : syracuseStep 2551429 = 478393) (by norm_num)
theorem B3401905 : Blo 2015435 3401905 := bstep (se 2 (by rfl) ⟨1275714, by rfl⟩ : syracuseStep 3401905 = 2551429) B2551429
theorem B4535873 : Blo 2015435 4535873 := bstep (se 2 (by rfl) ⟨1700952, by rfl⟩ : syracuseStep 4535873 = 3401905) B3401905
theorem B3023915 : Blo 2015435 3023915 := bstep (se 1 (by rfl) ⟨2267936, by rfl⟩ : syracuseStep 3023915 = 4535873) B4535873
theorem B2015943 : Blo 2015435 2015943 := bstep (se 1 (by rfl) ⟨1511957, by rfl⟩ : syracuseStep 2015943 = 3023915) B3023915
theorem B2267941 : Blo 2015435 2267941 := bbase (se 4 (by rfl) ⟨212619, by rfl⟩ : syracuseStep 2267941 = 425239) (by norm_num)
theorem B3023921 : Blo 2015435 3023921 := bstep (se 2 (by rfl) ⟨1133970, by rfl⟩ : syracuseStep 3023921 = 2267941) B2267941
theorem B2015947 : Blo 2015435 2015947 := bstep (se 1 (by rfl) ⟨1511960, by rfl⟩ : syracuseStep 2015947 = 3023921) B3023921
theorem B8611109 : Blo 2015435 8611109 := bbase (se 4 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 8611109 = 1614583) (by norm_num)
theorem B5740739 : Blo 2015435 5740739 := bstep (se 1 (by rfl) ⟨4305554, by rfl⟩ : syracuseStep 5740739 = 8611109) B8611109
theorem B3827159 : Blo 2015435 3827159 := bstep (se 1 (by rfl) ⟨2870369, by rfl⟩ : syracuseStep 3827159 = 5740739) B5740739
theorem B2551439 : Blo 2015435 2551439 := bstep (se 1 (by rfl) ⟨1913579, by rfl⟩ : syracuseStep 2551439 = 3827159) B3827159
theorem B6803837 : Blo 2015435 6803837 := bstep (se 3 (by rfl) ⟨1275719, by rfl⟩ : syracuseStep 6803837 = 2551439) B2551439
theorem B4535891 : Blo 2015435 4535891 := bstep (se 1 (by rfl) ⟨3401918, by rfl⟩ : syracuseStep 4535891 = 6803837) B6803837
theorem B3023927 : Blo 2015435 3023927 := bstep (se 1 (by rfl) ⟨2267945, by rfl⟩ : syracuseStep 3023927 = 4535891) B4535891
theorem B2015951 : Blo 2015435 2015951 := bstep (se 1 (by rfl) ⟨1511963, by rfl⟩ : syracuseStep 2015951 = 3023927) B3023927
theorem B3023933 : Blo 2015435 3023933 := bbase (se 3 (by rfl) ⟨566987, by rfl⟩ : syracuseStep 3023933 = 1133975) (by norm_num)
theorem B2015955 : Blo 2015435 2015955 := bstep (se 1 (by rfl) ⟨1511966, by rfl⟩ : syracuseStep 2015955 = 3023933) B3023933
theorem B4535909 : Blo 2015435 4535909 := bbase (se 4 (by rfl) ⟨425241, by rfl⟩ : syracuseStep 4535909 = 850483) (by norm_num)
theorem B3023939 : Blo 2015435 3023939 := bstep (se 1 (by rfl) ⟨2267954, by rfl⟩ : syracuseStep 3023939 = 4535909) B4535909
theorem B2015959 : Blo 2015435 2015959 := bstep (se 1 (by rfl) ⟨1511969, by rfl⟩ : syracuseStep 2015959 = 3023939) B3023939
theorem B5102909 : Blo 2015435 5102909 := bbase (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) (by norm_num)
theorem B3401939 : Blo 2015435 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B2267959 : Blo 2015435 2267959 := bstep (se 1 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 2267959 = 3401939) B3401939
theorem B3023945 : Blo 2015435 3023945 := bstep (se 2 (by rfl) ⟨1133979, by rfl⟩ : syracuseStep 3023945 = 2267959) B2267959
theorem B2015963 : Blo 2015435 2015963 := bstep (se 1 (by rfl) ⟨1511972, by rfl⟩ : syracuseStep 2015963 = 3023945) B3023945
theorem B3827189 : Blo 2015435 3827189 := bbase (se 5 (by rfl) ⟨179399, by rfl⟩ : syracuseStep 3827189 = 358799) (by norm_num)
theorem B10205837 : Blo 2015435 10205837 := bstep (se 3 (by rfl) ⟨1913594, by rfl⟩ : syracuseStep 10205837 = 3827189) B3827189
theorem B6803891 : Blo 2015435 6803891 := bstep (se 1 (by rfl) ⟨5102918, by rfl⟩ : syracuseStep 6803891 = 10205837) B10205837
theorem B4535927 : Blo 2015435 4535927 := bstep (se 1 (by rfl) ⟨3401945, by rfl⟩ : syracuseStep 4535927 = 6803891) B6803891
theorem B3023951 : Blo 2015435 3023951 := bstep (se 1 (by rfl) ⟨2267963, by rfl⟩ : syracuseStep 3023951 = 4535927) B4535927
theorem B2015967 : Blo 2015435 2015967 := bstep (se 1 (by rfl) ⟨1511975, by rfl⟩ : syracuseStep 2015967 = 3023951) B3023951
theorem B3023957 : Blo 2015435 3023957 := bbase (se 8 (by rfl) ⟨17718, by rfl⟩ : syracuseStep 3023957 = 35437) (by norm_num)
theorem B2015971 : Blo 2015435 2015971 := bstep (se 1 (by rfl) ⟨1511978, by rfl⟩ : syracuseStep 2015971 = 3023957) B3023957
theorem B8173925 : Blo 2015435 8173925 := bbase (se 4 (by rfl) ⟨766305, by rfl⟩ : syracuseStep 8173925 = 1532611) (by norm_num)
theorem B5449283 : Blo 2015435 5449283 := bstep (se 1 (by rfl) ⟨4086962, by rfl⟩ : syracuseStep 5449283 = 8173925) B8173925
theorem B3632855 : Blo 2015435 3632855 := bstep (se 1 (by rfl) ⟨2724641, by rfl⟩ : syracuseStep 3632855 = 5449283) B5449283
theorem B9687613 : Blo 2015435 9687613 := bstep (se 3 (by rfl) ⟨1816427, by rfl⟩ : syracuseStep 9687613 = 3632855) B3632855
theorem B12916817 : Blo 2015435 12916817 := bstep (se 2 (by rfl) ⟨4843806, by rfl⟩ : syracuseStep 12916817 = 9687613) B9687613
theorem B8611211 : Blo 2015435 8611211 := bstep (se 1 (by rfl) ⟨6458408, by rfl⟩ : syracuseStep 8611211 = 12916817) B12916817
theorem B5740807 : Blo 2015435 5740807 := bstep (se 1 (by rfl) ⟨4305605, by rfl⟩ : syracuseStep 5740807 = 8611211) B8611211
theorem B7654409 : Blo 2015435 7654409 := bstep (se 2 (by rfl) ⟨2870403, by rfl⟩ : syracuseStep 7654409 = 5740807) B5740807
theorem B5102939 : Blo 2015435 5102939 := bstep (se 1 (by rfl) ⟨3827204, by rfl⟩ : syracuseStep 5102939 = 7654409) B7654409
theorem B3401959 : Blo 2015435 3401959 := bstep (se 1 (by rfl) ⟨2551469, by rfl⟩ : syracuseStep 3401959 = 5102939) B5102939
theorem B4535945 : Blo 2015435 4535945 := bstep (se 2 (by rfl) ⟨1700979, by rfl⟩ : syracuseStep 4535945 = 3401959) B3401959
theorem B3023963 : Blo 2015435 3023963 := bstep (se 1 (by rfl) ⟨2267972, by rfl⟩ : syracuseStep 3023963 = 4535945) B4535945
theorem B2015975 : Blo 2015435 2015975 := bstep (se 1 (by rfl) ⟨1511981, by rfl⟩ : syracuseStep 2015975 = 3023963) B3023963
theorem B2267977 : Blo 2015435 2267977 := bbase (se 2 (by rfl) ⟨850491, by rfl⟩ : syracuseStep 2267977 = 1700983) (by norm_num)
theorem B3023969 : Blo 2015435 3023969 := bstep (se 2 (by rfl) ⟨1133988, by rfl⟩ : syracuseStep 3023969 = 2267977) B2267977
theorem B2015979 : Blo 2015435 2015979 := bstep (se 1 (by rfl) ⟨1511984, by rfl⟩ : syracuseStep 2015979 = 3023969) B3023969
theorem B3632869 : Blo 2015435 3632869 := bbase (se 4 (by rfl) ⟨340581, by rfl⟩ : syracuseStep 3632869 = 681163) (by norm_num)
theorem B19375301 : Blo 2015435 19375301 := bstep (se 4 (by rfl) ⟨1816434, by rfl⟩ : syracuseStep 19375301 = 3632869) B3632869
theorem B12916867 : Blo 2015435 12916867 := bstep (se 1 (by rfl) ⟨9687650, by rfl⟩ : syracuseStep 12916867 = 19375301) B19375301
theorem B17222489 : Blo 2015435 17222489 := bstep (se 2 (by rfl) ⟨6458433, by rfl⟩ : syracuseStep 17222489 = 12916867) B12916867
theorem B11481659 : Blo 2015435 11481659 := bstep (se 1 (by rfl) ⟨8611244, by rfl⟩ : syracuseStep 11481659 = 17222489) B17222489
theorem B7654439 : Blo 2015435 7654439 := bstep (se 1 (by rfl) ⟨5740829, by rfl⟩ : syracuseStep 7654439 = 11481659) B11481659
theorem B5102959 : Blo 2015435 5102959 := bstep (se 1 (by rfl) ⟨3827219, by rfl⟩ : syracuseStep 5102959 = 7654439) B7654439
theorem B6803945 : Blo 2015435 6803945 := bstep (se 2 (by rfl) ⟨2551479, by rfl⟩ : syracuseStep 6803945 = 5102959) B5102959
theorem B4535963 : Blo 2015435 4535963 := bstep (se 1 (by rfl) ⟨3401972, by rfl⟩ : syracuseStep 4535963 = 6803945) B6803945
theorem B3023975 : Blo 2015435 3023975 := bstep (se 1 (by rfl) ⟨2267981, by rfl⟩ : syracuseStep 3023975 = 4535963) B4535963
theorem B2015983 : Blo 2015435 2015983 := bstep (se 1 (by rfl) ⟨1511987, by rfl⟩ : syracuseStep 2015983 = 3023975) B3023975
theorem B3023981 : Blo 2015435 3023981 := bbase (se 3 (by rfl) ⟨566996, by rfl⟩ : syracuseStep 3023981 = 1133993) (by norm_num)
theorem B2015987 : Blo 2015435 2015987 := bstep (se 1 (by rfl) ⟨1511990, by rfl⟩ : syracuseStep 2015987 = 3023981) B3023981
theorem B4535981 : Blo 2015435 4535981 := bbase (se 3 (by rfl) ⟨850496, by rfl⟩ : syracuseStep 4535981 = 1700993) (by norm_num)
theorem B3023987 : Blo 2015435 3023987 := bstep (se 1 (by rfl) ⟨2267990, by rfl⟩ : syracuseStep 3023987 = 4535981) B4535981
theorem B2015991 : Blo 2015435 2015991 := bstep (se 1 (by rfl) ⟨1511993, by rfl⟩ : syracuseStep 2015991 = 3023987) B3023987
theorem B3229237 : Blo 2015435 3229237 := bbase (se 5 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 3229237 = 302741) (by norm_num)
theorem B4305649 : Blo 2015435 4305649 := bstep (se 2 (by rfl) ⟨1614618, by rfl⟩ : syracuseStep 4305649 = 3229237) B3229237
theorem B5740865 : Blo 2015435 5740865 := bstep (se 2 (by rfl) ⟨2152824, by rfl⟩ : syracuseStep 5740865 = 4305649) B4305649
theorem B3827243 : Blo 2015435 3827243 := bstep (se 1 (by rfl) ⟨2870432, by rfl⟩ : syracuseStep 3827243 = 5740865) B5740865
theorem B2551495 : Blo 2015435 2551495 := bstep (se 1 (by rfl) ⟨1913621, by rfl⟩ : syracuseStep 2551495 = 3827243) B3827243
theorem B3401993 : Blo 2015435 3401993 := bstep (se 2 (by rfl) ⟨1275747, by rfl⟩ : syracuseStep 3401993 = 2551495) B2551495
theorem B2267995 : Blo 2015435 2267995 := bstep (se 1 (by rfl) ⟨1700996, by rfl⟩ : syracuseStep 2267995 = 3401993) B3401993
theorem B3023993 : Blo 2015435 3023993 := bstep (se 2 (by rfl) ⟨1133997, by rfl⟩ : syracuseStep 3023993 = 2267995) B2267995
theorem B2015995 : Blo 2015435 2015995 := bstep (se 1 (by rfl) ⟨1511996, by rfl⟩ : syracuseStep 2015995 = 3023993) B3023993
theorem B2043505 : Blo 2015435 2043505 := bbase (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) (by norm_num)
theorem B10898693 : Blo 2015435 10898693 := bstep (se 4 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 10898693 = 2043505) B2043505
theorem B7265795 : Blo 2015435 7265795 := bstep (se 1 (by rfl) ⟨5449346, by rfl⟩ : syracuseStep 7265795 = 10898693) B10898693
theorem B19375453 : Blo 2015435 19375453 := bstep (se 3 (by rfl) ⟨3632897, by rfl⟩ : syracuseStep 19375453 = 7265795) B7265795
theorem B25833937 : Blo 2015435 25833937 := bstep (se 2 (by rfl) ⟨9687726, by rfl⟩ : syracuseStep 25833937 = 19375453) B19375453
theorem B34445249 : Blo 2015435 34445249 := bstep (se 2 (by rfl) ⟨12916968, by rfl⟩ : syracuseStep 34445249 = 25833937) B25833937
theorem B22963499 : Blo 2015435 22963499 := bstep (se 1 (by rfl) ⟨17222624, by rfl⟩ : syracuseStep 22963499 = 34445249) B34445249
theorem B15308999 : Blo 2015435 15308999 := bstep (se 1 (by rfl) ⟨11481749, by rfl⟩ : syracuseStep 15308999 = 22963499) B22963499
theorem B10205999 : Blo 2015435 10205999 := bstep (se 1 (by rfl) ⟨7654499, by rfl⟩ : syracuseStep 10205999 = 15308999) B15308999
theorem B6803999 : Blo 2015435 6803999 := bstep (se 1 (by rfl) ⟨5102999, by rfl⟩ : syracuseStep 6803999 = 10205999) B10205999
theorem B4535999 : Blo 2015435 4535999 := bstep (se 1 (by rfl) ⟨3401999, by rfl⟩ : syracuseStep 4535999 = 6803999) B6803999
theorem B3023999 : Blo 2015435 3023999 := bstep (se 1 (by rfl) ⟨2267999, by rfl⟩ : syracuseStep 3023999 = 4535999) B4535999
theorem B2015999 : Blo 2015435 2015999 := bstep (se 1 (by rfl) ⟨1511999, by rfl⟩ : syracuseStep 2015999 = 3023999) B3023999
theorem B3024005 : Blo 2015435 3024005 := bbase (se 4 (by rfl) ⟨283500, by rfl⟩ : syracuseStep 3024005 = 567001) (by norm_num)
theorem B2016003 : Blo 2015435 2016003 := bstep (se 1 (by rfl) ⟨1512002, by rfl⟩ : syracuseStep 2016003 = 3024005) B3024005
theorem B3402013 : Blo 2015435 3402013 := bbase (se 3 (by rfl) ⟨637877, by rfl⟩ : syracuseStep 3402013 = 1275755) (by norm_num)
theorem B4536017 : Blo 2015435 4536017 := bstep (se 2 (by rfl) ⟨1701006, by rfl⟩ : syracuseStep 4536017 = 3402013) B3402013
theorem B3024011 : Blo 2015435 3024011 := bstep (se 1 (by rfl) ⟨2268008, by rfl⟩ : syracuseStep 3024011 = 4536017) B4536017
theorem B2016007 : Blo 2015435 2016007 := bstep (se 1 (by rfl) ⟨1512005, by rfl⟩ : syracuseStep 2016007 = 3024011) B3024011
theorem B2268013 : Blo 2015435 2268013 := bbase (se 3 (by rfl) ⟨425252, by rfl⟩ : syracuseStep 2268013 = 850505) (by norm_num)
theorem B3024017 : Blo 2015435 3024017 := bstep (se 2 (by rfl) ⟨1134006, by rfl⟩ : syracuseStep 3024017 = 2268013) B2268013
theorem B2016011 : Blo 2015435 2016011 := bstep (se 1 (by rfl) ⟨1512008, by rfl⟩ : syracuseStep 2016011 = 3024017) B3024017
theorem B6804053 : Blo 2015435 6804053 := bbase (se 8 (by rfl) ⟨39867, by rfl⟩ : syracuseStep 6804053 = 79735) (by norm_num)
theorem B4536035 : Blo 2015435 4536035 := bstep (se 1 (by rfl) ⟨3402026, by rfl⟩ : syracuseStep 4536035 = 6804053) B6804053
theorem B3024023 : Blo 2015435 3024023 := bstep (se 1 (by rfl) ⟨2268017, by rfl⟩ : syracuseStep 3024023 = 4536035) B4536035
theorem B2016015 : Blo 2015435 2016015 := bstep (se 1 (by rfl) ⟨1512011, by rfl⟩ : syracuseStep 2016015 = 3024023) B3024023
theorem B3024029 : Blo 2015435 3024029 := bbase (se 3 (by rfl) ⟨567005, by rfl⟩ : syracuseStep 3024029 = 1134011) (by norm_num)
theorem B2016019 : Blo 2015435 2016019 := bstep (se 1 (by rfl) ⟨1512014, by rfl⟩ : syracuseStep 2016019 = 3024029) B3024029
theorem B4536053 : Blo 2015435 4536053 := bbase (se 5 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 4536053 = 425255) (by norm_num)
theorem B3024035 : Blo 2015435 3024035 := bstep (se 1 (by rfl) ⟨2268026, by rfl⟩ : syracuseStep 3024035 = 4536053) B4536053
theorem B2016023 : Blo 2015435 2016023 := bstep (se 1 (by rfl) ⟨1512017, by rfl⟩ : syracuseStep 2016023 = 3024035) B3024035
theorem B26186773 : Blo 2015435 26186773 := bbase (se 6 (by rfl) ⟨613752, by rfl⟩ : syracuseStep 26186773 = 1227505) (by norm_num)
theorem B34915697 : Blo 2015435 34915697 := bstep (se 2 (by rfl) ⟨13093386, by rfl⟩ : syracuseStep 34915697 = 26186773) B26186773
theorem B23277131 : Blo 2015435 23277131 := bstep (se 1 (by rfl) ⟨17457848, by rfl⟩ : syracuseStep 23277131 = 34915697) B34915697
theorem B15518087 : Blo 2015435 15518087 := bstep (se 1 (by rfl) ⟨11638565, by rfl⟩ : syracuseStep 15518087 = 23277131) B23277131
theorem B10345391 : Blo 2015435 10345391 := bstep (se 1 (by rfl) ⟨7759043, by rfl⟩ : syracuseStep 10345391 = 15518087) B15518087
theorem B6896927 : Blo 2015435 6896927 := bstep (se 1 (by rfl) ⟨5172695, by rfl⟩ : syracuseStep 6896927 = 10345391) B10345391
theorem B18391805 : Blo 2015435 18391805 := bstep (se 3 (by rfl) ⟨3448463, by rfl⟩ : syracuseStep 18391805 = 6896927) B6896927
theorem B12261203 : Blo 2015435 12261203 := bstep (se 1 (by rfl) ⟨9195902, by rfl⟩ : syracuseStep 12261203 = 18391805) B18391805
theorem B8174135 : Blo 2015435 8174135 := bstep (se 1 (by rfl) ⟨6130601, by rfl⟩ : syracuseStep 8174135 = 12261203) B12261203
theorem B21797693 : Blo 2015435 21797693 := bstep (se 3 (by rfl) ⟨4087067, by rfl⟩ : syracuseStep 21797693 = 8174135) B8174135
theorem B14531795 : Blo 2015435 14531795 := bstep (se 1 (by rfl) ⟨10898846, by rfl⟩ : syracuseStep 14531795 = 21797693) B21797693
theorem B9687863 : Blo 2015435 9687863 := bstep (se 1 (by rfl) ⟨7265897, by rfl⟩ : syracuseStep 9687863 = 14531795) B14531795
theorem B25834301 : Blo 2015435 25834301 := bstep (se 3 (by rfl) ⟨4843931, by rfl⟩ : syracuseStep 25834301 = 9687863) B9687863
theorem B17222867 : Blo 2015435 17222867 := bstep (se 1 (by rfl) ⟨12917150, by rfl⟩ : syracuseStep 17222867 = 25834301) B25834301
theorem B11481911 : Blo 2015435 11481911 := bstep (se 1 (by rfl) ⟨8611433, by rfl⟩ : syracuseStep 11481911 = 17222867) B17222867
theorem B7654607 : Blo 2015435 7654607 := bstep (se 1 (by rfl) ⟨5740955, by rfl⟩ : syracuseStep 7654607 = 11481911) B11481911
theorem B5103071 : Blo 2015435 5103071 := bstep (se 1 (by rfl) ⟨3827303, by rfl⟩ : syracuseStep 5103071 = 7654607) B7654607
theorem B3402047 : Blo 2015435 3402047 := bstep (se 1 (by rfl) ⟨2551535, by rfl⟩ : syracuseStep 3402047 = 5103071) B5103071
theorem B2268031 : Blo 2015435 2268031 := bstep (se 1 (by rfl) ⟨1701023, by rfl⟩ : syracuseStep 2268031 = 3402047) B3402047
theorem B3024041 : Blo 2015435 3024041 := bstep (se 2 (by rfl) ⟨1134015, by rfl⟩ : syracuseStep 3024041 = 2268031) B2268031
theorem B2016027 : Blo 2015435 2016027 := bstep (se 1 (by rfl) ⟨1512020, by rfl⟩ : syracuseStep 2016027 = 3024041) B3024041
theorem B4305725 : Blo 2015435 4305725 := bbase (se 3 (by rfl) ⟨807323, by rfl⟩ : syracuseStep 4305725 = 1614647) (by norm_num)
theorem B2870483 : Blo 2015435 2870483 := bstep (se 1 (by rfl) ⟨2152862, by rfl⟩ : syracuseStep 2870483 = 4305725) B4305725
theorem B7654621 : Blo 2015435 7654621 := bstep (se 3 (by rfl) ⟨1435241, by rfl⟩ : syracuseStep 7654621 = 2870483) B2870483
theorem B10206161 : Blo 2015435 10206161 := bstep (se 2 (by rfl) ⟨3827310, by rfl⟩ : syracuseStep 10206161 = 7654621) B7654621
theorem B6804107 : Blo 2015435 6804107 := bstep (se 1 (by rfl) ⟨5103080, by rfl⟩ : syracuseStep 6804107 = 10206161) B10206161
theorem B4536071 : Blo 2015435 4536071 := bstep (se 1 (by rfl) ⟨3402053, by rfl⟩ : syracuseStep 4536071 = 6804107) B6804107
theorem B3024047 : Blo 2015435 3024047 := bstep (se 1 (by rfl) ⟨2268035, by rfl⟩ : syracuseStep 3024047 = 4536071) B4536071
theorem B2016031 : Blo 2015435 2016031 := bstep (se 1 (by rfl) ⟨1512023, by rfl⟩ : syracuseStep 2016031 = 3024047) B3024047
theorem B3024053 : Blo 2015435 3024053 := bbase (se 5 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 3024053 = 283505) (by norm_num)
theorem B2016035 : Blo 2015435 2016035 := bstep (se 1 (by rfl) ⟨1512026, by rfl⟩ : syracuseStep 2016035 = 3024053) B3024053
theorem B5103101 : Blo 2015435 5103101 := bbase (se 3 (by rfl) ⟨956831, by rfl⟩ : syracuseStep 5103101 = 1913663) (by norm_num)
theorem B3402067 : Blo 2015435 3402067 := bstep (se 1 (by rfl) ⟨2551550, by rfl⟩ : syracuseStep 3402067 = 5103101) B5103101
theorem B4536089 : Blo 2015435 4536089 := bstep (se 2 (by rfl) ⟨1701033, by rfl⟩ : syracuseStep 4536089 = 3402067) B3402067
theorem B3024059 : Blo 2015435 3024059 := bstep (se 1 (by rfl) ⟨2268044, by rfl⟩ : syracuseStep 3024059 = 4536089) B4536089
theorem B2016039 : Blo 2015435 2016039 := bstep (se 1 (by rfl) ⟨1512029, by rfl⟩ : syracuseStep 2016039 = 3024059) B3024059
theorem B2268049 : Blo 2015435 2268049 := bbase (se 2 (by rfl) ⟨850518, by rfl⟩ : syracuseStep 2268049 = 1701037) (by norm_num)
theorem B3024065 : Blo 2015435 3024065 := bstep (se 2 (by rfl) ⟨1134024, by rfl⟩ : syracuseStep 3024065 = 2268049) B2268049
theorem B2016043 : Blo 2015435 2016043 := bstep (se 1 (by rfl) ⟨1512032, by rfl⟩ : syracuseStep 2016043 = 3024065) B3024065
theorem B3827341 : Blo 2015435 3827341 := bbase (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) (by norm_num)
theorem B5103121 : Blo 2015435 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B6804161 : Blo 2015435 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B4536107 : Blo 2015435 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B3024071 : Blo 2015435 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B2016047 : Blo 2015435 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B3024077 : Blo 2015435 3024077 := bbase (se 3 (by rfl) ⟨567014, by rfl⟩ : syracuseStep 3024077 = 1134029) (by norm_num)
theorem B2016051 : Blo 2015435 2016051 := bstep (se 1 (by rfl) ⟨1512038, by rfl⟩ : syracuseStep 2016051 = 3024077) B3024077
theorem B4536125 : Blo 2015435 4536125 := bbase (se 3 (by rfl) ⟨850523, by rfl⟩ : syracuseStep 4536125 = 1701047) (by norm_num)
theorem B3024083 : Blo 2015435 3024083 := bstep (se 1 (by rfl) ⟨2268062, by rfl⟩ : syracuseStep 3024083 = 4536125) B4536125
theorem B2016055 : Blo 2015435 2016055 := bstep (se 1 (by rfl) ⟨1512041, by rfl⟩ : syracuseStep 2016055 = 3024083) B3024083
theorem B3402101 : Blo 2015435 3402101 := bbase (se 5 (by rfl) ⟨159473, by rfl⟩ : syracuseStep 3402101 = 318947) (by norm_num)
theorem B2268067 : Blo 2015435 2268067 := bstep (se 1 (by rfl) ⟨1701050, by rfl⟩ : syracuseStep 2268067 = 3402101) B3402101
theorem B3024089 : Blo 2015435 3024089 := bstep (se 2 (by rfl) ⟨1134033, by rfl⟩ : syracuseStep 3024089 = 2268067) B2268067
theorem B2016059 : Blo 2015435 2016059 := bstep (se 1 (by rfl) ⟨1512044, by rfl⟩ : syracuseStep 2016059 = 3024089) B3024089
theorem B2422009 : Blo 2015435 2422009 := bbase (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) (by norm_num)
theorem B3229345 : Blo 2015435 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B4305793 : Blo 2015435 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B5741057 : Blo 2015435 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B15309485 : Blo 2015435 15309485 := bstep (se 3 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 15309485 = 5741057) B5741057
theorem B10206323 : Blo 2015435 10206323 := bstep (se 1 (by rfl) ⟨7654742, by rfl⟩ : syracuseStep 10206323 = 15309485) B15309485
theorem B6804215 : Blo 2015435 6804215 := bstep (se 1 (by rfl) ⟨5103161, by rfl⟩ : syracuseStep 6804215 = 10206323) B10206323
theorem B4536143 : Blo 2015435 4536143 := bstep (se 1 (by rfl) ⟨3402107, by rfl⟩ : syracuseStep 4536143 = 6804215) B6804215
theorem B3024095 : Blo 2015435 3024095 := bstep (se 1 (by rfl) ⟨2268071, by rfl⟩ : syracuseStep 3024095 = 4536143) B4536143
theorem B2016063 : Blo 2015435 2016063 := bstep (se 1 (by rfl) ⟨1512047, by rfl⟩ : syracuseStep 2016063 = 3024095) B3024095
theorem B3024101 : Blo 2015435 3024101 := bbase (se 4 (by rfl) ⟨283509, by rfl⟩ : syracuseStep 3024101 = 567019) (by norm_num)
theorem B2016067 : Blo 2015435 2016067 := bstep (se 1 (by rfl) ⟨1512050, by rfl⟩ : syracuseStep 2016067 = 3024101) B3024101
theorem B3633029 : Blo 2015435 3633029 := bbase (se 4 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 3633029 = 681193) (by norm_num)
theorem B2422019 : Blo 2015435 2422019 := bstep (se 1 (by rfl) ⟨1816514, by rfl⟩ : syracuseStep 2422019 = 3633029) B3633029
theorem B6458717 : Blo 2015435 6458717 := bstep (se 3 (by rfl) ⟨1211009, by rfl⟩ : syracuseStep 6458717 = 2422019) B2422019
theorem B4305811 : Blo 2015435 4305811 := bstep (se 1 (by rfl) ⟨3229358, by rfl⟩ : syracuseStep 4305811 = 6458717) B6458717
theorem B5741081 : Blo 2015435 5741081 := bstep (se 2 (by rfl) ⟨2152905, by rfl⟩ : syracuseStep 5741081 = 4305811) B4305811
theorem B3827387 : Blo 2015435 3827387 := bstep (se 1 (by rfl) ⟨2870540, by rfl⟩ : syracuseStep 3827387 = 5741081) B5741081
theorem B2551591 : Blo 2015435 2551591 := bstep (se 1 (by rfl) ⟨1913693, by rfl⟩ : syracuseStep 2551591 = 3827387) B3827387
theorem B3402121 : Blo 2015435 3402121 := bstep (se 2 (by rfl) ⟨1275795, by rfl⟩ : syracuseStep 3402121 = 2551591) B2551591
theorem B4536161 : Blo 2015435 4536161 := bstep (se 2 (by rfl) ⟨1701060, by rfl⟩ : syracuseStep 4536161 = 3402121) B3402121
theorem B3024107 : Blo 2015435 3024107 := bstep (se 1 (by rfl) ⟨2268080, by rfl⟩ : syracuseStep 3024107 = 4536161) B4536161
theorem B2016071 : Blo 2015435 2016071 := bstep (se 1 (by rfl) ⟨1512053, by rfl⟩ : syracuseStep 2016071 = 3024107) B3024107
theorem B2268085 : Blo 2015435 2268085 := bbase (se 5 (by rfl) ⟨106316, by rfl⟩ : syracuseStep 2268085 = 212633) (by norm_num)
theorem B3024113 : Blo 2015435 3024113 := bstep (se 2 (by rfl) ⟨1134042, by rfl⟩ : syracuseStep 3024113 = 2268085) B2268085
theorem B2016075 : Blo 2015435 2016075 := bstep (se 1 (by rfl) ⟨1512056, by rfl⟩ : syracuseStep 2016075 = 3024113) B3024113
theorem B2551601 : Blo 2015435 2551601 := bbase (se 2 (by rfl) ⟨956850, by rfl⟩ : syracuseStep 2551601 = 1913701) (by norm_num)
theorem B6804269 : Blo 2015435 6804269 := bstep (se 3 (by rfl) ⟨1275800, by rfl⟩ : syracuseStep 6804269 = 2551601) B2551601
theorem B4536179 : Blo 2015435 4536179 := bstep (se 1 (by rfl) ⟨3402134, by rfl⟩ : syracuseStep 4536179 = 6804269) B6804269
theorem B3024119 : Blo 2015435 3024119 := bstep (se 1 (by rfl) ⟨2268089, by rfl⟩ : syracuseStep 3024119 = 4536179) B4536179
theorem B2016079 : Blo 2015435 2016079 := bstep (se 1 (by rfl) ⟨1512059, by rfl⟩ : syracuseStep 2016079 = 3024119) B3024119
theorem B3024125 : Blo 2015435 3024125 := bbase (se 3 (by rfl) ⟨567023, by rfl⟩ : syracuseStep 3024125 = 1134047) (by norm_num)
theorem B2016083 : Blo 2015435 2016083 := bstep (se 1 (by rfl) ⟨1512062, by rfl⟩ : syracuseStep 2016083 = 3024125) B3024125
theorem B4536197 : Blo 2015435 4536197 := bbase (se 4 (by rfl) ⟨425268, by rfl⟩ : syracuseStep 4536197 = 850537) (by norm_num)
theorem B3024131 : Blo 2015435 3024131 := bstep (se 1 (by rfl) ⟨2268098, by rfl⟩ : syracuseStep 3024131 = 4536197) B4536197
theorem B2016087 : Blo 2015435 2016087 := bstep (se 1 (by rfl) ⟨1512065, by rfl⟩ : syracuseStep 2016087 = 3024131) B3024131
theorem B5898869 : Blo 2015435 5898869 := bbase (se 5 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 5898869 = 553019) (by norm_num)
theorem B3932579 : Blo 2015435 3932579 := bstep (se 1 (by rfl) ⟨2949434, by rfl⟩ : syracuseStep 3932579 = 5898869) B5898869
theorem B2621719 : Blo 2015435 2621719 := bstep (se 1 (by rfl) ⟨1966289, by rfl⟩ : syracuseStep 2621719 = 3932579) B3932579
theorem B13982501 : Blo 2015435 13982501 := bstep (se 4 (by rfl) ⟨1310859, by rfl⟩ : syracuseStep 13982501 = 2621719) B2621719
theorem B37286669 : Blo 2015435 37286669 := bstep (se 3 (by rfl) ⟨6991250, by rfl⟩ : syracuseStep 37286669 = 13982501) B13982501
theorem B24857779 : Blo 2015435 24857779 := bstep (se 1 (by rfl) ⟨18643334, by rfl⟩ : syracuseStep 24857779 = 37286669) B37286669
theorem B33143705 : Blo 2015435 33143705 := bstep (se 2 (by rfl) ⟨12428889, by rfl⟩ : syracuseStep 33143705 = 24857779) B24857779
theorem B22095803 : Blo 2015435 22095803 := bstep (se 1 (by rfl) ⟨16571852, by rfl⟩ : syracuseStep 22095803 = 33143705) B33143705
theorem B14730535 : Blo 2015435 14730535 := bstep (se 1 (by rfl) ⟨11047901, by rfl⟩ : syracuseStep 14730535 = 22095803) B22095803
theorem B19640713 : Blo 2015435 19640713 := bstep (se 2 (by rfl) ⟨7365267, by rfl⟩ : syracuseStep 19640713 = 14730535) B14730535
theorem B26187617 : Blo 2015435 26187617 := bstep (se 2 (by rfl) ⟨9820356, by rfl⟩ : syracuseStep 26187617 = 19640713) B19640713
theorem B17458411 : Blo 2015435 17458411 := bstep (se 1 (by rfl) ⟨13093808, by rfl⟩ : syracuseStep 17458411 = 26187617) B26187617
theorem B23277881 : Blo 2015435 23277881 := bstep (se 2 (by rfl) ⟨8729205, by rfl⟩ : syracuseStep 23277881 = 17458411) B17458411
theorem B15518587 : Blo 2015435 15518587 := bstep (se 1 (by rfl) ⟨11638940, by rfl⟩ : syracuseStep 15518587 = 23277881) B23277881
theorem B20691449 : Blo 2015435 20691449 := bstep (se 2 (by rfl) ⟨7759293, by rfl⟩ : syracuseStep 20691449 = 15518587) B15518587
theorem B13794299 : Blo 2015435 13794299 := bstep (se 1 (by rfl) ⟨10345724, by rfl⟩ : syracuseStep 13794299 = 20691449) B20691449
theorem B9196199 : Blo 2015435 9196199 := bstep (se 1 (by rfl) ⟨6897149, by rfl⟩ : syracuseStep 9196199 = 13794299) B13794299
theorem B6130799 : Blo 2015435 6130799 := bstep (se 1 (by rfl) ⟨4598099, by rfl⟩ : syracuseStep 6130799 = 9196199) B9196199
theorem B4087199 : Blo 2015435 4087199 := bstep (se 1 (by rfl) ⟨3065399, by rfl⟩ : syracuseStep 4087199 = 6130799) B6130799
theorem B10899197 : Blo 2015435 10899197 := bstep (se 3 (by rfl) ⟨2043599, by rfl⟩ : syracuseStep 10899197 = 4087199) B4087199
theorem B7266131 : Blo 2015435 7266131 := bstep (se 1 (by rfl) ⟨5449598, by rfl⟩ : syracuseStep 7266131 = 10899197) B10899197
theorem B4844087 : Blo 2015435 4844087 := bstep (se 1 (by rfl) ⟨3633065, by rfl⟩ : syracuseStep 4844087 = 7266131) B7266131
theorem B3229391 : Blo 2015435 3229391 := bstep (se 1 (by rfl) ⟨2422043, by rfl⟩ : syracuseStep 3229391 = 4844087) B4844087
theorem B2152927 : Blo 2015435 2152927 := bstep (se 1 (by rfl) ⟨1614695, by rfl⟩ : syracuseStep 2152927 = 3229391) B3229391
theorem B2870569 : Blo 2015435 2870569 := bstep (se 2 (by rfl) ⟨1076463, by rfl⟩ : syracuseStep 2870569 = 2152927) B2152927
theorem B3827425 : Blo 2015435 3827425 := bstep (se 2 (by rfl) ⟨1435284, by rfl⟩ : syracuseStep 3827425 = 2870569) B2870569
theorem B5103233 : Blo 2015435 5103233 := bstep (se 2 (by rfl) ⟨1913712, by rfl⟩ : syracuseStep 5103233 = 3827425) B3827425
theorem B3402155 : Blo 2015435 3402155 := bstep (se 1 (by rfl) ⟨2551616, by rfl⟩ : syracuseStep 3402155 = 5103233) B5103233
theorem B2268103 : Blo 2015435 2268103 := bstep (se 1 (by rfl) ⟨1701077, by rfl⟩ : syracuseStep 2268103 = 3402155) B3402155
theorem B3024137 : Blo 2015435 3024137 := bstep (se 2 (by rfl) ⟨1134051, by rfl⟩ : syracuseStep 3024137 = 2268103) B2268103
theorem B2016091 : Blo 2015435 2016091 := bstep (se 1 (by rfl) ⟨1512068, by rfl⟩ : syracuseStep 2016091 = 3024137) B3024137
theorem B10206485 : Blo 2015435 10206485 := bbase (se 6 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 10206485 = 478429) (by norm_num)
theorem B6804323 : Blo 2015435 6804323 := bstep (se 1 (by rfl) ⟨5103242, by rfl⟩ : syracuseStep 6804323 = 10206485) B10206485
theorem B4536215 : Blo 2015435 4536215 := bstep (se 1 (by rfl) ⟨3402161, by rfl⟩ : syracuseStep 4536215 = 6804323) B6804323
theorem B3024143 : Blo 2015435 3024143 := bstep (se 1 (by rfl) ⟨2268107, by rfl⟩ : syracuseStep 3024143 = 4536215) B4536215
theorem B2016095 : Blo 2015435 2016095 := bstep (se 1 (by rfl) ⟨1512071, by rfl⟩ : syracuseStep 2016095 = 3024143) B3024143
theorem B3024149 : Blo 2015435 3024149 := bbase (se 6 (by rfl) ⟨70878, by rfl⟩ : syracuseStep 3024149 = 141757) (by norm_num)
theorem B2016099 : Blo 2015435 2016099 := bstep (se 1 (by rfl) ⟨1512074, by rfl⟩ : syracuseStep 2016099 = 3024149) B3024149
theorem B13093877 : Blo 2015435 13093877 := bbase (se 5 (by rfl) ⟨613775, by rfl⟩ : syracuseStep 13093877 = 1227551) (by norm_num)
theorem B8729251 : Blo 2015435 8729251 := bstep (se 1 (by rfl) ⟨6546938, by rfl⟩ : syracuseStep 8729251 = 13093877) B13093877
theorem B186224021 : Blo 2015435 186224021 := bstep (se 6 (by rfl) ⟨4364625, by rfl⟩ : syracuseStep 186224021 = 8729251) B8729251
theorem B124149347 : Blo 2015435 124149347 := bstep (se 1 (by rfl) ⟨93112010, by rfl⟩ : syracuseStep 124149347 = 186224021) B186224021
theorem B82766231 : Blo 2015435 82766231 := bstep (se 1 (by rfl) ⟨62074673, by rfl⟩ : syracuseStep 82766231 = 124149347) B124149347
theorem B55177487 : Blo 2015435 55177487 := bstep (se 1 (by rfl) ⟨41383115, by rfl⟩ : syracuseStep 55177487 = 82766231) B82766231
theorem B36784991 : Blo 2015435 36784991 := bstep (se 1 (by rfl) ⟨27588743, by rfl⟩ : syracuseStep 36784991 = 55177487) B55177487
theorem B24523327 : Blo 2015435 24523327 := bstep (se 1 (by rfl) ⟨18392495, by rfl⟩ : syracuseStep 24523327 = 36784991) B36784991
theorem B32697769 : Blo 2015435 32697769 := bstep (se 2 (by rfl) ⟨12261663, by rfl⟩ : syracuseStep 32697769 = 24523327) B24523327
theorem B43597025 : Blo 2015435 43597025 := bstep (se 2 (by rfl) ⟨16348884, by rfl⟩ : syracuseStep 43597025 = 32697769) B32697769
theorem B29064683 : Blo 2015435 29064683 := bstep (se 1 (by rfl) ⟨21798512, by rfl⟩ : syracuseStep 29064683 = 43597025) B43597025
theorem B19376455 : Blo 2015435 19376455 := bstep (se 1 (by rfl) ⟨14532341, by rfl⟩ : syracuseStep 19376455 = 29064683) B29064683
theorem B25835273 : Blo 2015435 25835273 := bstep (se 2 (by rfl) ⟨9688227, by rfl⟩ : syracuseStep 25835273 = 19376455) B19376455
theorem B17223515 : Blo 2015435 17223515 := bstep (se 1 (by rfl) ⟨12917636, by rfl⟩ : syracuseStep 17223515 = 25835273) B25835273
theorem B11482343 : Blo 2015435 11482343 := bstep (se 1 (by rfl) ⟨8611757, by rfl⟩ : syracuseStep 11482343 = 17223515) B17223515
theorem B7654895 : Blo 2015435 7654895 := bstep (se 1 (by rfl) ⟨5741171, by rfl⟩ : syracuseStep 7654895 = 11482343) B11482343
theorem B5103263 : Blo 2015435 5103263 := bstep (se 1 (by rfl) ⟨3827447, by rfl⟩ : syracuseStep 5103263 = 7654895) B7654895
theorem B3402175 : Blo 2015435 3402175 := bstep (se 1 (by rfl) ⟨2551631, by rfl⟩ : syracuseStep 3402175 = 5103263) B5103263
theorem B4536233 : Blo 2015435 4536233 := bstep (se 2 (by rfl) ⟨1701087, by rfl⟩ : syracuseStep 4536233 = 3402175) B3402175
theorem B3024155 : Blo 2015435 3024155 := bstep (se 1 (by rfl) ⟨2268116, by rfl⟩ : syracuseStep 3024155 = 4536233) B4536233
theorem B2016103 : Blo 2015435 2016103 := bstep (se 1 (by rfl) ⟨1512077, by rfl⟩ : syracuseStep 2016103 = 3024155) B3024155
theorem B2268121 : Blo 2015435 2268121 := bbase (se 2 (by rfl) ⟨850545, by rfl⟩ : syracuseStep 2268121 = 1701091) (by norm_num)
theorem B3024161 : Blo 2015435 3024161 := bstep (se 2 (by rfl) ⟨1134060, by rfl⟩ : syracuseStep 3024161 = 2268121) B2268121
theorem B2016107 : Blo 2015435 2016107 := bstep (se 1 (by rfl) ⟨1512080, by rfl⟩ : syracuseStep 2016107 = 3024161) B3024161
theorem B2870597 : Blo 2015435 2870597 := bbase (se 4 (by rfl) ⟨269118, by rfl⟩ : syracuseStep 2870597 = 538237) (by norm_num)
theorem B7654925 : Blo 2015435 7654925 := bstep (se 3 (by rfl) ⟨1435298, by rfl⟩ : syracuseStep 7654925 = 2870597) B2870597
theorem B5103283 : Blo 2015435 5103283 := bstep (se 1 (by rfl) ⟨3827462, by rfl⟩ : syracuseStep 5103283 = 7654925) B7654925
theorem B6804377 : Blo 2015435 6804377 := bstep (se 2 (by rfl) ⟨2551641, by rfl⟩ : syracuseStep 6804377 = 5103283) B5103283
theorem B4536251 : Blo 2015435 4536251 := bstep (se 1 (by rfl) ⟨3402188, by rfl⟩ : syracuseStep 4536251 = 6804377) B6804377
theorem B3024167 : Blo 2015435 3024167 := bstep (se 1 (by rfl) ⟨2268125, by rfl⟩ : syracuseStep 3024167 = 4536251) B4536251
theorem B2016111 : Blo 2015435 2016111 := bstep (se 1 (by rfl) ⟨1512083, by rfl⟩ : syracuseStep 2016111 = 3024167) B3024167
theorem B3024173 : Blo 2015435 3024173 := bbase (se 3 (by rfl) ⟨567032, by rfl⟩ : syracuseStep 3024173 = 1134065) (by norm_num)
theorem B2016115 : Blo 2015435 2016115 := bstep (se 1 (by rfl) ⟨1512086, by rfl⟩ : syracuseStep 2016115 = 3024173) B3024173
theorem B4536269 : Blo 2015435 4536269 := bbase (se 3 (by rfl) ⟨850550, by rfl⟩ : syracuseStep 4536269 = 1701101) (by norm_num)
theorem B3024179 : Blo 2015435 3024179 := bstep (se 1 (by rfl) ⟨2268134, by rfl⟩ : syracuseStep 3024179 = 4536269) B4536269
theorem B2016119 : Blo 2015435 2016119 := bstep (se 1 (by rfl) ⟨1512089, by rfl⟩ : syracuseStep 2016119 = 3024179) B3024179
theorem B2551657 : Blo 2015435 2551657 := bbase (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) (by norm_num)
theorem B3402209 : Blo 2015435 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B2268139 : Blo 2015435 2268139 := bstep (se 1 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 2268139 = 3402209) B3402209
theorem B3024185 : Blo 2015435 3024185 := bstep (se 2 (by rfl) ⟨1134069, by rfl⟩ : syracuseStep 3024185 = 2268139) B2268139
theorem B2016123 : Blo 2015435 2016123 := bstep (se 1 (by rfl) ⟨1512092, by rfl⟩ : syracuseStep 2016123 = 3024185) B3024185
theorem B3065453 : Blo 2015435 3065453 := bbase (se 3 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 3065453 = 1149545) (by norm_num)
theorem B2043635 : Blo 2015435 2043635 := bstep (se 1 (by rfl) ⟨1532726, by rfl⟩ : syracuseStep 2043635 = 3065453) B3065453
theorem B5449693 : Blo 2015435 5449693 := bstep (se 3 (by rfl) ⟨1021817, by rfl⟩ : syracuseStep 5449693 = 2043635) B2043635
theorem B7266257 : Blo 2015435 7266257 := bstep (se 2 (by rfl) ⟨2724846, by rfl⟩ : syracuseStep 7266257 = 5449693) B5449693
theorem B4844171 : Blo 2015435 4844171 := bstep (se 1 (by rfl) ⟨3633128, by rfl⟩ : syracuseStep 4844171 = 7266257) B7266257
theorem B12917789 : Blo 2015435 12917789 := bstep (se 3 (by rfl) ⟨2422085, by rfl⟩ : syracuseStep 12917789 = 4844171) B4844171
theorem B8611859 : Blo 2015435 8611859 := bstep (se 1 (by rfl) ⟨6458894, by rfl⟩ : syracuseStep 8611859 = 12917789) B12917789
theorem B22964957 : Blo 2015435 22964957 := bstep (se 3 (by rfl) ⟨4305929, by rfl⟩ : syracuseStep 22964957 = 8611859) B8611859
theorem B15309971 : Blo 2015435 15309971 := bstep (se 1 (by rfl) ⟨11482478, by rfl⟩ : syracuseStep 15309971 = 22964957) B22964957
theorem B10206647 : Blo 2015435 10206647 := bstep (se 1 (by rfl) ⟨7654985, by rfl⟩ : syracuseStep 10206647 = 15309971) B15309971
theorem B6804431 : Blo 2015435 6804431 := bstep (se 1 (by rfl) ⟨5103323, by rfl⟩ : syracuseStep 6804431 = 10206647) B10206647
theorem B4536287 : Blo 2015435 4536287 := bstep (se 1 (by rfl) ⟨3402215, by rfl⟩ : syracuseStep 4536287 = 6804431) B6804431
theorem B3024191 : Blo 2015435 3024191 := bstep (se 1 (by rfl) ⟨2268143, by rfl⟩ : syracuseStep 3024191 = 4536287) B4536287
theorem B2016127 : Blo 2015435 2016127 := bstep (se 1 (by rfl) ⟨1512095, by rfl⟩ : syracuseStep 2016127 = 3024191) B3024191
theorem B3024197 : Blo 2015435 3024197 := bbase (se 4 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 3024197 = 567037) (by norm_num)
theorem B2016131 : Blo 2015435 2016131 := bstep (se 1 (by rfl) ⟨1512098, by rfl⟩ : syracuseStep 2016131 = 3024197) B3024197
theorem B3402229 : Blo 2015435 3402229 := bbase (se 5 (by rfl) ⟨159479, by rfl⟩ : syracuseStep 3402229 = 318959) (by norm_num)
theorem B4536305 : Blo 2015435 4536305 := bstep (se 2 (by rfl) ⟨1701114, by rfl⟩ : syracuseStep 4536305 = 3402229) B3402229
theorem B3024203 : Blo 2015435 3024203 := bstep (se 1 (by rfl) ⟨2268152, by rfl⟩ : syracuseStep 3024203 = 4536305) B4536305
theorem B2016135 : Blo 2015435 2016135 := bstep (se 1 (by rfl) ⟨1512101, by rfl⟩ : syracuseStep 2016135 = 3024203) B3024203
theorem B2268157 : Blo 2015435 2268157 := bbase (se 3 (by rfl) ⟨425279, by rfl⟩ : syracuseStep 2268157 = 850559) (by norm_num)
theorem B3024209 : Blo 2015435 3024209 := bstep (se 2 (by rfl) ⟨1134078, by rfl⟩ : syracuseStep 3024209 = 2268157) B2268157
theorem B2016139 : Blo 2015435 2016139 := bstep (se 1 (by rfl) ⟨1512104, by rfl⟩ : syracuseStep 2016139 = 3024209) B3024209
theorem B6804485 : Blo 2015435 6804485 := bbase (se 4 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 6804485 = 1275841) (by norm_num)
theorem B4536323 : Blo 2015435 4536323 := bstep (se 1 (by rfl) ⟨3402242, by rfl⟩ : syracuseStep 4536323 = 6804485) B6804485
theorem B3024215 : Blo 2015435 3024215 := bstep (se 1 (by rfl) ⟨2268161, by rfl⟩ : syracuseStep 3024215 = 4536323) B4536323
theorem B2016143 : Blo 2015435 2016143 := bstep (se 1 (by rfl) ⟨1512107, by rfl⟩ : syracuseStep 2016143 = 3024215) B3024215
theorem B3024221 : Blo 2015435 3024221 := bbase (se 3 (by rfl) ⟨567041, by rfl⟩ : syracuseStep 3024221 = 1134083) (by norm_num)
theorem B2016147 : Blo 2015435 2016147 := bstep (se 1 (by rfl) ⟨1512110, by rfl⟩ : syracuseStep 2016147 = 3024221) B3024221
theorem B4536341 : Blo 2015435 4536341 := bbase (se 6 (by rfl) ⟨106320, by rfl⟩ : syracuseStep 4536341 = 212641) (by norm_num)
theorem B3024227 : Blo 2015435 3024227 := bstep (se 1 (by rfl) ⟨2268170, by rfl⟩ : syracuseStep 3024227 = 4536341) B4536341
theorem B2016151 : Blo 2015435 2016151 := bstep (se 1 (by rfl) ⟨1512113, by rfl⟩ : syracuseStep 2016151 = 3024227) B3024227
theorem B7655093 : Blo 2015435 7655093 := bbase (se 5 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 7655093 = 717665) (by norm_num)
theorem B5103395 : Blo 2015435 5103395 := bstep (se 1 (by rfl) ⟨3827546, by rfl⟩ : syracuseStep 5103395 = 7655093) B7655093
theorem B3402263 : Blo 2015435 3402263 := bstep (se 1 (by rfl) ⟨2551697, by rfl⟩ : syracuseStep 3402263 = 5103395) B5103395
theorem B2268175 : Blo 2015435 2268175 := bstep (se 1 (by rfl) ⟨1701131, by rfl⟩ : syracuseStep 2268175 = 3402263) B3402263
theorem B3024233 : Blo 2015435 3024233 := bstep (se 2 (by rfl) ⟨1134087, by rfl⟩ : syracuseStep 3024233 = 2268175) B2268175
theorem B2016155 : Blo 2015435 2016155 := bstep (se 1 (by rfl) ⟨1512116, by rfl⟩ : syracuseStep 2016155 = 3024233) B3024233
theorem B5449781 : Blo 2015435 5449781 := bbase (se 5 (by rfl) ⟨255458, by rfl⟩ : syracuseStep 5449781 = 510917) (by norm_num)
theorem B3633187 : Blo 2015435 3633187 := bstep (se 1 (by rfl) ⟨2724890, by rfl⟩ : syracuseStep 3633187 = 5449781) B5449781
theorem B4844249 : Blo 2015435 4844249 := bstep (se 2 (by rfl) ⟨1816593, by rfl⟩ : syracuseStep 4844249 = 3633187) B3633187
theorem B3229499 : Blo 2015435 3229499 := bstep (se 1 (by rfl) ⟨2422124, by rfl⟩ : syracuseStep 3229499 = 4844249) B4844249
theorem B2152999 : Blo 2015435 2152999 := bstep (se 1 (by rfl) ⟨1614749, by rfl⟩ : syracuseStep 2152999 = 3229499) B3229499
theorem B11482661 : Blo 2015435 11482661 := bstep (se 4 (by rfl) ⟨1076499, by rfl⟩ : syracuseStep 11482661 = 2152999) B2152999
theorem B7655107 : Blo 2015435 7655107 := bstep (se 1 (by rfl) ⟨5741330, by rfl⟩ : syracuseStep 7655107 = 11482661) B11482661
theorem B10206809 : Blo 2015435 10206809 := bstep (se 2 (by rfl) ⟨3827553, by rfl⟩ : syracuseStep 10206809 = 7655107) B7655107
theorem B6804539 : Blo 2015435 6804539 := bstep (se 1 (by rfl) ⟨5103404, by rfl⟩ : syracuseStep 6804539 = 10206809) B10206809
theorem B4536359 : Blo 2015435 4536359 := bstep (se 1 (by rfl) ⟨3402269, by rfl⟩ : syracuseStep 4536359 = 6804539) B6804539
theorem B3024239 : Blo 2015435 3024239 := bstep (se 1 (by rfl) ⟨2268179, by rfl⟩ : syracuseStep 3024239 = 4536359) B4536359
theorem B2016159 : Blo 2015435 2016159 := bstep (se 1 (by rfl) ⟨1512119, by rfl⟩ : syracuseStep 2016159 = 3024239) B3024239
theorem B3024245 : Blo 2015435 3024245 := bbase (se 5 (by rfl) ⟨141761, by rfl⟩ : syracuseStep 3024245 = 283523) (by norm_num)
theorem B2016163 : Blo 2015435 2016163 := bstep (se 1 (by rfl) ⟨1512122, by rfl⟩ : syracuseStep 2016163 = 3024245) B3024245
theorem B2870677 : Blo 2015435 2870677 := bbase (se 6 (by rfl) ⟨67281, by rfl⟩ : syracuseStep 2870677 = 134563) (by norm_num)
theorem B3827569 : Blo 2015435 3827569 := bstep (se 2 (by rfl) ⟨1435338, by rfl⟩ : syracuseStep 3827569 = 2870677) B2870677
theorem B5103425 : Blo 2015435 5103425 := bstep (se 2 (by rfl) ⟨1913784, by rfl⟩ : syracuseStep 5103425 = 3827569) B3827569
theorem B3402283 : Blo 2015435 3402283 := bstep (se 1 (by rfl) ⟨2551712, by rfl⟩ : syracuseStep 3402283 = 5103425) B5103425
theorem B4536377 : Blo 2015435 4536377 := bstep (se 2 (by rfl) ⟨1701141, by rfl⟩ : syracuseStep 4536377 = 3402283) B3402283
theorem B3024251 : Blo 2015435 3024251 := bstep (se 1 (by rfl) ⟨2268188, by rfl⟩ : syracuseStep 3024251 = 4536377) B4536377
theorem B2016167 : Blo 2015435 2016167 := bstep (se 1 (by rfl) ⟨1512125, by rfl⟩ : syracuseStep 2016167 = 3024251) B3024251
theorem B2268193 : Blo 2015435 2268193 := bbase (se 2 (by rfl) ⟨850572, by rfl⟩ : syracuseStep 2268193 = 1701145) (by norm_num)
theorem B3024257 : Blo 2015435 3024257 := bstep (se 2 (by rfl) ⟨1134096, by rfl⟩ : syracuseStep 3024257 = 2268193) B2268193
theorem B2016171 : Blo 2015435 2016171 := bstep (se 1 (by rfl) ⟨1512128, by rfl⟩ : syracuseStep 2016171 = 3024257) B3024257
theorem B5103445 : Blo 2015435 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B6804593 : Blo 2015435 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B4536395 : Blo 2015435 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B3024263 : Blo 2015435 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B2016175 : Blo 2015435 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B3024269 : Blo 2015435 3024269 := bbase (se 3 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 3024269 = 1134101) (by norm_num)
theorem B2016179 : Blo 2015435 2016179 := bstep (se 1 (by rfl) ⟨1512134, by rfl⟩ : syracuseStep 2016179 = 3024269) B3024269
theorem B4536413 : Blo 2015435 4536413 := bbase (se 3 (by rfl) ⟨850577, by rfl⟩ : syracuseStep 4536413 = 1701155) (by norm_num)
theorem B3024275 : Blo 2015435 3024275 := bstep (se 1 (by rfl) ⟨2268206, by rfl⟩ : syracuseStep 3024275 = 4536413) B4536413
theorem B2016183 : Blo 2015435 2016183 := bstep (se 1 (by rfl) ⟨1512137, by rfl⟩ : syracuseStep 2016183 = 3024275) B3024275
theorem B3402317 : Blo 2015435 3402317 := bbase (se 3 (by rfl) ⟨637934, by rfl⟩ : syracuseStep 3402317 = 1275869) (by norm_num)
theorem B2268211 : Blo 2015435 2268211 := bstep (se 1 (by rfl) ⟨1701158, by rfl⟩ : syracuseStep 2268211 = 3402317) B3402317
theorem B3024281 : Blo 2015435 3024281 := bstep (se 2 (by rfl) ⟨1134105, by rfl⟩ : syracuseStep 3024281 = 2268211) B2268211
theorem B2016187 : Blo 2015435 2016187 := bstep (se 1 (by rfl) ⟨1512140, by rfl⟩ : syracuseStep 2016187 = 3024281) B3024281
theorem B13273109 : Blo 2015435 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B8848739 : Blo 2015435 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B5899159 : Blo 2015435 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B31462181 : Blo 2015435 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B20974787 : Blo 2015435 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B13983191 : Blo 2015435 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B9322127 : Blo 2015435 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B6214751 : Blo 2015435 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B4143167 : Blo 2015435 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B2762111 : Blo 2015435 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B7365629 : Blo 2015435 7365629 := bstep (se 3 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 7365629 = 2762111) B2762111
theorem B4910419 : Blo 2015435 4910419 := bstep (se 1 (by rfl) ⟨3682814, by rfl⟩ : syracuseStep 4910419 = 7365629) B7365629
theorem B6547225 : Blo 2015435 6547225 := bstep (se 2 (by rfl) ⟨2455209, by rfl⟩ : syracuseStep 6547225 = 4910419) B4910419
theorem B8729633 : Blo 2015435 8729633 := bstep (se 2 (by rfl) ⟨3273612, by rfl⟩ : syracuseStep 8729633 = 6547225) B6547225
theorem B23279021 : Blo 2015435 23279021 := bstep (se 3 (by rfl) ⟨4364816, by rfl⟩ : syracuseStep 23279021 = 8729633) B8729633
theorem B15519347 : Blo 2015435 15519347 := bstep (se 1 (by rfl) ⟨11639510, by rfl⟩ : syracuseStep 15519347 = 23279021) B23279021
theorem B10346231 : Blo 2015435 10346231 := bstep (se 1 (by rfl) ⟨7759673, by rfl⟩ : syracuseStep 10346231 = 15519347) B15519347
theorem B6897487 : Blo 2015435 6897487 := bstep (se 1 (by rfl) ⟨5173115, by rfl⟩ : syracuseStep 6897487 = 10346231) B10346231
theorem B9196649 : Blo 2015435 9196649 := bstep (se 2 (by rfl) ⟨3448743, by rfl⟩ : syracuseStep 9196649 = 6897487) B6897487
theorem B6131099 : Blo 2015435 6131099 := bstep (se 1 (by rfl) ⟨4598324, by rfl⟩ : syracuseStep 6131099 = 9196649) B9196649
theorem B16349597 : Blo 2015435 16349597 := bstep (se 3 (by rfl) ⟨3065549, by rfl⟩ : syracuseStep 16349597 = 6131099) B6131099
theorem B10899731 : Blo 2015435 10899731 := bstep (se 1 (by rfl) ⟨8174798, by rfl⟩ : syracuseStep 10899731 = 16349597) B16349597
theorem B29065949 : Blo 2015435 29065949 := bstep (se 3 (by rfl) ⟨5449865, by rfl⟩ : syracuseStep 29065949 = 10899731) B10899731
theorem B19377299 : Blo 2015435 19377299 := bstep (se 1 (by rfl) ⟨14532974, by rfl⟩ : syracuseStep 19377299 = 29065949) B29065949
theorem B12918199 : Blo 2015435 12918199 := bstep (se 1 (by rfl) ⟨9688649, by rfl⟩ : syracuseStep 12918199 = 19377299) B19377299
theorem B17224265 : Blo 2015435 17224265 := bstep (se 2 (by rfl) ⟨6459099, by rfl⟩ : syracuseStep 17224265 = 12918199) B12918199
theorem B11482843 : Blo 2015435 11482843 := bstep (se 1 (by rfl) ⟨8612132, by rfl⟩ : syracuseStep 11482843 = 17224265) B17224265
theorem B15310457 : Blo 2015435 15310457 := bstep (se 2 (by rfl) ⟨5741421, by rfl⟩ : syracuseStep 15310457 = 11482843) B11482843
theorem B10206971 : Blo 2015435 10206971 := bstep (se 1 (by rfl) ⟨7655228, by rfl⟩ : syracuseStep 10206971 = 15310457) B15310457
theorem B6804647 : Blo 2015435 6804647 := bstep (se 1 (by rfl) ⟨5103485, by rfl⟩ : syracuseStep 6804647 = 10206971) B10206971
theorem B4536431 : Blo 2015435 4536431 := bstep (se 1 (by rfl) ⟨3402323, by rfl⟩ : syracuseStep 4536431 = 6804647) B6804647
theorem B3024287 : Blo 2015435 3024287 := bstep (se 1 (by rfl) ⟨2268215, by rfl⟩ : syracuseStep 3024287 = 4536431) B4536431
theorem B2016191 : Blo 2015435 2016191 := bstep (se 1 (by rfl) ⟨1512143, by rfl⟩ : syracuseStep 2016191 = 3024287) B3024287
theorem B3024293 : Blo 2015435 3024293 := bbase (se 4 (by rfl) ⟨283527, by rfl⟩ : syracuseStep 3024293 = 567055) (by norm_num)
theorem B2016195 : Blo 2015435 2016195 := bstep (se 1 (by rfl) ⟨1512146, by rfl⟩ : syracuseStep 2016195 = 3024293) B3024293
theorem B2551753 : Blo 2015435 2551753 := bbase (se 2 (by rfl) ⟨956907, by rfl⟩ : syracuseStep 2551753 = 1913815) (by norm_num)
theorem B3402337 : Blo 2015435 3402337 := bstep (se 2 (by rfl) ⟨1275876, by rfl⟩ : syracuseStep 3402337 = 2551753) B2551753
theorem B4536449 : Blo 2015435 4536449 := bstep (se 2 (by rfl) ⟨1701168, by rfl⟩ : syracuseStep 4536449 = 3402337) B3402337
theorem B3024299 : Blo 2015435 3024299 := bstep (se 1 (by rfl) ⟨2268224, by rfl⟩ : syracuseStep 3024299 = 4536449) B4536449
theorem B2016199 : Blo 2015435 2016199 := bstep (se 1 (by rfl) ⟨1512149, by rfl⟩ : syracuseStep 2016199 = 3024299) B3024299
theorem B2268229 : Blo 2015435 2268229 := bbase (se 4 (by rfl) ⟨212646, by rfl⟩ : syracuseStep 2268229 = 425293) (by norm_num)
theorem B3024305 : Blo 2015435 3024305 := bstep (se 2 (by rfl) ⟨1134114, by rfl⟩ : syracuseStep 3024305 = 2268229) B2268229
theorem B2016203 : Blo 2015435 2016203 := bstep (se 1 (by rfl) ⟨1512152, by rfl⟩ : syracuseStep 2016203 = 3024305) B3024305
theorem B3827645 : Blo 2015435 3827645 := bbase (se 3 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 3827645 = 1435367) (by norm_num)
theorem B2551763 : Blo 2015435 2551763 := bstep (se 1 (by rfl) ⟨1913822, by rfl⟩ : syracuseStep 2551763 = 3827645) B3827645
theorem B6804701 : Blo 2015435 6804701 := bstep (se 3 (by rfl) ⟨1275881, by rfl⟩ : syracuseStep 6804701 = 2551763) B2551763
theorem B4536467 : Blo 2015435 4536467 := bstep (se 1 (by rfl) ⟨3402350, by rfl⟩ : syracuseStep 4536467 = 6804701) B6804701
theorem B3024311 : Blo 2015435 3024311 := bstep (se 1 (by rfl) ⟨2268233, by rfl⟩ : syracuseStep 3024311 = 4536467) B4536467
theorem B2016207 : Blo 2015435 2016207 := bstep (se 1 (by rfl) ⟨1512155, by rfl⟩ : syracuseStep 2016207 = 3024311) B3024311
theorem B3024317 : Blo 2015435 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2016211 : Blo 2015435 2016211 := bstep (se 1 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 2016211 = 3024317) B3024317
theorem B4536485 : Blo 2015435 4536485 := bbase (se 4 (by rfl) ⟨425295, by rfl⟩ : syracuseStep 4536485 = 850591) (by norm_num)
theorem B3024323 : Blo 2015435 3024323 := bstep (se 1 (by rfl) ⟨2268242, by rfl⟩ : syracuseStep 3024323 = 4536485) B4536485
theorem B2016215 : Blo 2015435 2016215 := bstep (se 1 (by rfl) ⟨1512161, by rfl⟩ : syracuseStep 2016215 = 3024323) B3024323
theorem B5103557 : Blo 2015435 5103557 := bbase (se 4 (by rfl) ⟨478458, by rfl⟩ : syracuseStep 5103557 = 956917) (by norm_num)
theorem B3402371 : Blo 2015435 3402371 := bstep (se 1 (by rfl) ⟨2551778, by rfl⟩ : syracuseStep 3402371 = 5103557) B5103557
theorem B2268247 : Blo 2015435 2268247 := bstep (se 1 (by rfl) ⟨1701185, by rfl⟩ : syracuseStep 2268247 = 3402371) B3402371
theorem B3024329 : Blo 2015435 3024329 := bstep (se 2 (by rfl) ⟨1134123, by rfl⟩ : syracuseStep 3024329 = 2268247) B2268247
theorem B2016219 : Blo 2015435 2016219 := bstep (se 1 (by rfl) ⟨1512164, by rfl⟩ : syracuseStep 2016219 = 3024329) B3024329
theorem B9688805 : Blo 2015435 9688805 := bbase (se 4 (by rfl) ⟨908325, by rfl⟩ : syracuseStep 9688805 = 1816651) (by norm_num)
theorem B6459203 : Blo 2015435 6459203 := bstep (se 1 (by rfl) ⟨4844402, by rfl⟩ : syracuseStep 6459203 = 9688805) B9688805
theorem B4306135 : Blo 2015435 4306135 := bstep (se 1 (by rfl) ⟨3229601, by rfl⟩ : syracuseStep 4306135 = 6459203) B6459203
theorem B5741513 : Blo 2015435 5741513 := bstep (se 2 (by rfl) ⟨2153067, by rfl⟩ : syracuseStep 5741513 = 4306135) B4306135
theorem B3827675 : Blo 2015435 3827675 := bstep (se 1 (by rfl) ⟨2870756, by rfl⟩ : syracuseStep 3827675 = 5741513) B5741513
theorem B10207133 : Blo 2015435 10207133 := bstep (se 3 (by rfl) ⟨1913837, by rfl⟩ : syracuseStep 10207133 = 3827675) B3827675
theorem B6804755 : Blo 2015435 6804755 := bstep (se 1 (by rfl) ⟨5103566, by rfl⟩ : syracuseStep 6804755 = 10207133) B10207133
theorem B4536503 : Blo 2015435 4536503 := bstep (se 1 (by rfl) ⟨3402377, by rfl⟩ : syracuseStep 4536503 = 6804755) B6804755
theorem B3024335 : Blo 2015435 3024335 := bstep (se 1 (by rfl) ⟨2268251, by rfl⟩ : syracuseStep 3024335 = 4536503) B4536503
theorem B2016223 : Blo 2015435 2016223 := bstep (se 1 (by rfl) ⟨1512167, by rfl⟩ : syracuseStep 2016223 = 3024335) B3024335
theorem B3024341 : Blo 2015435 3024341 := bbase (se 7 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 3024341 = 70883) (by norm_num)
theorem B2016227 : Blo 2015435 2016227 := bstep (se 1 (by rfl) ⟨1512170, by rfl⟩ : syracuseStep 2016227 = 3024341) B3024341
theorem B7655381 : Blo 2015435 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B5103587 : Blo 2015435 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B3402391 : Blo 2015435 3402391 := bstep (se 1 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 3402391 = 5103587) B5103587
theorem B4536521 : Blo 2015435 4536521 := bstep (se 2 (by rfl) ⟨1701195, by rfl⟩ : syracuseStep 4536521 = 3402391) B3402391
theorem B3024347 : Blo 2015435 3024347 := bstep (se 1 (by rfl) ⟨2268260, by rfl⟩ : syracuseStep 3024347 = 4536521) B4536521
theorem B2016231 : Blo 2015435 2016231 := bstep (se 1 (by rfl) ⟨1512173, by rfl⟩ : syracuseStep 2016231 = 3024347) B3024347
theorem B2268265 : Blo 2015435 2268265 := bbase (se 2 (by rfl) ⟨850599, by rfl⟩ : syracuseStep 2268265 = 1701199) (by norm_num)
theorem B3024353 : Blo 2015435 3024353 := bstep (se 2 (by rfl) ⟨1134132, by rfl⟩ : syracuseStep 3024353 = 2268265) B2268265
theorem B2016235 : Blo 2015435 2016235 := bstep (se 1 (by rfl) ⟨1512176, by rfl⟩ : syracuseStep 2016235 = 3024353) B3024353
theorem B2043749 : Blo 2015435 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B5449997 : Blo 2015435 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B3633331 : Blo 2015435 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B4844441 : Blo 2015435 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B3229627 : Blo 2015435 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B4306169 : Blo 2015435 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B11483117 : Blo 2015435 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B7655411 : Blo 2015435 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B5103607 : Blo 2015435 5103607 := bstep (se 1 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 5103607 = 7655411) B7655411
theorem B6804809 : Blo 2015435 6804809 := bstep (se 2 (by rfl) ⟨2551803, by rfl⟩ : syracuseStep 6804809 = 5103607) B5103607
theorem B4536539 : Blo 2015435 4536539 := bstep (se 1 (by rfl) ⟨3402404, by rfl⟩ : syracuseStep 4536539 = 6804809) B6804809
theorem B3024359 : Blo 2015435 3024359 := bstep (se 1 (by rfl) ⟨2268269, by rfl⟩ : syracuseStep 3024359 = 4536539) B4536539
theorem B2016239 : Blo 2015435 2016239 := bstep (se 1 (by rfl) ⟨1512179, by rfl⟩ : syracuseStep 2016239 = 3024359) B3024359
theorem B3024365 : Blo 2015435 3024365 := bbase (se 3 (by rfl) ⟨567068, by rfl⟩ : syracuseStep 3024365 = 1134137) (by norm_num)
theorem B2016243 : Blo 2015435 2016243 := bstep (se 1 (by rfl) ⟨1512182, by rfl⟩ : syracuseStep 2016243 = 3024365) B3024365
theorem B4536557 : Blo 2015435 4536557 := bbase (se 3 (by rfl) ⟨850604, by rfl⟩ : syracuseStep 4536557 = 1701209) (by norm_num)
theorem B3024371 : Blo 2015435 3024371 := bstep (se 1 (by rfl) ⟨2268278, by rfl⟩ : syracuseStep 3024371 = 4536557) B4536557
theorem B2016247 : Blo 2015435 2016247 := bstep (se 1 (by rfl) ⟨1512185, by rfl⟩ : syracuseStep 2016247 = 3024371) B3024371
theorem B2870797 : Blo 2015435 2870797 := bbase (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) (by norm_num)
theorem B3827729 : Blo 2015435 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B2551819 : Blo 2015435 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B3402425 : Blo 2015435 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2268283 : Blo 2015435 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B3024377 : Blo 2015435 3024377 := bstep (se 2 (by rfl) ⟨1134141, by rfl⟩ : syracuseStep 3024377 = 2268283) B2268283
theorem B2016251 : Blo 2015435 2016251 := bstep (se 1 (by rfl) ⟨1512188, by rfl⟩ : syracuseStep 2016251 = 3024377) B3024377
theorem B3448853 : Blo 2015435 3448853 := bbase (se 6 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 3448853 = 161665) (by norm_num)
theorem B2299235 : Blo 2015435 2299235 := bstep (se 1 (by rfl) ⟨1724426, by rfl⟩ : syracuseStep 2299235 = 3448853) B3448853
theorem B24525173 : Blo 2015435 24525173 := bstep (se 5 (by rfl) ⟨1149617, by rfl⟩ : syracuseStep 24525173 = 2299235) B2299235
theorem B16350115 : Blo 2015435 16350115 := bstep (se 1 (by rfl) ⟨12262586, by rfl⟩ : syracuseStep 16350115 = 24525173) B24525173
theorem B21800153 : Blo 2015435 21800153 := bstep (se 2 (by rfl) ⟨8175057, by rfl⟩ : syracuseStep 21800153 = 16350115) B16350115
theorem B14533435 : Blo 2015435 14533435 := bstep (se 1 (by rfl) ⟨10900076, by rfl⟩ : syracuseStep 14533435 = 21800153) B21800153
theorem B77511653 : Blo 2015435 77511653 := bstep (se 4 (by rfl) ⟨7266717, by rfl⟩ : syracuseStep 77511653 = 14533435) B14533435
theorem B51674435 : Blo 2015435 51674435 := bstep (se 1 (by rfl) ⟨38755826, by rfl⟩ : syracuseStep 51674435 = 77511653) B77511653
theorem B34449623 : Blo 2015435 34449623 := bstep (se 1 (by rfl) ⟨25837217, by rfl⟩ : syracuseStep 34449623 = 51674435) B51674435
theorem B22966415 : Blo 2015435 22966415 := bstep (se 1 (by rfl) ⟨17224811, by rfl⟩ : syracuseStep 22966415 = 34449623) B34449623
theorem B15310943 : Blo 2015435 15310943 := bstep (se 1 (by rfl) ⟨11483207, by rfl⟩ : syracuseStep 15310943 = 22966415) B22966415
theorem B10207295 : Blo 2015435 10207295 := bstep (se 1 (by rfl) ⟨7655471, by rfl⟩ : syracuseStep 10207295 = 15310943) B15310943
theorem B6804863 : Blo 2015435 6804863 := bstep (se 1 (by rfl) ⟨5103647, by rfl⟩ : syracuseStep 6804863 = 10207295) B10207295
theorem B4536575 : Blo 2015435 4536575 := bstep (se 1 (by rfl) ⟨3402431, by rfl⟩ : syracuseStep 4536575 = 6804863) B6804863
theorem B3024383 : Blo 2015435 3024383 := bstep (se 1 (by rfl) ⟨2268287, by rfl⟩ : syracuseStep 3024383 = 4536575) B4536575
theorem B2016255 : Blo 2015435 2016255 := bstep (se 1 (by rfl) ⟨1512191, by rfl⟩ : syracuseStep 2016255 = 3024383) B3024383
theorem B3024389 : Blo 2015435 3024389 := bbase (se 4 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 3024389 = 567073) (by norm_num)
theorem B2016259 : Blo 2015435 2016259 := bstep (se 1 (by rfl) ⟨1512194, by rfl⟩ : syracuseStep 2016259 = 3024389) B3024389
theorem B3402445 : Blo 2015435 3402445 := bbase (se 3 (by rfl) ⟨637958, by rfl⟩ : syracuseStep 3402445 = 1275917) (by norm_num)
theorem B4536593 : Blo 2015435 4536593 := bstep (se 2 (by rfl) ⟨1701222, by rfl⟩ : syracuseStep 4536593 = 3402445) B3402445
theorem B3024395 : Blo 2015435 3024395 := bstep (se 1 (by rfl) ⟨2268296, by rfl⟩ : syracuseStep 3024395 = 4536593) B4536593
theorem B2016263 : Blo 2015435 2016263 := bstep (se 1 (by rfl) ⟨1512197, by rfl⟩ : syracuseStep 2016263 = 3024395) B3024395
theorem B2268301 : Blo 2015435 2268301 := bbase (se 3 (by rfl) ⟨425306, by rfl⟩ : syracuseStep 2268301 = 850613) (by norm_num)
theorem B3024401 : Blo 2015435 3024401 := bstep (se 2 (by rfl) ⟨1134150, by rfl⟩ : syracuseStep 3024401 = 2268301) B2268301
theorem B2016267 : Blo 2015435 2016267 := bstep (se 1 (by rfl) ⟨1512200, by rfl⟩ : syracuseStep 2016267 = 3024401) B3024401
theorem B6804917 : Blo 2015435 6804917 := bbase (se 5 (by rfl) ⟨318980, by rfl⟩ : syracuseStep 6804917 = 637961) (by norm_num)
theorem B4536611 : Blo 2015435 4536611 := bstep (se 1 (by rfl) ⟨3402458, by rfl⟩ : syracuseStep 4536611 = 6804917) B6804917
theorem B3024407 : Blo 2015435 3024407 := bstep (se 1 (by rfl) ⟨2268305, by rfl⟩ : syracuseStep 3024407 = 4536611) B4536611
theorem B2016271 : Blo 2015435 2016271 := bstep (se 1 (by rfl) ⟨1512203, by rfl⟩ : syracuseStep 2016271 = 3024407) B3024407
theorem B3024413 : Blo 2015435 3024413 := bbase (se 3 (by rfl) ⟨567077, by rfl⟩ : syracuseStep 3024413 = 1134155) (by norm_num)
theorem B2016275 : Blo 2015435 2016275 := bstep (se 1 (by rfl) ⟨1512206, by rfl⟩ : syracuseStep 2016275 = 3024413) B3024413
theorem B4536629 : Blo 2015435 4536629 := bbase (se 5 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 4536629 = 425309) (by norm_num)
theorem B3024419 : Blo 2015435 3024419 := bstep (se 1 (by rfl) ⟨2268314, by rfl⟩ : syracuseStep 3024419 = 4536629) B4536629
theorem B2016279 : Blo 2015435 2016279 := bstep (se 1 (by rfl) ⟨1512209, by rfl⟩ : syracuseStep 2016279 = 3024419) B3024419
theorem B8175173 : Blo 2015435 8175173 := bbase (se 4 (by rfl) ⟨766422, by rfl⟩ : syracuseStep 8175173 = 1532845) (by norm_num)
theorem B21800461 : Blo 2015435 21800461 := bstep (se 3 (by rfl) ⟨4087586, by rfl⟩ : syracuseStep 21800461 = 8175173) B8175173
theorem B29067281 : Blo 2015435 29067281 := bstep (se 2 (by rfl) ⟨10900230, by rfl⟩ : syracuseStep 29067281 = 21800461) B21800461
theorem B19378187 : Blo 2015435 19378187 := bstep (se 1 (by rfl) ⟨14533640, by rfl⟩ : syracuseStep 19378187 = 29067281) B29067281
theorem B12918791 : Blo 2015435 12918791 := bstep (se 1 (by rfl) ⟨9689093, by rfl⟩ : syracuseStep 12918791 = 19378187) B19378187
theorem B8612527 : Blo 2015435 8612527 := bstep (se 1 (by rfl) ⟨6459395, by rfl⟩ : syracuseStep 8612527 = 12918791) B12918791
theorem B11483369 : Blo 2015435 11483369 := bstep (se 2 (by rfl) ⟨4306263, by rfl⟩ : syracuseStep 11483369 = 8612527) B8612527
theorem B7655579 : Blo 2015435 7655579 := bstep (se 1 (by rfl) ⟨5741684, by rfl⟩ : syracuseStep 7655579 = 11483369) B11483369
theorem B5103719 : Blo 2015435 5103719 := bstep (se 1 (by rfl) ⟨3827789, by rfl⟩ : syracuseStep 5103719 = 7655579) B7655579
theorem B3402479 : Blo 2015435 3402479 := bstep (se 1 (by rfl) ⟨2551859, by rfl⟩ : syracuseStep 3402479 = 5103719) B5103719
theorem B2268319 : Blo 2015435 2268319 := bstep (se 1 (by rfl) ⟨1701239, by rfl⟩ : syracuseStep 2268319 = 3402479) B3402479
theorem B3024425 : Blo 2015435 3024425 := bstep (se 2 (by rfl) ⟨1134159, by rfl⟩ : syracuseStep 3024425 = 2268319) B2268319
theorem B2016283 : Blo 2015435 2016283 := bstep (se 1 (by rfl) ⟨1512212, by rfl⟩ : syracuseStep 2016283 = 3024425) B3024425
theorem B113397077 : Blo 2015435 113397077 := bbase (se 11 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 113397077 = 166109) (by norm_num)
theorem B75598051 : Blo 2015435 75598051 := bstep (se 1 (by rfl) ⟨56698538, by rfl⟩ : syracuseStep 75598051 = 113397077) B113397077
theorem B100797401 : Blo 2015435 100797401 := bstep (se 2 (by rfl) ⟨37799025, by rfl⟩ : syracuseStep 100797401 = 75598051) B75598051
theorem B67198267 : Blo 2015435 67198267 := bstep (se 1 (by rfl) ⟨50398700, by rfl⟩ : syracuseStep 67198267 = 100797401) B100797401
theorem B358390757 : Blo 2015435 358390757 := bstep (se 4 (by rfl) ⟨33599133, by rfl⟩ : syracuseStep 358390757 = 67198267) B67198267
theorem B238927171 : Blo 2015435 238927171 := bstep (se 1 (by rfl) ⟨179195378, by rfl⟩ : syracuseStep 238927171 = 358390757) B358390757
theorem B318569561 : Blo 2015435 318569561 := bstep (se 2 (by rfl) ⟨119463585, by rfl⟩ : syracuseStep 318569561 = 238927171) B238927171
theorem B212379707 : Blo 2015435 212379707 := bstep (se 1 (by rfl) ⟨159284780, by rfl⟩ : syracuseStep 212379707 = 318569561) B318569561
theorem B141586471 : Blo 2015435 141586471 := bstep (se 1 (by rfl) ⟨106189853, by rfl⟩ : syracuseStep 141586471 = 212379707) B212379707
theorem B188781961 : Blo 2015435 188781961 := bstep (se 2 (by rfl) ⟨70793235, by rfl⟩ : syracuseStep 188781961 = 141586471) B141586471
theorem B251709281 : Blo 2015435 251709281 := bstep (se 2 (by rfl) ⟨94390980, by rfl⟩ : syracuseStep 251709281 = 188781961) B188781961
theorem B167806187 : Blo 2015435 167806187 := bstep (se 1 (by rfl) ⟨125854640, by rfl⟩ : syracuseStep 167806187 = 251709281) B251709281
theorem B111870791 : Blo 2015435 111870791 := bstep (se 1 (by rfl) ⟨83903093, by rfl⟩ : syracuseStep 111870791 = 167806187) B167806187
theorem B74580527 : Blo 2015435 74580527 := bstep (se 1 (by rfl) ⟨55935395, by rfl⟩ : syracuseStep 74580527 = 111870791) B111870791
theorem B198881405 : Blo 2015435 198881405 := bstep (se 3 (by rfl) ⟨37290263, by rfl⟩ : syracuseStep 198881405 = 74580527) B74580527
theorem B132587603 : Blo 2015435 132587603 := bstep (se 1 (by rfl) ⟨99440702, by rfl⟩ : syracuseStep 132587603 = 198881405) B198881405
theorem B88391735 : Blo 2015435 88391735 := bstep (se 1 (by rfl) ⟨66293801, by rfl⟩ : syracuseStep 88391735 = 132587603) B132587603
theorem B58927823 : Blo 2015435 58927823 := bstep (se 1 (by rfl) ⟨44195867, by rfl⟩ : syracuseStep 58927823 = 88391735) B88391735
theorem B39285215 : Blo 2015435 39285215 := bstep (se 1 (by rfl) ⟨29463911, by rfl⟩ : syracuseStep 39285215 = 58927823) B58927823
theorem B26190143 : Blo 2015435 26190143 := bstep (se 1 (by rfl) ⟨19642607, by rfl⟩ : syracuseStep 26190143 = 39285215) B39285215
theorem B17460095 : Blo 2015435 17460095 := bstep (se 1 (by rfl) ⟨13095071, by rfl⟩ : syracuseStep 17460095 = 26190143) B26190143
theorem B46560253 : Blo 2015435 46560253 := bstep (se 3 (by rfl) ⟨8730047, by rfl⟩ : syracuseStep 46560253 = 17460095) B17460095
theorem B62080337 : Blo 2015435 62080337 := bstep (se 2 (by rfl) ⟨23280126, by rfl⟩ : syracuseStep 62080337 = 46560253) B46560253
theorem B41386891 : Blo 2015435 41386891 := bstep (se 1 (by rfl) ⟨31040168, by rfl⟩ : syracuseStep 41386891 = 62080337) B62080337
theorem B55182521 : Blo 2015435 55182521 := bstep (se 2 (by rfl) ⟨20693445, by rfl⟩ : syracuseStep 55182521 = 41386891) B41386891
theorem B36788347 : Blo 2015435 36788347 := bstep (se 1 (by rfl) ⟨27591260, by rfl⟩ : syracuseStep 36788347 = 55182521) B55182521
theorem B49051129 : Blo 2015435 49051129 := bstep (se 2 (by rfl) ⟨18394173, by rfl⟩ : syracuseStep 49051129 = 36788347) B36788347
theorem B65401505 : Blo 2015435 65401505 := bstep (se 2 (by rfl) ⟨24525564, by rfl⟩ : syracuseStep 65401505 = 49051129) B49051129
theorem B43601003 : Blo 2015435 43601003 := bstep (se 1 (by rfl) ⟨32700752, by rfl⟩ : syracuseStep 43601003 = 65401505) B65401505
theorem B29067335 : Blo 2015435 29067335 := bstep (se 1 (by rfl) ⟨21800501, by rfl⟩ : syracuseStep 29067335 = 43601003) B43601003
theorem B19378223 : Blo 2015435 19378223 := bstep (se 1 (by rfl) ⟨14533667, by rfl⟩ : syracuseStep 19378223 = 29067335) B29067335
theorem B12918815 : Blo 2015435 12918815 := bstep (se 1 (by rfl) ⟨9689111, by rfl⟩ : syracuseStep 12918815 = 19378223) B19378223
theorem B8612543 : Blo 2015435 8612543 := bstep (se 1 (by rfl) ⟨6459407, by rfl⟩ : syracuseStep 8612543 = 12918815) B12918815
theorem B5741695 : Blo 2015435 5741695 := bstep (se 1 (by rfl) ⟨4306271, by rfl⟩ : syracuseStep 5741695 = 8612543) B8612543
theorem B7655593 : Blo 2015435 7655593 := bstep (se 2 (by rfl) ⟨2870847, by rfl⟩ : syracuseStep 7655593 = 5741695) B5741695
theorem B10207457 : Blo 2015435 10207457 := bstep (se 2 (by rfl) ⟨3827796, by rfl⟩ : syracuseStep 10207457 = 7655593) B7655593
theorem B6804971 : Blo 2015435 6804971 := bstep (se 1 (by rfl) ⟨5103728, by rfl⟩ : syracuseStep 6804971 = 10207457) B10207457
theorem B4536647 : Blo 2015435 4536647 := bstep (se 1 (by rfl) ⟨3402485, by rfl⟩ : syracuseStep 4536647 = 6804971) B6804971
theorem B3024431 : Blo 2015435 3024431 := bstep (se 1 (by rfl) ⟨2268323, by rfl⟩ : syracuseStep 3024431 = 4536647) B4536647
theorem B2016287 : Blo 2015435 2016287 := bstep (se 1 (by rfl) ⟨1512215, by rfl⟩ : syracuseStep 2016287 = 3024431) B3024431
theorem B3024437 : Blo 2015435 3024437 := bbase (se 5 (by rfl) ⟨141770, by rfl⟩ : syracuseStep 3024437 = 283541) (by norm_num)
theorem B2016291 : Blo 2015435 2016291 := bstep (se 1 (by rfl) ⟨1512218, by rfl⟩ : syracuseStep 2016291 = 3024437) B3024437
theorem B5103749 : Blo 2015435 5103749 := bbase (se 4 (by rfl) ⟨478476, by rfl⟩ : syracuseStep 5103749 = 956953) (by norm_num)
theorem B3402499 : Blo 2015435 3402499 := bstep (se 1 (by rfl) ⟨2551874, by rfl⟩ : syracuseStep 3402499 = 5103749) B5103749
theorem B4536665 : Blo 2015435 4536665 := bstep (se 2 (by rfl) ⟨1701249, by rfl⟩ : syracuseStep 4536665 = 3402499) B3402499
theorem B3024443 : Blo 2015435 3024443 := bstep (se 1 (by rfl) ⟨2268332, by rfl⟩ : syracuseStep 3024443 = 4536665) B4536665
theorem B2016295 : Blo 2015435 2016295 := bstep (se 1 (by rfl) ⟨1512221, by rfl⟩ : syracuseStep 2016295 = 3024443) B3024443
theorem B2268337 : Blo 2015435 2268337 := bbase (se 2 (by rfl) ⟨850626, by rfl⟩ : syracuseStep 2268337 = 1701253) (by norm_num)
theorem B3024449 : Blo 2015435 3024449 := bstep (se 2 (by rfl) ⟨1134168, by rfl⟩ : syracuseStep 3024449 = 2268337) B2268337
theorem B2016299 : Blo 2015435 2016299 := bstep (se 1 (by rfl) ⟨1512224, by rfl⟩ : syracuseStep 2016299 = 3024449) B3024449
theorem B2153153 : Blo 2015435 2153153 := bbase (se 2 (by rfl) ⟨807432, by rfl⟩ : syracuseStep 2153153 = 1614865) (by norm_num)
theorem B5741741 : Blo 2015435 5741741 := bstep (se 3 (by rfl) ⟨1076576, by rfl⟩ : syracuseStep 5741741 = 2153153) B2153153
theorem B3827827 : Blo 2015435 3827827 := bstep (se 1 (by rfl) ⟨2870870, by rfl⟩ : syracuseStep 3827827 = 5741741) B5741741
theorem B5103769 : Blo 2015435 5103769 := bstep (se 2 (by rfl) ⟨1913913, by rfl⟩ : syracuseStep 5103769 = 3827827) B3827827
theorem B6805025 : Blo 2015435 6805025 := bstep (se 2 (by rfl) ⟨2551884, by rfl⟩ : syracuseStep 6805025 = 5103769) B5103769
theorem B4536683 : Blo 2015435 4536683 := bstep (se 1 (by rfl) ⟨3402512, by rfl⟩ : syracuseStep 4536683 = 6805025) B6805025
theorem B3024455 : Blo 2015435 3024455 := bstep (se 1 (by rfl) ⟨2268341, by rfl⟩ : syracuseStep 3024455 = 4536683) B4536683
theorem B2016303 : Blo 2015435 2016303 := bstep (se 1 (by rfl) ⟨1512227, by rfl⟩ : syracuseStep 2016303 = 3024455) B3024455
theorem B3024461 : Blo 2015435 3024461 := bbase (se 3 (by rfl) ⟨567086, by rfl⟩ : syracuseStep 3024461 = 1134173) (by norm_num)
theorem B2016307 : Blo 2015435 2016307 := bstep (se 1 (by rfl) ⟨1512230, by rfl⟩ : syracuseStep 2016307 = 3024461) B3024461
theorem B4536701 : Blo 2015435 4536701 := bbase (se 3 (by rfl) ⟨850631, by rfl⟩ : syracuseStep 4536701 = 1701263) (by norm_num)
theorem B3024467 : Blo 2015435 3024467 := bstep (se 1 (by rfl) ⟨2268350, by rfl⟩ : syracuseStep 3024467 = 4536701) B4536701
theorem B2016311 : Blo 2015435 2016311 := bstep (se 1 (by rfl) ⟨1512233, by rfl⟩ : syracuseStep 2016311 = 3024467) B3024467
theorem B3402533 : Blo 2015435 3402533 := bbase (se 4 (by rfl) ⟨318987, by rfl⟩ : syracuseStep 3402533 = 637975) (by norm_num)
theorem B2268355 : Blo 2015435 2268355 := bstep (se 1 (by rfl) ⟨1701266, by rfl⟩ : syracuseStep 2268355 = 3402533) B3402533
theorem B3024473 : Blo 2015435 3024473 := bstep (se 2 (by rfl) ⟨1134177, by rfl⟩ : syracuseStep 3024473 = 2268355) B2268355
theorem B2016315 : Blo 2015435 2016315 := bstep (se 1 (by rfl) ⟨1512236, by rfl⟩ : syracuseStep 2016315 = 3024473) B3024473
theorem B2870893 : Blo 2015435 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B15311429 : Blo 2015435 15311429 := bstep (se 4 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 15311429 = 2870893) B2870893
theorem B10207619 : Blo 2015435 10207619 := bstep (se 1 (by rfl) ⟨7655714, by rfl⟩ : syracuseStep 10207619 = 15311429) B15311429
theorem B6805079 : Blo 2015435 6805079 := bstep (se 1 (by rfl) ⟨5103809, by rfl⟩ : syracuseStep 6805079 = 10207619) B10207619
theorem B4536719 : Blo 2015435 4536719 := bstep (se 1 (by rfl) ⟨3402539, by rfl⟩ : syracuseStep 4536719 = 6805079) B6805079
theorem B3024479 : Blo 2015435 3024479 := bstep (se 1 (by rfl) ⟨2268359, by rfl⟩ : syracuseStep 3024479 = 4536719) B4536719
theorem B2016319 : Blo 2015435 2016319 := bstep (se 1 (by rfl) ⟨1512239, by rfl⟩ : syracuseStep 2016319 = 3024479) B3024479
theorem B3024485 : Blo 2015435 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B2016323 : Blo 2015435 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B7366133 : Blo 2015435 7366133 := bbase (se 5 (by rfl) ⟨345287, by rfl⟩ : syracuseStep 7366133 = 690575) (by norm_num)
theorem B4910755 : Blo 2015435 4910755 := bstep (se 1 (by rfl) ⟨3683066, by rfl⟩ : syracuseStep 4910755 = 7366133) B7366133
theorem B6547673 : Blo 2015435 6547673 := bstep (se 2 (by rfl) ⟨2455377, by rfl⟩ : syracuseStep 6547673 = 4910755) B4910755
theorem B17460461 : Blo 2015435 17460461 := bstep (se 3 (by rfl) ⟨3273836, by rfl⟩ : syracuseStep 17460461 = 6547673) B6547673
theorem B11640307 : Blo 2015435 11640307 := bstep (se 1 (by rfl) ⟨8730230, by rfl⟩ : syracuseStep 11640307 = 17460461) B17460461
theorem B15520409 : Blo 2015435 15520409 := bstep (se 2 (by rfl) ⟨5820153, by rfl⟩ : syracuseStep 15520409 = 11640307) B11640307
theorem B10346939 : Blo 2015435 10346939 := bstep (se 1 (by rfl) ⟨7760204, by rfl⟩ : syracuseStep 10346939 = 15520409) B15520409
theorem B6897959 : Blo 2015435 6897959 := bstep (se 1 (by rfl) ⟨5173469, by rfl⟩ : syracuseStep 6897959 = 10346939) B10346939
theorem B4598639 : Blo 2015435 4598639 := bstep (se 1 (by rfl) ⟨3448979, by rfl⟩ : syracuseStep 4598639 = 6897959) B6897959
theorem B3065759 : Blo 2015435 3065759 := bstep (se 1 (by rfl) ⟨2299319, by rfl⟩ : syracuseStep 3065759 = 4598639) B4598639
theorem B2043839 : Blo 2015435 2043839 := bstep (se 1 (by rfl) ⟨1532879, by rfl⟩ : syracuseStep 2043839 = 3065759) B3065759
theorem B5450237 : Blo 2015435 5450237 := bstep (se 3 (by rfl) ⟨1021919, by rfl⟩ : syracuseStep 5450237 = 2043839) B2043839
theorem B3633491 : Blo 2015435 3633491 := bstep (se 1 (by rfl) ⟨2725118, by rfl⟩ : syracuseStep 3633491 = 5450237) B5450237
theorem B2422327 : Blo 2015435 2422327 := bstep (se 1 (by rfl) ⟨1816745, by rfl⟩ : syracuseStep 2422327 = 3633491) B3633491
theorem B3229769 : Blo 2015435 3229769 := bstep (se 2 (by rfl) ⟨1211163, by rfl⟩ : syracuseStep 3229769 = 2422327) B2422327
theorem B2153179 : Blo 2015435 2153179 := bstep (se 1 (by rfl) ⟨1614884, by rfl⟩ : syracuseStep 2153179 = 3229769) B3229769
theorem B2870905 : Blo 2015435 2870905 := bstep (se 2 (by rfl) ⟨1076589, by rfl⟩ : syracuseStep 2870905 = 2153179) B2153179
theorem B3827873 : Blo 2015435 3827873 := bstep (se 2 (by rfl) ⟨1435452, by rfl⟩ : syracuseStep 3827873 = 2870905) B2870905
theorem B2551915 : Blo 2015435 2551915 := bstep (se 1 (by rfl) ⟨1913936, by rfl⟩ : syracuseStep 2551915 = 3827873) B3827873
theorem B3402553 : Blo 2015435 3402553 := bstep (se 2 (by rfl) ⟨1275957, by rfl⟩ : syracuseStep 3402553 = 2551915) B2551915
theorem B4536737 : Blo 2015435 4536737 := bstep (se 2 (by rfl) ⟨1701276, by rfl⟩ : syracuseStep 4536737 = 3402553) B3402553
theorem B3024491 : Blo 2015435 3024491 := bstep (se 1 (by rfl) ⟨2268368, by rfl⟩ : syracuseStep 3024491 = 4536737) B4536737
theorem B2016327 : Blo 2015435 2016327 := bstep (se 1 (by rfl) ⟨1512245, by rfl⟩ : syracuseStep 2016327 = 3024491) B3024491
theorem B2268373 : Blo 2015435 2268373 := bbase (se 7 (by rfl) ⟨26582, by rfl⟩ : syracuseStep 2268373 = 53165) (by norm_num)
theorem B3024497 : Blo 2015435 3024497 := bstep (se 2 (by rfl) ⟨1134186, by rfl⟩ : syracuseStep 3024497 = 2268373) B2268373
theorem B2016331 : Blo 2015435 2016331 := bstep (se 1 (by rfl) ⟨1512248, by rfl⟩ : syracuseStep 2016331 = 3024497) B3024497
theorem B2551925 : Blo 2015435 2551925 := bbase (se 5 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 2551925 = 239243) (by norm_num)
theorem B6805133 : Blo 2015435 6805133 := bstep (se 3 (by rfl) ⟨1275962, by rfl⟩ : syracuseStep 6805133 = 2551925) B2551925
theorem B4536755 : Blo 2015435 4536755 := bstep (se 1 (by rfl) ⟨3402566, by rfl⟩ : syracuseStep 4536755 = 6805133) B6805133
theorem B3024503 : Blo 2015435 3024503 := bstep (se 1 (by rfl) ⟨2268377, by rfl⟩ : syracuseStep 3024503 = 4536755) B4536755
theorem B2016335 : Blo 2015435 2016335 := bstep (se 1 (by rfl) ⟨1512251, by rfl⟩ : syracuseStep 2016335 = 3024503) B3024503
theorem B3024509 : Blo 2015435 3024509 := bbase (se 3 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 3024509 = 1134191) (by norm_num)
theorem B2016339 : Blo 2015435 2016339 := bstep (se 1 (by rfl) ⟨1512254, by rfl⟩ : syracuseStep 2016339 = 3024509) B3024509
theorem B4536773 : Blo 2015435 4536773 := bbase (se 4 (by rfl) ⟨425322, by rfl⟩ : syracuseStep 4536773 = 850645) (by norm_num)
theorem B3024515 : Blo 2015435 3024515 := bstep (se 1 (by rfl) ⟨2268386, by rfl⟩ : syracuseStep 3024515 = 4536773) B4536773
theorem B2016343 : Blo 2015435 2016343 := bstep (se 1 (by rfl) ⟨1512257, by rfl⟩ : syracuseStep 2016343 = 3024515) B3024515
theorem B4844701 : Blo 2015435 4844701 := bbase (se 3 (by rfl) ⟨908381, by rfl⟩ : syracuseStep 4844701 = 1816763) (by norm_num)
theorem B6459601 : Blo 2015435 6459601 := bstep (se 2 (by rfl) ⟨2422350, by rfl⟩ : syracuseStep 6459601 = 4844701) B4844701
theorem B8612801 : Blo 2015435 8612801 := bstep (se 2 (by rfl) ⟨3229800, by rfl⟩ : syracuseStep 8612801 = 6459601) B6459601
theorem B5741867 : Blo 2015435 5741867 := bstep (se 1 (by rfl) ⟨4306400, by rfl⟩ : syracuseStep 5741867 = 8612801) B8612801
theorem B3827911 : Blo 2015435 3827911 := bstep (se 1 (by rfl) ⟨2870933, by rfl⟩ : syracuseStep 3827911 = 5741867) B5741867
theorem B5103881 : Blo 2015435 5103881 := bstep (se 2 (by rfl) ⟨1913955, by rfl⟩ : syracuseStep 5103881 = 3827911) B3827911
theorem B3402587 : Blo 2015435 3402587 := bstep (se 1 (by rfl) ⟨2551940, by rfl⟩ : syracuseStep 3402587 = 5103881) B5103881
theorem B2268391 : Blo 2015435 2268391 := bstep (se 1 (by rfl) ⟨1701293, by rfl⟩ : syracuseStep 2268391 = 3402587) B3402587
theorem B3024521 : Blo 2015435 3024521 := bstep (se 2 (by rfl) ⟨1134195, by rfl⟩ : syracuseStep 3024521 = 2268391) B2268391
theorem B2016347 : Blo 2015435 2016347 := bstep (se 1 (by rfl) ⟨1512260, by rfl⟩ : syracuseStep 2016347 = 3024521) B3024521
theorem B10207781 : Blo 2015435 10207781 := bbase (se 4 (by rfl) ⟨956979, by rfl⟩ : syracuseStep 10207781 = 1913959) (by norm_num)
theorem B6805187 : Blo 2015435 6805187 := bstep (se 1 (by rfl) ⟨5103890, by rfl⟩ : syracuseStep 6805187 = 10207781) B10207781
theorem B4536791 : Blo 2015435 4536791 := bstep (se 1 (by rfl) ⟨3402593, by rfl⟩ : syracuseStep 4536791 = 6805187) B6805187
theorem B3024527 : Blo 2015435 3024527 := bstep (se 1 (by rfl) ⟨2268395, by rfl⟩ : syracuseStep 3024527 = 4536791) B4536791
theorem B2016351 : Blo 2015435 2016351 := bstep (se 1 (by rfl) ⟨1512263, by rfl⟩ : syracuseStep 2016351 = 3024527) B3024527
theorem B3024533 : Blo 2015435 3024533 := bbase (se 6 (by rfl) ⟨70887, by rfl⟩ : syracuseStep 3024533 = 141775) (by norm_num)
theorem B2016355 : Blo 2015435 2016355 := bstep (se 1 (by rfl) ⟨1512266, by rfl⟩ : syracuseStep 2016355 = 3024533) B3024533
theorem B4087741 : Blo 2015435 4087741 := bbase (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) (by norm_num)
theorem B5450321 : Blo 2015435 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B3633547 : Blo 2015435 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B4844729 : Blo 2015435 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B12919277 : Blo 2015435 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B8612851 : Blo 2015435 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B11483801 : Blo 2015435 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B7655867 : Blo 2015435 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B5103911 : Blo 2015435 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B3402607 : Blo 2015435 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B4536809 : Blo 2015435 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B3024539 : Blo 2015435 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B2016359 : Blo 2015435 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B2268409 : Blo 2015435 2268409 := bbase (se 2 (by rfl) ⟨850653, by rfl⟩ : syracuseStep 2268409 = 1701307) (by norm_num)
theorem B3024545 : Blo 2015435 3024545 := bstep (se 2 (by rfl) ⟨1134204, by rfl⟩ : syracuseStep 3024545 = 2268409) B2268409
theorem B2016363 : Blo 2015435 2016363 := bstep (se 1 (by rfl) ⟨1512272, by rfl⟩ : syracuseStep 2016363 = 3024545) B3024545
theorem B8612885 : Blo 2015435 8612885 := bbase (se 6 (by rfl) ⟨201864, by rfl⟩ : syracuseStep 8612885 = 403729) (by norm_num)
theorem B5741923 : Blo 2015435 5741923 := bstep (se 1 (by rfl) ⟨4306442, by rfl⟩ : syracuseStep 5741923 = 8612885) B8612885
theorem B7655897 : Blo 2015435 7655897 := bstep (se 2 (by rfl) ⟨2870961, by rfl⟩ : syracuseStep 7655897 = 5741923) B5741923
theorem B5103931 : Blo 2015435 5103931 := bstep (se 1 (by rfl) ⟨3827948, by rfl⟩ : syracuseStep 5103931 = 7655897) B7655897
theorem B6805241 : Blo 2015435 6805241 := bstep (se 2 (by rfl) ⟨2551965, by rfl⟩ : syracuseStep 6805241 = 5103931) B5103931
theorem B4536827 : Blo 2015435 4536827 := bstep (se 1 (by rfl) ⟨3402620, by rfl⟩ : syracuseStep 4536827 = 6805241) B6805241
theorem B3024551 : Blo 2015435 3024551 := bstep (se 1 (by rfl) ⟨2268413, by rfl⟩ : syracuseStep 3024551 = 4536827) B4536827
theorem B2016367 : Blo 2015435 2016367 := bstep (se 1 (by rfl) ⟨1512275, by rfl⟩ : syracuseStep 2016367 = 3024551) B3024551
theorem B3024557 : Blo 2015435 3024557 := bbase (se 3 (by rfl) ⟨567104, by rfl⟩ : syracuseStep 3024557 = 1134209) (by norm_num)
theorem B2016371 : Blo 2015435 2016371 := bstep (se 1 (by rfl) ⟨1512278, by rfl⟩ : syracuseStep 2016371 = 3024557) B3024557
theorem B4536845 : Blo 2015435 4536845 := bbase (se 3 (by rfl) ⟨850658, by rfl⟩ : syracuseStep 4536845 = 1701317) (by norm_num)
theorem B3024563 : Blo 2015435 3024563 := bstep (se 1 (by rfl) ⟨2268422, by rfl⟩ : syracuseStep 3024563 = 4536845) B4536845
theorem B2016375 : Blo 2015435 2016375 := bstep (se 1 (by rfl) ⟨1512281, by rfl⟩ : syracuseStep 2016375 = 3024563) B3024563
theorem B2551981 : Blo 2015435 2551981 := bbase (se 3 (by rfl) ⟨478496, by rfl⟩ : syracuseStep 2551981 = 956993) (by norm_num)
theorem B3402641 : Blo 2015435 3402641 := bstep (se 2 (by rfl) ⟨1275990, by rfl⟩ : syracuseStep 3402641 = 2551981) B2551981
theorem B2268427 : Blo 2015435 2268427 := bstep (se 1 (by rfl) ⟨1701320, by rfl⟩ : syracuseStep 2268427 = 3402641) B3402641
theorem B3024569 : Blo 2015435 3024569 := bstep (se 2 (by rfl) ⟨1134213, by rfl⟩ : syracuseStep 3024569 = 2268427) B2268427
theorem B2016379 : Blo 2015435 2016379 := bstep (se 1 (by rfl) ⟨1512284, by rfl⟩ : syracuseStep 2016379 = 3024569) B3024569
theorem B2422393 : Blo 2015435 2422393 := bbase (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) (by norm_num)
theorem B12919429 : Blo 2015435 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B17225905 : Blo 2015435 17225905 := bstep (se 2 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 17225905 = 12919429) B12919429
theorem B22967873 : Blo 2015435 22967873 := bstep (se 2 (by rfl) ⟨8612952, by rfl⟩ : syracuseStep 22967873 = 17225905) B17225905
theorem B15311915 : Blo 2015435 15311915 := bstep (se 1 (by rfl) ⟨11483936, by rfl⟩ : syracuseStep 15311915 = 22967873) B22967873
theorem B10207943 : Blo 2015435 10207943 := bstep (se 1 (by rfl) ⟨7655957, by rfl⟩ : syracuseStep 10207943 = 15311915) B15311915
theorem B6805295 : Blo 2015435 6805295 := bstep (se 1 (by rfl) ⟨5103971, by rfl⟩ : syracuseStep 6805295 = 10207943) B10207943
theorem B4536863 : Blo 2015435 4536863 := bstep (se 1 (by rfl) ⟨3402647, by rfl⟩ : syracuseStep 4536863 = 6805295) B6805295
theorem B3024575 : Blo 2015435 3024575 := bstep (se 1 (by rfl) ⟨2268431, by rfl⟩ : syracuseStep 3024575 = 4536863) B4536863
theorem B2016383 : Blo 2015435 2016383 := bstep (se 1 (by rfl) ⟨1512287, by rfl⟩ : syracuseStep 2016383 = 3024575) B3024575
theorem B3024581 : Blo 2015435 3024581 := bbase (se 4 (by rfl) ⟨283554, by rfl⟩ : syracuseStep 3024581 = 567109) (by norm_num)
theorem B2016387 : Blo 2015435 2016387 := bstep (se 1 (by rfl) ⟨1512290, by rfl⟩ : syracuseStep 2016387 = 3024581) B3024581
theorem B3402661 : Blo 2015435 3402661 := bbase (se 4 (by rfl) ⟨318999, by rfl⟩ : syracuseStep 3402661 = 637999) (by norm_num)
theorem B4536881 : Blo 2015435 4536881 := bstep (se 2 (by rfl) ⟨1701330, by rfl⟩ : syracuseStep 4536881 = 3402661) B3402661
theorem B3024587 : Blo 2015435 3024587 := bstep (se 1 (by rfl) ⟨2268440, by rfl⟩ : syracuseStep 3024587 = 4536881) B4536881
theorem B2016391 : Blo 2015435 2016391 := bstep (se 1 (by rfl) ⟨1512293, by rfl⟩ : syracuseStep 2016391 = 3024587) B3024587
theorem B2268445 : Blo 2015435 2268445 := bbase (se 3 (by rfl) ⟨425333, by rfl⟩ : syracuseStep 2268445 = 850667) (by norm_num)
theorem B3024593 : Blo 2015435 3024593 := bstep (se 2 (by rfl) ⟨1134222, by rfl⟩ : syracuseStep 3024593 = 2268445) B2268445
theorem B2016395 : Blo 2015435 2016395 := bstep (se 1 (by rfl) ⟨1512296, by rfl⟩ : syracuseStep 2016395 = 3024593) B3024593
theorem B6805349 : Blo 2015435 6805349 := bbase (se 4 (by rfl) ⟨638001, by rfl⟩ : syracuseStep 6805349 = 1276003) (by norm_num)
theorem B4536899 : Blo 2015435 4536899 := bstep (se 1 (by rfl) ⟨3402674, by rfl⟩ : syracuseStep 4536899 = 6805349) B6805349
theorem B3024599 : Blo 2015435 3024599 := bstep (se 1 (by rfl) ⟨2268449, by rfl⟩ : syracuseStep 3024599 = 4536899) B4536899
theorem B2016399 : Blo 2015435 2016399 := bstep (se 1 (by rfl) ⟨1512299, by rfl⟩ : syracuseStep 2016399 = 3024599) B3024599
theorem B3024605 : Blo 2015435 3024605 := bbase (se 3 (by rfl) ⟨567113, by rfl⟩ : syracuseStep 3024605 = 1134227) (by norm_num)
theorem B2016403 : Blo 2015435 2016403 := bstep (se 1 (by rfl) ⟨1512302, by rfl⟩ : syracuseStep 2016403 = 3024605) B3024605
theorem B4536917 : Blo 2015435 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B3024611 : Blo 2015435 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B2016407 : Blo 2015435 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B10347365 : Blo 2015435 10347365 := bbase (se 4 (by rfl) ⟨970065, by rfl⟩ : syracuseStep 10347365 = 1940131) (by norm_num)
theorem B6898243 : Blo 2015435 6898243 := bstep (se 1 (by rfl) ⟨5173682, by rfl⟩ : syracuseStep 6898243 = 10347365) B10347365
theorem B9197657 : Blo 2015435 9197657 := bstep (se 2 (by rfl) ⟨3449121, by rfl⟩ : syracuseStep 9197657 = 6898243) B6898243
theorem B6131771 : Blo 2015435 6131771 := bstep (se 1 (by rfl) ⟨4598828, by rfl⟩ : syracuseStep 6131771 = 9197657) B9197657
theorem B4087847 : Blo 2015435 4087847 := bstep (se 1 (by rfl) ⟨3065885, by rfl⟩ : syracuseStep 4087847 = 6131771) B6131771
theorem B10900925 : Blo 2015435 10900925 := bstep (se 3 (by rfl) ⟨2043923, by rfl⟩ : syracuseStep 10900925 = 4087847) B4087847
theorem B7267283 : Blo 2015435 7267283 := bstep (se 1 (by rfl) ⟨5450462, by rfl⟩ : syracuseStep 7267283 = 10900925) B10900925
theorem B4844855 : Blo 2015435 4844855 := bstep (se 1 (by rfl) ⟨3633641, by rfl⟩ : syracuseStep 4844855 = 7267283) B7267283
theorem B3229903 : Blo 2015435 3229903 := bstep (se 1 (by rfl) ⟨2422427, by rfl⟩ : syracuseStep 3229903 = 4844855) B4844855
theorem B4306537 : Blo 2015435 4306537 := bstep (se 2 (by rfl) ⟨1614951, by rfl⟩ : syracuseStep 4306537 = 3229903) B3229903
theorem B5742049 : Blo 2015435 5742049 := bstep (se 2 (by rfl) ⟨2153268, by rfl⟩ : syracuseStep 5742049 = 4306537) B4306537
theorem B7656065 : Blo 2015435 7656065 := bstep (se 2 (by rfl) ⟨2871024, by rfl⟩ : syracuseStep 7656065 = 5742049) B5742049
theorem B5104043 : Blo 2015435 5104043 := bstep (se 1 (by rfl) ⟨3828032, by rfl⟩ : syracuseStep 5104043 = 7656065) B7656065
theorem B3402695 : Blo 2015435 3402695 := bstep (se 1 (by rfl) ⟨2552021, by rfl⟩ : syracuseStep 3402695 = 5104043) B5104043
theorem B2268463 : Blo 2015435 2268463 := bstep (se 1 (by rfl) ⟨1701347, by rfl⟩ : syracuseStep 2268463 = 3402695) B3402695
theorem B3024617 : Blo 2015435 3024617 := bstep (se 2 (by rfl) ⟨1134231, by rfl⟩ : syracuseStep 3024617 = 2268463) B2268463
theorem B2016411 : Blo 2015435 2016411 := bstep (se 1 (by rfl) ⟨1512308, by rfl⟩ : syracuseStep 2016411 = 3024617) B3024617
theorem B20977109 : Blo 2015435 20977109 := bbase (se 7 (by rfl) ⟨245825, by rfl⟩ : syracuseStep 20977109 = 491651) (by norm_num)
theorem B13984739 : Blo 2015435 13984739 := bstep (se 1 (by rfl) ⟨10488554, by rfl⟩ : syracuseStep 13984739 = 20977109) B20977109
theorem B9323159 : Blo 2015435 9323159 := bstep (se 1 (by rfl) ⟨6992369, by rfl⟩ : syracuseStep 9323159 = 13984739) B13984739
theorem B24861757 : Blo 2015435 24861757 := bstep (se 3 (by rfl) ⟨4661579, by rfl⟩ : syracuseStep 24861757 = 9323159) B9323159
theorem B33149009 : Blo 2015435 33149009 := bstep (se 2 (by rfl) ⟨12430878, by rfl⟩ : syracuseStep 33149009 = 24861757) B24861757
theorem B22099339 : Blo 2015435 22099339 := bstep (se 1 (by rfl) ⟨16574504, by rfl⟩ : syracuseStep 22099339 = 33149009) B33149009
theorem B29465785 : Blo 2015435 29465785 := bstep (se 2 (by rfl) ⟨11049669, by rfl⟩ : syracuseStep 29465785 = 22099339) B22099339
theorem B39287713 : Blo 2015435 39287713 := bstep (se 2 (by rfl) ⟨14732892, by rfl⟩ : syracuseStep 39287713 = 29465785) B29465785
theorem B52383617 : Blo 2015435 52383617 := bstep (se 2 (by rfl) ⟨19643856, by rfl⟩ : syracuseStep 52383617 = 39287713) B39287713
theorem B34922411 : Blo 2015435 34922411 := bstep (se 1 (by rfl) ⟨26191808, by rfl⟩ : syracuseStep 34922411 = 52383617) B52383617
theorem B23281607 : Blo 2015435 23281607 := bstep (se 1 (by rfl) ⟨17461205, by rfl⟩ : syracuseStep 23281607 = 34922411) B34922411
theorem B15521071 : Blo 2015435 15521071 := bstep (se 1 (by rfl) ⟨11640803, by rfl⟩ : syracuseStep 15521071 = 23281607) B23281607
theorem B20694761 : Blo 2015435 20694761 := bstep (se 2 (by rfl) ⟨7760535, by rfl⟩ : syracuseStep 20694761 = 15521071) B15521071
theorem B13796507 : Blo 2015435 13796507 := bstep (se 1 (by rfl) ⟨10347380, by rfl⟩ : syracuseStep 13796507 = 20694761) B20694761
theorem B36790685 : Blo 2015435 36790685 := bstep (se 3 (by rfl) ⟨6898253, by rfl⟩ : syracuseStep 36790685 = 13796507) B13796507
theorem B24527123 : Blo 2015435 24527123 := bstep (se 1 (by rfl) ⟨18395342, by rfl⟩ : syracuseStep 24527123 = 36790685) B36790685
theorem B16351415 : Blo 2015435 16351415 := bstep (se 1 (by rfl) ⟨12263561, by rfl⟩ : syracuseStep 16351415 = 24527123) B24527123
theorem B10900943 : Blo 2015435 10900943 := bstep (se 1 (by rfl) ⟨8175707, by rfl⟩ : syracuseStep 10900943 = 16351415) B16351415
theorem B7267295 : Blo 2015435 7267295 := bstep (se 1 (by rfl) ⟨5450471, by rfl⟩ : syracuseStep 7267295 = 10900943) B10900943
theorem B4844863 : Blo 2015435 4844863 := bstep (se 1 (by rfl) ⟨3633647, by rfl⟩ : syracuseStep 4844863 = 7267295) B7267295
theorem B25839269 : Blo 2015435 25839269 := bstep (se 4 (by rfl) ⟨2422431, by rfl⟩ : syracuseStep 25839269 = 4844863) B4844863
theorem B17226179 : Blo 2015435 17226179 := bstep (se 1 (by rfl) ⟨12919634, by rfl⟩ : syracuseStep 17226179 = 25839269) B25839269
theorem B11484119 : Blo 2015435 11484119 := bstep (se 1 (by rfl) ⟨8613089, by rfl⟩ : syracuseStep 11484119 = 17226179) B17226179
theorem B7656079 : Blo 2015435 7656079 := bstep (se 1 (by rfl) ⟨5742059, by rfl⟩ : syracuseStep 7656079 = 11484119) B11484119
theorem B10208105 : Blo 2015435 10208105 := bstep (se 2 (by rfl) ⟨3828039, by rfl⟩ : syracuseStep 10208105 = 7656079) B7656079
theorem B6805403 : Blo 2015435 6805403 := bstep (se 1 (by rfl) ⟨5104052, by rfl⟩ : syracuseStep 6805403 = 10208105) B10208105
theorem B4536935 : Blo 2015435 4536935 := bstep (se 1 (by rfl) ⟨3402701, by rfl⟩ : syracuseStep 4536935 = 6805403) B6805403
theorem B3024623 : Blo 2015435 3024623 := bstep (se 1 (by rfl) ⟨2268467, by rfl⟩ : syracuseStep 3024623 = 4536935) B4536935
theorem B2016415 : Blo 2015435 2016415 := bstep (se 1 (by rfl) ⟨1512311, by rfl⟩ : syracuseStep 2016415 = 3024623) B3024623
theorem B3024629 : Blo 2015435 3024629 := bbase (se 5 (by rfl) ⟨141779, by rfl⟩ : syracuseStep 3024629 = 283559) (by norm_num)
theorem B2016419 : Blo 2015435 2016419 := bstep (se 1 (by rfl) ⟨1512314, by rfl⟩ : syracuseStep 2016419 = 3024629) B3024629
theorem B8613125 : Blo 2015435 8613125 := bbase (se 4 (by rfl) ⟨807480, by rfl⟩ : syracuseStep 8613125 = 1614961) (by norm_num)
theorem B5742083 : Blo 2015435 5742083 := bstep (se 1 (by rfl) ⟨4306562, by rfl⟩ : syracuseStep 5742083 = 8613125) B8613125
theorem B3828055 : Blo 2015435 3828055 := bstep (se 1 (by rfl) ⟨2871041, by rfl⟩ : syracuseStep 3828055 = 5742083) B5742083
theorem B5104073 : Blo 2015435 5104073 := bstep (se 2 (by rfl) ⟨1914027, by rfl⟩ : syracuseStep 5104073 = 3828055) B3828055
theorem B3402715 : Blo 2015435 3402715 := bstep (se 1 (by rfl) ⟨2552036, by rfl⟩ : syracuseStep 3402715 = 5104073) B5104073
theorem B4536953 : Blo 2015435 4536953 := bstep (se 2 (by rfl) ⟨1701357, by rfl⟩ : syracuseStep 4536953 = 3402715) B3402715
theorem B3024635 : Blo 2015435 3024635 := bstep (se 1 (by rfl) ⟨2268476, by rfl⟩ : syracuseStep 3024635 = 4536953) B4536953
theorem B2016423 : Blo 2015435 2016423 := bstep (se 1 (by rfl) ⟨1512317, by rfl⟩ : syracuseStep 2016423 = 3024635) B3024635
theorem B2268481 : Blo 2015435 2268481 := bbase (se 2 (by rfl) ⟨850680, by rfl⟩ : syracuseStep 2268481 = 1701361) (by norm_num)
theorem B3024641 : Blo 2015435 3024641 := bstep (se 2 (by rfl) ⟨1134240, by rfl⟩ : syracuseStep 3024641 = 2268481) B2268481
theorem B2016427 : Blo 2015435 2016427 := bstep (se 1 (by rfl) ⟨1512320, by rfl⟩ : syracuseStep 2016427 = 3024641) B3024641
theorem B5104093 : Blo 2015435 5104093 := bbase (se 3 (by rfl) ⟨957017, by rfl⟩ : syracuseStep 5104093 = 1914035) (by norm_num)
theorem B6805457 : Blo 2015435 6805457 := bstep (se 2 (by rfl) ⟨2552046, by rfl⟩ : syracuseStep 6805457 = 5104093) B5104093
theorem B4536971 : Blo 2015435 4536971 := bstep (se 1 (by rfl) ⟨3402728, by rfl⟩ : syracuseStep 4536971 = 6805457) B6805457
theorem B3024647 : Blo 2015435 3024647 := bstep (se 1 (by rfl) ⟨2268485, by rfl⟩ : syracuseStep 3024647 = 4536971) B4536971
theorem B2016431 : Blo 2015435 2016431 := bstep (se 1 (by rfl) ⟨1512323, by rfl⟩ : syracuseStep 2016431 = 3024647) B3024647
theorem B3024653 : Blo 2015435 3024653 := bbase (se 3 (by rfl) ⟨567122, by rfl⟩ : syracuseStep 3024653 = 1134245) (by norm_num)
theorem B2016435 : Blo 2015435 2016435 := bstep (se 1 (by rfl) ⟨1512326, by rfl⟩ : syracuseStep 2016435 = 3024653) B3024653
theorem B4536989 : Blo 2015435 4536989 := bbase (se 3 (by rfl) ⟨850685, by rfl⟩ : syracuseStep 4536989 = 1701371) (by norm_num)
theorem B3024659 : Blo 2015435 3024659 := bstep (se 1 (by rfl) ⟨2268494, by rfl⟩ : syracuseStep 3024659 = 4536989) B4536989
theorem B2016439 : Blo 2015435 2016439 := bstep (se 1 (by rfl) ⟨1512329, by rfl⟩ : syracuseStep 2016439 = 3024659) B3024659
theorem B3402749 : Blo 2015435 3402749 := bbase (se 3 (by rfl) ⟨638015, by rfl⟩ : syracuseStep 3402749 = 1276031) (by norm_num)
theorem B2268499 : Blo 2015435 2268499 := bstep (se 1 (by rfl) ⟨1701374, by rfl⟩ : syracuseStep 2268499 = 3402749) B3402749
theorem B3024665 : Blo 2015435 3024665 := bstep (se 2 (by rfl) ⟨1134249, by rfl⟩ : syracuseStep 3024665 = 2268499) B2268499
theorem B2016443 : Blo 2015435 2016443 := bstep (se 1 (by rfl) ⟨1512332, by rfl⟩ : syracuseStep 2016443 = 3024665) B3024665
theorem B4306613 : Blo 2015435 4306613 := bbase (se 5 (by rfl) ⟨201872, by rfl⟩ : syracuseStep 4306613 = 403745) (by norm_num)
theorem B11484301 : Blo 2015435 11484301 := bstep (se 3 (by rfl) ⟨2153306, by rfl⟩ : syracuseStep 11484301 = 4306613) B4306613
theorem B15312401 : Blo 2015435 15312401 := bstep (se 2 (by rfl) ⟨5742150, by rfl⟩ : syracuseStep 15312401 = 11484301) B11484301
theorem B10208267 : Blo 2015435 10208267 := bstep (se 1 (by rfl) ⟨7656200, by rfl⟩ : syracuseStep 10208267 = 15312401) B15312401
theorem B6805511 : Blo 2015435 6805511 := bstep (se 1 (by rfl) ⟨5104133, by rfl⟩ : syracuseStep 6805511 = 10208267) B10208267
theorem B4537007 : Blo 2015435 4537007 := bstep (se 1 (by rfl) ⟨3402755, by rfl⟩ : syracuseStep 4537007 = 6805511) B6805511
theorem B3024671 : Blo 2015435 3024671 := bstep (se 1 (by rfl) ⟨2268503, by rfl⟩ : syracuseStep 3024671 = 4537007) B4537007
theorem B2016447 : Blo 2015435 2016447 := bstep (se 1 (by rfl) ⟨1512335, by rfl⟩ : syracuseStep 2016447 = 3024671) B3024671
theorem B3024677 : Blo 2015435 3024677 := bbase (se 4 (by rfl) ⟨283563, by rfl⟩ : syracuseStep 3024677 = 567127) (by norm_num)
theorem B2016451 : Blo 2015435 2016451 := bstep (se 1 (by rfl) ⟨1512338, by rfl⟩ : syracuseStep 2016451 = 3024677) B3024677
theorem B2552077 : Blo 2015435 2552077 := bbase (se 3 (by rfl) ⟨478514, by rfl⟩ : syracuseStep 2552077 = 957029) (by norm_num)
theorem B3402769 : Blo 2015435 3402769 := bstep (se 2 (by rfl) ⟨1276038, by rfl⟩ : syracuseStep 3402769 = 2552077) B2552077
theorem B4537025 : Blo 2015435 4537025 := bstep (se 2 (by rfl) ⟨1701384, by rfl⟩ : syracuseStep 4537025 = 3402769) B3402769
theorem B3024683 : Blo 2015435 3024683 := bstep (se 1 (by rfl) ⟨2268512, by rfl⟩ : syracuseStep 3024683 = 4537025) B4537025
theorem B2016455 : Blo 2015435 2016455 := bstep (se 1 (by rfl) ⟨1512341, by rfl⟩ : syracuseStep 2016455 = 3024683) B3024683
theorem B2268517 : Blo 2015435 2268517 := bbase (se 4 (by rfl) ⟨212673, by rfl⟩ : syracuseStep 2268517 = 425347) (by norm_num)
theorem B3024689 : Blo 2015435 3024689 := bstep (se 2 (by rfl) ⟨1134258, by rfl⟩ : syracuseStep 3024689 = 2268517) B2268517
theorem B2016459 : Blo 2015435 2016459 := bstep (se 1 (by rfl) ⟨1512344, by rfl⟩ : syracuseStep 2016459 = 3024689) B3024689
theorem B5742197 : Blo 2015435 5742197 := bbase (se 5 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 5742197 = 538331) (by norm_num)
theorem B3828131 : Blo 2015435 3828131 := bstep (se 1 (by rfl) ⟨2871098, by rfl⟩ : syracuseStep 3828131 = 5742197) B5742197
theorem B2552087 : Blo 2015435 2552087 := bstep (se 1 (by rfl) ⟨1914065, by rfl⟩ : syracuseStep 2552087 = 3828131) B3828131
theorem B6805565 : Blo 2015435 6805565 := bstep (se 3 (by rfl) ⟨1276043, by rfl⟩ : syracuseStep 6805565 = 2552087) B2552087
theorem B4537043 : Blo 2015435 4537043 := bstep (se 1 (by rfl) ⟨3402782, by rfl⟩ : syracuseStep 4537043 = 6805565) B6805565
theorem B3024695 : Blo 2015435 3024695 := bstep (se 1 (by rfl) ⟨2268521, by rfl⟩ : syracuseStep 3024695 = 4537043) B4537043
theorem B2016463 : Blo 2015435 2016463 := bstep (se 1 (by rfl) ⟨1512347, by rfl⟩ : syracuseStep 2016463 = 3024695) B3024695
theorem B3024701 : Blo 2015435 3024701 := bbase (se 3 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 3024701 = 1134263) (by norm_num)
theorem B2016467 : Blo 2015435 2016467 := bstep (se 1 (by rfl) ⟨1512350, by rfl⟩ : syracuseStep 2016467 = 3024701) B3024701
theorem B4537061 : Blo 2015435 4537061 := bbase (se 4 (by rfl) ⟨425349, by rfl⟩ : syracuseStep 4537061 = 850699) (by norm_num)
theorem B3024707 : Blo 2015435 3024707 := bstep (se 1 (by rfl) ⟨2268530, by rfl⟩ : syracuseStep 3024707 = 4537061) B4537061
theorem B2016471 : Blo 2015435 2016471 := bstep (se 1 (by rfl) ⟨1512353, by rfl⟩ : syracuseStep 2016471 = 3024707) B3024707
theorem B5104205 : Blo 2015435 5104205 := bbase (se 3 (by rfl) ⟨957038, by rfl⟩ : syracuseStep 5104205 = 1914077) (by norm_num)
theorem B3402803 : Blo 2015435 3402803 := bstep (se 1 (by rfl) ⟨2552102, by rfl⟩ : syracuseStep 3402803 = 5104205) B5104205
theorem B2268535 : Blo 2015435 2268535 := bstep (se 1 (by rfl) ⟨1701401, by rfl⟩ : syracuseStep 2268535 = 3402803) B3402803
theorem B3024713 : Blo 2015435 3024713 := bstep (se 2 (by rfl) ⟨1134267, by rfl⟩ : syracuseStep 3024713 = 2268535) B2268535
theorem B2016475 : Blo 2015435 2016475 := bstep (se 1 (by rfl) ⟨1512356, by rfl⟩ : syracuseStep 2016475 = 3024713) B3024713
theorem B2153341 : Blo 2015435 2153341 := bbase (se 3 (by rfl) ⟨403751, by rfl⟩ : syracuseStep 2153341 = 807503) (by norm_num)
theorem B2871121 : Blo 2015435 2871121 := bstep (se 2 (by rfl) ⟨1076670, by rfl⟩ : syracuseStep 2871121 = 2153341) B2153341
theorem B3828161 : Blo 2015435 3828161 := bstep (se 2 (by rfl) ⟨1435560, by rfl⟩ : syracuseStep 3828161 = 2871121) B2871121
theorem B10208429 : Blo 2015435 10208429 := bstep (se 3 (by rfl) ⟨1914080, by rfl⟩ : syracuseStep 10208429 = 3828161) B3828161
theorem B6805619 : Blo 2015435 6805619 := bstep (se 1 (by rfl) ⟨5104214, by rfl⟩ : syracuseStep 6805619 = 10208429) B10208429
theorem B4537079 : Blo 2015435 4537079 := bstep (se 1 (by rfl) ⟨3402809, by rfl⟩ : syracuseStep 4537079 = 6805619) B6805619
theorem B3024719 : Blo 2015435 3024719 := bstep (se 1 (by rfl) ⟨2268539, by rfl⟩ : syracuseStep 3024719 = 4537079) B4537079
theorem B2016479 : Blo 2015435 2016479 := bstep (se 1 (by rfl) ⟨1512359, by rfl⟩ : syracuseStep 2016479 = 3024719) B3024719
theorem B3024725 : Blo 2015435 3024725 := bbase (se 9 (by rfl) ⟨8861, by rfl⟩ : syracuseStep 3024725 = 17723) (by norm_num)
theorem B2016483 : Blo 2015435 2016483 := bstep (se 1 (by rfl) ⟨1512362, by rfl⟩ : syracuseStep 2016483 = 3024725) B3024725
theorem B4845037 : Blo 2015435 4845037 := bbase (se 3 (by rfl) ⟨908444, by rfl⟩ : syracuseStep 4845037 = 1816889) (by norm_num)
theorem B6460049 : Blo 2015435 6460049 := bstep (se 2 (by rfl) ⟨2422518, by rfl⟩ : syracuseStep 6460049 = 4845037) B4845037
theorem B4306699 : Blo 2015435 4306699 := bstep (se 1 (by rfl) ⟨3230024, by rfl⟩ : syracuseStep 4306699 = 6460049) B6460049
theorem B5742265 : Blo 2015435 5742265 := bstep (se 2 (by rfl) ⟨2153349, by rfl⟩ : syracuseStep 5742265 = 4306699) B4306699
theorem B7656353 : Blo 2015435 7656353 := bstep (se 2 (by rfl) ⟨2871132, by rfl⟩ : syracuseStep 7656353 = 5742265) B5742265
theorem B5104235 : Blo 2015435 5104235 := bstep (se 1 (by rfl) ⟨3828176, by rfl⟩ : syracuseStep 5104235 = 7656353) B7656353
theorem B3402823 : Blo 2015435 3402823 := bstep (se 1 (by rfl) ⟨2552117, by rfl⟩ : syracuseStep 3402823 = 5104235) B5104235
theorem B4537097 : Blo 2015435 4537097 := bstep (se 2 (by rfl) ⟨1701411, by rfl⟩ : syracuseStep 4537097 = 3402823) B3402823
theorem B3024731 : Blo 2015435 3024731 := bstep (se 1 (by rfl) ⟨2268548, by rfl⟩ : syracuseStep 3024731 = 4537097) B4537097
theorem B2016487 : Blo 2015435 2016487 := bstep (se 1 (by rfl) ⟨1512365, by rfl⟩ : syracuseStep 2016487 = 3024731) B3024731
theorem B2268553 : Blo 2015435 2268553 := bbase (se 2 (by rfl) ⟨850707, by rfl⟩ : syracuseStep 2268553 = 1701415) (by norm_num)
theorem B3024737 : Blo 2015435 3024737 := bstep (se 2 (by rfl) ⟨1134276, by rfl⟩ : syracuseStep 3024737 = 2268553) B2268553
theorem B2016491 : Blo 2015435 2016491 := bstep (se 1 (by rfl) ⟨1512368, by rfl⟩ : syracuseStep 2016491 = 3024737) B3024737
theorem B4661765 : Blo 2015435 4661765 := bbase (se 4 (by rfl) ⟨437040, by rfl⟩ : syracuseStep 4661765 = 874081) (by norm_num)
theorem B3107843 : Blo 2015435 3107843 := bstep (se 1 (by rfl) ⟨2330882, by rfl⟩ : syracuseStep 3107843 = 4661765) B4661765
theorem B2071895 : Blo 2015435 2071895 := bstep (se 1 (by rfl) ⟨1553921, by rfl⟩ : syracuseStep 2071895 = 3107843) B3107843
theorem B5525053 : Blo 2015435 5525053 := bstep (se 3 (by rfl) ⟨1035947, by rfl⟩ : syracuseStep 5525053 = 2071895) B2071895
theorem B117867797 : Blo 2015435 117867797 := bstep (se 6 (by rfl) ⟨2762526, by rfl⟩ : syracuseStep 117867797 = 5525053) B5525053
theorem B78578531 : Blo 2015435 78578531 := bstep (se 1 (by rfl) ⟨58933898, by rfl⟩ : syracuseStep 78578531 = 117867797) B117867797
theorem B52385687 : Blo 2015435 52385687 := bstep (se 1 (by rfl) ⟨39289265, by rfl⟩ : syracuseStep 52385687 = 78578531) B78578531
theorem B34923791 : Blo 2015435 34923791 := bstep (se 1 (by rfl) ⟨26192843, by rfl⟩ : syracuseStep 34923791 = 52385687) B52385687
theorem B23282527 : Blo 2015435 23282527 := bstep (se 1 (by rfl) ⟨17461895, by rfl⟩ : syracuseStep 23282527 = 34923791) B34923791
theorem B31043369 : Blo 2015435 31043369 := bstep (se 2 (by rfl) ⟨11641263, by rfl⟩ : syracuseStep 31043369 = 23282527) B23282527
theorem B82782317 : Blo 2015435 82782317 := bstep (se 3 (by rfl) ⟨15521684, by rfl⟩ : syracuseStep 82782317 = 31043369) B31043369
theorem B55188211 : Blo 2015435 55188211 := bstep (se 1 (by rfl) ⟨41391158, by rfl⟩ : syracuseStep 55188211 = 82782317) B82782317
theorem B73584281 : Blo 2015435 73584281 := bstep (se 2 (by rfl) ⟨27594105, by rfl⟩ : syracuseStep 73584281 = 55188211) B55188211
theorem B49056187 : Blo 2015435 49056187 := bstep (se 1 (by rfl) ⟨36792140, by rfl⟩ : syracuseStep 49056187 = 73584281) B73584281
theorem B65408249 : Blo 2015435 65408249 := bstep (se 2 (by rfl) ⟨24528093, by rfl⟩ : syracuseStep 65408249 = 49056187) B49056187
theorem B43605499 : Blo 2015435 43605499 := bstep (se 1 (by rfl) ⟨32704124, by rfl⟩ : syracuseStep 43605499 = 65408249) B65408249
theorem B58140665 : Blo 2015435 58140665 := bstep (se 2 (by rfl) ⟨21802749, by rfl⟩ : syracuseStep 58140665 = 43605499) B43605499
theorem B38760443 : Blo 2015435 38760443 := bstep (se 1 (by rfl) ⟨29070332, by rfl⟩ : syracuseStep 38760443 = 58140665) B58140665
theorem B25840295 : Blo 2015435 25840295 := bstep (se 1 (by rfl) ⟨19380221, by rfl⟩ : syracuseStep 25840295 = 38760443) B38760443
theorem B17226863 : Blo 2015435 17226863 := bstep (se 1 (by rfl) ⟨12920147, by rfl⟩ : syracuseStep 17226863 = 25840295) B25840295
theorem B11484575 : Blo 2015435 11484575 := bstep (se 1 (by rfl) ⟨8613431, by rfl⟩ : syracuseStep 11484575 = 17226863) B17226863
theorem B7656383 : Blo 2015435 7656383 := bstep (se 1 (by rfl) ⟨5742287, by rfl⟩ : syracuseStep 7656383 = 11484575) B11484575
theorem B5104255 : Blo 2015435 5104255 := bstep (se 1 (by rfl) ⟨3828191, by rfl⟩ : syracuseStep 5104255 = 7656383) B7656383
theorem B6805673 : Blo 2015435 6805673 := bstep (se 2 (by rfl) ⟨2552127, by rfl⟩ : syracuseStep 6805673 = 5104255) B5104255
theorem B4537115 : Blo 2015435 4537115 := bstep (se 1 (by rfl) ⟨3402836, by rfl⟩ : syracuseStep 4537115 = 6805673) B6805673
theorem B3024743 : Blo 2015435 3024743 := bstep (se 1 (by rfl) ⟨2268557, by rfl⟩ : syracuseStep 3024743 = 4537115) B4537115
theorem B2016495 : Blo 2015435 2016495 := bstep (se 1 (by rfl) ⟨1512371, by rfl⟩ : syracuseStep 2016495 = 3024743) B3024743
theorem B3024749 : Blo 2015435 3024749 := bbase (se 3 (by rfl) ⟨567140, by rfl⟩ : syracuseStep 3024749 = 1134281) (by norm_num)
theorem B2016499 : Blo 2015435 2016499 := bstep (se 1 (by rfl) ⟨1512374, by rfl⟩ : syracuseStep 2016499 = 3024749) B3024749
theorem B4537133 : Blo 2015435 4537133 := bbase (se 3 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 4537133 = 1701425) (by norm_num)
theorem B3024755 : Blo 2015435 3024755 := bstep (se 1 (by rfl) ⟨2268566, by rfl⟩ : syracuseStep 3024755 = 4537133) B4537133
theorem B2016503 : Blo 2015435 2016503 := bstep (se 1 (by rfl) ⟨1512377, by rfl⟩ : syracuseStep 2016503 = 3024755) B3024755
theorem B8176085 : Blo 2015435 8176085 := bbase (se 7 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 8176085 = 191627) (by norm_num)
theorem B5450723 : Blo 2015435 5450723 := bstep (se 1 (by rfl) ⟨4088042, by rfl⟩ : syracuseStep 5450723 = 8176085) B8176085
theorem B3633815 : Blo 2015435 3633815 := bstep (se 1 (by rfl) ⟨2725361, by rfl⟩ : syracuseStep 3633815 = 5450723) B5450723
theorem B2422543 : Blo 2015435 2422543 := bstep (se 1 (by rfl) ⟨1816907, by rfl⟩ : syracuseStep 2422543 = 3633815) B3633815
theorem B3230057 : Blo 2015435 3230057 := bstep (se 2 (by rfl) ⟨1211271, by rfl⟩ : syracuseStep 3230057 = 2422543) B2422543
theorem B8613485 : Blo 2015435 8613485 := bstep (se 3 (by rfl) ⟨1615028, by rfl⟩ : syracuseStep 8613485 = 3230057) B3230057
theorem B5742323 : Blo 2015435 5742323 := bstep (se 1 (by rfl) ⟨4306742, by rfl⟩ : syracuseStep 5742323 = 8613485) B8613485
theorem B3828215 : Blo 2015435 3828215 := bstep (se 1 (by rfl) ⟨2871161, by rfl⟩ : syracuseStep 3828215 = 5742323) B5742323
theorem B2552143 : Blo 2015435 2552143 := bstep (se 1 (by rfl) ⟨1914107, by rfl⟩ : syracuseStep 2552143 = 3828215) B3828215
theorem B3402857 : Blo 2015435 3402857 := bstep (se 2 (by rfl) ⟨1276071, by rfl⟩ : syracuseStep 3402857 = 2552143) B2552143
theorem B2268571 : Blo 2015435 2268571 := bstep (se 1 (by rfl) ⟨1701428, by rfl⟩ : syracuseStep 2268571 = 3402857) B3402857
theorem B3024761 : Blo 2015435 3024761 := bstep (se 2 (by rfl) ⟨1134285, by rfl⟩ : syracuseStep 3024761 = 2268571) B2268571
theorem B2016507 : Blo 2015435 2016507 := bstep (se 1 (by rfl) ⟨1512380, by rfl⟩ : syracuseStep 2016507 = 3024761) B3024761
theorem B10901461 : Blo 2015435 10901461 := bbase (se 7 (by rfl) ⟨127751, by rfl⟩ : syracuseStep 10901461 = 255503) (by norm_num)
theorem B14535281 : Blo 2015435 14535281 := bstep (se 2 (by rfl) ⟨5450730, by rfl⟩ : syracuseStep 14535281 = 10901461) B10901461
theorem B9690187 : Blo 2015435 9690187 := bstep (se 1 (by rfl) ⟨7267640, by rfl⟩ : syracuseStep 9690187 = 14535281) B14535281
theorem B12920249 : Blo 2015435 12920249 := bstep (se 2 (by rfl) ⟨4845093, by rfl⟩ : syracuseStep 12920249 = 9690187) B9690187
theorem B34453997 : Blo 2015435 34453997 := bstep (se 3 (by rfl) ⟨6460124, by rfl⟩ : syracuseStep 34453997 = 12920249) B12920249
theorem B22969331 : Blo 2015435 22969331 := bstep (se 1 (by rfl) ⟨17226998, by rfl⟩ : syracuseStep 22969331 = 34453997) B34453997
theorem B15312887 : Blo 2015435 15312887 := bstep (se 1 (by rfl) ⟨11484665, by rfl⟩ : syracuseStep 15312887 = 22969331) B22969331
theorem B10208591 : Blo 2015435 10208591 := bstep (se 1 (by rfl) ⟨7656443, by rfl⟩ : syracuseStep 10208591 = 15312887) B15312887
theorem B6805727 : Blo 2015435 6805727 := bstep (se 1 (by rfl) ⟨5104295, by rfl⟩ : syracuseStep 6805727 = 10208591) B10208591
theorem B4537151 : Blo 2015435 4537151 := bstep (se 1 (by rfl) ⟨3402863, by rfl⟩ : syracuseStep 4537151 = 6805727) B6805727
theorem B3024767 : Blo 2015435 3024767 := bstep (se 1 (by rfl) ⟨2268575, by rfl⟩ : syracuseStep 3024767 = 4537151) B4537151
theorem B2016511 : Blo 2015435 2016511 := bstep (se 1 (by rfl) ⟨1512383, by rfl⟩ : syracuseStep 2016511 = 3024767) B3024767
theorem B3024773 : Blo 2015435 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B2016515 : Blo 2015435 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B3402877 : Blo 2015435 3402877 := bbase (se 3 (by rfl) ⟨638039, by rfl⟩ : syracuseStep 3402877 = 1276079) (by norm_num)
theorem B4537169 : Blo 2015435 4537169 := bstep (se 2 (by rfl) ⟨1701438, by rfl⟩ : syracuseStep 4537169 = 3402877) B3402877
theorem B3024779 : Blo 2015435 3024779 := bstep (se 1 (by rfl) ⟨2268584, by rfl⟩ : syracuseStep 3024779 = 4537169) B4537169
theorem B2016519 : Blo 2015435 2016519 := bstep (se 1 (by rfl) ⟨1512389, by rfl⟩ : syracuseStep 2016519 = 3024779) B3024779
theorem B2268589 : Blo 2015435 2268589 := bbase (se 3 (by rfl) ⟨425360, by rfl⟩ : syracuseStep 2268589 = 850721) (by norm_num)
theorem B3024785 : Blo 2015435 3024785 := bstep (se 2 (by rfl) ⟨1134294, by rfl⟩ : syracuseStep 3024785 = 2268589) B2268589
theorem B2016523 : Blo 2015435 2016523 := bstep (se 1 (by rfl) ⟨1512392, by rfl⟩ : syracuseStep 2016523 = 3024785) B3024785
theorem B6805781 : Blo 2015435 6805781 := bbase (se 6 (by rfl) ⟨159510, by rfl⟩ : syracuseStep 6805781 = 319021) (by norm_num)
theorem B4537187 : Blo 2015435 4537187 := bstep (se 1 (by rfl) ⟨3402890, by rfl⟩ : syracuseStep 4537187 = 6805781) B6805781
theorem B3024791 : Blo 2015435 3024791 := bstep (se 1 (by rfl) ⟨2268593, by rfl⟩ : syracuseStep 3024791 = 4537187) B4537187
theorem B2016527 : Blo 2015435 2016527 := bstep (se 1 (by rfl) ⟨1512395, by rfl⟩ : syracuseStep 2016527 = 3024791) B3024791
theorem B3024797 : Blo 2015435 3024797 := bbase (se 3 (by rfl) ⟨567149, by rfl⟩ : syracuseStep 3024797 = 1134299) (by norm_num)
theorem B2016531 : Blo 2015435 2016531 := bstep (se 1 (by rfl) ⟨1512398, by rfl⟩ : syracuseStep 2016531 = 3024797) B3024797
theorem B4537205 : Blo 2015435 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B3024803 : Blo 2015435 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B2016535 : Blo 2015435 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B6548357 : Blo 2015435 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B4365571 : Blo 2015435 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B5820761 : Blo 2015435 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B3880507 : Blo 2015435 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B5174009 : Blo 2015435 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B3449339 : Blo 2015435 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B36792949 : Blo 2015435 36792949 := bstep (se 5 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 36792949 = 3449339) B3449339
theorem B49057265 : Blo 2015435 49057265 := bstep (se 2 (by rfl) ⟨18396474, by rfl⟩ : syracuseStep 49057265 = 36792949) B36792949
theorem B32704843 : Blo 2015435 32704843 := bstep (se 1 (by rfl) ⟨24528632, by rfl⟩ : syracuseStep 32704843 = 49057265) B49057265
theorem B43606457 : Blo 2015435 43606457 := bstep (se 2 (by rfl) ⟨16352421, by rfl⟩ : syracuseStep 43606457 = 32704843) B32704843
theorem B29070971 : Blo 2015435 29070971 := bstep (se 1 (by rfl) ⟨21803228, by rfl⟩ : syracuseStep 29070971 = 43606457) B43606457
theorem B19380647 : Blo 2015435 19380647 := bstep (se 1 (by rfl) ⟨14535485, by rfl⟩ : syracuseStep 19380647 = 29070971) B29070971
theorem B12920431 : Blo 2015435 12920431 := bstep (se 1 (by rfl) ⟨9690323, by rfl⟩ : syracuseStep 12920431 = 19380647) B19380647
theorem B17227241 : Blo 2015435 17227241 := bstep (se 2 (by rfl) ⟨6460215, by rfl⟩ : syracuseStep 17227241 = 12920431) B12920431
theorem B11484827 : Blo 2015435 11484827 := bstep (se 1 (by rfl) ⟨8613620, by rfl⟩ : syracuseStep 11484827 = 17227241) B17227241
theorem B7656551 : Blo 2015435 7656551 := bstep (se 1 (by rfl) ⟨5742413, by rfl⟩ : syracuseStep 7656551 = 11484827) B11484827
theorem B5104367 : Blo 2015435 5104367 := bstep (se 1 (by rfl) ⟨3828275, by rfl⟩ : syracuseStep 5104367 = 7656551) B7656551
theorem B3402911 : Blo 2015435 3402911 := bstep (se 1 (by rfl) ⟨2552183, by rfl⟩ : syracuseStep 3402911 = 5104367) B5104367
theorem B2268607 : Blo 2015435 2268607 := bstep (se 1 (by rfl) ⟨1701455, by rfl⟩ : syracuseStep 2268607 = 3402911) B3402911
theorem B3024809 : Blo 2015435 3024809 := bstep (se 2 (by rfl) ⟨1134303, by rfl⟩ : syracuseStep 3024809 = 2268607) B2268607
theorem B2016539 : Blo 2015435 2016539 := bstep (se 1 (by rfl) ⟨1512404, by rfl⟩ : syracuseStep 2016539 = 3024809) B3024809
theorem B7656565 : Blo 2015435 7656565 := bbase (se 5 (by rfl) ⟨358901, by rfl⟩ : syracuseStep 7656565 = 717803) (by norm_num)
theorem B10208753 : Blo 2015435 10208753 := bstep (se 2 (by rfl) ⟨3828282, by rfl⟩ : syracuseStep 10208753 = 7656565) B7656565
theorem B6805835 : Blo 2015435 6805835 := bstep (se 1 (by rfl) ⟨5104376, by rfl⟩ : syracuseStep 6805835 = 10208753) B10208753
theorem B4537223 : Blo 2015435 4537223 := bstep (se 1 (by rfl) ⟨3402917, by rfl⟩ : syracuseStep 4537223 = 6805835) B6805835
theorem B3024815 : Blo 2015435 3024815 := bstep (se 1 (by rfl) ⟨2268611, by rfl⟩ : syracuseStep 3024815 = 4537223) B4537223
theorem B2016543 : Blo 2015435 2016543 := bstep (se 1 (by rfl) ⟨1512407, by rfl⟩ : syracuseStep 2016543 = 3024815) B3024815
theorem B3024821 : Blo 2015435 3024821 := bbase (se 5 (by rfl) ⟨141788, by rfl⟩ : syracuseStep 3024821 = 283577) (by norm_num)
theorem B2016547 : Blo 2015435 2016547 := bstep (se 1 (by rfl) ⟨1512410, by rfl⟩ : syracuseStep 2016547 = 3024821) B3024821
theorem B5104397 : Blo 2015435 5104397 := bbase (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) (by norm_num)
theorem B3402931 : Blo 2015435 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B4537241 : Blo 2015435 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B3024827 : Blo 2015435 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B2016551 : Blo 2015435 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B2268625 : Blo 2015435 2268625 := bbase (se 2 (by rfl) ⟨850734, by rfl⟩ : syracuseStep 2268625 = 1701469) (by norm_num)
theorem B3024833 : Blo 2015435 3024833 := bstep (se 2 (by rfl) ⟨1134312, by rfl⟩ : syracuseStep 3024833 = 2268625) B2268625
theorem B2016555 : Blo 2015435 2016555 := bstep (se 1 (by rfl) ⟨1512416, by rfl⟩ : syracuseStep 2016555 = 3024833) B3024833
theorem B4306853 : Blo 2015435 4306853 := bbase (se 4 (by rfl) ⟨403767, by rfl⟩ : syracuseStep 4306853 = 807535) (by norm_num)
theorem B2871235 : Blo 2015435 2871235 := bstep (se 1 (by rfl) ⟨2153426, by rfl⟩ : syracuseStep 2871235 = 4306853) B4306853
theorem B3828313 : Blo 2015435 3828313 := bstep (se 2 (by rfl) ⟨1435617, by rfl⟩ : syracuseStep 3828313 = 2871235) B2871235
theorem B5104417 : Blo 2015435 5104417 := bstep (se 2 (by rfl) ⟨1914156, by rfl⟩ : syracuseStep 5104417 = 3828313) B3828313
theorem B6805889 : Blo 2015435 6805889 := bstep (se 2 (by rfl) ⟨2552208, by rfl⟩ : syracuseStep 6805889 = 5104417) B5104417
theorem B4537259 : Blo 2015435 4537259 := bstep (se 1 (by rfl) ⟨3402944, by rfl⟩ : syracuseStep 4537259 = 6805889) B6805889
theorem B3024839 : Blo 2015435 3024839 := bstep (se 1 (by rfl) ⟨2268629, by rfl⟩ : syracuseStep 3024839 = 4537259) B4537259
theorem B2016559 : Blo 2015435 2016559 := bstep (se 1 (by rfl) ⟨1512419, by rfl⟩ : syracuseStep 2016559 = 3024839) B3024839
theorem B3024845 : Blo 2015435 3024845 := bbase (se 3 (by rfl) ⟨567158, by rfl⟩ : syracuseStep 3024845 = 1134317) (by norm_num)
theorem B2016563 : Blo 2015435 2016563 := bstep (se 1 (by rfl) ⟨1512422, by rfl⟩ : syracuseStep 2016563 = 3024845) B3024845
theorem B4537277 : Blo 2015435 4537277 := bbase (se 3 (by rfl) ⟨850739, by rfl⟩ : syracuseStep 4537277 = 1701479) (by norm_num)
theorem B3024851 : Blo 2015435 3024851 := bstep (se 1 (by rfl) ⟨2268638, by rfl⟩ : syracuseStep 3024851 = 4537277) B4537277
theorem B2016567 : Blo 2015435 2016567 := bstep (se 1 (by rfl) ⟨1512425, by rfl⟩ : syracuseStep 2016567 = 3024851) B3024851
theorem B3402965 : Blo 2015435 3402965 := bbase (se 7 (by rfl) ⟨39878, by rfl⟩ : syracuseStep 3402965 = 79757) (by norm_num)
theorem B2268643 : Blo 2015435 2268643 := bstep (se 1 (by rfl) ⟨1701482, by rfl⟩ : syracuseStep 2268643 = 3402965) B3402965
theorem B3024857 : Blo 2015435 3024857 := bstep (se 2 (by rfl) ⟨1134321, by rfl⟩ : syracuseStep 3024857 = 2268643) B2268643
theorem B2016571 : Blo 2015435 2016571 := bstep (se 1 (by rfl) ⟨1512428, by rfl⟩ : syracuseStep 2016571 = 3024857) B3024857
theorem B3230165 : Blo 2015435 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B8613773 : Blo 2015435 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B5742515 : Blo 2015435 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B15313373 : Blo 2015435 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B10208915 : Blo 2015435 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B6805943 : Blo 2015435 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B4537295 : Blo 2015435 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B3024863 : Blo 2015435 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B2016575 : Blo 2015435 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B3024869 : Blo 2015435 3024869 := bbase (se 4 (by rfl) ⟨283581, by rfl⟩ : syracuseStep 3024869 = 567163) (by norm_num)
theorem B2016579 : Blo 2015435 2016579 := bstep (se 1 (by rfl) ⟨1512434, by rfl⟩ : syracuseStep 2016579 = 3024869) B3024869
theorem B6460357 : Blo 2015435 6460357 := bbase (se 4 (by rfl) ⟨605658, by rfl⟩ : syracuseStep 6460357 = 1211317) (by norm_num)
theorem B8613809 : Blo 2015435 8613809 := bstep (se 2 (by rfl) ⟨3230178, by rfl⟩ : syracuseStep 8613809 = 6460357) B6460357
theorem B5742539 : Blo 2015435 5742539 := bstep (se 1 (by rfl) ⟨4306904, by rfl⟩ : syracuseStep 5742539 = 8613809) B8613809
theorem B3828359 : Blo 2015435 3828359 := bstep (se 1 (by rfl) ⟨2871269, by rfl⟩ : syracuseStep 3828359 = 5742539) B5742539
theorem B2552239 : Blo 2015435 2552239 := bstep (se 1 (by rfl) ⟨1914179, by rfl⟩ : syracuseStep 2552239 = 3828359) B3828359
theorem B3402985 : Blo 2015435 3402985 := bstep (se 2 (by rfl) ⟨1276119, by rfl⟩ : syracuseStep 3402985 = 2552239) B2552239
theorem B4537313 : Blo 2015435 4537313 := bstep (se 2 (by rfl) ⟨1701492, by rfl⟩ : syracuseStep 4537313 = 3402985) B3402985
theorem B3024875 : Blo 2015435 3024875 := bstep (se 1 (by rfl) ⟨2268656, by rfl⟩ : syracuseStep 3024875 = 4537313) B4537313
theorem B2016583 : Blo 2015435 2016583 := bstep (se 1 (by rfl) ⟨1512437, by rfl⟩ : syracuseStep 2016583 = 3024875) B3024875
theorem B2268661 : Blo 2015435 2268661 := bbase (se 5 (by rfl) ⟨106343, by rfl⟩ : syracuseStep 2268661 = 212687) (by norm_num)
theorem B3024881 : Blo 2015435 3024881 := bstep (se 2 (by rfl) ⟨1134330, by rfl⟩ : syracuseStep 3024881 = 2268661) B2268661
theorem B2016587 : Blo 2015435 2016587 := bstep (se 1 (by rfl) ⟨1512440, by rfl⟩ : syracuseStep 2016587 = 3024881) B3024881
theorem B2552249 : Blo 2015435 2552249 := bbase (se 2 (by rfl) ⟨957093, by rfl⟩ : syracuseStep 2552249 = 1914187) (by norm_num)
theorem B6805997 : Blo 2015435 6805997 := bstep (se 3 (by rfl) ⟨1276124, by rfl⟩ : syracuseStep 6805997 = 2552249) B2552249
theorem B4537331 : Blo 2015435 4537331 := bstep (se 1 (by rfl) ⟨3402998, by rfl⟩ : syracuseStep 4537331 = 6805997) B6805997
theorem B3024887 : Blo 2015435 3024887 := bstep (se 1 (by rfl) ⟨2268665, by rfl⟩ : syracuseStep 3024887 = 4537331) B4537331
theorem B2016591 : Blo 2015435 2016591 := bstep (se 1 (by rfl) ⟨1512443, by rfl⟩ : syracuseStep 2016591 = 3024887) B3024887
theorem B3024893 : Blo 2015435 3024893 := bbase (se 3 (by rfl) ⟨567167, by rfl⟩ : syracuseStep 3024893 = 1134335) (by norm_num)
theorem B2016595 : Blo 2015435 2016595 := bstep (se 1 (by rfl) ⟨1512446, by rfl⟩ : syracuseStep 2016595 = 3024893) B3024893
theorem B4537349 : Blo 2015435 4537349 := bbase (se 4 (by rfl) ⟨425376, by rfl⟩ : syracuseStep 4537349 = 850753) (by norm_num)
theorem B3024899 : Blo 2015435 3024899 := bstep (se 1 (by rfl) ⟨2268674, by rfl⟩ : syracuseStep 3024899 = 4537349) B4537349
theorem B2016599 : Blo 2015435 2016599 := bstep (se 1 (by rfl) ⟨1512449, by rfl⟩ : syracuseStep 2016599 = 3024899) B3024899
theorem B3828397 : Blo 2015435 3828397 := bbase (se 3 (by rfl) ⟨717824, by rfl⟩ : syracuseStep 3828397 = 1435649) (by norm_num)
theorem B5104529 : Blo 2015435 5104529 := bstep (se 2 (by rfl) ⟨1914198, by rfl⟩ : syracuseStep 5104529 = 3828397) B3828397
theorem B3403019 : Blo 2015435 3403019 := bstep (se 1 (by rfl) ⟨2552264, by rfl⟩ : syracuseStep 3403019 = 5104529) B5104529
theorem B2268679 : Blo 2015435 2268679 := bstep (se 1 (by rfl) ⟨1701509, by rfl⟩ : syracuseStep 2268679 = 3403019) B3403019
theorem B3024905 : Blo 2015435 3024905 := bstep (se 2 (by rfl) ⟨1134339, by rfl⟩ : syracuseStep 3024905 = 2268679) B2268679
theorem B2016603 : Blo 2015435 2016603 := bstep (se 1 (by rfl) ⟨1512452, by rfl⟩ : syracuseStep 2016603 = 3024905) B3024905
theorem B10209077 : Blo 2015435 10209077 := bbase (se 5 (by rfl) ⟨478550, by rfl⟩ : syracuseStep 10209077 = 957101) (by norm_num)
theorem B6806051 : Blo 2015435 6806051 := bstep (se 1 (by rfl) ⟨5104538, by rfl⟩ : syracuseStep 6806051 = 10209077) B10209077
theorem B4537367 : Blo 2015435 4537367 := bstep (se 1 (by rfl) ⟨3403025, by rfl⟩ : syracuseStep 4537367 = 6806051) B6806051
theorem B3024911 : Blo 2015435 3024911 := bstep (se 1 (by rfl) ⟨2268683, by rfl⟩ : syracuseStep 3024911 = 4537367) B4537367
theorem B2016607 : Blo 2015435 2016607 := bstep (se 1 (by rfl) ⟨1512455, by rfl⟩ : syracuseStep 2016607 = 3024911) B3024911
theorem B3024917 : Blo 2015435 3024917 := bbase (se 6 (by rfl) ⟨70896, by rfl⟩ : syracuseStep 3024917 = 141793) (by norm_num)
theorem B2016611 : Blo 2015435 2016611 := bstep (se 1 (by rfl) ⟨1512458, by rfl⟩ : syracuseStep 2016611 = 3024917) B3024917
theorem B12920917 : Blo 2015435 12920917 := bbase (se 8 (by rfl) ⟨75708, by rfl⟩ : syracuseStep 12920917 = 151417) (by norm_num)
theorem B17227889 : Blo 2015435 17227889 := bstep (se 2 (by rfl) ⟨6460458, by rfl⟩ : syracuseStep 17227889 = 12920917) B12920917
theorem B11485259 : Blo 2015435 11485259 := bstep (se 1 (by rfl) ⟨8613944, by rfl⟩ : syracuseStep 11485259 = 17227889) B17227889
theorem B7656839 : Blo 2015435 7656839 := bstep (se 1 (by rfl) ⟨5742629, by rfl⟩ : syracuseStep 7656839 = 11485259) B11485259
theorem B5104559 : Blo 2015435 5104559 := bstep (se 1 (by rfl) ⟨3828419, by rfl⟩ : syracuseStep 5104559 = 7656839) B7656839
theorem B3403039 : Blo 2015435 3403039 := bstep (se 1 (by rfl) ⟨2552279, by rfl⟩ : syracuseStep 3403039 = 5104559) B5104559
theorem B4537385 : Blo 2015435 4537385 := bstep (se 2 (by rfl) ⟨1701519, by rfl⟩ : syracuseStep 4537385 = 3403039) B3403039
theorem B3024923 : Blo 2015435 3024923 := bstep (se 1 (by rfl) ⟨2268692, by rfl⟩ : syracuseStep 3024923 = 4537385) B4537385
theorem B2016615 : Blo 2015435 2016615 := bstep (se 1 (by rfl) ⟨1512461, by rfl⟩ : syracuseStep 2016615 = 3024923) B3024923
theorem B2268697 : Blo 2015435 2268697 := bbase (se 2 (by rfl) ⟨850761, by rfl⟩ : syracuseStep 2268697 = 1701523) (by norm_num)
theorem B3024929 : Blo 2015435 3024929 := bstep (se 2 (by rfl) ⟨1134348, by rfl⟩ : syracuseStep 3024929 = 2268697) B2268697
theorem B2016619 : Blo 2015435 2016619 := bstep (se 1 (by rfl) ⟨1512464, by rfl⟩ : syracuseStep 2016619 = 3024929) B3024929
theorem B7656869 : Blo 2015435 7656869 := bbase (se 4 (by rfl) ⟨717831, by rfl⟩ : syracuseStep 7656869 = 1435663) (by norm_num)
theorem B5104579 : Blo 2015435 5104579 := bstep (se 1 (by rfl) ⟨3828434, by rfl⟩ : syracuseStep 5104579 = 7656869) B7656869
theorem B6806105 : Blo 2015435 6806105 := bstep (se 2 (by rfl) ⟨2552289, by rfl⟩ : syracuseStep 6806105 = 5104579) B5104579
theorem B4537403 : Blo 2015435 4537403 := bstep (se 1 (by rfl) ⟨3403052, by rfl⟩ : syracuseStep 4537403 = 6806105) B6806105
theorem B3024935 : Blo 2015435 3024935 := bstep (se 1 (by rfl) ⟨2268701, by rfl⟩ : syracuseStep 3024935 = 4537403) B4537403
theorem B2016623 : Blo 2015435 2016623 := bstep (se 1 (by rfl) ⟨1512467, by rfl⟩ : syracuseStep 2016623 = 3024935) B3024935
theorem B3024941 : Blo 2015435 3024941 := bbase (se 3 (by rfl) ⟨567176, by rfl⟩ : syracuseStep 3024941 = 1134353) (by norm_num)
theorem B2016627 : Blo 2015435 2016627 := bstep (se 1 (by rfl) ⟨1512470, by rfl⟩ : syracuseStep 2016627 = 3024941) B3024941
theorem B4537421 : Blo 2015435 4537421 := bbase (se 3 (by rfl) ⟨850766, by rfl⟩ : syracuseStep 4537421 = 1701533) (by norm_num)
theorem B3024947 : Blo 2015435 3024947 := bstep (se 1 (by rfl) ⟨2268710, by rfl⟩ : syracuseStep 3024947 = 4537421) B4537421
theorem B2016631 : Blo 2015435 2016631 := bstep (se 1 (by rfl) ⟨1512473, by rfl⟩ : syracuseStep 2016631 = 3024947) B3024947
theorem B2552305 : Blo 2015435 2552305 := bbase (se 2 (by rfl) ⟨957114, by rfl⟩ : syracuseStep 2552305 = 1914229) (by norm_num)
theorem B3403073 : Blo 2015435 3403073 := bstep (se 2 (by rfl) ⟨1276152, by rfl⟩ : syracuseStep 3403073 = 2552305) B2552305
theorem B2268715 : Blo 2015435 2268715 := bstep (se 1 (by rfl) ⟨1701536, by rfl⟩ : syracuseStep 2268715 = 3403073) B3403073
theorem B3024953 : Blo 2015435 3024953 := bstep (se 2 (by rfl) ⟨1134357, by rfl⟩ : syracuseStep 3024953 = 2268715) B2268715
theorem B2016635 : Blo 2015435 2016635 := bstep (se 1 (by rfl) ⟨1512476, by rfl⟩ : syracuseStep 2016635 = 3024953) B3024953
theorem B5451077 : Blo 2015435 5451077 := bbase (se 4 (by rfl) ⟨511038, by rfl⟩ : syracuseStep 5451077 = 1022077) (by norm_num)
theorem B14536205 : Blo 2015435 14536205 := bstep (se 3 (by rfl) ⟨2725538, by rfl⟩ : syracuseStep 14536205 = 5451077) B5451077
theorem B9690803 : Blo 2015435 9690803 := bstep (se 1 (by rfl) ⟨7268102, by rfl⟩ : syracuseStep 9690803 = 14536205) B14536205
theorem B6460535 : Blo 2015435 6460535 := bstep (se 1 (by rfl) ⟨4845401, by rfl⟩ : syracuseStep 6460535 = 9690803) B9690803
theorem B4307023 : Blo 2015435 4307023 := bstep (se 1 (by rfl) ⟨3230267, by rfl⟩ : syracuseStep 4307023 = 6460535) B6460535
theorem B22970789 : Blo 2015435 22970789 := bstep (se 4 (by rfl) ⟨2153511, by rfl⟩ : syracuseStep 22970789 = 4307023) B4307023
theorem B15313859 : Blo 2015435 15313859 := bstep (se 1 (by rfl) ⟨11485394, by rfl⟩ : syracuseStep 15313859 = 22970789) B22970789
theorem B10209239 : Blo 2015435 10209239 := bstep (se 1 (by rfl) ⟨7656929, by rfl⟩ : syracuseStep 10209239 = 15313859) B15313859
theorem B6806159 : Blo 2015435 6806159 := bstep (se 1 (by rfl) ⟨5104619, by rfl⟩ : syracuseStep 6806159 = 10209239) B10209239
theorem B4537439 : Blo 2015435 4537439 := bstep (se 1 (by rfl) ⟨3403079, by rfl⟩ : syracuseStep 4537439 = 6806159) B6806159
theorem B3024959 : Blo 2015435 3024959 := bstep (se 1 (by rfl) ⟨2268719, by rfl⟩ : syracuseStep 3024959 = 4537439) B4537439
theorem B2016639 : Blo 2015435 2016639 := bstep (se 1 (by rfl) ⟨1512479, by rfl⟩ : syracuseStep 2016639 = 3024959) B3024959
theorem B3024965 : Blo 2015435 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2016643 : Blo 2015435 2016643 := bstep (se 1 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 2016643 = 3024965) B3024965
theorem B3403093 : Blo 2015435 3403093 := bbase (se 11 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 3403093 = 4985) (by norm_num)
theorem B4537457 : Blo 2015435 4537457 := bstep (se 2 (by rfl) ⟨1701546, by rfl⟩ : syracuseStep 4537457 = 3403093) B3403093
theorem B3024971 : Blo 2015435 3024971 := bstep (se 1 (by rfl) ⟨2268728, by rfl⟩ : syracuseStep 3024971 = 4537457) B4537457
theorem B2016647 : Blo 2015435 2016647 := bstep (se 1 (by rfl) ⟨1512485, by rfl⟩ : syracuseStep 2016647 = 3024971) B3024971
theorem B2268733 : Blo 2015435 2268733 := bbase (se 3 (by rfl) ⟨425387, by rfl⟩ : syracuseStep 2268733 = 850775) (by norm_num)
theorem B3024977 : Blo 2015435 3024977 := bstep (se 2 (by rfl) ⟨1134366, by rfl⟩ : syracuseStep 3024977 = 2268733) B2268733
theorem B2016651 : Blo 2015435 2016651 := bstep (se 1 (by rfl) ⟨1512488, by rfl⟩ : syracuseStep 2016651 = 3024977) B3024977
theorem B6806213 : Blo 2015435 6806213 := bbase (se 4 (by rfl) ⟨638082, by rfl⟩ : syracuseStep 6806213 = 1276165) (by norm_num)
theorem B4537475 : Blo 2015435 4537475 := bstep (se 1 (by rfl) ⟨3403106, by rfl⟩ : syracuseStep 4537475 = 6806213) B6806213
theorem B3024983 : Blo 2015435 3024983 := bstep (se 1 (by rfl) ⟨2268737, by rfl⟩ : syracuseStep 3024983 = 4537475) B4537475
theorem B2016655 : Blo 2015435 2016655 := bstep (se 1 (by rfl) ⟨1512491, by rfl⟩ : syracuseStep 2016655 = 3024983) B3024983
theorem B3024989 : Blo 2015435 3024989 := bbase (se 3 (by rfl) ⟨567185, by rfl⟩ : syracuseStep 3024989 = 1134371) (by norm_num)
theorem B2016659 : Blo 2015435 2016659 := bstep (se 1 (by rfl) ⟨1512494, by rfl⟩ : syracuseStep 2016659 = 3024989) B3024989
theorem B4537493 : Blo 2015435 4537493 := bbase (se 6 (by rfl) ⟨106347, by rfl⟩ : syracuseStep 4537493 = 212695) (by norm_num)
theorem B3024995 : Blo 2015435 3024995 := bstep (se 1 (by rfl) ⟨2268746, by rfl⟩ : syracuseStep 3024995 = 4537493) B4537493
theorem B2016663 : Blo 2015435 2016663 := bstep (se 1 (by rfl) ⟨1512497, by rfl⟩ : syracuseStep 2016663 = 3024995) B3024995
theorem B2871389 : Blo 2015435 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B7657037 : Blo 2015435 7657037 := bstep (se 3 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 7657037 = 2871389) B2871389
theorem B5104691 : Blo 2015435 5104691 := bstep (se 1 (by rfl) ⟨3828518, by rfl⟩ : syracuseStep 5104691 = 7657037) B7657037
theorem B3403127 : Blo 2015435 3403127 := bstep (se 1 (by rfl) ⟨2552345, by rfl⟩ : syracuseStep 3403127 = 5104691) B5104691
theorem B2268751 : Blo 2015435 2268751 := bstep (se 1 (by rfl) ⟨1701563, by rfl⟩ : syracuseStep 2268751 = 3403127) B3403127
theorem B3025001 : Blo 2015435 3025001 := bstep (se 2 (by rfl) ⟨1134375, by rfl⟩ : syracuseStep 3025001 = 2268751) B2268751
theorem B2016667 : Blo 2015435 2016667 := bstep (se 1 (by rfl) ⟨1512500, by rfl⟩ : syracuseStep 2016667 = 3025001) B3025001
theorem B5821141 : Blo 2015435 5821141 := bbase (se 7 (by rfl) ⟨68216, by rfl⟩ : syracuseStep 5821141 = 136433) (by norm_num)
theorem B7761521 : Blo 2015435 7761521 := bstep (se 2 (by rfl) ⟨2910570, by rfl⟩ : syracuseStep 7761521 = 5821141) B5821141
theorem B20697389 : Blo 2015435 20697389 := bstep (se 3 (by rfl) ⟨3880760, by rfl⟩ : syracuseStep 20697389 = 7761521) B7761521
theorem B13798259 : Blo 2015435 13798259 := bstep (se 1 (by rfl) ⟨10348694, by rfl⟩ : syracuseStep 13798259 = 20697389) B20697389
theorem B9198839 : Blo 2015435 9198839 := bstep (se 1 (by rfl) ⟨6899129, by rfl⟩ : syracuseStep 9198839 = 13798259) B13798259
theorem B6132559 : Blo 2015435 6132559 := bstep (se 1 (by rfl) ⟨4599419, by rfl⟩ : syracuseStep 6132559 = 9198839) B9198839
theorem B8176745 : Blo 2015435 8176745 := bstep (se 2 (by rfl) ⟨3066279, by rfl⟩ : syracuseStep 8176745 = 6132559) B6132559
theorem B21804653 : Blo 2015435 21804653 := bstep (se 3 (by rfl) ⟨4088372, by rfl⟩ : syracuseStep 21804653 = 8176745) B8176745
theorem B14536435 : Blo 2015435 14536435 := bstep (se 1 (by rfl) ⟨10902326, by rfl⟩ : syracuseStep 14536435 = 21804653) B21804653
theorem B19381913 : Blo 2015435 19381913 := bstep (se 2 (by rfl) ⟨7268217, by rfl⟩ : syracuseStep 19381913 = 14536435) B14536435
theorem B12921275 : Blo 2015435 12921275 := bstep (se 1 (by rfl) ⟨9690956, by rfl⟩ : syracuseStep 12921275 = 19381913) B19381913
theorem B8614183 : Blo 2015435 8614183 := bstep (se 1 (by rfl) ⟨6460637, by rfl⟩ : syracuseStep 8614183 = 12921275) B12921275
theorem B11485577 : Blo 2015435 11485577 := bstep (se 2 (by rfl) ⟨4307091, by rfl⟩ : syracuseStep 11485577 = 8614183) B8614183
theorem B7657051 : Blo 2015435 7657051 := bstep (se 1 (by rfl) ⟨5742788, by rfl⟩ : syracuseStep 7657051 = 11485577) B11485577
theorem B10209401 : Blo 2015435 10209401 := bstep (se 2 (by rfl) ⟨3828525, by rfl⟩ : syracuseStep 10209401 = 7657051) B7657051
theorem B6806267 : Blo 2015435 6806267 := bstep (se 1 (by rfl) ⟨5104700, by rfl⟩ : syracuseStep 6806267 = 10209401) B10209401
theorem B4537511 : Blo 2015435 4537511 := bstep (se 1 (by rfl) ⟨3403133, by rfl⟩ : syracuseStep 4537511 = 6806267) B6806267
theorem B3025007 : Blo 2015435 3025007 := bstep (se 1 (by rfl) ⟨2268755, by rfl⟩ : syracuseStep 3025007 = 4537511) B4537511
theorem B2016671 : Blo 2015435 2016671 := bstep (se 1 (by rfl) ⟨1512503, by rfl⟩ : syracuseStep 2016671 = 3025007) B3025007
theorem B3025013 : Blo 2015435 3025013 := bbase (se 5 (by rfl) ⟨141797, by rfl⟩ : syracuseStep 3025013 = 283595) (by norm_num)
theorem B2016675 : Blo 2015435 2016675 := bstep (se 1 (by rfl) ⟨1512506, by rfl⟩ : syracuseStep 2016675 = 3025013) B3025013
theorem B3828541 : Blo 2015435 3828541 := bbase (se 3 (by rfl) ⟨717851, by rfl⟩ : syracuseStep 3828541 = 1435703) (by norm_num)
theorem B5104721 : Blo 2015435 5104721 := bstep (se 2 (by rfl) ⟨1914270, by rfl⟩ : syracuseStep 5104721 = 3828541) B3828541
theorem B3403147 : Blo 2015435 3403147 := bstep (se 1 (by rfl) ⟨2552360, by rfl⟩ : syracuseStep 3403147 = 5104721) B5104721
theorem B4537529 : Blo 2015435 4537529 := bstep (se 2 (by rfl) ⟨1701573, by rfl⟩ : syracuseStep 4537529 = 3403147) B3403147
theorem B3025019 : Blo 2015435 3025019 := bstep (se 1 (by rfl) ⟨2268764, by rfl⟩ : syracuseStep 3025019 = 4537529) B4537529
theorem B2016679 : Blo 2015435 2016679 := bstep (se 1 (by rfl) ⟨1512509, by rfl⟩ : syracuseStep 2016679 = 3025019) B3025019
theorem B2268769 : Blo 2015435 2268769 := bbase (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) (by norm_num)
theorem B3025025 : Blo 2015435 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B2016683 : Blo 2015435 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B5104741 : Blo 2015435 5104741 := bbase (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) (by norm_num)
theorem B6806321 : Blo 2015435 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B4537547 : Blo 2015435 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B3025031 : Blo 2015435 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B2016687 : Blo 2015435 2016687 := bstep (se 1 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 2016687 = 3025031) B3025031
theorem B3025037 : Blo 2015435 3025037 := bbase (se 3 (by rfl) ⟨567194, by rfl⟩ : syracuseStep 3025037 = 1134389) (by norm_num)
theorem B2016691 : Blo 2015435 2016691 := bstep (se 1 (by rfl) ⟨1512518, by rfl⟩ : syracuseStep 2016691 = 3025037) B3025037
theorem B4537565 : Blo 2015435 4537565 := bbase (se 3 (by rfl) ⟨850793, by rfl⟩ : syracuseStep 4537565 = 1701587) (by norm_num)
theorem B3025043 : Blo 2015435 3025043 := bstep (se 1 (by rfl) ⟨2268782, by rfl⟩ : syracuseStep 3025043 = 4537565) B4537565
theorem B2016695 : Blo 2015435 2016695 := bstep (se 1 (by rfl) ⟨1512521, by rfl⟩ : syracuseStep 2016695 = 3025043) B3025043
theorem B3403181 : Blo 2015435 3403181 := bbase (se 3 (by rfl) ⟨638096, by rfl⟩ : syracuseStep 3403181 = 1276193) (by norm_num)
theorem B2268787 : Blo 2015435 2268787 := bstep (se 1 (by rfl) ⟨1701590, by rfl⟩ : syracuseStep 2268787 = 3403181) B3403181
theorem B3025049 : Blo 2015435 3025049 := bstep (se 2 (by rfl) ⟨1134393, by rfl⟩ : syracuseStep 3025049 = 2268787) B2268787
theorem B2016699 : Blo 2015435 2016699 := bstep (se 1 (by rfl) ⟨1512524, by rfl⟩ : syracuseStep 2016699 = 3025049) B3025049
theorem B4088437 : Blo 2015435 4088437 := bbase (se 5 (by rfl) ⟨191645, by rfl⟩ : syracuseStep 4088437 = 383291) (by norm_num)
theorem B87219989 : Blo 2015435 87219989 := bstep (se 6 (by rfl) ⟨2044218, by rfl⟩ : syracuseStep 87219989 = 4088437) B4088437
theorem B58146659 : Blo 2015435 58146659 := bstep (se 1 (by rfl) ⟨43609994, by rfl⟩ : syracuseStep 58146659 = 87219989) B87219989
theorem B38764439 : Blo 2015435 38764439 := bstep (se 1 (by rfl) ⟨29073329, by rfl⟩ : syracuseStep 38764439 = 58146659) B58146659
theorem B25842959 : Blo 2015435 25842959 := bstep (se 1 (by rfl) ⟨19382219, by rfl⟩ : syracuseStep 25842959 = 38764439) B38764439
theorem B17228639 : Blo 2015435 17228639 := bstep (se 1 (by rfl) ⟨12921479, by rfl⟩ : syracuseStep 17228639 = 25842959) B25842959
theorem B11485759 : Blo 2015435 11485759 := bstep (se 1 (by rfl) ⟨8614319, by rfl⟩ : syracuseStep 11485759 = 17228639) B17228639
theorem B15314345 : Blo 2015435 15314345 := bstep (se 2 (by rfl) ⟨5742879, by rfl⟩ : syracuseStep 15314345 = 11485759) B11485759
theorem B10209563 : Blo 2015435 10209563 := bstep (se 1 (by rfl) ⟨7657172, by rfl⟩ : syracuseStep 10209563 = 15314345) B15314345
theorem B6806375 : Blo 2015435 6806375 := bstep (se 1 (by rfl) ⟨5104781, by rfl⟩ : syracuseStep 6806375 = 10209563) B10209563
theorem B4537583 : Blo 2015435 4537583 := bstep (se 1 (by rfl) ⟨3403187, by rfl⟩ : syracuseStep 4537583 = 6806375) B6806375
theorem B3025055 : Blo 2015435 3025055 := bstep (se 1 (by rfl) ⟨2268791, by rfl⟩ : syracuseStep 3025055 = 4537583) B4537583
theorem B2016703 : Blo 2015435 2016703 := bstep (se 1 (by rfl) ⟨1512527, by rfl⟩ : syracuseStep 2016703 = 3025055) B3025055
theorem B3025061 : Blo 2015435 3025061 := bbase (se 4 (by rfl) ⟨283599, by rfl⟩ : syracuseStep 3025061 = 567199) (by norm_num)
theorem B2016707 : Blo 2015435 2016707 := bstep (se 1 (by rfl) ⟨1512530, by rfl⟩ : syracuseStep 2016707 = 3025061) B3025061
theorem B2552401 : Blo 2015435 2552401 := bbase (se 2 (by rfl) ⟨957150, by rfl⟩ : syracuseStep 2552401 = 1914301) (by norm_num)
theorem B3403201 : Blo 2015435 3403201 := bstep (se 2 (by rfl) ⟨1276200, by rfl⟩ : syracuseStep 3403201 = 2552401) B2552401
theorem B4537601 : Blo 2015435 4537601 := bstep (se 2 (by rfl) ⟨1701600, by rfl⟩ : syracuseStep 4537601 = 3403201) B3403201
theorem B3025067 : Blo 2015435 3025067 := bstep (se 1 (by rfl) ⟨2268800, by rfl⟩ : syracuseStep 3025067 = 4537601) B4537601
theorem B2016711 : Blo 2015435 2016711 := bstep (se 1 (by rfl) ⟨1512533, by rfl⟩ : syracuseStep 2016711 = 3025067) B3025067
theorem B2268805 : Blo 2015435 2268805 := bbase (se 4 (by rfl) ⟨212700, by rfl⟩ : syracuseStep 2268805 = 425401) (by norm_num)
theorem B3025073 : Blo 2015435 3025073 := bstep (se 2 (by rfl) ⟨1134402, by rfl⟩ : syracuseStep 3025073 = 2268805) B2268805
theorem B2016715 : Blo 2015435 2016715 := bstep (se 1 (by rfl) ⟨1512536, by rfl⟩ : syracuseStep 2016715 = 3025073) B3025073
theorem B5601061 : Blo 2015435 5601061 := bbase (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) (by norm_num)
theorem B7468081 : Blo 2015435 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B39829765 : Blo 2015435 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B53106353 : Blo 2015435 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B35404235 : Blo 2015435 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B23602823 : Blo 2015435 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B15735215 : Blo 2015435 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B10490143 : Blo 2015435 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B13986857 : Blo 2015435 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B9324571 : Blo 2015435 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B12432761 : Blo 2015435 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B8288507 : Blo 2015435 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B5525671 : Blo 2015435 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B7367561 : Blo 2015435 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B4911707 : Blo 2015435 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B3274471 : Blo 2015435 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B17463845 : Blo 2015435 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B11642563 : Blo 2015435 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B15523417 : Blo 2015435 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B20697889 : Blo 2015435 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B27597185 : Blo 2015435 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B18398123 : Blo 2015435 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B12265415 : Blo 2015435 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B8176943 : Blo 2015435 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B5451295 : Blo 2015435 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B7268393 : Blo 2015435 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B4845595 : Blo 2015435 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B6460793 : Blo 2015435 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B4307195 : Blo 2015435 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B2871463 : Blo 2015435 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B3828617 : Blo 2015435 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B2552411 : Blo 2015435 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B6806429 : Blo 2015435 6806429 := bstep (se 3 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 6806429 = 2552411) B2552411
theorem B4537619 : Blo 2015435 4537619 := bstep (se 1 (by rfl) ⟨3403214, by rfl⟩ : syracuseStep 4537619 = 6806429) B6806429
theorem B3025079 : Blo 2015435 3025079 := bstep (se 1 (by rfl) ⟨2268809, by rfl⟩ : syracuseStep 3025079 = 4537619) B4537619
theorem B2016719 : Blo 2015435 2016719 := bstep (se 1 (by rfl) ⟨1512539, by rfl⟩ : syracuseStep 2016719 = 3025079) B3025079
theorem B3025085 : Blo 2015435 3025085 := bbase (se 3 (by rfl) ⟨567203, by rfl⟩ : syracuseStep 3025085 = 1134407) (by norm_num)
theorem B2016723 : Blo 2015435 2016723 := bstep (se 1 (by rfl) ⟨1512542, by rfl⟩ : syracuseStep 2016723 = 3025085) B3025085
theorem B4537637 : Blo 2015435 4537637 := bbase (se 4 (by rfl) ⟨425403, by rfl⟩ : syracuseStep 4537637 = 850807) (by norm_num)
theorem B3025091 : Blo 2015435 3025091 := bstep (se 1 (by rfl) ⟨2268818, by rfl⟩ : syracuseStep 3025091 = 4537637) B4537637
theorem B2016727 : Blo 2015435 2016727 := bstep (se 1 (by rfl) ⟨1512545, by rfl⟩ : syracuseStep 2016727 = 3025091) B3025091
theorem B5104853 : Blo 2015435 5104853 := bbase (se 7 (by rfl) ⟨59822, by rfl⟩ : syracuseStep 5104853 = 119645) (by norm_num)
theorem B3403235 : Blo 2015435 3403235 := bstep (se 1 (by rfl) ⟨2552426, by rfl⟩ : syracuseStep 3403235 = 5104853) B5104853
theorem B2268823 : Blo 2015435 2268823 := bstep (se 1 (by rfl) ⟨1701617, by rfl⟩ : syracuseStep 2268823 = 3403235) B3403235
theorem B3025097 : Blo 2015435 3025097 := bstep (se 2 (by rfl) ⟨1134411, by rfl⟩ : syracuseStep 3025097 = 2268823) B2268823
theorem B2016731 : Blo 2015435 2016731 := bstep (se 1 (by rfl) ⟨1512548, by rfl⟩ : syracuseStep 2016731 = 3025097) B3025097
theorem B3880885 : Blo 2015435 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B5174513 : Blo 2015435 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B3449675 : Blo 2015435 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B9199133 : Blo 2015435 9199133 := bstep (se 3 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 9199133 = 3449675) B3449675
theorem B6132755 : Blo 2015435 6132755 := bstep (se 1 (by rfl) ⟨4599566, by rfl⟩ : syracuseStep 6132755 = 9199133) B9199133
theorem B4088503 : Blo 2015435 4088503 := bstep (se 1 (by rfl) ⟨3066377, by rfl⟩ : syracuseStep 4088503 = 6132755) B6132755
theorem B5451337 : Blo 2015435 5451337 := bstep (se 2 (by rfl) ⟨2044251, by rfl⟩ : syracuseStep 5451337 = 4088503) B4088503
theorem B7268449 : Blo 2015435 7268449 := bstep (se 2 (by rfl) ⟨2725668, by rfl⟩ : syracuseStep 7268449 = 5451337) B5451337
theorem B9691265 : Blo 2015435 9691265 := bstep (se 2 (by rfl) ⟨3634224, by rfl⟩ : syracuseStep 9691265 = 7268449) B7268449
theorem B6460843 : Blo 2015435 6460843 := bstep (se 1 (by rfl) ⟨4845632, by rfl⟩ : syracuseStep 6460843 = 9691265) B9691265
theorem B8614457 : Blo 2015435 8614457 := bstep (se 2 (by rfl) ⟨3230421, by rfl⟩ : syracuseStep 8614457 = 6460843) B6460843
theorem B5742971 : Blo 2015435 5742971 := bstep (se 1 (by rfl) ⟨4307228, by rfl⟩ : syracuseStep 5742971 = 8614457) B8614457
theorem B3828647 : Blo 2015435 3828647 := bstep (se 1 (by rfl) ⟨2871485, by rfl⟩ : syracuseStep 3828647 = 5742971) B5742971
theorem B10209725 : Blo 2015435 10209725 := bstep (se 3 (by rfl) ⟨1914323, by rfl⟩ : syracuseStep 10209725 = 3828647) B3828647
theorem B6806483 : Blo 2015435 6806483 := bstep (se 1 (by rfl) ⟨5104862, by rfl⟩ : syracuseStep 6806483 = 10209725) B10209725
theorem B4537655 : Blo 2015435 4537655 := bstep (se 1 (by rfl) ⟨3403241, by rfl⟩ : syracuseStep 4537655 = 6806483) B6806483
theorem B3025103 : Blo 2015435 3025103 := bstep (se 1 (by rfl) ⟨2268827, by rfl⟩ : syracuseStep 3025103 = 4537655) B4537655
theorem B2016735 : Blo 2015435 2016735 := bstep (se 1 (by rfl) ⟨1512551, by rfl⟩ : syracuseStep 2016735 = 3025103) B3025103
theorem B3025109 : Blo 2015435 3025109 := bbase (se 7 (by rfl) ⟨35450, by rfl⟩ : syracuseStep 3025109 = 70901) (by norm_num)
theorem B2016739 : Blo 2015435 2016739 := bstep (se 1 (by rfl) ⟨1512554, by rfl⟩ : syracuseStep 2016739 = 3025109) B3025109
theorem B4845653 : Blo 2015435 4845653 := bbase (se 8 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 4845653 = 56785) (by norm_num)
theorem B3230435 : Blo 2015435 3230435 := bstep (se 1 (by rfl) ⟨2422826, by rfl⟩ : syracuseStep 3230435 = 4845653) B4845653
theorem B2153623 : Blo 2015435 2153623 := bstep (se 1 (by rfl) ⟨1615217, by rfl⟩ : syracuseStep 2153623 = 3230435) B3230435
theorem B2871497 : Blo 2015435 2871497 := bstep (se 2 (by rfl) ⟨1076811, by rfl⟩ : syracuseStep 2871497 = 2153623) B2153623
theorem B7657325 : Blo 2015435 7657325 := bstep (se 3 (by rfl) ⟨1435748, by rfl⟩ : syracuseStep 7657325 = 2871497) B2871497
theorem B5104883 : Blo 2015435 5104883 := bstep (se 1 (by rfl) ⟨3828662, by rfl⟩ : syracuseStep 5104883 = 7657325) B7657325
theorem B3403255 : Blo 2015435 3403255 := bstep (se 1 (by rfl) ⟨2552441, by rfl⟩ : syracuseStep 3403255 = 5104883) B5104883
theorem B4537673 : Blo 2015435 4537673 := bstep (se 2 (by rfl) ⟨1701627, by rfl⟩ : syracuseStep 4537673 = 3403255) B3403255
theorem B3025115 : Blo 2015435 3025115 := bstep (se 1 (by rfl) ⟨2268836, by rfl⟩ : syracuseStep 3025115 = 4537673) B4537673
theorem B2016743 : Blo 2015435 2016743 := bstep (se 1 (by rfl) ⟨1512557, by rfl⟩ : syracuseStep 2016743 = 3025115) B3025115
theorem B2268841 : Blo 2015435 2268841 := bbase (se 2 (by rfl) ⟨850815, by rfl⟩ : syracuseStep 2268841 = 1701631) (by norm_num)
theorem B3025121 : Blo 2015435 3025121 := bstep (se 2 (by rfl) ⟨1134420, by rfl⟩ : syracuseStep 3025121 = 2268841) B2268841
theorem B2016747 : Blo 2015435 2016747 := bstep (se 1 (by rfl) ⟨1512560, by rfl⟩ : syracuseStep 2016747 = 3025121) B3025121
theorem B3592837 : Blo 2015435 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B4790449 : Blo 2015435 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B6387265 : Blo 2015435 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B8516353 : Blo 2015435 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B11355137 : Blo 2015435 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B7570091 : Blo 2015435 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B20186909 : Blo 2015435 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B13457939 : Blo 2015435 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B143551349 : Blo 2015435 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B95700899 : Blo 2015435 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B255202397 : Blo 2015435 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B170134931 : Blo 2015435 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B113423287 : Blo 2015435 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B151231049 : Blo 2015435 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B100820699 : Blo 2015435 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B67213799 : Blo 2015435 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B44809199 : Blo 2015435 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B29872799 : Blo 2015435 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B19915199 : Blo 2015435 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B13276799 : Blo 2015435 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B8851199 : Blo 2015435 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B94412789 : Blo 2015435 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B62941859 : Blo 2015435 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B41961239 : Blo 2015435 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B27974159 : Blo 2015435 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B18649439 : Blo 2015435 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B12432959 : Blo 2015435 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B8288639 : Blo 2015435 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B5525759 : Blo 2015435 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B3683839 : Blo 2015435 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B4911785 : Blo 2015435 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B3274523 : Blo 2015435 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B2183015 : Blo 2015435 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B5821373 : Blo 2015435 5821373 := bstep (se 3 (by rfl) ⟨1091507, by rfl⟩ : syracuseStep 5821373 = 2183015) B2183015
theorem B3880915 : Blo 2015435 3880915 := bstep (se 1 (by rfl) ⟨2910686, by rfl⟩ : syracuseStep 3880915 = 5821373) B5821373
theorem B20698213 : Blo 2015435 20698213 := bstep (se 4 (by rfl) ⟨1940457, by rfl⟩ : syracuseStep 20698213 = 3880915) B3880915
theorem B27597617 : Blo 2015435 27597617 := bstep (se 2 (by rfl) ⟨10349106, by rfl⟩ : syracuseStep 27597617 = 20698213) B20698213
theorem B18398411 : Blo 2015435 18398411 := bstep (se 1 (by rfl) ⟨13798808, by rfl⟩ : syracuseStep 18398411 = 27597617) B27597617
theorem B12265607 : Blo 2015435 12265607 := bstep (se 1 (by rfl) ⟨9199205, by rfl⟩ : syracuseStep 12265607 = 18398411) B18398411
theorem B8177071 : Blo 2015435 8177071 := bstep (se 1 (by rfl) ⟨6132803, by rfl⟩ : syracuseStep 8177071 = 12265607) B12265607
theorem B10902761 : Blo 2015435 10902761 := bstep (se 2 (by rfl) ⟨4088535, by rfl⟩ : syracuseStep 10902761 = 8177071) B8177071
theorem B7268507 : Blo 2015435 7268507 := bstep (se 1 (by rfl) ⟨5451380, by rfl⟩ : syracuseStep 7268507 = 10902761) B10902761
theorem B4845671 : Blo 2015435 4845671 := bstep (se 1 (by rfl) ⟨3634253, by rfl⟩ : syracuseStep 4845671 = 7268507) B7268507
theorem B3230447 : Blo 2015435 3230447 := bstep (se 1 (by rfl) ⟨2422835, by rfl⟩ : syracuseStep 3230447 = 4845671) B4845671
theorem B8614525 : Blo 2015435 8614525 := bstep (se 3 (by rfl) ⟨1615223, by rfl⟩ : syracuseStep 8614525 = 3230447) B3230447
theorem B11486033 : Blo 2015435 11486033 := bstep (se 2 (by rfl) ⟨4307262, by rfl⟩ : syracuseStep 11486033 = 8614525) B8614525
theorem B7657355 : Blo 2015435 7657355 := bstep (se 1 (by rfl) ⟨5743016, by rfl⟩ : syracuseStep 7657355 = 11486033) B11486033
theorem B5104903 : Blo 2015435 5104903 := bstep (se 1 (by rfl) ⟨3828677, by rfl⟩ : syracuseStep 5104903 = 7657355) B7657355
theorem B6806537 : Blo 2015435 6806537 := bstep (se 2 (by rfl) ⟨2552451, by rfl⟩ : syracuseStep 6806537 = 5104903) B5104903
theorem B4537691 : Blo 2015435 4537691 := bstep (se 1 (by rfl) ⟨3403268, by rfl⟩ : syracuseStep 4537691 = 6806537) B6806537
theorem B3025127 : Blo 2015435 3025127 := bstep (se 1 (by rfl) ⟨2268845, by rfl⟩ : syracuseStep 3025127 = 4537691) B4537691
theorem B2016751 : Blo 2015435 2016751 := bstep (se 1 (by rfl) ⟨1512563, by rfl⟩ : syracuseStep 2016751 = 3025127) B3025127
theorem B3025133 : Blo 2015435 3025133 := bbase (se 3 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 3025133 = 1134425) (by norm_num)
theorem B2016755 : Blo 2015435 2016755 := bstep (se 1 (by rfl) ⟨1512566, by rfl⟩ : syracuseStep 2016755 = 3025133) B3025133
theorem B4537709 : Blo 2015435 4537709 := bbase (se 3 (by rfl) ⟨850820, by rfl⟩ : syracuseStep 4537709 = 1701641) (by norm_num)
theorem B3025139 : Blo 2015435 3025139 := bstep (se 1 (by rfl) ⟨2268854, by rfl⟩ : syracuseStep 3025139 = 4537709) B4537709
theorem B2016759 : Blo 2015435 2016759 := bstep (se 1 (by rfl) ⟨1512569, by rfl⟩ : syracuseStep 2016759 = 3025139) B3025139
theorem B3828701 : Blo 2015435 3828701 := bbase (se 3 (by rfl) ⟨717881, by rfl⟩ : syracuseStep 3828701 = 1435763) (by norm_num)
theorem B2552467 : Blo 2015435 2552467 := bstep (se 1 (by rfl) ⟨1914350, by rfl⟩ : syracuseStep 2552467 = 3828701) B3828701
theorem B3403289 : Blo 2015435 3403289 := bstep (se 2 (by rfl) ⟨1276233, by rfl⟩ : syracuseStep 3403289 = 2552467) B2552467
theorem B2268859 : Blo 2015435 2268859 := bstep (se 1 (by rfl) ⟨1701644, by rfl⟩ : syracuseStep 2268859 = 3403289) B3403289
theorem B3025145 : Blo 2015435 3025145 := bstep (se 2 (by rfl) ⟨1134429, by rfl⟩ : syracuseStep 3025145 = 2268859) B2268859
theorem B2016763 : Blo 2015435 2016763 := bstep (se 1 (by rfl) ⟨1512572, by rfl⟩ : syracuseStep 2016763 = 3025145) B3025145
theorem B2587297 : Blo 2015435 2587297 := bbase (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) (by norm_num)
theorem B3449729 : Blo 2015435 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B9199277 : Blo 2015435 9199277 := bstep (se 3 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 9199277 = 3449729) B3449729
theorem B6132851 : Blo 2015435 6132851 := bstep (se 1 (by rfl) ⟨4599638, by rfl⟩ : syracuseStep 6132851 = 9199277) B9199277
theorem B4088567 : Blo 2015435 4088567 := bstep (se 1 (by rfl) ⟨3066425, by rfl⟩ : syracuseStep 4088567 = 6132851) B6132851
theorem B10902845 : Blo 2015435 10902845 := bstep (se 3 (by rfl) ⟨2044283, by rfl⟩ : syracuseStep 10902845 = 4088567) B4088567
theorem B7268563 : Blo 2015435 7268563 := bstep (se 1 (by rfl) ⟨5451422, by rfl⟩ : syracuseStep 7268563 = 10902845) B10902845
theorem B9691417 : Blo 2015435 9691417 := bstep (se 2 (by rfl) ⟨3634281, by rfl⟩ : syracuseStep 9691417 = 7268563) B7268563
theorem B51687557 : Blo 2015435 51687557 := bstep (se 4 (by rfl) ⟨4845708, by rfl⟩ : syracuseStep 51687557 = 9691417) B9691417
theorem B34458371 : Blo 2015435 34458371 := bstep (se 1 (by rfl) ⟨25843778, by rfl⟩ : syracuseStep 34458371 = 51687557) B51687557
theorem B22972247 : Blo 2015435 22972247 := bstep (se 1 (by rfl) ⟨17229185, by rfl⟩ : syracuseStep 22972247 = 34458371) B34458371
theorem B15314831 : Blo 2015435 15314831 := bstep (se 1 (by rfl) ⟨11486123, by rfl⟩ : syracuseStep 15314831 = 22972247) B22972247
theorem B10209887 : Blo 2015435 10209887 := bstep (se 1 (by rfl) ⟨7657415, by rfl⟩ : syracuseStep 10209887 = 15314831) B15314831
theorem B6806591 : Blo 2015435 6806591 := bstep (se 1 (by rfl) ⟨5104943, by rfl⟩ : syracuseStep 6806591 = 10209887) B10209887
theorem B4537727 : Blo 2015435 4537727 := bstep (se 1 (by rfl) ⟨3403295, by rfl⟩ : syracuseStep 4537727 = 6806591) B6806591
theorem B3025151 : Blo 2015435 3025151 := bstep (se 1 (by rfl) ⟨2268863, by rfl⟩ : syracuseStep 3025151 = 4537727) B4537727
theorem B2016767 : Blo 2015435 2016767 := bstep (se 1 (by rfl) ⟨1512575, by rfl⟩ : syracuseStep 2016767 = 3025151) B3025151
theorem B3025157 : Blo 2015435 3025157 := bbase (se 4 (by rfl) ⟨283608, by rfl⟩ : syracuseStep 3025157 = 567217) (by norm_num)
theorem B2016771 : Blo 2015435 2016771 := bstep (se 1 (by rfl) ⟨1512578, by rfl⟩ : syracuseStep 2016771 = 3025157) B3025157
theorem B3403309 : Blo 2015435 3403309 := bbase (se 3 (by rfl) ⟨638120, by rfl⟩ : syracuseStep 3403309 = 1276241) (by norm_num)
theorem B4537745 : Blo 2015435 4537745 := bstep (se 2 (by rfl) ⟨1701654, by rfl⟩ : syracuseStep 4537745 = 3403309) B3403309
theorem B3025163 : Blo 2015435 3025163 := bstep (se 1 (by rfl) ⟨2268872, by rfl⟩ : syracuseStep 3025163 = 4537745) B4537745
theorem B2016775 : Blo 2015435 2016775 := bstep (se 1 (by rfl) ⟨1512581, by rfl⟩ : syracuseStep 2016775 = 3025163) B3025163
theorem B2268877 : Blo 2015435 2268877 := bbase (se 3 (by rfl) ⟨425414, by rfl⟩ : syracuseStep 2268877 = 850829) (by norm_num)
theorem B3025169 : Blo 2015435 3025169 := bstep (se 2 (by rfl) ⟨1134438, by rfl⟩ : syracuseStep 3025169 = 2268877) B2268877
theorem B2016779 : Blo 2015435 2016779 := bstep (se 1 (by rfl) ⟨1512584, by rfl⟩ : syracuseStep 2016779 = 3025169) B3025169
theorem B6806645 : Blo 2015435 6806645 := bbase (se 5 (by rfl) ⟨319061, by rfl⟩ : syracuseStep 6806645 = 638123) (by norm_num)
theorem B4537763 : Blo 2015435 4537763 := bstep (se 1 (by rfl) ⟨3403322, by rfl⟩ : syracuseStep 4537763 = 6806645) B6806645
theorem B3025175 : Blo 2015435 3025175 := bstep (se 1 (by rfl) ⟨2268881, by rfl⟩ : syracuseStep 3025175 = 4537763) B4537763
theorem B2016783 : Blo 2015435 2016783 := bstep (se 1 (by rfl) ⟨1512587, by rfl⟩ : syracuseStep 2016783 = 3025175) B3025175
theorem B3025181 : Blo 2015435 3025181 := bbase (se 3 (by rfl) ⟨567221, by rfl⟩ : syracuseStep 3025181 = 1134443) (by norm_num)
theorem B2016787 : Blo 2015435 2016787 := bstep (se 1 (by rfl) ⟨1512590, by rfl⟩ : syracuseStep 2016787 = 3025181) B3025181
theorem B4537781 : Blo 2015435 4537781 := bbase (se 5 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 4537781 = 425417) (by norm_num)
theorem B3025187 : Blo 2015435 3025187 := bstep (se 1 (by rfl) ⟨2268890, by rfl⟩ : syracuseStep 3025187 = 4537781) B4537781
theorem B2016791 : Blo 2015435 2016791 := bstep (se 1 (by rfl) ⟨1512593, by rfl⟩ : syracuseStep 2016791 = 3025187) B3025187
theorem B4307357 : Blo 2015435 4307357 := bbase (se 3 (by rfl) ⟨807629, by rfl⟩ : syracuseStep 4307357 = 1615259) (by norm_num)
theorem B11486285 : Blo 2015435 11486285 := bstep (se 3 (by rfl) ⟨2153678, by rfl⟩ : syracuseStep 11486285 = 4307357) B4307357
theorem B7657523 : Blo 2015435 7657523 := bstep (se 1 (by rfl) ⟨5743142, by rfl⟩ : syracuseStep 7657523 = 11486285) B11486285
theorem B5105015 : Blo 2015435 5105015 := bstep (se 1 (by rfl) ⟨3828761, by rfl⟩ : syracuseStep 5105015 = 7657523) B7657523
theorem B3403343 : Blo 2015435 3403343 := bstep (se 1 (by rfl) ⟨2552507, by rfl⟩ : syracuseStep 3403343 = 5105015) B5105015
theorem B2268895 : Blo 2015435 2268895 := bstep (se 1 (by rfl) ⟨1701671, by rfl⟩ : syracuseStep 2268895 = 3403343) B3403343
theorem B3025193 : Blo 2015435 3025193 := bstep (se 2 (by rfl) ⟨1134447, by rfl⟩ : syracuseStep 3025193 = 2268895) B2268895
theorem B2016795 : Blo 2015435 2016795 := bstep (se 1 (by rfl) ⟨1512596, by rfl⟩ : syracuseStep 2016795 = 3025193) B3025193
theorem B4307365 : Blo 2015435 4307365 := bbase (se 4 (by rfl) ⟨403815, by rfl⟩ : syracuseStep 4307365 = 807631) (by norm_num)
theorem B5743153 : Blo 2015435 5743153 := bstep (se 2 (by rfl) ⟨2153682, by rfl⟩ : syracuseStep 5743153 = 4307365) B4307365
theorem B7657537 : Blo 2015435 7657537 := bstep (se 2 (by rfl) ⟨2871576, by rfl⟩ : syracuseStep 7657537 = 5743153) B5743153
theorem B10210049 : Blo 2015435 10210049 := bstep (se 2 (by rfl) ⟨3828768, by rfl⟩ : syracuseStep 10210049 = 7657537) B7657537
theorem B6806699 : Blo 2015435 6806699 := bstep (se 1 (by rfl) ⟨5105024, by rfl⟩ : syracuseStep 6806699 = 10210049) B10210049
theorem B4537799 : Blo 2015435 4537799 := bstep (se 1 (by rfl) ⟨3403349, by rfl⟩ : syracuseStep 4537799 = 6806699) B6806699
theorem B3025199 : Blo 2015435 3025199 := bstep (se 1 (by rfl) ⟨2268899, by rfl⟩ : syracuseStep 3025199 = 4537799) B4537799
theorem B2016799 : Blo 2015435 2016799 := bstep (se 1 (by rfl) ⟨1512599, by rfl⟩ : syracuseStep 2016799 = 3025199) B3025199
theorem B3025205 : Blo 2015435 3025205 := bbase (se 5 (by rfl) ⟨141806, by rfl⟩ : syracuseStep 3025205 = 283613) (by norm_num)
theorem B2016803 : Blo 2015435 2016803 := bstep (se 1 (by rfl) ⟨1512602, by rfl⟩ : syracuseStep 2016803 = 3025205) B3025205
theorem B5105045 : Blo 2015435 5105045 := bbase (se 6 (by rfl) ⟨119649, by rfl⟩ : syracuseStep 5105045 = 239299) (by norm_num)
theorem B3403363 : Blo 2015435 3403363 := bstep (se 1 (by rfl) ⟨2552522, by rfl⟩ : syracuseStep 3403363 = 5105045) B5105045
theorem B4537817 : Blo 2015435 4537817 := bstep (se 2 (by rfl) ⟨1701681, by rfl⟩ : syracuseStep 4537817 = 3403363) B3403363
theorem B3025211 : Blo 2015435 3025211 := bstep (se 1 (by rfl) ⟨2268908, by rfl⟩ : syracuseStep 3025211 = 4537817) B4537817
theorem B2016807 : Blo 2015435 2016807 := bstep (se 1 (by rfl) ⟨1512605, by rfl⟩ : syracuseStep 2016807 = 3025211) B3025211
theorem B2268913 : Blo 2015435 2268913 := bbase (se 2 (by rfl) ⟨850842, by rfl⟩ : syracuseStep 2268913 = 1701685) (by norm_num)
theorem B3025217 : Blo 2015435 3025217 := bstep (se 2 (by rfl) ⟨1134456, by rfl⟩ : syracuseStep 3025217 = 2268913) B2268913
theorem B2016811 : Blo 2015435 2016811 := bstep (se 1 (by rfl) ⟨1512608, by rfl⟩ : syracuseStep 2016811 = 3025217) B3025217
theorem B4599749 : Blo 2015435 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B3066499 : Blo 2015435 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B4088665 : Blo 2015435 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B5451553 : Blo 2015435 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B29074949 : Blo 2015435 29074949 := bstep (se 4 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 29074949 = 5451553) B5451553
theorem B19383299 : Blo 2015435 19383299 := bstep (se 1 (by rfl) ⟨14537474, by rfl⟩ : syracuseStep 19383299 = 29074949) B29074949
theorem B12922199 : Blo 2015435 12922199 := bstep (se 1 (by rfl) ⟨9691649, by rfl⟩ : syracuseStep 12922199 = 19383299) B19383299
theorem B8614799 : Blo 2015435 8614799 := bstep (se 1 (by rfl) ⟨6461099, by rfl⟩ : syracuseStep 8614799 = 12922199) B12922199
theorem B5743199 : Blo 2015435 5743199 := bstep (se 1 (by rfl) ⟨4307399, by rfl⟩ : syracuseStep 5743199 = 8614799) B8614799
theorem B3828799 : Blo 2015435 3828799 := bstep (se 1 (by rfl) ⟨2871599, by rfl⟩ : syracuseStep 3828799 = 5743199) B5743199
theorem B5105065 : Blo 2015435 5105065 := bstep (se 2 (by rfl) ⟨1914399, by rfl⟩ : syracuseStep 5105065 = 3828799) B3828799
theorem B6806753 : Blo 2015435 6806753 := bstep (se 2 (by rfl) ⟨2552532, by rfl⟩ : syracuseStep 6806753 = 5105065) B5105065
theorem B4537835 : Blo 2015435 4537835 := bstep (se 1 (by rfl) ⟨3403376, by rfl⟩ : syracuseStep 4537835 = 6806753) B6806753
theorem B3025223 : Blo 2015435 3025223 := bstep (se 1 (by rfl) ⟨2268917, by rfl⟩ : syracuseStep 3025223 = 4537835) B4537835
theorem B2016815 : Blo 2015435 2016815 := bstep (se 1 (by rfl) ⟨1512611, by rfl⟩ : syracuseStep 2016815 = 3025223) B3025223
theorem B3025229 : Blo 2015435 3025229 := bbase (se 3 (by rfl) ⟨567230, by rfl⟩ : syracuseStep 3025229 = 1134461) (by norm_num)
theorem B2016819 : Blo 2015435 2016819 := bstep (se 1 (by rfl) ⟨1512614, by rfl⟩ : syracuseStep 2016819 = 3025229) B3025229
theorem B4537853 : Blo 2015435 4537853 := bbase (se 3 (by rfl) ⟨850847, by rfl⟩ : syracuseStep 4537853 = 1701695) (by norm_num)
theorem B3025235 : Blo 2015435 3025235 := bstep (se 1 (by rfl) ⟨2268926, by rfl⟩ : syracuseStep 3025235 = 4537853) B4537853
theorem B2016823 : Blo 2015435 2016823 := bstep (se 1 (by rfl) ⟨1512617, by rfl⟩ : syracuseStep 2016823 = 3025235) B3025235
theorem B3403397 : Blo 2015435 3403397 := bbase (se 4 (by rfl) ⟨319068, by rfl⟩ : syracuseStep 3403397 = 638137) (by norm_num)
theorem B2268931 : Blo 2015435 2268931 := bstep (se 1 (by rfl) ⟨1701698, by rfl⟩ : syracuseStep 2268931 = 3403397) B3403397
theorem B3025241 : Blo 2015435 3025241 := bstep (se 2 (by rfl) ⟨1134465, by rfl⟩ : syracuseStep 3025241 = 2268931) B2268931
theorem B2016827 : Blo 2015435 2016827 := bstep (se 1 (by rfl) ⟨1512620, by rfl⟩ : syracuseStep 2016827 = 3025241) B3025241
theorem B15315317 : Blo 2015435 15315317 := bbase (se 5 (by rfl) ⟨717905, by rfl⟩ : syracuseStep 15315317 = 1435811) (by norm_num)
theorem B10210211 : Blo 2015435 10210211 := bstep (se 1 (by rfl) ⟨7657658, by rfl⟩ : syracuseStep 10210211 = 15315317) B15315317
theorem B6806807 : Blo 2015435 6806807 := bstep (se 1 (by rfl) ⟨5105105, by rfl⟩ : syracuseStep 6806807 = 10210211) B10210211
theorem B4537871 : Blo 2015435 4537871 := bstep (se 1 (by rfl) ⟨3403403, by rfl⟩ : syracuseStep 4537871 = 6806807) B6806807
theorem B3025247 : Blo 2015435 3025247 := bstep (se 1 (by rfl) ⟨2268935, by rfl⟩ : syracuseStep 3025247 = 4537871) B4537871
theorem B2016831 : Blo 2015435 2016831 := bstep (se 1 (by rfl) ⟨1512623, by rfl⟩ : syracuseStep 2016831 = 3025247) B3025247
theorem B3025253 : Blo 2015435 3025253 := bbase (se 4 (by rfl) ⟨283617, by rfl⟩ : syracuseStep 3025253 = 567235) (by norm_num)
theorem B2016835 : Blo 2015435 2016835 := bstep (se 1 (by rfl) ⟨1512626, by rfl⟩ : syracuseStep 2016835 = 3025253) B3025253
theorem B3828845 : Blo 2015435 3828845 := bbase (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) (by norm_num)
theorem B2552563 : Blo 2015435 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B3403417 : Blo 2015435 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B4537889 : Blo 2015435 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B3025259 : Blo 2015435 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B2016839 : Blo 2015435 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B2268949 : Blo 2015435 2268949 := bbase (se 6 (by rfl) ⟨53178, by rfl⟩ : syracuseStep 2268949 = 106357) (by norm_num)
theorem B3025265 : Blo 2015435 3025265 := bstep (se 2 (by rfl) ⟨1134474, by rfl⟩ : syracuseStep 3025265 = 2268949) B2268949
theorem B2016843 : Blo 2015435 2016843 := bstep (se 1 (by rfl) ⟨1512632, by rfl⟩ : syracuseStep 2016843 = 3025265) B3025265
theorem B2552573 : Blo 2015435 2552573 := bbase (se 3 (by rfl) ⟨478607, by rfl⟩ : syracuseStep 2552573 = 957215) (by norm_num)
theorem B6806861 : Blo 2015435 6806861 := bstep (se 3 (by rfl) ⟨1276286, by rfl⟩ : syracuseStep 6806861 = 2552573) B2552573
theorem B4537907 : Blo 2015435 4537907 := bstep (se 1 (by rfl) ⟨3403430, by rfl⟩ : syracuseStep 4537907 = 6806861) B6806861
theorem B3025271 : Blo 2015435 3025271 := bstep (se 1 (by rfl) ⟨2268953, by rfl⟩ : syracuseStep 3025271 = 4537907) B4537907
theorem B2016847 : Blo 2015435 2016847 := bstep (se 1 (by rfl) ⟨1512635, by rfl⟩ : syracuseStep 2016847 = 3025271) B3025271
theorem B3025277 : Blo 2015435 3025277 := bbase (se 3 (by rfl) ⟨567239, by rfl⟩ : syracuseStep 3025277 = 1134479) (by norm_num)
theorem B2016851 : Blo 2015435 2016851 := bstep (se 1 (by rfl) ⟨1512638, by rfl⟩ : syracuseStep 2016851 = 3025277) B3025277
theorem B4537925 : Blo 2015435 4537925 := bbase (se 4 (by rfl) ⟨425430, by rfl⟩ : syracuseStep 4537925 = 850861) (by norm_num)
theorem B3025283 : Blo 2015435 3025283 := bstep (se 1 (by rfl) ⟨2268962, by rfl⟩ : syracuseStep 3025283 = 4537925) B4537925
theorem B2016855 : Blo 2015435 2016855 := bstep (se 1 (by rfl) ⟨1512641, by rfl⟩ : syracuseStep 2016855 = 3025283) B3025283
theorem B3230621 : Blo 2015435 3230621 := bbase (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) (by norm_num)
theorem B2153747 : Blo 2015435 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B5743325 : Blo 2015435 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B3828883 : Blo 2015435 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B5105177 : Blo 2015435 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B3403451 : Blo 2015435 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B2268967 : Blo 2015435 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B3025289 : Blo 2015435 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B2016859 : Blo 2015435 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B10210373 : Blo 2015435 10210373 := bbase (se 4 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 10210373 = 1914445) (by norm_num)
theorem B6806915 : Blo 2015435 6806915 := bstep (se 1 (by rfl) ⟨5105186, by rfl⟩ : syracuseStep 6806915 = 10210373) B10210373
theorem B4537943 : Blo 2015435 4537943 := bstep (se 1 (by rfl) ⟨3403457, by rfl⟩ : syracuseStep 4537943 = 6806915) B6806915
theorem B3025295 : Blo 2015435 3025295 := bstep (se 1 (by rfl) ⟨2268971, by rfl⟩ : syracuseStep 3025295 = 4537943) B4537943
theorem B2016863 : Blo 2015435 2016863 := bstep (se 1 (by rfl) ⟨1512647, by rfl⟩ : syracuseStep 2016863 = 3025295) B3025295
theorem B3025301 : Blo 2015435 3025301 := bbase (se 6 (by rfl) ⟨70905, by rfl⟩ : syracuseStep 3025301 = 141811) (by norm_num)
theorem B2016867 : Blo 2015435 2016867 := bstep (se 1 (by rfl) ⟨1512650, by rfl⟩ : syracuseStep 2016867 = 3025301) B3025301
theorem B32710229 : Blo 2015435 32710229 := bbase (se 8 (by rfl) ⟨191661, by rfl⟩ : syracuseStep 32710229 = 383323) (by norm_num)
theorem B21806819 : Blo 2015435 21806819 := bstep (se 1 (by rfl) ⟨16355114, by rfl⟩ : syracuseStep 21806819 = 32710229) B32710229
theorem B14537879 : Blo 2015435 14537879 := bstep (se 1 (by rfl) ⟨10903409, by rfl⟩ : syracuseStep 14537879 = 21806819) B21806819
theorem B9691919 : Blo 2015435 9691919 := bstep (se 1 (by rfl) ⟨7268939, by rfl⟩ : syracuseStep 9691919 = 14537879) B14537879
theorem B6461279 : Blo 2015435 6461279 := bstep (se 1 (by rfl) ⟨4845959, by rfl⟩ : syracuseStep 6461279 = 9691919) B9691919
theorem B4307519 : Blo 2015435 4307519 := bstep (se 1 (by rfl) ⟨3230639, by rfl⟩ : syracuseStep 4307519 = 6461279) B6461279
theorem B11486717 : Blo 2015435 11486717 := bstep (se 3 (by rfl) ⟨2153759, by rfl⟩ : syracuseStep 11486717 = 4307519) B4307519
theorem B7657811 : Blo 2015435 7657811 := bstep (se 1 (by rfl) ⟨5743358, by rfl⟩ : syracuseStep 7657811 = 11486717) B11486717
theorem B5105207 : Blo 2015435 5105207 := bstep (se 1 (by rfl) ⟨3828905, by rfl⟩ : syracuseStep 5105207 = 7657811) B7657811
theorem B3403471 : Blo 2015435 3403471 := bstep (se 1 (by rfl) ⟨2552603, by rfl⟩ : syracuseStep 3403471 = 5105207) B5105207
theorem B4537961 : Blo 2015435 4537961 := bstep (se 2 (by rfl) ⟨1701735, by rfl⟩ : syracuseStep 4537961 = 3403471) B3403471
theorem B3025307 : Blo 2015435 3025307 := bstep (se 1 (by rfl) ⟨2268980, by rfl⟩ : syracuseStep 3025307 = 4537961) B4537961
theorem B2016871 : Blo 2015435 2016871 := bstep (se 1 (by rfl) ⟨1512653, by rfl⟩ : syracuseStep 2016871 = 3025307) B3025307
theorem B2268985 : Blo 2015435 2268985 := bbase (se 2 (by rfl) ⟨850869, by rfl⟩ : syracuseStep 2268985 = 1701739) (by norm_num)
theorem B3025313 : Blo 2015435 3025313 := bstep (se 2 (by rfl) ⟨1134492, by rfl⟩ : syracuseStep 3025313 = 2268985) B2268985
theorem B2016875 : Blo 2015435 2016875 := bstep (se 1 (by rfl) ⟨1512656, by rfl⟩ : syracuseStep 2016875 = 3025313) B3025313
theorem B5743381 : Blo 2015435 5743381 := bbase (se 6 (by rfl) ⟨134610, by rfl⟩ : syracuseStep 5743381 = 269221) (by norm_num)
theorem B7657841 : Blo 2015435 7657841 := bstep (se 2 (by rfl) ⟨2871690, by rfl⟩ : syracuseStep 7657841 = 5743381) B5743381
theorem B5105227 : Blo 2015435 5105227 := bstep (se 1 (by rfl) ⟨3828920, by rfl⟩ : syracuseStep 5105227 = 7657841) B7657841
theorem B6806969 : Blo 2015435 6806969 := bstep (se 2 (by rfl) ⟨2552613, by rfl⟩ : syracuseStep 6806969 = 5105227) B5105227
theorem B4537979 : Blo 2015435 4537979 := bstep (se 1 (by rfl) ⟨3403484, by rfl⟩ : syracuseStep 4537979 = 6806969) B6806969
theorem B3025319 : Blo 2015435 3025319 := bstep (se 1 (by rfl) ⟨2268989, by rfl⟩ : syracuseStep 3025319 = 4537979) B4537979
theorem B2016879 : Blo 2015435 2016879 := bstep (se 1 (by rfl) ⟨1512659, by rfl⟩ : syracuseStep 2016879 = 3025319) B3025319
theorem B3025325 : Blo 2015435 3025325 := bbase (se 3 (by rfl) ⟨567248, by rfl⟩ : syracuseStep 3025325 = 1134497) (by norm_num)
theorem B2016883 : Blo 2015435 2016883 := bstep (se 1 (by rfl) ⟨1512662, by rfl⟩ : syracuseStep 2016883 = 3025325) B3025325
theorem B4537997 : Blo 2015435 4537997 := bbase (se 3 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 4537997 = 1701749) (by norm_num)
theorem B3025331 : Blo 2015435 3025331 := bstep (se 1 (by rfl) ⟨2268998, by rfl⟩ : syracuseStep 3025331 = 4537997) B4537997
theorem B2016887 : Blo 2015435 2016887 := bstep (se 1 (by rfl) ⟨1512665, by rfl⟩ : syracuseStep 2016887 = 3025331) B3025331
theorem B2552629 : Blo 2015435 2552629 := bbase (se 5 (by rfl) ⟨119654, by rfl⟩ : syracuseStep 2552629 = 239309) (by norm_num)
theorem B3403505 : Blo 2015435 3403505 := bstep (se 2 (by rfl) ⟨1276314, by rfl⟩ : syracuseStep 3403505 = 2552629) B2552629
theorem B2269003 : Blo 2015435 2269003 := bstep (se 1 (by rfl) ⟨1701752, by rfl⟩ : syracuseStep 2269003 = 3403505) B3403505
theorem B3025337 : Blo 2015435 3025337 := bstep (se 2 (by rfl) ⟨1134501, by rfl⟩ : syracuseStep 3025337 = 2269003) B2269003
theorem B2016891 : Blo 2015435 2016891 := bstep (se 1 (by rfl) ⟨1512668, by rfl⟩ : syracuseStep 2016891 = 3025337) B3025337
theorem B5526149 : Blo 2015435 5526149 := bbase (se 4 (by rfl) ⟨518076, by rfl⟩ : syracuseStep 5526149 = 1036153) (by norm_num)
theorem B58945589 : Blo 2015435 58945589 := bstep (se 5 (by rfl) ⟨2763074, by rfl⟩ : syracuseStep 58945589 = 5526149) B5526149
theorem B39297059 : Blo 2015435 39297059 := bstep (se 1 (by rfl) ⟨29472794, by rfl⟩ : syracuseStep 39297059 = 58945589) B58945589
theorem B26198039 : Blo 2015435 26198039 := bstep (se 1 (by rfl) ⟨19648529, by rfl⟩ : syracuseStep 26198039 = 39297059) B39297059
theorem B69861437 : Blo 2015435 69861437 := bstep (se 3 (by rfl) ⟨13099019, by rfl⟩ : syracuseStep 69861437 = 26198039) B26198039
theorem B46574291 : Blo 2015435 46574291 := bstep (se 1 (by rfl) ⟨34930718, by rfl⟩ : syracuseStep 46574291 = 69861437) B69861437
theorem B31049527 : Blo 2015435 31049527 := bstep (se 1 (by rfl) ⟨23287145, by rfl⟩ : syracuseStep 31049527 = 46574291) B46574291
theorem B41399369 : Blo 2015435 41399369 := bstep (se 2 (by rfl) ⟨15524763, by rfl⟩ : syracuseStep 41399369 = 31049527) B31049527
theorem B27599579 : Blo 2015435 27599579 := bstep (se 1 (by rfl) ⟨20699684, by rfl⟩ : syracuseStep 27599579 = 41399369) B41399369
theorem B18399719 : Blo 2015435 18399719 := bstep (se 1 (by rfl) ⟨13799789, by rfl⟩ : syracuseStep 18399719 = 27599579) B27599579
theorem B12266479 : Blo 2015435 12266479 := bstep (se 1 (by rfl) ⟨9199859, by rfl⟩ : syracuseStep 12266479 = 18399719) B18399719
theorem B16355305 : Blo 2015435 16355305 := bstep (se 2 (by rfl) ⟨6133239, by rfl⟩ : syracuseStep 16355305 = 12266479) B12266479
theorem B21807073 : Blo 2015435 21807073 := bstep (se 2 (by rfl) ⟨8177652, by rfl⟩ : syracuseStep 21807073 = 16355305) B16355305
theorem B29076097 : Blo 2015435 29076097 := bstep (se 2 (by rfl) ⟨10903536, by rfl⟩ : syracuseStep 29076097 = 21807073) B21807073
theorem B38768129 : Blo 2015435 38768129 := bstep (se 2 (by rfl) ⟨14538048, by rfl⟩ : syracuseStep 38768129 = 29076097) B29076097
theorem B25845419 : Blo 2015435 25845419 := bstep (se 1 (by rfl) ⟨19384064, by rfl⟩ : syracuseStep 25845419 = 38768129) B38768129
theorem B17230279 : Blo 2015435 17230279 := bstep (se 1 (by rfl) ⟨12922709, by rfl⟩ : syracuseStep 17230279 = 25845419) B25845419
theorem B22973705 : Blo 2015435 22973705 := bstep (se 2 (by rfl) ⟨8615139, by rfl⟩ : syracuseStep 22973705 = 17230279) B17230279
theorem B15315803 : Blo 2015435 15315803 := bstep (se 1 (by rfl) ⟨11486852, by rfl⟩ : syracuseStep 15315803 = 22973705) B22973705
theorem B10210535 : Blo 2015435 10210535 := bstep (se 1 (by rfl) ⟨7657901, by rfl⟩ : syracuseStep 10210535 = 15315803) B15315803
theorem B6807023 : Blo 2015435 6807023 := bstep (se 1 (by rfl) ⟨5105267, by rfl⟩ : syracuseStep 6807023 = 10210535) B10210535
theorem B4538015 : Blo 2015435 4538015 := bstep (se 1 (by rfl) ⟨3403511, by rfl⟩ : syracuseStep 4538015 = 6807023) B6807023
theorem B3025343 : Blo 2015435 3025343 := bstep (se 1 (by rfl) ⟨2269007, by rfl⟩ : syracuseStep 3025343 = 4538015) B4538015
theorem B2016895 : Blo 2015435 2016895 := bstep (se 1 (by rfl) ⟨1512671, by rfl⟩ : syracuseStep 2016895 = 3025343) B3025343
theorem B3025349 : Blo 2015435 3025349 := bbase (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) (by norm_num)
theorem B2016899 : Blo 2015435 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B3403525 : Blo 2015435 3403525 := bbase (se 4 (by rfl) ⟨319080, by rfl⟩ : syracuseStep 3403525 = 638161) (by norm_num)
theorem B4538033 : Blo 2015435 4538033 := bstep (se 2 (by rfl) ⟨1701762, by rfl⟩ : syracuseStep 4538033 = 3403525) B3403525
theorem B3025355 : Blo 2015435 3025355 := bstep (se 1 (by rfl) ⟨2269016, by rfl⟩ : syracuseStep 3025355 = 4538033) B4538033
theorem B2016903 : Blo 2015435 2016903 := bstep (se 1 (by rfl) ⟨1512677, by rfl⟩ : syracuseStep 2016903 = 3025355) B3025355
theorem B2269021 : Blo 2015435 2269021 := bbase (se 3 (by rfl) ⟨425441, by rfl⟩ : syracuseStep 2269021 = 850883) (by norm_num)
theorem B3025361 : Blo 2015435 3025361 := bstep (se 2 (by rfl) ⟨1134510, by rfl⟩ : syracuseStep 3025361 = 2269021) B2269021
theorem B2016907 : Blo 2015435 2016907 := bstep (se 1 (by rfl) ⟨1512680, by rfl⟩ : syracuseStep 2016907 = 3025361) B3025361
theorem B6807077 : Blo 2015435 6807077 := bbase (se 4 (by rfl) ⟨638163, by rfl⟩ : syracuseStep 6807077 = 1276327) (by norm_num)
theorem B4538051 : Blo 2015435 4538051 := bstep (se 1 (by rfl) ⟨3403538, by rfl⟩ : syracuseStep 4538051 = 6807077) B6807077
theorem B3025367 : Blo 2015435 3025367 := bstep (se 1 (by rfl) ⟨2269025, by rfl⟩ : syracuseStep 3025367 = 4538051) B4538051
theorem B2016911 : Blo 2015435 2016911 := bstep (se 1 (by rfl) ⟨1512683, by rfl⟩ : syracuseStep 2016911 = 3025367) B3025367
theorem B3025373 : Blo 2015435 3025373 := bbase (se 3 (by rfl) ⟨567257, by rfl⟩ : syracuseStep 3025373 = 1134515) (by norm_num)
theorem B2016915 : Blo 2015435 2016915 := bstep (se 1 (by rfl) ⟨1512686, by rfl⟩ : syracuseStep 2016915 = 3025373) B3025373
theorem B4538069 : Blo 2015435 4538069 := bbase (se 7 (by rfl) ⟨53180, by rfl⟩ : syracuseStep 4538069 = 106361) (by norm_num)
theorem B3025379 : Blo 2015435 3025379 := bstep (se 1 (by rfl) ⟨2269034, by rfl⟩ : syracuseStep 3025379 = 4538069) B4538069
theorem B2016919 : Blo 2015435 2016919 := bstep (se 1 (by rfl) ⟨1512689, by rfl⟩ : syracuseStep 2016919 = 3025379) B3025379
theorem B4846085 : Blo 2015435 4846085 := bbase (se 4 (by rfl) ⟨454320, by rfl⟩ : syracuseStep 4846085 = 908641) (by norm_num)
theorem B3230723 : Blo 2015435 3230723 := bstep (se 1 (by rfl) ⟨2423042, by rfl⟩ : syracuseStep 3230723 = 4846085) B4846085
theorem B8615261 : Blo 2015435 8615261 := bstep (se 3 (by rfl) ⟨1615361, by rfl⟩ : syracuseStep 8615261 = 3230723) B3230723
theorem B5743507 : Blo 2015435 5743507 := bstep (se 1 (by rfl) ⟨4307630, by rfl⟩ : syracuseStep 5743507 = 8615261) B8615261
theorem B7658009 : Blo 2015435 7658009 := bstep (se 2 (by rfl) ⟨2871753, by rfl⟩ : syracuseStep 7658009 = 5743507) B5743507
theorem B5105339 : Blo 2015435 5105339 := bstep (se 1 (by rfl) ⟨3829004, by rfl⟩ : syracuseStep 5105339 = 7658009) B7658009
theorem B3403559 : Blo 2015435 3403559 := bstep (se 1 (by rfl) ⟨2552669, by rfl⟩ : syracuseStep 3403559 = 5105339) B5105339
theorem B2269039 : Blo 2015435 2269039 := bstep (se 1 (by rfl) ⟨1701779, by rfl⟩ : syracuseStep 2269039 = 3403559) B3403559
theorem B3025385 : Blo 2015435 3025385 := bstep (se 2 (by rfl) ⟨1134519, by rfl⟩ : syracuseStep 3025385 = 2269039) B2269039
theorem B2016923 : Blo 2015435 2016923 := bstep (se 1 (by rfl) ⟨1512692, by rfl⟩ : syracuseStep 2016923 = 3025385) B3025385
theorem B19384373 : Blo 2015435 19384373 := bbase (se 5 (by rfl) ⟨908642, by rfl⟩ : syracuseStep 19384373 = 1817285) (by norm_num)
theorem B12922915 : Blo 2015435 12922915 := bstep (se 1 (by rfl) ⟨9692186, by rfl⟩ : syracuseStep 12922915 = 19384373) B19384373
theorem B17230553 : Blo 2015435 17230553 := bstep (se 2 (by rfl) ⟨6461457, by rfl⟩ : syracuseStep 17230553 = 12922915) B12922915
theorem B11487035 : Blo 2015435 11487035 := bstep (se 1 (by rfl) ⟨8615276, by rfl⟩ : syracuseStep 11487035 = 17230553) B17230553
theorem B7658023 : Blo 2015435 7658023 := bstep (se 1 (by rfl) ⟨5743517, by rfl⟩ : syracuseStep 7658023 = 11487035) B11487035
theorem B10210697 : Blo 2015435 10210697 := bstep (se 2 (by rfl) ⟨3829011, by rfl⟩ : syracuseStep 10210697 = 7658023) B7658023
theorem B6807131 : Blo 2015435 6807131 := bstep (se 1 (by rfl) ⟨5105348, by rfl⟩ : syracuseStep 6807131 = 10210697) B10210697
theorem B4538087 : Blo 2015435 4538087 := bstep (se 1 (by rfl) ⟨3403565, by rfl⟩ : syracuseStep 4538087 = 6807131) B6807131
theorem B3025391 : Blo 2015435 3025391 := bstep (se 1 (by rfl) ⟨2269043, by rfl⟩ : syracuseStep 3025391 = 4538087) B4538087
theorem B2016927 : Blo 2015435 2016927 := bstep (se 1 (by rfl) ⟨1512695, by rfl⟩ : syracuseStep 2016927 = 3025391) B3025391
theorem B3025397 : Blo 2015435 3025397 := bbase (se 5 (by rfl) ⟨141815, by rfl⟩ : syracuseStep 3025397 = 283631) (by norm_num)
theorem B2016931 : Blo 2015435 2016931 := bstep (se 1 (by rfl) ⟨1512698, by rfl⟩ : syracuseStep 2016931 = 3025397) B3025397
theorem B5743541 : Blo 2015435 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B3829027 : Blo 2015435 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B5105369 : Blo 2015435 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B3403579 : Blo 2015435 3403579 := bstep (se 1 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 3403579 = 5105369) B5105369
theorem B4538105 : Blo 2015435 4538105 := bstep (se 2 (by rfl) ⟨1701789, by rfl⟩ : syracuseStep 4538105 = 3403579) B3403579
theorem B3025403 : Blo 2015435 3025403 := bstep (se 1 (by rfl) ⟨2269052, by rfl⟩ : syracuseStep 3025403 = 4538105) B4538105
theorem B2016935 : Blo 2015435 2016935 := bstep (se 1 (by rfl) ⟨1512701, by rfl⟩ : syracuseStep 2016935 = 3025403) B3025403
theorem B2269057 : Blo 2015435 2269057 := bbase (se 2 (by rfl) ⟨850896, by rfl⟩ : syracuseStep 2269057 = 1701793) (by norm_num)
theorem B3025409 : Blo 2015435 3025409 := bstep (se 2 (by rfl) ⟨1134528, by rfl⟩ : syracuseStep 3025409 = 2269057) B2269057
theorem B2016939 : Blo 2015435 2016939 := bstep (se 1 (by rfl) ⟨1512704, by rfl⟩ : syracuseStep 2016939 = 3025409) B3025409
theorem B5105389 : Blo 2015435 5105389 := bbase (se 3 (by rfl) ⟨957260, by rfl⟩ : syracuseStep 5105389 = 1914521) (by norm_num)
theorem B6807185 : Blo 2015435 6807185 := bstep (se 2 (by rfl) ⟨2552694, by rfl⟩ : syracuseStep 6807185 = 5105389) B5105389
theorem B4538123 : Blo 2015435 4538123 := bstep (se 1 (by rfl) ⟨3403592, by rfl⟩ : syracuseStep 4538123 = 6807185) B6807185
theorem B3025415 : Blo 2015435 3025415 := bstep (se 1 (by rfl) ⟨2269061, by rfl⟩ : syracuseStep 3025415 = 4538123) B4538123
theorem B2016943 : Blo 2015435 2016943 := bstep (se 1 (by rfl) ⟨1512707, by rfl⟩ : syracuseStep 2016943 = 3025415) B3025415
theorem B3025421 : Blo 2015435 3025421 := bbase (se 3 (by rfl) ⟨567266, by rfl⟩ : syracuseStep 3025421 = 1134533) (by norm_num)
theorem B2016947 : Blo 2015435 2016947 := bstep (se 1 (by rfl) ⟨1512710, by rfl⟩ : syracuseStep 2016947 = 3025421) B3025421
theorem B4538141 : Blo 2015435 4538141 := bbase (se 3 (by rfl) ⟨850901, by rfl⟩ : syracuseStep 4538141 = 1701803) (by norm_num)
theorem B3025427 : Blo 2015435 3025427 := bstep (se 1 (by rfl) ⟨2269070, by rfl⟩ : syracuseStep 3025427 = 4538141) B4538141
theorem B2016951 : Blo 2015435 2016951 := bstep (se 1 (by rfl) ⟨1512713, by rfl⟩ : syracuseStep 2016951 = 3025427) B3025427
theorem B3403613 : Blo 2015435 3403613 := bbase (se 3 (by rfl) ⟨638177, by rfl⟩ : syracuseStep 3403613 = 1276355) (by norm_num)
theorem B2269075 : Blo 2015435 2269075 := bstep (se 1 (by rfl) ⟨1701806, by rfl⟩ : syracuseStep 2269075 = 3403613) B3403613
theorem B3025433 : Blo 2015435 3025433 := bstep (se 2 (by rfl) ⟨1134537, by rfl⟩ : syracuseStep 3025433 = 2269075) B2269075
theorem B2016955 : Blo 2015435 2016955 := bstep (se 1 (by rfl) ⟨1512716, by rfl⟩ : syracuseStep 2016955 = 3025433) B3025433
theorem B8615413 : Blo 2015435 8615413 := bbase (se 5 (by rfl) ⟨403847, by rfl⟩ : syracuseStep 8615413 = 807695) (by norm_num)
theorem B11487217 : Blo 2015435 11487217 := bstep (se 2 (by rfl) ⟨4307706, by rfl⟩ : syracuseStep 11487217 = 8615413) B8615413
theorem B15316289 : Blo 2015435 15316289 := bstep (se 2 (by rfl) ⟨5743608, by rfl⟩ : syracuseStep 15316289 = 11487217) B11487217
theorem B10210859 : Blo 2015435 10210859 := bstep (se 1 (by rfl) ⟨7658144, by rfl⟩ : syracuseStep 10210859 = 15316289) B15316289
theorem B6807239 : Blo 2015435 6807239 := bstep (se 1 (by rfl) ⟨5105429, by rfl⟩ : syracuseStep 6807239 = 10210859) B10210859
theorem B4538159 : Blo 2015435 4538159 := bstep (se 1 (by rfl) ⟨3403619, by rfl⟩ : syracuseStep 4538159 = 6807239) B6807239
theorem B3025439 : Blo 2015435 3025439 := bstep (se 1 (by rfl) ⟨2269079, by rfl⟩ : syracuseStep 3025439 = 4538159) B4538159
theorem B2016959 : Blo 2015435 2016959 := bstep (se 1 (by rfl) ⟨1512719, by rfl⟩ : syracuseStep 2016959 = 3025439) B3025439
theorem B3025445 : Blo 2015435 3025445 := bbase (se 4 (by rfl) ⟨283635, by rfl⟩ : syracuseStep 3025445 = 567271) (by norm_num)
theorem B2016963 : Blo 2015435 2016963 := bstep (se 1 (by rfl) ⟨1512722, by rfl⟩ : syracuseStep 2016963 = 3025445) B3025445
theorem B2552725 : Blo 2015435 2552725 := bbase (se 6 (by rfl) ⟨59829, by rfl⟩ : syracuseStep 2552725 = 119659) (by norm_num)
theorem B3403633 : Blo 2015435 3403633 := bstep (se 2 (by rfl) ⟨1276362, by rfl⟩ : syracuseStep 3403633 = 2552725) B2552725
theorem B4538177 : Blo 2015435 4538177 := bstep (se 2 (by rfl) ⟨1701816, by rfl⟩ : syracuseStep 4538177 = 3403633) B3403633
theorem B3025451 : Blo 2015435 3025451 := bstep (se 1 (by rfl) ⟨2269088, by rfl⟩ : syracuseStep 3025451 = 4538177) B4538177
theorem B2016967 : Blo 2015435 2016967 := bstep (se 1 (by rfl) ⟨1512725, by rfl⟩ : syracuseStep 2016967 = 3025451) B3025451
theorem B2269093 : Blo 2015435 2269093 := bbase (se 4 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 2269093 = 425455) (by norm_num)
theorem B3025457 : Blo 2015435 3025457 := bstep (se 2 (by rfl) ⟨1134546, by rfl⟩ : syracuseStep 3025457 = 2269093) B2269093
theorem B2016971 : Blo 2015435 2016971 := bstep (se 1 (by rfl) ⟨1512728, by rfl⟩ : syracuseStep 2016971 = 3025457) B3025457
theorem B2587565 : Blo 2015435 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B6900173 : Blo 2015435 6900173 := bstep (se 3 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 6900173 = 2587565) B2587565
theorem B4600115 : Blo 2015435 4600115 := bstep (se 1 (by rfl) ⟨3450086, by rfl⟩ : syracuseStep 4600115 = 6900173) B6900173
theorem B3066743 : Blo 2015435 3066743 := bstep (se 1 (by rfl) ⟨2300057, by rfl⟩ : syracuseStep 3066743 = 4600115) B4600115
theorem B2044495 : Blo 2015435 2044495 := bstep (se 1 (by rfl) ⟨1533371, by rfl⟩ : syracuseStep 2044495 = 3066743) B3066743
theorem B2725993 : Blo 2015435 2725993 := bstep (se 2 (by rfl) ⟨1022247, by rfl⟩ : syracuseStep 2725993 = 2044495) B2044495
theorem B14538629 : Blo 2015435 14538629 := bstep (se 4 (by rfl) ⟨1362996, by rfl⟩ : syracuseStep 14538629 = 2725993) B2725993
theorem B9692419 : Blo 2015435 9692419 := bstep (se 1 (by rfl) ⟨7269314, by rfl⟩ : syracuseStep 9692419 = 14538629) B14538629
theorem B12923225 : Blo 2015435 12923225 := bstep (se 2 (by rfl) ⟨4846209, by rfl⟩ : syracuseStep 12923225 = 9692419) B9692419
theorem B8615483 : Blo 2015435 8615483 := bstep (se 1 (by rfl) ⟨6461612, by rfl⟩ : syracuseStep 8615483 = 12923225) B12923225
theorem B5743655 : Blo 2015435 5743655 := bstep (se 1 (by rfl) ⟨4307741, by rfl⟩ : syracuseStep 5743655 = 8615483) B8615483
theorem B3829103 : Blo 2015435 3829103 := bstep (se 1 (by rfl) ⟨2871827, by rfl⟩ : syracuseStep 3829103 = 5743655) B5743655
theorem B2552735 : Blo 2015435 2552735 := bstep (se 1 (by rfl) ⟨1914551, by rfl⟩ : syracuseStep 2552735 = 3829103) B3829103
theorem B6807293 : Blo 2015435 6807293 := bstep (se 3 (by rfl) ⟨1276367, by rfl⟩ : syracuseStep 6807293 = 2552735) B2552735
theorem B4538195 : Blo 2015435 4538195 := bstep (se 1 (by rfl) ⟨3403646, by rfl⟩ : syracuseStep 4538195 = 6807293) B6807293
theorem B3025463 : Blo 2015435 3025463 := bstep (se 1 (by rfl) ⟨2269097, by rfl⟩ : syracuseStep 3025463 = 4538195) B4538195
theorem B2016975 : Blo 2015435 2016975 := bstep (se 1 (by rfl) ⟨1512731, by rfl⟩ : syracuseStep 2016975 = 3025463) B3025463
theorem B3025469 : Blo 2015435 3025469 := bbase (se 3 (by rfl) ⟨567275, by rfl⟩ : syracuseStep 3025469 = 1134551) (by norm_num)
theorem B2016979 : Blo 2015435 2016979 := bstep (se 1 (by rfl) ⟨1512734, by rfl⟩ : syracuseStep 2016979 = 3025469) B3025469
theorem B4538213 : Blo 2015435 4538213 := bbase (se 4 (by rfl) ⟨425457, by rfl⟩ : syracuseStep 4538213 = 850915) (by norm_num)
theorem B3025475 : Blo 2015435 3025475 := bstep (se 1 (by rfl) ⟨2269106, by rfl⟩ : syracuseStep 3025475 = 4538213) B4538213
theorem B2016983 : Blo 2015435 2016983 := bstep (se 1 (by rfl) ⟨1512737, by rfl⟩ : syracuseStep 2016983 = 3025475) B3025475
theorem B5105501 : Blo 2015435 5105501 := bbase (se 3 (by rfl) ⟨957281, by rfl⟩ : syracuseStep 5105501 = 1914563) (by norm_num)
theorem B3403667 : Blo 2015435 3403667 := bstep (se 1 (by rfl) ⟨2552750, by rfl⟩ : syracuseStep 3403667 = 5105501) B5105501
theorem B2269111 : Blo 2015435 2269111 := bstep (se 1 (by rfl) ⟨1701833, by rfl⟩ : syracuseStep 2269111 = 3403667) B3403667
theorem B3025481 : Blo 2015435 3025481 := bstep (se 2 (by rfl) ⟨1134555, by rfl⟩ : syracuseStep 3025481 = 2269111) B2269111
theorem B2016987 : Blo 2015435 2016987 := bstep (se 1 (by rfl) ⟨1512740, by rfl⟩ : syracuseStep 2016987 = 3025481) B3025481
theorem B3829133 : Blo 2015435 3829133 := bbase (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) (by norm_num)
theorem B10211021 : Blo 2015435 10211021 := bstep (se 3 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 10211021 = 3829133) B3829133
theorem B6807347 : Blo 2015435 6807347 := bstep (se 1 (by rfl) ⟨5105510, by rfl⟩ : syracuseStep 6807347 = 10211021) B10211021
theorem B4538231 : Blo 2015435 4538231 := bstep (se 1 (by rfl) ⟨3403673, by rfl⟩ : syracuseStep 4538231 = 6807347) B6807347
theorem B3025487 : Blo 2015435 3025487 := bstep (se 1 (by rfl) ⟨2269115, by rfl⟩ : syracuseStep 3025487 = 4538231) B4538231
theorem B2016991 : Blo 2015435 2016991 := bstep (se 1 (by rfl) ⟨1512743, by rfl⟩ : syracuseStep 2016991 = 3025487) B3025487
theorem B3025493 : Blo 2015435 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B2016995 : Blo 2015435 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B11644181 : Blo 2015435 11644181 := bbase (se 6 (by rfl) ⟨272910, by rfl⟩ : syracuseStep 11644181 = 545821) (by norm_num)
theorem B7762787 : Blo 2015435 7762787 := bstep (se 1 (by rfl) ⟨5822090, by rfl⟩ : syracuseStep 7762787 = 11644181) B11644181
theorem B5175191 : Blo 2015435 5175191 := bstep (se 1 (by rfl) ⟨3881393, by rfl⟩ : syracuseStep 5175191 = 7762787) B7762787
theorem B3450127 : Blo 2015435 3450127 := bstep (se 1 (by rfl) ⟨2587595, by rfl⟩ : syracuseStep 3450127 = 5175191) B5175191
theorem B4600169 : Blo 2015435 4600169 := bstep (se 2 (by rfl) ⟨1725063, by rfl⟩ : syracuseStep 4600169 = 3450127) B3450127
theorem B3066779 : Blo 2015435 3066779 := bstep (se 1 (by rfl) ⟨2300084, by rfl⟩ : syracuseStep 3066779 = 4600169) B4600169
theorem B8178077 : Blo 2015435 8178077 := bstep (se 3 (by rfl) ⟨1533389, by rfl⟩ : syracuseStep 8178077 = 3066779) B3066779
theorem B5452051 : Blo 2015435 5452051 := bstep (se 1 (by rfl) ⟨4089038, by rfl⟩ : syracuseStep 5452051 = 8178077) B8178077
theorem B7269401 : Blo 2015435 7269401 := bstep (se 2 (by rfl) ⟨2726025, by rfl⟩ : syracuseStep 7269401 = 5452051) B5452051
theorem B4846267 : Blo 2015435 4846267 := bstep (se 1 (by rfl) ⟨3634700, by rfl⟩ : syracuseStep 4846267 = 7269401) B7269401
theorem B6461689 : Blo 2015435 6461689 := bstep (se 2 (by rfl) ⟨2423133, by rfl⟩ : syracuseStep 6461689 = 4846267) B4846267
theorem B8615585 : Blo 2015435 8615585 := bstep (se 2 (by rfl) ⟨3230844, by rfl⟩ : syracuseStep 8615585 = 6461689) B6461689
theorem B5743723 : Blo 2015435 5743723 := bstep (se 1 (by rfl) ⟨4307792, by rfl⟩ : syracuseStep 5743723 = 8615585) B8615585
theorem B7658297 : Blo 2015435 7658297 := bstep (se 2 (by rfl) ⟨2871861, by rfl⟩ : syracuseStep 7658297 = 5743723) B5743723
theorem B5105531 : Blo 2015435 5105531 := bstep (se 1 (by rfl) ⟨3829148, by rfl⟩ : syracuseStep 5105531 = 7658297) B7658297
theorem B3403687 : Blo 2015435 3403687 := bstep (se 1 (by rfl) ⟨2552765, by rfl⟩ : syracuseStep 3403687 = 5105531) B5105531
theorem B4538249 : Blo 2015435 4538249 := bstep (se 2 (by rfl) ⟨1701843, by rfl⟩ : syracuseStep 4538249 = 3403687) B3403687
theorem B3025499 : Blo 2015435 3025499 := bstep (se 1 (by rfl) ⟨2269124, by rfl⟩ : syracuseStep 3025499 = 4538249) B4538249
theorem B2016999 : Blo 2015435 2016999 := bstep (se 1 (by rfl) ⟨1512749, by rfl⟩ : syracuseStep 2016999 = 3025499) B3025499
theorem B2269129 : Blo 2015435 2269129 := bbase (se 2 (by rfl) ⟨850923, by rfl⟩ : syracuseStep 2269129 = 1701847) (by norm_num)
theorem B3025505 : Blo 2015435 3025505 := bstep (se 2 (by rfl) ⟨1134564, by rfl⟩ : syracuseStep 3025505 = 2269129) B2269129
theorem B2017003 : Blo 2015435 2017003 := bstep (se 1 (by rfl) ⟨1512752, by rfl⟩ : syracuseStep 2017003 = 3025505) B3025505
theorem B24254741 : Blo 2015435 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B16169827 : Blo 2015435 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B21559769 : Blo 2015435 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B14373179 : Blo 2015435 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B9582119 : Blo 2015435 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B6388079 : Blo 2015435 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B17034877 : Blo 2015435 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B22713169 : Blo 2015435 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B30284225 : Blo 2015435 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B20189483 : Blo 2015435 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B13459655 : Blo 2015435 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B35892413 : Blo 2015435 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B23928275 : Blo 2015435 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B15952183 : Blo 2015435 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B85078309 : Blo 2015435 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B113437745 : Blo 2015435 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B75625163 : Blo 2015435 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B50416775 : Blo 2015435 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B33611183 : Blo 2015435 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B22407455 : Blo 2015435 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B59753213 : Blo 2015435 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B39835475 : Blo 2015435 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B26556983 : Blo 2015435 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B17704655 : Blo 2015435 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B11803103 : Blo 2015435 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B7868735 : Blo 2015435 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B5245823 : Blo 2015435 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B3497215 : Blo 2015435 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B4662953 : Blo 2015435 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B3108635 : Blo 2015435 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2072423 : Blo 2015435 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B5526461 : Blo 2015435 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B3684307 : Blo 2015435 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B4912409 : Blo 2015435 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B3274939 : Blo 2015435 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B4366585 : Blo 2015435 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B5822113 : Blo 2015435 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B7762817 : Blo 2015435 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B20700845 : Blo 2015435 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B13800563 : Blo 2015435 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B9200375 : Blo 2015435 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B6133583 : Blo 2015435 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B4089055 : Blo 2015435 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B5452073 : Blo 2015435 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B3634715 : Blo 2015435 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B2423143 : Blo 2015435 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B3230857 : Blo 2015435 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B17231237 : Blo 2015435 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B11487491 : Blo 2015435 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B7658327 : Blo 2015435 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B5105551 : Blo 2015435 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B6807401 : Blo 2015435 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B4538267 : Blo 2015435 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B3025511 : Blo 2015435 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B2017007 : Blo 2015435 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B3025517 : Blo 2015435 3025517 := bbase (se 3 (by rfl) ⟨567284, by rfl⟩ : syracuseStep 3025517 = 1134569) (by norm_num)
theorem B2017011 : Blo 2015435 2017011 := bstep (se 1 (by rfl) ⟨1512758, by rfl⟩ : syracuseStep 2017011 = 3025517) B3025517
theorem B4538285 : Blo 2015435 4538285 := bbase (se 3 (by rfl) ⟨850928, by rfl⟩ : syracuseStep 4538285 = 1701857) (by norm_num)
theorem B3025523 : Blo 2015435 3025523 := bstep (se 1 (by rfl) ⟨2269142, by rfl⟩ : syracuseStep 3025523 = 4538285) B4538285
theorem B2017015 : Blo 2015435 2017015 := bstep (se 1 (by rfl) ⟨1512761, by rfl⟩ : syracuseStep 2017015 = 3025523) B3025523
theorem B5743781 : Blo 2015435 5743781 := bbase (se 4 (by rfl) ⟨538479, by rfl⟩ : syracuseStep 5743781 = 1076959) (by norm_num)
theorem B3829187 : Blo 2015435 3829187 := bstep (se 1 (by rfl) ⟨2871890, by rfl⟩ : syracuseStep 3829187 = 5743781) B5743781
theorem B2552791 : Blo 2015435 2552791 := bstep (se 1 (by rfl) ⟨1914593, by rfl⟩ : syracuseStep 2552791 = 3829187) B3829187
theorem B3403721 : Blo 2015435 3403721 := bstep (se 2 (by rfl) ⟨1276395, by rfl⟩ : syracuseStep 3403721 = 2552791) B2552791
theorem B2269147 : Blo 2015435 2269147 := bstep (se 1 (by rfl) ⟨1701860, by rfl⟩ : syracuseStep 2269147 = 3403721) B3403721
theorem B3025529 : Blo 2015435 3025529 := bstep (se 2 (by rfl) ⟨1134573, by rfl⟩ : syracuseStep 3025529 = 2269147) B2269147
theorem B2017019 : Blo 2015435 2017019 := bstep (se 1 (by rfl) ⟨1512764, by rfl⟩ : syracuseStep 2017019 = 3025529) B3025529
theorem B15525749 : Blo 2015435 15525749 := bbase (se 5 (by rfl) ⟨727769, by rfl⟩ : syracuseStep 15525749 = 1455539) (by norm_num)
theorem B10350499 : Blo 2015435 10350499 := bstep (se 1 (by rfl) ⟨7762874, by rfl⟩ : syracuseStep 10350499 = 15525749) B15525749
theorem B13800665 : Blo 2015435 13800665 := bstep (se 2 (by rfl) ⟨5175249, by rfl⟩ : syracuseStep 13800665 = 10350499) B10350499
theorem B36801773 : Blo 2015435 36801773 := bstep (se 3 (by rfl) ⟨6900332, by rfl⟩ : syracuseStep 36801773 = 13800665) B13800665
theorem B24534515 : Blo 2015435 24534515 := bstep (se 1 (by rfl) ⟨18400886, by rfl⟩ : syracuseStep 24534515 = 36801773) B36801773
theorem B16356343 : Blo 2015435 16356343 := bstep (se 1 (by rfl) ⟨12267257, by rfl⟩ : syracuseStep 16356343 = 24534515) B24534515
theorem B21808457 : Blo 2015435 21808457 := bstep (se 2 (by rfl) ⟨8178171, by rfl⟩ : syracuseStep 21808457 = 16356343) B16356343
theorem B14538971 : Blo 2015435 14538971 := bstep (se 1 (by rfl) ⟨10904228, by rfl⟩ : syracuseStep 14538971 = 21808457) B21808457
theorem B38770589 : Blo 2015435 38770589 := bstep (se 3 (by rfl) ⟨7269485, by rfl⟩ : syracuseStep 38770589 = 14538971) B14538971
theorem B25847059 : Blo 2015435 25847059 := bstep (se 1 (by rfl) ⟨19385294, by rfl⟩ : syracuseStep 25847059 = 38770589) B38770589
theorem B34462745 : Blo 2015435 34462745 := bstep (se 2 (by rfl) ⟨12923529, by rfl⟩ : syracuseStep 34462745 = 25847059) B25847059
theorem B22975163 : Blo 2015435 22975163 := bstep (se 1 (by rfl) ⟨17231372, by rfl⟩ : syracuseStep 22975163 = 34462745) B34462745
theorem B15316775 : Blo 2015435 15316775 := bstep (se 1 (by rfl) ⟨11487581, by rfl⟩ : syracuseStep 15316775 = 22975163) B22975163
theorem B10211183 : Blo 2015435 10211183 := bstep (se 1 (by rfl) ⟨7658387, by rfl⟩ : syracuseStep 10211183 = 15316775) B15316775
theorem B6807455 : Blo 2015435 6807455 := bstep (se 1 (by rfl) ⟨5105591, by rfl⟩ : syracuseStep 6807455 = 10211183) B10211183
theorem B4538303 : Blo 2015435 4538303 := bstep (se 1 (by rfl) ⟨3403727, by rfl⟩ : syracuseStep 4538303 = 6807455) B6807455
theorem B3025535 : Blo 2015435 3025535 := bstep (se 1 (by rfl) ⟨2269151, by rfl⟩ : syracuseStep 3025535 = 4538303) B4538303
theorem B2017023 : Blo 2015435 2017023 := bstep (se 1 (by rfl) ⟨1512767, by rfl⟩ : syracuseStep 2017023 = 3025535) B3025535
theorem B3025541 : Blo 2015435 3025541 := bbase (se 4 (by rfl) ⟨283644, by rfl⟩ : syracuseStep 3025541 = 567289) (by norm_num)
theorem B2017027 : Blo 2015435 2017027 := bstep (se 1 (by rfl) ⟨1512770, by rfl⟩ : syracuseStep 2017027 = 3025541) B3025541
theorem B3403741 : Blo 2015435 3403741 := bbase (se 3 (by rfl) ⟨638201, by rfl⟩ : syracuseStep 3403741 = 1276403) (by norm_num)
theorem B4538321 : Blo 2015435 4538321 := bstep (se 2 (by rfl) ⟨1701870, by rfl⟩ : syracuseStep 4538321 = 3403741) B3403741
theorem B3025547 : Blo 2015435 3025547 := bstep (se 1 (by rfl) ⟨2269160, by rfl⟩ : syracuseStep 3025547 = 4538321) B4538321
theorem B2017031 : Blo 2015435 2017031 := bstep (se 1 (by rfl) ⟨1512773, by rfl⟩ : syracuseStep 2017031 = 3025547) B3025547
theorem B2269165 : Blo 2015435 2269165 := bbase (se 3 (by rfl) ⟨425468, by rfl⟩ : syracuseStep 2269165 = 850937) (by norm_num)
theorem B3025553 : Blo 2015435 3025553 := bstep (se 2 (by rfl) ⟨1134582, by rfl⟩ : syracuseStep 3025553 = 2269165) B2269165
theorem B2017035 : Blo 2015435 2017035 := bstep (se 1 (by rfl) ⟨1512776, by rfl⟩ : syracuseStep 2017035 = 3025553) B3025553
theorem B6807509 : Blo 2015435 6807509 := bbase (se 7 (by rfl) ⟨79775, by rfl⟩ : syracuseStep 6807509 = 159551) (by norm_num)
theorem B4538339 : Blo 2015435 4538339 := bstep (se 1 (by rfl) ⟨3403754, by rfl⟩ : syracuseStep 4538339 = 6807509) B6807509
theorem B3025559 : Blo 2015435 3025559 := bstep (se 1 (by rfl) ⟨2269169, by rfl⟩ : syracuseStep 3025559 = 4538339) B4538339
theorem B2017039 : Blo 2015435 2017039 := bstep (se 1 (by rfl) ⟨1512779, by rfl⟩ : syracuseStep 2017039 = 3025559) B3025559
theorem B3025565 : Blo 2015435 3025565 := bbase (se 3 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 3025565 = 1134587) (by norm_num)
theorem B2017043 : Blo 2015435 2017043 := bstep (se 1 (by rfl) ⟨1512782, by rfl⟩ : syracuseStep 2017043 = 3025565) B3025565
theorem B4538357 : Blo 2015435 4538357 := bbase (se 5 (by rfl) ⟨212735, by rfl⟩ : syracuseStep 4538357 = 425471) (by norm_num)
theorem B3025571 : Blo 2015435 3025571 := bstep (se 1 (by rfl) ⟨2269178, by rfl⟩ : syracuseStep 3025571 = 4538357) B4538357
theorem B2017047 : Blo 2015435 2017047 := bstep (se 1 (by rfl) ⟨1512785, by rfl⟩ : syracuseStep 2017047 = 3025571) B3025571
theorem B4144933 : Blo 2015435 4144933 := bbase (se 4 (by rfl) ⟨388587, by rfl⟩ : syracuseStep 4144933 = 777175) (by norm_num)
theorem B5526577 : Blo 2015435 5526577 := bstep (se 2 (by rfl) ⟨2072466, by rfl⟩ : syracuseStep 5526577 = 4144933) B4144933
theorem B7368769 : Blo 2015435 7368769 := bstep (se 2 (by rfl) ⟨2763288, by rfl⟩ : syracuseStep 7368769 = 5526577) B5526577
theorem B39300101 : Blo 2015435 39300101 := bstep (se 4 (by rfl) ⟨3684384, by rfl⟩ : syracuseStep 39300101 = 7368769) B7368769
theorem B419201077 : Blo 2015435 419201077 := bstep (se 5 (by rfl) ⟨19650050, by rfl⟩ : syracuseStep 419201077 = 39300101) B39300101
theorem B558934769 : Blo 2015435 558934769 := bstep (se 2 (by rfl) ⟨209600538, by rfl⟩ : syracuseStep 558934769 = 419201077) B419201077
theorem B372623179 : Blo 2015435 372623179 := bstep (se 1 (by rfl) ⟨279467384, by rfl⟩ : syracuseStep 372623179 = 558934769) B558934769
theorem B496830905 : Blo 2015435 496830905 := bstep (se 2 (by rfl) ⟨186311589, by rfl⟩ : syracuseStep 496830905 = 372623179) B372623179
theorem B331220603 : Blo 2015435 331220603 := bstep (se 1 (by rfl) ⟨248415452, by rfl⟩ : syracuseStep 331220603 = 496830905) B496830905
theorem B220813735 : Blo 2015435 220813735 := bstep (se 1 (by rfl) ⟨165610301, by rfl⟩ : syracuseStep 220813735 = 331220603) B331220603
theorem B294418313 : Blo 2015435 294418313 := bstep (se 2 (by rfl) ⟨110406867, by rfl⟩ : syracuseStep 294418313 = 220813735) B220813735
theorem B196278875 : Blo 2015435 196278875 := bstep (se 1 (by rfl) ⟨147209156, by rfl⟩ : syracuseStep 196278875 = 294418313) B294418313
theorem B130852583 : Blo 2015435 130852583 := bstep (se 1 (by rfl) ⟨98139437, by rfl⟩ : syracuseStep 130852583 = 196278875) B196278875
theorem B87235055 : Blo 2015435 87235055 := bstep (se 1 (by rfl) ⟨65426291, by rfl⟩ : syracuseStep 87235055 = 130852583) B130852583
theorem B58156703 : Blo 2015435 58156703 := bstep (se 1 (by rfl) ⟨43617527, by rfl⟩ : syracuseStep 58156703 = 87235055) B87235055
theorem B38771135 : Blo 2015435 38771135 := bstep (se 1 (by rfl) ⟨29078351, by rfl⟩ : syracuseStep 38771135 = 58156703) B58156703
theorem B25847423 : Blo 2015435 25847423 := bstep (se 1 (by rfl) ⟨19385567, by rfl⟩ : syracuseStep 25847423 = 38771135) B38771135
theorem B17231615 : Blo 2015435 17231615 := bstep (se 1 (by rfl) ⟨12923711, by rfl⟩ : syracuseStep 17231615 = 25847423) B25847423
theorem B11487743 : Blo 2015435 11487743 := bstep (se 1 (by rfl) ⟨8615807, by rfl⟩ : syracuseStep 11487743 = 17231615) B17231615
theorem B7658495 : Blo 2015435 7658495 := bstep (se 1 (by rfl) ⟨5743871, by rfl⟩ : syracuseStep 7658495 = 11487743) B11487743
theorem B5105663 : Blo 2015435 5105663 := bstep (se 1 (by rfl) ⟨3829247, by rfl⟩ : syracuseStep 5105663 = 7658495) B7658495
theorem B3403775 : Blo 2015435 3403775 := bstep (se 1 (by rfl) ⟨2552831, by rfl⟩ : syracuseStep 3403775 = 5105663) B5105663
theorem B2269183 : Blo 2015435 2269183 := bstep (se 1 (by rfl) ⟨1701887, by rfl⟩ : syracuseStep 2269183 = 3403775) B3403775
theorem B3025577 : Blo 2015435 3025577 := bstep (se 2 (by rfl) ⟨1134591, by rfl⟩ : syracuseStep 3025577 = 2269183) B2269183
theorem B2017051 : Blo 2015435 2017051 := bstep (se 1 (by rfl) ⟨1512788, by rfl⟩ : syracuseStep 2017051 = 3025577) B3025577
theorem B2871941 : Blo 2015435 2871941 := bbase (se 4 (by rfl) ⟨269244, by rfl⟩ : syracuseStep 2871941 = 538489) (by norm_num)
theorem B7658509 : Blo 2015435 7658509 := bstep (se 3 (by rfl) ⟨1435970, by rfl⟩ : syracuseStep 7658509 = 2871941) B2871941
theorem B10211345 : Blo 2015435 10211345 := bstep (se 2 (by rfl) ⟨3829254, by rfl⟩ : syracuseStep 10211345 = 7658509) B7658509
theorem B6807563 : Blo 2015435 6807563 := bstep (se 1 (by rfl) ⟨5105672, by rfl⟩ : syracuseStep 6807563 = 10211345) B10211345
theorem B4538375 : Blo 2015435 4538375 := bstep (se 1 (by rfl) ⟨3403781, by rfl⟩ : syracuseStep 4538375 = 6807563) B6807563
theorem B3025583 : Blo 2015435 3025583 := bstep (se 1 (by rfl) ⟨2269187, by rfl⟩ : syracuseStep 3025583 = 4538375) B4538375
theorem B2017055 : Blo 2015435 2017055 := bstep (se 1 (by rfl) ⟨1512791, by rfl⟩ : syracuseStep 2017055 = 3025583) B3025583
theorem B3025589 : Blo 2015435 3025589 := bbase (se 5 (by rfl) ⟨141824, by rfl⟩ : syracuseStep 3025589 = 283649) (by norm_num)
theorem B2017059 : Blo 2015435 2017059 := bstep (se 1 (by rfl) ⟨1512794, by rfl⟩ : syracuseStep 2017059 = 3025589) B3025589
theorem B5105693 : Blo 2015435 5105693 := bbase (se 3 (by rfl) ⟨957317, by rfl⟩ : syracuseStep 5105693 = 1914635) (by norm_num)
theorem B3403795 : Blo 2015435 3403795 := bstep (se 1 (by rfl) ⟨2552846, by rfl⟩ : syracuseStep 3403795 = 5105693) B5105693
theorem B4538393 : Blo 2015435 4538393 := bstep (se 2 (by rfl) ⟨1701897, by rfl⟩ : syracuseStep 4538393 = 3403795) B3403795
theorem B3025595 : Blo 2015435 3025595 := bstep (se 1 (by rfl) ⟨2269196, by rfl⟩ : syracuseStep 3025595 = 4538393) B4538393
theorem B2017063 : Blo 2015435 2017063 := bstep (se 1 (by rfl) ⟨1512797, by rfl⟩ : syracuseStep 2017063 = 3025595) B3025595
theorem B2269201 : Blo 2015435 2269201 := bbase (se 2 (by rfl) ⟨850950, by rfl⟩ : syracuseStep 2269201 = 1701901) (by norm_num)
theorem B3025601 : Blo 2015435 3025601 := bstep (se 2 (by rfl) ⟨1134600, by rfl⟩ : syracuseStep 3025601 = 2269201) B2269201
theorem B2017067 : Blo 2015435 2017067 := bstep (se 1 (by rfl) ⟨1512800, by rfl⟩ : syracuseStep 2017067 = 3025601) B3025601
theorem B3829285 : Blo 2015435 3829285 := bbase (se 4 (by rfl) ⟨358995, by rfl⟩ : syracuseStep 3829285 = 717991) (by norm_num)
theorem B5105713 : Blo 2015435 5105713 := bstep (se 2 (by rfl) ⟨1914642, by rfl⟩ : syracuseStep 5105713 = 3829285) B3829285
theorem B6807617 : Blo 2015435 6807617 := bstep (se 2 (by rfl) ⟨2552856, by rfl⟩ : syracuseStep 6807617 = 5105713) B5105713
theorem B4538411 : Blo 2015435 4538411 := bstep (se 1 (by rfl) ⟨3403808, by rfl⟩ : syracuseStep 4538411 = 6807617) B6807617
theorem B3025607 : Blo 2015435 3025607 := bstep (se 1 (by rfl) ⟨2269205, by rfl⟩ : syracuseStep 3025607 = 4538411) B4538411
theorem B2017071 : Blo 2015435 2017071 := bstep (se 1 (by rfl) ⟨1512803, by rfl⟩ : syracuseStep 2017071 = 3025607) B3025607
theorem B3025613 : Blo 2015435 3025613 := bbase (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) (by norm_num)
theorem B2017075 : Blo 2015435 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B4538429 : Blo 2015435 4538429 := bbase (se 3 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 4538429 = 1701911) (by norm_num)
theorem B3025619 : Blo 2015435 3025619 := bstep (se 1 (by rfl) ⟨2269214, by rfl⟩ : syracuseStep 3025619 = 4538429) B4538429
theorem B2017079 : Blo 2015435 2017079 := bstep (se 1 (by rfl) ⟨1512809, by rfl⟩ : syracuseStep 2017079 = 3025619) B3025619
theorem B3403829 : Blo 2015435 3403829 := bbase (se 5 (by rfl) ⟨159554, by rfl⟩ : syracuseStep 3403829 = 319109) (by norm_num)
theorem B2269219 : Blo 2015435 2269219 := bstep (se 1 (by rfl) ⟨1701914, by rfl⟩ : syracuseStep 2269219 = 3403829) B3403829
theorem B3025625 : Blo 2015435 3025625 := bstep (se 2 (by rfl) ⟨1134609, by rfl⟩ : syracuseStep 3025625 = 2269219) B2269219
theorem B2017083 : Blo 2015435 2017083 := bstep (se 1 (by rfl) ⟨1512812, by rfl⟩ : syracuseStep 2017083 = 3025625) B3025625
theorem B5743973 : Blo 2015435 5743973 := bbase (se 4 (by rfl) ⟨538497, by rfl⟩ : syracuseStep 5743973 = 1076995) (by norm_num)
theorem B15317261 : Blo 2015435 15317261 := bstep (se 3 (by rfl) ⟨2871986, by rfl⟩ : syracuseStep 15317261 = 5743973) B5743973
theorem B10211507 : Blo 2015435 10211507 := bstep (se 1 (by rfl) ⟨7658630, by rfl⟩ : syracuseStep 10211507 = 15317261) B15317261
theorem B6807671 : Blo 2015435 6807671 := bstep (se 1 (by rfl) ⟨5105753, by rfl⟩ : syracuseStep 6807671 = 10211507) B10211507
theorem B4538447 : Blo 2015435 4538447 := bstep (se 1 (by rfl) ⟨3403835, by rfl⟩ : syracuseStep 4538447 = 6807671) B6807671
theorem B3025631 : Blo 2015435 3025631 := bstep (se 1 (by rfl) ⟨2269223, by rfl⟩ : syracuseStep 3025631 = 4538447) B4538447
theorem B2017087 : Blo 2015435 2017087 := bstep (se 1 (by rfl) ⟨1512815, by rfl⟩ : syracuseStep 2017087 = 3025631) B3025631
theorem B3025637 : Blo 2015435 3025637 := bbase (se 4 (by rfl) ⟨283653, by rfl⟩ : syracuseStep 3025637 = 567307) (by norm_num)
theorem B2017091 : Blo 2015435 2017091 := bstep (se 1 (by rfl) ⟨1512818, by rfl⟩ : syracuseStep 2017091 = 3025637) B3025637
theorem B7269749 : Blo 2015435 7269749 := bbase (se 5 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 7269749 = 681539) (by norm_num)
theorem B4846499 : Blo 2015435 4846499 := bstep (se 1 (by rfl) ⟨3634874, by rfl⟩ : syracuseStep 4846499 = 7269749) B7269749
theorem B3230999 : Blo 2015435 3230999 := bstep (se 1 (by rfl) ⟨2423249, by rfl⟩ : syracuseStep 3230999 = 4846499) B4846499
theorem B2153999 : Blo 2015435 2153999 := bstep (se 1 (by rfl) ⟨1615499, by rfl⟩ : syracuseStep 2153999 = 3230999) B3230999
theorem B5743997 : Blo 2015435 5743997 := bstep (se 3 (by rfl) ⟨1076999, by rfl⟩ : syracuseStep 5743997 = 2153999) B2153999
theorem B3829331 : Blo 2015435 3829331 := bstep (se 1 (by rfl) ⟨2871998, by rfl⟩ : syracuseStep 3829331 = 5743997) B5743997
theorem B2552887 : Blo 2015435 2552887 := bstep (se 1 (by rfl) ⟨1914665, by rfl⟩ : syracuseStep 2552887 = 3829331) B3829331
theorem B3403849 : Blo 2015435 3403849 := bstep (se 2 (by rfl) ⟨1276443, by rfl⟩ : syracuseStep 3403849 = 2552887) B2552887
theorem B4538465 : Blo 2015435 4538465 := bstep (se 2 (by rfl) ⟨1701924, by rfl⟩ : syracuseStep 4538465 = 3403849) B3403849
theorem B3025643 : Blo 2015435 3025643 := bstep (se 1 (by rfl) ⟨2269232, by rfl⟩ : syracuseStep 3025643 = 4538465) B4538465
theorem B2017095 : Blo 2015435 2017095 := bstep (se 1 (by rfl) ⟨1512821, by rfl⟩ : syracuseStep 2017095 = 3025643) B3025643
theorem B2269237 : Blo 2015435 2269237 := bbase (se 5 (by rfl) ⟨106370, by rfl⟩ : syracuseStep 2269237 = 212741) (by norm_num)
theorem B3025649 : Blo 2015435 3025649 := bstep (se 2 (by rfl) ⟨1134618, by rfl⟩ : syracuseStep 3025649 = 2269237) B2269237
theorem B2017099 : Blo 2015435 2017099 := bstep (se 1 (by rfl) ⟨1512824, by rfl⟩ : syracuseStep 2017099 = 3025649) B3025649
theorem B2552897 : Blo 2015435 2552897 := bbase (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) (by norm_num)
theorem B6807725 : Blo 2015435 6807725 := bstep (se 3 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 6807725 = 2552897) B2552897
theorem B4538483 : Blo 2015435 4538483 := bstep (se 1 (by rfl) ⟨3403862, by rfl⟩ : syracuseStep 4538483 = 6807725) B6807725
theorem B3025655 : Blo 2015435 3025655 := bstep (se 1 (by rfl) ⟨2269241, by rfl⟩ : syracuseStep 3025655 = 4538483) B4538483
theorem B2017103 : Blo 2015435 2017103 := bstep (se 1 (by rfl) ⟨1512827, by rfl⟩ : syracuseStep 2017103 = 3025655) B3025655
theorem B3025661 : Blo 2015435 3025661 := bbase (se 3 (by rfl) ⟨567311, by rfl⟩ : syracuseStep 3025661 = 1134623) (by norm_num)
theorem B2017107 : Blo 2015435 2017107 := bstep (se 1 (by rfl) ⟨1512830, by rfl⟩ : syracuseStep 2017107 = 3025661) B3025661
theorem B4538501 : Blo 2015435 4538501 := bbase (se 4 (by rfl) ⟨425484, by rfl⟩ : syracuseStep 4538501 = 850969) (by norm_num)
theorem B3025667 : Blo 2015435 3025667 := bstep (se 1 (by rfl) ⟨2269250, by rfl⟩ : syracuseStep 3025667 = 4538501) B4538501
theorem B2017111 : Blo 2015435 2017111 := bstep (se 1 (by rfl) ⟨1512833, by rfl⟩ : syracuseStep 2017111 = 3025667) B3025667
theorem B2587745 : Blo 2015435 2587745 := bbase (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) (by norm_num)
theorem B6900653 : Blo 2015435 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B4600435 : Blo 2015435 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B6133913 : Blo 2015435 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B4089275 : Blo 2015435 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B2726183 : Blo 2015435 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B7269821 : Blo 2015435 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B4846547 : Blo 2015435 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B3231031 : Blo 2015435 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B4308041 : Blo 2015435 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B2872027 : Blo 2015435 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B3829369 : Blo 2015435 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B5105825 : Blo 2015435 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B3403883 : Blo 2015435 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B2269255 : Blo 2015435 2269255 := bstep (se 1 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 2269255 = 3403883) B3403883
theorem B3025673 : Blo 2015435 3025673 := bstep (se 2 (by rfl) ⟨1134627, by rfl⟩ : syracuseStep 3025673 = 2269255) B2269255
theorem B2017115 : Blo 2015435 2017115 := bstep (se 1 (by rfl) ⟨1512836, by rfl⟩ : syracuseStep 2017115 = 3025673) B3025673
theorem B10211669 : Blo 2015435 10211669 := bbase (se 10 (by rfl) ⟨14958, by rfl⟩ : syracuseStep 10211669 = 29917) (by norm_num)
theorem B6807779 : Blo 2015435 6807779 := bstep (se 1 (by rfl) ⟨5105834, by rfl⟩ : syracuseStep 6807779 = 10211669) B10211669
theorem B4538519 : Blo 2015435 4538519 := bstep (se 1 (by rfl) ⟨3403889, by rfl⟩ : syracuseStep 4538519 = 6807779) B6807779
theorem B3025679 : Blo 2015435 3025679 := bstep (se 1 (by rfl) ⟨2269259, by rfl⟩ : syracuseStep 3025679 = 4538519) B4538519
theorem B2017119 : Blo 2015435 2017119 := bstep (se 1 (by rfl) ⟨1512839, by rfl⟩ : syracuseStep 2017119 = 3025679) B3025679
theorem B3025685 : Blo 2015435 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B2017123 : Blo 2015435 2017123 := bstep (se 1 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 2017123 = 3025685) B3025685
theorem B29079445 : Blo 2015435 29079445 := bbase (se 6 (by rfl) ⟨681549, by rfl⟩ : syracuseStep 29079445 = 1363099) (by norm_num)
theorem B38772593 : Blo 2015435 38772593 := bstep (se 2 (by rfl) ⟨14539722, by rfl⟩ : syracuseStep 38772593 = 29079445) B29079445
theorem B25848395 : Blo 2015435 25848395 := bstep (se 1 (by rfl) ⟨19386296, by rfl⟩ : syracuseStep 25848395 = 38772593) B38772593
theorem B17232263 : Blo 2015435 17232263 := bstep (se 1 (by rfl) ⟨12924197, by rfl⟩ : syracuseStep 17232263 = 25848395) B25848395
theorem B11488175 : Blo 2015435 11488175 := bstep (se 1 (by rfl) ⟨8616131, by rfl⟩ : syracuseStep 11488175 = 17232263) B17232263
theorem B7658783 : Blo 2015435 7658783 := bstep (se 1 (by rfl) ⟨5744087, by rfl⟩ : syracuseStep 7658783 = 11488175) B11488175
theorem B5105855 : Blo 2015435 5105855 := bstep (se 1 (by rfl) ⟨3829391, by rfl⟩ : syracuseStep 5105855 = 7658783) B7658783
theorem B3403903 : Blo 2015435 3403903 := bstep (se 1 (by rfl) ⟨2552927, by rfl⟩ : syracuseStep 3403903 = 5105855) B5105855
theorem B4538537 : Blo 2015435 4538537 := bstep (se 2 (by rfl) ⟨1701951, by rfl⟩ : syracuseStep 4538537 = 3403903) B3403903
theorem B3025691 : Blo 2015435 3025691 := bstep (se 1 (by rfl) ⟨2269268, by rfl⟩ : syracuseStep 3025691 = 4538537) B4538537
theorem B2017127 : Blo 2015435 2017127 := bstep (se 1 (by rfl) ⟨1512845, by rfl⟩ : syracuseStep 2017127 = 3025691) B3025691
theorem B2269273 : Blo 2015435 2269273 := bbase (se 2 (by rfl) ⟨850977, by rfl⟩ : syracuseStep 2269273 = 1701955) (by norm_num)
theorem B3025697 : Blo 2015435 3025697 := bstep (se 2 (by rfl) ⟨1134636, by rfl⟩ : syracuseStep 3025697 = 2269273) B2269273
theorem B2017131 : Blo 2015435 2017131 := bstep (se 1 (by rfl) ⟨1512848, by rfl⟩ : syracuseStep 2017131 = 3025697) B3025697
theorem B2423297 : Blo 2015435 2423297 := bbase (se 2 (by rfl) ⟨908736, by rfl⟩ : syracuseStep 2423297 = 1817473) (by norm_num)
theorem B6462125 : Blo 2015435 6462125 := bstep (se 3 (by rfl) ⟨1211648, by rfl⟩ : syracuseStep 6462125 = 2423297) B2423297
theorem B4308083 : Blo 2015435 4308083 := bstep (se 1 (by rfl) ⟨3231062, by rfl⟩ : syracuseStep 4308083 = 6462125) B6462125
theorem B2872055 : Blo 2015435 2872055 := bstep (se 1 (by rfl) ⟨2154041, by rfl⟩ : syracuseStep 2872055 = 4308083) B4308083
theorem B7658813 : Blo 2015435 7658813 := bstep (se 3 (by rfl) ⟨1436027, by rfl⟩ : syracuseStep 7658813 = 2872055) B2872055
theorem B5105875 : Blo 2015435 5105875 := bstep (se 1 (by rfl) ⟨3829406, by rfl⟩ : syracuseStep 5105875 = 7658813) B7658813
theorem B6807833 : Blo 2015435 6807833 := bstep (se 2 (by rfl) ⟨2552937, by rfl⟩ : syracuseStep 6807833 = 5105875) B5105875
theorem B4538555 : Blo 2015435 4538555 := bstep (se 1 (by rfl) ⟨3403916, by rfl⟩ : syracuseStep 4538555 = 6807833) B6807833
theorem B3025703 : Blo 2015435 3025703 := bstep (se 1 (by rfl) ⟨2269277, by rfl⟩ : syracuseStep 3025703 = 4538555) B4538555
theorem B2017135 : Blo 2015435 2017135 := bstep (se 1 (by rfl) ⟨1512851, by rfl⟩ : syracuseStep 2017135 = 3025703) B3025703
theorem B3025709 : Blo 2015435 3025709 := bbase (se 3 (by rfl) ⟨567320, by rfl⟩ : syracuseStep 3025709 = 1134641) (by norm_num)
theorem B2017139 : Blo 2015435 2017139 := bstep (se 1 (by rfl) ⟨1512854, by rfl⟩ : syracuseStep 2017139 = 3025709) B3025709
theorem B4538573 : Blo 2015435 4538573 := bbase (se 3 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 4538573 = 1701965) (by norm_num)
theorem B3025715 : Blo 2015435 3025715 := bstep (se 1 (by rfl) ⟨2269286, by rfl⟩ : syracuseStep 3025715 = 4538573) B4538573
theorem B2017143 : Blo 2015435 2017143 := bstep (se 1 (by rfl) ⟨1512857, by rfl⟩ : syracuseStep 2017143 = 3025715) B3025715
theorem B2552953 : Blo 2015435 2552953 := bbase (se 2 (by rfl) ⟨957357, by rfl⟩ : syracuseStep 2552953 = 1914715) (by norm_num)
theorem B3403937 : Blo 2015435 3403937 := bstep (se 2 (by rfl) ⟨1276476, by rfl⟩ : syracuseStep 3403937 = 2552953) B2552953
theorem B2269291 : Blo 2015435 2269291 := bstep (se 1 (by rfl) ⟨1701968, by rfl⟩ : syracuseStep 2269291 = 3403937) B3403937
theorem B3025721 : Blo 2015435 3025721 := bstep (se 2 (by rfl) ⟨1134645, by rfl⟩ : syracuseStep 3025721 = 2269291) B2269291
theorem B2017147 : Blo 2015435 2017147 := bstep (se 1 (by rfl) ⟨1512860, by rfl⟩ : syracuseStep 2017147 = 3025721) B3025721
theorem B2300257 : Blo 2015435 2300257 := bbase (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) (by norm_num)
theorem B12268037 : Blo 2015435 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B32714765 : Blo 2015435 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B21809843 : Blo 2015435 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B14539895 : Blo 2015435 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B9693263 : Blo 2015435 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B6462175 : Blo 2015435 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B8616233 : Blo 2015435 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B22976621 : Blo 2015435 22976621 := bstep (se 3 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 22976621 = 8616233) B8616233
theorem B15317747 : Blo 2015435 15317747 := bstep (se 1 (by rfl) ⟨11488310, by rfl⟩ : syracuseStep 15317747 = 22976621) B22976621
theorem B10211831 : Blo 2015435 10211831 := bstep (se 1 (by rfl) ⟨7658873, by rfl⟩ : syracuseStep 10211831 = 15317747) B15317747
theorem B6807887 : Blo 2015435 6807887 := bstep (se 1 (by rfl) ⟨5105915, by rfl⟩ : syracuseStep 6807887 = 10211831) B10211831
theorem B4538591 : Blo 2015435 4538591 := bstep (se 1 (by rfl) ⟨3403943, by rfl⟩ : syracuseStep 4538591 = 6807887) B6807887
theorem B3025727 : Blo 2015435 3025727 := bstep (se 1 (by rfl) ⟨2269295, by rfl⟩ : syracuseStep 3025727 = 4538591) B4538591
theorem B2017151 : Blo 2015435 2017151 := bstep (se 1 (by rfl) ⟨1512863, by rfl⟩ : syracuseStep 2017151 = 3025727) B3025727
theorem B3025733 : Blo 2015435 3025733 := bbase (se 4 (by rfl) ⟨283662, by rfl⟩ : syracuseStep 3025733 = 567325) (by norm_num)
theorem B2017155 : Blo 2015435 2017155 := bstep (se 1 (by rfl) ⟨1512866, by rfl⟩ : syracuseStep 2017155 = 3025733) B3025733
theorem B3403957 : Blo 2015435 3403957 := bbase (se 5 (by rfl) ⟨159560, by rfl⟩ : syracuseStep 3403957 = 319121) (by norm_num)
theorem B4538609 : Blo 2015435 4538609 := bstep (se 2 (by rfl) ⟨1701978, by rfl⟩ : syracuseStep 4538609 = 3403957) B3403957
theorem B3025739 : Blo 2015435 3025739 := bstep (se 1 (by rfl) ⟨2269304, by rfl⟩ : syracuseStep 3025739 = 4538609) B4538609
theorem B2017159 : Blo 2015435 2017159 := bstep (se 1 (by rfl) ⟨1512869, by rfl⟩ : syracuseStep 2017159 = 3025739) B3025739
theorem B2269309 : Blo 2015435 2269309 := bbase (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) (by norm_num)
theorem B3025745 : Blo 2015435 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B2017163 : Blo 2015435 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B6807941 : Blo 2015435 6807941 := bbase (se 4 (by rfl) ⟨638244, by rfl⟩ : syracuseStep 6807941 = 1276489) (by norm_num)
theorem B4538627 : Blo 2015435 4538627 := bstep (se 1 (by rfl) ⟨3403970, by rfl⟩ : syracuseStep 4538627 = 6807941) B6807941
theorem B3025751 : Blo 2015435 3025751 := bstep (se 1 (by rfl) ⟨2269313, by rfl⟩ : syracuseStep 3025751 = 4538627) B4538627
theorem B2017167 : Blo 2015435 2017167 := bstep (se 1 (by rfl) ⟨1512875, by rfl⟩ : syracuseStep 2017167 = 3025751) B3025751
theorem B3025757 : Blo 2015435 3025757 := bbase (se 3 (by rfl) ⟨567329, by rfl⟩ : syracuseStep 3025757 = 1134659) (by norm_num)
theorem B2017171 : Blo 2015435 2017171 := bstep (se 1 (by rfl) ⟨1512878, by rfl⟩ : syracuseStep 2017171 = 3025757) B3025757
theorem B4538645 : Blo 2015435 4538645 := bbase (se 6 (by rfl) ⟨106374, by rfl⟩ : syracuseStep 4538645 = 212749) (by norm_num)
theorem B3025763 : Blo 2015435 3025763 := bstep (se 1 (by rfl) ⟨2269322, by rfl⟩ : syracuseStep 3025763 = 4538645) B4538645
theorem B2017175 : Blo 2015435 2017175 := bstep (se 1 (by rfl) ⟨1512881, by rfl⟩ : syracuseStep 2017175 = 3025763) B3025763
theorem B7658981 : Blo 2015435 7658981 := bbase (se 4 (by rfl) ⟨718029, by rfl⟩ : syracuseStep 7658981 = 1436059) (by norm_num)
theorem B5105987 : Blo 2015435 5105987 := bstep (se 1 (by rfl) ⟨3829490, by rfl⟩ : syracuseStep 5105987 = 7658981) B7658981
theorem B3403991 : Blo 2015435 3403991 := bstep (se 1 (by rfl) ⟨2552993, by rfl⟩ : syracuseStep 3403991 = 5105987) B5105987
theorem B2269327 : Blo 2015435 2269327 := bstep (se 1 (by rfl) ⟨1701995, by rfl⟩ : syracuseStep 2269327 = 3403991) B3403991
theorem B3025769 : Blo 2015435 3025769 := bstep (se 2 (by rfl) ⟨1134663, by rfl⟩ : syracuseStep 3025769 = 2269327) B2269327
theorem B2017179 : Blo 2015435 2017179 := bstep (se 1 (by rfl) ⟨1512884, by rfl⟩ : syracuseStep 2017179 = 3025769) B3025769
theorem B4846709 : Blo 2015435 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B3231139 : Blo 2015435 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B4308185 : Blo 2015435 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B11488493 : Blo 2015435 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B7658995 : Blo 2015435 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B10211993 : Blo 2015435 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B6807995 : Blo 2015435 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B4538663 : Blo 2015435 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B3025775 : Blo 2015435 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B2017183 : Blo 2015435 2017183 := bstep (se 1 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 2017183 = 3025775) B3025775
theorem B3025781 : Blo 2015435 3025781 := bbase (se 5 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 3025781 = 283667) (by norm_num)
theorem B2017187 : Blo 2015435 2017187 := bstep (se 1 (by rfl) ⟨1512890, by rfl⟩ : syracuseStep 2017187 = 3025781) B3025781
theorem B7369285 : Blo 2015435 7369285 := bbase (se 4 (by rfl) ⟨690870, by rfl⟩ : syracuseStep 7369285 = 1381741) (by norm_num)
theorem B9825713 : Blo 2015435 9825713 := bstep (se 2 (by rfl) ⟨3684642, by rfl⟩ : syracuseStep 9825713 = 7369285) B7369285
theorem B6550475 : Blo 2015435 6550475 := bstep (se 1 (by rfl) ⟨4912856, by rfl⟩ : syracuseStep 6550475 = 9825713) B9825713
theorem B69871733 : Blo 2015435 69871733 := bstep (se 5 (by rfl) ⟨3275237, by rfl⟩ : syracuseStep 69871733 = 6550475) B6550475
theorem B46581155 : Blo 2015435 46581155 := bstep (se 1 (by rfl) ⟨34935866, by rfl⟩ : syracuseStep 46581155 = 69871733) B69871733
theorem B31054103 : Blo 2015435 31054103 := bstep (se 1 (by rfl) ⟨23290577, by rfl⟩ : syracuseStep 31054103 = 46581155) B46581155
theorem B20702735 : Blo 2015435 20702735 := bstep (se 1 (by rfl) ⟨15527051, by rfl⟩ : syracuseStep 20702735 = 31054103) B31054103
theorem B13801823 : Blo 2015435 13801823 := bstep (se 1 (by rfl) ⟨10351367, by rfl⟩ : syracuseStep 13801823 = 20702735) B20702735
theorem B9201215 : Blo 2015435 9201215 := bstep (se 1 (by rfl) ⟨6900911, by rfl⟩ : syracuseStep 9201215 = 13801823) B13801823
theorem B6134143 : Blo 2015435 6134143 := bstep (se 1 (by rfl) ⟨4600607, by rfl⟩ : syracuseStep 6134143 = 9201215) B9201215
theorem B8178857 : Blo 2015435 8178857 := bstep (se 2 (by rfl) ⟨3067071, by rfl⟩ : syracuseStep 8178857 = 6134143) B6134143
theorem B5452571 : Blo 2015435 5452571 := bstep (se 1 (by rfl) ⟨4089428, by rfl⟩ : syracuseStep 5452571 = 8178857) B8178857
theorem B3635047 : Blo 2015435 3635047 := bstep (se 1 (by rfl) ⟨2726285, by rfl⟩ : syracuseStep 3635047 = 5452571) B5452571
theorem B4846729 : Blo 2015435 4846729 := bstep (se 2 (by rfl) ⟨1817523, by rfl⟩ : syracuseStep 4846729 = 3635047) B3635047
theorem B6462305 : Blo 2015435 6462305 := bstep (se 2 (by rfl) ⟨2423364, by rfl⟩ : syracuseStep 6462305 = 4846729) B4846729
theorem B4308203 : Blo 2015435 4308203 := bstep (se 1 (by rfl) ⟨3231152, by rfl⟩ : syracuseStep 4308203 = 6462305) B6462305
theorem B2872135 : Blo 2015435 2872135 := bstep (se 1 (by rfl) ⟨2154101, by rfl⟩ : syracuseStep 2872135 = 4308203) B4308203
theorem B3829513 : Blo 2015435 3829513 := bstep (se 2 (by rfl) ⟨1436067, by rfl⟩ : syracuseStep 3829513 = 2872135) B2872135
theorem B5106017 : Blo 2015435 5106017 := bstep (se 2 (by rfl) ⟨1914756, by rfl⟩ : syracuseStep 5106017 = 3829513) B3829513
theorem B3404011 : Blo 2015435 3404011 := bstep (se 1 (by rfl) ⟨2553008, by rfl⟩ : syracuseStep 3404011 = 5106017) B5106017
theorem B4538681 : Blo 2015435 4538681 := bstep (se 2 (by rfl) ⟨1702005, by rfl⟩ : syracuseStep 4538681 = 3404011) B3404011
theorem B3025787 : Blo 2015435 3025787 := bstep (se 1 (by rfl) ⟨2269340, by rfl⟩ : syracuseStep 3025787 = 4538681) B4538681
theorem B2017191 : Blo 2015435 2017191 := bstep (se 1 (by rfl) ⟨1512893, by rfl⟩ : syracuseStep 2017191 = 3025787) B3025787
theorem B2269345 : Blo 2015435 2269345 := bbase (se 2 (by rfl) ⟨851004, by rfl⟩ : syracuseStep 2269345 = 1702009) (by norm_num)
theorem B3025793 : Blo 2015435 3025793 := bstep (se 2 (by rfl) ⟨1134672, by rfl⟩ : syracuseStep 3025793 = 2269345) B2269345
theorem B2017195 : Blo 2015435 2017195 := bstep (se 1 (by rfl) ⟨1512896, by rfl⟩ : syracuseStep 2017195 = 3025793) B3025793
theorem B5106037 : Blo 2015435 5106037 := bbase (se 5 (by rfl) ⟨239345, by rfl⟩ : syracuseStep 5106037 = 478691) (by norm_num)
theorem B6808049 : Blo 2015435 6808049 := bstep (se 2 (by rfl) ⟨2553018, by rfl⟩ : syracuseStep 6808049 = 5106037) B5106037
theorem B4538699 : Blo 2015435 4538699 := bstep (se 1 (by rfl) ⟨3404024, by rfl⟩ : syracuseStep 4538699 = 6808049) B6808049
theorem B3025799 : Blo 2015435 3025799 := bstep (se 1 (by rfl) ⟨2269349, by rfl⟩ : syracuseStep 3025799 = 4538699) B4538699
theorem B2017199 : Blo 2015435 2017199 := bstep (se 1 (by rfl) ⟨1512899, by rfl⟩ : syracuseStep 2017199 = 3025799) B3025799
theorem B3025805 : Blo 2015435 3025805 := bbase (se 3 (by rfl) ⟨567338, by rfl⟩ : syracuseStep 3025805 = 1134677) (by norm_num)
theorem B2017203 : Blo 2015435 2017203 := bstep (se 1 (by rfl) ⟨1512902, by rfl⟩ : syracuseStep 2017203 = 3025805) B3025805
theorem B4538717 : Blo 2015435 4538717 := bbase (se 3 (by rfl) ⟨851009, by rfl⟩ : syracuseStep 4538717 = 1702019) (by norm_num)
theorem B3025811 : Blo 2015435 3025811 := bstep (se 1 (by rfl) ⟨2269358, by rfl⟩ : syracuseStep 3025811 = 4538717) B4538717
theorem B2017207 : Blo 2015435 2017207 := bstep (se 1 (by rfl) ⟨1512905, by rfl⟩ : syracuseStep 2017207 = 3025811) B3025811
theorem B3404045 : Blo 2015435 3404045 := bbase (se 3 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 3404045 = 1276517) (by norm_num)
theorem B2269363 : Blo 2015435 2269363 := bstep (se 1 (by rfl) ⟨1702022, by rfl⟩ : syracuseStep 2269363 = 3404045) B3404045
theorem B3025817 : Blo 2015435 3025817 := bstep (se 2 (by rfl) ⟨1134681, by rfl⟩ : syracuseStep 3025817 = 2269363) B2269363
theorem B2017211 : Blo 2015435 2017211 := bstep (se 1 (by rfl) ⟨1512908, by rfl⟩ : syracuseStep 2017211 = 3025817) B3025817
theorem B17233013 : Blo 2015435 17233013 := bbase (se 5 (by rfl) ⟨807797, by rfl⟩ : syracuseStep 17233013 = 1615595) (by norm_num)
theorem B11488675 : Blo 2015435 11488675 := bstep (se 1 (by rfl) ⟨8616506, by rfl⟩ : syracuseStep 11488675 = 17233013) B17233013
theorem B15318233 : Blo 2015435 15318233 := bstep (se 2 (by rfl) ⟨5744337, by rfl⟩ : syracuseStep 15318233 = 11488675) B11488675
theorem B10212155 : Blo 2015435 10212155 := bstep (se 1 (by rfl) ⟨7659116, by rfl⟩ : syracuseStep 10212155 = 15318233) B15318233
theorem B6808103 : Blo 2015435 6808103 := bstep (se 1 (by rfl) ⟨5106077, by rfl⟩ : syracuseStep 6808103 = 10212155) B10212155
theorem B4538735 : Blo 2015435 4538735 := bstep (se 1 (by rfl) ⟨3404051, by rfl⟩ : syracuseStep 4538735 = 6808103) B6808103
theorem B3025823 : Blo 2015435 3025823 := bstep (se 1 (by rfl) ⟨2269367, by rfl⟩ : syracuseStep 3025823 = 4538735) B4538735
theorem B2017215 : Blo 2015435 2017215 := bstep (se 1 (by rfl) ⟨1512911, by rfl⟩ : syracuseStep 2017215 = 3025823) B3025823
theorem B3025829 : Blo 2015435 3025829 := bbase (se 4 (by rfl) ⟨283671, by rfl⟩ : syracuseStep 3025829 = 567343) (by norm_num)
theorem B2017219 : Blo 2015435 2017219 := bstep (se 1 (by rfl) ⟨1512914, by rfl⟩ : syracuseStep 2017219 = 3025829) B3025829
theorem B2553049 : Blo 2015435 2553049 := bbase (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) (by norm_num)
theorem B3404065 : Blo 2015435 3404065 := bstep (se 2 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 3404065 = 2553049) B2553049
theorem B4538753 : Blo 2015435 4538753 := bstep (se 2 (by rfl) ⟨1702032, by rfl⟩ : syracuseStep 4538753 = 3404065) B3404065
theorem B3025835 : Blo 2015435 3025835 := bstep (se 1 (by rfl) ⟨2269376, by rfl⟩ : syracuseStep 3025835 = 4538753) B4538753
theorem B2017223 : Blo 2015435 2017223 := bstep (se 1 (by rfl) ⟨1512917, by rfl⟩ : syracuseStep 2017223 = 3025835) B3025835
theorem B2269381 : Blo 2015435 2269381 := bbase (se 4 (by rfl) ⟨212754, by rfl⟩ : syracuseStep 2269381 = 425509) (by norm_num)
theorem B3025841 : Blo 2015435 3025841 := bstep (se 2 (by rfl) ⟨1134690, by rfl⟩ : syracuseStep 3025841 = 2269381) B2269381
theorem B2017227 : Blo 2015435 2017227 := bstep (se 1 (by rfl) ⟨1512920, by rfl⟩ : syracuseStep 2017227 = 3025841) B3025841
theorem B3829589 : Blo 2015435 3829589 := bbase (se 9 (by rfl) ⟨11219, by rfl⟩ : syracuseStep 3829589 = 22439) (by norm_num)
theorem B2553059 : Blo 2015435 2553059 := bstep (se 1 (by rfl) ⟨1914794, by rfl⟩ : syracuseStep 2553059 = 3829589) B3829589
theorem B6808157 : Blo 2015435 6808157 := bstep (se 3 (by rfl) ⟨1276529, by rfl⟩ : syracuseStep 6808157 = 2553059) B2553059
theorem B4538771 : Blo 2015435 4538771 := bstep (se 1 (by rfl) ⟨3404078, by rfl⟩ : syracuseStep 4538771 = 6808157) B6808157
theorem B3025847 : Blo 2015435 3025847 := bstep (se 1 (by rfl) ⟨2269385, by rfl⟩ : syracuseStep 3025847 = 4538771) B4538771
theorem B2017231 : Blo 2015435 2017231 := bstep (se 1 (by rfl) ⟨1512923, by rfl⟩ : syracuseStep 2017231 = 3025847) B3025847
theorem B3025853 : Blo 2015435 3025853 := bbase (se 3 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 3025853 = 1134695) (by norm_num)
theorem B2017235 : Blo 2015435 2017235 := bstep (se 1 (by rfl) ⟨1512926, by rfl⟩ : syracuseStep 2017235 = 3025853) B3025853
theorem B4538789 : Blo 2015435 4538789 := bbase (se 4 (by rfl) ⟨425511, by rfl⟩ : syracuseStep 4538789 = 851023) (by norm_num)
theorem B3025859 : Blo 2015435 3025859 := bstep (se 1 (by rfl) ⟨2269394, by rfl⟩ : syracuseStep 3025859 = 4538789) B4538789
theorem B2017239 : Blo 2015435 2017239 := bstep (se 1 (by rfl) ⟨1512929, by rfl⟩ : syracuseStep 2017239 = 3025859) B3025859
theorem B5106149 : Blo 2015435 5106149 := bbase (se 4 (by rfl) ⟨478701, by rfl⟩ : syracuseStep 5106149 = 957403) (by norm_num)
theorem B3404099 : Blo 2015435 3404099 := bstep (se 1 (by rfl) ⟨2553074, by rfl⟩ : syracuseStep 3404099 = 5106149) B5106149
theorem B2269399 : Blo 2015435 2269399 := bstep (se 1 (by rfl) ⟨1702049, by rfl⟩ : syracuseStep 2269399 = 3404099) B3404099
theorem B3025865 : Blo 2015435 3025865 := bstep (se 2 (by rfl) ⟨1134699, by rfl⟩ : syracuseStep 3025865 = 2269399) B2269399
theorem B2017243 : Blo 2015435 2017243 := bstep (se 1 (by rfl) ⟨1512932, by rfl⟩ : syracuseStep 2017243 = 3025865) B3025865
theorem B2154161 : Blo 2015435 2154161 := bbase (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) (by norm_num)
theorem B5744429 : Blo 2015435 5744429 := bstep (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) B2154161
theorem B3829619 : Blo 2015435 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B10212317 : Blo 2015435 10212317 := bstep (se 3 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 10212317 = 3829619) B3829619
theorem B6808211 : Blo 2015435 6808211 := bstep (se 1 (by rfl) ⟨5106158, by rfl⟩ : syracuseStep 6808211 = 10212317) B10212317
theorem B4538807 : Blo 2015435 4538807 := bstep (se 1 (by rfl) ⟨3404105, by rfl⟩ : syracuseStep 4538807 = 6808211) B6808211
theorem B3025871 : Blo 2015435 3025871 := bstep (se 1 (by rfl) ⟨2269403, by rfl⟩ : syracuseStep 3025871 = 4538807) B4538807
theorem B2017247 : Blo 2015435 2017247 := bstep (se 1 (by rfl) ⟨1512935, by rfl⟩ : syracuseStep 2017247 = 3025871) B3025871
theorem B3025877 : Blo 2015435 3025877 := bbase (se 7 (by rfl) ⟨35459, by rfl⟩ : syracuseStep 3025877 = 70919) (by norm_num)
theorem B2017251 : Blo 2015435 2017251 := bstep (se 1 (by rfl) ⟨1512938, by rfl⟩ : syracuseStep 2017251 = 3025877) B3025877
theorem B7659269 : Blo 2015435 7659269 := bbase (se 4 (by rfl) ⟨718056, by rfl⟩ : syracuseStep 7659269 = 1436113) (by norm_num)
theorem B5106179 : Blo 2015435 5106179 := bstep (se 1 (by rfl) ⟨3829634, by rfl⟩ : syracuseStep 5106179 = 7659269) B7659269
theorem B3404119 : Blo 2015435 3404119 := bstep (se 1 (by rfl) ⟨2553089, by rfl⟩ : syracuseStep 3404119 = 5106179) B5106179
theorem B4538825 : Blo 2015435 4538825 := bstep (se 2 (by rfl) ⟨1702059, by rfl⟩ : syracuseStep 4538825 = 3404119) B3404119
theorem B3025883 : Blo 2015435 3025883 := bstep (se 1 (by rfl) ⟨2269412, by rfl⟩ : syracuseStep 3025883 = 4538825) B4538825
theorem B2017255 : Blo 2015435 2017255 := bstep (se 1 (by rfl) ⟨1512941, by rfl⟩ : syracuseStep 2017255 = 3025883) B3025883
theorem B2269417 : Blo 2015435 2269417 := bbase (se 2 (by rfl) ⟨851031, by rfl⟩ : syracuseStep 2269417 = 1702063) (by norm_num)
theorem B3025889 : Blo 2015435 3025889 := bstep (se 2 (by rfl) ⟨1134708, by rfl⟩ : syracuseStep 3025889 = 2269417) B2269417
theorem B2017259 : Blo 2015435 2017259 := bstep (se 1 (by rfl) ⟨1512944, by rfl⟩ : syracuseStep 2017259 = 3025889) B3025889
theorem B11488949 : Blo 2015435 11488949 := bbase (se 5 (by rfl) ⟨538544, by rfl⟩ : syracuseStep 11488949 = 1077089) (by norm_num)
theorem B7659299 : Blo 2015435 7659299 := bstep (se 1 (by rfl) ⟨5744474, by rfl⟩ : syracuseStep 7659299 = 11488949) B11488949
theorem B5106199 : Blo 2015435 5106199 := bstep (se 1 (by rfl) ⟨3829649, by rfl⟩ : syracuseStep 5106199 = 7659299) B7659299
theorem B6808265 : Blo 2015435 6808265 := bstep (se 2 (by rfl) ⟨2553099, by rfl⟩ : syracuseStep 6808265 = 5106199) B5106199
theorem B4538843 : Blo 2015435 4538843 := bstep (se 1 (by rfl) ⟨3404132, by rfl⟩ : syracuseStep 4538843 = 6808265) B6808265
theorem B3025895 : Blo 2015435 3025895 := bstep (se 1 (by rfl) ⟨2269421, by rfl⟩ : syracuseStep 3025895 = 4538843) B4538843
theorem B2017263 : Blo 2015435 2017263 := bstep (se 1 (by rfl) ⟨1512947, by rfl⟩ : syracuseStep 2017263 = 3025895) B3025895
theorem B3025901 : Blo 2015435 3025901 := bbase (se 3 (by rfl) ⟨567356, by rfl⟩ : syracuseStep 3025901 = 1134713) (by norm_num)
theorem B2017267 : Blo 2015435 2017267 := bstep (se 1 (by rfl) ⟨1512950, by rfl⟩ : syracuseStep 2017267 = 3025901) B3025901
theorem B4538861 : Blo 2015435 4538861 := bbase (se 3 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 4538861 = 1702073) (by norm_num)
theorem B3025907 : Blo 2015435 3025907 := bstep (se 1 (by rfl) ⟨2269430, by rfl⟩ : syracuseStep 3025907 = 4538861) B4538861
theorem B2017271 : Blo 2015435 2017271 := bstep (se 1 (by rfl) ⟨1512953, by rfl⟩ : syracuseStep 2017271 = 3025907) B3025907
theorem B2331785 : Blo 2015435 2331785 := bbase (se 2 (by rfl) ⟨874419, by rfl⟩ : syracuseStep 2331785 = 1748839) (by norm_num)
theorem B6218093 : Blo 2015435 6218093 := bstep (se 3 (by rfl) ⟨1165892, by rfl⟩ : syracuseStep 6218093 = 2331785) B2331785
theorem B16581581 : Blo 2015435 16581581 := bstep (se 3 (by rfl) ⟨3109046, by rfl⟩ : syracuseStep 16581581 = 6218093) B6218093
theorem B11054387 : Blo 2015435 11054387 := bstep (se 1 (by rfl) ⟨8290790, by rfl⟩ : syracuseStep 11054387 = 16581581) B16581581
theorem B7369591 : Blo 2015435 7369591 := bstep (se 1 (by rfl) ⟨5527193, by rfl⟩ : syracuseStep 7369591 = 11054387) B11054387
theorem B9826121 : Blo 2015435 9826121 := bstep (se 2 (by rfl) ⟨3684795, by rfl⟩ : syracuseStep 9826121 = 7369591) B7369591
theorem B26202989 : Blo 2015435 26202989 := bstep (se 3 (by rfl) ⟨4913060, by rfl⟩ : syracuseStep 26202989 = 9826121) B9826121
theorem B17468659 : Blo 2015435 17468659 := bstep (se 1 (by rfl) ⟨13101494, by rfl⟩ : syracuseStep 17468659 = 26202989) B26202989
theorem B23291545 : Blo 2015435 23291545 := bstep (se 2 (by rfl) ⟨8734329, by rfl⟩ : syracuseStep 23291545 = 17468659) B17468659
theorem B31055393 : Blo 2015435 31055393 := bstep (se 2 (by rfl) ⟨11645772, by rfl⟩ : syracuseStep 31055393 = 23291545) B23291545
theorem B20703595 : Blo 2015435 20703595 := bstep (se 1 (by rfl) ⟨15527696, by rfl⟩ : syracuseStep 20703595 = 31055393) B31055393
theorem B27604793 : Blo 2015435 27604793 := bstep (se 2 (by rfl) ⟨10351797, by rfl⟩ : syracuseStep 27604793 = 20703595) B20703595
theorem B18403195 : Blo 2015435 18403195 := bstep (se 1 (by rfl) ⟨13802396, by rfl⟩ : syracuseStep 18403195 = 27604793) B27604793
theorem B24537593 : Blo 2015435 24537593 := bstep (se 2 (by rfl) ⟨9201597, by rfl⟩ : syracuseStep 24537593 = 18403195) B18403195
theorem B16358395 : Blo 2015435 16358395 := bstep (se 1 (by rfl) ⟨12268796, by rfl⟩ : syracuseStep 16358395 = 24537593) B24537593
theorem B21811193 : Blo 2015435 21811193 := bstep (se 2 (by rfl) ⟨8179197, by rfl⟩ : syracuseStep 21811193 = 16358395) B16358395
theorem B14540795 : Blo 2015435 14540795 := bstep (se 1 (by rfl) ⟨10905596, by rfl⟩ : syracuseStep 14540795 = 21811193) B21811193
theorem B9693863 : Blo 2015435 9693863 := bstep (se 1 (by rfl) ⟨7270397, by rfl⟩ : syracuseStep 9693863 = 14540795) B14540795
theorem B6462575 : Blo 2015435 6462575 := bstep (se 1 (by rfl) ⟨4846931, by rfl⟩ : syracuseStep 6462575 = 9693863) B9693863
theorem B4308383 : Blo 2015435 4308383 := bstep (se 1 (by rfl) ⟨3231287, by rfl⟩ : syracuseStep 4308383 = 6462575) B6462575
theorem B2872255 : Blo 2015435 2872255 := bstep (se 1 (by rfl) ⟨2154191, by rfl⟩ : syracuseStep 2872255 = 4308383) B4308383
theorem B3829673 : Blo 2015435 3829673 := bstep (se 2 (by rfl) ⟨1436127, by rfl⟩ : syracuseStep 3829673 = 2872255) B2872255
theorem B2553115 : Blo 2015435 2553115 := bstep (se 1 (by rfl) ⟨1914836, by rfl⟩ : syracuseStep 2553115 = 3829673) B3829673
theorem B3404153 : Blo 2015435 3404153 := bstep (se 2 (by rfl) ⟨1276557, by rfl⟩ : syracuseStep 3404153 = 2553115) B2553115
theorem B2269435 : Blo 2015435 2269435 := bstep (se 1 (by rfl) ⟨1702076, by rfl⟩ : syracuseStep 2269435 = 3404153) B3404153
theorem B3025913 : Blo 2015435 3025913 := bstep (se 2 (by rfl) ⟨1134717, by rfl⟩ : syracuseStep 3025913 = 2269435) B2269435
theorem B2017275 : Blo 2015435 2017275 := bstep (se 1 (by rfl) ⟨1512956, by rfl⟩ : syracuseStep 2017275 = 3025913) B3025913
theorem B139749461 : Blo 2015435 139749461 := bbase (se 8 (by rfl) ⟨818844, by rfl⟩ : syracuseStep 139749461 = 1637689) (by norm_num)
theorem B93166307 : Blo 2015435 93166307 := bstep (se 1 (by rfl) ⟨69874730, by rfl⟩ : syracuseStep 93166307 = 139749461) B139749461
theorem B62110871 : Blo 2015435 62110871 := bstep (se 1 (by rfl) ⟨46583153, by rfl⟩ : syracuseStep 62110871 = 93166307) B93166307
theorem B41407247 : Blo 2015435 41407247 := bstep (se 1 (by rfl) ⟨31055435, by rfl⟩ : syracuseStep 41407247 = 62110871) B62110871
theorem B110419325 : Blo 2015435 110419325 := bstep (se 3 (by rfl) ⟨20703623, by rfl⟩ : syracuseStep 110419325 = 41407247) B41407247
theorem B73612883 : Blo 2015435 73612883 := bstep (se 1 (by rfl) ⟨55209662, by rfl⟩ : syracuseStep 73612883 = 110419325) B110419325
theorem B49075255 : Blo 2015435 49075255 := bstep (se 1 (by rfl) ⟨36806441, by rfl⟩ : syracuseStep 49075255 = 73612883) B73612883
theorem B65433673 : Blo 2015435 65433673 := bstep (se 2 (by rfl) ⟨24537627, by rfl⟩ : syracuseStep 65433673 = 49075255) B49075255
theorem B87244897 : Blo 2015435 87244897 := bstep (se 2 (by rfl) ⟨32716836, by rfl⟩ : syracuseStep 87244897 = 65433673) B65433673
theorem B116326529 : Blo 2015435 116326529 := bstep (se 2 (by rfl) ⟨43622448, by rfl⟩ : syracuseStep 116326529 = 87244897) B87244897
theorem B77551019 : Blo 2015435 77551019 := bstep (se 1 (by rfl) ⟨58163264, by rfl⟩ : syracuseStep 77551019 = 116326529) B116326529
theorem B51700679 : Blo 2015435 51700679 := bstep (se 1 (by rfl) ⟨38775509, by rfl⟩ : syracuseStep 51700679 = 77551019) B77551019
theorem B34467119 : Blo 2015435 34467119 := bstep (se 1 (by rfl) ⟨25850339, by rfl⟩ : syracuseStep 34467119 = 51700679) B51700679
theorem B22978079 : Blo 2015435 22978079 := bstep (se 1 (by rfl) ⟨17233559, by rfl⟩ : syracuseStep 22978079 = 34467119) B34467119
theorem B15318719 : Blo 2015435 15318719 := bstep (se 1 (by rfl) ⟨11489039, by rfl⟩ : syracuseStep 15318719 = 22978079) B22978079
theorem B10212479 : Blo 2015435 10212479 := bstep (se 1 (by rfl) ⟨7659359, by rfl⟩ : syracuseStep 10212479 = 15318719) B15318719
theorem B6808319 : Blo 2015435 6808319 := bstep (se 1 (by rfl) ⟨5106239, by rfl⟩ : syracuseStep 6808319 = 10212479) B10212479
theorem B4538879 : Blo 2015435 4538879 := bstep (se 1 (by rfl) ⟨3404159, by rfl⟩ : syracuseStep 4538879 = 6808319) B6808319
theorem B3025919 : Blo 2015435 3025919 := bstep (se 1 (by rfl) ⟨2269439, by rfl⟩ : syracuseStep 3025919 = 4538879) B4538879
theorem B2017279 : Blo 2015435 2017279 := bstep (se 1 (by rfl) ⟨1512959, by rfl⟩ : syracuseStep 2017279 = 3025919) B3025919
theorem B3025925 : Blo 2015435 3025925 := bbase (se 4 (by rfl) ⟨283680, by rfl⟩ : syracuseStep 3025925 = 567361) (by norm_num)
theorem B2017283 : Blo 2015435 2017283 := bstep (se 1 (by rfl) ⟨1512962, by rfl⟩ : syracuseStep 2017283 = 3025925) B3025925
theorem B3404173 : Blo 2015435 3404173 := bbase (se 3 (by rfl) ⟨638282, by rfl⟩ : syracuseStep 3404173 = 1276565) (by norm_num)
theorem B4538897 : Blo 2015435 4538897 := bstep (se 2 (by rfl) ⟨1702086, by rfl⟩ : syracuseStep 4538897 = 3404173) B3404173
theorem B3025931 : Blo 2015435 3025931 := bstep (se 1 (by rfl) ⟨2269448, by rfl⟩ : syracuseStep 3025931 = 4538897) B4538897
theorem B2017287 : Blo 2015435 2017287 := bstep (se 1 (by rfl) ⟨1512965, by rfl⟩ : syracuseStep 2017287 = 3025931) B3025931
theorem B2269453 : Blo 2015435 2269453 := bbase (se 3 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 2269453 = 851045) (by norm_num)
theorem B3025937 : Blo 2015435 3025937 := bstep (se 2 (by rfl) ⟨1134726, by rfl⟩ : syracuseStep 3025937 = 2269453) B2269453
theorem B2017291 : Blo 2015435 2017291 := bstep (se 1 (by rfl) ⟨1512968, by rfl⟩ : syracuseStep 2017291 = 3025937) B3025937
theorem B6808373 : Blo 2015435 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B4538915 : Blo 2015435 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B3025943 : Blo 2015435 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B2017295 : Blo 2015435 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B3025949 : Blo 2015435 3025949 := bbase (se 3 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 3025949 = 1134731) (by norm_num)
theorem B2017299 : Blo 2015435 2017299 := bstep (se 1 (by rfl) ⟨1512974, by rfl⟩ : syracuseStep 2017299 = 3025949) B3025949
theorem B4538933 : Blo 2015435 4538933 := bbase (se 5 (by rfl) ⟨212762, by rfl⟩ : syracuseStep 4538933 = 425525) (by norm_num)
theorem B3025955 : Blo 2015435 3025955 := bstep (se 1 (by rfl) ⟨2269466, by rfl⟩ : syracuseStep 3025955 = 4538933) B4538933
theorem B2017303 : Blo 2015435 2017303 := bstep (se 1 (by rfl) ⟨1512977, by rfl⟩ : syracuseStep 2017303 = 3025955) B3025955
theorem B8616901 : Blo 2015435 8616901 := bbase (se 4 (by rfl) ⟨807834, by rfl⟩ : syracuseStep 8616901 = 1615669) (by norm_num)
theorem B11489201 : Blo 2015435 11489201 := bstep (se 2 (by rfl) ⟨4308450, by rfl⟩ : syracuseStep 11489201 = 8616901) B8616901
theorem B7659467 : Blo 2015435 7659467 := bstep (se 1 (by rfl) ⟨5744600, by rfl⟩ : syracuseStep 7659467 = 11489201) B11489201
theorem B5106311 : Blo 2015435 5106311 := bstep (se 1 (by rfl) ⟨3829733, by rfl⟩ : syracuseStep 5106311 = 7659467) B7659467
theorem B3404207 : Blo 2015435 3404207 := bstep (se 1 (by rfl) ⟨2553155, by rfl⟩ : syracuseStep 3404207 = 5106311) B5106311
theorem B2269471 : Blo 2015435 2269471 := bstep (se 1 (by rfl) ⟨1702103, by rfl⟩ : syracuseStep 2269471 = 3404207) B3404207
theorem B3025961 : Blo 2015435 3025961 := bstep (se 2 (by rfl) ⟨1134735, by rfl⟩ : syracuseStep 3025961 = 2269471) B2269471
theorem B2017307 : Blo 2015435 2017307 := bstep (se 1 (by rfl) ⟨1512980, by rfl⟩ : syracuseStep 2017307 = 3025961) B3025961
theorem B8616917 : Blo 2015435 8616917 := bbase (se 7 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 8616917 = 201959) (by norm_num)
theorem B5744611 : Blo 2015435 5744611 := bstep (se 1 (by rfl) ⟨4308458, by rfl⟩ : syracuseStep 5744611 = 8616917) B8616917
theorem B7659481 : Blo 2015435 7659481 := bstep (se 2 (by rfl) ⟨2872305, by rfl⟩ : syracuseStep 7659481 = 5744611) B5744611
theorem B10212641 : Blo 2015435 10212641 := bstep (se 2 (by rfl) ⟨3829740, by rfl⟩ : syracuseStep 10212641 = 7659481) B7659481
theorem B6808427 : Blo 2015435 6808427 := bstep (se 1 (by rfl) ⟨5106320, by rfl⟩ : syracuseStep 6808427 = 10212641) B10212641
theorem B4538951 : Blo 2015435 4538951 := bstep (se 1 (by rfl) ⟨3404213, by rfl⟩ : syracuseStep 4538951 = 6808427) B6808427
theorem B3025967 : Blo 2015435 3025967 := bstep (se 1 (by rfl) ⟨2269475, by rfl⟩ : syracuseStep 3025967 = 4538951) B4538951
theorem B2017311 : Blo 2015435 2017311 := bstep (se 1 (by rfl) ⟨1512983, by rfl⟩ : syracuseStep 2017311 = 3025967) B3025967
theorem B3025973 : Blo 2015435 3025973 := bbase (se 5 (by rfl) ⟨141842, by rfl⟩ : syracuseStep 3025973 = 283685) (by norm_num)
theorem B2017315 : Blo 2015435 2017315 := bstep (se 1 (by rfl) ⟨1512986, by rfl⟩ : syracuseStep 2017315 = 3025973) B3025973
theorem B5106341 : Blo 2015435 5106341 := bbase (se 4 (by rfl) ⟨478719, by rfl⟩ : syracuseStep 5106341 = 957439) (by norm_num)
theorem B3404227 : Blo 2015435 3404227 := bstep (se 1 (by rfl) ⟨2553170, by rfl⟩ : syracuseStep 3404227 = 5106341) B5106341
theorem B4538969 : Blo 2015435 4538969 := bstep (se 2 (by rfl) ⟨1702113, by rfl⟩ : syracuseStep 4538969 = 3404227) B3404227
theorem B3025979 : Blo 2015435 3025979 := bstep (se 1 (by rfl) ⟨2269484, by rfl⟩ : syracuseStep 3025979 = 4538969) B4538969
theorem B2017319 : Blo 2015435 2017319 := bstep (se 1 (by rfl) ⟨1512989, by rfl⟩ : syracuseStep 2017319 = 3025979) B3025979
theorem B2269489 : Blo 2015435 2269489 := bbase (se 2 (by rfl) ⟨851058, by rfl⟩ : syracuseStep 2269489 = 1702117) (by norm_num)
theorem B3025985 : Blo 2015435 3025985 := bstep (se 2 (by rfl) ⟨1134744, by rfl⟩ : syracuseStep 3025985 = 2269489) B2269489
theorem B2017323 : Blo 2015435 2017323 := bstep (se 1 (by rfl) ⟨1512992, by rfl⟩ : syracuseStep 2017323 = 3025985) B3025985
theorem B4308493 : Blo 2015435 4308493 := bbase (se 3 (by rfl) ⟨807842, by rfl⟩ : syracuseStep 4308493 = 1615685) (by norm_num)
theorem B5744657 : Blo 2015435 5744657 := bstep (se 2 (by rfl) ⟨2154246, by rfl⟩ : syracuseStep 5744657 = 4308493) B4308493
theorem B3829771 : Blo 2015435 3829771 := bstep (se 1 (by rfl) ⟨2872328, by rfl⟩ : syracuseStep 3829771 = 5744657) B5744657
theorem B5106361 : Blo 2015435 5106361 := bstep (se 2 (by rfl) ⟨1914885, by rfl⟩ : syracuseStep 5106361 = 3829771) B3829771
theorem B6808481 : Blo 2015435 6808481 := bstep (se 2 (by rfl) ⟨2553180, by rfl⟩ : syracuseStep 6808481 = 5106361) B5106361
theorem B4538987 : Blo 2015435 4538987 := bstep (se 1 (by rfl) ⟨3404240, by rfl⟩ : syracuseStep 4538987 = 6808481) B6808481
theorem B3025991 : Blo 2015435 3025991 := bstep (se 1 (by rfl) ⟨2269493, by rfl⟩ : syracuseStep 3025991 = 4538987) B4538987
theorem B2017327 : Blo 2015435 2017327 := bstep (se 1 (by rfl) ⟨1512995, by rfl⟩ : syracuseStep 2017327 = 3025991) B3025991
theorem B3025997 : Blo 2015435 3025997 := bbase (se 3 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 3025997 = 1134749) (by norm_num)
theorem B2017331 : Blo 2015435 2017331 := bstep (se 1 (by rfl) ⟨1512998, by rfl⟩ : syracuseStep 2017331 = 3025997) B3025997
theorem B4539005 : Blo 2015435 4539005 := bbase (se 3 (by rfl) ⟨851063, by rfl⟩ : syracuseStep 4539005 = 1702127) (by norm_num)
theorem B3026003 : Blo 2015435 3026003 := bstep (se 1 (by rfl) ⟨2269502, by rfl⟩ : syracuseStep 3026003 = 4539005) B4539005
theorem B2017335 : Blo 2015435 2017335 := bstep (se 1 (by rfl) ⟨1513001, by rfl⟩ : syracuseStep 2017335 = 3026003) B3026003
theorem B3404261 : Blo 2015435 3404261 := bbase (se 4 (by rfl) ⟨319149, by rfl⟩ : syracuseStep 3404261 = 638299) (by norm_num)
theorem B2269507 : Blo 2015435 2269507 := bstep (se 1 (by rfl) ⟨1702130, by rfl⟩ : syracuseStep 2269507 = 3404261) B3404261
theorem B3026009 : Blo 2015435 3026009 := bstep (se 2 (by rfl) ⟨1134753, by rfl⟩ : syracuseStep 3026009 = 2269507) B2269507
theorem B2017339 : Blo 2015435 2017339 := bstep (se 1 (by rfl) ⟨1513004, by rfl⟩ : syracuseStep 2017339 = 3026009) B3026009
theorem B27605717 : Blo 2015435 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B18403811 : Blo 2015435 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B12269207 : Blo 2015435 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B8179471 : Blo 2015435 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B10905961 : Blo 2015435 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B14541281 : Blo 2015435 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B9694187 : Blo 2015435 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B6462791 : Blo 2015435 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B4308527 : Blo 2015435 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B2872351 : Blo 2015435 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B15319205 : Blo 2015435 15319205 := bstep (se 4 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 15319205 = 2872351) B2872351
theorem B10212803 : Blo 2015435 10212803 := bstep (se 1 (by rfl) ⟨7659602, by rfl⟩ : syracuseStep 10212803 = 15319205) B15319205
theorem B6808535 : Blo 2015435 6808535 := bstep (se 1 (by rfl) ⟨5106401, by rfl⟩ : syracuseStep 6808535 = 10212803) B10212803
theorem B4539023 : Blo 2015435 4539023 := bstep (se 1 (by rfl) ⟨3404267, by rfl⟩ : syracuseStep 4539023 = 6808535) B6808535
theorem B3026015 : Blo 2015435 3026015 := bstep (se 1 (by rfl) ⟨2269511, by rfl⟩ : syracuseStep 3026015 = 4539023) B4539023
theorem B2017343 : Blo 2015435 2017343 := bstep (se 1 (by rfl) ⟨1513007, by rfl⟩ : syracuseStep 2017343 = 3026015) B3026015
theorem B3026021 : Blo 2015435 3026021 := bbase (se 4 (by rfl) ⟨283689, by rfl⟩ : syracuseStep 3026021 = 567379) (by norm_num)
theorem B2017347 : Blo 2015435 2017347 := bstep (se 1 (by rfl) ⟨1513010, by rfl⟩ : syracuseStep 2017347 = 3026021) B3026021
theorem B2423557 : Blo 2015435 2423557 := bbase (se 4 (by rfl) ⟨227208, by rfl⟩ : syracuseStep 2423557 = 454417) (by norm_num)
theorem B3231409 : Blo 2015435 3231409 := bstep (se 2 (by rfl) ⟨1211778, by rfl⟩ : syracuseStep 3231409 = 2423557) B2423557
theorem B4308545 : Blo 2015435 4308545 := bstep (se 2 (by rfl) ⟨1615704, by rfl⟩ : syracuseStep 4308545 = 3231409) B3231409
theorem B2872363 : Blo 2015435 2872363 := bstep (se 1 (by rfl) ⟨2154272, by rfl⟩ : syracuseStep 2872363 = 4308545) B4308545
theorem B3829817 : Blo 2015435 3829817 := bstep (se 2 (by rfl) ⟨1436181, by rfl⟩ : syracuseStep 3829817 = 2872363) B2872363
theorem B2553211 : Blo 2015435 2553211 := bstep (se 1 (by rfl) ⟨1914908, by rfl⟩ : syracuseStep 2553211 = 3829817) B3829817
theorem B3404281 : Blo 2015435 3404281 := bstep (se 2 (by rfl) ⟨1276605, by rfl⟩ : syracuseStep 3404281 = 2553211) B2553211
theorem B4539041 : Blo 2015435 4539041 := bstep (se 2 (by rfl) ⟨1702140, by rfl⟩ : syracuseStep 4539041 = 3404281) B3404281
theorem B3026027 : Blo 2015435 3026027 := bstep (se 1 (by rfl) ⟨2269520, by rfl⟩ : syracuseStep 3026027 = 4539041) B4539041
theorem B2017351 : Blo 2015435 2017351 := bstep (se 1 (by rfl) ⟨1513013, by rfl⟩ : syracuseStep 2017351 = 3026027) B3026027
theorem B2269525 : Blo 2015435 2269525 := bbase (se 10 (by rfl) ⟨3324, by rfl⟩ : syracuseStep 2269525 = 6649) (by norm_num)
theorem B3026033 : Blo 2015435 3026033 := bstep (se 2 (by rfl) ⟨1134762, by rfl⟩ : syracuseStep 3026033 = 2269525) B2269525
theorem B2017355 : Blo 2015435 2017355 := bstep (se 1 (by rfl) ⟨1513016, by rfl⟩ : syracuseStep 2017355 = 3026033) B3026033
theorem B2553221 : Blo 2015435 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B6808589 : Blo 2015435 6808589 := bstep (se 3 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 6808589 = 2553221) B2553221
theorem B4539059 : Blo 2015435 4539059 := bstep (se 1 (by rfl) ⟨3404294, by rfl⟩ : syracuseStep 4539059 = 6808589) B6808589
theorem B3026039 : Blo 2015435 3026039 := bstep (se 1 (by rfl) ⟨2269529, by rfl⟩ : syracuseStep 3026039 = 4539059) B4539059
theorem B2017359 : Blo 2015435 2017359 := bstep (se 1 (by rfl) ⟨1513019, by rfl⟩ : syracuseStep 2017359 = 3026039) B3026039
theorem B3026045 : Blo 2015435 3026045 := bbase (se 3 (by rfl) ⟨567383, by rfl⟩ : syracuseStep 3026045 = 1134767) (by norm_num)
theorem B2017363 : Blo 2015435 2017363 := bstep (se 1 (by rfl) ⟨1513022, by rfl⟩ : syracuseStep 2017363 = 3026045) B3026045
theorem B4539077 : Blo 2015435 4539077 := bbase (se 4 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 4539077 = 851077) (by norm_num)
theorem B3026051 : Blo 2015435 3026051 := bstep (se 1 (by rfl) ⟨2269538, by rfl⟩ : syracuseStep 3026051 = 4539077) B4539077
theorem B2017367 : Blo 2015435 2017367 := bstep (se 1 (by rfl) ⟨1513025, by rfl⟩ : syracuseStep 2017367 = 3026051) B3026051
theorem B2300509 : Blo 2015435 2300509 := bbase (se 3 (by rfl) ⟨431345, by rfl⟩ : syracuseStep 2300509 = 862691) (by norm_num)
theorem B3067345 : Blo 2015435 3067345 := bstep (se 2 (by rfl) ⟨1150254, by rfl⟩ : syracuseStep 3067345 = 2300509) B2300509
theorem B4089793 : Blo 2015435 4089793 := bstep (se 2 (by rfl) ⟨1533672, by rfl⟩ : syracuseStep 4089793 = 3067345) B3067345
theorem B5453057 : Blo 2015435 5453057 := bstep (se 2 (by rfl) ⟨2044896, by rfl⟩ : syracuseStep 5453057 = 4089793) B4089793
theorem B3635371 : Blo 2015435 3635371 := bstep (se 1 (by rfl) ⟨2726528, by rfl⟩ : syracuseStep 3635371 = 5453057) B5453057
theorem B19388645 : Blo 2015435 19388645 := bstep (se 4 (by rfl) ⟨1817685, by rfl⟩ : syracuseStep 19388645 = 3635371) B3635371
theorem B12925763 : Blo 2015435 12925763 := bstep (se 1 (by rfl) ⟨9694322, by rfl⟩ : syracuseStep 12925763 = 19388645) B19388645
theorem B8617175 : Blo 2015435 8617175 := bstep (se 1 (by rfl) ⟨6462881, by rfl⟩ : syracuseStep 8617175 = 12925763) B12925763
theorem B5744783 : Blo 2015435 5744783 := bstep (se 1 (by rfl) ⟨4308587, by rfl⟩ : syracuseStep 5744783 = 8617175) B8617175
theorem B3829855 : Blo 2015435 3829855 := bstep (se 1 (by rfl) ⟨2872391, by rfl⟩ : syracuseStep 3829855 = 5744783) B5744783
theorem B5106473 : Blo 2015435 5106473 := bstep (se 2 (by rfl) ⟨1914927, by rfl⟩ : syracuseStep 5106473 = 3829855) B3829855
theorem B3404315 : Blo 2015435 3404315 := bstep (se 1 (by rfl) ⟨2553236, by rfl⟩ : syracuseStep 3404315 = 5106473) B5106473
theorem B2269543 : Blo 2015435 2269543 := bstep (se 1 (by rfl) ⟨1702157, by rfl⟩ : syracuseStep 2269543 = 3404315) B3404315
theorem B3026057 : Blo 2015435 3026057 := bstep (se 2 (by rfl) ⟨1134771, by rfl⟩ : syracuseStep 3026057 = 2269543) B2269543
theorem B2017371 : Blo 2015435 2017371 := bstep (se 1 (by rfl) ⟨1513028, by rfl⟩ : syracuseStep 2017371 = 3026057) B3026057
theorem B10212965 : Blo 2015435 10212965 := bbase (se 4 (by rfl) ⟨957465, by rfl⟩ : syracuseStep 10212965 = 1914931) (by norm_num)
theorem B6808643 : Blo 2015435 6808643 := bstep (se 1 (by rfl) ⟨5106482, by rfl⟩ : syracuseStep 6808643 = 10212965) B10212965
theorem B4539095 : Blo 2015435 4539095 := bstep (se 1 (by rfl) ⟨3404321, by rfl⟩ : syracuseStep 4539095 = 6808643) B6808643
theorem B3026063 : Blo 2015435 3026063 := bstep (se 1 (by rfl) ⟨2269547, by rfl⟩ : syracuseStep 3026063 = 4539095) B4539095
theorem B2017375 : Blo 2015435 2017375 := bstep (se 1 (by rfl) ⟨1513031, by rfl⟩ : syracuseStep 2017375 = 3026063) B3026063
theorem B3026069 : Blo 2015435 3026069 := bbase (se 6 (by rfl) ⟨70923, by rfl⟩ : syracuseStep 3026069 = 141847) (by norm_num)
theorem B2017379 : Blo 2015435 2017379 := bstep (se 1 (by rfl) ⟨1513034, by rfl⟩ : syracuseStep 2017379 = 3026069) B3026069
theorem B6134725 : Blo 2015435 6134725 := bbase (se 4 (by rfl) ⟨575130, by rfl⟩ : syracuseStep 6134725 = 1150261) (by norm_num)
theorem B8179633 : Blo 2015435 8179633 := bstep (se 2 (by rfl) ⟨3067362, by rfl⟩ : syracuseStep 8179633 = 6134725) B6134725
theorem B10906177 : Blo 2015435 10906177 := bstep (se 2 (by rfl) ⟨4089816, by rfl⟩ : syracuseStep 10906177 = 8179633) B8179633
theorem B14541569 : Blo 2015435 14541569 := bstep (se 2 (by rfl) ⟨5453088, by rfl⟩ : syracuseStep 14541569 = 10906177) B10906177
theorem B9694379 : Blo 2015435 9694379 := bstep (se 1 (by rfl) ⟨7270784, by rfl⟩ : syracuseStep 9694379 = 14541569) B14541569
theorem B6462919 : Blo 2015435 6462919 := bstep (se 1 (by rfl) ⟨4847189, by rfl⟩ : syracuseStep 6462919 = 9694379) B9694379
theorem B8617225 : Blo 2015435 8617225 := bstep (se 2 (by rfl) ⟨3231459, by rfl⟩ : syracuseStep 8617225 = 6462919) B6462919
theorem B11489633 : Blo 2015435 11489633 := bstep (se 2 (by rfl) ⟨4308612, by rfl⟩ : syracuseStep 11489633 = 8617225) B8617225
theorem B7659755 : Blo 2015435 7659755 := bstep (se 1 (by rfl) ⟨5744816, by rfl⟩ : syracuseStep 7659755 = 11489633) B11489633
theorem B5106503 : Blo 2015435 5106503 := bstep (se 1 (by rfl) ⟨3829877, by rfl⟩ : syracuseStep 5106503 = 7659755) B7659755
theorem B3404335 : Blo 2015435 3404335 := bstep (se 1 (by rfl) ⟨2553251, by rfl⟩ : syracuseStep 3404335 = 5106503) B5106503
theorem B4539113 : Blo 2015435 4539113 := bstep (se 2 (by rfl) ⟨1702167, by rfl⟩ : syracuseStep 4539113 = 3404335) B3404335
theorem B3026075 : Blo 2015435 3026075 := bstep (se 1 (by rfl) ⟨2269556, by rfl⟩ : syracuseStep 3026075 = 4539113) B4539113
theorem B2017383 : Blo 2015435 2017383 := bstep (se 1 (by rfl) ⟨1513037, by rfl⟩ : syracuseStep 2017383 = 3026075) B3026075
theorem B2269561 : Blo 2015435 2269561 := bbase (se 2 (by rfl) ⟨851085, by rfl⟩ : syracuseStep 2269561 = 1702171) (by norm_num)
theorem B3026081 : Blo 2015435 3026081 := bstep (se 2 (by rfl) ⟨1134780, by rfl⟩ : syracuseStep 3026081 = 2269561) B2269561
theorem B2017387 : Blo 2015435 2017387 := bstep (se 1 (by rfl) ⟨1513040, by rfl⟩ : syracuseStep 2017387 = 3026081) B3026081
theorem B2623409 : Blo 2015435 2623409 := bbase (se 2 (by rfl) ⟨983778, by rfl⟩ : syracuseStep 2623409 = 1967557) (by norm_num)
theorem B111932117 : Blo 2015435 111932117 := bstep (se 7 (by rfl) ⟨1311704, by rfl⟩ : syracuseStep 111932117 = 2623409) B2623409
theorem B74621411 : Blo 2015435 74621411 := bstep (se 1 (by rfl) ⟨55966058, by rfl⟩ : syracuseStep 74621411 = 111932117) B111932117
theorem B49747607 : Blo 2015435 49747607 := bstep (se 1 (by rfl) ⟨37310705, by rfl⟩ : syracuseStep 49747607 = 74621411) B74621411
theorem B33165071 : Blo 2015435 33165071 := bstep (se 1 (by rfl) ⟨24873803, by rfl⟩ : syracuseStep 33165071 = 49747607) B49747607
theorem B22110047 : Blo 2015435 22110047 := bstep (se 1 (by rfl) ⟨16582535, by rfl⟩ : syracuseStep 22110047 = 33165071) B33165071
theorem B14740031 : Blo 2015435 14740031 := bstep (se 1 (by rfl) ⟨11055023, by rfl⟩ : syracuseStep 14740031 = 22110047) B22110047
theorem B9826687 : Blo 2015435 9826687 := bstep (se 1 (by rfl) ⟨7370015, by rfl⟩ : syracuseStep 9826687 = 14740031) B14740031
theorem B13102249 : Blo 2015435 13102249 := bstep (se 2 (by rfl) ⟨4913343, by rfl⟩ : syracuseStep 13102249 = 9826687) B9826687
theorem B17469665 : Blo 2015435 17469665 := bstep (se 2 (by rfl) ⟨6551124, by rfl⟩ : syracuseStep 17469665 = 13102249) B13102249
theorem B11646443 : Blo 2015435 11646443 := bstep (se 1 (by rfl) ⟨8734832, by rfl⟩ : syracuseStep 11646443 = 17469665) B17469665
theorem B7764295 : Blo 2015435 7764295 := bstep (se 1 (by rfl) ⟨5823221, by rfl⟩ : syracuseStep 7764295 = 11646443) B11646443
theorem B10352393 : Blo 2015435 10352393 := bstep (se 2 (by rfl) ⟨3882147, by rfl⟩ : syracuseStep 10352393 = 7764295) B7764295
theorem B6901595 : Blo 2015435 6901595 := bstep (se 1 (by rfl) ⟨5176196, by rfl⟩ : syracuseStep 6901595 = 10352393) B10352393
theorem B4601063 : Blo 2015435 4601063 := bstep (se 1 (by rfl) ⟨3450797, by rfl⟩ : syracuseStep 4601063 = 6901595) B6901595
theorem B3067375 : Blo 2015435 3067375 := bstep (se 1 (by rfl) ⟨2300531, by rfl⟩ : syracuseStep 3067375 = 4601063) B4601063
theorem B4089833 : Blo 2015435 4089833 := bstep (se 2 (by rfl) ⟨1533687, by rfl⟩ : syracuseStep 4089833 = 3067375) B3067375
theorem B2726555 : Blo 2015435 2726555 := bstep (se 1 (by rfl) ⟨2044916, by rfl⟩ : syracuseStep 2726555 = 4089833) B4089833
theorem B7270813 : Blo 2015435 7270813 := bstep (se 3 (by rfl) ⟨1363277, by rfl⟩ : syracuseStep 7270813 = 2726555) B2726555
theorem B9694417 : Blo 2015435 9694417 := bstep (se 2 (by rfl) ⟨3635406, by rfl⟩ : syracuseStep 9694417 = 7270813) B7270813
theorem B12925889 : Blo 2015435 12925889 := bstep (se 2 (by rfl) ⟨4847208, by rfl⟩ : syracuseStep 12925889 = 9694417) B9694417
theorem B8617259 : Blo 2015435 8617259 := bstep (se 1 (by rfl) ⟨6462944, by rfl⟩ : syracuseStep 8617259 = 12925889) B12925889
theorem B5744839 : Blo 2015435 5744839 := bstep (se 1 (by rfl) ⟨4308629, by rfl⟩ : syracuseStep 5744839 = 8617259) B8617259
theorem B7659785 : Blo 2015435 7659785 := bstep (se 2 (by rfl) ⟨2872419, by rfl⟩ : syracuseStep 7659785 = 5744839) B5744839
theorem B5106523 : Blo 2015435 5106523 := bstep (se 1 (by rfl) ⟨3829892, by rfl⟩ : syracuseStep 5106523 = 7659785) B7659785
theorem B6808697 : Blo 2015435 6808697 := bstep (se 2 (by rfl) ⟨2553261, by rfl⟩ : syracuseStep 6808697 = 5106523) B5106523
theorem B4539131 : Blo 2015435 4539131 := bstep (se 1 (by rfl) ⟨3404348, by rfl⟩ : syracuseStep 4539131 = 6808697) B6808697
theorem B3026087 : Blo 2015435 3026087 := bstep (se 1 (by rfl) ⟨2269565, by rfl⟩ : syracuseStep 3026087 = 4539131) B4539131
theorem B2017391 : Blo 2015435 2017391 := bstep (se 1 (by rfl) ⟨1513043, by rfl⟩ : syracuseStep 2017391 = 3026087) B3026087
theorem B3026093 : Blo 2015435 3026093 := bbase (se 3 (by rfl) ⟨567392, by rfl⟩ : syracuseStep 3026093 = 1134785) (by norm_num)
theorem B2017395 : Blo 2015435 2017395 := bstep (se 1 (by rfl) ⟨1513046, by rfl⟩ : syracuseStep 2017395 = 3026093) B3026093
theorem B4539149 : Blo 2015435 4539149 := bbase (se 3 (by rfl) ⟨851090, by rfl⟩ : syracuseStep 4539149 = 1702181) (by norm_num)
theorem B3026099 : Blo 2015435 3026099 := bstep (se 1 (by rfl) ⟨2269574, by rfl⟩ : syracuseStep 3026099 = 4539149) B4539149
theorem B2017399 : Blo 2015435 2017399 := bstep (se 1 (by rfl) ⟨1513049, by rfl⟩ : syracuseStep 2017399 = 3026099) B3026099
theorem B2553277 : Blo 2015435 2553277 := bbase (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) (by norm_num)
theorem B3404369 : Blo 2015435 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B2269579 : Blo 2015435 2269579 := bstep (se 1 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 2269579 = 3404369) B3404369
theorem B3026105 : Blo 2015435 3026105 := bstep (se 2 (by rfl) ⟨1134789, by rfl⟩ : syracuseStep 3026105 = 2269579) B2269579
theorem B2017403 : Blo 2015435 2017403 := bstep (se 1 (by rfl) ⟨1513052, by rfl⟩ : syracuseStep 2017403 = 3026105) B3026105
theorem B5176237 : Blo 2015435 5176237 := bbase (se 3 (by rfl) ⟨970544, by rfl⟩ : syracuseStep 5176237 = 1941089) (by norm_num)
theorem B6901649 : Blo 2015435 6901649 := bstep (se 2 (by rfl) ⟨2588118, by rfl⟩ : syracuseStep 6901649 = 5176237) B5176237
theorem B4601099 : Blo 2015435 4601099 := bstep (se 1 (by rfl) ⟨3450824, by rfl⟩ : syracuseStep 4601099 = 6901649) B6901649
theorem B3067399 : Blo 2015435 3067399 := bstep (se 1 (by rfl) ⟨2300549, by rfl⟩ : syracuseStep 3067399 = 4601099) B4601099
theorem B4089865 : Blo 2015435 4089865 := bstep (se 2 (by rfl) ⟨1533699, by rfl⟩ : syracuseStep 4089865 = 3067399) B3067399
theorem B5453153 : Blo 2015435 5453153 := bstep (se 2 (by rfl) ⟨2044932, by rfl⟩ : syracuseStep 5453153 = 4089865) B4089865
theorem B3635435 : Blo 2015435 3635435 := bstep (se 1 (by rfl) ⟨2726576, by rfl⟩ : syracuseStep 3635435 = 5453153) B5453153
theorem B9694493 : Blo 2015435 9694493 := bstep (se 3 (by rfl) ⟨1817717, by rfl⟩ : syracuseStep 9694493 = 3635435) B3635435
theorem B6462995 : Blo 2015435 6462995 := bstep (se 1 (by rfl) ⟨4847246, by rfl⟩ : syracuseStep 6462995 = 9694493) B9694493
theorem B17234653 : Blo 2015435 17234653 := bstep (se 3 (by rfl) ⟨3231497, by rfl⟩ : syracuseStep 17234653 = 6462995) B6462995
theorem B22979537 : Blo 2015435 22979537 := bstep (se 2 (by rfl) ⟨8617326, by rfl⟩ : syracuseStep 22979537 = 17234653) B17234653
theorem B15319691 : Blo 2015435 15319691 := bstep (se 1 (by rfl) ⟨11489768, by rfl⟩ : syracuseStep 15319691 = 22979537) B22979537
theorem B10213127 : Blo 2015435 10213127 := bstep (se 1 (by rfl) ⟨7659845, by rfl⟩ : syracuseStep 10213127 = 15319691) B15319691
theorem B6808751 : Blo 2015435 6808751 := bstep (se 1 (by rfl) ⟨5106563, by rfl⟩ : syracuseStep 6808751 = 10213127) B10213127
theorem B4539167 : Blo 2015435 4539167 := bstep (se 1 (by rfl) ⟨3404375, by rfl⟩ : syracuseStep 4539167 = 6808751) B6808751
theorem B3026111 : Blo 2015435 3026111 := bstep (se 1 (by rfl) ⟨2269583, by rfl⟩ : syracuseStep 3026111 = 4539167) B4539167
theorem B2017407 : Blo 2015435 2017407 := bstep (se 1 (by rfl) ⟨1513055, by rfl⟩ : syracuseStep 2017407 = 3026111) B3026111
theorem B3026117 : Blo 2015435 3026117 := bbase (se 4 (by rfl) ⟨283698, by rfl⟩ : syracuseStep 3026117 = 567397) (by norm_num)
theorem B2017411 : Blo 2015435 2017411 := bstep (se 1 (by rfl) ⟨1513058, by rfl⟩ : syracuseStep 2017411 = 3026117) B3026117
theorem B3404389 : Blo 2015435 3404389 := bbase (se 4 (by rfl) ⟨319161, by rfl⟩ : syracuseStep 3404389 = 638323) (by norm_num)
theorem B4539185 : Blo 2015435 4539185 := bstep (se 2 (by rfl) ⟨1702194, by rfl⟩ : syracuseStep 4539185 = 3404389) B3404389
theorem B3026123 : Blo 2015435 3026123 := bstep (se 1 (by rfl) ⟨2269592, by rfl⟩ : syracuseStep 3026123 = 4539185) B4539185
theorem B2017415 : Blo 2015435 2017415 := bstep (se 1 (by rfl) ⟨1513061, by rfl⟩ : syracuseStep 2017415 = 3026123) B3026123
theorem B2269597 : Blo 2015435 2269597 := bbase (se 3 (by rfl) ⟨425549, by rfl⟩ : syracuseStep 2269597 = 851099) (by norm_num)
theorem B3026129 : Blo 2015435 3026129 := bstep (se 2 (by rfl) ⟨1134798, by rfl⟩ : syracuseStep 3026129 = 2269597) B2269597
theorem B2017419 : Blo 2015435 2017419 := bstep (se 1 (by rfl) ⟨1513064, by rfl⟩ : syracuseStep 2017419 = 3026129) B3026129
theorem B6808805 : Blo 2015435 6808805 := bbase (se 4 (by rfl) ⟨638325, by rfl⟩ : syracuseStep 6808805 = 1276651) (by norm_num)
theorem B4539203 : Blo 2015435 4539203 := bstep (se 1 (by rfl) ⟨3404402, by rfl⟩ : syracuseStep 4539203 = 6808805) B6808805
theorem B3026135 : Blo 2015435 3026135 := bstep (se 1 (by rfl) ⟨2269601, by rfl⟩ : syracuseStep 3026135 = 4539203) B4539203
theorem B2017423 : Blo 2015435 2017423 := bstep (se 1 (by rfl) ⟨1513067, by rfl⟩ : syracuseStep 2017423 = 3026135) B3026135
theorem B3026141 : Blo 2015435 3026141 := bbase (se 3 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 3026141 = 1134803) (by norm_num)
theorem B2017427 : Blo 2015435 2017427 := bstep (se 1 (by rfl) ⟨1513070, by rfl⟩ : syracuseStep 2017427 = 3026141) B3026141
theorem B4539221 : Blo 2015435 4539221 := bbase (se 9 (by rfl) ⟨13298, by rfl⟩ : syracuseStep 4539221 = 26597) (by norm_num)
theorem B3026147 : Blo 2015435 3026147 := bstep (se 1 (by rfl) ⟨2269610, by rfl⟩ : syracuseStep 3026147 = 4539221) B4539221
theorem B2017431 : Blo 2015435 2017431 := bstep (se 1 (by rfl) ⟨1513073, by rfl⟩ : syracuseStep 2017431 = 3026147) B3026147
theorem B5744965 : Blo 2015435 5744965 := bbase (se 4 (by rfl) ⟨538590, by rfl⟩ : syracuseStep 5744965 = 1077181) (by norm_num)
theorem B7659953 : Blo 2015435 7659953 := bstep (se 2 (by rfl) ⟨2872482, by rfl⟩ : syracuseStep 7659953 = 5744965) B5744965
theorem B5106635 : Blo 2015435 5106635 := bstep (se 1 (by rfl) ⟨3829976, by rfl⟩ : syracuseStep 5106635 = 7659953) B7659953
theorem B3404423 : Blo 2015435 3404423 := bstep (se 1 (by rfl) ⟨2553317, by rfl⟩ : syracuseStep 3404423 = 5106635) B5106635
theorem B2269615 : Blo 2015435 2269615 := bstep (se 1 (by rfl) ⟨1702211, by rfl⟩ : syracuseStep 2269615 = 3404423) B3404423
theorem B3026153 : Blo 2015435 3026153 := bstep (se 2 (by rfl) ⟨1134807, by rfl⟩ : syracuseStep 3026153 = 2269615) B2269615
theorem B2017435 : Blo 2015435 2017435 := bstep (se 1 (by rfl) ⟨1513076, by rfl⟩ : syracuseStep 2017435 = 3026153) B3026153
theorem C0 (j : ℕ) (h1 : 503858 ≤ j) (h2 : j ≤ 504358) : Blo 2015435 (4 * j + 3) := by
  interval_cases j
  · exact B2015435
  · exact B2015439
  · exact B2015443
  · exact B2015447
  · exact B2015451
  · exact B2015455
  · exact B2015459
  · exact B2015463
  · exact B2015467
  · exact B2015471
  · exact B2015475
  · exact B2015479
  · exact B2015483
  · exact B2015487
  · exact B2015491
  · exact B2015495
  · exact B2015499
  · exact B2015503
  · exact B2015507
  · exact B2015511
  · exact B2015515
  · exact B2015519
  · exact B2015523
  · exact B2015527
  · exact B2015531
  · exact B2015535
  · exact B2015539
  · exact B2015543
  · exact B2015547
  · exact B2015551
  · exact B2015555
  · exact B2015559
  · exact B2015563
  · exact B2015567
  · exact B2015571
  · exact B2015575
  · exact B2015579
  · exact B2015583
  · exact B2015587
  · exact B2015591
  · exact B2015595
  · exact B2015599
  · exact B2015603
  · exact B2015607
  · exact B2015611
  · exact B2015615
  · exact B2015619
  · exact B2015623
  · exact B2015627
  · exact B2015631
  · exact B2015635
  · exact B2015639
  · exact B2015643
  · exact B2015647
  · exact B2015651
  · exact B2015655
  · exact B2015659
  · exact B2015663
  · exact B2015667
  · exact B2015671
  · exact B2015675
  · exact B2015679
  · exact B2015683
  · exact B2015687
  · exact B2015691
  · exact B2015695
  · exact B2015699
  · exact B2015703
  · exact B2015707
  · exact B2015711
  · exact B2015715
  · exact B2015719
  · exact B2015723
  · exact B2015727
  · exact B2015731
  · exact B2015735
  · exact B2015739
  · exact B2015743
  · exact B2015747
  · exact B2015751
  · exact B2015755
  · exact B2015759
  · exact B2015763
  · exact B2015767
  · exact B2015771
  · exact B2015775
  · exact B2015779
  · exact B2015783
  · exact B2015787
  · exact B2015791
  · exact B2015795
  · exact B2015799
  · exact B2015803
  · exact B2015807
  · exact B2015811
  · exact B2015815
  · exact B2015819
  · exact B2015823
  · exact B2015827
  · exact B2015831
  · exact B2015835
  · exact B2015839
  · exact B2015843
  · exact B2015847
  · exact B2015851
  · exact B2015855
  · exact B2015859
  · exact B2015863
  · exact B2015867
  · exact B2015871
  · exact B2015875
  · exact B2015879
  · exact B2015883
  · exact B2015887
  · exact B2015891
  · exact B2015895
  · exact B2015899
  · exact B2015903
  · exact B2015907
  · exact B2015911
  · exact B2015915
  · exact B2015919
  · exact B2015923
  · exact B2015927
  · exact B2015931
  · exact B2015935
  · exact B2015939
  · exact B2015943
  · exact B2015947
  · exact B2015951
  · exact B2015955
  · exact B2015959
  · exact B2015963
  · exact B2015967
  · exact B2015971
  · exact B2015975
  · exact B2015979
  · exact B2015983
  · exact B2015987
  · exact B2015991
  · exact B2015995
  · exact B2015999
  · exact B2016003
  · exact B2016007
  · exact B2016011
  · exact B2016015
  · exact B2016019
  · exact B2016023
  · exact B2016027
  · exact B2016031
  · exact B2016035
  · exact B2016039
  · exact B2016043
  · exact B2016047
  · exact B2016051
  · exact B2016055
  · exact B2016059
  · exact B2016063
  · exact B2016067
  · exact B2016071
  · exact B2016075
  · exact B2016079
  · exact B2016083
  · exact B2016087
  · exact B2016091
  · exact B2016095
  · exact B2016099
  · exact B2016103
  · exact B2016107
  · exact B2016111
  · exact B2016115
  · exact B2016119
  · exact B2016123
  · exact B2016127
  · exact B2016131
  · exact B2016135
  · exact B2016139
  · exact B2016143
  · exact B2016147
  · exact B2016151
  · exact B2016155
  · exact B2016159
  · exact B2016163
  · exact B2016167
  · exact B2016171
  · exact B2016175
  · exact B2016179
  · exact B2016183
  · exact B2016187
  · exact B2016191
  · exact B2016195
  · exact B2016199
  · exact B2016203
  · exact B2016207
  · exact B2016211
  · exact B2016215
  · exact B2016219
  · exact B2016223
  · exact B2016227
  · exact B2016231
  · exact B2016235
  · exact B2016239
  · exact B2016243
  · exact B2016247
  · exact B2016251
  · exact B2016255
  · exact B2016259
  · exact B2016263
  · exact B2016267
  · exact B2016271
  · exact B2016275
  · exact B2016279
  · exact B2016283
  · exact B2016287
  · exact B2016291
  · exact B2016295
  · exact B2016299
  · exact B2016303
  · exact B2016307
  · exact B2016311
  · exact B2016315
  · exact B2016319
  · exact B2016323
  · exact B2016327
  · exact B2016331
  · exact B2016335
  · exact B2016339
  · exact B2016343
  · exact B2016347
  · exact B2016351
  · exact B2016355
  · exact B2016359
  · exact B2016363
  · exact B2016367
  · exact B2016371
  · exact B2016375
  · exact B2016379
  · exact B2016383
  · exact B2016387
  · exact B2016391
  · exact B2016395
  · exact B2016399
  · exact B2016403
  · exact B2016407
  · exact B2016411
  · exact B2016415
  · exact B2016419
  · exact B2016423
  · exact B2016427
  · exact B2016431
  · exact B2016435
  · exact B2016439
  · exact B2016443
  · exact B2016447
  · exact B2016451
  · exact B2016455
  · exact B2016459
  · exact B2016463
  · exact B2016467
  · exact B2016471
  · exact B2016475
  · exact B2016479
  · exact B2016483
  · exact B2016487
  · exact B2016491
  · exact B2016495
  · exact B2016499
  · exact B2016503
  · exact B2016507
  · exact B2016511
  · exact B2016515
  · exact B2016519
  · exact B2016523
  · exact B2016527
  · exact B2016531
  · exact B2016535
  · exact B2016539
  · exact B2016543
  · exact B2016547
  · exact B2016551
  · exact B2016555
  · exact B2016559
  · exact B2016563
  · exact B2016567
  · exact B2016571
  · exact B2016575
  · exact B2016579
  · exact B2016583
  · exact B2016587
  · exact B2016591
  · exact B2016595
  · exact B2016599
  · exact B2016603
  · exact B2016607
  · exact B2016611
  · exact B2016615
  · exact B2016619
  · exact B2016623
  · exact B2016627
  · exact B2016631
  · exact B2016635
  · exact B2016639
  · exact B2016643
  · exact B2016647
  · exact B2016651
  · exact B2016655
  · exact B2016659
  · exact B2016663
  · exact B2016667
  · exact B2016671
  · exact B2016675
  · exact B2016679
  · exact B2016683
  · exact B2016687
  · exact B2016691
  · exact B2016695
  · exact B2016699
  · exact B2016703
  · exact B2016707
  · exact B2016711
  · exact B2016715
  · exact B2016719
  · exact B2016723
  · exact B2016727
  · exact B2016731
  · exact B2016735
  · exact B2016739
  · exact B2016743
  · exact B2016747
  · exact B2016751
  · exact B2016755
  · exact B2016759
  · exact B2016763
  · exact B2016767
  · exact B2016771
  · exact B2016775
  · exact B2016779
  · exact B2016783
  · exact B2016787
  · exact B2016791
  · exact B2016795
  · exact B2016799
  · exact B2016803
  · exact B2016807
  · exact B2016811
  · exact B2016815
  · exact B2016819
  · exact B2016823
  · exact B2016827
  · exact B2016831
  · exact B2016835
  · exact B2016839
  · exact B2016843
  · exact B2016847
  · exact B2016851
  · exact B2016855
  · exact B2016859
  · exact B2016863
  · exact B2016867
  · exact B2016871
  · exact B2016875
  · exact B2016879
  · exact B2016883
  · exact B2016887
  · exact B2016891
  · exact B2016895
  · exact B2016899
  · exact B2016903
  · exact B2016907
  · exact B2016911
  · exact B2016915
  · exact B2016919
  · exact B2016923
  · exact B2016927
  · exact B2016931
  · exact B2016935
  · exact B2016939
  · exact B2016943
  · exact B2016947
  · exact B2016951
  · exact B2016955
  · exact B2016959
  · exact B2016963
  · exact B2016967
  · exact B2016971
  · exact B2016975
  · exact B2016979
  · exact B2016983
  · exact B2016987
  · exact B2016991
  · exact B2016995
  · exact B2016999
  · exact B2017003
  · exact B2017007
  · exact B2017011
  · exact B2017015
  · exact B2017019
  · exact B2017023
  · exact B2017027
  · exact B2017031
  · exact B2017035
  · exact B2017039
  · exact B2017043
  · exact B2017047
  · exact B2017051
  · exact B2017055
  · exact B2017059
  · exact B2017063
  · exact B2017067
  · exact B2017071
  · exact B2017075
  · exact B2017079
  · exact B2017083
  · exact B2017087
  · exact B2017091
  · exact B2017095
  · exact B2017099
  · exact B2017103
  · exact B2017107
  · exact B2017111
  · exact B2017115
  · exact B2017119
  · exact B2017123
  · exact B2017127
  · exact B2017131
  · exact B2017135
  · exact B2017139
  · exact B2017143
  · exact B2017147
  · exact B2017151
  · exact B2017155
  · exact B2017159
  · exact B2017163
  · exact B2017167
  · exact B2017171
  · exact B2017175
  · exact B2017179
  · exact B2017183
  · exact B2017187
  · exact B2017191
  · exact B2017195
  · exact B2017199
  · exact B2017203
  · exact B2017207
  · exact B2017211
  · exact B2017215
  · exact B2017219
  · exact B2017223
  · exact B2017227
  · exact B2017231
  · exact B2017235
  · exact B2017239
  · exact B2017243
  · exact B2017247
  · exact B2017251
  · exact B2017255
  · exact B2017259
  · exact B2017263
  · exact B2017267
  · exact B2017271
  · exact B2017275
  · exact B2017279
  · exact B2017283
  · exact B2017287
  · exact B2017291
  · exact B2017295
  · exact B2017299
  · exact B2017303
  · exact B2017307
  · exact B2017311
  · exact B2017315
  · exact B2017319
  · exact B2017323
  · exact B2017327
  · exact B2017331
  · exact B2017335
  · exact B2017339
  · exact B2017343
  · exact B2017347
  · exact B2017351
  · exact B2017355
  · exact B2017359
  · exact B2017363
  · exact B2017367
  · exact B2017371
  · exact B2017375
  · exact B2017379
  · exact B2017383
  · exact B2017387
  · exact B2017391
  · exact B2017395
  · exact B2017399
  · exact B2017403
  · exact B2017407
  · exact B2017411
  · exact B2017415
  · exact B2017419
  · exact B2017423
  · exact B2017427
  · exact B2017431
  · exact B2017435
theorem solution (m : ℕ) (hlo : 2015435 ≤ m) (hhi : m ≤ 2017435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 503858 ≤ j := by omega
    have hj2 : j ≤ 504358 := by omega
    have hb : Blo 2015435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
