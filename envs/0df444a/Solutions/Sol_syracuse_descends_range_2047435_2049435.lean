-- Prove2me | solution 1 for syracuse_descends_range_2047435_2049435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:22.937575+00:00
-- url     : https://prove2.me/submissions/6ae97ffd-3c67-41e1-82cf-e9eff11629f0

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

theorem B2303365 : Blo 2047435 2303365 := bbase (se 4 (by rfl) ⟨215940, by rfl⟩ : syracuseStep 2303365 = 431881) (by norm_num)
theorem B3071153 : Blo 2047435 3071153 := bstep (se 2 (by rfl) ⟨1151682, by rfl⟩ : syracuseStep 3071153 = 2303365) B2303365
theorem B2047435 : Blo 2047435 2047435 := bstep (se 1 (by rfl) ⟨1535576, by rfl⟩ : syracuseStep 2047435 = 3071153) B3071153
theorem B4372805 : Blo 2047435 4372805 := bbase (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) (by norm_num)
theorem B2915203 : Blo 2047435 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B3886937 : Blo 2047435 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B2591291 : Blo 2047435 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B6910109 : Blo 2047435 6910109 := bstep (se 3 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 6910109 = 2591291) B2591291
theorem B4606739 : Blo 2047435 4606739 := bstep (se 1 (by rfl) ⟨3455054, by rfl⟩ : syracuseStep 4606739 = 6910109) B6910109
theorem B3071159 : Blo 2047435 3071159 := bstep (se 1 (by rfl) ⟨2303369, by rfl⟩ : syracuseStep 3071159 = 4606739) B4606739
theorem B2047439 : Blo 2047435 2047439 := bstep (se 1 (by rfl) ⟨1535579, by rfl⟩ : syracuseStep 2047439 = 3071159) B3071159
theorem B3071165 : Blo 2047435 3071165 := bbase (se 3 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 3071165 = 1151687) (by norm_num)
theorem B2047443 : Blo 2047435 2047443 := bstep (se 1 (by rfl) ⟨1535582, by rfl⟩ : syracuseStep 2047443 = 3071165) B3071165
theorem B4606757 : Blo 2047435 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B3071171 : Blo 2047435 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B2047447 : Blo 2047435 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B5182613 : Blo 2047435 5182613 := bbase (se 6 (by rfl) ⟨121467, by rfl⟩ : syracuseStep 5182613 = 242935) (by norm_num)
theorem B3455075 : Blo 2047435 3455075 := bstep (se 1 (by rfl) ⟨2591306, by rfl⟩ : syracuseStep 3455075 = 5182613) B5182613
theorem B2303383 : Blo 2047435 2303383 := bstep (se 1 (by rfl) ⟨1727537, by rfl⟩ : syracuseStep 2303383 = 3455075) B3455075
theorem B3071177 : Blo 2047435 3071177 := bstep (se 2 (by rfl) ⟨1151691, by rfl⟩ : syracuseStep 3071177 = 2303383) B2303383
theorem B2047451 : Blo 2047435 2047451 := bstep (se 1 (by rfl) ⟨1535588, by rfl⟩ : syracuseStep 2047451 = 3071177) B3071177
theorem B3279629 : Blo 2047435 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B8745677 : Blo 2047435 8745677 := bstep (se 3 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 8745677 = 3279629) B3279629
theorem B5830451 : Blo 2047435 5830451 := bstep (se 1 (by rfl) ⟨4372838, by rfl⟩ : syracuseStep 5830451 = 8745677) B8745677
theorem B3886967 : Blo 2047435 3886967 := bstep (se 1 (by rfl) ⟨2915225, by rfl⟩ : syracuseStep 3886967 = 5830451) B5830451
theorem B10365245 : Blo 2047435 10365245 := bstep (se 3 (by rfl) ⟨1943483, by rfl⟩ : syracuseStep 10365245 = 3886967) B3886967
theorem B6910163 : Blo 2047435 6910163 := bstep (se 1 (by rfl) ⟨5182622, by rfl⟩ : syracuseStep 6910163 = 10365245) B10365245
theorem B4606775 : Blo 2047435 4606775 := bstep (se 1 (by rfl) ⟨3455081, by rfl⟩ : syracuseStep 4606775 = 6910163) B6910163
theorem B3071183 : Blo 2047435 3071183 := bstep (se 1 (by rfl) ⟨2303387, by rfl⟩ : syracuseStep 3071183 = 4606775) B4606775
theorem B2047455 : Blo 2047435 2047455 := bstep (se 1 (by rfl) ⟨1535591, by rfl⟩ : syracuseStep 2047455 = 3071183) B3071183
theorem B3071189 : Blo 2047435 3071189 := bbase (se 7 (by rfl) ⟨35990, by rfl⟩ : syracuseStep 3071189 = 71981) (by norm_num)
theorem B2047459 : Blo 2047435 2047459 := bstep (se 1 (by rfl) ⟨1535594, by rfl⟩ : syracuseStep 2047459 = 3071189) B3071189
theorem B2915237 : Blo 2047435 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B7773965 : Blo 2047435 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B5182643 : Blo 2047435 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B3455095 : Blo 2047435 3455095 := bstep (se 1 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 3455095 = 5182643) B5182643
theorem B4606793 : Blo 2047435 4606793 := bstep (se 2 (by rfl) ⟨1727547, by rfl⟩ : syracuseStep 4606793 = 3455095) B3455095
theorem B3071195 : Blo 2047435 3071195 := bstep (se 1 (by rfl) ⟨2303396, by rfl⟩ : syracuseStep 3071195 = 4606793) B4606793
theorem B2047463 : Blo 2047435 2047463 := bstep (se 1 (by rfl) ⟨1535597, by rfl⟩ : syracuseStep 2047463 = 3071195) B3071195
theorem B2303401 : Blo 2047435 2303401 := bbase (se 2 (by rfl) ⟨863775, by rfl⟩ : syracuseStep 2303401 = 1727551) (by norm_num)
theorem B3071201 : Blo 2047435 3071201 := bstep (se 2 (by rfl) ⟨1151700, by rfl⟩ : syracuseStep 3071201 = 2303401) B2303401
theorem B2047467 : Blo 2047435 2047467 := bstep (se 1 (by rfl) ⟨1535600, by rfl⟩ : syracuseStep 2047467 = 3071201) B3071201
theorem B2459741 : Blo 2047435 2459741 := bbase (se 3 (by rfl) ⟨461201, by rfl⟩ : syracuseStep 2459741 = 922403) (by norm_num)
theorem B6559309 : Blo 2047435 6559309 := bstep (se 3 (by rfl) ⟨1229870, by rfl⟩ : syracuseStep 6559309 = 2459741) B2459741
theorem B8745745 : Blo 2047435 8745745 := bstep (se 2 (by rfl) ⟨3279654, by rfl⟩ : syracuseStep 8745745 = 6559309) B6559309
theorem B11660993 : Blo 2047435 11660993 := bstep (se 2 (by rfl) ⟨4372872, by rfl⟩ : syracuseStep 11660993 = 8745745) B8745745
theorem B7773995 : Blo 2047435 7773995 := bstep (se 1 (by rfl) ⟨5830496, by rfl⟩ : syracuseStep 7773995 = 11660993) B11660993
theorem B5182663 : Blo 2047435 5182663 := bstep (se 1 (by rfl) ⟨3886997, by rfl⟩ : syracuseStep 5182663 = 7773995) B7773995
theorem B6910217 : Blo 2047435 6910217 := bstep (se 2 (by rfl) ⟨2591331, by rfl⟩ : syracuseStep 6910217 = 5182663) B5182663
theorem B4606811 : Blo 2047435 4606811 := bstep (se 1 (by rfl) ⟨3455108, by rfl⟩ : syracuseStep 4606811 = 6910217) B6910217
theorem B3071207 : Blo 2047435 3071207 := bstep (se 1 (by rfl) ⟨2303405, by rfl⟩ : syracuseStep 3071207 = 4606811) B4606811
theorem B2047471 : Blo 2047435 2047471 := bstep (se 1 (by rfl) ⟨1535603, by rfl⟩ : syracuseStep 2047471 = 3071207) B3071207
theorem B3071213 : Blo 2047435 3071213 := bbase (se 3 (by rfl) ⟨575852, by rfl⟩ : syracuseStep 3071213 = 1151705) (by norm_num)
theorem B2047475 : Blo 2047435 2047475 := bstep (se 1 (by rfl) ⟨1535606, by rfl⟩ : syracuseStep 2047475 = 3071213) B3071213
theorem B4606829 : Blo 2047435 4606829 := bbase (se 3 (by rfl) ⟨863780, by rfl⟩ : syracuseStep 4606829 = 1727561) (by norm_num)
theorem B3071219 : Blo 2047435 3071219 := bstep (se 1 (by rfl) ⟨2303414, by rfl⟩ : syracuseStep 3071219 = 4606829) B4606829
theorem B2047479 : Blo 2047435 2047479 := bstep (se 1 (by rfl) ⟨1535609, by rfl⟩ : syracuseStep 2047479 = 3071219) B3071219
theorem B3887021 : Blo 2047435 3887021 := bbase (se 3 (by rfl) ⟨728816, by rfl⟩ : syracuseStep 3887021 = 1457633) (by norm_num)
theorem B2591347 : Blo 2047435 2591347 := bstep (se 1 (by rfl) ⟨1943510, by rfl⟩ : syracuseStep 2591347 = 3887021) B3887021
theorem B3455129 : Blo 2047435 3455129 := bstep (se 2 (by rfl) ⟨1295673, by rfl⟩ : syracuseStep 3455129 = 2591347) B2591347
theorem B2303419 : Blo 2047435 2303419 := bstep (se 1 (by rfl) ⟨1727564, by rfl⟩ : syracuseStep 2303419 = 3455129) B3455129
theorem B3071225 : Blo 2047435 3071225 := bstep (se 2 (by rfl) ⟨1151709, by rfl⟩ : syracuseStep 3071225 = 2303419) B2303419
theorem B2047483 : Blo 2047435 2047483 := bstep (se 1 (by rfl) ⟨1535612, by rfl⟩ : syracuseStep 2047483 = 3071225) B3071225
theorem B7100117 : Blo 2047435 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B4733411 : Blo 2047435 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B12622429 : Blo 2047435 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B16829905 : Blo 2047435 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B22439873 : Blo 2047435 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B59839661 : Blo 2047435 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B159572429 : Blo 2047435 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B106381619 : Blo 2047435 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B70921079 : Blo 2047435 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B47280719 : Blo 2047435 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B126081917 : Blo 2047435 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B84054611 : Blo 2047435 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B224145629 : Blo 2047435 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B149430419 : Blo 2047435 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B99620279 : Blo 2047435 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B66413519 : Blo 2047435 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B44275679 : Blo 2047435 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B29517119 : Blo 2047435 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B19678079 : Blo 2047435 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B52474877 : Blo 2047435 52474877 := bstep (se 3 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 52474877 = 19678079) B19678079
theorem B34983251 : Blo 2047435 34983251 := bstep (se 1 (by rfl) ⟨26237438, by rfl⟩ : syracuseStep 34983251 = 52474877) B52474877
theorem B23322167 : Blo 2047435 23322167 := bstep (se 1 (by rfl) ⟨17491625, by rfl⟩ : syracuseStep 23322167 = 34983251) B34983251
theorem B15548111 : Blo 2047435 15548111 := bstep (se 1 (by rfl) ⟨11661083, by rfl⟩ : syracuseStep 15548111 = 23322167) B23322167
theorem B10365407 : Blo 2047435 10365407 := bstep (se 1 (by rfl) ⟨7774055, by rfl⟩ : syracuseStep 10365407 = 15548111) B15548111
theorem B6910271 : Blo 2047435 6910271 := bstep (se 1 (by rfl) ⟨5182703, by rfl⟩ : syracuseStep 6910271 = 10365407) B10365407
theorem B4606847 : Blo 2047435 4606847 := bstep (se 1 (by rfl) ⟨3455135, by rfl⟩ : syracuseStep 4606847 = 6910271) B6910271
theorem B3071231 : Blo 2047435 3071231 := bstep (se 1 (by rfl) ⟨2303423, by rfl⟩ : syracuseStep 3071231 = 4606847) B4606847
theorem B2047487 : Blo 2047435 2047487 := bstep (se 1 (by rfl) ⟨1535615, by rfl⟩ : syracuseStep 2047487 = 3071231) B3071231
theorem B3071237 : Blo 2047435 3071237 := bbase (se 4 (by rfl) ⟨287928, by rfl⟩ : syracuseStep 3071237 = 575857) (by norm_num)
theorem B2047491 : Blo 2047435 2047491 := bstep (se 1 (by rfl) ⟨1535618, by rfl⟩ : syracuseStep 2047491 = 3071237) B3071237
theorem B3455149 : Blo 2047435 3455149 := bbase (se 3 (by rfl) ⟨647840, by rfl⟩ : syracuseStep 3455149 = 1295681) (by norm_num)
theorem B4606865 : Blo 2047435 4606865 := bstep (se 2 (by rfl) ⟨1727574, by rfl⟩ : syracuseStep 4606865 = 3455149) B3455149
theorem B3071243 : Blo 2047435 3071243 := bstep (se 1 (by rfl) ⟨2303432, by rfl⟩ : syracuseStep 3071243 = 4606865) B4606865
theorem B2047495 : Blo 2047435 2047495 := bstep (se 1 (by rfl) ⟨1535621, by rfl⟩ : syracuseStep 2047495 = 3071243) B3071243
theorem B2303437 : Blo 2047435 2303437 := bbase (se 3 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 2303437 = 863789) (by norm_num)
theorem B3071249 : Blo 2047435 3071249 := bstep (se 2 (by rfl) ⟨1151718, by rfl⟩ : syracuseStep 3071249 = 2303437) B2303437
theorem B2047499 : Blo 2047435 2047499 := bstep (se 1 (by rfl) ⟨1535624, by rfl⟩ : syracuseStep 2047499 = 3071249) B3071249
theorem B6910325 : Blo 2047435 6910325 := bbase (se 5 (by rfl) ⟨323921, by rfl⟩ : syracuseStep 6910325 = 647843) (by norm_num)
theorem B4606883 : Blo 2047435 4606883 := bstep (se 1 (by rfl) ⟨3455162, by rfl⟩ : syracuseStep 4606883 = 6910325) B6910325
theorem B3071255 : Blo 2047435 3071255 := bstep (se 1 (by rfl) ⟨2303441, by rfl⟩ : syracuseStep 3071255 = 4606883) B4606883
theorem B2047503 : Blo 2047435 2047503 := bstep (se 1 (by rfl) ⟨1535627, by rfl⟩ : syracuseStep 2047503 = 3071255) B3071255
theorem B3071261 : Blo 2047435 3071261 := bbase (se 3 (by rfl) ⟨575861, by rfl⟩ : syracuseStep 3071261 = 1151723) (by norm_num)
theorem B2047507 : Blo 2047435 2047507 := bstep (se 1 (by rfl) ⟨1535630, by rfl⟩ : syracuseStep 2047507 = 3071261) B3071261
theorem B4606901 : Blo 2047435 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B3071267 : Blo 2047435 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B2047511 : Blo 2047435 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B3502325 : Blo 2047435 3502325 := bbase (se 5 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 3502325 = 328343) (by norm_num)
theorem B9339533 : Blo 2047435 9339533 := bstep (se 3 (by rfl) ⟨1751162, by rfl⟩ : syracuseStep 9339533 = 3502325) B3502325
theorem B6226355 : Blo 2047435 6226355 := bstep (se 1 (by rfl) ⟨4669766, by rfl⟩ : syracuseStep 6226355 = 9339533) B9339533
theorem B16603613 : Blo 2047435 16603613 := bstep (se 3 (by rfl) ⟨3113177, by rfl⟩ : syracuseStep 16603613 = 6226355) B6226355
theorem B11069075 : Blo 2047435 11069075 := bstep (se 1 (by rfl) ⟨8301806, by rfl⟩ : syracuseStep 11069075 = 16603613) B16603613
theorem B7379383 : Blo 2047435 7379383 := bstep (se 1 (by rfl) ⟨5534537, by rfl⟩ : syracuseStep 7379383 = 11069075) B11069075
theorem B9839177 : Blo 2047435 9839177 := bstep (se 2 (by rfl) ⟨3689691, by rfl⟩ : syracuseStep 9839177 = 7379383) B7379383
theorem B6559451 : Blo 2047435 6559451 := bstep (se 1 (by rfl) ⟨4919588, by rfl⟩ : syracuseStep 6559451 = 9839177) B9839177
theorem B4372967 : Blo 2047435 4372967 := bstep (se 1 (by rfl) ⟨3279725, by rfl⟩ : syracuseStep 4372967 = 6559451) B6559451
theorem B11661245 : Blo 2047435 11661245 := bstep (se 3 (by rfl) ⟨2186483, by rfl⟩ : syracuseStep 11661245 = 4372967) B4372967
theorem B7774163 : Blo 2047435 7774163 := bstep (se 1 (by rfl) ⟨5830622, by rfl⟩ : syracuseStep 7774163 = 11661245) B11661245
theorem B5182775 : Blo 2047435 5182775 := bstep (se 1 (by rfl) ⟨3887081, by rfl⟩ : syracuseStep 5182775 = 7774163) B7774163
theorem B3455183 : Blo 2047435 3455183 := bstep (se 1 (by rfl) ⟨2591387, by rfl⟩ : syracuseStep 3455183 = 5182775) B5182775
theorem B2303455 : Blo 2047435 2303455 := bstep (se 1 (by rfl) ⟨1727591, by rfl⟩ : syracuseStep 2303455 = 3455183) B3455183
theorem B3071273 : Blo 2047435 3071273 := bstep (se 2 (by rfl) ⟨1151727, by rfl⟩ : syracuseStep 3071273 = 2303455) B2303455
theorem B2047515 : Blo 2047435 2047515 := bstep (se 1 (by rfl) ⟨1535636, by rfl⟩ : syracuseStep 2047515 = 3071273) B3071273
theorem B31520981 : Blo 2047435 31520981 := bbase (se 7 (by rfl) ⟨369386, by rfl⟩ : syracuseStep 31520981 = 738773) (by norm_num)
theorem B21013987 : Blo 2047435 21013987 := bstep (se 1 (by rfl) ⟨15760490, by rfl⟩ : syracuseStep 21013987 = 31520981) B31520981
theorem B28018649 : Blo 2047435 28018649 := bstep (se 2 (by rfl) ⟨10506993, by rfl⟩ : syracuseStep 28018649 = 21013987) B21013987
theorem B18679099 : Blo 2047435 18679099 := bstep (se 1 (by rfl) ⟨14009324, by rfl⟩ : syracuseStep 18679099 = 28018649) B28018649
theorem B24905465 : Blo 2047435 24905465 := bstep (se 2 (by rfl) ⟨9339549, by rfl⟩ : syracuseStep 24905465 = 18679099) B18679099
theorem B16603643 : Blo 2047435 16603643 := bstep (se 1 (by rfl) ⟨12452732, by rfl⟩ : syracuseStep 16603643 = 24905465) B24905465
theorem B11069095 : Blo 2047435 11069095 := bstep (se 1 (by rfl) ⟨8301821, by rfl⟩ : syracuseStep 11069095 = 16603643) B16603643
theorem B14758793 : Blo 2047435 14758793 := bstep (se 2 (by rfl) ⟨5534547, by rfl⟩ : syracuseStep 14758793 = 11069095) B11069095
theorem B9839195 : Blo 2047435 9839195 := bstep (se 1 (by rfl) ⟨7379396, by rfl⟩ : syracuseStep 9839195 = 14758793) B14758793
theorem B6559463 : Blo 2047435 6559463 := bstep (se 1 (by rfl) ⟨4919597, by rfl⟩ : syracuseStep 6559463 = 9839195) B9839195
theorem B4372975 : Blo 2047435 4372975 := bstep (se 1 (by rfl) ⟨3279731, by rfl⟩ : syracuseStep 4372975 = 6559463) B6559463
theorem B5830633 : Blo 2047435 5830633 := bstep (se 2 (by rfl) ⟨2186487, by rfl⟩ : syracuseStep 5830633 = 4372975) B4372975
theorem B7774177 : Blo 2047435 7774177 := bstep (se 2 (by rfl) ⟨2915316, by rfl⟩ : syracuseStep 7774177 = 5830633) B5830633
theorem B10365569 : Blo 2047435 10365569 := bstep (se 2 (by rfl) ⟨3887088, by rfl⟩ : syracuseStep 10365569 = 7774177) B7774177
theorem B6910379 : Blo 2047435 6910379 := bstep (se 1 (by rfl) ⟨5182784, by rfl⟩ : syracuseStep 6910379 = 10365569) B10365569
theorem B4606919 : Blo 2047435 4606919 := bstep (se 1 (by rfl) ⟨3455189, by rfl⟩ : syracuseStep 4606919 = 6910379) B6910379
theorem B3071279 : Blo 2047435 3071279 := bstep (se 1 (by rfl) ⟨2303459, by rfl⟩ : syracuseStep 3071279 = 4606919) B4606919
theorem B2047519 : Blo 2047435 2047519 := bstep (se 1 (by rfl) ⟨1535639, by rfl⟩ : syracuseStep 2047519 = 3071279) B3071279
theorem B3071285 : Blo 2047435 3071285 := bbase (se 5 (by rfl) ⟨143966, by rfl⟩ : syracuseStep 3071285 = 287933) (by norm_num)
theorem B2047523 : Blo 2047435 2047523 := bstep (se 1 (by rfl) ⟨1535642, by rfl⟩ : syracuseStep 2047523 = 3071285) B3071285
theorem B5182805 : Blo 2047435 5182805 := bbase (se 14 (by rfl) ⟨474, by rfl⟩ : syracuseStep 5182805 = 949) (by norm_num)
theorem B3455203 : Blo 2047435 3455203 := bstep (se 1 (by rfl) ⟨2591402, by rfl⟩ : syracuseStep 3455203 = 5182805) B5182805
theorem B4606937 : Blo 2047435 4606937 := bstep (se 2 (by rfl) ⟨1727601, by rfl⟩ : syracuseStep 4606937 = 3455203) B3455203
theorem B3071291 : Blo 2047435 3071291 := bstep (se 1 (by rfl) ⟨2303468, by rfl⟩ : syracuseStep 3071291 = 4606937) B4606937
theorem B2047527 : Blo 2047435 2047527 := bstep (se 1 (by rfl) ⟨1535645, by rfl⟩ : syracuseStep 2047527 = 3071291) B3071291
theorem B2303473 : Blo 2047435 2303473 := bbase (se 2 (by rfl) ⟨863802, by rfl⟩ : syracuseStep 2303473 = 1727605) (by norm_num)
theorem B3071297 : Blo 2047435 3071297 := bstep (se 2 (by rfl) ⟨1151736, by rfl⟩ : syracuseStep 3071297 = 2303473) B2303473
theorem B2047531 : Blo 2047435 2047531 := bstep (se 1 (by rfl) ⟨1535648, by rfl⟩ : syracuseStep 2047531 = 3071297) B3071297
theorem B13119029 : Blo 2047435 13119029 := bbase (se 5 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 13119029 = 1229909) (by norm_num)
theorem B8746019 : Blo 2047435 8746019 := bstep (se 1 (by rfl) ⟨6559514, by rfl⟩ : syracuseStep 8746019 = 13119029) B13119029
theorem B5830679 : Blo 2047435 5830679 := bstep (se 1 (by rfl) ⟨4373009, by rfl⟩ : syracuseStep 5830679 = 8746019) B8746019
theorem B3887119 : Blo 2047435 3887119 := bstep (se 1 (by rfl) ⟨2915339, by rfl⟩ : syracuseStep 3887119 = 5830679) B5830679
theorem B5182825 : Blo 2047435 5182825 := bstep (se 2 (by rfl) ⟨1943559, by rfl⟩ : syracuseStep 5182825 = 3887119) B3887119
theorem B6910433 : Blo 2047435 6910433 := bstep (se 2 (by rfl) ⟨2591412, by rfl⟩ : syracuseStep 6910433 = 5182825) B5182825
theorem B4606955 : Blo 2047435 4606955 := bstep (se 1 (by rfl) ⟨3455216, by rfl⟩ : syracuseStep 4606955 = 6910433) B6910433
theorem B3071303 : Blo 2047435 3071303 := bstep (se 1 (by rfl) ⟨2303477, by rfl⟩ : syracuseStep 3071303 = 4606955) B4606955
theorem B2047535 : Blo 2047435 2047535 := bstep (se 1 (by rfl) ⟨1535651, by rfl⟩ : syracuseStep 2047535 = 3071303) B3071303
theorem B3071309 : Blo 2047435 3071309 := bbase (se 3 (by rfl) ⟨575870, by rfl⟩ : syracuseStep 3071309 = 1151741) (by norm_num)
theorem B2047539 : Blo 2047435 2047539 := bstep (se 1 (by rfl) ⟨1535654, by rfl⟩ : syracuseStep 2047539 = 3071309) B3071309
theorem B4606973 : Blo 2047435 4606973 := bbase (se 3 (by rfl) ⟨863807, by rfl⟩ : syracuseStep 4606973 = 1727615) (by norm_num)
theorem B3071315 : Blo 2047435 3071315 := bstep (se 1 (by rfl) ⟨2303486, by rfl⟩ : syracuseStep 3071315 = 4606973) B4606973
theorem B2047543 : Blo 2047435 2047543 := bstep (se 1 (by rfl) ⟨1535657, by rfl⟩ : syracuseStep 2047543 = 3071315) B3071315
theorem B3455237 : Blo 2047435 3455237 := bbase (se 4 (by rfl) ⟨323928, by rfl⟩ : syracuseStep 3455237 = 647857) (by norm_num)
theorem B2303491 : Blo 2047435 2303491 := bstep (se 1 (by rfl) ⟨1727618, by rfl⟩ : syracuseStep 2303491 = 3455237) B3455237
theorem B3071321 : Blo 2047435 3071321 := bstep (se 2 (by rfl) ⟨1151745, by rfl⟩ : syracuseStep 3071321 = 2303491) B2303491
theorem B2047547 : Blo 2047435 2047547 := bstep (se 1 (by rfl) ⟨1535660, by rfl⟩ : syracuseStep 2047547 = 3071321) B3071321
theorem B15548597 : Blo 2047435 15548597 := bbase (se 5 (by rfl) ⟨728840, by rfl⟩ : syracuseStep 15548597 = 1457681) (by norm_num)
theorem B10365731 : Blo 2047435 10365731 := bstep (se 1 (by rfl) ⟨7774298, by rfl⟩ : syracuseStep 10365731 = 15548597) B15548597
theorem B6910487 : Blo 2047435 6910487 := bstep (se 1 (by rfl) ⟨5182865, by rfl⟩ : syracuseStep 6910487 = 10365731) B10365731
theorem B4606991 : Blo 2047435 4606991 := bstep (se 1 (by rfl) ⟨3455243, by rfl⟩ : syracuseStep 4606991 = 6910487) B6910487
theorem B3071327 : Blo 2047435 3071327 := bstep (se 1 (by rfl) ⟨2303495, by rfl⟩ : syracuseStep 3071327 = 4606991) B4606991
theorem B2047551 : Blo 2047435 2047551 := bstep (se 1 (by rfl) ⟨1535663, by rfl⟩ : syracuseStep 2047551 = 3071327) B3071327
theorem B3071333 : Blo 2047435 3071333 := bbase (se 4 (by rfl) ⟨287937, by rfl⟩ : syracuseStep 3071333 = 575875) (by norm_num)
theorem B2047555 : Blo 2047435 2047555 := bstep (se 1 (by rfl) ⟨1535666, by rfl⟩ : syracuseStep 2047555 = 3071333) B3071333
theorem B3887165 : Blo 2047435 3887165 := bbase (se 3 (by rfl) ⟨728843, by rfl⟩ : syracuseStep 3887165 = 1457687) (by norm_num)
theorem B2591443 : Blo 2047435 2591443 := bstep (se 1 (by rfl) ⟨1943582, by rfl⟩ : syracuseStep 2591443 = 3887165) B3887165
theorem B3455257 : Blo 2047435 3455257 := bstep (se 2 (by rfl) ⟨1295721, by rfl⟩ : syracuseStep 3455257 = 2591443) B2591443
theorem B4607009 : Blo 2047435 4607009 := bstep (se 2 (by rfl) ⟨1727628, by rfl⟩ : syracuseStep 4607009 = 3455257) B3455257
theorem B3071339 : Blo 2047435 3071339 := bstep (se 1 (by rfl) ⟨2303504, by rfl⟩ : syracuseStep 3071339 = 4607009) B4607009
theorem B2047559 : Blo 2047435 2047559 := bstep (se 1 (by rfl) ⟨1535669, by rfl⟩ : syracuseStep 2047559 = 3071339) B3071339
theorem B2303509 : Blo 2047435 2303509 := bbase (se 6 (by rfl) ⟨53988, by rfl⟩ : syracuseStep 2303509 = 107977) (by norm_num)
theorem B3071345 : Blo 2047435 3071345 := bstep (se 2 (by rfl) ⟨1151754, by rfl⟩ : syracuseStep 3071345 = 2303509) B2303509
theorem B2047563 : Blo 2047435 2047563 := bstep (se 1 (by rfl) ⟨1535672, by rfl⟩ : syracuseStep 2047563 = 3071345) B3071345
theorem B2591453 : Blo 2047435 2591453 := bbase (se 3 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 2591453 = 971795) (by norm_num)
theorem B6910541 : Blo 2047435 6910541 := bstep (se 3 (by rfl) ⟨1295726, by rfl⟩ : syracuseStep 6910541 = 2591453) B2591453
theorem B4607027 : Blo 2047435 4607027 := bstep (se 1 (by rfl) ⟨3455270, by rfl⟩ : syracuseStep 4607027 = 6910541) B6910541
theorem B3071351 : Blo 2047435 3071351 := bstep (se 1 (by rfl) ⟨2303513, by rfl⟩ : syracuseStep 3071351 = 4607027) B4607027
theorem B2047567 : Blo 2047435 2047567 := bstep (se 1 (by rfl) ⟨1535675, by rfl⟩ : syracuseStep 2047567 = 3071351) B3071351
theorem B3071357 : Blo 2047435 3071357 := bbase (se 3 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 3071357 = 1151759) (by norm_num)
theorem B2047571 : Blo 2047435 2047571 := bstep (se 1 (by rfl) ⟨1535678, by rfl⟩ : syracuseStep 2047571 = 3071357) B3071357
theorem B4607045 : Blo 2047435 4607045 := bbase (se 4 (by rfl) ⟨431910, by rfl⟩ : syracuseStep 4607045 = 863821) (by norm_num)
theorem B3071363 : Blo 2047435 3071363 := bstep (se 1 (by rfl) ⟨2303522, by rfl⟩ : syracuseStep 3071363 = 4607045) B4607045
theorem B2047575 : Blo 2047435 2047575 := bstep (se 1 (by rfl) ⟨1535681, by rfl⟩ : syracuseStep 2047575 = 3071363) B3071363
theorem B5830805 : Blo 2047435 5830805 := bbase (se 6 (by rfl) ⟨136659, by rfl⟩ : syracuseStep 5830805 = 273319) (by norm_num)
theorem B3887203 : Blo 2047435 3887203 := bstep (se 1 (by rfl) ⟨2915402, by rfl⟩ : syracuseStep 3887203 = 5830805) B5830805
theorem B5182937 : Blo 2047435 5182937 := bstep (se 2 (by rfl) ⟨1943601, by rfl⟩ : syracuseStep 5182937 = 3887203) B3887203
theorem B3455291 : Blo 2047435 3455291 := bstep (se 1 (by rfl) ⟨2591468, by rfl⟩ : syracuseStep 3455291 = 5182937) B5182937
theorem B2303527 : Blo 2047435 2303527 := bstep (se 1 (by rfl) ⟨1727645, by rfl⟩ : syracuseStep 2303527 = 3455291) B3455291
theorem B3071369 : Blo 2047435 3071369 := bstep (se 2 (by rfl) ⟨1151763, by rfl⟩ : syracuseStep 3071369 = 2303527) B2303527
theorem B2047579 : Blo 2047435 2047579 := bstep (se 1 (by rfl) ⟨1535684, by rfl⟩ : syracuseStep 2047579 = 3071369) B3071369
theorem B10365893 : Blo 2047435 10365893 := bbase (se 4 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 10365893 = 1943605) (by norm_num)
theorem B6910595 : Blo 2047435 6910595 := bstep (se 1 (by rfl) ⟨5182946, by rfl⟩ : syracuseStep 6910595 = 10365893) B10365893
theorem B4607063 : Blo 2047435 4607063 := bstep (se 1 (by rfl) ⟨3455297, by rfl⟩ : syracuseStep 4607063 = 6910595) B6910595
theorem B3071375 : Blo 2047435 3071375 := bstep (se 1 (by rfl) ⟨2303531, by rfl⟩ : syracuseStep 3071375 = 4607063) B4607063
theorem B2047583 : Blo 2047435 2047583 := bstep (se 1 (by rfl) ⟨1535687, by rfl⟩ : syracuseStep 2047583 = 3071375) B3071375
theorem B3071381 : Blo 2047435 3071381 := bbase (se 6 (by rfl) ⟨71985, by rfl⟩ : syracuseStep 3071381 = 143971) (by norm_num)
theorem B2047587 : Blo 2047435 2047587 := bstep (se 1 (by rfl) ⟨1535690, by rfl⟩ : syracuseStep 2047587 = 3071381) B3071381
theorem B12453173 : Blo 2047435 12453173 := bbase (se 5 (by rfl) ⟨583742, by rfl⟩ : syracuseStep 12453173 = 1167485) (by norm_num)
theorem B8302115 : Blo 2047435 8302115 := bstep (se 1 (by rfl) ⟨6226586, by rfl⟩ : syracuseStep 8302115 = 12453173) B12453173
theorem B5534743 : Blo 2047435 5534743 := bstep (se 1 (by rfl) ⟨4151057, by rfl⟩ : syracuseStep 5534743 = 8302115) B8302115
theorem B7379657 : Blo 2047435 7379657 := bstep (se 2 (by rfl) ⟨2767371, by rfl⟩ : syracuseStep 7379657 = 5534743) B5534743
theorem B4919771 : Blo 2047435 4919771 := bstep (se 1 (by rfl) ⟨3689828, by rfl⟩ : syracuseStep 4919771 = 7379657) B7379657
theorem B3279847 : Blo 2047435 3279847 := bstep (se 1 (by rfl) ⟨2459885, by rfl⟩ : syracuseStep 3279847 = 4919771) B4919771
theorem B4373129 : Blo 2047435 4373129 := bstep (se 2 (by rfl) ⟨1639923, by rfl⟩ : syracuseStep 4373129 = 3279847) B3279847
theorem B11661677 : Blo 2047435 11661677 := bstep (se 3 (by rfl) ⟨2186564, by rfl⟩ : syracuseStep 11661677 = 4373129) B4373129
theorem B7774451 : Blo 2047435 7774451 := bstep (se 1 (by rfl) ⟨5830838, by rfl⟩ : syracuseStep 7774451 = 11661677) B11661677
theorem B5182967 : Blo 2047435 5182967 := bstep (se 1 (by rfl) ⟨3887225, by rfl⟩ : syracuseStep 5182967 = 7774451) B7774451
theorem B3455311 : Blo 2047435 3455311 := bstep (se 1 (by rfl) ⟨2591483, by rfl⟩ : syracuseStep 3455311 = 5182967) B5182967
theorem B4607081 : Blo 2047435 4607081 := bstep (se 2 (by rfl) ⟨1727655, by rfl⟩ : syracuseStep 4607081 = 3455311) B3455311
theorem B3071387 : Blo 2047435 3071387 := bstep (se 1 (by rfl) ⟨2303540, by rfl⟩ : syracuseStep 3071387 = 4607081) B4607081
theorem B2047591 : Blo 2047435 2047591 := bstep (se 1 (by rfl) ⟨1535693, by rfl⟩ : syracuseStep 2047591 = 3071387) B3071387
theorem B2303545 : Blo 2047435 2303545 := bbase (se 2 (by rfl) ⟨863829, by rfl⟩ : syracuseStep 2303545 = 1727659) (by norm_num)
theorem B3071393 : Blo 2047435 3071393 := bstep (se 2 (by rfl) ⟨1151772, by rfl⟩ : syracuseStep 3071393 = 2303545) B2303545
theorem B2047595 : Blo 2047435 2047595 := bstep (se 1 (by rfl) ⟨1535696, by rfl⟩ : syracuseStep 2047595 = 3071393) B3071393
theorem B2186573 : Blo 2047435 2186573 := bbase (se 3 (by rfl) ⟨409982, by rfl⟩ : syracuseStep 2186573 = 819965) (by norm_num)
theorem B5830861 : Blo 2047435 5830861 := bstep (se 3 (by rfl) ⟨1093286, by rfl⟩ : syracuseStep 5830861 = 2186573) B2186573
theorem B7774481 : Blo 2047435 7774481 := bstep (se 2 (by rfl) ⟨2915430, by rfl⟩ : syracuseStep 7774481 = 5830861) B5830861
theorem B5182987 : Blo 2047435 5182987 := bstep (se 1 (by rfl) ⟨3887240, by rfl⟩ : syracuseStep 5182987 = 7774481) B7774481
theorem B6910649 : Blo 2047435 6910649 := bstep (se 2 (by rfl) ⟨2591493, by rfl⟩ : syracuseStep 6910649 = 5182987) B5182987
theorem B4607099 : Blo 2047435 4607099 := bstep (se 1 (by rfl) ⟨3455324, by rfl⟩ : syracuseStep 4607099 = 6910649) B6910649
theorem B3071399 : Blo 2047435 3071399 := bstep (se 1 (by rfl) ⟨2303549, by rfl⟩ : syracuseStep 3071399 = 4607099) B4607099
theorem B2047599 : Blo 2047435 2047599 := bstep (se 1 (by rfl) ⟨1535699, by rfl⟩ : syracuseStep 2047599 = 3071399) B3071399
theorem B3071405 : Blo 2047435 3071405 := bbase (se 3 (by rfl) ⟨575888, by rfl⟩ : syracuseStep 3071405 = 1151777) (by norm_num)
theorem B2047603 : Blo 2047435 2047603 := bstep (se 1 (by rfl) ⟨1535702, by rfl⟩ : syracuseStep 2047603 = 3071405) B3071405
theorem B4607117 : Blo 2047435 4607117 := bbase (se 3 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 4607117 = 1727669) (by norm_num)
theorem B3071411 : Blo 2047435 3071411 := bstep (se 1 (by rfl) ⟨2303558, by rfl⟩ : syracuseStep 3071411 = 4607117) B4607117
theorem B2047607 : Blo 2047435 2047607 := bstep (se 1 (by rfl) ⟨1535705, by rfl⟩ : syracuseStep 2047607 = 3071411) B3071411
theorem B2591509 : Blo 2047435 2591509 := bbase (se 6 (by rfl) ⟨60738, by rfl⟩ : syracuseStep 2591509 = 121477) (by norm_num)
theorem B3455345 : Blo 2047435 3455345 := bstep (se 2 (by rfl) ⟨1295754, by rfl⟩ : syracuseStep 3455345 = 2591509) B2591509
theorem B2303563 : Blo 2047435 2303563 := bstep (se 1 (by rfl) ⟨1727672, by rfl⟩ : syracuseStep 2303563 = 3455345) B3455345
theorem B3071417 : Blo 2047435 3071417 := bstep (se 2 (by rfl) ⟨1151781, by rfl⟩ : syracuseStep 3071417 = 2303563) B2303563
theorem B2047611 : Blo 2047435 2047611 := bstep (se 1 (by rfl) ⟨1535708, by rfl⟩ : syracuseStep 2047611 = 3071417) B3071417
theorem B3740213 : Blo 2047435 3740213 := bbase (se 5 (by rfl) ⟨175322, by rfl⟩ : syracuseStep 3740213 = 350645) (by norm_num)
theorem B9973901 : Blo 2047435 9973901 := bstep (se 3 (by rfl) ⟨1870106, by rfl⟩ : syracuseStep 9973901 = 3740213) B3740213
theorem B26597069 : Blo 2047435 26597069 := bstep (se 3 (by rfl) ⟨4986950, by rfl⟩ : syracuseStep 26597069 = 9973901) B9973901
theorem B17731379 : Blo 2047435 17731379 := bstep (se 1 (by rfl) ⟨13298534, by rfl⟩ : syracuseStep 17731379 = 26597069) B26597069
theorem B11820919 : Blo 2047435 11820919 := bstep (se 1 (by rfl) ⟨8865689, by rfl⟩ : syracuseStep 11820919 = 17731379) B17731379
theorem B15761225 : Blo 2047435 15761225 := bstep (se 2 (by rfl) ⟨5910459, by rfl⟩ : syracuseStep 15761225 = 11820919) B11820919
theorem B42029933 : Blo 2047435 42029933 := bstep (se 3 (by rfl) ⟨7880612, by rfl⟩ : syracuseStep 42029933 = 15761225) B15761225
theorem B112079821 : Blo 2047435 112079821 := bstep (se 3 (by rfl) ⟨21014966, by rfl⟩ : syracuseStep 112079821 = 42029933) B42029933
theorem B149439761 : Blo 2047435 149439761 := bstep (se 2 (by rfl) ⟨56039910, by rfl⟩ : syracuseStep 149439761 = 112079821) B112079821
theorem B99626507 : Blo 2047435 99626507 := bstep (se 1 (by rfl) ⟨74719880, by rfl⟩ : syracuseStep 99626507 = 149439761) B149439761
theorem B66417671 : Blo 2047435 66417671 := bstep (se 1 (by rfl) ⟨49813253, by rfl⟩ : syracuseStep 66417671 = 99626507) B99626507
theorem B44278447 : Blo 2047435 44278447 := bstep (se 1 (by rfl) ⟨33208835, by rfl⟩ : syracuseStep 44278447 = 66417671) B66417671
theorem B59037929 : Blo 2047435 59037929 := bstep (se 2 (by rfl) ⟨22139223, by rfl⟩ : syracuseStep 59037929 = 44278447) B44278447
theorem B39358619 : Blo 2047435 39358619 := bstep (se 1 (by rfl) ⟨29518964, by rfl⟩ : syracuseStep 39358619 = 59037929) B59037929
theorem B26239079 : Blo 2047435 26239079 := bstep (se 1 (by rfl) ⟨19679309, by rfl⟩ : syracuseStep 26239079 = 39358619) B39358619
theorem B17492719 : Blo 2047435 17492719 := bstep (se 1 (by rfl) ⟨13119539, by rfl⟩ : syracuseStep 17492719 = 26239079) B26239079
theorem B23323625 : Blo 2047435 23323625 := bstep (se 2 (by rfl) ⟨8746359, by rfl⟩ : syracuseStep 23323625 = 17492719) B17492719
theorem B15549083 : Blo 2047435 15549083 := bstep (se 1 (by rfl) ⟨11661812, by rfl⟩ : syracuseStep 15549083 = 23323625) B23323625
theorem B10366055 : Blo 2047435 10366055 := bstep (se 1 (by rfl) ⟨7774541, by rfl⟩ : syracuseStep 10366055 = 15549083) B15549083
theorem B6910703 : Blo 2047435 6910703 := bstep (se 1 (by rfl) ⟨5183027, by rfl⟩ : syracuseStep 6910703 = 10366055) B10366055
theorem B4607135 : Blo 2047435 4607135 := bstep (se 1 (by rfl) ⟨3455351, by rfl⟩ : syracuseStep 4607135 = 6910703) B6910703
theorem B3071423 : Blo 2047435 3071423 := bstep (se 1 (by rfl) ⟨2303567, by rfl⟩ : syracuseStep 3071423 = 4607135) B4607135
theorem B2047615 : Blo 2047435 2047615 := bstep (se 1 (by rfl) ⟨1535711, by rfl⟩ : syracuseStep 2047615 = 3071423) B3071423
theorem B3071429 : Blo 2047435 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B2047619 : Blo 2047435 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B3455365 : Blo 2047435 3455365 := bbase (se 4 (by rfl) ⟨323940, by rfl⟩ : syracuseStep 3455365 = 647881) (by norm_num)
theorem B4607153 : Blo 2047435 4607153 := bstep (se 2 (by rfl) ⟨1727682, by rfl⟩ : syracuseStep 4607153 = 3455365) B3455365
theorem B3071435 : Blo 2047435 3071435 := bstep (se 1 (by rfl) ⟨2303576, by rfl⟩ : syracuseStep 3071435 = 4607153) B4607153
theorem B2047623 : Blo 2047435 2047623 := bstep (se 1 (by rfl) ⟨1535717, by rfl⟩ : syracuseStep 2047623 = 3071435) B3071435
theorem B2303581 : Blo 2047435 2303581 := bbase (se 3 (by rfl) ⟨431921, by rfl⟩ : syracuseStep 2303581 = 863843) (by norm_num)
theorem B3071441 : Blo 2047435 3071441 := bstep (se 2 (by rfl) ⟨1151790, by rfl⟩ : syracuseStep 3071441 = 2303581) B2303581
theorem B2047627 : Blo 2047435 2047627 := bstep (se 1 (by rfl) ⟨1535720, by rfl⟩ : syracuseStep 2047627 = 3071441) B3071441
theorem B6910757 : Blo 2047435 6910757 := bbase (se 4 (by rfl) ⟨647883, by rfl⟩ : syracuseStep 6910757 = 1295767) (by norm_num)
theorem B4607171 : Blo 2047435 4607171 := bstep (se 1 (by rfl) ⟨3455378, by rfl⟩ : syracuseStep 4607171 = 6910757) B6910757
theorem B3071447 : Blo 2047435 3071447 := bstep (se 1 (by rfl) ⟨2303585, by rfl⟩ : syracuseStep 3071447 = 4607171) B4607171
theorem B2047631 : Blo 2047435 2047631 := bstep (se 1 (by rfl) ⟨1535723, by rfl⟩ : syracuseStep 2047631 = 3071447) B3071447
theorem B3071453 : Blo 2047435 3071453 := bbase (se 3 (by rfl) ⟨575897, by rfl⟩ : syracuseStep 3071453 = 1151795) (by norm_num)
theorem B2047635 : Blo 2047435 2047635 := bstep (se 1 (by rfl) ⟨1535726, by rfl⟩ : syracuseStep 2047635 = 3071453) B3071453
theorem B4607189 : Blo 2047435 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B3071459 : Blo 2047435 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B2047639 : Blo 2047435 2047639 := bstep (se 1 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 2047639 = 3071459) B3071459
theorem B6559861 : Blo 2047435 6559861 := bbase (se 5 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 6559861 = 614987) (by norm_num)
theorem B8746481 : Blo 2047435 8746481 := bstep (se 2 (by rfl) ⟨3279930, by rfl⟩ : syracuseStep 8746481 = 6559861) B6559861
theorem B5830987 : Blo 2047435 5830987 := bstep (se 1 (by rfl) ⟨4373240, by rfl⟩ : syracuseStep 5830987 = 8746481) B8746481
theorem B7774649 : Blo 2047435 7774649 := bstep (se 2 (by rfl) ⟨2915493, by rfl⟩ : syracuseStep 7774649 = 5830987) B5830987
theorem B5183099 : Blo 2047435 5183099 := bstep (se 1 (by rfl) ⟨3887324, by rfl⟩ : syracuseStep 5183099 = 7774649) B7774649
theorem B3455399 : Blo 2047435 3455399 := bstep (se 1 (by rfl) ⟨2591549, by rfl⟩ : syracuseStep 3455399 = 5183099) B5183099
theorem B2303599 : Blo 2047435 2303599 := bstep (se 1 (by rfl) ⟨1727699, by rfl⟩ : syracuseStep 2303599 = 3455399) B3455399
theorem B3071465 : Blo 2047435 3071465 := bstep (se 2 (by rfl) ⟨1151799, by rfl⟩ : syracuseStep 3071465 = 2303599) B2303599
theorem B2047643 : Blo 2047435 2047643 := bstep (se 1 (by rfl) ⟨1535732, by rfl⟩ : syracuseStep 2047643 = 3071465) B3071465
theorem B2075585 : Blo 2047435 2075585 := bbase (se 2 (by rfl) ⟨778344, by rfl⟩ : syracuseStep 2075585 = 1556689) (by norm_num)
theorem B5534893 : Blo 2047435 5534893 := bstep (se 3 (by rfl) ⟨1037792, by rfl⟩ : syracuseStep 5534893 = 2075585) B2075585
theorem B7379857 : Blo 2047435 7379857 := bstep (se 2 (by rfl) ⟨2767446, by rfl⟩ : syracuseStep 7379857 = 5534893) B5534893
theorem B9839809 : Blo 2047435 9839809 := bstep (se 2 (by rfl) ⟨3689928, by rfl⟩ : syracuseStep 9839809 = 7379857) B7379857
theorem B13119745 : Blo 2047435 13119745 := bstep (se 2 (by rfl) ⟨4919904, by rfl⟩ : syracuseStep 13119745 = 9839809) B9839809
theorem B17492993 : Blo 2047435 17492993 := bstep (se 2 (by rfl) ⟨6559872, by rfl⟩ : syracuseStep 17492993 = 13119745) B13119745
theorem B11661995 : Blo 2047435 11661995 := bstep (se 1 (by rfl) ⟨8746496, by rfl⟩ : syracuseStep 11661995 = 17492993) B17492993
theorem B7774663 : Blo 2047435 7774663 := bstep (se 1 (by rfl) ⟨5830997, by rfl⟩ : syracuseStep 7774663 = 11661995) B11661995
theorem B10366217 : Blo 2047435 10366217 := bstep (se 2 (by rfl) ⟨3887331, by rfl⟩ : syracuseStep 10366217 = 7774663) B7774663
theorem B6910811 : Blo 2047435 6910811 := bstep (se 1 (by rfl) ⟨5183108, by rfl⟩ : syracuseStep 6910811 = 10366217) B10366217
theorem B4607207 : Blo 2047435 4607207 := bstep (se 1 (by rfl) ⟨3455405, by rfl⟩ : syracuseStep 4607207 = 6910811) B6910811
theorem B3071471 : Blo 2047435 3071471 := bstep (se 1 (by rfl) ⟨2303603, by rfl⟩ : syracuseStep 3071471 = 4607207) B4607207
theorem B2047647 : Blo 2047435 2047647 := bstep (se 1 (by rfl) ⟨1535735, by rfl⟩ : syracuseStep 2047647 = 3071471) B3071471
theorem B3071477 : Blo 2047435 3071477 := bbase (se 5 (by rfl) ⟨143975, by rfl⟩ : syracuseStep 3071477 = 287951) (by norm_num)
theorem B2047651 : Blo 2047435 2047651 := bstep (se 1 (by rfl) ⟨1535738, by rfl⟩ : syracuseStep 2047651 = 3071477) B3071477
theorem B2186633 : Blo 2047435 2186633 := bbase (se 2 (by rfl) ⟨819987, by rfl⟩ : syracuseStep 2186633 = 1639975) (by norm_num)
theorem B5831021 : Blo 2047435 5831021 := bstep (se 3 (by rfl) ⟨1093316, by rfl⟩ : syracuseStep 5831021 = 2186633) B2186633
theorem B3887347 : Blo 2047435 3887347 := bstep (se 1 (by rfl) ⟨2915510, by rfl⟩ : syracuseStep 3887347 = 5831021) B5831021
theorem B5183129 : Blo 2047435 5183129 := bstep (se 2 (by rfl) ⟨1943673, by rfl⟩ : syracuseStep 5183129 = 3887347) B3887347
theorem B3455419 : Blo 2047435 3455419 := bstep (se 1 (by rfl) ⟨2591564, by rfl⟩ : syracuseStep 3455419 = 5183129) B5183129
theorem B4607225 : Blo 2047435 4607225 := bstep (se 2 (by rfl) ⟨1727709, by rfl⟩ : syracuseStep 4607225 = 3455419) B3455419
theorem B3071483 : Blo 2047435 3071483 := bstep (se 1 (by rfl) ⟨2303612, by rfl⟩ : syracuseStep 3071483 = 4607225) B4607225
theorem B2047655 : Blo 2047435 2047655 := bstep (se 1 (by rfl) ⟨1535741, by rfl⟩ : syracuseStep 2047655 = 3071483) B3071483
theorem B2303617 : Blo 2047435 2303617 := bbase (se 2 (by rfl) ⟨863856, by rfl⟩ : syracuseStep 2303617 = 1727713) (by norm_num)
theorem B3071489 : Blo 2047435 3071489 := bstep (se 2 (by rfl) ⟨1151808, by rfl⟩ : syracuseStep 3071489 = 2303617) B2303617
theorem B2047659 : Blo 2047435 2047659 := bstep (se 1 (by rfl) ⟨1535744, by rfl⟩ : syracuseStep 2047659 = 3071489) B3071489
theorem B5183149 : Blo 2047435 5183149 := bbase (se 3 (by rfl) ⟨971840, by rfl⟩ : syracuseStep 5183149 = 1943681) (by norm_num)
theorem B6910865 : Blo 2047435 6910865 := bstep (se 2 (by rfl) ⟨2591574, by rfl⟩ : syracuseStep 6910865 = 5183149) B5183149
theorem B4607243 : Blo 2047435 4607243 := bstep (se 1 (by rfl) ⟨3455432, by rfl⟩ : syracuseStep 4607243 = 6910865) B6910865
theorem B3071495 : Blo 2047435 3071495 := bstep (se 1 (by rfl) ⟨2303621, by rfl⟩ : syracuseStep 3071495 = 4607243) B4607243
theorem B2047663 : Blo 2047435 2047663 := bstep (se 1 (by rfl) ⟨1535747, by rfl⟩ : syracuseStep 2047663 = 3071495) B3071495
theorem B3071501 : Blo 2047435 3071501 := bbase (se 3 (by rfl) ⟨575906, by rfl⟩ : syracuseStep 3071501 = 1151813) (by norm_num)
theorem B2047667 : Blo 2047435 2047667 := bstep (se 1 (by rfl) ⟨1535750, by rfl⟩ : syracuseStep 2047667 = 3071501) B3071501
theorem B4607261 : Blo 2047435 4607261 := bbase (se 3 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 4607261 = 1727723) (by norm_num)
theorem B3071507 : Blo 2047435 3071507 := bstep (se 1 (by rfl) ⟨2303630, by rfl⟩ : syracuseStep 3071507 = 4607261) B4607261
theorem B2047671 : Blo 2047435 2047671 := bstep (se 1 (by rfl) ⟨1535753, by rfl⟩ : syracuseStep 2047671 = 3071507) B3071507
theorem B3455453 : Blo 2047435 3455453 := bbase (se 3 (by rfl) ⟨647897, by rfl⟩ : syracuseStep 3455453 = 1295795) (by norm_num)
theorem B2303635 : Blo 2047435 2303635 := bstep (se 1 (by rfl) ⟨1727726, by rfl⟩ : syracuseStep 2303635 = 3455453) B3455453
theorem B3071513 : Blo 2047435 3071513 := bstep (se 2 (by rfl) ⟨1151817, by rfl⟩ : syracuseStep 3071513 = 2303635) B2303635
theorem B2047675 : Blo 2047435 2047675 := bstep (se 1 (by rfl) ⟨1535756, by rfl⟩ : syracuseStep 2047675 = 3071513) B3071513
theorem B4987109 : Blo 2047435 4987109 := bbase (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) (by norm_num)
theorem B3324739 : Blo 2047435 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B4432985 : Blo 2047435 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B2955323 : Blo 2047435 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B7880861 : Blo 2047435 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B5253907 : Blo 2047435 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B7005209 : Blo 2047435 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B18680557 : Blo 2047435 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B24907409 : Blo 2047435 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B16604939 : Blo 2047435 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B11069959 : Blo 2047435 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B14759945 : Blo 2047435 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B9839963 : Blo 2047435 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B6559975 : Blo 2047435 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B8746633 : Blo 2047435 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B11662177 : Blo 2047435 11662177 := bstep (se 2 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 11662177 = 8746633) B8746633
theorem B15549569 : Blo 2047435 15549569 := bstep (se 2 (by rfl) ⟨5831088, by rfl⟩ : syracuseStep 15549569 = 11662177) B11662177
theorem B10366379 : Blo 2047435 10366379 := bstep (se 1 (by rfl) ⟨7774784, by rfl⟩ : syracuseStep 10366379 = 15549569) B15549569
theorem B6910919 : Blo 2047435 6910919 := bstep (se 1 (by rfl) ⟨5183189, by rfl⟩ : syracuseStep 6910919 = 10366379) B10366379
theorem B4607279 : Blo 2047435 4607279 := bstep (se 1 (by rfl) ⟨3455459, by rfl⟩ : syracuseStep 4607279 = 6910919) B6910919
theorem B3071519 : Blo 2047435 3071519 := bstep (se 1 (by rfl) ⟨2303639, by rfl⟩ : syracuseStep 3071519 = 4607279) B4607279
theorem B2047679 : Blo 2047435 2047679 := bstep (se 1 (by rfl) ⟨1535759, by rfl⟩ : syracuseStep 2047679 = 3071519) B3071519
theorem B3071525 : Blo 2047435 3071525 := bbase (se 4 (by rfl) ⟨287955, by rfl⟩ : syracuseStep 3071525 = 575911) (by norm_num)
theorem B2047683 : Blo 2047435 2047683 := bstep (se 1 (by rfl) ⟨1535762, by rfl⟩ : syracuseStep 2047683 = 3071525) B3071525
theorem B2591605 : Blo 2047435 2591605 := bbase (se 5 (by rfl) ⟨121481, by rfl⟩ : syracuseStep 2591605 = 242963) (by norm_num)
theorem B3455473 : Blo 2047435 3455473 := bstep (se 2 (by rfl) ⟨1295802, by rfl⟩ : syracuseStep 3455473 = 2591605) B2591605
theorem B4607297 : Blo 2047435 4607297 := bstep (se 2 (by rfl) ⟨1727736, by rfl⟩ : syracuseStep 4607297 = 3455473) B3455473
theorem B3071531 : Blo 2047435 3071531 := bstep (se 1 (by rfl) ⟨2303648, by rfl⟩ : syracuseStep 3071531 = 4607297) B4607297
theorem B2047687 : Blo 2047435 2047687 := bstep (se 1 (by rfl) ⟨1535765, by rfl⟩ : syracuseStep 2047687 = 3071531) B3071531
theorem B2303653 : Blo 2047435 2303653 := bbase (se 4 (by rfl) ⟨215967, by rfl⟩ : syracuseStep 2303653 = 431935) (by norm_num)
theorem B3071537 : Blo 2047435 3071537 := bstep (se 2 (by rfl) ⟨1151826, by rfl⟩ : syracuseStep 3071537 = 2303653) B2303653
theorem B2047691 : Blo 2047435 2047691 := bstep (se 1 (by rfl) ⟨1535768, by rfl⟩ : syracuseStep 2047691 = 3071537) B3071537
theorem B2103953 : Blo 2047435 2103953 := bbase (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) (by norm_num)
theorem B5610541 : Blo 2047435 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B7480721 : Blo 2047435 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B19948589 : Blo 2047435 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B13299059 : Blo 2047435 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B8866039 : Blo 2047435 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B11821385 : Blo 2047435 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B7880923 : Blo 2047435 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B10507897 : Blo 2047435 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B56042117 : Blo 2047435 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B37361411 : Blo 2047435 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B24907607 : Blo 2047435 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B16605071 : Blo 2047435 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B11070047 : Blo 2047435 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B29520125 : Blo 2047435 29520125 := bstep (se 3 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 29520125 = 11070047) B11070047
theorem B19680083 : Blo 2047435 19680083 := bstep (se 1 (by rfl) ⟨14760062, by rfl⟩ : syracuseStep 19680083 = 29520125) B29520125
theorem B13120055 : Blo 2047435 13120055 := bstep (se 1 (by rfl) ⟨9840041, by rfl⟩ : syracuseStep 13120055 = 19680083) B19680083
theorem B8746703 : Blo 2047435 8746703 := bstep (se 1 (by rfl) ⟨6560027, by rfl⟩ : syracuseStep 8746703 = 13120055) B13120055
theorem B5831135 : Blo 2047435 5831135 := bstep (se 1 (by rfl) ⟨4373351, by rfl⟩ : syracuseStep 5831135 = 8746703) B8746703
theorem B3887423 : Blo 2047435 3887423 := bstep (se 1 (by rfl) ⟨2915567, by rfl⟩ : syracuseStep 3887423 = 5831135) B5831135
theorem B2591615 : Blo 2047435 2591615 := bstep (se 1 (by rfl) ⟨1943711, by rfl⟩ : syracuseStep 2591615 = 3887423) B3887423
theorem B6910973 : Blo 2047435 6910973 := bstep (se 3 (by rfl) ⟨1295807, by rfl⟩ : syracuseStep 6910973 = 2591615) B2591615
theorem B4607315 : Blo 2047435 4607315 := bstep (se 1 (by rfl) ⟨3455486, by rfl⟩ : syracuseStep 4607315 = 6910973) B6910973
theorem B3071543 : Blo 2047435 3071543 := bstep (se 1 (by rfl) ⟨2303657, by rfl⟩ : syracuseStep 3071543 = 4607315) B4607315
theorem B2047695 : Blo 2047435 2047695 := bstep (se 1 (by rfl) ⟨1535771, by rfl⟩ : syracuseStep 2047695 = 3071543) B3071543
theorem B3071549 : Blo 2047435 3071549 := bbase (se 3 (by rfl) ⟨575915, by rfl⟩ : syracuseStep 3071549 = 1151831) (by norm_num)
theorem B2047699 : Blo 2047435 2047699 := bstep (se 1 (by rfl) ⟨1535774, by rfl⟩ : syracuseStep 2047699 = 3071549) B3071549
theorem B4607333 : Blo 2047435 4607333 := bbase (se 4 (by rfl) ⟨431937, by rfl⟩ : syracuseStep 4607333 = 863875) (by norm_num)
theorem B3071555 : Blo 2047435 3071555 := bstep (se 1 (by rfl) ⟨2303666, by rfl⟩ : syracuseStep 3071555 = 4607333) B4607333
theorem B2047703 : Blo 2047435 2047703 := bstep (se 1 (by rfl) ⟨1535777, by rfl⟩ : syracuseStep 2047703 = 3071555) B3071555
theorem B5183261 : Blo 2047435 5183261 := bbase (se 3 (by rfl) ⟨971861, by rfl⟩ : syracuseStep 5183261 = 1943723) (by norm_num)
theorem B3455507 : Blo 2047435 3455507 := bstep (se 1 (by rfl) ⟨2591630, by rfl⟩ : syracuseStep 3455507 = 5183261) B5183261
theorem B2303671 : Blo 2047435 2303671 := bstep (se 1 (by rfl) ⟨1727753, by rfl⟩ : syracuseStep 2303671 = 3455507) B3455507
theorem B3071561 : Blo 2047435 3071561 := bstep (se 2 (by rfl) ⟨1151835, by rfl⟩ : syracuseStep 3071561 = 2303671) B2303671
theorem B2047707 : Blo 2047435 2047707 := bstep (se 1 (by rfl) ⟨1535780, by rfl⟩ : syracuseStep 2047707 = 3071561) B3071561
theorem B3887453 : Blo 2047435 3887453 := bbase (se 3 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 3887453 = 1457795) (by norm_num)
theorem B10366541 : Blo 2047435 10366541 := bstep (se 3 (by rfl) ⟨1943726, by rfl⟩ : syracuseStep 10366541 = 3887453) B3887453
theorem B6911027 : Blo 2047435 6911027 := bstep (se 1 (by rfl) ⟨5183270, by rfl⟩ : syracuseStep 6911027 = 10366541) B10366541
theorem B4607351 : Blo 2047435 4607351 := bstep (se 1 (by rfl) ⟨3455513, by rfl⟩ : syracuseStep 4607351 = 6911027) B6911027
theorem B3071567 : Blo 2047435 3071567 := bstep (se 1 (by rfl) ⟨2303675, by rfl⟩ : syracuseStep 3071567 = 4607351) B4607351
theorem B2047711 : Blo 2047435 2047711 := bstep (se 1 (by rfl) ⟨1535783, by rfl⟩ : syracuseStep 2047711 = 3071567) B3071567
theorem B3071573 : Blo 2047435 3071573 := bbase (se 8 (by rfl) ⟨17997, by rfl⟩ : syracuseStep 3071573 = 35995) (by norm_num)
theorem B2047715 : Blo 2047435 2047715 := bstep (se 1 (by rfl) ⟨1535786, by rfl⟩ : syracuseStep 2047715 = 3071573) B3071573
theorem B8746805 : Blo 2047435 8746805 := bbase (se 5 (by rfl) ⟨410006, by rfl⟩ : syracuseStep 8746805 = 820013) (by norm_num)
theorem B5831203 : Blo 2047435 5831203 := bstep (se 1 (by rfl) ⟨4373402, by rfl⟩ : syracuseStep 5831203 = 8746805) B8746805
theorem B7774937 : Blo 2047435 7774937 := bstep (se 2 (by rfl) ⟨2915601, by rfl⟩ : syracuseStep 7774937 = 5831203) B5831203
theorem B5183291 : Blo 2047435 5183291 := bstep (se 1 (by rfl) ⟨3887468, by rfl⟩ : syracuseStep 5183291 = 7774937) B7774937
theorem B3455527 : Blo 2047435 3455527 := bstep (se 1 (by rfl) ⟨2591645, by rfl⟩ : syracuseStep 3455527 = 5183291) B5183291
theorem B4607369 : Blo 2047435 4607369 := bstep (se 2 (by rfl) ⟨1727763, by rfl⟩ : syracuseStep 4607369 = 3455527) B3455527
theorem B3071579 : Blo 2047435 3071579 := bstep (se 1 (by rfl) ⟨2303684, by rfl⟩ : syracuseStep 3071579 = 4607369) B4607369
theorem B2047719 : Blo 2047435 2047719 := bstep (se 1 (by rfl) ⟨1535789, by rfl⟩ : syracuseStep 2047719 = 3071579) B3071579
theorem B2303689 : Blo 2047435 2303689 := bbase (se 2 (by rfl) ⟨863883, by rfl⟩ : syracuseStep 2303689 = 1727767) (by norm_num)
theorem B3071585 : Blo 2047435 3071585 := bstep (se 2 (by rfl) ⟨1151844, by rfl⟩ : syracuseStep 3071585 = 2303689) B2303689
theorem B2047723 : Blo 2047435 2047723 := bstep (se 1 (by rfl) ⟨1535792, by rfl⟩ : syracuseStep 2047723 = 3071585) B3071585
theorem B4151333 : Blo 2047435 4151333 := bbase (se 4 (by rfl) ⟨389187, by rfl⟩ : syracuseStep 4151333 = 778375) (by norm_num)
theorem B2767555 : Blo 2047435 2767555 := bstep (se 1 (by rfl) ⟨2075666, by rfl⟩ : syracuseStep 2767555 = 4151333) B4151333
theorem B3690073 : Blo 2047435 3690073 := bstep (se 2 (by rfl) ⟨1383777, by rfl⟩ : syracuseStep 3690073 = 2767555) B2767555
theorem B4920097 : Blo 2047435 4920097 := bstep (se 2 (by rfl) ⟨1845036, by rfl⟩ : syracuseStep 4920097 = 3690073) B3690073
theorem B6560129 : Blo 2047435 6560129 := bstep (se 2 (by rfl) ⟨2460048, by rfl⟩ : syracuseStep 6560129 = 4920097) B4920097
theorem B17493677 : Blo 2047435 17493677 := bstep (se 3 (by rfl) ⟨3280064, by rfl⟩ : syracuseStep 17493677 = 6560129) B6560129
theorem B11662451 : Blo 2047435 11662451 := bstep (se 1 (by rfl) ⟨8746838, by rfl⟩ : syracuseStep 11662451 = 17493677) B17493677
theorem B7774967 : Blo 2047435 7774967 := bstep (se 1 (by rfl) ⟨5831225, by rfl⟩ : syracuseStep 7774967 = 11662451) B11662451
theorem B5183311 : Blo 2047435 5183311 := bstep (se 1 (by rfl) ⟨3887483, by rfl⟩ : syracuseStep 5183311 = 7774967) B7774967
theorem B6911081 : Blo 2047435 6911081 := bstep (se 2 (by rfl) ⟨2591655, by rfl⟩ : syracuseStep 6911081 = 5183311) B5183311
theorem B4607387 : Blo 2047435 4607387 := bstep (se 1 (by rfl) ⟨3455540, by rfl⟩ : syracuseStep 4607387 = 6911081) B6911081
theorem B3071591 : Blo 2047435 3071591 := bstep (se 1 (by rfl) ⟨2303693, by rfl⟩ : syracuseStep 3071591 = 4607387) B4607387
theorem B2047727 : Blo 2047435 2047727 := bstep (se 1 (by rfl) ⟨1535795, by rfl⟩ : syracuseStep 2047727 = 3071591) B3071591
theorem B3071597 : Blo 2047435 3071597 := bbase (se 3 (by rfl) ⟨575924, by rfl⟩ : syracuseStep 3071597 = 1151849) (by norm_num)
theorem B2047731 : Blo 2047435 2047731 := bstep (se 1 (by rfl) ⟨1535798, by rfl⟩ : syracuseStep 2047731 = 3071597) B3071597
theorem B4607405 : Blo 2047435 4607405 := bbase (se 3 (by rfl) ⟨863888, by rfl⟩ : syracuseStep 4607405 = 1727777) (by norm_num)
theorem B3071603 : Blo 2047435 3071603 := bstep (se 1 (by rfl) ⟨2303702, by rfl⟩ : syracuseStep 3071603 = 4607405) B4607405
theorem B2047735 : Blo 2047435 2047735 := bstep (se 1 (by rfl) ⟨1535801, by rfl⟩ : syracuseStep 2047735 = 3071603) B3071603
theorem B3280085 : Blo 2047435 3280085 := bbase (se 7 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 3280085 = 76877) (by norm_num)
theorem B2186723 : Blo 2047435 2186723 := bstep (se 1 (by rfl) ⟨1640042, by rfl⟩ : syracuseStep 2186723 = 3280085) B3280085
theorem B5831261 : Blo 2047435 5831261 := bstep (se 3 (by rfl) ⟨1093361, by rfl⟩ : syracuseStep 5831261 = 2186723) B2186723
theorem B3887507 : Blo 2047435 3887507 := bstep (se 1 (by rfl) ⟨2915630, by rfl⟩ : syracuseStep 3887507 = 5831261) B5831261
theorem B2591671 : Blo 2047435 2591671 := bstep (se 1 (by rfl) ⟨1943753, by rfl⟩ : syracuseStep 2591671 = 3887507) B3887507
theorem B3455561 : Blo 2047435 3455561 := bstep (se 2 (by rfl) ⟨1295835, by rfl⟩ : syracuseStep 3455561 = 2591671) B2591671
theorem B2303707 : Blo 2047435 2303707 := bstep (se 1 (by rfl) ⟨1727780, by rfl⟩ : syracuseStep 2303707 = 3455561) B3455561
theorem B3071609 : Blo 2047435 3071609 := bstep (se 2 (by rfl) ⟨1151853, by rfl⟩ : syracuseStep 3071609 = 2303707) B2303707
theorem B2047739 : Blo 2047435 2047739 := bstep (se 1 (by rfl) ⟨1535804, by rfl⟩ : syracuseStep 2047739 = 3071609) B3071609
theorem B3370205 : Blo 2047435 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B8987213 : Blo 2047435 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B5991475 : Blo 2047435 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B7988633 : Blo 2047435 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B5325755 : Blo 2047435 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B14202013 : Blo 2047435 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B18936017 : Blo 2047435 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B12624011 : Blo 2047435 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B8416007 : Blo 2047435 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B5610671 : Blo 2047435 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B3740447 : Blo 2047435 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B2493631 : Blo 2047435 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B13299365 : Blo 2047435 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B35464973 : Blo 2047435 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B94573261 : Blo 2047435 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B126097681 : Blo 2047435 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B168130241 : Blo 2047435 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B112086827 : Blo 2047435 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B74724551 : Blo 2047435 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B49816367 : Blo 2047435 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B33210911 : Blo 2047435 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B88562429 : Blo 2047435 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B59041619 : Blo 2047435 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B39361079 : Blo 2047435 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B26240719 : Blo 2047435 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B34987625 : Blo 2047435 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B23325083 : Blo 2047435 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B15550055 : Blo 2047435 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B10366703 : Blo 2047435 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B6911135 : Blo 2047435 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B4607423 : Blo 2047435 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B3071615 : Blo 2047435 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B2047743 : Blo 2047435 2047743 := bstep (se 1 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 2047743 = 3071615) B3071615
theorem B3071621 : Blo 2047435 3071621 := bbase (se 4 (by rfl) ⟨287964, by rfl⟩ : syracuseStep 3071621 = 575929) (by norm_num)
theorem B2047747 : Blo 2047435 2047747 := bstep (se 1 (by rfl) ⟨1535810, by rfl⟩ : syracuseStep 2047747 = 3071621) B3071621
theorem B3455581 : Blo 2047435 3455581 := bbase (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) (by norm_num)
theorem B4607441 : Blo 2047435 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B3071627 : Blo 2047435 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B2047751 : Blo 2047435 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B2303725 : Blo 2047435 2303725 := bbase (se 3 (by rfl) ⟨431948, by rfl⟩ : syracuseStep 2303725 = 863897) (by norm_num)
theorem B3071633 : Blo 2047435 3071633 := bstep (se 2 (by rfl) ⟨1151862, by rfl⟩ : syracuseStep 3071633 = 2303725) B2303725
theorem B2047755 : Blo 2047435 2047755 := bstep (se 1 (by rfl) ⟨1535816, by rfl⟩ : syracuseStep 2047755 = 3071633) B3071633
theorem B6911189 : Blo 2047435 6911189 := bbase (se 7 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 6911189 = 161981) (by norm_num)
theorem B4607459 : Blo 2047435 4607459 := bstep (se 1 (by rfl) ⟨3455594, by rfl⟩ : syracuseStep 4607459 = 6911189) B6911189
theorem B3071639 : Blo 2047435 3071639 := bstep (se 1 (by rfl) ⟨2303729, by rfl⟩ : syracuseStep 3071639 = 4607459) B4607459
theorem B2047759 : Blo 2047435 2047759 := bstep (se 1 (by rfl) ⟨1535819, by rfl⟩ : syracuseStep 2047759 = 3071639) B3071639
theorem B3071645 : Blo 2047435 3071645 := bbase (se 3 (by rfl) ⟨575933, by rfl⟩ : syracuseStep 3071645 = 1151867) (by norm_num)
theorem B2047763 : Blo 2047435 2047763 := bstep (se 1 (by rfl) ⟨1535822, by rfl⟩ : syracuseStep 2047763 = 3071645) B3071645
theorem B4607477 : Blo 2047435 4607477 := bbase (se 5 (by rfl) ⟨215975, by rfl⟩ : syracuseStep 4607477 = 431951) (by norm_num)
theorem B3071651 : Blo 2047435 3071651 := bstep (se 1 (by rfl) ⟨2303738, by rfl⟩ : syracuseStep 3071651 = 4607477) B4607477
theorem B2047767 : Blo 2047435 2047767 := bstep (se 1 (by rfl) ⟨1535825, by rfl⟩ : syracuseStep 2047767 = 3071651) B3071651
theorem B2699245 : Blo 2047435 2699245 := bbase (se 3 (by rfl) ⟨506108, by rfl⟩ : syracuseStep 2699245 = 1012217) (by norm_num)
theorem B14395973 : Blo 2047435 14395973 := bstep (se 4 (by rfl) ⟨1349622, by rfl⟩ : syracuseStep 14395973 = 2699245) B2699245
theorem B38389261 : Blo 2047435 38389261 := bstep (se 3 (by rfl) ⟨7197986, by rfl⟩ : syracuseStep 38389261 = 14395973) B14395973
theorem B51185681 : Blo 2047435 51185681 := bstep (se 2 (by rfl) ⟨19194630, by rfl⟩ : syracuseStep 51185681 = 38389261) B38389261
theorem B34123787 : Blo 2047435 34123787 := bstep (se 1 (by rfl) ⟨25592840, by rfl⟩ : syracuseStep 34123787 = 51185681) B51185681
theorem B22749191 : Blo 2047435 22749191 := bstep (se 1 (by rfl) ⟨17061893, by rfl⟩ : syracuseStep 22749191 = 34123787) B34123787
theorem B15166127 : Blo 2047435 15166127 := bstep (se 1 (by rfl) ⟨11374595, by rfl⟩ : syracuseStep 15166127 = 22749191) B22749191
theorem B40443005 : Blo 2047435 40443005 := bstep (se 3 (by rfl) ⟨7583063, by rfl⟩ : syracuseStep 40443005 = 15166127) B15166127
theorem B26962003 : Blo 2047435 26962003 := bstep (se 1 (by rfl) ⟨20221502, by rfl⟩ : syracuseStep 26962003 = 40443005) B40443005
theorem B143797349 : Blo 2047435 143797349 := bstep (se 4 (by rfl) ⟨13481001, by rfl⟩ : syracuseStep 143797349 = 26962003) B26962003
theorem B95864899 : Blo 2047435 95864899 := bstep (se 1 (by rfl) ⟨71898674, by rfl⟩ : syracuseStep 95864899 = 143797349) B143797349
theorem B127819865 : Blo 2047435 127819865 := bstep (se 2 (by rfl) ⟨47932449, by rfl⟩ : syracuseStep 127819865 = 95864899) B95864899
theorem B85213243 : Blo 2047435 85213243 := bstep (se 1 (by rfl) ⟨63909932, by rfl⟩ : syracuseStep 85213243 = 127819865) B127819865
theorem B113617657 : Blo 2047435 113617657 := bstep (se 2 (by rfl) ⟨42606621, by rfl⟩ : syracuseStep 113617657 = 85213243) B85213243
theorem B605960837 : Blo 2047435 605960837 := bstep (se 4 (by rfl) ⟨56808828, by rfl⟩ : syracuseStep 605960837 = 113617657) B113617657
theorem B403973891 : Blo 2047435 403973891 := bstep (se 1 (by rfl) ⟨302980418, by rfl⟩ : syracuseStep 403973891 = 605960837) B605960837
theorem B269315927 : Blo 2047435 269315927 := bstep (se 1 (by rfl) ⟨201986945, by rfl⟩ : syracuseStep 269315927 = 403973891) B403973891
theorem B179543951 : Blo 2047435 179543951 := bstep (se 1 (by rfl) ⟨134657963, by rfl⟩ : syracuseStep 179543951 = 269315927) B269315927
theorem B119695967 : Blo 2047435 119695967 := bstep (se 1 (by rfl) ⟨89771975, by rfl⟩ : syracuseStep 119695967 = 179543951) B179543951
theorem B79797311 : Blo 2047435 79797311 := bstep (se 1 (by rfl) ⟨59847983, by rfl⟩ : syracuseStep 79797311 = 119695967) B119695967
theorem B53198207 : Blo 2047435 53198207 := bstep (se 1 (by rfl) ⟨39898655, by rfl⟩ : syracuseStep 53198207 = 79797311) B79797311
theorem B35465471 : Blo 2047435 35465471 := bstep (se 1 (by rfl) ⟨26599103, by rfl⟩ : syracuseStep 35465471 = 53198207) B53198207
theorem B23643647 : Blo 2047435 23643647 := bstep (se 1 (by rfl) ⟨17732735, by rfl⟩ : syracuseStep 23643647 = 35465471) B35465471
theorem B15762431 : Blo 2047435 15762431 := bstep (se 1 (by rfl) ⟨11821823, by rfl⟩ : syracuseStep 15762431 = 23643647) B23643647
theorem B10508287 : Blo 2047435 10508287 := bstep (se 1 (by rfl) ⟨7881215, by rfl⟩ : syracuseStep 10508287 = 15762431) B15762431
theorem B14011049 : Blo 2047435 14011049 := bstep (se 2 (by rfl) ⟨5254143, by rfl⟩ : syracuseStep 14011049 = 10508287) B10508287
theorem B9340699 : Blo 2047435 9340699 := bstep (se 1 (by rfl) ⟨7005524, by rfl⟩ : syracuseStep 9340699 = 14011049) B14011049
theorem B12454265 : Blo 2047435 12454265 := bstep (se 2 (by rfl) ⟨4670349, by rfl⟩ : syracuseStep 12454265 = 9340699) B9340699
theorem B8302843 : Blo 2047435 8302843 := bstep (se 1 (by rfl) ⟨6227132, by rfl⟩ : syracuseStep 8302843 = 12454265) B12454265
theorem B44281829 : Blo 2047435 44281829 := bstep (se 4 (by rfl) ⟨4151421, by rfl⟩ : syracuseStep 44281829 = 8302843) B8302843
theorem B29521219 : Blo 2047435 29521219 := bstep (se 1 (by rfl) ⟨22140914, by rfl⟩ : syracuseStep 29521219 = 44281829) B44281829
theorem B39361625 : Blo 2047435 39361625 := bstep (se 2 (by rfl) ⟨14760609, by rfl⟩ : syracuseStep 39361625 = 29521219) B29521219
theorem B26241083 : Blo 2047435 26241083 := bstep (se 1 (by rfl) ⟨19680812, by rfl⟩ : syracuseStep 26241083 = 39361625) B39361625
theorem B17494055 : Blo 2047435 17494055 := bstep (se 1 (by rfl) ⟨13120541, by rfl⟩ : syracuseStep 17494055 = 26241083) B26241083
theorem B11662703 : Blo 2047435 11662703 := bstep (se 1 (by rfl) ⟨8747027, by rfl⟩ : syracuseStep 11662703 = 17494055) B17494055
theorem B7775135 : Blo 2047435 7775135 := bstep (se 1 (by rfl) ⟨5831351, by rfl⟩ : syracuseStep 7775135 = 11662703) B11662703
theorem B5183423 : Blo 2047435 5183423 := bstep (se 1 (by rfl) ⟨3887567, by rfl⟩ : syracuseStep 5183423 = 7775135) B7775135
theorem B3455615 : Blo 2047435 3455615 := bstep (se 1 (by rfl) ⟨2591711, by rfl⟩ : syracuseStep 3455615 = 5183423) B5183423
theorem B2303743 : Blo 2047435 2303743 := bstep (se 1 (by rfl) ⟨1727807, by rfl⟩ : syracuseStep 2303743 = 3455615) B3455615
theorem B3071657 : Blo 2047435 3071657 := bstep (se 2 (by rfl) ⟨1151871, by rfl⟩ : syracuseStep 3071657 = 2303743) B2303743
theorem B2047771 : Blo 2047435 2047771 := bstep (se 1 (by rfl) ⟨1535828, by rfl⟩ : syracuseStep 2047771 = 3071657) B3071657
theorem B2186761 : Blo 2047435 2186761 := bbase (se 2 (by rfl) ⟨820035, by rfl⟩ : syracuseStep 2186761 = 1640071) (by norm_num)
theorem B2915681 : Blo 2047435 2915681 := bstep (se 2 (by rfl) ⟨1093380, by rfl⟩ : syracuseStep 2915681 = 2186761) B2186761
theorem B7775149 : Blo 2047435 7775149 := bstep (se 3 (by rfl) ⟨1457840, by rfl⟩ : syracuseStep 7775149 = 2915681) B2915681
theorem B10366865 : Blo 2047435 10366865 := bstep (se 2 (by rfl) ⟨3887574, by rfl⟩ : syracuseStep 10366865 = 7775149) B7775149
theorem B6911243 : Blo 2047435 6911243 := bstep (se 1 (by rfl) ⟨5183432, by rfl⟩ : syracuseStep 6911243 = 10366865) B10366865
theorem B4607495 : Blo 2047435 4607495 := bstep (se 1 (by rfl) ⟨3455621, by rfl⟩ : syracuseStep 4607495 = 6911243) B6911243
theorem B3071663 : Blo 2047435 3071663 := bstep (se 1 (by rfl) ⟨2303747, by rfl⟩ : syracuseStep 3071663 = 4607495) B4607495
theorem B2047775 : Blo 2047435 2047775 := bstep (se 1 (by rfl) ⟨1535831, by rfl⟩ : syracuseStep 2047775 = 3071663) B3071663
theorem B3071669 : Blo 2047435 3071669 := bbase (se 5 (by rfl) ⟨143984, by rfl⟩ : syracuseStep 3071669 = 287969) (by norm_num)
theorem B2047779 : Blo 2047435 2047779 := bstep (se 1 (by rfl) ⟨1535834, by rfl⟩ : syracuseStep 2047779 = 3071669) B3071669
theorem B5183453 : Blo 2047435 5183453 := bbase (se 3 (by rfl) ⟨971897, by rfl⟩ : syracuseStep 5183453 = 1943795) (by norm_num)
theorem B3455635 : Blo 2047435 3455635 := bstep (se 1 (by rfl) ⟨2591726, by rfl⟩ : syracuseStep 3455635 = 5183453) B5183453
theorem B4607513 : Blo 2047435 4607513 := bstep (se 2 (by rfl) ⟨1727817, by rfl⟩ : syracuseStep 4607513 = 3455635) B3455635
theorem B3071675 : Blo 2047435 3071675 := bstep (se 1 (by rfl) ⟨2303756, by rfl⟩ : syracuseStep 3071675 = 4607513) B4607513
theorem B2047783 : Blo 2047435 2047783 := bstep (se 1 (by rfl) ⟨1535837, by rfl⟩ : syracuseStep 2047783 = 3071675) B3071675
theorem B2303761 : Blo 2047435 2303761 := bbase (se 2 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 2303761 = 1727821) (by norm_num)
theorem B3071681 : Blo 2047435 3071681 := bstep (se 2 (by rfl) ⟨1151880, by rfl⟩ : syracuseStep 3071681 = 2303761) B2303761
theorem B2047787 : Blo 2047435 2047787 := bstep (se 1 (by rfl) ⟨1535840, by rfl⟩ : syracuseStep 2047787 = 3071681) B3071681
theorem B3887605 : Blo 2047435 3887605 := bbase (se 5 (by rfl) ⟨182231, by rfl⟩ : syracuseStep 3887605 = 364463) (by norm_num)
theorem B5183473 : Blo 2047435 5183473 := bstep (se 2 (by rfl) ⟨1943802, by rfl⟩ : syracuseStep 5183473 = 3887605) B3887605
theorem B6911297 : Blo 2047435 6911297 := bstep (se 2 (by rfl) ⟨2591736, by rfl⟩ : syracuseStep 6911297 = 5183473) B5183473
theorem B4607531 : Blo 2047435 4607531 := bstep (se 1 (by rfl) ⟨3455648, by rfl⟩ : syracuseStep 4607531 = 6911297) B6911297
theorem B3071687 : Blo 2047435 3071687 := bstep (se 1 (by rfl) ⟨2303765, by rfl⟩ : syracuseStep 3071687 = 4607531) B4607531
theorem B2047791 : Blo 2047435 2047791 := bstep (se 1 (by rfl) ⟨1535843, by rfl⟩ : syracuseStep 2047791 = 3071687) B3071687
theorem B3071693 : Blo 2047435 3071693 := bbase (se 3 (by rfl) ⟨575942, by rfl⟩ : syracuseStep 3071693 = 1151885) (by norm_num)
theorem B2047795 : Blo 2047435 2047795 := bstep (se 1 (by rfl) ⟨1535846, by rfl⟩ : syracuseStep 2047795 = 3071693) B3071693
theorem B4607549 : Blo 2047435 4607549 := bbase (se 3 (by rfl) ⟨863915, by rfl⟩ : syracuseStep 4607549 = 1727831) (by norm_num)
theorem B3071699 : Blo 2047435 3071699 := bstep (se 1 (by rfl) ⟨2303774, by rfl⟩ : syracuseStep 3071699 = 4607549) B4607549
theorem B2047799 : Blo 2047435 2047799 := bstep (se 1 (by rfl) ⟨1535849, by rfl⟩ : syracuseStep 2047799 = 3071699) B3071699
theorem B3455669 : Blo 2047435 3455669 := bbase (se 5 (by rfl) ⟨161984, by rfl⟩ : syracuseStep 3455669 = 323969) (by norm_num)
theorem B2303779 : Blo 2047435 2303779 := bstep (se 1 (by rfl) ⟨1727834, by rfl⟩ : syracuseStep 2303779 = 3455669) B3455669
theorem B3071705 : Blo 2047435 3071705 := bstep (se 2 (by rfl) ⟨1151889, by rfl⟩ : syracuseStep 3071705 = 2303779) B2303779
theorem B2047803 : Blo 2047435 2047803 := bstep (se 1 (by rfl) ⟨1535852, by rfl⟩ : syracuseStep 2047803 = 3071705) B3071705
theorem B2460145 : Blo 2047435 2460145 := bbase (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) (by norm_num)
theorem B3280193 : Blo 2047435 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B2186795 : Blo 2047435 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B5831453 : Blo 2047435 5831453 := bstep (se 3 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 5831453 = 2186795) B2186795
theorem B15550541 : Blo 2047435 15550541 := bstep (se 3 (by rfl) ⟨2915726, by rfl⟩ : syracuseStep 15550541 = 5831453) B5831453
theorem B10367027 : Blo 2047435 10367027 := bstep (se 1 (by rfl) ⟨7775270, by rfl⟩ : syracuseStep 10367027 = 15550541) B15550541
theorem B6911351 : Blo 2047435 6911351 := bstep (se 1 (by rfl) ⟨5183513, by rfl⟩ : syracuseStep 6911351 = 10367027) B10367027
theorem B4607567 : Blo 2047435 4607567 := bstep (se 1 (by rfl) ⟨3455675, by rfl⟩ : syracuseStep 4607567 = 6911351) B6911351
theorem B3071711 : Blo 2047435 3071711 := bstep (se 1 (by rfl) ⟨2303783, by rfl⟩ : syracuseStep 3071711 = 4607567) B4607567
theorem B2047807 : Blo 2047435 2047807 := bstep (se 1 (by rfl) ⟨1535855, by rfl⟩ : syracuseStep 2047807 = 3071711) B3071711
theorem B3071717 : Blo 2047435 3071717 := bbase (se 4 (by rfl) ⟨287973, by rfl⟩ : syracuseStep 3071717 = 575947) (by norm_num)
theorem B2047811 : Blo 2047435 2047811 := bstep (se 1 (by rfl) ⟨1535858, by rfl⟩ : syracuseStep 2047811 = 3071717) B3071717
theorem B5831477 : Blo 2047435 5831477 := bbase (se 5 (by rfl) ⟨273350, by rfl⟩ : syracuseStep 5831477 = 546701) (by norm_num)
theorem B3887651 : Blo 2047435 3887651 := bstep (se 1 (by rfl) ⟨2915738, by rfl⟩ : syracuseStep 3887651 = 5831477) B5831477
theorem B2591767 : Blo 2047435 2591767 := bstep (se 1 (by rfl) ⟨1943825, by rfl⟩ : syracuseStep 2591767 = 3887651) B3887651
theorem B3455689 : Blo 2047435 3455689 := bstep (se 2 (by rfl) ⟨1295883, by rfl⟩ : syracuseStep 3455689 = 2591767) B2591767
theorem B4607585 : Blo 2047435 4607585 := bstep (se 2 (by rfl) ⟨1727844, by rfl⟩ : syracuseStep 4607585 = 3455689) B3455689
theorem B3071723 : Blo 2047435 3071723 := bstep (se 1 (by rfl) ⟨2303792, by rfl⟩ : syracuseStep 3071723 = 4607585) B4607585
theorem B2047815 : Blo 2047435 2047815 := bstep (se 1 (by rfl) ⟨1535861, by rfl⟩ : syracuseStep 2047815 = 3071723) B3071723
theorem B2303797 : Blo 2047435 2303797 := bbase (se 5 (by rfl) ⟨107990, by rfl⟩ : syracuseStep 2303797 = 215981) (by norm_num)
theorem B3071729 : Blo 2047435 3071729 := bstep (se 2 (by rfl) ⟨1151898, by rfl⟩ : syracuseStep 3071729 = 2303797) B2303797
theorem B2047819 : Blo 2047435 2047819 := bstep (se 1 (by rfl) ⟨1535864, by rfl⟩ : syracuseStep 2047819 = 3071729) B3071729
theorem B2591777 : Blo 2047435 2591777 := bbase (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) (by norm_num)
theorem B6911405 : Blo 2047435 6911405 := bstep (se 3 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 6911405 = 2591777) B2591777
theorem B4607603 : Blo 2047435 4607603 := bstep (se 1 (by rfl) ⟨3455702, by rfl⟩ : syracuseStep 4607603 = 6911405) B6911405
theorem B3071735 : Blo 2047435 3071735 := bstep (se 1 (by rfl) ⟨2303801, by rfl⟩ : syracuseStep 3071735 = 4607603) B4607603
theorem B2047823 : Blo 2047435 2047823 := bstep (se 1 (by rfl) ⟨1535867, by rfl⟩ : syracuseStep 2047823 = 3071735) B3071735
theorem B3071741 : Blo 2047435 3071741 := bbase (se 3 (by rfl) ⟨575951, by rfl⟩ : syracuseStep 3071741 = 1151903) (by norm_num)
theorem B2047827 : Blo 2047435 2047827 := bstep (se 1 (by rfl) ⟨1535870, by rfl⟩ : syracuseStep 2047827 = 3071741) B3071741
theorem B4607621 : Blo 2047435 4607621 := bbase (se 4 (by rfl) ⟨431964, by rfl⟩ : syracuseStep 4607621 = 863929) (by norm_num)
theorem B3071747 : Blo 2047435 3071747 := bstep (se 1 (by rfl) ⟨2303810, by rfl⟩ : syracuseStep 3071747 = 4607621) B4607621
theorem B2047831 : Blo 2047435 2047831 := bstep (se 1 (by rfl) ⟨1535873, by rfl⟩ : syracuseStep 2047831 = 3071747) B3071747
theorem B3690269 : Blo 2047435 3690269 := bbase (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) (by norm_num)
theorem B2460179 : Blo 2047435 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B6560477 : Blo 2047435 6560477 := bstep (se 3 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 6560477 = 2460179) B2460179
theorem B4373651 : Blo 2047435 4373651 := bstep (se 1 (by rfl) ⟨3280238, by rfl⟩ : syracuseStep 4373651 = 6560477) B6560477
theorem B2915767 : Blo 2047435 2915767 := bstep (se 1 (by rfl) ⟨2186825, by rfl⟩ : syracuseStep 2915767 = 4373651) B4373651
theorem B3887689 : Blo 2047435 3887689 := bstep (se 2 (by rfl) ⟨1457883, by rfl⟩ : syracuseStep 3887689 = 2915767) B2915767
theorem B5183585 : Blo 2047435 5183585 := bstep (se 2 (by rfl) ⟨1943844, by rfl⟩ : syracuseStep 5183585 = 3887689) B3887689
theorem B3455723 : Blo 2047435 3455723 := bstep (se 1 (by rfl) ⟨2591792, by rfl⟩ : syracuseStep 3455723 = 5183585) B5183585
theorem B2303815 : Blo 2047435 2303815 := bstep (se 1 (by rfl) ⟨1727861, by rfl⟩ : syracuseStep 2303815 = 3455723) B3455723
theorem B3071753 : Blo 2047435 3071753 := bstep (se 2 (by rfl) ⟨1151907, by rfl⟩ : syracuseStep 3071753 = 2303815) B2303815
theorem B2047835 : Blo 2047435 2047835 := bstep (se 1 (by rfl) ⟨1535876, by rfl⟩ : syracuseStep 2047835 = 3071753) B3071753
theorem B10367189 : Blo 2047435 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B6911459 : Blo 2047435 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B4607639 : Blo 2047435 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B3071759 : Blo 2047435 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B2047839 : Blo 2047435 2047839 := bstep (se 1 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 2047839 = 3071759) B3071759
theorem B3071765 : Blo 2047435 3071765 := bbase (se 6 (by rfl) ⟨71994, by rfl⟩ : syracuseStep 3071765 = 143989) (by norm_num)
theorem B2047843 : Blo 2047435 2047843 := bstep (se 1 (by rfl) ⟨1535882, by rfl⟩ : syracuseStep 2047843 = 3071765) B3071765
theorem B9341045 : Blo 2047435 9341045 := bbase (se 5 (by rfl) ⟨437861, by rfl⟩ : syracuseStep 9341045 = 875723) (by norm_num)
theorem B6227363 : Blo 2047435 6227363 := bstep (se 1 (by rfl) ⟨4670522, by rfl⟩ : syracuseStep 6227363 = 9341045) B9341045
theorem B16606301 : Blo 2047435 16606301 := bstep (se 3 (by rfl) ⟨3113681, by rfl⟩ : syracuseStep 16606301 = 6227363) B6227363
theorem B44283469 : Blo 2047435 44283469 := bstep (se 3 (by rfl) ⟨8303150, by rfl⟩ : syracuseStep 44283469 = 16606301) B16606301
theorem B59044625 : Blo 2047435 59044625 := bstep (se 2 (by rfl) ⟨22141734, by rfl⟩ : syracuseStep 59044625 = 44283469) B44283469
theorem B39363083 : Blo 2047435 39363083 := bstep (se 1 (by rfl) ⟨29522312, by rfl⟩ : syracuseStep 39363083 = 59044625) B59044625
theorem B26242055 : Blo 2047435 26242055 := bstep (se 1 (by rfl) ⟨19681541, by rfl⟩ : syracuseStep 26242055 = 39363083) B39363083
theorem B17494703 : Blo 2047435 17494703 := bstep (se 1 (by rfl) ⟨13121027, by rfl⟩ : syracuseStep 17494703 = 26242055) B26242055
theorem B11663135 : Blo 2047435 11663135 := bstep (se 1 (by rfl) ⟨8747351, by rfl⟩ : syracuseStep 11663135 = 17494703) B17494703
theorem B7775423 : Blo 2047435 7775423 := bstep (se 1 (by rfl) ⟨5831567, by rfl⟩ : syracuseStep 7775423 = 11663135) B11663135
theorem B5183615 : Blo 2047435 5183615 := bstep (se 1 (by rfl) ⟨3887711, by rfl⟩ : syracuseStep 5183615 = 7775423) B7775423
theorem B3455743 : Blo 2047435 3455743 := bstep (se 1 (by rfl) ⟨2591807, by rfl⟩ : syracuseStep 3455743 = 5183615) B5183615
theorem B4607657 : Blo 2047435 4607657 := bstep (se 2 (by rfl) ⟨1727871, by rfl⟩ : syracuseStep 4607657 = 3455743) B3455743
theorem B3071771 : Blo 2047435 3071771 := bstep (se 1 (by rfl) ⟨2303828, by rfl⟩ : syracuseStep 3071771 = 4607657) B4607657
theorem B2047847 : Blo 2047435 2047847 := bstep (se 1 (by rfl) ⟨1535885, by rfl⟩ : syracuseStep 2047847 = 3071771) B3071771
theorem B2303833 : Blo 2047435 2303833 := bbase (se 2 (by rfl) ⟨863937, by rfl⟩ : syracuseStep 2303833 = 1727875) (by norm_num)
theorem B3071777 : Blo 2047435 3071777 := bstep (se 2 (by rfl) ⟨1151916, by rfl⟩ : syracuseStep 3071777 = 2303833) B2303833
theorem B2047851 : Blo 2047435 2047851 := bstep (se 1 (by rfl) ⟨1535888, by rfl⟩ : syracuseStep 2047851 = 3071777) B3071777
theorem B4373693 : Blo 2047435 4373693 := bbase (se 3 (by rfl) ⟨820067, by rfl⟩ : syracuseStep 4373693 = 1640135) (by norm_num)
theorem B2915795 : Blo 2047435 2915795 := bstep (se 1 (by rfl) ⟨2186846, by rfl⟩ : syracuseStep 2915795 = 4373693) B4373693
theorem B7775453 : Blo 2047435 7775453 := bstep (se 3 (by rfl) ⟨1457897, by rfl⟩ : syracuseStep 7775453 = 2915795) B2915795
theorem B5183635 : Blo 2047435 5183635 := bstep (se 1 (by rfl) ⟨3887726, by rfl⟩ : syracuseStep 5183635 = 7775453) B7775453
theorem B6911513 : Blo 2047435 6911513 := bstep (se 2 (by rfl) ⟨2591817, by rfl⟩ : syracuseStep 6911513 = 5183635) B5183635
theorem B4607675 : Blo 2047435 4607675 := bstep (se 1 (by rfl) ⟨3455756, by rfl⟩ : syracuseStep 4607675 = 6911513) B6911513
theorem B3071783 : Blo 2047435 3071783 := bstep (se 1 (by rfl) ⟨2303837, by rfl⟩ : syracuseStep 3071783 = 4607675) B4607675
theorem B2047855 : Blo 2047435 2047855 := bstep (se 1 (by rfl) ⟨1535891, by rfl⟩ : syracuseStep 2047855 = 3071783) B3071783
theorem B3071789 : Blo 2047435 3071789 := bbase (se 3 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 3071789 = 1151921) (by norm_num)
theorem B2047859 : Blo 2047435 2047859 := bstep (se 1 (by rfl) ⟨1535894, by rfl⟩ : syracuseStep 2047859 = 3071789) B3071789
theorem B4607693 : Blo 2047435 4607693 := bbase (se 3 (by rfl) ⟨863942, by rfl⟩ : syracuseStep 4607693 = 1727885) (by norm_num)
theorem B3071795 : Blo 2047435 3071795 := bstep (se 1 (by rfl) ⟨2303846, by rfl⟩ : syracuseStep 3071795 = 4607693) B4607693
theorem B2047863 : Blo 2047435 2047863 := bstep (se 1 (by rfl) ⟨1535897, by rfl⟩ : syracuseStep 2047863 = 3071795) B3071795
theorem B2591833 : Blo 2047435 2591833 := bbase (se 2 (by rfl) ⟨971937, by rfl⟩ : syracuseStep 2591833 = 1943875) (by norm_num)
theorem B3455777 : Blo 2047435 3455777 := bstep (se 2 (by rfl) ⟨1295916, by rfl⟩ : syracuseStep 3455777 = 2591833) B2591833
theorem B2303851 : Blo 2047435 2303851 := bstep (se 1 (by rfl) ⟨1727888, by rfl⟩ : syracuseStep 2303851 = 3455777) B3455777
theorem B3071801 : Blo 2047435 3071801 := bstep (se 2 (by rfl) ⟨1151925, by rfl⟩ : syracuseStep 3071801 = 2303851) B2303851
theorem B2047867 : Blo 2047435 2047867 := bstep (se 1 (by rfl) ⟨1535900, by rfl⟩ : syracuseStep 2047867 = 3071801) B3071801
theorem B2335289 : Blo 2047435 2335289 := bbase (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) (by norm_num)
theorem B6227437 : Blo 2047435 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B8303249 : Blo 2047435 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B5535499 : Blo 2047435 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B7380665 : Blo 2047435 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B4920443 : Blo 2047435 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B3280295 : Blo 2047435 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B8747453 : Blo 2047435 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B23326541 : Blo 2047435 23326541 := bstep (se 3 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 23326541 = 8747453) B8747453
theorem B15551027 : Blo 2047435 15551027 := bstep (se 1 (by rfl) ⟨11663270, by rfl⟩ : syracuseStep 15551027 = 23326541) B23326541
theorem B10367351 : Blo 2047435 10367351 := bstep (se 1 (by rfl) ⟨7775513, by rfl⟩ : syracuseStep 10367351 = 15551027) B15551027
theorem B6911567 : Blo 2047435 6911567 := bstep (se 1 (by rfl) ⟨5183675, by rfl⟩ : syracuseStep 6911567 = 10367351) B10367351
theorem B4607711 : Blo 2047435 4607711 := bstep (se 1 (by rfl) ⟨3455783, by rfl⟩ : syracuseStep 4607711 = 6911567) B6911567
theorem B3071807 : Blo 2047435 3071807 := bstep (se 1 (by rfl) ⟨2303855, by rfl⟩ : syracuseStep 3071807 = 4607711) B4607711
theorem B2047871 : Blo 2047435 2047871 := bstep (se 1 (by rfl) ⟨1535903, by rfl⟩ : syracuseStep 2047871 = 3071807) B3071807
theorem B3071813 : Blo 2047435 3071813 := bbase (se 4 (by rfl) ⟨287982, by rfl⟩ : syracuseStep 3071813 = 575965) (by norm_num)
theorem B2047875 : Blo 2047435 2047875 := bstep (se 1 (by rfl) ⟨1535906, by rfl⟩ : syracuseStep 2047875 = 3071813) B3071813
theorem B3455797 : Blo 2047435 3455797 := bbase (se 5 (by rfl) ⟨161990, by rfl⟩ : syracuseStep 3455797 = 323981) (by norm_num)
theorem B4607729 : Blo 2047435 4607729 := bstep (se 2 (by rfl) ⟨1727898, by rfl⟩ : syracuseStep 4607729 = 3455797) B3455797
theorem B3071819 : Blo 2047435 3071819 := bstep (se 1 (by rfl) ⟨2303864, by rfl⟩ : syracuseStep 3071819 = 4607729) B4607729
theorem B2047879 : Blo 2047435 2047879 := bstep (se 1 (by rfl) ⟨1535909, by rfl⟩ : syracuseStep 2047879 = 3071819) B3071819
theorem B2303869 : Blo 2047435 2303869 := bbase (se 3 (by rfl) ⟨431975, by rfl⟩ : syracuseStep 2303869 = 863951) (by norm_num)
theorem B3071825 : Blo 2047435 3071825 := bstep (se 2 (by rfl) ⟨1151934, by rfl⟩ : syracuseStep 3071825 = 2303869) B2303869
theorem B2047883 : Blo 2047435 2047883 := bstep (se 1 (by rfl) ⟨1535912, by rfl⟩ : syracuseStep 2047883 = 3071825) B3071825
theorem B6911621 : Blo 2047435 6911621 := bbase (se 4 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 6911621 = 1295929) (by norm_num)
theorem B4607747 : Blo 2047435 4607747 := bstep (se 1 (by rfl) ⟨3455810, by rfl⟩ : syracuseStep 4607747 = 6911621) B6911621
theorem B3071831 : Blo 2047435 3071831 := bstep (se 1 (by rfl) ⟨2303873, by rfl⟩ : syracuseStep 3071831 = 4607747) B4607747
theorem B2047887 : Blo 2047435 2047887 := bstep (se 1 (by rfl) ⟨1535915, by rfl⟩ : syracuseStep 2047887 = 3071831) B3071831
theorem B3071837 : Blo 2047435 3071837 := bbase (se 3 (by rfl) ⟨575969, by rfl⟩ : syracuseStep 3071837 = 1151939) (by norm_num)
theorem B2047891 : Blo 2047435 2047891 := bstep (se 1 (by rfl) ⟨1535918, by rfl⟩ : syracuseStep 2047891 = 3071837) B3071837
theorem B4607765 : Blo 2047435 4607765 := bbase (se 6 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 4607765 = 215989) (by norm_num)
theorem B3071843 : Blo 2047435 3071843 := bstep (se 1 (by rfl) ⟨2303882, by rfl⟩ : syracuseStep 3071843 = 4607765) B4607765
theorem B2047895 : Blo 2047435 2047895 := bstep (se 1 (by rfl) ⟨1535921, by rfl⟩ : syracuseStep 2047895 = 3071843) B3071843
theorem B7775621 : Blo 2047435 7775621 := bbase (se 4 (by rfl) ⟨728964, by rfl⟩ : syracuseStep 7775621 = 1457929) (by norm_num)
theorem B5183747 : Blo 2047435 5183747 := bstep (se 1 (by rfl) ⟨3887810, by rfl⟩ : syracuseStep 5183747 = 7775621) B7775621
theorem B3455831 : Blo 2047435 3455831 := bstep (se 1 (by rfl) ⟨2591873, by rfl⟩ : syracuseStep 3455831 = 5183747) B5183747
theorem B2303887 : Blo 2047435 2303887 := bstep (se 1 (by rfl) ⟨1727915, by rfl⟩ : syracuseStep 2303887 = 3455831) B3455831
theorem B3071849 : Blo 2047435 3071849 := bstep (se 2 (by rfl) ⟨1151943, by rfl⟩ : syracuseStep 3071849 = 2303887) B2303887
theorem B2047899 : Blo 2047435 2047899 := bstep (se 1 (by rfl) ⟨1535924, by rfl⟩ : syracuseStep 2047899 = 3071849) B3071849
theorem B6560693 : Blo 2047435 6560693 := bbase (se 5 (by rfl) ⟨307532, by rfl⟩ : syracuseStep 6560693 = 615065) (by norm_num)
theorem B4373795 : Blo 2047435 4373795 := bstep (se 1 (by rfl) ⟨3280346, by rfl⟩ : syracuseStep 4373795 = 6560693) B6560693
theorem B11663453 : Blo 2047435 11663453 := bstep (se 3 (by rfl) ⟨2186897, by rfl⟩ : syracuseStep 11663453 = 4373795) B4373795
theorem B7775635 : Blo 2047435 7775635 := bstep (se 1 (by rfl) ⟨5831726, by rfl⟩ : syracuseStep 7775635 = 11663453) B11663453
theorem B10367513 : Blo 2047435 10367513 := bstep (se 2 (by rfl) ⟨3887817, by rfl⟩ : syracuseStep 10367513 = 7775635) B7775635
theorem B6911675 : Blo 2047435 6911675 := bstep (se 1 (by rfl) ⟨5183756, by rfl⟩ : syracuseStep 6911675 = 10367513) B10367513
theorem B4607783 : Blo 2047435 4607783 := bstep (se 1 (by rfl) ⟨3455837, by rfl⟩ : syracuseStep 4607783 = 6911675) B6911675
theorem B3071855 : Blo 2047435 3071855 := bstep (se 1 (by rfl) ⟨2303891, by rfl⟩ : syracuseStep 3071855 = 4607783) B4607783
theorem B2047903 : Blo 2047435 2047903 := bstep (se 1 (by rfl) ⟨1535927, by rfl⟩ : syracuseStep 2047903 = 3071855) B3071855
theorem B3071861 : Blo 2047435 3071861 := bbase (se 5 (by rfl) ⟨143993, by rfl⟩ : syracuseStep 3071861 = 287987) (by norm_num)
theorem B2047907 : Blo 2047435 2047907 := bstep (se 1 (by rfl) ⟨1535930, by rfl⟩ : syracuseStep 2047907 = 3071861) B3071861
theorem B4373813 : Blo 2047435 4373813 := bbase (se 5 (by rfl) ⟨205022, by rfl⟩ : syracuseStep 4373813 = 410045) (by norm_num)
theorem B2915875 : Blo 2047435 2915875 := bstep (se 1 (by rfl) ⟨2186906, by rfl⟩ : syracuseStep 2915875 = 4373813) B4373813
theorem B3887833 : Blo 2047435 3887833 := bstep (se 2 (by rfl) ⟨1457937, by rfl⟩ : syracuseStep 3887833 = 2915875) B2915875
theorem B5183777 : Blo 2047435 5183777 := bstep (se 2 (by rfl) ⟨1943916, by rfl⟩ : syracuseStep 5183777 = 3887833) B3887833
theorem B3455851 : Blo 2047435 3455851 := bstep (se 1 (by rfl) ⟨2591888, by rfl⟩ : syracuseStep 3455851 = 5183777) B5183777
theorem B4607801 : Blo 2047435 4607801 := bstep (se 2 (by rfl) ⟨1727925, by rfl⟩ : syracuseStep 4607801 = 3455851) B3455851
theorem B3071867 : Blo 2047435 3071867 := bstep (se 1 (by rfl) ⟨2303900, by rfl⟩ : syracuseStep 3071867 = 4607801) B4607801
theorem B2047911 : Blo 2047435 2047911 := bstep (se 1 (by rfl) ⟨1535933, by rfl⟩ : syracuseStep 2047911 = 3071867) B3071867
theorem B2303905 : Blo 2047435 2303905 := bbase (se 2 (by rfl) ⟨863964, by rfl⟩ : syracuseStep 2303905 = 1727929) (by norm_num)
theorem B3071873 : Blo 2047435 3071873 := bstep (se 2 (by rfl) ⟨1151952, by rfl⟩ : syracuseStep 3071873 = 2303905) B2303905
theorem B2047915 : Blo 2047435 2047915 := bstep (se 1 (by rfl) ⟨1535936, by rfl⟩ : syracuseStep 2047915 = 3071873) B3071873
theorem B5183797 : Blo 2047435 5183797 := bbase (se 5 (by rfl) ⟨242990, by rfl⟩ : syracuseStep 5183797 = 485981) (by norm_num)
theorem B6911729 : Blo 2047435 6911729 := bstep (se 2 (by rfl) ⟨2591898, by rfl⟩ : syracuseStep 6911729 = 5183797) B5183797
theorem B4607819 : Blo 2047435 4607819 := bstep (se 1 (by rfl) ⟨3455864, by rfl⟩ : syracuseStep 4607819 = 6911729) B6911729
theorem B3071879 : Blo 2047435 3071879 := bstep (se 1 (by rfl) ⟨2303909, by rfl⟩ : syracuseStep 3071879 = 4607819) B4607819
theorem B2047919 : Blo 2047435 2047919 := bstep (se 1 (by rfl) ⟨1535939, by rfl⟩ : syracuseStep 2047919 = 3071879) B3071879
theorem B3071885 : Blo 2047435 3071885 := bbase (se 3 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 3071885 = 1151957) (by norm_num)
theorem B2047923 : Blo 2047435 2047923 := bstep (se 1 (by rfl) ⟨1535942, by rfl⟩ : syracuseStep 2047923 = 3071885) B3071885
theorem B4607837 : Blo 2047435 4607837 := bbase (se 3 (by rfl) ⟨863969, by rfl⟩ : syracuseStep 4607837 = 1727939) (by norm_num)
theorem B3071891 : Blo 2047435 3071891 := bstep (se 1 (by rfl) ⟨2303918, by rfl⟩ : syracuseStep 3071891 = 4607837) B4607837
theorem B2047927 : Blo 2047435 2047927 := bstep (se 1 (by rfl) ⟨1535945, by rfl⟩ : syracuseStep 2047927 = 3071891) B3071891
theorem B3455885 : Blo 2047435 3455885 := bbase (se 3 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 3455885 = 1295957) (by norm_num)
theorem B2303923 : Blo 2047435 2303923 := bstep (se 1 (by rfl) ⟨1727942, by rfl⟩ : syracuseStep 2303923 = 3455885) B3455885
theorem B3071897 : Blo 2047435 3071897 := bstep (se 2 (by rfl) ⟨1151961, by rfl⟩ : syracuseStep 3071897 = 2303923) B2303923
theorem B2047931 : Blo 2047435 2047931 := bstep (se 1 (by rfl) ⟨1535948, by rfl⟩ : syracuseStep 2047931 = 3071897) B3071897
theorem B3550837 : Blo 2047435 3550837 := bbase (se 5 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 3550837 = 332891) (by norm_num)
theorem B4734449 : Blo 2047435 4734449 := bstep (se 2 (by rfl) ⟨1775418, by rfl⟩ : syracuseStep 4734449 = 3550837) B3550837
theorem B3156299 : Blo 2047435 3156299 := bstep (se 1 (by rfl) ⟨2367224, by rfl⟩ : syracuseStep 3156299 = 4734449) B4734449
theorem B2104199 : Blo 2047435 2104199 := bstep (se 1 (by rfl) ⟨1578149, by rfl⟩ : syracuseStep 2104199 = 3156299) B3156299
theorem B22444789 : Blo 2047435 22444789 := bstep (se 5 (by rfl) ⟨1052099, by rfl⟩ : syracuseStep 22444789 = 2104199) B2104199
theorem B29926385 : Blo 2047435 29926385 := bstep (se 2 (by rfl) ⟨11222394, by rfl⟩ : syracuseStep 29926385 = 22444789) B22444789
theorem B19950923 : Blo 2047435 19950923 := bstep (se 1 (by rfl) ⟨14963192, by rfl⟩ : syracuseStep 19950923 = 29926385) B29926385
theorem B13300615 : Blo 2047435 13300615 := bstep (se 1 (by rfl) ⟨9975461, by rfl⟩ : syracuseStep 13300615 = 19950923) B19950923
theorem B17734153 : Blo 2047435 17734153 := bstep (se 2 (by rfl) ⟨6650307, by rfl⟩ : syracuseStep 17734153 = 13300615) B13300615
theorem B23645537 : Blo 2047435 23645537 := bstep (se 2 (by rfl) ⟨8867076, by rfl⟩ : syracuseStep 23645537 = 17734153) B17734153
theorem B15763691 : Blo 2047435 15763691 := bstep (se 1 (by rfl) ⟨11822768, by rfl⟩ : syracuseStep 15763691 = 23645537) B23645537
theorem B42036509 : Blo 2047435 42036509 := bstep (se 3 (by rfl) ⟨7881845, by rfl⟩ : syracuseStep 42036509 = 15763691) B15763691
theorem B28024339 : Blo 2047435 28024339 := bstep (se 1 (by rfl) ⟨21018254, by rfl⟩ : syracuseStep 28024339 = 42036509) B42036509
theorem B37365785 : Blo 2047435 37365785 := bstep (se 2 (by rfl) ⟨14012169, by rfl⟩ : syracuseStep 37365785 = 28024339) B28024339
theorem B24910523 : Blo 2047435 24910523 := bstep (se 1 (by rfl) ⟨18682892, by rfl⟩ : syracuseStep 24910523 = 37365785) B37365785
theorem B16607015 : Blo 2047435 16607015 := bstep (se 1 (by rfl) ⟨12455261, by rfl⟩ : syracuseStep 16607015 = 24910523) B24910523
theorem B11071343 : Blo 2047435 11071343 := bstep (se 1 (by rfl) ⟨8303507, by rfl⟩ : syracuseStep 11071343 = 16607015) B16607015
theorem B7380895 : Blo 2047435 7380895 := bstep (se 1 (by rfl) ⟨5535671, by rfl⟩ : syracuseStep 7380895 = 11071343) B11071343
theorem B9841193 : Blo 2047435 9841193 := bstep (se 2 (by rfl) ⟨3690447, by rfl⟩ : syracuseStep 9841193 = 7380895) B7380895
theorem B6560795 : Blo 2047435 6560795 := bstep (se 1 (by rfl) ⟨4920596, by rfl⟩ : syracuseStep 6560795 = 9841193) B9841193
theorem B17495453 : Blo 2047435 17495453 := bstep (se 3 (by rfl) ⟨3280397, by rfl⟩ : syracuseStep 17495453 = 6560795) B6560795
theorem B11663635 : Blo 2047435 11663635 := bstep (se 1 (by rfl) ⟨8747726, by rfl⟩ : syracuseStep 11663635 = 17495453) B17495453
theorem B15551513 : Blo 2047435 15551513 := bstep (se 2 (by rfl) ⟨5831817, by rfl⟩ : syracuseStep 15551513 = 11663635) B11663635
theorem B10367675 : Blo 2047435 10367675 := bstep (se 1 (by rfl) ⟨7775756, by rfl⟩ : syracuseStep 10367675 = 15551513) B15551513
theorem B6911783 : Blo 2047435 6911783 := bstep (se 1 (by rfl) ⟨5183837, by rfl⟩ : syracuseStep 6911783 = 10367675) B10367675
theorem B4607855 : Blo 2047435 4607855 := bstep (se 1 (by rfl) ⟨3455891, by rfl⟩ : syracuseStep 4607855 = 6911783) B6911783
theorem B3071903 : Blo 2047435 3071903 := bstep (se 1 (by rfl) ⟨2303927, by rfl⟩ : syracuseStep 3071903 = 4607855) B4607855
theorem B2047935 : Blo 2047435 2047935 := bstep (se 1 (by rfl) ⟨1535951, by rfl⟩ : syracuseStep 2047935 = 3071903) B3071903
theorem B3071909 : Blo 2047435 3071909 := bbase (se 4 (by rfl) ⟨287991, by rfl⟩ : syracuseStep 3071909 = 575983) (by norm_num)
theorem B2047939 : Blo 2047435 2047939 := bstep (se 1 (by rfl) ⟨1535954, by rfl⟩ : syracuseStep 2047939 = 3071909) B3071909
theorem B2591929 : Blo 2047435 2591929 := bbase (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) (by norm_num)
theorem B3455905 : Blo 2047435 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B4607873 : Blo 2047435 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B3071915 : Blo 2047435 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B2047943 : Blo 2047435 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B2303941 : Blo 2047435 2303941 := bbase (se 4 (by rfl) ⟨215994, by rfl⟩ : syracuseStep 2303941 = 431989) (by norm_num)
theorem B3071921 : Blo 2047435 3071921 := bstep (se 2 (by rfl) ⟨1151970, by rfl⟩ : syracuseStep 3071921 = 2303941) B2303941
theorem B2047947 : Blo 2047435 2047947 := bstep (se 1 (by rfl) ⟨1535960, by rfl⟩ : syracuseStep 2047947 = 3071921) B3071921
theorem B3887909 : Blo 2047435 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B2591939 : Blo 2047435 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B6911837 : Blo 2047435 6911837 := bstep (se 3 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 6911837 = 2591939) B2591939
theorem B4607891 : Blo 2047435 4607891 := bstep (se 1 (by rfl) ⟨3455918, by rfl⟩ : syracuseStep 4607891 = 6911837) B6911837
theorem B3071927 : Blo 2047435 3071927 := bstep (se 1 (by rfl) ⟨2303945, by rfl⟩ : syracuseStep 3071927 = 4607891) B4607891
theorem B2047951 : Blo 2047435 2047951 := bstep (se 1 (by rfl) ⟨1535963, by rfl⟩ : syracuseStep 2047951 = 3071927) B3071927
theorem B3071933 : Blo 2047435 3071933 := bbase (se 3 (by rfl) ⟨575987, by rfl⟩ : syracuseStep 3071933 = 1151975) (by norm_num)
theorem B2047955 : Blo 2047435 2047955 := bstep (se 1 (by rfl) ⟨1535966, by rfl⟩ : syracuseStep 2047955 = 3071933) B3071933
theorem B4607909 : Blo 2047435 4607909 := bbase (se 4 (by rfl) ⟨431991, by rfl⟩ : syracuseStep 4607909 = 863983) (by norm_num)
theorem B3071939 : Blo 2047435 3071939 := bstep (se 1 (by rfl) ⟨2303954, by rfl⟩ : syracuseStep 3071939 = 4607909) B4607909
theorem B2047959 : Blo 2047435 2047959 := bstep (se 1 (by rfl) ⟨1535969, by rfl⟩ : syracuseStep 2047959 = 3071939) B3071939
theorem B5183909 : Blo 2047435 5183909 := bbase (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) (by norm_num)
theorem B3455939 : Blo 2047435 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B2303959 : Blo 2047435 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B3071945 : Blo 2047435 3071945 := bstep (se 2 (by rfl) ⟨1151979, by rfl⟩ : syracuseStep 3071945 = 2303959) B2303959
theorem B2047963 : Blo 2047435 2047963 := bstep (se 1 (by rfl) ⟨1535972, by rfl⟩ : syracuseStep 2047963 = 3071945) B3071945
theorem B5831909 : Blo 2047435 5831909 := bbase (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) (by norm_num)
theorem B3887939 : Blo 2047435 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B10367837 : Blo 2047435 10367837 := bstep (se 3 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 10367837 = 3887939) B3887939
theorem B6911891 : Blo 2047435 6911891 := bstep (se 1 (by rfl) ⟨5183918, by rfl⟩ : syracuseStep 6911891 = 10367837) B10367837
theorem B4607927 : Blo 2047435 4607927 := bstep (se 1 (by rfl) ⟨3455945, by rfl⟩ : syracuseStep 4607927 = 6911891) B6911891
theorem B3071951 : Blo 2047435 3071951 := bstep (se 1 (by rfl) ⟨2303963, by rfl⟩ : syracuseStep 3071951 = 4607927) B4607927
theorem B2047967 : Blo 2047435 2047967 := bstep (se 1 (by rfl) ⟨1535975, by rfl⟩ : syracuseStep 2047967 = 3071951) B3071951
theorem B3071957 : Blo 2047435 3071957 := bbase (se 7 (by rfl) ⟨35999, by rfl⟩ : syracuseStep 3071957 = 71999) (by norm_num)
theorem B2047971 : Blo 2047435 2047971 := bstep (se 1 (by rfl) ⟨1535978, by rfl⟩ : syracuseStep 2047971 = 3071957) B3071957
theorem B7775909 : Blo 2047435 7775909 := bbase (se 4 (by rfl) ⟨728991, by rfl⟩ : syracuseStep 7775909 = 1457983) (by norm_num)
theorem B5183939 : Blo 2047435 5183939 := bstep (se 1 (by rfl) ⟨3887954, by rfl⟩ : syracuseStep 5183939 = 7775909) B7775909
theorem B3455959 : Blo 2047435 3455959 := bstep (se 1 (by rfl) ⟨2591969, by rfl⟩ : syracuseStep 3455959 = 5183939) B5183939
theorem B4607945 : Blo 2047435 4607945 := bstep (se 2 (by rfl) ⟨1727979, by rfl⟩ : syracuseStep 4607945 = 3455959) B3455959
theorem B3071963 : Blo 2047435 3071963 := bstep (se 1 (by rfl) ⟨2303972, by rfl⟩ : syracuseStep 3071963 = 4607945) B4607945
theorem B2047975 : Blo 2047435 2047975 := bstep (se 1 (by rfl) ⟨1535981, by rfl⟩ : syracuseStep 2047975 = 3071963) B3071963
theorem B2303977 : Blo 2047435 2303977 := bbase (se 2 (by rfl) ⟨863991, by rfl⟩ : syracuseStep 2303977 = 1727983) (by norm_num)
theorem B3071969 : Blo 2047435 3071969 := bstep (se 2 (by rfl) ⟨1151988, by rfl⟩ : syracuseStep 3071969 = 2303977) B2303977
theorem B2047979 : Blo 2047435 2047979 := bstep (se 1 (by rfl) ⟨1535984, by rfl⟩ : syracuseStep 2047979 = 3071969) B3071969
theorem B9341669 : Blo 2047435 9341669 := bbase (se 4 (by rfl) ⟨875781, by rfl⟩ : syracuseStep 9341669 = 1751563) (by norm_num)
theorem B6227779 : Blo 2047435 6227779 := bstep (se 1 (by rfl) ⟨4670834, by rfl⟩ : syracuseStep 6227779 = 9341669) B9341669
theorem B8303705 : Blo 2047435 8303705 := bstep (se 2 (by rfl) ⟨3113889, by rfl⟩ : syracuseStep 8303705 = 6227779) B6227779
theorem B5535803 : Blo 2047435 5535803 := bstep (se 1 (by rfl) ⟨4151852, by rfl⟩ : syracuseStep 5535803 = 8303705) B8303705
theorem B3690535 : Blo 2047435 3690535 := bstep (se 1 (by rfl) ⟨2767901, by rfl⟩ : syracuseStep 3690535 = 5535803) B5535803
theorem B4920713 : Blo 2047435 4920713 := bstep (se 2 (by rfl) ⟨1845267, by rfl⟩ : syracuseStep 4920713 = 3690535) B3690535
theorem B3280475 : Blo 2047435 3280475 := bstep (se 1 (by rfl) ⟨2460356, by rfl⟩ : syracuseStep 3280475 = 4920713) B4920713
theorem B2186983 : Blo 2047435 2186983 := bstep (se 1 (by rfl) ⟨1640237, by rfl⟩ : syracuseStep 2186983 = 3280475) B3280475
theorem B11663909 : Blo 2047435 11663909 := bstep (se 4 (by rfl) ⟨1093491, by rfl⟩ : syracuseStep 11663909 = 2186983) B2186983
theorem B7775939 : Blo 2047435 7775939 := bstep (se 1 (by rfl) ⟨5831954, by rfl⟩ : syracuseStep 7775939 = 11663909) B11663909
theorem B5183959 : Blo 2047435 5183959 := bstep (se 1 (by rfl) ⟨3887969, by rfl⟩ : syracuseStep 5183959 = 7775939) B7775939
theorem B6911945 : Blo 2047435 6911945 := bstep (se 2 (by rfl) ⟨2591979, by rfl⟩ : syracuseStep 6911945 = 5183959) B5183959
theorem B4607963 : Blo 2047435 4607963 := bstep (se 1 (by rfl) ⟨3455972, by rfl⟩ : syracuseStep 4607963 = 6911945) B6911945
theorem B3071975 : Blo 2047435 3071975 := bstep (se 1 (by rfl) ⟨2303981, by rfl⟩ : syracuseStep 3071975 = 4607963) B4607963
theorem B2047983 : Blo 2047435 2047983 := bstep (se 1 (by rfl) ⟨1535987, by rfl⟩ : syracuseStep 2047983 = 3071975) B3071975
theorem B3071981 : Blo 2047435 3071981 := bbase (se 3 (by rfl) ⟨575996, by rfl⟩ : syracuseStep 3071981 = 1151993) (by norm_num)
theorem B2047987 : Blo 2047435 2047987 := bstep (se 1 (by rfl) ⟨1535990, by rfl⟩ : syracuseStep 2047987 = 3071981) B3071981
theorem B4607981 : Blo 2047435 4607981 := bbase (se 3 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 4607981 = 1727993) (by norm_num)
theorem B3071987 : Blo 2047435 3071987 := bstep (se 1 (by rfl) ⟨2303990, by rfl⟩ : syracuseStep 3071987 = 4607981) B4607981
theorem B2047991 : Blo 2047435 2047991 := bstep (se 1 (by rfl) ⟨1535993, by rfl⟩ : syracuseStep 2047991 = 3071987) B3071987
theorem B2955781 : Blo 2047435 2955781 := bbase (se 4 (by rfl) ⟨277104, by rfl⟩ : syracuseStep 2955781 = 554209) (by norm_num)
theorem B3941041 : Blo 2047435 3941041 := bstep (se 2 (by rfl) ⟨1477890, by rfl⟩ : syracuseStep 3941041 = 2955781) B2955781
theorem B5254721 : Blo 2047435 5254721 := bstep (se 2 (by rfl) ⟨1970520, by rfl⟩ : syracuseStep 5254721 = 3941041) B3941041
theorem B3503147 : Blo 2047435 3503147 := bstep (se 1 (by rfl) ⟨2627360, by rfl⟩ : syracuseStep 3503147 = 5254721) B5254721
theorem B9341725 : Blo 2047435 9341725 := bstep (se 3 (by rfl) ⟨1751573, by rfl⟩ : syracuseStep 9341725 = 3503147) B3503147
theorem B12455633 : Blo 2047435 12455633 := bstep (se 2 (by rfl) ⟨4670862, by rfl⟩ : syracuseStep 12455633 = 9341725) B9341725
theorem B8303755 : Blo 2047435 8303755 := bstep (se 1 (by rfl) ⟨6227816, by rfl⟩ : syracuseStep 8303755 = 12455633) B12455633
theorem B11071673 : Blo 2047435 11071673 := bstep (se 2 (by rfl) ⟨4151877, by rfl⟩ : syracuseStep 11071673 = 8303755) B8303755
theorem B7381115 : Blo 2047435 7381115 := bstep (se 1 (by rfl) ⟨5535836, by rfl⟩ : syracuseStep 7381115 = 11071673) B11071673
theorem B4920743 : Blo 2047435 4920743 := bstep (se 1 (by rfl) ⟨3690557, by rfl⟩ : syracuseStep 4920743 = 7381115) B7381115
theorem B3280495 : Blo 2047435 3280495 := bstep (se 1 (by rfl) ⟨2460371, by rfl⟩ : syracuseStep 3280495 = 4920743) B4920743
theorem B4373993 : Blo 2047435 4373993 := bstep (se 2 (by rfl) ⟨1640247, by rfl⟩ : syracuseStep 4373993 = 3280495) B3280495
theorem B2915995 : Blo 2047435 2915995 := bstep (se 1 (by rfl) ⟨2186996, by rfl⟩ : syracuseStep 2915995 = 4373993) B4373993
theorem B3887993 : Blo 2047435 3887993 := bstep (se 2 (by rfl) ⟨1457997, by rfl⟩ : syracuseStep 3887993 = 2915995) B2915995
theorem B2591995 : Blo 2047435 2591995 := bstep (se 1 (by rfl) ⟨1943996, by rfl⟩ : syracuseStep 2591995 = 3887993) B3887993
theorem B3455993 : Blo 2047435 3455993 := bstep (se 2 (by rfl) ⟨1295997, by rfl⟩ : syracuseStep 3455993 = 2591995) B2591995
theorem B2303995 : Blo 2047435 2303995 := bstep (se 1 (by rfl) ⟨1727996, by rfl⟩ : syracuseStep 2303995 = 3455993) B3455993
theorem B3071993 : Blo 2047435 3071993 := bstep (se 2 (by rfl) ⟨1151997, by rfl⟩ : syracuseStep 3071993 = 2303995) B2303995
theorem B2047995 : Blo 2047435 2047995 := bstep (se 1 (by rfl) ⟨1535996, by rfl⟩ : syracuseStep 2047995 = 3071993) B3071993
theorem B9469189 : Blo 2047435 9469189 := bbase (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) (by norm_num)
theorem B50502341 : Blo 2047435 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B33668227 : Blo 2047435 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B179563877 : Blo 2047435 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B119709251 : Blo 2047435 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B79806167 : Blo 2047435 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B53204111 : Blo 2047435 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B35469407 : Blo 2047435 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B23646271 : Blo 2047435 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B31528361 : Blo 2047435 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B21018907 : Blo 2047435 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B28025209 : Blo 2047435 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B149467781 : Blo 2047435 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B398580749 : Blo 2047435 398580749 := bstep (se 3 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 398580749 = 149467781) B149467781
theorem B265720499 : Blo 2047435 265720499 := bstep (se 1 (by rfl) ⟨199290374, by rfl⟩ : syracuseStep 265720499 = 398580749) B398580749
theorem B177146999 : Blo 2047435 177146999 := bstep (se 1 (by rfl) ⟨132860249, by rfl⟩ : syracuseStep 177146999 = 265720499) B265720499
theorem B118097999 : Blo 2047435 118097999 := bstep (se 1 (by rfl) ⟨88573499, by rfl⟩ : syracuseStep 118097999 = 177146999) B177146999
theorem B78731999 : Blo 2047435 78731999 := bstep (se 1 (by rfl) ⟨59048999, by rfl⟩ : syracuseStep 78731999 = 118097999) B118097999
theorem B52487999 : Blo 2047435 52487999 := bstep (se 1 (by rfl) ⟨39365999, by rfl⟩ : syracuseStep 52487999 = 78731999) B78731999
theorem B34991999 : Blo 2047435 34991999 := bstep (se 1 (by rfl) ⟨26243999, by rfl⟩ : syracuseStep 34991999 = 52487999) B52487999
theorem B23327999 : Blo 2047435 23327999 := bstep (se 1 (by rfl) ⟨17495999, by rfl⟩ : syracuseStep 23327999 = 34991999) B34991999
theorem B15551999 : Blo 2047435 15551999 := bstep (se 1 (by rfl) ⟨11663999, by rfl⟩ : syracuseStep 15551999 = 23327999) B23327999
theorem B10367999 : Blo 2047435 10367999 := bstep (se 1 (by rfl) ⟨7775999, by rfl⟩ : syracuseStep 10367999 = 15551999) B15551999
theorem B6911999 : Blo 2047435 6911999 := bstep (se 1 (by rfl) ⟨5183999, by rfl⟩ : syracuseStep 6911999 = 10367999) B10367999
theorem B4607999 : Blo 2047435 4607999 := bstep (se 1 (by rfl) ⟨3455999, by rfl⟩ : syracuseStep 4607999 = 6911999) B6911999
theorem B3071999 : Blo 2047435 3071999 := bstep (se 1 (by rfl) ⟨2303999, by rfl⟩ : syracuseStep 3071999 = 4607999) B4607999
theorem B2047999 : Blo 2047435 2047999 := bstep (se 1 (by rfl) ⟨1535999, by rfl⟩ : syracuseStep 2047999 = 3071999) B3071999
theorem B3072005 : Blo 2047435 3072005 := bbase (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) (by norm_num)
theorem B2048003 : Blo 2047435 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B3456013 : Blo 2047435 3456013 := bbase (se 3 (by rfl) ⟨648002, by rfl⟩ : syracuseStep 3456013 = 1296005) (by norm_num)
theorem B4608017 : Blo 2047435 4608017 := bstep (se 2 (by rfl) ⟨1728006, by rfl⟩ : syracuseStep 4608017 = 3456013) B3456013
theorem B3072011 : Blo 2047435 3072011 := bstep (se 1 (by rfl) ⟨2304008, by rfl⟩ : syracuseStep 3072011 = 4608017) B4608017
theorem B2048007 : Blo 2047435 2048007 := bstep (se 1 (by rfl) ⟨1536005, by rfl⟩ : syracuseStep 2048007 = 3072011) B3072011
theorem B2304013 : Blo 2047435 2304013 := bbase (se 3 (by rfl) ⟨432002, by rfl⟩ : syracuseStep 2304013 = 864005) (by norm_num)
theorem B3072017 : Blo 2047435 3072017 := bstep (se 2 (by rfl) ⟨1152006, by rfl⟩ : syracuseStep 3072017 = 2304013) B2304013
theorem B2048011 : Blo 2047435 2048011 := bstep (se 1 (by rfl) ⟨1536008, by rfl⟩ : syracuseStep 2048011 = 3072017) B3072017
theorem B6912053 : Blo 2047435 6912053 := bbase (se 5 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 6912053 = 648005) (by norm_num)
theorem B4608035 : Blo 2047435 4608035 := bstep (se 1 (by rfl) ⟨3456026, by rfl⟩ : syracuseStep 4608035 = 6912053) B6912053
theorem B3072023 : Blo 2047435 3072023 := bstep (se 1 (by rfl) ⟨2304017, by rfl⟩ : syracuseStep 3072023 = 4608035) B4608035
theorem B2048015 : Blo 2047435 2048015 := bstep (se 1 (by rfl) ⟨1536011, by rfl⟩ : syracuseStep 2048015 = 3072023) B3072023
theorem B3072029 : Blo 2047435 3072029 := bbase (se 3 (by rfl) ⟨576005, by rfl⟩ : syracuseStep 3072029 = 1152011) (by norm_num)
theorem B2048019 : Blo 2047435 2048019 := bstep (se 1 (by rfl) ⟨1536014, by rfl⟩ : syracuseStep 2048019 = 3072029) B3072029
theorem B4608053 : Blo 2047435 4608053 := bbase (se 5 (by rfl) ⟨216002, by rfl⟩ : syracuseStep 4608053 = 432005) (by norm_num)
theorem B3072035 : Blo 2047435 3072035 := bstep (se 1 (by rfl) ⟨2304026, by rfl⟩ : syracuseStep 3072035 = 4608053) B4608053
theorem B2048023 : Blo 2047435 2048023 := bstep (se 1 (by rfl) ⟨1536017, by rfl⟩ : syracuseStep 2048023 = 3072035) B3072035
theorem B9841637 : Blo 2047435 9841637 := bbase (se 4 (by rfl) ⟨922653, by rfl⟩ : syracuseStep 9841637 = 1845307) (by norm_num)
theorem B6561091 : Blo 2047435 6561091 := bstep (se 1 (by rfl) ⟨4920818, by rfl⟩ : syracuseStep 6561091 = 9841637) B9841637
theorem B8748121 : Blo 2047435 8748121 := bstep (se 2 (by rfl) ⟨3280545, by rfl⟩ : syracuseStep 8748121 = 6561091) B6561091
theorem B11664161 : Blo 2047435 11664161 := bstep (se 2 (by rfl) ⟨4374060, by rfl⟩ : syracuseStep 11664161 = 8748121) B8748121
theorem B7776107 : Blo 2047435 7776107 := bstep (se 1 (by rfl) ⟨5832080, by rfl⟩ : syracuseStep 7776107 = 11664161) B11664161
theorem B5184071 : Blo 2047435 5184071 := bstep (se 1 (by rfl) ⟨3888053, by rfl⟩ : syracuseStep 5184071 = 7776107) B7776107
theorem B3456047 : Blo 2047435 3456047 := bstep (se 1 (by rfl) ⟨2592035, by rfl⟩ : syracuseStep 3456047 = 5184071) B5184071
theorem B2304031 : Blo 2047435 2304031 := bstep (se 1 (by rfl) ⟨1728023, by rfl⟩ : syracuseStep 2304031 = 3456047) B3456047
theorem B3072041 : Blo 2047435 3072041 := bstep (se 2 (by rfl) ⟨1152015, by rfl⟩ : syracuseStep 3072041 = 2304031) B2304031
theorem B2048027 : Blo 2047435 2048027 := bstep (se 1 (by rfl) ⟨1536020, by rfl⟩ : syracuseStep 2048027 = 3072041) B3072041
theorem B5194925 : Blo 2047435 5194925 := bbase (se 3 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 5194925 = 1948097) (by norm_num)
theorem B3463283 : Blo 2047435 3463283 := bstep (se 1 (by rfl) ⟨2597462, by rfl⟩ : syracuseStep 3463283 = 5194925) B5194925
theorem B9235421 : Blo 2047435 9235421 := bstep (se 3 (by rfl) ⟨1731641, by rfl⟩ : syracuseStep 9235421 = 3463283) B3463283
theorem B6156947 : Blo 2047435 6156947 := bstep (se 1 (by rfl) ⟨4617710, by rfl⟩ : syracuseStep 6156947 = 9235421) B9235421
theorem B4104631 : Blo 2047435 4104631 := bstep (se 1 (by rfl) ⟨3078473, by rfl⟩ : syracuseStep 4104631 = 6156947) B6156947
theorem B5472841 : Blo 2047435 5472841 := bstep (se 2 (by rfl) ⟨2052315, by rfl⟩ : syracuseStep 5472841 = 4104631) B4104631
theorem B7297121 : Blo 2047435 7297121 := bstep (se 2 (by rfl) ⟨2736420, by rfl⟩ : syracuseStep 7297121 = 5472841) B5472841
theorem B4864747 : Blo 2047435 4864747 := bstep (se 1 (by rfl) ⟨3648560, by rfl⟩ : syracuseStep 4864747 = 7297121) B7297121
theorem B6486329 : Blo 2047435 6486329 := bstep (se 2 (by rfl) ⟨2432373, by rfl⟩ : syracuseStep 6486329 = 4864747) B4864747
theorem B17296877 : Blo 2047435 17296877 := bstep (se 3 (by rfl) ⟨3243164, by rfl⟩ : syracuseStep 17296877 = 6486329) B6486329
theorem B11531251 : Blo 2047435 11531251 := bstep (se 1 (by rfl) ⟨8648438, by rfl⟩ : syracuseStep 11531251 = 17296877) B17296877
theorem B61500005 : Blo 2047435 61500005 := bstep (se 4 (by rfl) ⟨5765625, by rfl⟩ : syracuseStep 61500005 = 11531251) B11531251
theorem B41000003 : Blo 2047435 41000003 := bstep (se 1 (by rfl) ⟨30750002, by rfl⟩ : syracuseStep 41000003 = 61500005) B61500005
theorem B27333335 : Blo 2047435 27333335 := bstep (se 1 (by rfl) ⟨20500001, by rfl⟩ : syracuseStep 27333335 = 41000003) B41000003
theorem B72888893 : Blo 2047435 72888893 := bstep (se 3 (by rfl) ⟨13666667, by rfl⟩ : syracuseStep 72888893 = 27333335) B27333335
theorem B48592595 : Blo 2047435 48592595 := bstep (se 1 (by rfl) ⟨36444446, by rfl⟩ : syracuseStep 48592595 = 72888893) B72888893
theorem B32395063 : Blo 2047435 32395063 := bstep (se 1 (by rfl) ⟨24296297, by rfl⟩ : syracuseStep 32395063 = 48592595) B48592595
theorem B43193417 : Blo 2047435 43193417 := bstep (se 2 (by rfl) ⟨16197531, by rfl⟩ : syracuseStep 43193417 = 32395063) B32395063
theorem B115182445 : Blo 2047435 115182445 := bstep (se 3 (by rfl) ⟨21596708, by rfl⟩ : syracuseStep 115182445 = 43193417) B43193417
theorem B153576593 : Blo 2047435 153576593 := bstep (se 2 (by rfl) ⟨57591222, by rfl⟩ : syracuseStep 153576593 = 115182445) B115182445
theorem B102384395 : Blo 2047435 102384395 := bstep (se 1 (by rfl) ⟨76788296, by rfl⟩ : syracuseStep 102384395 = 153576593) B153576593
theorem B68256263 : Blo 2047435 68256263 := bstep (se 1 (by rfl) ⟨51192197, by rfl⟩ : syracuseStep 68256263 = 102384395) B102384395
theorem B45504175 : Blo 2047435 45504175 := bstep (se 1 (by rfl) ⟨34128131, by rfl⟩ : syracuseStep 45504175 = 68256263) B68256263
theorem B60672233 : Blo 2047435 60672233 := bstep (se 2 (by rfl) ⟨22752087, by rfl⟩ : syracuseStep 60672233 = 45504175) B45504175
theorem B40448155 : Blo 2047435 40448155 := bstep (se 1 (by rfl) ⟨30336116, by rfl⟩ : syracuseStep 40448155 = 60672233) B60672233
theorem B53930873 : Blo 2047435 53930873 := bstep (se 2 (by rfl) ⟨20224077, by rfl⟩ : syracuseStep 53930873 = 40448155) B40448155
theorem B35953915 : Blo 2047435 35953915 := bstep (se 1 (by rfl) ⟨26965436, by rfl⟩ : syracuseStep 35953915 = 53930873) B53930873
theorem B47938553 : Blo 2047435 47938553 := bstep (se 2 (by rfl) ⟨17976957, by rfl⟩ : syracuseStep 47938553 = 35953915) B35953915
theorem B31959035 : Blo 2047435 31959035 := bstep (se 1 (by rfl) ⟨23969276, by rfl⟩ : syracuseStep 31959035 = 47938553) B47938553
theorem B21306023 : Blo 2047435 21306023 := bstep (se 1 (by rfl) ⟨15979517, by rfl⟩ : syracuseStep 21306023 = 31959035) B31959035
theorem B14204015 : Blo 2047435 14204015 := bstep (se 1 (by rfl) ⟨10653011, by rfl⟩ : syracuseStep 14204015 = 21306023) B21306023
theorem B9469343 : Blo 2047435 9469343 := bstep (se 1 (by rfl) ⟨7102007, by rfl⟩ : syracuseStep 9469343 = 14204015) B14204015
theorem B25251581 : Blo 2047435 25251581 := bstep (se 3 (by rfl) ⟨4734671, by rfl⟩ : syracuseStep 25251581 = 9469343) B9469343
theorem B16834387 : Blo 2047435 16834387 := bstep (se 1 (by rfl) ⟨12625790, by rfl⟩ : syracuseStep 16834387 = 25251581) B25251581
theorem B22445849 : Blo 2047435 22445849 := bstep (se 2 (by rfl) ⟨8417193, by rfl⟩ : syracuseStep 22445849 = 16834387) B16834387
theorem B14963899 : Blo 2047435 14963899 := bstep (se 1 (by rfl) ⟨11222924, by rfl⟩ : syracuseStep 14963899 = 22445849) B22445849
theorem B19951865 : Blo 2047435 19951865 := bstep (se 2 (by rfl) ⟨7481949, by rfl⟩ : syracuseStep 19951865 = 14963899) B14963899
theorem B13301243 : Blo 2047435 13301243 := bstep (se 1 (by rfl) ⟨9975932, by rfl⟩ : syracuseStep 13301243 = 19951865) B19951865
theorem B8867495 : Blo 2047435 8867495 := bstep (se 1 (by rfl) ⟨6650621, by rfl⟩ : syracuseStep 8867495 = 13301243) B13301243
theorem B5911663 : Blo 2047435 5911663 := bstep (se 1 (by rfl) ⟨4433747, by rfl⟩ : syracuseStep 5911663 = 8867495) B8867495
theorem B7882217 : Blo 2047435 7882217 := bstep (se 2 (by rfl) ⟨2955831, by rfl⟩ : syracuseStep 7882217 = 5911663) B5911663
theorem B5254811 : Blo 2047435 5254811 := bstep (se 1 (by rfl) ⟨3941108, by rfl⟩ : syracuseStep 5254811 = 7882217) B7882217
theorem B3503207 : Blo 2047435 3503207 := bstep (se 1 (by rfl) ⟨2627405, by rfl⟩ : syracuseStep 3503207 = 5254811) B5254811
theorem B9341885 : Blo 2047435 9341885 := bstep (se 3 (by rfl) ⟨1751603, by rfl⟩ : syracuseStep 9341885 = 3503207) B3503207
theorem B6227923 : Blo 2047435 6227923 := bstep (se 1 (by rfl) ⟨4670942, by rfl⟩ : syracuseStep 6227923 = 9341885) B9341885
theorem B8303897 : Blo 2047435 8303897 := bstep (se 2 (by rfl) ⟨3113961, by rfl⟩ : syracuseStep 8303897 = 6227923) B6227923
theorem B22143725 : Blo 2047435 22143725 := bstep (se 3 (by rfl) ⟨4151948, by rfl⟩ : syracuseStep 22143725 = 8303897) B8303897
theorem B14762483 : Blo 2047435 14762483 := bstep (se 1 (by rfl) ⟨11071862, by rfl⟩ : syracuseStep 14762483 = 22143725) B22143725
theorem B9841655 : Blo 2047435 9841655 := bstep (se 1 (by rfl) ⟨7381241, by rfl⟩ : syracuseStep 9841655 = 14762483) B14762483
theorem B6561103 : Blo 2047435 6561103 := bstep (se 1 (by rfl) ⟨4920827, by rfl⟩ : syracuseStep 6561103 = 9841655) B9841655
theorem B8748137 : Blo 2047435 8748137 := bstep (se 2 (by rfl) ⟨3280551, by rfl⟩ : syracuseStep 8748137 = 6561103) B6561103
theorem B5832091 : Blo 2047435 5832091 := bstep (se 1 (by rfl) ⟨4374068, by rfl⟩ : syracuseStep 5832091 = 8748137) B8748137
theorem B7776121 : Blo 2047435 7776121 := bstep (se 2 (by rfl) ⟨2916045, by rfl⟩ : syracuseStep 7776121 = 5832091) B5832091
theorem B10368161 : Blo 2047435 10368161 := bstep (se 2 (by rfl) ⟨3888060, by rfl⟩ : syracuseStep 10368161 = 7776121) B7776121
theorem B6912107 : Blo 2047435 6912107 := bstep (se 1 (by rfl) ⟨5184080, by rfl⟩ : syracuseStep 6912107 = 10368161) B10368161
theorem B4608071 : Blo 2047435 4608071 := bstep (se 1 (by rfl) ⟨3456053, by rfl⟩ : syracuseStep 4608071 = 6912107) B6912107
theorem B3072047 : Blo 2047435 3072047 := bstep (se 1 (by rfl) ⟨2304035, by rfl⟩ : syracuseStep 3072047 = 4608071) B4608071
theorem B2048031 : Blo 2047435 2048031 := bstep (se 1 (by rfl) ⟨1536023, by rfl⟩ : syracuseStep 2048031 = 3072047) B3072047
theorem B3072053 : Blo 2047435 3072053 := bbase (se 5 (by rfl) ⟨144002, by rfl⟩ : syracuseStep 3072053 = 288005) (by norm_num)
theorem B2048035 : Blo 2047435 2048035 := bstep (se 1 (by rfl) ⟨1536026, by rfl⟩ : syracuseStep 2048035 = 3072053) B3072053
theorem B5184101 : Blo 2047435 5184101 := bbase (se 4 (by rfl) ⟨486009, by rfl⟩ : syracuseStep 5184101 = 972019) (by norm_num)
theorem B3456067 : Blo 2047435 3456067 := bstep (se 1 (by rfl) ⟨2592050, by rfl⟩ : syracuseStep 3456067 = 5184101) B5184101
theorem B4608089 : Blo 2047435 4608089 := bstep (se 2 (by rfl) ⟨1728033, by rfl⟩ : syracuseStep 4608089 = 3456067) B3456067
theorem B3072059 : Blo 2047435 3072059 := bstep (se 1 (by rfl) ⟨2304044, by rfl⟩ : syracuseStep 3072059 = 4608089) B4608089
theorem B2048039 : Blo 2047435 2048039 := bstep (se 1 (by rfl) ⟨1536029, by rfl⟩ : syracuseStep 2048039 = 3072059) B3072059
theorem B2304049 : Blo 2047435 2304049 := bbase (se 2 (by rfl) ⟨864018, by rfl⟩ : syracuseStep 2304049 = 1728037) (by norm_num)
theorem B3072065 : Blo 2047435 3072065 := bstep (se 2 (by rfl) ⟨1152024, by rfl⟩ : syracuseStep 3072065 = 2304049) B2304049
theorem B2048043 : Blo 2047435 2048043 := bstep (se 1 (by rfl) ⟨1536032, by rfl⟩ : syracuseStep 2048043 = 3072065) B3072065
theorem B9841733 : Blo 2047435 9841733 := bbase (se 4 (by rfl) ⟨922662, by rfl⟩ : syracuseStep 9841733 = 1845325) (by norm_num)
theorem B6561155 : Blo 2047435 6561155 := bstep (se 1 (by rfl) ⟨4920866, by rfl⟩ : syracuseStep 6561155 = 9841733) B9841733
theorem B4374103 : Blo 2047435 4374103 := bstep (se 1 (by rfl) ⟨3280577, by rfl⟩ : syracuseStep 4374103 = 6561155) B6561155
theorem B5832137 : Blo 2047435 5832137 := bstep (se 2 (by rfl) ⟨2187051, by rfl⟩ : syracuseStep 5832137 = 4374103) B4374103
theorem B3888091 : Blo 2047435 3888091 := bstep (se 1 (by rfl) ⟨2916068, by rfl⟩ : syracuseStep 3888091 = 5832137) B5832137
theorem B5184121 : Blo 2047435 5184121 := bstep (se 2 (by rfl) ⟨1944045, by rfl⟩ : syracuseStep 5184121 = 3888091) B3888091
theorem B6912161 : Blo 2047435 6912161 := bstep (se 2 (by rfl) ⟨2592060, by rfl⟩ : syracuseStep 6912161 = 5184121) B5184121
theorem B4608107 : Blo 2047435 4608107 := bstep (se 1 (by rfl) ⟨3456080, by rfl⟩ : syracuseStep 4608107 = 6912161) B6912161
theorem B3072071 : Blo 2047435 3072071 := bstep (se 1 (by rfl) ⟨2304053, by rfl⟩ : syracuseStep 3072071 = 4608107) B4608107
theorem B2048047 : Blo 2047435 2048047 := bstep (se 1 (by rfl) ⟨1536035, by rfl⟩ : syracuseStep 2048047 = 3072071) B3072071
theorem B3072077 : Blo 2047435 3072077 := bbase (se 3 (by rfl) ⟨576014, by rfl⟩ : syracuseStep 3072077 = 1152029) (by norm_num)
theorem B2048051 : Blo 2047435 2048051 := bstep (se 1 (by rfl) ⟨1536038, by rfl⟩ : syracuseStep 2048051 = 3072077) B3072077
theorem B4608125 : Blo 2047435 4608125 := bbase (se 3 (by rfl) ⟨864023, by rfl⟩ : syracuseStep 4608125 = 1728047) (by norm_num)
theorem B3072083 : Blo 2047435 3072083 := bstep (se 1 (by rfl) ⟨2304062, by rfl⟩ : syracuseStep 3072083 = 4608125) B4608125
theorem B2048055 : Blo 2047435 2048055 := bstep (se 1 (by rfl) ⟨1536041, by rfl⟩ : syracuseStep 2048055 = 3072083) B3072083
theorem B3456101 : Blo 2047435 3456101 := bbase (se 4 (by rfl) ⟨324009, by rfl⟩ : syracuseStep 3456101 = 648019) (by norm_num)
theorem B2304067 : Blo 2047435 2304067 := bstep (se 1 (by rfl) ⟨1728050, by rfl⟩ : syracuseStep 2304067 = 3456101) B3456101
theorem B3072089 : Blo 2047435 3072089 := bstep (se 2 (by rfl) ⟨1152033, by rfl⟩ : syracuseStep 3072089 = 2304067) B2304067
theorem B2048059 : Blo 2047435 2048059 := bstep (se 1 (by rfl) ⟨1536044, by rfl⟩ : syracuseStep 2048059 = 3072089) B3072089
theorem B3599509 : Blo 2047435 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B4799345 : Blo 2047435 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B12798253 : Blo 2047435 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B68257349 : Blo 2047435 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B45504899 : Blo 2047435 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B30336599 : Blo 2047435 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B20224399 : Blo 2047435 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B26965865 : Blo 2047435 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B17977243 : Blo 2047435 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B23969657 : Blo 2047435 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B15979771 : Blo 2047435 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B85225445 : Blo 2047435 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B56816963 : Blo 2047435 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B37877975 : Blo 2047435 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B25251983 : Blo 2047435 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B16834655 : Blo 2047435 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B44892413 : Blo 2047435 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B29928275 : Blo 2047435 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B19952183 : Blo 2047435 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B13301455 : Blo 2047435 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B17735273 : Blo 2047435 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B11823515 : Blo 2047435 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B7882343 : Blo 2047435 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B5254895 : Blo 2047435 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B3503263 : Blo 2047435 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B4671017 : Blo 2047435 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B3114011 : Blo 2047435 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B8304029 : Blo 2047435 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B5536019 : Blo 2047435 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B3690679 : Blo 2047435 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B4920905 : Blo 2047435 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B3280603 : Blo 2047435 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B4374137 : Blo 2047435 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B2916091 : Blo 2047435 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B15552485 : Blo 2047435 15552485 := bstep (se 4 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 15552485 = 2916091) B2916091
theorem B10368323 : Blo 2047435 10368323 := bstep (se 1 (by rfl) ⟨7776242, by rfl⟩ : syracuseStep 10368323 = 15552485) B15552485
theorem B6912215 : Blo 2047435 6912215 := bstep (se 1 (by rfl) ⟨5184161, by rfl⟩ : syracuseStep 6912215 = 10368323) B10368323
theorem B4608143 : Blo 2047435 4608143 := bstep (se 1 (by rfl) ⟨3456107, by rfl⟩ : syracuseStep 4608143 = 6912215) B6912215
theorem B3072095 : Blo 2047435 3072095 := bstep (se 1 (by rfl) ⟨2304071, by rfl⟩ : syracuseStep 3072095 = 4608143) B4608143
theorem B2048063 : Blo 2047435 2048063 := bstep (se 1 (by rfl) ⟨1536047, by rfl⟩ : syracuseStep 2048063 = 3072095) B3072095
theorem B3072101 : Blo 2047435 3072101 := bbase (se 4 (by rfl) ⟨288009, by rfl⟩ : syracuseStep 3072101 = 576019) (by norm_num)
theorem B2048067 : Blo 2047435 2048067 := bstep (se 1 (by rfl) ⟨1536050, by rfl⟩ : syracuseStep 2048067 = 3072101) B3072101
theorem B4920925 : Blo 2047435 4920925 := bbase (se 3 (by rfl) ⟨922673, by rfl⟩ : syracuseStep 4920925 = 1845347) (by norm_num)
theorem B6561233 : Blo 2047435 6561233 := bstep (se 2 (by rfl) ⟨2460462, by rfl⟩ : syracuseStep 6561233 = 4920925) B4920925
theorem B4374155 : Blo 2047435 4374155 := bstep (se 1 (by rfl) ⟨3280616, by rfl⟩ : syracuseStep 4374155 = 6561233) B6561233
theorem B2916103 : Blo 2047435 2916103 := bstep (se 1 (by rfl) ⟨2187077, by rfl⟩ : syracuseStep 2916103 = 4374155) B4374155
theorem B3888137 : Blo 2047435 3888137 := bstep (se 2 (by rfl) ⟨1458051, by rfl⟩ : syracuseStep 3888137 = 2916103) B2916103
theorem B2592091 : Blo 2047435 2592091 := bstep (se 1 (by rfl) ⟨1944068, by rfl⟩ : syracuseStep 2592091 = 3888137) B3888137
theorem B3456121 : Blo 2047435 3456121 := bstep (se 2 (by rfl) ⟨1296045, by rfl⟩ : syracuseStep 3456121 = 2592091) B2592091
theorem B4608161 : Blo 2047435 4608161 := bstep (se 2 (by rfl) ⟨1728060, by rfl⟩ : syracuseStep 4608161 = 3456121) B3456121
theorem B3072107 : Blo 2047435 3072107 := bstep (se 1 (by rfl) ⟨2304080, by rfl⟩ : syracuseStep 3072107 = 4608161) B4608161
theorem B2048071 : Blo 2047435 2048071 := bstep (se 1 (by rfl) ⟨1536053, by rfl⟩ : syracuseStep 2048071 = 3072107) B3072107
theorem B2304085 : Blo 2047435 2304085 := bbase (se 8 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 2304085 = 27001) (by norm_num)
theorem B3072113 : Blo 2047435 3072113 := bstep (se 2 (by rfl) ⟨1152042, by rfl⟩ : syracuseStep 3072113 = 2304085) B2304085
theorem B2048075 : Blo 2047435 2048075 := bstep (se 1 (by rfl) ⟨1536056, by rfl⟩ : syracuseStep 2048075 = 3072113) B3072113
theorem B2592101 : Blo 2047435 2592101 := bbase (se 4 (by rfl) ⟨243009, by rfl⟩ : syracuseStep 2592101 = 486019) (by norm_num)
theorem B6912269 : Blo 2047435 6912269 := bstep (se 3 (by rfl) ⟨1296050, by rfl⟩ : syracuseStep 6912269 = 2592101) B2592101
theorem B4608179 : Blo 2047435 4608179 := bstep (se 1 (by rfl) ⟨3456134, by rfl⟩ : syracuseStep 4608179 = 6912269) B6912269
theorem B3072119 : Blo 2047435 3072119 := bstep (se 1 (by rfl) ⟨2304089, by rfl⟩ : syracuseStep 3072119 = 4608179) B4608179
theorem B2048079 : Blo 2047435 2048079 := bstep (se 1 (by rfl) ⟨1536059, by rfl⟩ : syracuseStep 2048079 = 3072119) B3072119
theorem B3072125 : Blo 2047435 3072125 := bbase (se 3 (by rfl) ⟨576023, by rfl⟩ : syracuseStep 3072125 = 1152047) (by norm_num)
theorem B2048083 : Blo 2047435 2048083 := bstep (se 1 (by rfl) ⟨1536062, by rfl⟩ : syracuseStep 2048083 = 3072125) B3072125
theorem B4608197 : Blo 2047435 4608197 := bbase (se 4 (by rfl) ⟨432018, by rfl⟩ : syracuseStep 4608197 = 864037) (by norm_num)
theorem B3072131 : Blo 2047435 3072131 := bstep (se 1 (by rfl) ⟨2304098, by rfl⟩ : syracuseStep 3072131 = 4608197) B4608197
theorem B2048087 : Blo 2047435 2048087 := bstep (se 1 (by rfl) ⟨1536065, by rfl⟩ : syracuseStep 2048087 = 3072131) B3072131
theorem B9976229 : Blo 2047435 9976229 := bbase (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) (by norm_num)
theorem B6650819 : Blo 2047435 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B4433879 : Blo 2047435 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B2955919 : Blo 2047435 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B3941225 : Blo 2047435 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B2627483 : Blo 2047435 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B7006621 : Blo 2047435 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B9342161 : Blo 2047435 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B6228107 : Blo 2047435 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B4152071 : Blo 2047435 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B11072189 : Blo 2047435 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B7381459 : Blo 2047435 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B9841945 : Blo 2047435 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B13122593 : Blo 2047435 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B8748395 : Blo 2047435 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B5832263 : Blo 2047435 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B3888175 : Blo 2047435 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B5184233 : Blo 2047435 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B3456155 : Blo 2047435 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B2304103 : Blo 2047435 2304103 := bstep (se 1 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 2304103 = 3456155) B3456155
theorem B3072137 : Blo 2047435 3072137 := bstep (se 2 (by rfl) ⟨1152051, by rfl⟩ : syracuseStep 3072137 = 2304103) B2304103
theorem B2048091 : Blo 2047435 2048091 := bstep (se 1 (by rfl) ⟨1536068, by rfl⟩ : syracuseStep 2048091 = 3072137) B3072137
theorem B10368485 : Blo 2047435 10368485 := bbase (se 4 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 10368485 = 1944091) (by norm_num)
theorem B6912323 : Blo 2047435 6912323 := bstep (se 1 (by rfl) ⟨5184242, by rfl⟩ : syracuseStep 6912323 = 10368485) B10368485
theorem B4608215 : Blo 2047435 4608215 := bstep (se 1 (by rfl) ⟨3456161, by rfl⟩ : syracuseStep 4608215 = 6912323) B6912323
theorem B3072143 : Blo 2047435 3072143 := bstep (se 1 (by rfl) ⟨2304107, by rfl⟩ : syracuseStep 3072143 = 4608215) B4608215
theorem B2048095 : Blo 2047435 2048095 := bstep (se 1 (by rfl) ⟨1536071, by rfl⟩ : syracuseStep 2048095 = 3072143) B3072143
theorem B3072149 : Blo 2047435 3072149 := bbase (se 6 (by rfl) ⟨72003, by rfl⟩ : syracuseStep 3072149 = 144007) (by norm_num)
theorem B2048099 : Blo 2047435 2048099 := bstep (se 1 (by rfl) ⟨1536074, by rfl⟩ : syracuseStep 2048099 = 3072149) B3072149
theorem B3995021 : Blo 2047435 3995021 := bbase (se 3 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 3995021 = 1498133) (by norm_num)
theorem B2663347 : Blo 2047435 2663347 := bstep (se 1 (by rfl) ⟨1997510, by rfl⟩ : syracuseStep 2663347 = 3995021) B3995021
theorem B3551129 : Blo 2047435 3551129 := bstep (se 2 (by rfl) ⟨1331673, by rfl⟩ : syracuseStep 3551129 = 2663347) B2663347
theorem B2367419 : Blo 2047435 2367419 := bstep (se 1 (by rfl) ⟨1775564, by rfl⟩ : syracuseStep 2367419 = 3551129) B3551129
theorem B25252469 : Blo 2047435 25252469 := bstep (se 5 (by rfl) ⟨1183709, by rfl⟩ : syracuseStep 25252469 = 2367419) B2367419
theorem B16834979 : Blo 2047435 16834979 := bstep (se 1 (by rfl) ⟨12626234, by rfl⟩ : syracuseStep 16834979 = 25252469) B25252469
theorem B44893277 : Blo 2047435 44893277 := bstep (se 3 (by rfl) ⟨8417489, by rfl⟩ : syracuseStep 44893277 = 16834979) B16834979
theorem B29928851 : Blo 2047435 29928851 := bstep (se 1 (by rfl) ⟨22446638, by rfl⟩ : syracuseStep 29928851 = 44893277) B44893277
theorem B19952567 : Blo 2047435 19952567 := bstep (se 1 (by rfl) ⟨14964425, by rfl⟩ : syracuseStep 19952567 = 29928851) B29928851
theorem B13301711 : Blo 2047435 13301711 := bstep (se 1 (by rfl) ⟨9976283, by rfl⟩ : syracuseStep 13301711 = 19952567) B19952567
theorem B8867807 : Blo 2047435 8867807 := bstep (se 1 (by rfl) ⟨6650855, by rfl⟩ : syracuseStep 8867807 = 13301711) B13301711
theorem B5911871 : Blo 2047435 5911871 := bstep (se 1 (by rfl) ⟨4433903, by rfl⟩ : syracuseStep 5911871 = 8867807) B8867807
theorem B63059957 : Blo 2047435 63059957 := bstep (se 5 (by rfl) ⟨2955935, by rfl⟩ : syracuseStep 63059957 = 5911871) B5911871
theorem B42039971 : Blo 2047435 42039971 := bstep (se 1 (by rfl) ⟨31529978, by rfl⟩ : syracuseStep 42039971 = 63059957) B63059957
theorem B28026647 : Blo 2047435 28026647 := bstep (se 1 (by rfl) ⟨21019985, by rfl⟩ : syracuseStep 28026647 = 42039971) B42039971
theorem B18684431 : Blo 2047435 18684431 := bstep (se 1 (by rfl) ⟨14013323, by rfl⟩ : syracuseStep 18684431 = 28026647) B28026647
theorem B12456287 : Blo 2047435 12456287 := bstep (se 1 (by rfl) ⟨9342215, by rfl⟩ : syracuseStep 12456287 = 18684431) B18684431
theorem B8304191 : Blo 2047435 8304191 := bstep (se 1 (by rfl) ⟨6228143, by rfl⟩ : syracuseStep 8304191 = 12456287) B12456287
theorem B5536127 : Blo 2047435 5536127 := bstep (se 1 (by rfl) ⟨4152095, by rfl⟩ : syracuseStep 5536127 = 8304191) B8304191
theorem B3690751 : Blo 2047435 3690751 := bstep (se 1 (by rfl) ⟨2768063, by rfl⟩ : syracuseStep 3690751 = 5536127) B5536127
theorem B4921001 : Blo 2047435 4921001 := bstep (se 2 (by rfl) ⟨1845375, by rfl⟩ : syracuseStep 4921001 = 3690751) B3690751
theorem B3280667 : Blo 2047435 3280667 := bstep (se 1 (by rfl) ⟨2460500, by rfl⟩ : syracuseStep 3280667 = 4921001) B4921001
theorem B8748445 : Blo 2047435 8748445 := bstep (se 3 (by rfl) ⟨1640333, by rfl⟩ : syracuseStep 8748445 = 3280667) B3280667
theorem B11664593 : Blo 2047435 11664593 := bstep (se 2 (by rfl) ⟨4374222, by rfl⟩ : syracuseStep 11664593 = 8748445) B8748445
theorem B7776395 : Blo 2047435 7776395 := bstep (se 1 (by rfl) ⟨5832296, by rfl⟩ : syracuseStep 7776395 = 11664593) B11664593
theorem B5184263 : Blo 2047435 5184263 := bstep (se 1 (by rfl) ⟨3888197, by rfl⟩ : syracuseStep 5184263 = 7776395) B7776395
theorem B3456175 : Blo 2047435 3456175 := bstep (se 1 (by rfl) ⟨2592131, by rfl⟩ : syracuseStep 3456175 = 5184263) B5184263
theorem B4608233 : Blo 2047435 4608233 := bstep (se 2 (by rfl) ⟨1728087, by rfl⟩ : syracuseStep 4608233 = 3456175) B3456175
theorem B3072155 : Blo 2047435 3072155 := bstep (se 1 (by rfl) ⟨2304116, by rfl⟩ : syracuseStep 3072155 = 4608233) B4608233
theorem B2048103 : Blo 2047435 2048103 := bstep (se 1 (by rfl) ⟨1536077, by rfl⟩ : syracuseStep 2048103 = 3072155) B3072155
theorem B2304121 : Blo 2047435 2304121 := bbase (se 2 (by rfl) ⟨864045, by rfl⟩ : syracuseStep 2304121 = 1728091) (by norm_num)
theorem B3072161 : Blo 2047435 3072161 := bstep (se 2 (by rfl) ⟨1152060, by rfl⟩ : syracuseStep 3072161 = 2304121) B2304121
theorem B2048107 : Blo 2047435 2048107 := bstep (se 1 (by rfl) ⟨1536080, by rfl⟩ : syracuseStep 2048107 = 3072161) B3072161
theorem B6074309 : Blo 2047435 6074309 := bbase (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) (by norm_num)
theorem B16198157 : Blo 2047435 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B10798771 : Blo 2047435 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B14398361 : Blo 2047435 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B9598907 : Blo 2047435 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B6399271 : Blo 2047435 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B8532361 : Blo 2047435 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B45505925 : Blo 2047435 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B30337283 : Blo 2047435 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B20224855 : Blo 2047435 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B107865893 : Blo 2047435 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B71910595 : Blo 2047435 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B383523173 : Blo 2047435 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B255682115 : Blo 2047435 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B170454743 : Blo 2047435 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B113636495 : Blo 2047435 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B75757663 : Blo 2047435 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B404040869 : Blo 2047435 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B269360579 : Blo 2047435 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B718294877 : Blo 2047435 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B478863251 : Blo 2047435 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B319242167 : Blo 2047435 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B212828111 : Blo 2047435 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B141885407 : Blo 2047435 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B94590271 : Blo 2047435 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B126120361 : Blo 2047435 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B168160481 : Blo 2047435 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B112106987 : Blo 2047435 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B74737991 : Blo 2047435 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B49825327 : Blo 2047435 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B66433769 : Blo 2047435 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B44289179 : Blo 2047435 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B29526119 : Blo 2047435 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B19684079 : Blo 2047435 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B13122719 : Blo 2047435 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B8748479 : Blo 2047435 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B5832319 : Blo 2047435 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B7776425 : Blo 2047435 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B5184283 : Blo 2047435 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B6912377 : Blo 2047435 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B4608251 : Blo 2047435 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B3072167 : Blo 2047435 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B2048111 : Blo 2047435 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B3072173 : Blo 2047435 3072173 := bbase (se 3 (by rfl) ⟨576032, by rfl⟩ : syracuseStep 3072173 = 1152065) (by norm_num)
theorem B2048115 : Blo 2047435 2048115 := bstep (se 1 (by rfl) ⟨1536086, by rfl⟩ : syracuseStep 2048115 = 3072173) B3072173
theorem B4608269 : Blo 2047435 4608269 := bbase (se 3 (by rfl) ⟨864050, by rfl⟩ : syracuseStep 4608269 = 1728101) (by norm_num)
theorem B3072179 : Blo 2047435 3072179 := bstep (se 1 (by rfl) ⟨2304134, by rfl⟩ : syracuseStep 3072179 = 4608269) B4608269
theorem B2048119 : Blo 2047435 2048119 := bstep (se 1 (by rfl) ⟨1536089, by rfl⟩ : syracuseStep 2048119 = 3072179) B3072179
theorem B2592157 : Blo 2047435 2592157 := bbase (se 3 (by rfl) ⟨486029, by rfl⟩ : syracuseStep 2592157 = 972059) (by norm_num)
theorem B3456209 : Blo 2047435 3456209 := bstep (se 2 (by rfl) ⟨1296078, by rfl⟩ : syracuseStep 3456209 = 2592157) B2592157
theorem B2304139 : Blo 2047435 2304139 := bstep (se 1 (by rfl) ⟨1728104, by rfl⟩ : syracuseStep 2304139 = 3456209) B3456209
theorem B3072185 : Blo 2047435 3072185 := bstep (se 2 (by rfl) ⟨1152069, by rfl⟩ : syracuseStep 3072185 = 2304139) B2304139
theorem B2048123 : Blo 2047435 2048123 := bstep (se 1 (by rfl) ⟨1536092, by rfl⟩ : syracuseStep 2048123 = 3072185) B3072185
theorem B2460529 : Blo 2047435 2460529 := bbase (se 2 (by rfl) ⟨922698, by rfl⟩ : syracuseStep 2460529 = 1845397) (by norm_num)
theorem B3280705 : Blo 2047435 3280705 := bstep (se 2 (by rfl) ⟨1230264, by rfl⟩ : syracuseStep 3280705 = 2460529) B2460529
theorem B17497093 : Blo 2047435 17497093 := bstep (se 4 (by rfl) ⟨1640352, by rfl⟩ : syracuseStep 17497093 = 3280705) B3280705
theorem B23329457 : Blo 2047435 23329457 := bstep (se 2 (by rfl) ⟨8748546, by rfl⟩ : syracuseStep 23329457 = 17497093) B17497093
theorem B15552971 : Blo 2047435 15552971 := bstep (se 1 (by rfl) ⟨11664728, by rfl⟩ : syracuseStep 15552971 = 23329457) B23329457
theorem B10368647 : Blo 2047435 10368647 := bstep (se 1 (by rfl) ⟨7776485, by rfl⟩ : syracuseStep 10368647 = 15552971) B15552971
theorem B6912431 : Blo 2047435 6912431 := bstep (se 1 (by rfl) ⟨5184323, by rfl⟩ : syracuseStep 6912431 = 10368647) B10368647
theorem B4608287 : Blo 2047435 4608287 := bstep (se 1 (by rfl) ⟨3456215, by rfl⟩ : syracuseStep 4608287 = 6912431) B6912431
theorem B3072191 : Blo 2047435 3072191 := bstep (se 1 (by rfl) ⟨2304143, by rfl⟩ : syracuseStep 3072191 = 4608287) B4608287
theorem B2048127 : Blo 2047435 2048127 := bstep (se 1 (by rfl) ⟨1536095, by rfl⟩ : syracuseStep 2048127 = 3072191) B3072191
theorem B3072197 : Blo 2047435 3072197 := bbase (se 4 (by rfl) ⟨288018, by rfl⟩ : syracuseStep 3072197 = 576037) (by norm_num)
theorem B2048131 : Blo 2047435 2048131 := bstep (se 1 (by rfl) ⟨1536098, by rfl⟩ : syracuseStep 2048131 = 3072197) B3072197
theorem B3456229 : Blo 2047435 3456229 := bbase (se 4 (by rfl) ⟨324021, by rfl⟩ : syracuseStep 3456229 = 648043) (by norm_num)
theorem B4608305 : Blo 2047435 4608305 := bstep (se 2 (by rfl) ⟨1728114, by rfl⟩ : syracuseStep 4608305 = 3456229) B3456229
theorem B3072203 : Blo 2047435 3072203 := bstep (se 1 (by rfl) ⟨2304152, by rfl⟩ : syracuseStep 3072203 = 4608305) B4608305
theorem B2048135 : Blo 2047435 2048135 := bstep (se 1 (by rfl) ⟨1536101, by rfl⟩ : syracuseStep 2048135 = 3072203) B3072203
theorem B2304157 : Blo 2047435 2304157 := bbase (se 3 (by rfl) ⟨432029, by rfl⟩ : syracuseStep 2304157 = 864059) (by norm_num)
theorem B3072209 : Blo 2047435 3072209 := bstep (se 2 (by rfl) ⟨1152078, by rfl⟩ : syracuseStep 3072209 = 2304157) B2304157
theorem B2048139 : Blo 2047435 2048139 := bstep (se 1 (by rfl) ⟨1536104, by rfl⟩ : syracuseStep 2048139 = 3072209) B3072209
theorem B6912485 : Blo 2047435 6912485 := bbase (se 4 (by rfl) ⟨648045, by rfl⟩ : syracuseStep 6912485 = 1296091) (by norm_num)
theorem B4608323 : Blo 2047435 4608323 := bstep (se 1 (by rfl) ⟨3456242, by rfl⟩ : syracuseStep 4608323 = 6912485) B6912485
theorem B3072215 : Blo 2047435 3072215 := bstep (se 1 (by rfl) ⟨2304161, by rfl⟩ : syracuseStep 3072215 = 4608323) B4608323
theorem B2048143 : Blo 2047435 2048143 := bstep (se 1 (by rfl) ⟨1536107, by rfl⟩ : syracuseStep 2048143 = 3072215) B3072215
theorem B3072221 : Blo 2047435 3072221 := bbase (se 3 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 3072221 = 1152083) (by norm_num)
theorem B2048147 : Blo 2047435 2048147 := bstep (se 1 (by rfl) ⟨1536110, by rfl⟩ : syracuseStep 2048147 = 3072221) B3072221
theorem B4608341 : Blo 2047435 4608341 := bbase (se 10 (by rfl) ⟨6750, by rfl⟩ : syracuseStep 4608341 = 13501) (by norm_num)
theorem B3072227 : Blo 2047435 3072227 := bstep (se 1 (by rfl) ⟨2304170, by rfl⟩ : syracuseStep 3072227 = 4608341) B4608341
theorem B2048151 : Blo 2047435 2048151 := bstep (se 1 (by rfl) ⟨1536113, by rfl⟩ : syracuseStep 2048151 = 3072227) B3072227
theorem B2367481 : Blo 2047435 2367481 := bbase (se 2 (by rfl) ⟨887805, by rfl⟩ : syracuseStep 2367481 = 1775611) (by norm_num)
theorem B3156641 : Blo 2047435 3156641 := bstep (se 2 (by rfl) ⟨1183740, by rfl⟩ : syracuseStep 3156641 = 2367481) B2367481
theorem B2104427 : Blo 2047435 2104427 := bstep (se 1 (by rfl) ⟨1578320, by rfl⟩ : syracuseStep 2104427 = 3156641) B3156641
theorem B5611805 : Blo 2047435 5611805 := bstep (se 3 (by rfl) ⟨1052213, by rfl⟩ : syracuseStep 5611805 = 2104427) B2104427
theorem B3741203 : Blo 2047435 3741203 := bstep (se 1 (by rfl) ⟨2805902, by rfl⟩ : syracuseStep 3741203 = 5611805) B5611805
theorem B2494135 : Blo 2047435 2494135 := bstep (se 1 (by rfl) ⟨1870601, by rfl⟩ : syracuseStep 2494135 = 3741203) B3741203
theorem B13302053 : Blo 2047435 13302053 := bstep (se 4 (by rfl) ⟨1247067, by rfl⟩ : syracuseStep 13302053 = 2494135) B2494135
theorem B8868035 : Blo 2047435 8868035 := bstep (se 1 (by rfl) ⟨6651026, by rfl⟩ : syracuseStep 8868035 = 13302053) B13302053
theorem B5912023 : Blo 2047435 5912023 := bstep (se 1 (by rfl) ⟨4434017, by rfl⟩ : syracuseStep 5912023 = 8868035) B8868035
theorem B7882697 : Blo 2047435 7882697 := bstep (se 2 (by rfl) ⟨2956011, by rfl⟩ : syracuseStep 7882697 = 5912023) B5912023
theorem B5255131 : Blo 2047435 5255131 := bstep (se 1 (by rfl) ⟨3941348, by rfl⟩ : syracuseStep 5255131 = 7882697) B7882697
theorem B7006841 : Blo 2047435 7006841 := bstep (se 2 (by rfl) ⟨2627565, by rfl⟩ : syracuseStep 7006841 = 5255131) B5255131
theorem B4671227 : Blo 2047435 4671227 := bstep (se 1 (by rfl) ⟨3503420, by rfl⟩ : syracuseStep 4671227 = 7006841) B7006841
theorem B12456605 : Blo 2047435 12456605 := bstep (se 3 (by rfl) ⟨2335613, by rfl⟩ : syracuseStep 12456605 = 4671227) B4671227
theorem B8304403 : Blo 2047435 8304403 := bstep (se 1 (by rfl) ⟨6228302, by rfl⟩ : syracuseStep 8304403 = 12456605) B12456605
theorem B11072537 : Blo 2047435 11072537 := bstep (se 2 (by rfl) ⟨4152201, by rfl⟩ : syracuseStep 11072537 = 8304403) B8304403
theorem B7381691 : Blo 2047435 7381691 := bstep (se 1 (by rfl) ⟨5536268, by rfl⟩ : syracuseStep 7381691 = 11072537) B11072537
theorem B4921127 : Blo 2047435 4921127 := bstep (se 1 (by rfl) ⟨3690845, by rfl⟩ : syracuseStep 4921127 = 7381691) B7381691
theorem B3280751 : Blo 2047435 3280751 := bstep (se 1 (by rfl) ⟨2460563, by rfl⟩ : syracuseStep 3280751 = 4921127) B4921127
theorem B2187167 : Blo 2047435 2187167 := bstep (se 1 (by rfl) ⟨1640375, by rfl⟩ : syracuseStep 2187167 = 3280751) B3280751
theorem B5832445 : Blo 2047435 5832445 := bstep (se 3 (by rfl) ⟨1093583, by rfl⟩ : syracuseStep 5832445 = 2187167) B2187167
theorem B7776593 : Blo 2047435 7776593 := bstep (se 2 (by rfl) ⟨2916222, by rfl⟩ : syracuseStep 7776593 = 5832445) B5832445
theorem B5184395 : Blo 2047435 5184395 := bstep (se 1 (by rfl) ⟨3888296, by rfl⟩ : syracuseStep 5184395 = 7776593) B7776593
theorem B3456263 : Blo 2047435 3456263 := bstep (se 1 (by rfl) ⟨2592197, by rfl⟩ : syracuseStep 3456263 = 5184395) B5184395
theorem B2304175 : Blo 2047435 2304175 := bstep (se 1 (by rfl) ⟨1728131, by rfl⟩ : syracuseStep 2304175 = 3456263) B3456263
theorem B3072233 : Blo 2047435 3072233 := bstep (se 2 (by rfl) ⟨1152087, by rfl⟩ : syracuseStep 3072233 = 2304175) B2304175
theorem B2048155 : Blo 2047435 2048155 := bstep (se 1 (by rfl) ⟨1536116, by rfl⟩ : syracuseStep 2048155 = 3072233) B3072233
theorem B5536277 : Blo 2047435 5536277 := bbase (se 6 (by rfl) ⟨129756, by rfl⟩ : syracuseStep 5536277 = 259513) (by norm_num)
theorem B3690851 : Blo 2047435 3690851 := bstep (se 1 (by rfl) ⟨2768138, by rfl⟩ : syracuseStep 3690851 = 5536277) B5536277
theorem B39369077 : Blo 2047435 39369077 := bstep (se 5 (by rfl) ⟨1845425, by rfl⟩ : syracuseStep 39369077 = 3690851) B3690851
theorem B26246051 : Blo 2047435 26246051 := bstep (se 1 (by rfl) ⟨19684538, by rfl⟩ : syracuseStep 26246051 = 39369077) B39369077
theorem B17497367 : Blo 2047435 17497367 := bstep (se 1 (by rfl) ⟨13123025, by rfl⟩ : syracuseStep 17497367 = 26246051) B26246051
theorem B11664911 : Blo 2047435 11664911 := bstep (se 1 (by rfl) ⟨8748683, by rfl⟩ : syracuseStep 11664911 = 17497367) B17497367
theorem B7776607 : Blo 2047435 7776607 := bstep (se 1 (by rfl) ⟨5832455, by rfl⟩ : syracuseStep 7776607 = 11664911) B11664911
theorem B10368809 : Blo 2047435 10368809 := bstep (se 2 (by rfl) ⟨3888303, by rfl⟩ : syracuseStep 10368809 = 7776607) B7776607
theorem B6912539 : Blo 2047435 6912539 := bstep (se 1 (by rfl) ⟨5184404, by rfl⟩ : syracuseStep 6912539 = 10368809) B10368809
theorem B4608359 : Blo 2047435 4608359 := bstep (se 1 (by rfl) ⟨3456269, by rfl⟩ : syracuseStep 4608359 = 6912539) B6912539
theorem B3072239 : Blo 2047435 3072239 := bstep (se 1 (by rfl) ⟨2304179, by rfl⟩ : syracuseStep 3072239 = 4608359) B4608359
theorem B2048159 : Blo 2047435 2048159 := bstep (se 1 (by rfl) ⟨1536119, by rfl⟩ : syracuseStep 2048159 = 3072239) B3072239
theorem B3072245 : Blo 2047435 3072245 := bbase (se 5 (by rfl) ⟨144011, by rfl⟩ : syracuseStep 3072245 = 288023) (by norm_num)
theorem B2048163 : Blo 2047435 2048163 := bstep (se 1 (by rfl) ⟨1536122, by rfl⟩ : syracuseStep 2048163 = 3072245) B3072245
theorem B4671253 : Blo 2047435 4671253 := bbase (se 6 (by rfl) ⟨109482, by rfl⟩ : syracuseStep 4671253 = 218965) (by norm_num)
theorem B6228337 : Blo 2047435 6228337 := bstep (se 2 (by rfl) ⟨2335626, by rfl⟩ : syracuseStep 6228337 = 4671253) B4671253
theorem B8304449 : Blo 2047435 8304449 := bstep (se 2 (by rfl) ⟨3114168, by rfl⟩ : syracuseStep 8304449 = 6228337) B6228337
theorem B22145197 : Blo 2047435 22145197 := bstep (se 3 (by rfl) ⟨4152224, by rfl⟩ : syracuseStep 22145197 = 8304449) B8304449
theorem B29526929 : Blo 2047435 29526929 := bstep (se 2 (by rfl) ⟨11072598, by rfl⟩ : syracuseStep 29526929 = 22145197) B22145197
theorem B19684619 : Blo 2047435 19684619 := bstep (se 1 (by rfl) ⟨14763464, by rfl⟩ : syracuseStep 19684619 = 29526929) B29526929
theorem B13123079 : Blo 2047435 13123079 := bstep (se 1 (by rfl) ⟨9842309, by rfl⟩ : syracuseStep 13123079 = 19684619) B19684619
theorem B8748719 : Blo 2047435 8748719 := bstep (se 1 (by rfl) ⟨6561539, by rfl⟩ : syracuseStep 8748719 = 13123079) B13123079
theorem B5832479 : Blo 2047435 5832479 := bstep (se 1 (by rfl) ⟨4374359, by rfl⟩ : syracuseStep 5832479 = 8748719) B8748719
theorem B3888319 : Blo 2047435 3888319 := bstep (se 1 (by rfl) ⟨2916239, by rfl⟩ : syracuseStep 3888319 = 5832479) B5832479
theorem B5184425 : Blo 2047435 5184425 := bstep (se 2 (by rfl) ⟨1944159, by rfl⟩ : syracuseStep 5184425 = 3888319) B3888319
theorem B3456283 : Blo 2047435 3456283 := bstep (se 1 (by rfl) ⟨2592212, by rfl⟩ : syracuseStep 3456283 = 5184425) B5184425
theorem B4608377 : Blo 2047435 4608377 := bstep (se 2 (by rfl) ⟨1728141, by rfl⟩ : syracuseStep 4608377 = 3456283) B3456283
theorem B3072251 : Blo 2047435 3072251 := bstep (se 1 (by rfl) ⟨2304188, by rfl⟩ : syracuseStep 3072251 = 4608377) B4608377
theorem B2048167 : Blo 2047435 2048167 := bstep (se 1 (by rfl) ⟨1536125, by rfl⟩ : syracuseStep 2048167 = 3072251) B3072251
theorem B2304193 : Blo 2047435 2304193 := bbase (se 2 (by rfl) ⟨864072, by rfl⟩ : syracuseStep 2304193 = 1728145) (by norm_num)
theorem B3072257 : Blo 2047435 3072257 := bstep (se 2 (by rfl) ⟨1152096, by rfl⟩ : syracuseStep 3072257 = 2304193) B2304193
theorem B2048171 : Blo 2047435 2048171 := bstep (se 1 (by rfl) ⟨1536128, by rfl⟩ : syracuseStep 2048171 = 3072257) B3072257
theorem B5184445 : Blo 2047435 5184445 := bbase (se 3 (by rfl) ⟨972083, by rfl⟩ : syracuseStep 5184445 = 1944167) (by norm_num)
theorem B6912593 : Blo 2047435 6912593 := bstep (se 2 (by rfl) ⟨2592222, by rfl⟩ : syracuseStep 6912593 = 5184445) B5184445
theorem B4608395 : Blo 2047435 4608395 := bstep (se 1 (by rfl) ⟨3456296, by rfl⟩ : syracuseStep 4608395 = 6912593) B6912593
theorem B3072263 : Blo 2047435 3072263 := bstep (se 1 (by rfl) ⟨2304197, by rfl⟩ : syracuseStep 3072263 = 4608395) B4608395
theorem B2048175 : Blo 2047435 2048175 := bstep (se 1 (by rfl) ⟨1536131, by rfl⟩ : syracuseStep 2048175 = 3072263) B3072263
theorem B3072269 : Blo 2047435 3072269 := bbase (se 3 (by rfl) ⟨576050, by rfl⟩ : syracuseStep 3072269 = 1152101) (by norm_num)
theorem B2048179 : Blo 2047435 2048179 := bstep (se 1 (by rfl) ⟨1536134, by rfl⟩ : syracuseStep 2048179 = 3072269) B3072269
theorem B4608413 : Blo 2047435 4608413 := bbase (se 3 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 4608413 = 1728155) (by norm_num)
theorem B3072275 : Blo 2047435 3072275 := bstep (se 1 (by rfl) ⟨2304206, by rfl⟩ : syracuseStep 3072275 = 4608413) B4608413
theorem B2048183 : Blo 2047435 2048183 := bstep (se 1 (by rfl) ⟨1536137, by rfl⟩ : syracuseStep 2048183 = 3072275) B3072275
theorem B3456317 : Blo 2047435 3456317 := bbase (se 3 (by rfl) ⟨648059, by rfl⟩ : syracuseStep 3456317 = 1296119) (by norm_num)
theorem B2304211 : Blo 2047435 2304211 := bstep (se 1 (by rfl) ⟨1728158, by rfl⟩ : syracuseStep 2304211 = 3456317) B3456317
theorem B3072281 : Blo 2047435 3072281 := bstep (se 2 (by rfl) ⟨1152105, by rfl⟩ : syracuseStep 3072281 = 2304211) B2304211
theorem B2048187 : Blo 2047435 2048187 := bstep (se 1 (by rfl) ⟨1536140, by rfl⟩ : syracuseStep 2048187 = 3072281) B3072281
theorem B2187205 : Blo 2047435 2187205 := bbase (se 4 (by rfl) ⟨205050, by rfl⟩ : syracuseStep 2187205 = 410101) (by norm_num)
theorem B11665093 : Blo 2047435 11665093 := bstep (se 4 (by rfl) ⟨1093602, by rfl⟩ : syracuseStep 11665093 = 2187205) B2187205
theorem B15553457 : Blo 2047435 15553457 := bstep (se 2 (by rfl) ⟨5832546, by rfl⟩ : syracuseStep 15553457 = 11665093) B11665093
theorem B10368971 : Blo 2047435 10368971 := bstep (se 1 (by rfl) ⟨7776728, by rfl⟩ : syracuseStep 10368971 = 15553457) B15553457
theorem B6912647 : Blo 2047435 6912647 := bstep (se 1 (by rfl) ⟨5184485, by rfl⟩ : syracuseStep 6912647 = 10368971) B10368971
theorem B4608431 : Blo 2047435 4608431 := bstep (se 1 (by rfl) ⟨3456323, by rfl⟩ : syracuseStep 4608431 = 6912647) B6912647
theorem B3072287 : Blo 2047435 3072287 := bstep (se 1 (by rfl) ⟨2304215, by rfl⟩ : syracuseStep 3072287 = 4608431) B4608431
theorem B2048191 : Blo 2047435 2048191 := bstep (se 1 (by rfl) ⟨1536143, by rfl⟩ : syracuseStep 2048191 = 3072287) B3072287
theorem B3072293 : Blo 2047435 3072293 := bbase (se 4 (by rfl) ⟨288027, by rfl⟩ : syracuseStep 3072293 = 576055) (by norm_num)
theorem B2048195 : Blo 2047435 2048195 := bstep (se 1 (by rfl) ⟨1536146, by rfl⟩ : syracuseStep 2048195 = 3072293) B3072293
theorem B2592253 : Blo 2047435 2592253 := bbase (se 3 (by rfl) ⟨486047, by rfl⟩ : syracuseStep 2592253 = 972095) (by norm_num)
theorem B3456337 : Blo 2047435 3456337 := bstep (se 2 (by rfl) ⟨1296126, by rfl⟩ : syracuseStep 3456337 = 2592253) B2592253
theorem B4608449 : Blo 2047435 4608449 := bstep (se 2 (by rfl) ⟨1728168, by rfl⟩ : syracuseStep 4608449 = 3456337) B3456337
theorem B3072299 : Blo 2047435 3072299 := bstep (se 1 (by rfl) ⟨2304224, by rfl⟩ : syracuseStep 3072299 = 4608449) B4608449
theorem B2048199 : Blo 2047435 2048199 := bstep (se 1 (by rfl) ⟨1536149, by rfl⟩ : syracuseStep 2048199 = 3072299) B3072299
theorem B2304229 : Blo 2047435 2304229 := bbase (se 4 (by rfl) ⟨216021, by rfl⟩ : syracuseStep 2304229 = 432043) (by norm_num)
theorem B3072305 : Blo 2047435 3072305 := bstep (se 2 (by rfl) ⟨1152114, by rfl⟩ : syracuseStep 3072305 = 2304229) B2304229
theorem B2048203 : Blo 2047435 2048203 := bstep (se 1 (by rfl) ⟨1536152, by rfl⟩ : syracuseStep 2048203 = 3072305) B3072305
theorem B4374445 : Blo 2047435 4374445 := bbase (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) (by norm_num)
theorem B5832593 : Blo 2047435 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B3888395 : Blo 2047435 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B2592263 : Blo 2047435 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B6912701 : Blo 2047435 6912701 := bstep (se 3 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 6912701 = 2592263) B2592263
theorem B4608467 : Blo 2047435 4608467 := bstep (se 1 (by rfl) ⟨3456350, by rfl⟩ : syracuseStep 4608467 = 6912701) B6912701
theorem B3072311 : Blo 2047435 3072311 := bstep (se 1 (by rfl) ⟨2304233, by rfl⟩ : syracuseStep 3072311 = 4608467) B4608467
theorem B2048207 : Blo 2047435 2048207 := bstep (se 1 (by rfl) ⟨1536155, by rfl⟩ : syracuseStep 2048207 = 3072311) B3072311
theorem B3072317 : Blo 2047435 3072317 := bbase (se 3 (by rfl) ⟨576059, by rfl⟩ : syracuseStep 3072317 = 1152119) (by norm_num)
theorem B2048211 : Blo 2047435 2048211 := bstep (se 1 (by rfl) ⟨1536158, by rfl⟩ : syracuseStep 2048211 = 3072317) B3072317
theorem B4608485 : Blo 2047435 4608485 := bbase (se 4 (by rfl) ⟨432045, by rfl⟩ : syracuseStep 4608485 = 864091) (by norm_num)
theorem B3072323 : Blo 2047435 3072323 := bstep (se 1 (by rfl) ⟨2304242, by rfl⟩ : syracuseStep 3072323 = 4608485) B4608485
theorem B2048215 : Blo 2047435 2048215 := bstep (se 1 (by rfl) ⟨1536161, by rfl⟩ : syracuseStep 2048215 = 3072323) B3072323
theorem B5184557 : Blo 2047435 5184557 := bbase (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) (by norm_num)
theorem B3456371 : Blo 2047435 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B2304247 : Blo 2047435 2304247 := bstep (se 1 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 2304247 = 3456371) B3456371
theorem B3072329 : Blo 2047435 3072329 := bstep (se 2 (by rfl) ⟨1152123, by rfl⟩ : syracuseStep 3072329 = 2304247) B2304247
theorem B2048219 : Blo 2047435 2048219 := bstep (se 1 (by rfl) ⟨1536164, by rfl⟩ : syracuseStep 2048219 = 3072329) B3072329
theorem B8304677 : Blo 2047435 8304677 := bbase (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) (by norm_num)
theorem B5536451 : Blo 2047435 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B14763869 : Blo 2047435 14763869 := bstep (se 3 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 14763869 = 5536451) B5536451
theorem B9842579 : Blo 2047435 9842579 := bstep (se 1 (by rfl) ⟨7381934, by rfl⟩ : syracuseStep 9842579 = 14763869) B14763869
theorem B6561719 : Blo 2047435 6561719 := bstep (se 1 (by rfl) ⟨4921289, by rfl⟩ : syracuseStep 6561719 = 9842579) B9842579
theorem B4374479 : Blo 2047435 4374479 := bstep (se 1 (by rfl) ⟨3280859, by rfl⟩ : syracuseStep 4374479 = 6561719) B6561719
theorem B2916319 : Blo 2047435 2916319 := bstep (se 1 (by rfl) ⟨2187239, by rfl⟩ : syracuseStep 2916319 = 4374479) B4374479
theorem B3888425 : Blo 2047435 3888425 := bstep (se 2 (by rfl) ⟨1458159, by rfl⟩ : syracuseStep 3888425 = 2916319) B2916319
theorem B10369133 : Blo 2047435 10369133 := bstep (se 3 (by rfl) ⟨1944212, by rfl⟩ : syracuseStep 10369133 = 3888425) B3888425
theorem B6912755 : Blo 2047435 6912755 := bstep (se 1 (by rfl) ⟨5184566, by rfl⟩ : syracuseStep 6912755 = 10369133) B10369133
theorem B4608503 : Blo 2047435 4608503 := bstep (se 1 (by rfl) ⟨3456377, by rfl⟩ : syracuseStep 4608503 = 6912755) B6912755
theorem B3072335 : Blo 2047435 3072335 := bstep (se 1 (by rfl) ⟨2304251, by rfl⟩ : syracuseStep 3072335 = 4608503) B4608503
theorem B2048223 : Blo 2047435 2048223 := bstep (se 1 (by rfl) ⟨1536167, by rfl⟩ : syracuseStep 2048223 = 3072335) B3072335
theorem B3072341 : Blo 2047435 3072341 := bbase (se 10 (by rfl) ⟨4500, by rfl⟩ : syracuseStep 3072341 = 9001) (by norm_num)
theorem B2048227 : Blo 2047435 2048227 := bstep (se 1 (by rfl) ⟨1536170, by rfl⟩ : syracuseStep 2048227 = 3072341) B3072341
theorem B5832661 : Blo 2047435 5832661 := bbase (se 7 (by rfl) ⟨68351, by rfl⟩ : syracuseStep 5832661 = 136703) (by norm_num)
theorem B7776881 : Blo 2047435 7776881 := bstep (se 2 (by rfl) ⟨2916330, by rfl⟩ : syracuseStep 7776881 = 5832661) B5832661
theorem B5184587 : Blo 2047435 5184587 := bstep (se 1 (by rfl) ⟨3888440, by rfl⟩ : syracuseStep 5184587 = 7776881) B7776881
theorem B3456391 : Blo 2047435 3456391 := bstep (se 1 (by rfl) ⟨2592293, by rfl⟩ : syracuseStep 3456391 = 5184587) B5184587
theorem B4608521 : Blo 2047435 4608521 := bstep (se 2 (by rfl) ⟨1728195, by rfl⟩ : syracuseStep 4608521 = 3456391) B3456391
theorem B3072347 : Blo 2047435 3072347 := bstep (se 1 (by rfl) ⟨2304260, by rfl⟩ : syracuseStep 3072347 = 4608521) B4608521
theorem B2048231 : Blo 2047435 2048231 := bstep (se 1 (by rfl) ⟨1536173, by rfl⟩ : syracuseStep 2048231 = 3072347) B3072347
theorem B2304265 : Blo 2047435 2304265 := bbase (se 2 (by rfl) ⟨864099, by rfl⟩ : syracuseStep 2304265 = 1728199) (by norm_num)
theorem B3072353 : Blo 2047435 3072353 := bstep (se 2 (by rfl) ⟨1152132, by rfl⟩ : syracuseStep 3072353 = 2304265) B2304265
theorem B2048235 : Blo 2047435 2048235 := bstep (se 1 (by rfl) ⟨1536176, by rfl⟩ : syracuseStep 2048235 = 3072353) B3072353
theorem B28028501 : Blo 2047435 28028501 := bbase (se 8 (by rfl) ⟨164229, by rfl⟩ : syracuseStep 28028501 = 328459) (by norm_num)
theorem B18685667 : Blo 2047435 18685667 := bstep (se 1 (by rfl) ⟨14014250, by rfl⟩ : syracuseStep 18685667 = 28028501) B28028501
theorem B12457111 : Blo 2047435 12457111 := bstep (se 1 (by rfl) ⟨9342833, by rfl⟩ : syracuseStep 12457111 = 18685667) B18685667
theorem B16609481 : Blo 2047435 16609481 := bstep (se 2 (by rfl) ⟨6228555, by rfl⟩ : syracuseStep 16609481 = 12457111) B12457111
theorem B11072987 : Blo 2047435 11072987 := bstep (se 1 (by rfl) ⟨8304740, by rfl⟩ : syracuseStep 11072987 = 16609481) B16609481
theorem B7381991 : Blo 2047435 7381991 := bstep (se 1 (by rfl) ⟨5536493, by rfl⟩ : syracuseStep 7381991 = 11072987) B11072987
theorem B4921327 : Blo 2047435 4921327 := bstep (se 1 (by rfl) ⟨3690995, by rfl⟩ : syracuseStep 4921327 = 7381991) B7381991
theorem B26247077 : Blo 2047435 26247077 := bstep (se 4 (by rfl) ⟨2460663, by rfl⟩ : syracuseStep 26247077 = 4921327) B4921327
theorem B17498051 : Blo 2047435 17498051 := bstep (se 1 (by rfl) ⟨13123538, by rfl⟩ : syracuseStep 17498051 = 26247077) B26247077
theorem B11665367 : Blo 2047435 11665367 := bstep (se 1 (by rfl) ⟨8749025, by rfl⟩ : syracuseStep 11665367 = 17498051) B17498051
theorem B7776911 : Blo 2047435 7776911 := bstep (se 1 (by rfl) ⟨5832683, by rfl⟩ : syracuseStep 7776911 = 11665367) B11665367
theorem B5184607 : Blo 2047435 5184607 := bstep (se 1 (by rfl) ⟨3888455, by rfl⟩ : syracuseStep 5184607 = 7776911) B7776911
theorem B6912809 : Blo 2047435 6912809 := bstep (se 2 (by rfl) ⟨2592303, by rfl⟩ : syracuseStep 6912809 = 5184607) B5184607
theorem B4608539 : Blo 2047435 4608539 := bstep (se 1 (by rfl) ⟨3456404, by rfl⟩ : syracuseStep 4608539 = 6912809) B6912809
theorem B3072359 : Blo 2047435 3072359 := bstep (se 1 (by rfl) ⟨2304269, by rfl⟩ : syracuseStep 3072359 = 4608539) B4608539
theorem B2048239 : Blo 2047435 2048239 := bstep (se 1 (by rfl) ⟨1536179, by rfl⟩ : syracuseStep 2048239 = 3072359) B3072359
theorem B3072365 : Blo 2047435 3072365 := bbase (se 3 (by rfl) ⟨576068, by rfl⟩ : syracuseStep 3072365 = 1152137) (by norm_num)
theorem B2048243 : Blo 2047435 2048243 := bstep (se 1 (by rfl) ⟨1536182, by rfl⟩ : syracuseStep 2048243 = 3072365) B3072365
theorem B4608557 : Blo 2047435 4608557 := bbase (se 3 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 4608557 = 1728209) (by norm_num)
theorem B3072371 : Blo 2047435 3072371 := bstep (se 1 (by rfl) ⟨2304278, by rfl⟩ : syracuseStep 3072371 = 4608557) B4608557
theorem B2048247 : Blo 2047435 2048247 := bstep (se 1 (by rfl) ⟨1536185, by rfl⟩ : syracuseStep 2048247 = 3072371) B3072371
theorem B19685429 : Blo 2047435 19685429 := bbase (se 5 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 19685429 = 1845509) (by norm_num)
theorem B13123619 : Blo 2047435 13123619 := bstep (se 1 (by rfl) ⟨9842714, by rfl⟩ : syracuseStep 13123619 = 19685429) B19685429
theorem B8749079 : Blo 2047435 8749079 := bstep (se 1 (by rfl) ⟨6561809, by rfl⟩ : syracuseStep 8749079 = 13123619) B13123619
theorem B5832719 : Blo 2047435 5832719 := bstep (se 1 (by rfl) ⟨4374539, by rfl⟩ : syracuseStep 5832719 = 8749079) B8749079
theorem B3888479 : Blo 2047435 3888479 := bstep (se 1 (by rfl) ⟨2916359, by rfl⟩ : syracuseStep 3888479 = 5832719) B5832719
theorem B2592319 : Blo 2047435 2592319 := bstep (se 1 (by rfl) ⟨1944239, by rfl⟩ : syracuseStep 2592319 = 3888479) B3888479
theorem B3456425 : Blo 2047435 3456425 := bstep (se 2 (by rfl) ⟨1296159, by rfl⟩ : syracuseStep 3456425 = 2592319) B2592319
theorem B2304283 : Blo 2047435 2304283 := bstep (se 1 (by rfl) ⟨1728212, by rfl⟩ : syracuseStep 2304283 = 3456425) B3456425
theorem B3072377 : Blo 2047435 3072377 := bstep (se 2 (by rfl) ⟨1152141, by rfl⟩ : syracuseStep 3072377 = 2304283) B2304283
theorem B2048251 : Blo 2047435 2048251 := bstep (se 1 (by rfl) ⟨1536188, by rfl⟩ : syracuseStep 2048251 = 3072377) B3072377
theorem B34996373 : Blo 2047435 34996373 := bbase (se 6 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 34996373 = 1640455) (by norm_num)
theorem B23330915 : Blo 2047435 23330915 := bstep (se 1 (by rfl) ⟨17498186, by rfl⟩ : syracuseStep 23330915 = 34996373) B34996373
theorem B15553943 : Blo 2047435 15553943 := bstep (se 1 (by rfl) ⟨11665457, by rfl⟩ : syracuseStep 15553943 = 23330915) B23330915
theorem B10369295 : Blo 2047435 10369295 := bstep (se 1 (by rfl) ⟨7776971, by rfl⟩ : syracuseStep 10369295 = 15553943) B15553943
theorem B6912863 : Blo 2047435 6912863 := bstep (se 1 (by rfl) ⟨5184647, by rfl⟩ : syracuseStep 6912863 = 10369295) B10369295
theorem B4608575 : Blo 2047435 4608575 := bstep (se 1 (by rfl) ⟨3456431, by rfl⟩ : syracuseStep 4608575 = 6912863) B6912863
theorem B3072383 : Blo 2047435 3072383 := bstep (se 1 (by rfl) ⟨2304287, by rfl⟩ : syracuseStep 3072383 = 4608575) B4608575
theorem B2048255 : Blo 2047435 2048255 := bstep (se 1 (by rfl) ⟨1536191, by rfl⟩ : syracuseStep 2048255 = 3072383) B3072383
theorem B3072389 : Blo 2047435 3072389 := bbase (se 4 (by rfl) ⟨288036, by rfl⟩ : syracuseStep 3072389 = 576073) (by norm_num)
theorem B2048259 : Blo 2047435 2048259 := bstep (se 1 (by rfl) ⟨1536194, by rfl⟩ : syracuseStep 2048259 = 3072389) B3072389
theorem B3456445 : Blo 2047435 3456445 := bbase (se 3 (by rfl) ⟨648083, by rfl⟩ : syracuseStep 3456445 = 1296167) (by norm_num)
theorem B4608593 : Blo 2047435 4608593 := bstep (se 2 (by rfl) ⟨1728222, by rfl⟩ : syracuseStep 4608593 = 3456445) B3456445
theorem B3072395 : Blo 2047435 3072395 := bstep (se 1 (by rfl) ⟨2304296, by rfl⟩ : syracuseStep 3072395 = 4608593) B4608593
theorem B2048263 : Blo 2047435 2048263 := bstep (se 1 (by rfl) ⟨1536197, by rfl⟩ : syracuseStep 2048263 = 3072395) B3072395
theorem B2304301 : Blo 2047435 2304301 := bbase (se 3 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 2304301 = 864113) (by norm_num)
theorem B3072401 : Blo 2047435 3072401 := bstep (se 2 (by rfl) ⟨1152150, by rfl⟩ : syracuseStep 3072401 = 2304301) B2304301
theorem B2048267 : Blo 2047435 2048267 := bstep (se 1 (by rfl) ⟨1536200, by rfl⟩ : syracuseStep 2048267 = 3072401) B3072401
theorem B6912917 : Blo 2047435 6912917 := bbase (se 6 (by rfl) ⟨162021, by rfl⟩ : syracuseStep 6912917 = 324043) (by norm_num)
theorem B4608611 : Blo 2047435 4608611 := bstep (se 1 (by rfl) ⟨3456458, by rfl⟩ : syracuseStep 4608611 = 6912917) B6912917
theorem B3072407 : Blo 2047435 3072407 := bstep (se 1 (by rfl) ⟨2304305, by rfl⟩ : syracuseStep 3072407 = 4608611) B4608611
theorem B2048271 : Blo 2047435 2048271 := bstep (se 1 (by rfl) ⟨1536203, by rfl⟩ : syracuseStep 2048271 = 3072407) B3072407
theorem B3072413 : Blo 2047435 3072413 := bbase (se 3 (by rfl) ⟨576077, by rfl⟩ : syracuseStep 3072413 = 1152155) (by norm_num)
theorem B2048275 : Blo 2047435 2048275 := bstep (se 1 (by rfl) ⟨1536206, by rfl⟩ : syracuseStep 2048275 = 3072413) B3072413
theorem B4608629 : Blo 2047435 4608629 := bbase (se 5 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 4608629 = 432059) (by norm_num)
theorem B3072419 : Blo 2047435 3072419 := bstep (se 1 (by rfl) ⟨2304314, by rfl⟩ : syracuseStep 3072419 = 4608629) B4608629
theorem B2048279 : Blo 2047435 2048279 := bstep (se 1 (by rfl) ⟨1536209, by rfl⟩ : syracuseStep 2048279 = 3072419) B3072419
theorem B5536613 : Blo 2047435 5536613 := bbase (se 4 (by rfl) ⟨519057, by rfl⟩ : syracuseStep 5536613 = 1038115) (by norm_num)
theorem B14764301 : Blo 2047435 14764301 := bstep (se 3 (by rfl) ⟨2768306, by rfl⟩ : syracuseStep 14764301 = 5536613) B5536613
theorem B9842867 : Blo 2047435 9842867 := bstep (se 1 (by rfl) ⟨7382150, by rfl⟩ : syracuseStep 9842867 = 14764301) B14764301
theorem B6561911 : Blo 2047435 6561911 := bstep (se 1 (by rfl) ⟨4921433, by rfl⟩ : syracuseStep 6561911 = 9842867) B9842867
theorem B17498429 : Blo 2047435 17498429 := bstep (se 3 (by rfl) ⟨3280955, by rfl⟩ : syracuseStep 17498429 = 6561911) B6561911
theorem B11665619 : Blo 2047435 11665619 := bstep (se 1 (by rfl) ⟨8749214, by rfl⟩ : syracuseStep 11665619 = 17498429) B17498429
theorem B7777079 : Blo 2047435 7777079 := bstep (se 1 (by rfl) ⟨5832809, by rfl⟩ : syracuseStep 7777079 = 11665619) B11665619
theorem B5184719 : Blo 2047435 5184719 := bstep (se 1 (by rfl) ⟨3888539, by rfl⟩ : syracuseStep 5184719 = 7777079) B7777079
theorem B3456479 : Blo 2047435 3456479 := bstep (se 1 (by rfl) ⟨2592359, by rfl⟩ : syracuseStep 3456479 = 5184719) B5184719
theorem B2304319 : Blo 2047435 2304319 := bstep (se 1 (by rfl) ⟨1728239, by rfl⟩ : syracuseStep 2304319 = 3456479) B3456479
theorem B3072425 : Blo 2047435 3072425 := bstep (se 2 (by rfl) ⟨1152159, by rfl⟩ : syracuseStep 3072425 = 2304319) B2304319
theorem B2048283 : Blo 2047435 2048283 := bstep (se 1 (by rfl) ⟨1536212, by rfl⟩ : syracuseStep 2048283 = 3072425) B3072425
theorem B7777093 : Blo 2047435 7777093 := bbase (se 4 (by rfl) ⟨729102, by rfl⟩ : syracuseStep 7777093 = 1458205) (by norm_num)
theorem B10369457 : Blo 2047435 10369457 := bstep (se 2 (by rfl) ⟨3888546, by rfl⟩ : syracuseStep 10369457 = 7777093) B7777093
theorem B6912971 : Blo 2047435 6912971 := bstep (se 1 (by rfl) ⟨5184728, by rfl⟩ : syracuseStep 6912971 = 10369457) B10369457
theorem B4608647 : Blo 2047435 4608647 := bstep (se 1 (by rfl) ⟨3456485, by rfl⟩ : syracuseStep 4608647 = 6912971) B6912971
theorem B3072431 : Blo 2047435 3072431 := bstep (se 1 (by rfl) ⟨2304323, by rfl⟩ : syracuseStep 3072431 = 4608647) B4608647
theorem B2048287 : Blo 2047435 2048287 := bstep (se 1 (by rfl) ⟨1536215, by rfl⟩ : syracuseStep 2048287 = 3072431) B3072431
theorem B3072437 : Blo 2047435 3072437 := bbase (se 5 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 3072437 = 288041) (by norm_num)
theorem B2048291 : Blo 2047435 2048291 := bstep (se 1 (by rfl) ⟨1536218, by rfl⟩ : syracuseStep 2048291 = 3072437) B3072437
theorem B5184749 : Blo 2047435 5184749 := bbase (se 3 (by rfl) ⟨972140, by rfl⟩ : syracuseStep 5184749 = 1944281) (by norm_num)
theorem B3456499 : Blo 2047435 3456499 := bstep (se 1 (by rfl) ⟨2592374, by rfl⟩ : syracuseStep 3456499 = 5184749) B5184749
theorem B4608665 : Blo 2047435 4608665 := bstep (se 2 (by rfl) ⟨1728249, by rfl⟩ : syracuseStep 4608665 = 3456499) B3456499
theorem B3072443 : Blo 2047435 3072443 := bstep (se 1 (by rfl) ⟨2304332, by rfl⟩ : syracuseStep 3072443 = 4608665) B4608665
theorem B2048295 : Blo 2047435 2048295 := bstep (se 1 (by rfl) ⟨1536221, by rfl⟩ : syracuseStep 2048295 = 3072443) B3072443
theorem B2304337 : Blo 2047435 2304337 := bbase (se 2 (by rfl) ⟨864126, by rfl⟩ : syracuseStep 2304337 = 1728253) (by norm_num)
theorem B3072449 : Blo 2047435 3072449 := bstep (se 2 (by rfl) ⟨1152168, by rfl⟩ : syracuseStep 3072449 = 2304337) B2304337
theorem B2048299 : Blo 2047435 2048299 := bstep (se 1 (by rfl) ⟨1536224, by rfl⟩ : syracuseStep 2048299 = 3072449) B3072449
theorem B2187325 : Blo 2047435 2187325 := bbase (se 3 (by rfl) ⟨410123, by rfl⟩ : syracuseStep 2187325 = 820247) (by norm_num)
theorem B2916433 : Blo 2047435 2916433 := bstep (se 2 (by rfl) ⟨1093662, by rfl⟩ : syracuseStep 2916433 = 2187325) B2187325
theorem B3888577 : Blo 2047435 3888577 := bstep (se 2 (by rfl) ⟨1458216, by rfl⟩ : syracuseStep 3888577 = 2916433) B2916433
theorem B5184769 : Blo 2047435 5184769 := bstep (se 2 (by rfl) ⟨1944288, by rfl⟩ : syracuseStep 5184769 = 3888577) B3888577
theorem B6913025 : Blo 2047435 6913025 := bstep (se 2 (by rfl) ⟨2592384, by rfl⟩ : syracuseStep 6913025 = 5184769) B5184769
theorem B4608683 : Blo 2047435 4608683 := bstep (se 1 (by rfl) ⟨3456512, by rfl⟩ : syracuseStep 4608683 = 6913025) B6913025
theorem B3072455 : Blo 2047435 3072455 := bstep (se 1 (by rfl) ⟨2304341, by rfl⟩ : syracuseStep 3072455 = 4608683) B4608683
theorem B2048303 : Blo 2047435 2048303 := bstep (se 1 (by rfl) ⟨1536227, by rfl⟩ : syracuseStep 2048303 = 3072455) B3072455
theorem B3072461 : Blo 2047435 3072461 := bbase (se 3 (by rfl) ⟨576086, by rfl⟩ : syracuseStep 3072461 = 1152173) (by norm_num)
theorem B2048307 : Blo 2047435 2048307 := bstep (se 1 (by rfl) ⟨1536230, by rfl⟩ : syracuseStep 2048307 = 3072461) B3072461
theorem B4608701 : Blo 2047435 4608701 := bbase (se 3 (by rfl) ⟨864131, by rfl⟩ : syracuseStep 4608701 = 1728263) (by norm_num)
theorem B3072467 : Blo 2047435 3072467 := bstep (se 1 (by rfl) ⟨2304350, by rfl⟩ : syracuseStep 3072467 = 4608701) B4608701
theorem B2048311 : Blo 2047435 2048311 := bstep (se 1 (by rfl) ⟨1536233, by rfl⟩ : syracuseStep 2048311 = 3072467) B3072467
theorem B3456533 : Blo 2047435 3456533 := bbase (se 6 (by rfl) ⟨81012, by rfl⟩ : syracuseStep 3456533 = 162025) (by norm_num)
theorem B2304355 : Blo 2047435 2304355 := bstep (se 1 (by rfl) ⟨1728266, by rfl⟩ : syracuseStep 2304355 = 3456533) B3456533
theorem B3072473 : Blo 2047435 3072473 := bstep (se 2 (by rfl) ⟨1152177, by rfl⟩ : syracuseStep 3072473 = 2304355) B2304355
theorem B2048315 : Blo 2047435 2048315 := bstep (se 1 (by rfl) ⟨1536236, by rfl⟩ : syracuseStep 2048315 = 3072473) B3072473
theorem B2528365 : Blo 2047435 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B3371153 : Blo 2047435 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B8989741 : Blo 2047435 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B11986321 : Blo 2047435 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B15981761 : Blo 2047435 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B10654507 : Blo 2047435 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B56824037 : Blo 2047435 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B37882691 : Blo 2047435 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B25255127 : Blo 2047435 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B16836751 : Blo 2047435 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B22449001 : Blo 2047435 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B29932001 : Blo 2047435 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B19954667 : Blo 2047435 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B13303111 : Blo 2047435 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B17737481 : Blo 2047435 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B11824987 : Blo 2047435 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B15766649 : Blo 2047435 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B10511099 : Blo 2047435 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B7007399 : Blo 2047435 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B4671599 : Blo 2047435 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B12457597 : Blo 2047435 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B16610129 : Blo 2047435 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B11073419 : Blo 2047435 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B7382279 : Blo 2047435 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B19686077 : Blo 2047435 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B13124051 : Blo 2047435 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B8749367 : Blo 2047435 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B5832911 : Blo 2047435 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B15554429 : Blo 2047435 15554429 := bstep (se 3 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 15554429 = 5832911) B5832911
theorem B10369619 : Blo 2047435 10369619 := bstep (se 1 (by rfl) ⟨7777214, by rfl⟩ : syracuseStep 10369619 = 15554429) B15554429
theorem B6913079 : Blo 2047435 6913079 := bstep (se 1 (by rfl) ⟨5184809, by rfl⟩ : syracuseStep 6913079 = 10369619) B10369619
theorem B4608719 : Blo 2047435 4608719 := bstep (se 1 (by rfl) ⟨3456539, by rfl⟩ : syracuseStep 4608719 = 6913079) B6913079
theorem B3072479 : Blo 2047435 3072479 := bstep (se 1 (by rfl) ⟨2304359, by rfl⟩ : syracuseStep 3072479 = 4608719) B4608719
theorem B2048319 : Blo 2047435 2048319 := bstep (se 1 (by rfl) ⟨1536239, by rfl⟩ : syracuseStep 2048319 = 3072479) B3072479
theorem B3072485 : Blo 2047435 3072485 := bbase (se 4 (by rfl) ⟨288045, by rfl⟩ : syracuseStep 3072485 = 576091) (by norm_num)
theorem B2048323 : Blo 2047435 2048323 := bstep (se 1 (by rfl) ⟨1536242, by rfl⟩ : syracuseStep 2048323 = 3072485) B3072485
theorem B16610197 : Blo 2047435 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B22146929 : Blo 2047435 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B14764619 : Blo 2047435 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B9843079 : Blo 2047435 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B13124105 : Blo 2047435 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B8749403 : Blo 2047435 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B5832935 : Blo 2047435 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B3888623 : Blo 2047435 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B2592415 : Blo 2047435 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B3456553 : Blo 2047435 3456553 := bstep (se 2 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 3456553 = 2592415) B2592415
theorem B4608737 : Blo 2047435 4608737 := bstep (se 2 (by rfl) ⟨1728276, by rfl⟩ : syracuseStep 4608737 = 3456553) B3456553
theorem B3072491 : Blo 2047435 3072491 := bstep (se 1 (by rfl) ⟨2304368, by rfl⟩ : syracuseStep 3072491 = 4608737) B4608737
theorem B2048327 : Blo 2047435 2048327 := bstep (se 1 (by rfl) ⟨1536245, by rfl⟩ : syracuseStep 2048327 = 3072491) B3072491
theorem B2304373 : Blo 2047435 2304373 := bbase (se 5 (by rfl) ⟨108017, by rfl⟩ : syracuseStep 2304373 = 216035) (by norm_num)
theorem B3072497 : Blo 2047435 3072497 := bstep (se 2 (by rfl) ⟨1152186, by rfl⟩ : syracuseStep 3072497 = 2304373) B2304373
theorem B2048331 : Blo 2047435 2048331 := bstep (se 1 (by rfl) ⟨1536248, by rfl⟩ : syracuseStep 2048331 = 3072497) B3072497
theorem B2592425 : Blo 2047435 2592425 := bbase (se 2 (by rfl) ⟨972159, by rfl⟩ : syracuseStep 2592425 = 1944319) (by norm_num)
theorem B6913133 : Blo 2047435 6913133 := bstep (se 3 (by rfl) ⟨1296212, by rfl⟩ : syracuseStep 6913133 = 2592425) B2592425
theorem B4608755 : Blo 2047435 4608755 := bstep (se 1 (by rfl) ⟨3456566, by rfl⟩ : syracuseStep 4608755 = 6913133) B6913133
theorem B3072503 : Blo 2047435 3072503 := bstep (se 1 (by rfl) ⟨2304377, by rfl⟩ : syracuseStep 3072503 = 4608755) B4608755
theorem B2048335 : Blo 2047435 2048335 := bstep (se 1 (by rfl) ⟨1536251, by rfl⟩ : syracuseStep 2048335 = 3072503) B3072503
theorem B3072509 : Blo 2047435 3072509 := bbase (se 3 (by rfl) ⟨576095, by rfl⟩ : syracuseStep 3072509 = 1152191) (by norm_num)
theorem B2048339 : Blo 2047435 2048339 := bstep (se 1 (by rfl) ⟨1536254, by rfl⟩ : syracuseStep 2048339 = 3072509) B3072509
theorem B4608773 : Blo 2047435 4608773 := bbase (se 4 (by rfl) ⟨432072, by rfl⟩ : syracuseStep 4608773 = 864145) (by norm_num)
theorem B3072515 : Blo 2047435 3072515 := bstep (se 1 (by rfl) ⟨2304386, by rfl⟩ : syracuseStep 3072515 = 4608773) B4608773
theorem B2048343 : Blo 2047435 2048343 := bstep (se 1 (by rfl) ⟨1536257, by rfl⟩ : syracuseStep 2048343 = 3072515) B3072515
theorem B3888661 : Blo 2047435 3888661 := bbase (se 6 (by rfl) ⟨91140, by rfl⟩ : syracuseStep 3888661 = 182281) (by norm_num)
theorem B5184881 : Blo 2047435 5184881 := bstep (se 2 (by rfl) ⟨1944330, by rfl⟩ : syracuseStep 5184881 = 3888661) B3888661
theorem B3456587 : Blo 2047435 3456587 := bstep (se 1 (by rfl) ⟨2592440, by rfl⟩ : syracuseStep 3456587 = 5184881) B5184881
theorem B2304391 : Blo 2047435 2304391 := bstep (se 1 (by rfl) ⟨1728293, by rfl⟩ : syracuseStep 2304391 = 3456587) B3456587
theorem B3072521 : Blo 2047435 3072521 := bstep (se 2 (by rfl) ⟨1152195, by rfl⟩ : syracuseStep 3072521 = 2304391) B2304391
theorem B2048347 : Blo 2047435 2048347 := bstep (se 1 (by rfl) ⟨1536260, by rfl⟩ : syracuseStep 2048347 = 3072521) B3072521
theorem B10369781 : Blo 2047435 10369781 := bbase (se 5 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 10369781 = 972167) (by norm_num)
theorem B6913187 : Blo 2047435 6913187 := bstep (se 1 (by rfl) ⟨5184890, by rfl⟩ : syracuseStep 6913187 = 10369781) B10369781
theorem B4608791 : Blo 2047435 4608791 := bstep (se 1 (by rfl) ⟨3456593, by rfl⟩ : syracuseStep 4608791 = 6913187) B6913187
theorem B3072527 : Blo 2047435 3072527 := bstep (se 1 (by rfl) ⟨2304395, by rfl⟩ : syracuseStep 3072527 = 4608791) B4608791
theorem B2048351 : Blo 2047435 2048351 := bstep (se 1 (by rfl) ⟨1536263, by rfl⟩ : syracuseStep 2048351 = 3072527) B3072527
theorem B3072533 : Blo 2047435 3072533 := bbase (se 6 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 3072533 = 144025) (by norm_num)
theorem B2048355 : Blo 2047435 2048355 := bstep (se 1 (by rfl) ⟨1536266, by rfl⟩ : syracuseStep 2048355 = 3072533) B3072533
theorem B3281077 : Blo 2047435 3281077 := bbase (se 5 (by rfl) ⟨153800, by rfl⟩ : syracuseStep 3281077 = 307601) (by norm_num)
theorem B17499077 : Blo 2047435 17499077 := bstep (se 4 (by rfl) ⟨1640538, by rfl⟩ : syracuseStep 17499077 = 3281077) B3281077
theorem B11666051 : Blo 2047435 11666051 := bstep (se 1 (by rfl) ⟨8749538, by rfl⟩ : syracuseStep 11666051 = 17499077) B17499077
theorem B7777367 : Blo 2047435 7777367 := bstep (se 1 (by rfl) ⟨5833025, by rfl⟩ : syracuseStep 7777367 = 11666051) B11666051
theorem B5184911 : Blo 2047435 5184911 := bstep (se 1 (by rfl) ⟨3888683, by rfl⟩ : syracuseStep 5184911 = 7777367) B7777367
theorem B3456607 : Blo 2047435 3456607 := bstep (se 1 (by rfl) ⟨2592455, by rfl⟩ : syracuseStep 3456607 = 5184911) B5184911
theorem B4608809 : Blo 2047435 4608809 := bstep (se 2 (by rfl) ⟨1728303, by rfl⟩ : syracuseStep 4608809 = 3456607) B3456607
theorem B3072539 : Blo 2047435 3072539 := bstep (se 1 (by rfl) ⟨2304404, by rfl⟩ : syracuseStep 3072539 = 4608809) B4608809
theorem B2048359 : Blo 2047435 2048359 := bstep (se 1 (by rfl) ⟨1536269, by rfl⟩ : syracuseStep 2048359 = 3072539) B3072539
theorem B2304409 : Blo 2047435 2304409 := bbase (se 2 (by rfl) ⟨864153, by rfl⟩ : syracuseStep 2304409 = 1728307) (by norm_num)
theorem B3072545 : Blo 2047435 3072545 := bstep (se 2 (by rfl) ⟨1152204, by rfl⟩ : syracuseStep 3072545 = 2304409) B2304409
theorem B2048363 : Blo 2047435 2048363 := bstep (se 1 (by rfl) ⟨1536272, by rfl⟩ : syracuseStep 2048363 = 3072545) B3072545
theorem B7777397 : Blo 2047435 7777397 := bbase (se 5 (by rfl) ⟨364565, by rfl⟩ : syracuseStep 7777397 = 729131) (by norm_num)
theorem B5184931 : Blo 2047435 5184931 := bstep (se 1 (by rfl) ⟨3888698, by rfl⟩ : syracuseStep 5184931 = 7777397) B7777397
theorem B6913241 : Blo 2047435 6913241 := bstep (se 2 (by rfl) ⟨2592465, by rfl⟩ : syracuseStep 6913241 = 5184931) B5184931
theorem B4608827 : Blo 2047435 4608827 := bstep (se 1 (by rfl) ⟨3456620, by rfl⟩ : syracuseStep 4608827 = 6913241) B6913241
theorem B3072551 : Blo 2047435 3072551 := bstep (se 1 (by rfl) ⟨2304413, by rfl⟩ : syracuseStep 3072551 = 4608827) B4608827
theorem B2048367 : Blo 2047435 2048367 := bstep (se 1 (by rfl) ⟨1536275, by rfl⟩ : syracuseStep 2048367 = 3072551) B3072551
theorem B3072557 : Blo 2047435 3072557 := bbase (se 3 (by rfl) ⟨576104, by rfl⟩ : syracuseStep 3072557 = 1152209) (by norm_num)
theorem B2048371 : Blo 2047435 2048371 := bstep (se 1 (by rfl) ⟨1536278, by rfl⟩ : syracuseStep 2048371 = 3072557) B3072557
theorem B4608845 : Blo 2047435 4608845 := bbase (se 3 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 4608845 = 1728317) (by norm_num)
theorem B3072563 : Blo 2047435 3072563 := bstep (se 1 (by rfl) ⟨2304422, by rfl⟩ : syracuseStep 3072563 = 4608845) B4608845
theorem B2048375 : Blo 2047435 2048375 := bstep (se 1 (by rfl) ⟨1536281, by rfl⟩ : syracuseStep 2048375 = 3072563) B3072563
theorem B2592481 : Blo 2047435 2592481 := bbase (se 2 (by rfl) ⟨972180, by rfl⟩ : syracuseStep 2592481 = 1944361) (by norm_num)
theorem B3456641 : Blo 2047435 3456641 := bstep (se 2 (by rfl) ⟨1296240, by rfl⟩ : syracuseStep 3456641 = 2592481) B2592481
theorem B2304427 : Blo 2047435 2304427 := bstep (se 1 (by rfl) ⟨1728320, by rfl⟩ : syracuseStep 2304427 = 3456641) B3456641
theorem B3072569 : Blo 2047435 3072569 := bstep (se 2 (by rfl) ⟨1152213, by rfl⟩ : syracuseStep 3072569 = 2304427) B2304427
theorem B2048379 : Blo 2047435 2048379 := bstep (se 1 (by rfl) ⟨1536284, by rfl⟩ : syracuseStep 2048379 = 3072569) B3072569
theorem B23332373 : Blo 2047435 23332373 := bbase (se 6 (by rfl) ⟨546852, by rfl⟩ : syracuseStep 23332373 = 1093705) (by norm_num)
theorem B15554915 : Blo 2047435 15554915 := bstep (se 1 (by rfl) ⟨11666186, by rfl⟩ : syracuseStep 15554915 = 23332373) B23332373
theorem B10369943 : Blo 2047435 10369943 := bstep (se 1 (by rfl) ⟨7777457, by rfl⟩ : syracuseStep 10369943 = 15554915) B15554915
theorem B6913295 : Blo 2047435 6913295 := bstep (se 1 (by rfl) ⟨5184971, by rfl⟩ : syracuseStep 6913295 = 10369943) B10369943
theorem B4608863 : Blo 2047435 4608863 := bstep (se 1 (by rfl) ⟨3456647, by rfl⟩ : syracuseStep 4608863 = 6913295) B6913295
theorem B3072575 : Blo 2047435 3072575 := bstep (se 1 (by rfl) ⟨2304431, by rfl⟩ : syracuseStep 3072575 = 4608863) B4608863
theorem B2048383 : Blo 2047435 2048383 := bstep (se 1 (by rfl) ⟨1536287, by rfl⟩ : syracuseStep 2048383 = 3072575) B3072575
theorem B3072581 : Blo 2047435 3072581 := bbase (se 4 (by rfl) ⟨288054, by rfl⟩ : syracuseStep 3072581 = 576109) (by norm_num)
theorem B2048387 : Blo 2047435 2048387 := bstep (se 1 (by rfl) ⟨1536290, by rfl⟩ : syracuseStep 2048387 = 3072581) B3072581
theorem B3456661 : Blo 2047435 3456661 := bbase (se 6 (by rfl) ⟨81015, by rfl⟩ : syracuseStep 3456661 = 162031) (by norm_num)
theorem B4608881 : Blo 2047435 4608881 := bstep (se 2 (by rfl) ⟨1728330, by rfl⟩ : syracuseStep 4608881 = 3456661) B3456661
theorem B3072587 : Blo 2047435 3072587 := bstep (se 1 (by rfl) ⟨2304440, by rfl⟩ : syracuseStep 3072587 = 4608881) B4608881
theorem B2048391 : Blo 2047435 2048391 := bstep (se 1 (by rfl) ⟨1536293, by rfl⟩ : syracuseStep 2048391 = 3072587) B3072587
theorem B2304445 : Blo 2047435 2304445 := bbase (se 3 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 2304445 = 864167) (by norm_num)
theorem B3072593 : Blo 2047435 3072593 := bstep (se 2 (by rfl) ⟨1152222, by rfl⟩ : syracuseStep 3072593 = 2304445) B2304445
theorem B2048395 : Blo 2047435 2048395 := bstep (se 1 (by rfl) ⟨1536296, by rfl⟩ : syracuseStep 2048395 = 3072593) B3072593
theorem B6913349 : Blo 2047435 6913349 := bbase (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) (by norm_num)
theorem B4608899 : Blo 2047435 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B3072599 : Blo 2047435 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B2048399 : Blo 2047435 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B3072605 : Blo 2047435 3072605 := bbase (se 3 (by rfl) ⟨576113, by rfl⟩ : syracuseStep 3072605 = 1152227) (by norm_num)
theorem B2048403 : Blo 2047435 2048403 := bstep (se 1 (by rfl) ⟨1536302, by rfl⟩ : syracuseStep 2048403 = 3072605) B3072605
theorem B4608917 : Blo 2047435 4608917 := bbase (se 6 (by rfl) ⟨108021, by rfl⟩ : syracuseStep 4608917 = 216043) (by norm_num)
theorem B3072611 : Blo 2047435 3072611 := bstep (se 1 (by rfl) ⟨2304458, by rfl⟩ : syracuseStep 3072611 = 4608917) B4608917
theorem B2048407 : Blo 2047435 2048407 := bstep (se 1 (by rfl) ⟨1536305, by rfl⟩ : syracuseStep 2048407 = 3072611) B3072611
theorem B3114541 : Blo 2047435 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B4152721 : Blo 2047435 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B5536961 : Blo 2047435 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B3691307 : Blo 2047435 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B2460871 : Blo 2047435 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B3281161 : Blo 2047435 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B4374881 : Blo 2047435 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B2916587 : Blo 2047435 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B7777565 : Blo 2047435 7777565 := bstep (se 3 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 7777565 = 2916587) B2916587
theorem B5185043 : Blo 2047435 5185043 := bstep (se 1 (by rfl) ⟨3888782, by rfl⟩ : syracuseStep 5185043 = 7777565) B7777565
theorem B3456695 : Blo 2047435 3456695 := bstep (se 1 (by rfl) ⟨2592521, by rfl⟩ : syracuseStep 3456695 = 5185043) B5185043
theorem B2304463 : Blo 2047435 2304463 := bstep (se 1 (by rfl) ⟨1728347, by rfl⟩ : syracuseStep 2304463 = 3456695) B3456695
theorem B3072617 : Blo 2047435 3072617 := bstep (se 2 (by rfl) ⟨1152231, by rfl⟩ : syracuseStep 3072617 = 2304463) B2304463
theorem B2048411 : Blo 2047435 2048411 := bstep (se 1 (by rfl) ⟨1536308, by rfl⟩ : syracuseStep 2048411 = 3072617) B3072617
theorem B2768485 : Blo 2047435 2768485 := bbase (se 4 (by rfl) ⟨259545, by rfl⟩ : syracuseStep 2768485 = 519091) (by norm_num)
theorem B3691313 : Blo 2047435 3691313 := bstep (se 2 (by rfl) ⟨1384242, by rfl⟩ : syracuseStep 3691313 = 2768485) B2768485
theorem B2460875 : Blo 2047435 2460875 := bstep (se 1 (by rfl) ⟨1845656, by rfl⟩ : syracuseStep 2460875 = 3691313) B3691313
theorem B6562333 : Blo 2047435 6562333 := bstep (se 3 (by rfl) ⟨1230437, by rfl⟩ : syracuseStep 6562333 = 2460875) B2460875
theorem B8749777 : Blo 2047435 8749777 := bstep (se 2 (by rfl) ⟨3281166, by rfl⟩ : syracuseStep 8749777 = 6562333) B6562333
theorem B11666369 : Blo 2047435 11666369 := bstep (se 2 (by rfl) ⟨4374888, by rfl⟩ : syracuseStep 11666369 = 8749777) B8749777
theorem B7777579 : Blo 2047435 7777579 := bstep (se 1 (by rfl) ⟨5833184, by rfl⟩ : syracuseStep 7777579 = 11666369) B11666369
theorem B10370105 : Blo 2047435 10370105 := bstep (se 2 (by rfl) ⟨3888789, by rfl⟩ : syracuseStep 10370105 = 7777579) B7777579
theorem B6913403 : Blo 2047435 6913403 := bstep (se 1 (by rfl) ⟨5185052, by rfl⟩ : syracuseStep 6913403 = 10370105) B10370105
theorem B4608935 : Blo 2047435 4608935 := bstep (se 1 (by rfl) ⟨3456701, by rfl⟩ : syracuseStep 4608935 = 6913403) B6913403
theorem B3072623 : Blo 2047435 3072623 := bstep (se 1 (by rfl) ⟨2304467, by rfl⟩ : syracuseStep 3072623 = 4608935) B4608935
theorem B2048415 : Blo 2047435 2048415 := bstep (se 1 (by rfl) ⟨1536311, by rfl⟩ : syracuseStep 2048415 = 3072623) B3072623
theorem B3072629 : Blo 2047435 3072629 := bbase (se 5 (by rfl) ⟨144029, by rfl⟩ : syracuseStep 3072629 = 288059) (by norm_num)
theorem B2048419 : Blo 2047435 2048419 := bstep (se 1 (by rfl) ⟨1536314, by rfl⟩ : syracuseStep 2048419 = 3072629) B3072629
theorem B3888805 : Blo 2047435 3888805 := bbase (se 4 (by rfl) ⟨364575, by rfl⟩ : syracuseStep 3888805 = 729151) (by norm_num)
theorem B5185073 : Blo 2047435 5185073 := bstep (se 2 (by rfl) ⟨1944402, by rfl⟩ : syracuseStep 5185073 = 3888805) B3888805
theorem B3456715 : Blo 2047435 3456715 := bstep (se 1 (by rfl) ⟨2592536, by rfl⟩ : syracuseStep 3456715 = 5185073) B5185073
theorem B4608953 : Blo 2047435 4608953 := bstep (se 2 (by rfl) ⟨1728357, by rfl⟩ : syracuseStep 4608953 = 3456715) B3456715
theorem B3072635 : Blo 2047435 3072635 := bstep (se 1 (by rfl) ⟨2304476, by rfl⟩ : syracuseStep 3072635 = 4608953) B4608953
theorem B2048423 : Blo 2047435 2048423 := bstep (se 1 (by rfl) ⟨1536317, by rfl⟩ : syracuseStep 2048423 = 3072635) B3072635
theorem B2304481 : Blo 2047435 2304481 := bbase (se 2 (by rfl) ⟨864180, by rfl⟩ : syracuseStep 2304481 = 1728361) (by norm_num)
theorem B3072641 : Blo 2047435 3072641 := bstep (se 2 (by rfl) ⟨1152240, by rfl⟩ : syracuseStep 3072641 = 2304481) B2304481
theorem B2048427 : Blo 2047435 2048427 := bstep (se 1 (by rfl) ⟨1536320, by rfl⟩ : syracuseStep 2048427 = 3072641) B3072641
theorem B5185093 : Blo 2047435 5185093 := bbase (se 4 (by rfl) ⟨486102, by rfl⟩ : syracuseStep 5185093 = 972205) (by norm_num)
theorem B6913457 : Blo 2047435 6913457 := bstep (se 2 (by rfl) ⟨2592546, by rfl⟩ : syracuseStep 6913457 = 5185093) B5185093
theorem B4608971 : Blo 2047435 4608971 := bstep (se 1 (by rfl) ⟨3456728, by rfl⟩ : syracuseStep 4608971 = 6913457) B6913457
theorem B3072647 : Blo 2047435 3072647 := bstep (se 1 (by rfl) ⟨2304485, by rfl⟩ : syracuseStep 3072647 = 4608971) B4608971
theorem B2048431 : Blo 2047435 2048431 := bstep (se 1 (by rfl) ⟨1536323, by rfl⟩ : syracuseStep 2048431 = 3072647) B3072647
theorem B3072653 : Blo 2047435 3072653 := bbase (se 3 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 3072653 = 1152245) (by norm_num)
theorem B2048435 : Blo 2047435 2048435 := bstep (se 1 (by rfl) ⟨1536326, by rfl⟩ : syracuseStep 2048435 = 3072653) B3072653
theorem B4608989 : Blo 2047435 4608989 := bbase (se 3 (by rfl) ⟨864185, by rfl⟩ : syracuseStep 4608989 = 1728371) (by norm_num)
theorem B3072659 : Blo 2047435 3072659 := bstep (se 1 (by rfl) ⟨2304494, by rfl⟩ : syracuseStep 3072659 = 4608989) B4608989
theorem B2048439 : Blo 2047435 2048439 := bstep (se 1 (by rfl) ⟨1536329, by rfl⟩ : syracuseStep 2048439 = 3072659) B3072659
theorem B3456749 : Blo 2047435 3456749 := bbase (se 3 (by rfl) ⟨648140, by rfl⟩ : syracuseStep 3456749 = 1296281) (by norm_num)
theorem B2304499 : Blo 2047435 2304499 := bstep (se 1 (by rfl) ⟨1728374, by rfl⟩ : syracuseStep 2304499 = 3456749) B3456749
theorem B3072665 : Blo 2047435 3072665 := bstep (se 2 (by rfl) ⟨1152249, by rfl⟩ : syracuseStep 3072665 = 2304499) B2304499
theorem B2048443 : Blo 2047435 2048443 := bstep (se 1 (by rfl) ⟨1536332, by rfl⟩ : syracuseStep 2048443 = 3072665) B3072665
theorem B9843653 : Blo 2047435 9843653 := bbase (se 4 (by rfl) ⟨922842, by rfl⟩ : syracuseStep 9843653 = 1845685) (by norm_num)
theorem B26249741 : Blo 2047435 26249741 := bstep (se 3 (by rfl) ⟨4921826, by rfl⟩ : syracuseStep 26249741 = 9843653) B9843653
theorem B17499827 : Blo 2047435 17499827 := bstep (se 1 (by rfl) ⟨13124870, by rfl⟩ : syracuseStep 17499827 = 26249741) B26249741
theorem B11666551 : Blo 2047435 11666551 := bstep (se 1 (by rfl) ⟨8749913, by rfl⟩ : syracuseStep 11666551 = 17499827) B17499827
theorem B15555401 : Blo 2047435 15555401 := bstep (se 2 (by rfl) ⟨5833275, by rfl⟩ : syracuseStep 15555401 = 11666551) B11666551
theorem B10370267 : Blo 2047435 10370267 := bstep (se 1 (by rfl) ⟨7777700, by rfl⟩ : syracuseStep 10370267 = 15555401) B15555401
theorem B6913511 : Blo 2047435 6913511 := bstep (se 1 (by rfl) ⟨5185133, by rfl⟩ : syracuseStep 6913511 = 10370267) B10370267
theorem B4609007 : Blo 2047435 4609007 := bstep (se 1 (by rfl) ⟨3456755, by rfl⟩ : syracuseStep 4609007 = 6913511) B6913511
theorem B3072671 : Blo 2047435 3072671 := bstep (se 1 (by rfl) ⟨2304503, by rfl⟩ : syracuseStep 3072671 = 4609007) B4609007
theorem B2048447 : Blo 2047435 2048447 := bstep (se 1 (by rfl) ⟨1536335, by rfl⟩ : syracuseStep 2048447 = 3072671) B3072671
theorem B3072677 : Blo 2047435 3072677 := bbase (se 4 (by rfl) ⟨288063, by rfl⟩ : syracuseStep 3072677 = 576127) (by norm_num)
theorem B2048451 : Blo 2047435 2048451 := bstep (se 1 (by rfl) ⟨1536338, by rfl⟩ : syracuseStep 2048451 = 3072677) B3072677
theorem B2592577 : Blo 2047435 2592577 := bbase (se 2 (by rfl) ⟨972216, by rfl⟩ : syracuseStep 2592577 = 1944433) (by norm_num)
theorem B3456769 : Blo 2047435 3456769 := bstep (se 2 (by rfl) ⟨1296288, by rfl⟩ : syracuseStep 3456769 = 2592577) B2592577
theorem B4609025 : Blo 2047435 4609025 := bstep (se 2 (by rfl) ⟨1728384, by rfl⟩ : syracuseStep 4609025 = 3456769) B3456769
theorem B3072683 : Blo 2047435 3072683 := bstep (se 1 (by rfl) ⟨2304512, by rfl⟩ : syracuseStep 3072683 = 4609025) B4609025
theorem B2048455 : Blo 2047435 2048455 := bstep (se 1 (by rfl) ⟨1536341, by rfl⟩ : syracuseStep 2048455 = 3072683) B3072683
theorem B2304517 : Blo 2047435 2304517 := bbase (se 4 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 2304517 = 432097) (by norm_num)
theorem B3072689 : Blo 2047435 3072689 := bstep (se 2 (by rfl) ⟨1152258, by rfl⟩ : syracuseStep 3072689 = 2304517) B2304517
theorem B2048459 : Blo 2047435 2048459 := bstep (se 1 (by rfl) ⟨1536344, by rfl⟩ : syracuseStep 2048459 = 3072689) B3072689
theorem B2916661 : Blo 2047435 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B3888881 : Blo 2047435 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B2592587 : Blo 2047435 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B6913565 : Blo 2047435 6913565 := bstep (se 3 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 6913565 = 2592587) B2592587
theorem B4609043 : Blo 2047435 4609043 := bstep (se 1 (by rfl) ⟨3456782, by rfl⟩ : syracuseStep 4609043 = 6913565) B6913565
theorem B3072695 : Blo 2047435 3072695 := bstep (se 1 (by rfl) ⟨2304521, by rfl⟩ : syracuseStep 3072695 = 4609043) B4609043
theorem B2048463 : Blo 2047435 2048463 := bstep (se 1 (by rfl) ⟨1536347, by rfl⟩ : syracuseStep 2048463 = 3072695) B3072695
theorem B3072701 : Blo 2047435 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B2048467 : Blo 2047435 2048467 := bstep (se 1 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 2048467 = 3072701) B3072701
theorem B4609061 : Blo 2047435 4609061 := bbase (se 4 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 4609061 = 864199) (by norm_num)
theorem B3072707 : Blo 2047435 3072707 := bstep (se 1 (by rfl) ⟨2304530, by rfl⟩ : syracuseStep 3072707 = 4609061) B4609061
theorem B2048471 : Blo 2047435 2048471 := bstep (se 1 (by rfl) ⟨1536353, by rfl⟩ : syracuseStep 2048471 = 3072707) B3072707
theorem B5185205 : Blo 2047435 5185205 := bbase (se 5 (by rfl) ⟨243056, by rfl⟩ : syracuseStep 5185205 = 486113) (by norm_num)
theorem B3456803 : Blo 2047435 3456803 := bstep (se 1 (by rfl) ⟨2592602, by rfl⟩ : syracuseStep 3456803 = 5185205) B5185205
theorem B2304535 : Blo 2047435 2304535 := bstep (se 1 (by rfl) ⟨1728401, by rfl⟩ : syracuseStep 2304535 = 3456803) B3456803
theorem B3072713 : Blo 2047435 3072713 := bstep (se 2 (by rfl) ⟨1152267, by rfl⟩ : syracuseStep 3072713 = 2304535) B2304535
theorem B2048475 : Blo 2047435 2048475 := bstep (se 1 (by rfl) ⟨1536356, by rfl⟩ : syracuseStep 2048475 = 3072713) B3072713
theorem B13125077 : Blo 2047435 13125077 := bbase (se 7 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 13125077 = 307619) (by norm_num)
theorem B8750051 : Blo 2047435 8750051 := bstep (se 1 (by rfl) ⟨6562538, by rfl⟩ : syracuseStep 8750051 = 13125077) B13125077
theorem B5833367 : Blo 2047435 5833367 := bstep (se 1 (by rfl) ⟨4375025, by rfl⟩ : syracuseStep 5833367 = 8750051) B8750051
theorem B3888911 : Blo 2047435 3888911 := bstep (se 1 (by rfl) ⟨2916683, by rfl⟩ : syracuseStep 3888911 = 5833367) B5833367
theorem B10370429 : Blo 2047435 10370429 := bstep (se 3 (by rfl) ⟨1944455, by rfl⟩ : syracuseStep 10370429 = 3888911) B3888911
theorem B6913619 : Blo 2047435 6913619 := bstep (se 1 (by rfl) ⟨5185214, by rfl⟩ : syracuseStep 6913619 = 10370429) B10370429
theorem B4609079 : Blo 2047435 4609079 := bstep (se 1 (by rfl) ⟨3456809, by rfl⟩ : syracuseStep 4609079 = 6913619) B6913619
theorem B3072719 : Blo 2047435 3072719 := bstep (se 1 (by rfl) ⟨2304539, by rfl⟩ : syracuseStep 3072719 = 4609079) B4609079
theorem B2048479 : Blo 2047435 2048479 := bstep (se 1 (by rfl) ⟨1536359, by rfl⟩ : syracuseStep 2048479 = 3072719) B3072719
theorem B3072725 : Blo 2047435 3072725 := bbase (se 7 (by rfl) ⟨36008, by rfl⟩ : syracuseStep 3072725 = 72017) (by norm_num)
theorem B2048483 : Blo 2047435 2048483 := bstep (se 1 (by rfl) ⟨1536362, by rfl⟩ : syracuseStep 2048483 = 3072725) B3072725
theorem B6562565 : Blo 2047435 6562565 := bbase (se 4 (by rfl) ⟨615240, by rfl⟩ : syracuseStep 6562565 = 1230481) (by norm_num)
theorem B4375043 : Blo 2047435 4375043 := bstep (se 1 (by rfl) ⟨3281282, by rfl⟩ : syracuseStep 4375043 = 6562565) B6562565
theorem B2916695 : Blo 2047435 2916695 := bstep (se 1 (by rfl) ⟨2187521, by rfl⟩ : syracuseStep 2916695 = 4375043) B4375043
theorem B7777853 : Blo 2047435 7777853 := bstep (se 3 (by rfl) ⟨1458347, by rfl⟩ : syracuseStep 7777853 = 2916695) B2916695
theorem B5185235 : Blo 2047435 5185235 := bstep (se 1 (by rfl) ⟨3888926, by rfl⟩ : syracuseStep 5185235 = 7777853) B7777853
theorem B3456823 : Blo 2047435 3456823 := bstep (se 1 (by rfl) ⟨2592617, by rfl⟩ : syracuseStep 3456823 = 5185235) B5185235
theorem B4609097 : Blo 2047435 4609097 := bstep (se 2 (by rfl) ⟨1728411, by rfl⟩ : syracuseStep 4609097 = 3456823) B3456823
theorem B3072731 : Blo 2047435 3072731 := bstep (se 1 (by rfl) ⟨2304548, by rfl⟩ : syracuseStep 3072731 = 4609097) B4609097
theorem B2048487 : Blo 2047435 2048487 := bstep (se 1 (by rfl) ⟨1536365, by rfl⟩ : syracuseStep 2048487 = 3072731) B3072731
theorem B2304553 : Blo 2047435 2304553 := bbase (se 2 (by rfl) ⟨864207, by rfl⟩ : syracuseStep 2304553 = 1728415) (by norm_num)
theorem B3072737 : Blo 2047435 3072737 := bstep (se 2 (by rfl) ⟨1152276, by rfl⟩ : syracuseStep 3072737 = 2304553) B2304553
theorem B2048491 : Blo 2047435 2048491 := bstep (se 1 (by rfl) ⟨1536368, by rfl⟩ : syracuseStep 2048491 = 3072737) B3072737
theorem B2628001 : Blo 2047435 2628001 := bbase (se 2 (by rfl) ⟨985500, by rfl⟩ : syracuseStep 2628001 = 1971001) (by norm_num)
theorem B3504001 : Blo 2047435 3504001 := bstep (se 2 (by rfl) ⟨1314000, by rfl⟩ : syracuseStep 3504001 = 2628001) B2628001
theorem B4672001 : Blo 2047435 4672001 := bstep (se 2 (by rfl) ⟨1752000, by rfl⟩ : syracuseStep 4672001 = 3504001) B3504001
theorem B3114667 : Blo 2047435 3114667 := bstep (se 1 (by rfl) ⟨2336000, by rfl⟩ : syracuseStep 3114667 = 4672001) B4672001
theorem B4152889 : Blo 2047435 4152889 := bstep (se 2 (by rfl) ⟨1557333, by rfl⟩ : syracuseStep 4152889 = 3114667) B3114667
theorem B22148741 : Blo 2047435 22148741 := bstep (se 4 (by rfl) ⟨2076444, by rfl⟩ : syracuseStep 22148741 = 4152889) B4152889
theorem B14765827 : Blo 2047435 14765827 := bstep (se 1 (by rfl) ⟨11074370, by rfl⟩ : syracuseStep 14765827 = 22148741) B22148741
theorem B19687769 : Blo 2047435 19687769 := bstep (se 2 (by rfl) ⟨7382913, by rfl⟩ : syracuseStep 19687769 = 14765827) B14765827
theorem B13125179 : Blo 2047435 13125179 := bstep (se 1 (by rfl) ⟨9843884, by rfl⟩ : syracuseStep 13125179 = 19687769) B19687769
theorem B8750119 : Blo 2047435 8750119 := bstep (se 1 (by rfl) ⟨6562589, by rfl⟩ : syracuseStep 8750119 = 13125179) B13125179
theorem B11666825 : Blo 2047435 11666825 := bstep (se 2 (by rfl) ⟨4375059, by rfl⟩ : syracuseStep 11666825 = 8750119) B8750119
theorem B7777883 : Blo 2047435 7777883 := bstep (se 1 (by rfl) ⟨5833412, by rfl⟩ : syracuseStep 7777883 = 11666825) B11666825
theorem B5185255 : Blo 2047435 5185255 := bstep (se 1 (by rfl) ⟨3888941, by rfl⟩ : syracuseStep 5185255 = 7777883) B7777883
theorem B6913673 : Blo 2047435 6913673 := bstep (se 2 (by rfl) ⟨2592627, by rfl⟩ : syracuseStep 6913673 = 5185255) B5185255
theorem B4609115 : Blo 2047435 4609115 := bstep (se 1 (by rfl) ⟨3456836, by rfl⟩ : syracuseStep 4609115 = 6913673) B6913673
theorem B3072743 : Blo 2047435 3072743 := bstep (se 1 (by rfl) ⟨2304557, by rfl⟩ : syracuseStep 3072743 = 4609115) B4609115
theorem B2048495 : Blo 2047435 2048495 := bstep (se 1 (by rfl) ⟨1536371, by rfl⟩ : syracuseStep 2048495 = 3072743) B3072743
theorem B3072749 : Blo 2047435 3072749 := bbase (se 3 (by rfl) ⟨576140, by rfl⟩ : syracuseStep 3072749 = 1152281) (by norm_num)
theorem B2048499 : Blo 2047435 2048499 := bstep (se 1 (by rfl) ⟨1536374, by rfl⟩ : syracuseStep 2048499 = 3072749) B3072749
theorem B4609133 : Blo 2047435 4609133 := bbase (se 3 (by rfl) ⟨864212, by rfl⟩ : syracuseStep 4609133 = 1728425) (by norm_num)
theorem B3072755 : Blo 2047435 3072755 := bstep (se 1 (by rfl) ⟨2304566, by rfl⟩ : syracuseStep 3072755 = 4609133) B4609133
theorem B2048503 : Blo 2047435 2048503 := bstep (se 1 (by rfl) ⟨1536377, by rfl⟩ : syracuseStep 2048503 = 3072755) B3072755
theorem B3888965 : Blo 2047435 3888965 := bbase (se 4 (by rfl) ⟨364590, by rfl⟩ : syracuseStep 3888965 = 729181) (by norm_num)
theorem B2592643 : Blo 2047435 2592643 := bstep (se 1 (by rfl) ⟨1944482, by rfl⟩ : syracuseStep 2592643 = 3888965) B3888965
theorem B3456857 : Blo 2047435 3456857 := bstep (se 2 (by rfl) ⟨1296321, by rfl⟩ : syracuseStep 3456857 = 2592643) B2592643
theorem B2304571 : Blo 2047435 2304571 := bstep (se 1 (by rfl) ⟨1728428, by rfl⟩ : syracuseStep 2304571 = 3456857) B3456857
theorem B3072761 : Blo 2047435 3072761 := bstep (se 2 (by rfl) ⟨1152285, by rfl⟩ : syracuseStep 3072761 = 2304571) B2304571
theorem B2048507 : Blo 2047435 2048507 := bstep (se 1 (by rfl) ⟨1536380, by rfl⟩ : syracuseStep 2048507 = 3072761) B3072761
theorem B10655509 : Blo 2047435 10655509 := bbase (se 6 (by rfl) ⟨249738, by rfl⟩ : syracuseStep 10655509 = 499477) (by norm_num)
theorem B14207345 : Blo 2047435 14207345 := bstep (se 2 (by rfl) ⟨5327754, by rfl⟩ : syracuseStep 14207345 = 10655509) B10655509
theorem B9471563 : Blo 2047435 9471563 := bstep (se 1 (by rfl) ⟨7103672, by rfl⟩ : syracuseStep 9471563 = 14207345) B14207345
theorem B6314375 : Blo 2047435 6314375 := bstep (se 1 (by rfl) ⟨4735781, by rfl⟩ : syracuseStep 6314375 = 9471563) B9471563
theorem B4209583 : Blo 2047435 4209583 := bstep (se 1 (by rfl) ⟨3157187, by rfl⟩ : syracuseStep 4209583 = 6314375) B6314375
theorem B5612777 : Blo 2047435 5612777 := bstep (se 2 (by rfl) ⟨2104791, by rfl⟩ : syracuseStep 5612777 = 4209583) B4209583
theorem B3741851 : Blo 2047435 3741851 := bstep (se 1 (by rfl) ⟨2806388, by rfl⟩ : syracuseStep 3741851 = 5612777) B5612777
theorem B2494567 : Blo 2047435 2494567 := bstep (se 1 (by rfl) ⟨1870925, by rfl⟩ : syracuseStep 2494567 = 3741851) B3741851
theorem B3326089 : Blo 2047435 3326089 := bstep (se 2 (by rfl) ⟨1247283, by rfl⟩ : syracuseStep 3326089 = 2494567) B2494567
theorem B4434785 : Blo 2047435 4434785 := bstep (se 2 (by rfl) ⟨1663044, by rfl⟩ : syracuseStep 4434785 = 3326089) B3326089
theorem B2956523 : Blo 2047435 2956523 := bstep (se 1 (by rfl) ⟨2217392, by rfl⟩ : syracuseStep 2956523 = 4434785) B4434785
theorem B7884061 : Blo 2047435 7884061 := bstep (se 3 (by rfl) ⟨1478261, by rfl⟩ : syracuseStep 7884061 = 2956523) B2956523
theorem B42048325 : Blo 2047435 42048325 := bstep (se 4 (by rfl) ⟨3942030, by rfl⟩ : syracuseStep 42048325 = 7884061) B7884061
theorem B56064433 : Blo 2047435 56064433 := bstep (se 2 (by rfl) ⟨21024162, by rfl⟩ : syracuseStep 56064433 = 42048325) B42048325
theorem B74752577 : Blo 2047435 74752577 := bstep (se 2 (by rfl) ⟨28032216, by rfl⟩ : syracuseStep 74752577 = 56064433) B56064433
theorem B49835051 : Blo 2047435 49835051 := bstep (se 1 (by rfl) ⟨37376288, by rfl⟩ : syracuseStep 49835051 = 74752577) B74752577
theorem B33223367 : Blo 2047435 33223367 := bstep (se 1 (by rfl) ⟨24917525, by rfl⟩ : syracuseStep 33223367 = 49835051) B49835051
theorem B22148911 : Blo 2047435 22148911 := bstep (se 1 (by rfl) ⟨16611683, by rfl⟩ : syracuseStep 22148911 = 33223367) B33223367
theorem B29531881 : Blo 2047435 29531881 := bstep (se 2 (by rfl) ⟨11074455, by rfl⟩ : syracuseStep 29531881 = 22148911) B22148911
theorem B39375841 : Blo 2047435 39375841 := bstep (se 2 (by rfl) ⟨14765940, by rfl⟩ : syracuseStep 39375841 = 29531881) B29531881
theorem B52501121 : Blo 2047435 52501121 := bstep (se 2 (by rfl) ⟨19687920, by rfl⟩ : syracuseStep 52501121 = 39375841) B39375841
theorem B35000747 : Blo 2047435 35000747 := bstep (se 1 (by rfl) ⟨26250560, by rfl⟩ : syracuseStep 35000747 = 52501121) B52501121
theorem B23333831 : Blo 2047435 23333831 := bstep (se 1 (by rfl) ⟨17500373, by rfl⟩ : syracuseStep 23333831 = 35000747) B35000747
theorem B15555887 : Blo 2047435 15555887 := bstep (se 1 (by rfl) ⟨11666915, by rfl⟩ : syracuseStep 15555887 = 23333831) B23333831
theorem B10370591 : Blo 2047435 10370591 := bstep (se 1 (by rfl) ⟨7777943, by rfl⟩ : syracuseStep 10370591 = 15555887) B15555887
theorem B6913727 : Blo 2047435 6913727 := bstep (se 1 (by rfl) ⟨5185295, by rfl⟩ : syracuseStep 6913727 = 10370591) B10370591
theorem B4609151 : Blo 2047435 4609151 := bstep (se 1 (by rfl) ⟨3456863, by rfl⟩ : syracuseStep 4609151 = 6913727) B6913727
theorem B3072767 : Blo 2047435 3072767 := bstep (se 1 (by rfl) ⟨2304575, by rfl⟩ : syracuseStep 3072767 = 4609151) B4609151
theorem B2048511 : Blo 2047435 2048511 := bstep (se 1 (by rfl) ⟨1536383, by rfl⟩ : syracuseStep 2048511 = 3072767) B3072767
theorem B3072773 : Blo 2047435 3072773 := bbase (se 4 (by rfl) ⟨288072, by rfl⟩ : syracuseStep 3072773 = 576145) (by norm_num)
theorem B2048515 : Blo 2047435 2048515 := bstep (se 1 (by rfl) ⟨1536386, by rfl⟩ : syracuseStep 2048515 = 3072773) B3072773
theorem B3456877 : Blo 2047435 3456877 := bbase (se 3 (by rfl) ⟨648164, by rfl⟩ : syracuseStep 3456877 = 1296329) (by norm_num)
theorem B4609169 : Blo 2047435 4609169 := bstep (se 2 (by rfl) ⟨1728438, by rfl⟩ : syracuseStep 4609169 = 3456877) B3456877
theorem B3072779 : Blo 2047435 3072779 := bstep (se 1 (by rfl) ⟨2304584, by rfl⟩ : syracuseStep 3072779 = 4609169) B4609169
theorem B2048519 : Blo 2047435 2048519 := bstep (se 1 (by rfl) ⟨1536389, by rfl⟩ : syracuseStep 2048519 = 3072779) B3072779
theorem B2304589 : Blo 2047435 2304589 := bbase (se 3 (by rfl) ⟨432110, by rfl⟩ : syracuseStep 2304589 = 864221) (by norm_num)
theorem B3072785 : Blo 2047435 3072785 := bstep (se 2 (by rfl) ⟨1152294, by rfl⟩ : syracuseStep 3072785 = 2304589) B2304589
theorem B2048523 : Blo 2047435 2048523 := bstep (se 1 (by rfl) ⟨1536392, by rfl⟩ : syracuseStep 2048523 = 3072785) B3072785
theorem B6913781 : Blo 2047435 6913781 := bbase (se 5 (by rfl) ⟨324083, by rfl⟩ : syracuseStep 6913781 = 648167) (by norm_num)
theorem B4609187 : Blo 2047435 4609187 := bstep (se 1 (by rfl) ⟨3456890, by rfl⟩ : syracuseStep 4609187 = 6913781) B6913781
theorem B3072791 : Blo 2047435 3072791 := bstep (se 1 (by rfl) ⟨2304593, by rfl⟩ : syracuseStep 3072791 = 4609187) B4609187
theorem B2048527 : Blo 2047435 2048527 := bstep (se 1 (by rfl) ⟨1536395, by rfl⟩ : syracuseStep 2048527 = 3072791) B3072791
theorem B3072797 : Blo 2047435 3072797 := bbase (se 3 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 3072797 = 1152299) (by norm_num)
theorem B2048531 : Blo 2047435 2048531 := bstep (se 1 (by rfl) ⟨1536398, by rfl⟩ : syracuseStep 2048531 = 3072797) B3072797
theorem B4609205 : Blo 2047435 4609205 := bbase (se 5 (by rfl) ⟨216056, by rfl⟩ : syracuseStep 4609205 = 432113) (by norm_num)
theorem B3072803 : Blo 2047435 3072803 := bstep (se 1 (by rfl) ⟨2304602, by rfl⟩ : syracuseStep 3072803 = 4609205) B4609205
theorem B2048535 : Blo 2047435 2048535 := bstep (se 1 (by rfl) ⟨1536401, by rfl⟩ : syracuseStep 2048535 = 3072803) B3072803
theorem B2187577 : Blo 2047435 2187577 := bbase (se 2 (by rfl) ⟨820341, by rfl⟩ : syracuseStep 2187577 = 1640683) (by norm_num)
theorem B11667077 : Blo 2047435 11667077 := bstep (se 4 (by rfl) ⟨1093788, by rfl⟩ : syracuseStep 11667077 = 2187577) B2187577
theorem B7778051 : Blo 2047435 7778051 := bstep (se 1 (by rfl) ⟨5833538, by rfl⟩ : syracuseStep 7778051 = 11667077) B11667077
theorem B5185367 : Blo 2047435 5185367 := bstep (se 1 (by rfl) ⟨3889025, by rfl⟩ : syracuseStep 5185367 = 7778051) B7778051
theorem B3456911 : Blo 2047435 3456911 := bstep (se 1 (by rfl) ⟨2592683, by rfl⟩ : syracuseStep 3456911 = 5185367) B5185367
theorem B2304607 : Blo 2047435 2304607 := bstep (se 1 (by rfl) ⟨1728455, by rfl⟩ : syracuseStep 2304607 = 3456911) B3456911
theorem B3072809 : Blo 2047435 3072809 := bstep (se 2 (by rfl) ⟨1152303, by rfl⟩ : syracuseStep 3072809 = 2304607) B2304607
theorem B2048539 : Blo 2047435 2048539 := bstep (se 1 (by rfl) ⟨1536404, by rfl⟩ : syracuseStep 2048539 = 3072809) B3072809
theorem B2187581 : Blo 2047435 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B5833549 : Blo 2047435 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B7778065 : Blo 2047435 7778065 := bstep (se 2 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 7778065 = 5833549) B5833549
theorem B10370753 : Blo 2047435 10370753 := bstep (se 2 (by rfl) ⟨3889032, by rfl⟩ : syracuseStep 10370753 = 7778065) B7778065
theorem B6913835 : Blo 2047435 6913835 := bstep (se 1 (by rfl) ⟨5185376, by rfl⟩ : syracuseStep 6913835 = 10370753) B10370753
theorem B4609223 : Blo 2047435 4609223 := bstep (se 1 (by rfl) ⟨3456917, by rfl⟩ : syracuseStep 4609223 = 6913835) B6913835
theorem B3072815 : Blo 2047435 3072815 := bstep (se 1 (by rfl) ⟨2304611, by rfl⟩ : syracuseStep 3072815 = 4609223) B4609223
theorem B2048543 : Blo 2047435 2048543 := bstep (se 1 (by rfl) ⟨1536407, by rfl⟩ : syracuseStep 2048543 = 3072815) B3072815
theorem B3072821 : Blo 2047435 3072821 := bbase (se 5 (by rfl) ⟨144038, by rfl⟩ : syracuseStep 3072821 = 288077) (by norm_num)
theorem B2048547 : Blo 2047435 2048547 := bstep (se 1 (by rfl) ⟨1536410, by rfl⟩ : syracuseStep 2048547 = 3072821) B3072821
theorem B5185397 : Blo 2047435 5185397 := bbase (se 5 (by rfl) ⟨243065, by rfl⟩ : syracuseStep 5185397 = 486131) (by norm_num)
theorem B3456931 : Blo 2047435 3456931 := bstep (se 1 (by rfl) ⟨2592698, by rfl⟩ : syracuseStep 3456931 = 5185397) B5185397
theorem B4609241 : Blo 2047435 4609241 := bstep (se 2 (by rfl) ⟨1728465, by rfl⟩ : syracuseStep 4609241 = 3456931) B3456931
theorem B3072827 : Blo 2047435 3072827 := bstep (se 1 (by rfl) ⟨2304620, by rfl⟩ : syracuseStep 3072827 = 4609241) B4609241
theorem B2048551 : Blo 2047435 2048551 := bstep (se 1 (by rfl) ⟨1536413, by rfl⟩ : syracuseStep 2048551 = 3072827) B3072827
theorem B2304625 : Blo 2047435 2304625 := bbase (se 2 (by rfl) ⟨864234, by rfl⟩ : syracuseStep 2304625 = 1728469) (by norm_num)
theorem B3072833 : Blo 2047435 3072833 := bstep (se 2 (by rfl) ⟨1152312, by rfl⟩ : syracuseStep 3072833 = 2304625) B2304625
theorem B2048555 : Blo 2047435 2048555 := bstep (se 1 (by rfl) ⟨1536416, by rfl⟩ : syracuseStep 2048555 = 3072833) B3072833
theorem B3942125 : Blo 2047435 3942125 := bbase (se 3 (by rfl) ⟨739148, by rfl⟩ : syracuseStep 3942125 = 1478297) (by norm_num)
theorem B2628083 : Blo 2047435 2628083 := bstep (se 1 (by rfl) ⟨1971062, by rfl⟩ : syracuseStep 2628083 = 3942125) B3942125
theorem B7008221 : Blo 2047435 7008221 := bstep (se 3 (by rfl) ⟨1314041, by rfl⟩ : syracuseStep 7008221 = 2628083) B2628083
theorem B18688589 : Blo 2047435 18688589 := bstep (se 3 (by rfl) ⟨3504110, by rfl⟩ : syracuseStep 18688589 = 7008221) B7008221
theorem B12459059 : Blo 2047435 12459059 := bstep (se 1 (by rfl) ⟨9344294, by rfl⟩ : syracuseStep 12459059 = 18688589) B18688589
theorem B8306039 : Blo 2047435 8306039 := bstep (se 1 (by rfl) ⟨6229529, by rfl⟩ : syracuseStep 8306039 = 12459059) B12459059
theorem B5537359 : Blo 2047435 5537359 := bstep (se 1 (by rfl) ⟨4153019, by rfl⟩ : syracuseStep 5537359 = 8306039) B8306039
theorem B7383145 : Blo 2047435 7383145 := bstep (se 2 (by rfl) ⟨2768679, by rfl⟩ : syracuseStep 7383145 = 5537359) B5537359
theorem B9844193 : Blo 2047435 9844193 := bstep (se 2 (by rfl) ⟨3691572, by rfl⟩ : syracuseStep 9844193 = 7383145) B7383145
theorem B6562795 : Blo 2047435 6562795 := bstep (se 1 (by rfl) ⟨4922096, by rfl⟩ : syracuseStep 6562795 = 9844193) B9844193
theorem B8750393 : Blo 2047435 8750393 := bstep (se 2 (by rfl) ⟨3281397, by rfl⟩ : syracuseStep 8750393 = 6562795) B6562795
theorem B5833595 : Blo 2047435 5833595 := bstep (se 1 (by rfl) ⟨4375196, by rfl⟩ : syracuseStep 5833595 = 8750393) B8750393
theorem B3889063 : Blo 2047435 3889063 := bstep (se 1 (by rfl) ⟨2916797, by rfl⟩ : syracuseStep 3889063 = 5833595) B5833595
theorem B5185417 : Blo 2047435 5185417 := bstep (se 2 (by rfl) ⟨1944531, by rfl⟩ : syracuseStep 5185417 = 3889063) B3889063
theorem B6913889 : Blo 2047435 6913889 := bstep (se 2 (by rfl) ⟨2592708, by rfl⟩ : syracuseStep 6913889 = 5185417) B5185417
theorem B4609259 : Blo 2047435 4609259 := bstep (se 1 (by rfl) ⟨3456944, by rfl⟩ : syracuseStep 4609259 = 6913889) B6913889
theorem B3072839 : Blo 2047435 3072839 := bstep (se 1 (by rfl) ⟨2304629, by rfl⟩ : syracuseStep 3072839 = 4609259) B4609259
theorem B2048559 : Blo 2047435 2048559 := bstep (se 1 (by rfl) ⟨1536419, by rfl⟩ : syracuseStep 2048559 = 3072839) B3072839
theorem B3072845 : Blo 2047435 3072845 := bbase (se 3 (by rfl) ⟨576158, by rfl⟩ : syracuseStep 3072845 = 1152317) (by norm_num)
theorem B2048563 : Blo 2047435 2048563 := bstep (se 1 (by rfl) ⟨1536422, by rfl⟩ : syracuseStep 2048563 = 3072845) B3072845
theorem B4609277 : Blo 2047435 4609277 := bbase (se 3 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 4609277 = 1728479) (by norm_num)
theorem B3072851 : Blo 2047435 3072851 := bstep (se 1 (by rfl) ⟨2304638, by rfl⟩ : syracuseStep 3072851 = 4609277) B4609277
theorem B2048567 : Blo 2047435 2048567 := bstep (se 1 (by rfl) ⟨1536425, by rfl⟩ : syracuseStep 2048567 = 3072851) B3072851
theorem B3456965 : Blo 2047435 3456965 := bbase (se 4 (by rfl) ⟨324090, by rfl⟩ : syracuseStep 3456965 = 648181) (by norm_num)
theorem B2304643 : Blo 2047435 2304643 := bstep (se 1 (by rfl) ⟨1728482, by rfl⟩ : syracuseStep 2304643 = 3456965) B3456965
theorem B3072857 : Blo 2047435 3072857 := bstep (se 2 (by rfl) ⟨1152321, by rfl⟩ : syracuseStep 3072857 = 2304643) B2304643
theorem B2048571 : Blo 2047435 2048571 := bstep (se 1 (by rfl) ⟨1536428, by rfl⟩ : syracuseStep 2048571 = 3072857) B3072857
theorem B15556373 : Blo 2047435 15556373 := bbase (se 6 (by rfl) ⟨364602, by rfl⟩ : syracuseStep 15556373 = 729205) (by norm_num)
theorem B10370915 : Blo 2047435 10370915 := bstep (se 1 (by rfl) ⟨7778186, by rfl⟩ : syracuseStep 10370915 = 15556373) B15556373
theorem B6913943 : Blo 2047435 6913943 := bstep (se 1 (by rfl) ⟨5185457, by rfl⟩ : syracuseStep 6913943 = 10370915) B10370915
theorem B4609295 : Blo 2047435 4609295 := bstep (se 1 (by rfl) ⟨3456971, by rfl⟩ : syracuseStep 4609295 = 6913943) B6913943
theorem B3072863 : Blo 2047435 3072863 := bstep (se 1 (by rfl) ⟨2304647, by rfl⟩ : syracuseStep 3072863 = 4609295) B4609295
theorem B2048575 : Blo 2047435 2048575 := bstep (se 1 (by rfl) ⟨1536431, by rfl⟩ : syracuseStep 2048575 = 3072863) B3072863
theorem B3072869 : Blo 2047435 3072869 := bbase (se 4 (by rfl) ⟨288081, by rfl⟩ : syracuseStep 3072869 = 576163) (by norm_num)
theorem B2048579 : Blo 2047435 2048579 := bstep (se 1 (by rfl) ⟨1536434, by rfl⟩ : syracuseStep 2048579 = 3072869) B3072869
theorem B3889109 : Blo 2047435 3889109 := bbase (se 7 (by rfl) ⟨45575, by rfl⟩ : syracuseStep 3889109 = 91151) (by norm_num)
theorem B2592739 : Blo 2047435 2592739 := bstep (se 1 (by rfl) ⟨1944554, by rfl⟩ : syracuseStep 2592739 = 3889109) B3889109
theorem B3456985 : Blo 2047435 3456985 := bstep (se 2 (by rfl) ⟨1296369, by rfl⟩ : syracuseStep 3456985 = 2592739) B2592739
theorem B4609313 : Blo 2047435 4609313 := bstep (se 2 (by rfl) ⟨1728492, by rfl⟩ : syracuseStep 4609313 = 3456985) B3456985
theorem B3072875 : Blo 2047435 3072875 := bstep (se 1 (by rfl) ⟨2304656, by rfl⟩ : syracuseStep 3072875 = 4609313) B4609313
theorem B2048583 : Blo 2047435 2048583 := bstep (se 1 (by rfl) ⟨1536437, by rfl⟩ : syracuseStep 2048583 = 3072875) B3072875
theorem B2304661 : Blo 2047435 2304661 := bbase (se 6 (by rfl) ⟨54015, by rfl⟩ : syracuseStep 2304661 = 108031) (by norm_num)
theorem B3072881 : Blo 2047435 3072881 := bstep (se 2 (by rfl) ⟨1152330, by rfl⟩ : syracuseStep 3072881 = 2304661) B2304661
theorem B2048587 : Blo 2047435 2048587 := bstep (se 1 (by rfl) ⟨1536440, by rfl⟩ : syracuseStep 2048587 = 3072881) B3072881
theorem B2592749 : Blo 2047435 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B6913997 : Blo 2047435 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B4609331 : Blo 2047435 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B3072887 : Blo 2047435 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B2048591 : Blo 2047435 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B3072893 : Blo 2047435 3072893 := bbase (se 3 (by rfl) ⟨576167, by rfl⟩ : syracuseStep 3072893 = 1152335) (by norm_num)
theorem B2048595 : Blo 2047435 2048595 := bstep (se 1 (by rfl) ⟨1536446, by rfl⟩ : syracuseStep 2048595 = 3072893) B3072893
theorem B4609349 : Blo 2047435 4609349 := bbase (se 4 (by rfl) ⟨432126, by rfl⟩ : syracuseStep 4609349 = 864253) (by norm_num)
theorem B3072899 : Blo 2047435 3072899 := bstep (se 1 (by rfl) ⟨2304674, by rfl⟩ : syracuseStep 3072899 = 4609349) B4609349
theorem B2048599 : Blo 2047435 2048599 := bstep (se 1 (by rfl) ⟨1536449, by rfl⟩ : syracuseStep 2048599 = 3072899) B3072899
theorem B7008373 : Blo 2047435 7008373 := bbase (se 5 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 7008373 = 657035) (by norm_num)
theorem B9344497 : Blo 2047435 9344497 := bstep (se 2 (by rfl) ⟨3504186, by rfl⟩ : syracuseStep 9344497 = 7008373) B7008373
theorem B12459329 : Blo 2047435 12459329 := bstep (se 2 (by rfl) ⟨4672248, by rfl⟩ : syracuseStep 12459329 = 9344497) B9344497
theorem B8306219 : Blo 2047435 8306219 := bstep (se 1 (by rfl) ⟨6229664, by rfl⟩ : syracuseStep 8306219 = 12459329) B12459329
theorem B5537479 : Blo 2047435 5537479 := bstep (se 1 (by rfl) ⟨4153109, by rfl⟩ : syracuseStep 5537479 = 8306219) B8306219
theorem B7383305 : Blo 2047435 7383305 := bstep (se 2 (by rfl) ⟨2768739, by rfl⟩ : syracuseStep 7383305 = 5537479) B5537479
theorem B4922203 : Blo 2047435 4922203 := bstep (se 1 (by rfl) ⟨3691652, by rfl⟩ : syracuseStep 4922203 = 7383305) B7383305
theorem B6562937 : Blo 2047435 6562937 := bstep (se 2 (by rfl) ⟨2461101, by rfl⟩ : syracuseStep 6562937 = 4922203) B4922203
theorem B4375291 : Blo 2047435 4375291 := bstep (se 1 (by rfl) ⟨3281468, by rfl⟩ : syracuseStep 4375291 = 6562937) B6562937
theorem B5833721 : Blo 2047435 5833721 := bstep (se 2 (by rfl) ⟨2187645, by rfl⟩ : syracuseStep 5833721 = 4375291) B4375291
theorem B3889147 : Blo 2047435 3889147 := bstep (se 1 (by rfl) ⟨2916860, by rfl⟩ : syracuseStep 3889147 = 5833721) B5833721
theorem B5185529 : Blo 2047435 5185529 := bstep (se 2 (by rfl) ⟨1944573, by rfl⟩ : syracuseStep 5185529 = 3889147) B3889147
theorem B3457019 : Blo 2047435 3457019 := bstep (se 1 (by rfl) ⟨2592764, by rfl⟩ : syracuseStep 3457019 = 5185529) B5185529
theorem B2304679 : Blo 2047435 2304679 := bstep (se 1 (by rfl) ⟨1728509, by rfl⟩ : syracuseStep 2304679 = 3457019) B3457019
theorem B3072905 : Blo 2047435 3072905 := bstep (se 2 (by rfl) ⟨1152339, by rfl⟩ : syracuseStep 3072905 = 2304679) B2304679
theorem B2048603 : Blo 2047435 2048603 := bstep (se 1 (by rfl) ⟨1536452, by rfl⟩ : syracuseStep 2048603 = 3072905) B3072905
theorem B10371077 : Blo 2047435 10371077 := bbase (se 4 (by rfl) ⟨972288, by rfl⟩ : syracuseStep 10371077 = 1944577) (by norm_num)
theorem B6914051 : Blo 2047435 6914051 := bstep (se 1 (by rfl) ⟨5185538, by rfl⟩ : syracuseStep 6914051 = 10371077) B10371077
theorem B4609367 : Blo 2047435 4609367 := bstep (se 1 (by rfl) ⟨3457025, by rfl⟩ : syracuseStep 4609367 = 6914051) B6914051
theorem B3072911 : Blo 2047435 3072911 := bstep (se 1 (by rfl) ⟨2304683, by rfl⟩ : syracuseStep 3072911 = 4609367) B4609367
theorem B2048607 : Blo 2047435 2048607 := bstep (se 1 (by rfl) ⟨1536455, by rfl⟩ : syracuseStep 2048607 = 3072911) B3072911
theorem B3072917 : Blo 2047435 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B2048611 : Blo 2047435 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B11667509 : Blo 2047435 11667509 := bbase (se 5 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 11667509 = 1093829) (by norm_num)
theorem B7778339 : Blo 2047435 7778339 := bstep (se 1 (by rfl) ⟨5833754, by rfl⟩ : syracuseStep 7778339 = 11667509) B11667509
theorem B5185559 : Blo 2047435 5185559 := bstep (se 1 (by rfl) ⟨3889169, by rfl⟩ : syracuseStep 5185559 = 7778339) B7778339
theorem B3457039 : Blo 2047435 3457039 := bstep (se 1 (by rfl) ⟨2592779, by rfl⟩ : syracuseStep 3457039 = 5185559) B5185559
theorem B4609385 : Blo 2047435 4609385 := bstep (se 2 (by rfl) ⟨1728519, by rfl⟩ : syracuseStep 4609385 = 3457039) B3457039
theorem B3072923 : Blo 2047435 3072923 := bstep (se 1 (by rfl) ⟨2304692, by rfl⟩ : syracuseStep 3072923 = 4609385) B4609385
theorem B2048615 : Blo 2047435 2048615 := bstep (se 1 (by rfl) ⟨1536461, by rfl⟩ : syracuseStep 2048615 = 3072923) B3072923
theorem B2304697 : Blo 2047435 2304697 := bbase (se 2 (by rfl) ⟨864261, by rfl⟩ : syracuseStep 2304697 = 1728523) (by norm_num)
theorem B3072929 : Blo 2047435 3072929 := bstep (se 2 (by rfl) ⟨1152348, by rfl⟩ : syracuseStep 3072929 = 2304697) B2304697
theorem B2048619 : Blo 2047435 2048619 := bstep (se 1 (by rfl) ⟨1536464, by rfl⟩ : syracuseStep 2048619 = 3072929) B3072929
theorem B4375333 : Blo 2047435 4375333 := bbase (se 4 (by rfl) ⟨410187, by rfl⟩ : syracuseStep 4375333 = 820375) (by norm_num)
theorem B5833777 : Blo 2047435 5833777 := bstep (se 2 (by rfl) ⟨2187666, by rfl⟩ : syracuseStep 5833777 = 4375333) B4375333
theorem B7778369 : Blo 2047435 7778369 := bstep (se 2 (by rfl) ⟨2916888, by rfl⟩ : syracuseStep 7778369 = 5833777) B5833777
theorem B5185579 : Blo 2047435 5185579 := bstep (se 1 (by rfl) ⟨3889184, by rfl⟩ : syracuseStep 5185579 = 7778369) B7778369
theorem B6914105 : Blo 2047435 6914105 := bstep (se 2 (by rfl) ⟨2592789, by rfl⟩ : syracuseStep 6914105 = 5185579) B5185579
theorem B4609403 : Blo 2047435 4609403 := bstep (se 1 (by rfl) ⟨3457052, by rfl⟩ : syracuseStep 4609403 = 6914105) B6914105
theorem B3072935 : Blo 2047435 3072935 := bstep (se 1 (by rfl) ⟨2304701, by rfl⟩ : syracuseStep 3072935 = 4609403) B4609403
theorem B2048623 : Blo 2047435 2048623 := bstep (se 1 (by rfl) ⟨1536467, by rfl⟩ : syracuseStep 2048623 = 3072935) B3072935
theorem B3072941 : Blo 2047435 3072941 := bbase (se 3 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 3072941 = 1152353) (by norm_num)
theorem B2048627 : Blo 2047435 2048627 := bstep (se 1 (by rfl) ⟨1536470, by rfl⟩ : syracuseStep 2048627 = 3072941) B3072941
theorem B4609421 : Blo 2047435 4609421 := bbase (se 3 (by rfl) ⟨864266, by rfl⟩ : syracuseStep 4609421 = 1728533) (by norm_num)
theorem B3072947 : Blo 2047435 3072947 := bstep (se 1 (by rfl) ⟨2304710, by rfl⟩ : syracuseStep 3072947 = 4609421) B4609421
theorem B2048631 : Blo 2047435 2048631 := bstep (se 1 (by rfl) ⟨1536473, by rfl⟩ : syracuseStep 2048631 = 3072947) B3072947
theorem B2592805 : Blo 2047435 2592805 := bbase (se 4 (by rfl) ⟨243075, by rfl⟩ : syracuseStep 2592805 = 486151) (by norm_num)
theorem B3457073 : Blo 2047435 3457073 := bstep (se 2 (by rfl) ⟨1296402, by rfl⟩ : syracuseStep 3457073 = 2592805) B2592805
theorem B2304715 : Blo 2047435 2304715 := bstep (se 1 (by rfl) ⟨1728536, by rfl⟩ : syracuseStep 2304715 = 3457073) B3457073
theorem B3072953 : Blo 2047435 3072953 := bstep (se 2 (by rfl) ⟨1152357, by rfl⟩ : syracuseStep 3072953 = 2304715) B2304715
theorem B2048635 : Blo 2047435 2048635 := bstep (se 1 (by rfl) ⟨1536476, by rfl⟩ : syracuseStep 2048635 = 3072953) B3072953
theorem B5328085 : Blo 2047435 5328085 := bbase (se 7 (by rfl) ⟨62438, by rfl⟩ : syracuseStep 5328085 = 124877) (by norm_num)
theorem B7104113 : Blo 2047435 7104113 := bstep (se 2 (by rfl) ⟨2664042, by rfl⟩ : syracuseStep 7104113 = 5328085) B5328085
theorem B4736075 : Blo 2047435 4736075 := bstep (se 1 (by rfl) ⟨3552056, by rfl⟩ : syracuseStep 4736075 = 7104113) B7104113
theorem B12629533 : Blo 2047435 12629533 := bstep (se 3 (by rfl) ⟨2368037, by rfl⟩ : syracuseStep 12629533 = 4736075) B4736075
theorem B16839377 : Blo 2047435 16839377 := bstep (se 2 (by rfl) ⟨6314766, by rfl⟩ : syracuseStep 16839377 = 12629533) B12629533
theorem B11226251 : Blo 2047435 11226251 := bstep (se 1 (by rfl) ⟨8419688, by rfl⟩ : syracuseStep 11226251 = 16839377) B16839377
theorem B7484167 : Blo 2047435 7484167 := bstep (se 1 (by rfl) ⟨5613125, by rfl⟩ : syracuseStep 7484167 = 11226251) B11226251
theorem B9978889 : Blo 2047435 9978889 := bstep (se 2 (by rfl) ⟨3742083, by rfl⟩ : syracuseStep 9978889 = 7484167) B7484167
theorem B13305185 : Blo 2047435 13305185 := bstep (se 2 (by rfl) ⟨4989444, by rfl⟩ : syracuseStep 13305185 = 9978889) B9978889
theorem B8870123 : Blo 2047435 8870123 := bstep (se 1 (by rfl) ⟨6652592, by rfl⟩ : syracuseStep 8870123 = 13305185) B13305185
theorem B23653661 : Blo 2047435 23653661 := bstep (se 3 (by rfl) ⟨4435061, by rfl⟩ : syracuseStep 23653661 = 8870123) B8870123
theorem B63076429 : Blo 2047435 63076429 := bstep (se 3 (by rfl) ⟨11826830, by rfl⟩ : syracuseStep 63076429 = 23653661) B23653661
theorem B84101905 : Blo 2047435 84101905 := bstep (se 2 (by rfl) ⟨31538214, by rfl⟩ : syracuseStep 84101905 = 63076429) B63076429
theorem B112135873 : Blo 2047435 112135873 := bstep (se 2 (by rfl) ⟨42050952, by rfl⟩ : syracuseStep 112135873 = 84101905) B84101905
theorem B149514497 : Blo 2047435 149514497 := bstep (se 2 (by rfl) ⟨56067936, by rfl⟩ : syracuseStep 149514497 = 112135873) B112135873
theorem B99676331 : Blo 2047435 99676331 := bstep (se 1 (by rfl) ⟨74757248, by rfl⟩ : syracuseStep 99676331 = 149514497) B149514497
theorem B66450887 : Blo 2047435 66450887 := bstep (se 1 (by rfl) ⟨49838165, by rfl⟩ : syracuseStep 66450887 = 99676331) B99676331
theorem B44300591 : Blo 2047435 44300591 := bstep (se 1 (by rfl) ⟨33225443, by rfl⟩ : syracuseStep 44300591 = 66450887) B66450887
theorem B29533727 : Blo 2047435 29533727 := bstep (se 1 (by rfl) ⟨22150295, by rfl⟩ : syracuseStep 29533727 = 44300591) B44300591
theorem B19689151 : Blo 2047435 19689151 := bstep (se 1 (by rfl) ⟨14766863, by rfl⟩ : syracuseStep 19689151 = 29533727) B29533727
theorem B26252201 : Blo 2047435 26252201 := bstep (se 2 (by rfl) ⟨9844575, by rfl⟩ : syracuseStep 26252201 = 19689151) B19689151
theorem B17501467 : Blo 2047435 17501467 := bstep (se 1 (by rfl) ⟨13126100, by rfl⟩ : syracuseStep 17501467 = 26252201) B26252201
theorem B23335289 : Blo 2047435 23335289 := bstep (se 2 (by rfl) ⟨8750733, by rfl⟩ : syracuseStep 23335289 = 17501467) B17501467
theorem B15556859 : Blo 2047435 15556859 := bstep (se 1 (by rfl) ⟨11667644, by rfl⟩ : syracuseStep 15556859 = 23335289) B23335289
theorem B10371239 : Blo 2047435 10371239 := bstep (se 1 (by rfl) ⟨7778429, by rfl⟩ : syracuseStep 10371239 = 15556859) B15556859
theorem B6914159 : Blo 2047435 6914159 := bstep (se 1 (by rfl) ⟨5185619, by rfl⟩ : syracuseStep 6914159 = 10371239) B10371239
theorem B4609439 : Blo 2047435 4609439 := bstep (se 1 (by rfl) ⟨3457079, by rfl⟩ : syracuseStep 4609439 = 6914159) B6914159
theorem B3072959 : Blo 2047435 3072959 := bstep (se 1 (by rfl) ⟨2304719, by rfl⟩ : syracuseStep 3072959 = 4609439) B4609439
theorem B2048639 : Blo 2047435 2048639 := bstep (se 1 (by rfl) ⟨1536479, by rfl⟩ : syracuseStep 2048639 = 3072959) B3072959
theorem B3072965 : Blo 2047435 3072965 := bbase (se 4 (by rfl) ⟨288090, by rfl⟩ : syracuseStep 3072965 = 576181) (by norm_num)
theorem B2048643 : Blo 2047435 2048643 := bstep (se 1 (by rfl) ⟨1536482, by rfl⟩ : syracuseStep 2048643 = 3072965) B3072965
theorem B3457093 : Blo 2047435 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B4609457 : Blo 2047435 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B3072971 : Blo 2047435 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2048647 : Blo 2047435 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B2304733 : Blo 2047435 2304733 := bbase (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) (by norm_num)
theorem B3072977 : Blo 2047435 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B2048651 : Blo 2047435 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B6914213 : Blo 2047435 6914213 := bbase (se 4 (by rfl) ⟨648207, by rfl⟩ : syracuseStep 6914213 = 1296415) (by norm_num)
theorem B4609475 : Blo 2047435 4609475 := bstep (se 1 (by rfl) ⟨3457106, by rfl⟩ : syracuseStep 4609475 = 6914213) B6914213
theorem B3072983 : Blo 2047435 3072983 := bstep (se 1 (by rfl) ⟨2304737, by rfl⟩ : syracuseStep 3072983 = 4609475) B4609475
theorem B2048655 : Blo 2047435 2048655 := bstep (se 1 (by rfl) ⟨1536491, by rfl⟩ : syracuseStep 2048655 = 3072983) B3072983
theorem B3072989 : Blo 2047435 3072989 := bbase (se 3 (by rfl) ⟨576185, by rfl⟩ : syracuseStep 3072989 = 1152371) (by norm_num)
theorem B2048659 : Blo 2047435 2048659 := bstep (se 1 (by rfl) ⟨1536494, by rfl⟩ : syracuseStep 2048659 = 3072989) B3072989
theorem B4609493 : Blo 2047435 4609493 := bbase (se 7 (by rfl) ⟨54017, by rfl⟩ : syracuseStep 4609493 = 108035) (by norm_num)
theorem B3072995 : Blo 2047435 3072995 := bstep (se 1 (by rfl) ⟨2304746, by rfl⟩ : syracuseStep 3072995 = 4609493) B4609493
theorem B2048663 : Blo 2047435 2048663 := bstep (se 1 (by rfl) ⟨1536497, by rfl⟩ : syracuseStep 2048663 = 3072995) B3072995
theorem B2336197 : Blo 2047435 2336197 := bbase (se 4 (by rfl) ⟨219018, by rfl⟩ : syracuseStep 2336197 = 438037) (by norm_num)
theorem B3114929 : Blo 2047435 3114929 := bstep (se 2 (by rfl) ⟨1168098, by rfl⟩ : syracuseStep 3114929 = 2336197) B2336197
theorem B8306477 : Blo 2047435 8306477 := bstep (se 3 (by rfl) ⟨1557464, by rfl⟩ : syracuseStep 8306477 = 3114929) B3114929
theorem B5537651 : Blo 2047435 5537651 := bstep (se 1 (by rfl) ⟨4153238, by rfl⟩ : syracuseStep 5537651 = 8306477) B8306477
theorem B14767069 : Blo 2047435 14767069 := bstep (se 3 (by rfl) ⟨2768825, by rfl⟩ : syracuseStep 14767069 = 5537651) B5537651
theorem B19689425 : Blo 2047435 19689425 := bstep (se 2 (by rfl) ⟨7383534, by rfl⟩ : syracuseStep 19689425 = 14767069) B14767069
theorem B13126283 : Blo 2047435 13126283 := bstep (se 1 (by rfl) ⟨9844712, by rfl⟩ : syracuseStep 13126283 = 19689425) B19689425
theorem B8750855 : Blo 2047435 8750855 := bstep (se 1 (by rfl) ⟨6563141, by rfl⟩ : syracuseStep 8750855 = 13126283) B13126283
theorem B5833903 : Blo 2047435 5833903 := bstep (se 1 (by rfl) ⟨4375427, by rfl⟩ : syracuseStep 5833903 = 8750855) B8750855
theorem B7778537 : Blo 2047435 7778537 := bstep (se 2 (by rfl) ⟨2916951, by rfl⟩ : syracuseStep 7778537 = 5833903) B5833903
theorem B5185691 : Blo 2047435 5185691 := bstep (se 1 (by rfl) ⟨3889268, by rfl⟩ : syracuseStep 5185691 = 7778537) B7778537
theorem B3457127 : Blo 2047435 3457127 := bstep (se 1 (by rfl) ⟨2592845, by rfl⟩ : syracuseStep 3457127 = 5185691) B5185691
theorem B2304751 : Blo 2047435 2304751 := bstep (se 1 (by rfl) ⟨1728563, by rfl⟩ : syracuseStep 2304751 = 3457127) B3457127
theorem B3073001 : Blo 2047435 3073001 := bstep (se 2 (by rfl) ⟨1152375, by rfl⟩ : syracuseStep 3073001 = 2304751) B2304751
theorem B2048667 : Blo 2047435 2048667 := bstep (se 1 (by rfl) ⟨1536500, by rfl⟩ : syracuseStep 2048667 = 3073001) B3073001
theorem B4922365 : Blo 2047435 4922365 := bbase (se 3 (by rfl) ⟨922943, by rfl⟩ : syracuseStep 4922365 = 1845887) (by norm_num)
theorem B6563153 : Blo 2047435 6563153 := bstep (se 2 (by rfl) ⟨2461182, by rfl⟩ : syracuseStep 6563153 = 4922365) B4922365
theorem B17501741 : Blo 2047435 17501741 := bstep (se 3 (by rfl) ⟨3281576, by rfl⟩ : syracuseStep 17501741 = 6563153) B6563153
theorem B11667827 : Blo 2047435 11667827 := bstep (se 1 (by rfl) ⟨8750870, by rfl⟩ : syracuseStep 11667827 = 17501741) B17501741
theorem B7778551 : Blo 2047435 7778551 := bstep (se 1 (by rfl) ⟨5833913, by rfl⟩ : syracuseStep 7778551 = 11667827) B11667827
theorem B10371401 : Blo 2047435 10371401 := bstep (se 2 (by rfl) ⟨3889275, by rfl⟩ : syracuseStep 10371401 = 7778551) B7778551
theorem B6914267 : Blo 2047435 6914267 := bstep (se 1 (by rfl) ⟨5185700, by rfl⟩ : syracuseStep 6914267 = 10371401) B10371401
theorem B4609511 : Blo 2047435 4609511 := bstep (se 1 (by rfl) ⟨3457133, by rfl⟩ : syracuseStep 4609511 = 6914267) B6914267
theorem B3073007 : Blo 2047435 3073007 := bstep (se 1 (by rfl) ⟨2304755, by rfl⟩ : syracuseStep 3073007 = 4609511) B4609511
theorem B2048671 : Blo 2047435 2048671 := bstep (se 1 (by rfl) ⟨1536503, by rfl⟩ : syracuseStep 2048671 = 3073007) B3073007
theorem B3073013 : Blo 2047435 3073013 := bbase (se 5 (by rfl) ⟨144047, by rfl⟩ : syracuseStep 3073013 = 288095) (by norm_num)
theorem B2048675 : Blo 2047435 2048675 := bstep (se 1 (by rfl) ⟨1536506, by rfl⟩ : syracuseStep 2048675 = 3073013) B3073013
theorem B4375453 : Blo 2047435 4375453 := bbase (se 3 (by rfl) ⟨820397, by rfl⟩ : syracuseStep 4375453 = 1640795) (by norm_num)
theorem B5833937 : Blo 2047435 5833937 := bstep (se 2 (by rfl) ⟨2187726, by rfl⟩ : syracuseStep 5833937 = 4375453) B4375453
theorem B3889291 : Blo 2047435 3889291 := bstep (se 1 (by rfl) ⟨2916968, by rfl⟩ : syracuseStep 3889291 = 5833937) B5833937
theorem B5185721 : Blo 2047435 5185721 := bstep (se 2 (by rfl) ⟨1944645, by rfl⟩ : syracuseStep 5185721 = 3889291) B3889291
theorem B3457147 : Blo 2047435 3457147 := bstep (se 1 (by rfl) ⟨2592860, by rfl⟩ : syracuseStep 3457147 = 5185721) B5185721
theorem B4609529 : Blo 2047435 4609529 := bstep (se 2 (by rfl) ⟨1728573, by rfl⟩ : syracuseStep 4609529 = 3457147) B3457147
theorem B3073019 : Blo 2047435 3073019 := bstep (se 1 (by rfl) ⟨2304764, by rfl⟩ : syracuseStep 3073019 = 4609529) B4609529
theorem B2048679 : Blo 2047435 2048679 := bstep (se 1 (by rfl) ⟨1536509, by rfl⟩ : syracuseStep 2048679 = 3073019) B3073019
theorem B2304769 : Blo 2047435 2304769 := bbase (se 2 (by rfl) ⟨864288, by rfl⟩ : syracuseStep 2304769 = 1728577) (by norm_num)
theorem B3073025 : Blo 2047435 3073025 := bstep (se 2 (by rfl) ⟨1152384, by rfl⟩ : syracuseStep 3073025 = 2304769) B2304769
theorem B2048683 : Blo 2047435 2048683 := bstep (se 1 (by rfl) ⟨1536512, by rfl⟩ : syracuseStep 2048683 = 3073025) B3073025
theorem B5185741 : Blo 2047435 5185741 := bbase (se 3 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 5185741 = 1944653) (by norm_num)
theorem B6914321 : Blo 2047435 6914321 := bstep (se 2 (by rfl) ⟨2592870, by rfl⟩ : syracuseStep 6914321 = 5185741) B5185741
theorem B4609547 : Blo 2047435 4609547 := bstep (se 1 (by rfl) ⟨3457160, by rfl⟩ : syracuseStep 4609547 = 6914321) B6914321
theorem B3073031 : Blo 2047435 3073031 := bstep (se 1 (by rfl) ⟨2304773, by rfl⟩ : syracuseStep 3073031 = 4609547) B4609547
theorem B2048687 : Blo 2047435 2048687 := bstep (se 1 (by rfl) ⟨1536515, by rfl⟩ : syracuseStep 2048687 = 3073031) B3073031
theorem B3073037 : Blo 2047435 3073037 := bbase (se 3 (by rfl) ⟨576194, by rfl⟩ : syracuseStep 3073037 = 1152389) (by norm_num)
theorem B2048691 : Blo 2047435 2048691 := bstep (se 1 (by rfl) ⟨1536518, by rfl⟩ : syracuseStep 2048691 = 3073037) B3073037
theorem B4609565 : Blo 2047435 4609565 := bbase (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) (by norm_num)
theorem B3073043 : Blo 2047435 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B2048695 : Blo 2047435 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B3457181 : Blo 2047435 3457181 := bbase (se 3 (by rfl) ⟨648221, by rfl⟩ : syracuseStep 3457181 = 1296443) (by norm_num)
theorem B2304787 : Blo 2047435 2304787 := bstep (se 1 (by rfl) ⟨1728590, by rfl⟩ : syracuseStep 2304787 = 3457181) B3457181
theorem B3073049 : Blo 2047435 3073049 := bstep (se 2 (by rfl) ⟨1152393, by rfl⟩ : syracuseStep 3073049 = 2304787) B2304787
theorem B2048699 : Blo 2047435 2048699 := bstep (se 1 (by rfl) ⟨1536524, by rfl⟩ : syracuseStep 2048699 = 3073049) B3073049
theorem B2133709 : Blo 2047435 2133709 := bbase (se 3 (by rfl) ⟨400070, by rfl⟩ : syracuseStep 2133709 = 800141) (by norm_num)
theorem B11379781 : Blo 2047435 11379781 := bstep (se 4 (by rfl) ⟨1066854, by rfl⟩ : syracuseStep 11379781 = 2133709) B2133709
theorem B15173041 : Blo 2047435 15173041 := bstep (se 2 (by rfl) ⟨5689890, by rfl⟩ : syracuseStep 15173041 = 11379781) B11379781
theorem B20230721 : Blo 2047435 20230721 := bstep (se 2 (by rfl) ⟨7586520, by rfl⟩ : syracuseStep 20230721 = 15173041) B15173041
theorem B13487147 : Blo 2047435 13487147 := bstep (se 1 (by rfl) ⟨10115360, by rfl⟩ : syracuseStep 13487147 = 20230721) B20230721
theorem B8991431 : Blo 2047435 8991431 := bstep (se 1 (by rfl) ⟨6743573, by rfl⟩ : syracuseStep 8991431 = 13487147) B13487147
theorem B5994287 : Blo 2047435 5994287 := bstep (se 1 (by rfl) ⟨4495715, by rfl⟩ : syracuseStep 5994287 = 8991431) B8991431
theorem B3996191 : Blo 2047435 3996191 := bstep (se 1 (by rfl) ⟨2997143, by rfl⟩ : syracuseStep 3996191 = 5994287) B5994287
theorem B2664127 : Blo 2047435 2664127 := bstep (se 1 (by rfl) ⟨1998095, by rfl⟩ : syracuseStep 2664127 = 3996191) B3996191
theorem B3552169 : Blo 2047435 3552169 := bstep (se 2 (by rfl) ⟨1332063, by rfl⟩ : syracuseStep 3552169 = 2664127) B2664127
theorem B4736225 : Blo 2047435 4736225 := bstep (se 2 (by rfl) ⟨1776084, by rfl⟩ : syracuseStep 4736225 = 3552169) B3552169
theorem B3157483 : Blo 2047435 3157483 := bstep (se 1 (by rfl) ⟨2368112, by rfl⟩ : syracuseStep 3157483 = 4736225) B4736225
theorem B4209977 : Blo 2047435 4209977 := bstep (se 2 (by rfl) ⟨1578741, by rfl⟩ : syracuseStep 4209977 = 3157483) B3157483
theorem B2806651 : Blo 2047435 2806651 := bstep (se 1 (by rfl) ⟨2104988, by rfl⟩ : syracuseStep 2806651 = 4209977) B4209977
theorem B3742201 : Blo 2047435 3742201 := bstep (se 2 (by rfl) ⟨1403325, by rfl⟩ : syracuseStep 3742201 = 2806651) B2806651
theorem B4989601 : Blo 2047435 4989601 := bstep (se 2 (by rfl) ⟨1871100, by rfl⟩ : syracuseStep 4989601 = 3742201) B3742201
theorem B6652801 : Blo 2047435 6652801 := bstep (se 2 (by rfl) ⟨2494800, by rfl⟩ : syracuseStep 6652801 = 4989601) B4989601
theorem B8870401 : Blo 2047435 8870401 := bstep (se 2 (by rfl) ⟨3326400, by rfl⟩ : syracuseStep 8870401 = 6652801) B6652801
theorem B47308805 : Blo 2047435 47308805 := bstep (se 4 (by rfl) ⟨4435200, by rfl⟩ : syracuseStep 47308805 = 8870401) B8870401
theorem B31539203 : Blo 2047435 31539203 := bstep (se 1 (by rfl) ⟨23654402, by rfl⟩ : syracuseStep 31539203 = 47308805) B47308805
theorem B21026135 : Blo 2047435 21026135 := bstep (se 1 (by rfl) ⟨15769601, by rfl⟩ : syracuseStep 21026135 = 31539203) B31539203
theorem B14017423 : Blo 2047435 14017423 := bstep (se 1 (by rfl) ⟨10513067, by rfl⟩ : syracuseStep 14017423 = 21026135) B21026135
theorem B18689897 : Blo 2047435 18689897 := bstep (se 2 (by rfl) ⟨7008711, by rfl⟩ : syracuseStep 18689897 = 14017423) B14017423
theorem B49839725 : Blo 2047435 49839725 := bstep (se 3 (by rfl) ⟨9344948, by rfl⟩ : syracuseStep 49839725 = 18689897) B18689897
theorem B33226483 : Blo 2047435 33226483 := bstep (se 1 (by rfl) ⟨24919862, by rfl⟩ : syracuseStep 33226483 = 49839725) B49839725
theorem B44301977 : Blo 2047435 44301977 := bstep (se 2 (by rfl) ⟨16613241, by rfl⟩ : syracuseStep 44301977 = 33226483) B33226483
theorem B29534651 : Blo 2047435 29534651 := bstep (se 1 (by rfl) ⟨22150988, by rfl⟩ : syracuseStep 29534651 = 44301977) B44301977
theorem B19689767 : Blo 2047435 19689767 := bstep (se 1 (by rfl) ⟨14767325, by rfl⟩ : syracuseStep 19689767 = 29534651) B29534651
theorem B13126511 : Blo 2047435 13126511 := bstep (se 1 (by rfl) ⟨9844883, by rfl⟩ : syracuseStep 13126511 = 19689767) B19689767
theorem B8751007 : Blo 2047435 8751007 := bstep (se 1 (by rfl) ⟨6563255, by rfl⟩ : syracuseStep 8751007 = 13126511) B13126511
theorem B11668009 : Blo 2047435 11668009 := bstep (se 2 (by rfl) ⟨4375503, by rfl⟩ : syracuseStep 11668009 = 8751007) B8751007
theorem B15557345 : Blo 2047435 15557345 := bstep (se 2 (by rfl) ⟨5834004, by rfl⟩ : syracuseStep 15557345 = 11668009) B11668009
theorem B10371563 : Blo 2047435 10371563 := bstep (se 1 (by rfl) ⟨7778672, by rfl⟩ : syracuseStep 10371563 = 15557345) B15557345
theorem B6914375 : Blo 2047435 6914375 := bstep (se 1 (by rfl) ⟨5185781, by rfl⟩ : syracuseStep 6914375 = 10371563) B10371563
theorem B4609583 : Blo 2047435 4609583 := bstep (se 1 (by rfl) ⟨3457187, by rfl⟩ : syracuseStep 4609583 = 6914375) B6914375
theorem B3073055 : Blo 2047435 3073055 := bstep (se 1 (by rfl) ⟨2304791, by rfl⟩ : syracuseStep 3073055 = 4609583) B4609583
theorem B2048703 : Blo 2047435 2048703 := bstep (se 1 (by rfl) ⟨1536527, by rfl⟩ : syracuseStep 2048703 = 3073055) B3073055
theorem B3073061 : Blo 2047435 3073061 := bbase (se 4 (by rfl) ⟨288099, by rfl⟩ : syracuseStep 3073061 = 576199) (by norm_num)
theorem B2048707 : Blo 2047435 2048707 := bstep (se 1 (by rfl) ⟨1536530, by rfl⟩ : syracuseStep 2048707 = 3073061) B3073061
theorem B2592901 : Blo 2047435 2592901 := bbase (se 4 (by rfl) ⟨243084, by rfl⟩ : syracuseStep 2592901 = 486169) (by norm_num)
theorem B3457201 : Blo 2047435 3457201 := bstep (se 2 (by rfl) ⟨1296450, by rfl⟩ : syracuseStep 3457201 = 2592901) B2592901
theorem B4609601 : Blo 2047435 4609601 := bstep (se 2 (by rfl) ⟨1728600, by rfl⟩ : syracuseStep 4609601 = 3457201) B3457201
theorem B3073067 : Blo 2047435 3073067 := bstep (se 1 (by rfl) ⟨2304800, by rfl⟩ : syracuseStep 3073067 = 4609601) B4609601
theorem B2048711 : Blo 2047435 2048711 := bstep (se 1 (by rfl) ⟨1536533, by rfl⟩ : syracuseStep 2048711 = 3073067) B3073067
theorem B2304805 : Blo 2047435 2304805 := bbase (se 4 (by rfl) ⟨216075, by rfl⟩ : syracuseStep 2304805 = 432151) (by norm_num)
theorem B3073073 : Blo 2047435 3073073 := bstep (se 2 (by rfl) ⟨1152402, by rfl⟩ : syracuseStep 3073073 = 2304805) B2304805
theorem B2048715 : Blo 2047435 2048715 := bstep (se 1 (by rfl) ⟨1536536, by rfl⟩ : syracuseStep 2048715 = 3073073) B3073073
theorem B8751077 : Blo 2047435 8751077 := bbase (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) (by norm_num)
theorem B5834051 : Blo 2047435 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B3889367 : Blo 2047435 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B2592911 : Blo 2047435 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B6914429 : Blo 2047435 6914429 := bstep (se 3 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 6914429 = 2592911) B2592911
theorem B4609619 : Blo 2047435 4609619 := bstep (se 1 (by rfl) ⟨3457214, by rfl⟩ : syracuseStep 4609619 = 6914429) B6914429
theorem B3073079 : Blo 2047435 3073079 := bstep (se 1 (by rfl) ⟨2304809, by rfl⟩ : syracuseStep 3073079 = 4609619) B4609619
theorem B2048719 : Blo 2047435 2048719 := bstep (se 1 (by rfl) ⟨1536539, by rfl⟩ : syracuseStep 2048719 = 3073079) B3073079
theorem B3073085 : Blo 2047435 3073085 := bbase (se 3 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 3073085 = 1152407) (by norm_num)
theorem B2048723 : Blo 2047435 2048723 := bstep (se 1 (by rfl) ⟨1536542, by rfl⟩ : syracuseStep 2048723 = 3073085) B3073085
theorem B4609637 : Blo 2047435 4609637 := bbase (se 4 (by rfl) ⟨432153, by rfl⟩ : syracuseStep 4609637 = 864307) (by norm_num)
theorem B3073091 : Blo 2047435 3073091 := bstep (se 1 (by rfl) ⟨2304818, by rfl⟩ : syracuseStep 3073091 = 4609637) B4609637
theorem B2048727 : Blo 2047435 2048727 := bstep (se 1 (by rfl) ⟨1536545, by rfl⟩ : syracuseStep 2048727 = 3073091) B3073091
theorem B5185853 : Blo 2047435 5185853 := bbase (se 3 (by rfl) ⟨972347, by rfl⟩ : syracuseStep 5185853 = 1944695) (by norm_num)
theorem B3457235 : Blo 2047435 3457235 := bstep (se 1 (by rfl) ⟨2592926, by rfl⟩ : syracuseStep 3457235 = 5185853) B5185853
theorem B2304823 : Blo 2047435 2304823 := bstep (se 1 (by rfl) ⟨1728617, by rfl⟩ : syracuseStep 2304823 = 3457235) B3457235
theorem B3073097 : Blo 2047435 3073097 := bstep (se 2 (by rfl) ⟨1152411, by rfl⟩ : syracuseStep 3073097 = 2304823) B2304823
theorem B2048731 : Blo 2047435 2048731 := bstep (se 1 (by rfl) ⟨1536548, by rfl⟩ : syracuseStep 2048731 = 3073097) B3073097
theorem B3889397 : Blo 2047435 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B10371725 : Blo 2047435 10371725 := bstep (se 3 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 10371725 = 3889397) B3889397
theorem B6914483 : Blo 2047435 6914483 := bstep (se 1 (by rfl) ⟨5185862, by rfl⟩ : syracuseStep 6914483 = 10371725) B10371725
theorem B4609655 : Blo 2047435 4609655 := bstep (se 1 (by rfl) ⟨3457241, by rfl⟩ : syracuseStep 4609655 = 6914483) B6914483
theorem B3073103 : Blo 2047435 3073103 := bstep (se 1 (by rfl) ⟨2304827, by rfl⟩ : syracuseStep 3073103 = 4609655) B4609655
theorem B2048735 : Blo 2047435 2048735 := bstep (se 1 (by rfl) ⟨1536551, by rfl⟩ : syracuseStep 2048735 = 3073103) B3073103
theorem B3073109 : Blo 2047435 3073109 := bbase (se 8 (by rfl) ⟨18006, by rfl⟩ : syracuseStep 3073109 = 36013) (by norm_num)
theorem B2048739 : Blo 2047435 2048739 := bstep (se 1 (by rfl) ⟨1536554, by rfl⟩ : syracuseStep 2048739 = 3073109) B3073109
theorem B9845077 : Blo 2047435 9845077 := bbase (se 10 (by rfl) ⟨14421, by rfl⟩ : syracuseStep 9845077 = 28843) (by norm_num)
theorem B13126769 : Blo 2047435 13126769 := bstep (se 2 (by rfl) ⟨4922538, by rfl⟩ : syracuseStep 13126769 = 9845077) B9845077
theorem B8751179 : Blo 2047435 8751179 := bstep (se 1 (by rfl) ⟨6563384, by rfl⟩ : syracuseStep 8751179 = 13126769) B13126769
theorem B5834119 : Blo 2047435 5834119 := bstep (se 1 (by rfl) ⟨4375589, by rfl⟩ : syracuseStep 5834119 = 8751179) B8751179
theorem B7778825 : Blo 2047435 7778825 := bstep (se 2 (by rfl) ⟨2917059, by rfl⟩ : syracuseStep 7778825 = 5834119) B5834119
theorem B5185883 : Blo 2047435 5185883 := bstep (se 1 (by rfl) ⟨3889412, by rfl⟩ : syracuseStep 5185883 = 7778825) B7778825
theorem B3457255 : Blo 2047435 3457255 := bstep (se 1 (by rfl) ⟨2592941, by rfl⟩ : syracuseStep 3457255 = 5185883) B5185883
theorem B4609673 : Blo 2047435 4609673 := bstep (se 2 (by rfl) ⟨1728627, by rfl⟩ : syracuseStep 4609673 = 3457255) B3457255
theorem B3073115 : Blo 2047435 3073115 := bstep (se 1 (by rfl) ⟨2304836, by rfl⟩ : syracuseStep 3073115 = 4609673) B4609673
theorem B2048743 : Blo 2047435 2048743 := bstep (se 1 (by rfl) ⟨1536557, by rfl⟩ : syracuseStep 2048743 = 3073115) B3073115
theorem B2304841 : Blo 2047435 2304841 := bbase (se 2 (by rfl) ⟨864315, by rfl⟩ : syracuseStep 2304841 = 1728631) (by norm_num)
theorem B3073121 : Blo 2047435 3073121 := bstep (se 2 (by rfl) ⟨1152420, by rfl⟩ : syracuseStep 3073121 = 2304841) B2304841
theorem B2048747 : Blo 2047435 2048747 := bstep (se 1 (by rfl) ⟨1536560, by rfl⟩ : syracuseStep 2048747 = 3073121) B3073121
theorem B19690229 : Blo 2047435 19690229 := bbase (se 5 (by rfl) ⟨922979, by rfl⟩ : syracuseStep 19690229 = 1845959) (by norm_num)
theorem B13126819 : Blo 2047435 13126819 := bstep (se 1 (by rfl) ⟨9845114, by rfl⟩ : syracuseStep 13126819 = 19690229) B19690229
theorem B17502425 : Blo 2047435 17502425 := bstep (se 2 (by rfl) ⟨6563409, by rfl⟩ : syracuseStep 17502425 = 13126819) B13126819
theorem B11668283 : Blo 2047435 11668283 := bstep (se 1 (by rfl) ⟨8751212, by rfl⟩ : syracuseStep 11668283 = 17502425) B17502425
theorem B7778855 : Blo 2047435 7778855 := bstep (se 1 (by rfl) ⟨5834141, by rfl⟩ : syracuseStep 7778855 = 11668283) B11668283
theorem B5185903 : Blo 2047435 5185903 := bstep (se 1 (by rfl) ⟨3889427, by rfl⟩ : syracuseStep 5185903 = 7778855) B7778855
theorem B6914537 : Blo 2047435 6914537 := bstep (se 2 (by rfl) ⟨2592951, by rfl⟩ : syracuseStep 6914537 = 5185903) B5185903
theorem B4609691 : Blo 2047435 4609691 := bstep (se 1 (by rfl) ⟨3457268, by rfl⟩ : syracuseStep 4609691 = 6914537) B6914537
theorem B3073127 : Blo 2047435 3073127 := bstep (se 1 (by rfl) ⟨2304845, by rfl⟩ : syracuseStep 3073127 = 4609691) B4609691
theorem B2048751 : Blo 2047435 2048751 := bstep (se 1 (by rfl) ⟨1536563, by rfl⟩ : syracuseStep 2048751 = 3073127) B3073127
theorem B3073133 : Blo 2047435 3073133 := bbase (se 3 (by rfl) ⟨576212, by rfl⟩ : syracuseStep 3073133 = 1152425) (by norm_num)
theorem B2048755 : Blo 2047435 2048755 := bstep (se 1 (by rfl) ⟨1536566, by rfl⟩ : syracuseStep 2048755 = 3073133) B3073133
theorem B4609709 : Blo 2047435 4609709 := bbase (se 3 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 4609709 = 1728641) (by norm_num)
theorem B3073139 : Blo 2047435 3073139 := bstep (se 1 (by rfl) ⟨2304854, by rfl⟩ : syracuseStep 3073139 = 4609709) B4609709
theorem B2048759 : Blo 2047435 2048759 := bstep (se 1 (by rfl) ⟨1536569, by rfl⟩ : syracuseStep 2048759 = 3073139) B3073139
theorem B3281725 : Blo 2047435 3281725 := bbase (se 3 (by rfl) ⟨615323, by rfl⟩ : syracuseStep 3281725 = 1230647) (by norm_num)
theorem B4375633 : Blo 2047435 4375633 := bstep (se 2 (by rfl) ⟨1640862, by rfl⟩ : syracuseStep 4375633 = 3281725) B3281725
theorem B5834177 : Blo 2047435 5834177 := bstep (se 2 (by rfl) ⟨2187816, by rfl⟩ : syracuseStep 5834177 = 4375633) B4375633
theorem B3889451 : Blo 2047435 3889451 := bstep (se 1 (by rfl) ⟨2917088, by rfl⟩ : syracuseStep 3889451 = 5834177) B5834177
theorem B2592967 : Blo 2047435 2592967 := bstep (se 1 (by rfl) ⟨1944725, by rfl⟩ : syracuseStep 2592967 = 3889451) B3889451
theorem B3457289 : Blo 2047435 3457289 := bstep (se 2 (by rfl) ⟨1296483, by rfl⟩ : syracuseStep 3457289 = 2592967) B2592967
theorem B2304859 : Blo 2047435 2304859 := bstep (se 1 (by rfl) ⟨1728644, by rfl⟩ : syracuseStep 2304859 = 3457289) B3457289
theorem B3073145 : Blo 2047435 3073145 := bstep (se 2 (by rfl) ⟨1152429, by rfl⟩ : syracuseStep 3073145 = 2304859) B2304859
theorem B2048763 : Blo 2047435 2048763 := bstep (se 1 (by rfl) ⟨1536572, by rfl⟩ : syracuseStep 2048763 = 3073145) B3073145
theorem B7383893 : Blo 2047435 7383893 := bbase (se 9 (by rfl) ⟨21632, by rfl⟩ : syracuseStep 7383893 = 43265) (by norm_num)
theorem B19690381 : Blo 2047435 19690381 := bstep (se 3 (by rfl) ⟨3691946, by rfl⟩ : syracuseStep 19690381 = 7383893) B7383893
theorem B26253841 : Blo 2047435 26253841 := bstep (se 2 (by rfl) ⟨9845190, by rfl⟩ : syracuseStep 26253841 = 19690381) B19690381
theorem B35005121 : Blo 2047435 35005121 := bstep (se 2 (by rfl) ⟨13126920, by rfl⟩ : syracuseStep 35005121 = 26253841) B26253841
theorem B23336747 : Blo 2047435 23336747 := bstep (se 1 (by rfl) ⟨17502560, by rfl⟩ : syracuseStep 23336747 = 35005121) B35005121
theorem B15557831 : Blo 2047435 15557831 := bstep (se 1 (by rfl) ⟨11668373, by rfl⟩ : syracuseStep 15557831 = 23336747) B23336747
theorem B10371887 : Blo 2047435 10371887 := bstep (se 1 (by rfl) ⟨7778915, by rfl⟩ : syracuseStep 10371887 = 15557831) B15557831
theorem B6914591 : Blo 2047435 6914591 := bstep (se 1 (by rfl) ⟨5185943, by rfl⟩ : syracuseStep 6914591 = 10371887) B10371887
theorem B4609727 : Blo 2047435 4609727 := bstep (se 1 (by rfl) ⟨3457295, by rfl⟩ : syracuseStep 4609727 = 6914591) B6914591
theorem B3073151 : Blo 2047435 3073151 := bstep (se 1 (by rfl) ⟨2304863, by rfl⟩ : syracuseStep 3073151 = 4609727) B4609727
theorem B2048767 : Blo 2047435 2048767 := bstep (se 1 (by rfl) ⟨1536575, by rfl⟩ : syracuseStep 2048767 = 3073151) B3073151
theorem B3073157 : Blo 2047435 3073157 := bbase (se 4 (by rfl) ⟨288108, by rfl⟩ : syracuseStep 3073157 = 576217) (by norm_num)
theorem B2048771 : Blo 2047435 2048771 := bstep (se 1 (by rfl) ⟨1536578, by rfl⟩ : syracuseStep 2048771 = 3073157) B3073157
theorem B3457309 : Blo 2047435 3457309 := bbase (se 3 (by rfl) ⟨648245, by rfl⟩ : syracuseStep 3457309 = 1296491) (by norm_num)
theorem B4609745 : Blo 2047435 4609745 := bstep (se 2 (by rfl) ⟨1728654, by rfl⟩ : syracuseStep 4609745 = 3457309) B3457309
theorem B3073163 : Blo 2047435 3073163 := bstep (se 1 (by rfl) ⟨2304872, by rfl⟩ : syracuseStep 3073163 = 4609745) B4609745
theorem B2048775 : Blo 2047435 2048775 := bstep (se 1 (by rfl) ⟨1536581, by rfl⟩ : syracuseStep 2048775 = 3073163) B3073163
theorem B2304877 : Blo 2047435 2304877 := bbase (se 3 (by rfl) ⟨432164, by rfl⟩ : syracuseStep 2304877 = 864329) (by norm_num)
theorem B3073169 : Blo 2047435 3073169 := bstep (se 2 (by rfl) ⟨1152438, by rfl⟩ : syracuseStep 3073169 = 2304877) B2304877
theorem B2048779 : Blo 2047435 2048779 := bstep (se 1 (by rfl) ⟨1536584, by rfl⟩ : syracuseStep 2048779 = 3073169) B3073169
theorem B6914645 : Blo 2047435 6914645 := bbase (se 8 (by rfl) ⟨40515, by rfl⟩ : syracuseStep 6914645 = 81031) (by norm_num)
theorem B4609763 : Blo 2047435 4609763 := bstep (se 1 (by rfl) ⟨3457322, by rfl⟩ : syracuseStep 4609763 = 6914645) B6914645
theorem B3073175 : Blo 2047435 3073175 := bstep (se 1 (by rfl) ⟨2304881, by rfl⟩ : syracuseStep 3073175 = 4609763) B4609763
theorem B2048783 : Blo 2047435 2048783 := bstep (se 1 (by rfl) ⟨1536587, by rfl⟩ : syracuseStep 2048783 = 3073175) B3073175
theorem B3073181 : Blo 2047435 3073181 := bbase (se 3 (by rfl) ⟨576221, by rfl⟩ : syracuseStep 3073181 = 1152443) (by norm_num)
theorem B2048787 : Blo 2047435 2048787 := bstep (se 1 (by rfl) ⟨1536590, by rfl⟩ : syracuseStep 2048787 = 3073181) B3073181
theorem B4609781 : Blo 2047435 4609781 := bbase (se 5 (by rfl) ⟨216083, by rfl⟩ : syracuseStep 4609781 = 432167) (by norm_num)
theorem B3073187 : Blo 2047435 3073187 := bstep (se 1 (by rfl) ⟨2304890, by rfl⟩ : syracuseStep 3073187 = 4609781) B4609781
theorem B2048791 : Blo 2047435 2048791 := bstep (se 1 (by rfl) ⟨1536593, by rfl⟩ : syracuseStep 2048791 = 3073187) B3073187
theorem B4672685 : Blo 2047435 4672685 := bbase (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) (by norm_num)
theorem B12460493 : Blo 2047435 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B33227981 : Blo 2047435 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B22151987 : Blo 2047435 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B14767991 : Blo 2047435 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B9845327 : Blo 2047435 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B26254205 : Blo 2047435 26254205 := bstep (se 3 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 26254205 = 9845327) B9845327
theorem B17502803 : Blo 2047435 17502803 := bstep (se 1 (by rfl) ⟨13127102, by rfl⟩ : syracuseStep 17502803 = 26254205) B26254205
theorem B11668535 : Blo 2047435 11668535 := bstep (se 1 (by rfl) ⟨8751401, by rfl⟩ : syracuseStep 11668535 = 17502803) B17502803
theorem B7779023 : Blo 2047435 7779023 := bstep (se 1 (by rfl) ⟨5834267, by rfl⟩ : syracuseStep 7779023 = 11668535) B11668535
theorem B5186015 : Blo 2047435 5186015 := bstep (se 1 (by rfl) ⟨3889511, by rfl⟩ : syracuseStep 5186015 = 7779023) B7779023
theorem B3457343 : Blo 2047435 3457343 := bstep (se 1 (by rfl) ⟨2593007, by rfl⟩ : syracuseStep 3457343 = 5186015) B5186015
theorem B2304895 : Blo 2047435 2304895 := bstep (se 1 (by rfl) ⟨1728671, by rfl⟩ : syracuseStep 2304895 = 3457343) B3457343
theorem B3073193 : Blo 2047435 3073193 := bstep (se 2 (by rfl) ⟨1152447, by rfl⟩ : syracuseStep 3073193 = 2304895) B2304895
theorem B2048795 : Blo 2047435 2048795 := bstep (se 1 (by rfl) ⟨1536596, by rfl⟩ : syracuseStep 2048795 = 3073193) B3073193
theorem B4375709 : Blo 2047435 4375709 := bbase (se 3 (by rfl) ⟨820445, by rfl⟩ : syracuseStep 4375709 = 1640891) (by norm_num)
theorem B2917139 : Blo 2047435 2917139 := bstep (se 1 (by rfl) ⟨2187854, by rfl⟩ : syracuseStep 2917139 = 4375709) B4375709
theorem B7779037 : Blo 2047435 7779037 := bstep (se 3 (by rfl) ⟨1458569, by rfl⟩ : syracuseStep 7779037 = 2917139) B2917139
theorem B10372049 : Blo 2047435 10372049 := bstep (se 2 (by rfl) ⟨3889518, by rfl⟩ : syracuseStep 10372049 = 7779037) B7779037
theorem B6914699 : Blo 2047435 6914699 := bstep (se 1 (by rfl) ⟨5186024, by rfl⟩ : syracuseStep 6914699 = 10372049) B10372049
theorem B4609799 : Blo 2047435 4609799 := bstep (se 1 (by rfl) ⟨3457349, by rfl⟩ : syracuseStep 4609799 = 6914699) B6914699
theorem B3073199 : Blo 2047435 3073199 := bstep (se 1 (by rfl) ⟨2304899, by rfl⟩ : syracuseStep 3073199 = 4609799) B4609799
theorem B2048799 : Blo 2047435 2048799 := bstep (se 1 (by rfl) ⟨1536599, by rfl⟩ : syracuseStep 2048799 = 3073199) B3073199
theorem B3073205 : Blo 2047435 3073205 := bbase (se 5 (by rfl) ⟨144056, by rfl⟩ : syracuseStep 3073205 = 288113) (by norm_num)
theorem B2048803 : Blo 2047435 2048803 := bstep (se 1 (by rfl) ⟨1536602, by rfl⟩ : syracuseStep 2048803 = 3073205) B3073205
theorem B5186045 : Blo 2047435 5186045 := bbase (se 3 (by rfl) ⟨972383, by rfl⟩ : syracuseStep 5186045 = 1944767) (by norm_num)
theorem B3457363 : Blo 2047435 3457363 := bstep (se 1 (by rfl) ⟨2593022, by rfl⟩ : syracuseStep 3457363 = 5186045) B5186045
theorem B4609817 : Blo 2047435 4609817 := bstep (se 2 (by rfl) ⟨1728681, by rfl⟩ : syracuseStep 4609817 = 3457363) B3457363
theorem B3073211 : Blo 2047435 3073211 := bstep (se 1 (by rfl) ⟨2304908, by rfl⟩ : syracuseStep 3073211 = 4609817) B4609817
theorem B2048807 : Blo 2047435 2048807 := bstep (se 1 (by rfl) ⟨1536605, by rfl⟩ : syracuseStep 2048807 = 3073211) B3073211
theorem B2304913 : Blo 2047435 2304913 := bbase (se 2 (by rfl) ⟨864342, by rfl⟩ : syracuseStep 2304913 = 1728685) (by norm_num)
theorem B3073217 : Blo 2047435 3073217 := bstep (se 2 (by rfl) ⟨1152456, by rfl⟩ : syracuseStep 3073217 = 2304913) B2304913
theorem B2048811 : Blo 2047435 2048811 := bstep (se 1 (by rfl) ⟨1536608, by rfl⟩ : syracuseStep 2048811 = 3073217) B3073217
theorem B3889549 : Blo 2047435 3889549 := bbase (se 3 (by rfl) ⟨729290, by rfl⟩ : syracuseStep 3889549 = 1458581) (by norm_num)
theorem B5186065 : Blo 2047435 5186065 := bstep (se 2 (by rfl) ⟨1944774, by rfl⟩ : syracuseStep 5186065 = 3889549) B3889549
theorem B6914753 : Blo 2047435 6914753 := bstep (se 2 (by rfl) ⟨2593032, by rfl⟩ : syracuseStep 6914753 = 5186065) B5186065
theorem B4609835 : Blo 2047435 4609835 := bstep (se 1 (by rfl) ⟨3457376, by rfl⟩ : syracuseStep 4609835 = 6914753) B6914753
theorem B3073223 : Blo 2047435 3073223 := bstep (se 1 (by rfl) ⟨2304917, by rfl⟩ : syracuseStep 3073223 = 4609835) B4609835
theorem B2048815 : Blo 2047435 2048815 := bstep (se 1 (by rfl) ⟨1536611, by rfl⟩ : syracuseStep 2048815 = 3073223) B3073223
theorem B3073229 : Blo 2047435 3073229 := bbase (se 3 (by rfl) ⟨576230, by rfl⟩ : syracuseStep 3073229 = 1152461) (by norm_num)
theorem B2048819 : Blo 2047435 2048819 := bstep (se 1 (by rfl) ⟨1536614, by rfl⟩ : syracuseStep 2048819 = 3073229) B3073229
theorem B4609853 : Blo 2047435 4609853 := bbase (se 3 (by rfl) ⟨864347, by rfl⟩ : syracuseStep 4609853 = 1728695) (by norm_num)
theorem B3073235 : Blo 2047435 3073235 := bstep (se 1 (by rfl) ⟨2304926, by rfl⟩ : syracuseStep 3073235 = 4609853) B4609853
theorem B2048823 : Blo 2047435 2048823 := bstep (se 1 (by rfl) ⟨1536617, by rfl⟩ : syracuseStep 2048823 = 3073235) B3073235
theorem B3457397 : Blo 2047435 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B2304931 : Blo 2047435 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B3073241 : Blo 2047435 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B2048827 : Blo 2047435 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B5913973 : Blo 2047435 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B7885297 : Blo 2047435 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B10513729 : Blo 2047435 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B14018305 : Blo 2047435 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B18691073 : Blo 2047435 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B12460715 : Blo 2047435 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B8307143 : Blo 2047435 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B5538095 : Blo 2047435 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B3692063 : Blo 2047435 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B2461375 : Blo 2047435 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B3281833 : Blo 2047435 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B4375777 : Blo 2047435 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B5834369 : Blo 2047435 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B15558317 : Blo 2047435 15558317 := bstep (se 3 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 15558317 = 5834369) B5834369
theorem B10372211 : Blo 2047435 10372211 := bstep (se 1 (by rfl) ⟨7779158, by rfl⟩ : syracuseStep 10372211 = 15558317) B15558317
theorem B6914807 : Blo 2047435 6914807 := bstep (se 1 (by rfl) ⟨5186105, by rfl⟩ : syracuseStep 6914807 = 10372211) B10372211
theorem B4609871 : Blo 2047435 4609871 := bstep (se 1 (by rfl) ⟨3457403, by rfl⟩ : syracuseStep 4609871 = 6914807) B6914807
theorem B3073247 : Blo 2047435 3073247 := bstep (se 1 (by rfl) ⟨2304935, by rfl⟩ : syracuseStep 3073247 = 4609871) B4609871
theorem B2048831 : Blo 2047435 2048831 := bstep (se 1 (by rfl) ⟨1536623, by rfl⟩ : syracuseStep 2048831 = 3073247) B3073247
theorem B3073253 : Blo 2047435 3073253 := bbase (se 4 (by rfl) ⟨288117, by rfl⟩ : syracuseStep 3073253 = 576235) (by norm_num)
theorem B2048835 : Blo 2047435 2048835 := bstep (se 1 (by rfl) ⟨1536626, by rfl⟩ : syracuseStep 2048835 = 3073253) B3073253
theorem B2461385 : Blo 2047435 2461385 := bbase (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) (by norm_num)
theorem B6563693 : Blo 2047435 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B4375795 : Blo 2047435 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B5834393 : Blo 2047435 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B3889595 : Blo 2047435 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B2593063 : Blo 2047435 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B3457417 : Blo 2047435 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B4609889 : Blo 2047435 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B3073259 : Blo 2047435 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B2048839 : Blo 2047435 2048839 := bstep (se 1 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 2048839 = 3073259) B3073259
theorem B2304949 : Blo 2047435 2304949 := bbase (se 5 (by rfl) ⟨108044, by rfl⟩ : syracuseStep 2304949 = 216089) (by norm_num)
theorem B3073265 : Blo 2047435 3073265 := bstep (se 2 (by rfl) ⟨1152474, by rfl⟩ : syracuseStep 3073265 = 2304949) B2304949
theorem B2048843 : Blo 2047435 2048843 := bstep (se 1 (by rfl) ⟨1536632, by rfl⟩ : syracuseStep 2048843 = 3073265) B3073265
theorem B2593073 : Blo 2047435 2593073 := bbase (se 2 (by rfl) ⟨972402, by rfl⟩ : syracuseStep 2593073 = 1944805) (by norm_num)
theorem B6914861 : Blo 2047435 6914861 := bstep (se 3 (by rfl) ⟨1296536, by rfl⟩ : syracuseStep 6914861 = 2593073) B2593073
theorem B4609907 : Blo 2047435 4609907 := bstep (se 1 (by rfl) ⟨3457430, by rfl⟩ : syracuseStep 4609907 = 6914861) B6914861
theorem B3073271 : Blo 2047435 3073271 := bstep (se 1 (by rfl) ⟨2304953, by rfl⟩ : syracuseStep 3073271 = 4609907) B4609907
theorem B2048847 : Blo 2047435 2048847 := bstep (se 1 (by rfl) ⟨1536635, by rfl⟩ : syracuseStep 2048847 = 3073271) B3073271
theorem B3073277 : Blo 2047435 3073277 := bbase (se 3 (by rfl) ⟨576239, by rfl⟩ : syracuseStep 3073277 = 1152479) (by norm_num)
theorem B2048851 : Blo 2047435 2048851 := bstep (se 1 (by rfl) ⟨1536638, by rfl⟩ : syracuseStep 2048851 = 3073277) B3073277
theorem B4609925 : Blo 2047435 4609925 := bbase (se 4 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 4609925 = 864361) (by norm_num)
theorem B3073283 : Blo 2047435 3073283 := bstep (se 1 (by rfl) ⟨2304962, by rfl⟩ : syracuseStep 3073283 = 4609925) B4609925
theorem B2048855 : Blo 2047435 2048855 := bstep (se 1 (by rfl) ⟨1536641, by rfl⟩ : syracuseStep 2048855 = 3073283) B3073283
theorem B7384229 : Blo 2047435 7384229 := bbase (se 4 (by rfl) ⟨692271, by rfl⟩ : syracuseStep 7384229 = 1384543) (by norm_num)
theorem B4922819 : Blo 2047435 4922819 := bstep (se 1 (by rfl) ⟨3692114, by rfl⟩ : syracuseStep 4922819 = 7384229) B7384229
theorem B3281879 : Blo 2047435 3281879 := bstep (se 1 (by rfl) ⟨2461409, by rfl⟩ : syracuseStep 3281879 = 4922819) B4922819
theorem B2187919 : Blo 2047435 2187919 := bstep (se 1 (by rfl) ⟨1640939, by rfl⟩ : syracuseStep 2187919 = 3281879) B3281879
theorem B2917225 : Blo 2047435 2917225 := bstep (se 2 (by rfl) ⟨1093959, by rfl⟩ : syracuseStep 2917225 = 2187919) B2187919
theorem B3889633 : Blo 2047435 3889633 := bstep (se 2 (by rfl) ⟨1458612, by rfl⟩ : syracuseStep 3889633 = 2917225) B2917225
theorem B5186177 : Blo 2047435 5186177 := bstep (se 2 (by rfl) ⟨1944816, by rfl⟩ : syracuseStep 5186177 = 3889633) B3889633
theorem B3457451 : Blo 2047435 3457451 := bstep (se 1 (by rfl) ⟨2593088, by rfl⟩ : syracuseStep 3457451 = 5186177) B5186177
theorem B2304967 : Blo 2047435 2304967 := bstep (se 1 (by rfl) ⟨1728725, by rfl⟩ : syracuseStep 2304967 = 3457451) B3457451
theorem B3073289 : Blo 2047435 3073289 := bstep (se 2 (by rfl) ⟨1152483, by rfl⟩ : syracuseStep 3073289 = 2304967) B2304967
theorem B2048859 : Blo 2047435 2048859 := bstep (se 1 (by rfl) ⟨1536644, by rfl⟩ : syracuseStep 2048859 = 3073289) B3073289
theorem B10372373 : Blo 2047435 10372373 := bbase (se 6 (by rfl) ⟨243102, by rfl⟩ : syracuseStep 10372373 = 486205) (by norm_num)
theorem B6914915 : Blo 2047435 6914915 := bstep (se 1 (by rfl) ⟨5186186, by rfl⟩ : syracuseStep 6914915 = 10372373) B10372373
theorem B4609943 : Blo 2047435 4609943 := bstep (se 1 (by rfl) ⟨3457457, by rfl⟩ : syracuseStep 4609943 = 6914915) B6914915
theorem B3073295 : Blo 2047435 3073295 := bstep (se 1 (by rfl) ⟨2304971, by rfl⟩ : syracuseStep 3073295 = 4609943) B4609943
theorem B2048863 : Blo 2047435 2048863 := bstep (se 1 (by rfl) ⟨1536647, by rfl⟩ : syracuseStep 2048863 = 3073295) B3073295
theorem B3073301 : Blo 2047435 3073301 := bbase (se 6 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 3073301 = 144061) (by norm_num)
theorem B2048867 : Blo 2047435 2048867 := bstep (se 1 (by rfl) ⟨1536650, by rfl⟩ : syracuseStep 2048867 = 3073301) B3073301
theorem B2336429 : Blo 2047435 2336429 := bbase (se 3 (by rfl) ⟨438080, by rfl⟩ : syracuseStep 2336429 = 876161) (by norm_num)
theorem B6230477 : Blo 2047435 6230477 := bstep (se 3 (by rfl) ⟨1168214, by rfl⟩ : syracuseStep 6230477 = 2336429) B2336429
theorem B16614605 : Blo 2047435 16614605 := bstep (se 3 (by rfl) ⟨3115238, by rfl⟩ : syracuseStep 16614605 = 6230477) B6230477
theorem B44305613 : Blo 2047435 44305613 := bstep (se 3 (by rfl) ⟨8307302, by rfl⟩ : syracuseStep 44305613 = 16614605) B16614605
theorem B29537075 : Blo 2047435 29537075 := bstep (se 1 (by rfl) ⟨22152806, by rfl⟩ : syracuseStep 29537075 = 44305613) B44305613
theorem B19691383 : Blo 2047435 19691383 := bstep (se 1 (by rfl) ⟨14768537, by rfl⟩ : syracuseStep 19691383 = 29537075) B29537075
theorem B26255177 : Blo 2047435 26255177 := bstep (se 2 (by rfl) ⟨9845691, by rfl⟩ : syracuseStep 26255177 = 19691383) B19691383
theorem B17503451 : Blo 2047435 17503451 := bstep (se 1 (by rfl) ⟨13127588, by rfl⟩ : syracuseStep 17503451 = 26255177) B26255177
theorem B11668967 : Blo 2047435 11668967 := bstep (se 1 (by rfl) ⟨8751725, by rfl⟩ : syracuseStep 11668967 = 17503451) B17503451
theorem B7779311 : Blo 2047435 7779311 := bstep (se 1 (by rfl) ⟨5834483, by rfl⟩ : syracuseStep 7779311 = 11668967) B11668967
theorem B5186207 : Blo 2047435 5186207 := bstep (se 1 (by rfl) ⟨3889655, by rfl⟩ : syracuseStep 5186207 = 7779311) B7779311
theorem B3457471 : Blo 2047435 3457471 := bstep (se 1 (by rfl) ⟨2593103, by rfl⟩ : syracuseStep 3457471 = 5186207) B5186207
theorem B4609961 : Blo 2047435 4609961 := bstep (se 2 (by rfl) ⟨1728735, by rfl⟩ : syracuseStep 4609961 = 3457471) B3457471
theorem B3073307 : Blo 2047435 3073307 := bstep (se 1 (by rfl) ⟨2304980, by rfl⟩ : syracuseStep 3073307 = 4609961) B4609961
theorem B2048871 : Blo 2047435 2048871 := bstep (se 1 (by rfl) ⟨1536653, by rfl⟩ : syracuseStep 2048871 = 3073307) B3073307
theorem B2304985 : Blo 2047435 2304985 := bbase (se 2 (by rfl) ⟨864369, by rfl⟩ : syracuseStep 2304985 = 1728739) (by norm_num)
theorem B3073313 : Blo 2047435 3073313 := bstep (se 2 (by rfl) ⟨1152492, by rfl⟩ : syracuseStep 3073313 = 2304985) B2304985
theorem B2048875 : Blo 2047435 2048875 := bstep (se 1 (by rfl) ⟨1536656, by rfl⟩ : syracuseStep 2048875 = 3073313) B3073313
theorem B2917253 : Blo 2047435 2917253 := bbase (se 4 (by rfl) ⟨273492, by rfl⟩ : syracuseStep 2917253 = 546985) (by norm_num)
theorem B7779341 : Blo 2047435 7779341 := bstep (se 3 (by rfl) ⟨1458626, by rfl⟩ : syracuseStep 7779341 = 2917253) B2917253
theorem B5186227 : Blo 2047435 5186227 := bstep (se 1 (by rfl) ⟨3889670, by rfl⟩ : syracuseStep 5186227 = 7779341) B7779341
theorem B6914969 : Blo 2047435 6914969 := bstep (se 2 (by rfl) ⟨2593113, by rfl⟩ : syracuseStep 6914969 = 5186227) B5186227
theorem B4609979 : Blo 2047435 4609979 := bstep (se 1 (by rfl) ⟨3457484, by rfl⟩ : syracuseStep 4609979 = 6914969) B6914969
theorem B3073319 : Blo 2047435 3073319 := bstep (se 1 (by rfl) ⟨2304989, by rfl⟩ : syracuseStep 3073319 = 4609979) B4609979
theorem B2048879 : Blo 2047435 2048879 := bstep (se 1 (by rfl) ⟨1536659, by rfl⟩ : syracuseStep 2048879 = 3073319) B3073319
theorem B3073325 : Blo 2047435 3073325 := bbase (se 3 (by rfl) ⟨576248, by rfl⟩ : syracuseStep 3073325 = 1152497) (by norm_num)
theorem B2048883 : Blo 2047435 2048883 := bstep (se 1 (by rfl) ⟨1536662, by rfl⟩ : syracuseStep 2048883 = 3073325) B3073325
theorem B4609997 : Blo 2047435 4609997 := bbase (se 3 (by rfl) ⟨864374, by rfl⟩ : syracuseStep 4609997 = 1728749) (by norm_num)
theorem B3073331 : Blo 2047435 3073331 := bstep (se 1 (by rfl) ⟨2304998, by rfl⟩ : syracuseStep 3073331 = 4609997) B4609997
theorem B2048887 : Blo 2047435 2048887 := bstep (se 1 (by rfl) ⟨1536665, by rfl⟩ : syracuseStep 2048887 = 3073331) B3073331
theorem B2593129 : Blo 2047435 2593129 := bbase (se 2 (by rfl) ⟨972423, by rfl⟩ : syracuseStep 2593129 = 1944847) (by norm_num)
theorem B3457505 : Blo 2047435 3457505 := bstep (se 2 (by rfl) ⟨1296564, by rfl⟩ : syracuseStep 3457505 = 2593129) B2593129
theorem B2305003 : Blo 2047435 2305003 := bstep (se 1 (by rfl) ⟨1728752, by rfl⟩ : syracuseStep 2305003 = 3457505) B3457505
theorem B3073337 : Blo 2047435 3073337 := bstep (se 2 (by rfl) ⟨1152501, by rfl⟩ : syracuseStep 3073337 = 2305003) B2305003
theorem B2048891 : Blo 2047435 2048891 := bstep (se 1 (by rfl) ⟨1536668, by rfl⟩ : syracuseStep 2048891 = 3073337) B3073337
theorem B11076533 : Blo 2047435 11076533 := bbase (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) (by norm_num)
theorem B7384355 : Blo 2047435 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B4922903 : Blo 2047435 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B13127741 : Blo 2047435 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B8751827 : Blo 2047435 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B23338205 : Blo 2047435 23338205 := bstep (se 3 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 23338205 = 8751827) B8751827
theorem B15558803 : Blo 2047435 15558803 := bstep (se 1 (by rfl) ⟨11669102, by rfl⟩ : syracuseStep 15558803 = 23338205) B23338205
theorem B10372535 : Blo 2047435 10372535 := bstep (se 1 (by rfl) ⟨7779401, by rfl⟩ : syracuseStep 10372535 = 15558803) B15558803
theorem B6915023 : Blo 2047435 6915023 := bstep (se 1 (by rfl) ⟨5186267, by rfl⟩ : syracuseStep 6915023 = 10372535) B10372535
theorem B4610015 : Blo 2047435 4610015 := bstep (se 1 (by rfl) ⟨3457511, by rfl⟩ : syracuseStep 4610015 = 6915023) B6915023
theorem B3073343 : Blo 2047435 3073343 := bstep (se 1 (by rfl) ⟨2305007, by rfl⟩ : syracuseStep 3073343 = 4610015) B4610015
theorem B2048895 : Blo 2047435 2048895 := bstep (se 1 (by rfl) ⟨1536671, by rfl⟩ : syracuseStep 2048895 = 3073343) B3073343
theorem B3073349 : Blo 2047435 3073349 := bbase (se 4 (by rfl) ⟨288126, by rfl⟩ : syracuseStep 3073349 = 576253) (by norm_num)
theorem B2048899 : Blo 2047435 2048899 := bstep (se 1 (by rfl) ⟨1536674, by rfl⟩ : syracuseStep 2048899 = 3073349) B3073349
theorem B3457525 : Blo 2047435 3457525 := bbase (se 5 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 3457525 = 324143) (by norm_num)
theorem B4610033 : Blo 2047435 4610033 := bstep (se 2 (by rfl) ⟨1728762, by rfl⟩ : syracuseStep 4610033 = 3457525) B3457525
theorem B3073355 : Blo 2047435 3073355 := bstep (se 1 (by rfl) ⟨2305016, by rfl⟩ : syracuseStep 3073355 = 4610033) B4610033
theorem B2048903 : Blo 2047435 2048903 := bstep (se 1 (by rfl) ⟨1536677, by rfl⟩ : syracuseStep 2048903 = 3073355) B3073355
theorem B2305021 : Blo 2047435 2305021 := bbase (se 3 (by rfl) ⟨432191, by rfl⟩ : syracuseStep 2305021 = 864383) (by norm_num)
theorem B3073361 : Blo 2047435 3073361 := bstep (se 2 (by rfl) ⟨1152510, by rfl⟩ : syracuseStep 3073361 = 2305021) B2305021
theorem B2048907 : Blo 2047435 2048907 := bstep (se 1 (by rfl) ⟨1536680, by rfl⟩ : syracuseStep 2048907 = 3073361) B3073361
theorem B6915077 : Blo 2047435 6915077 := bbase (se 4 (by rfl) ⟨648288, by rfl⟩ : syracuseStep 6915077 = 1296577) (by norm_num)
theorem B4610051 : Blo 2047435 4610051 := bstep (se 1 (by rfl) ⟨3457538, by rfl⟩ : syracuseStep 4610051 = 6915077) B6915077
theorem B3073367 : Blo 2047435 3073367 := bstep (se 1 (by rfl) ⟨2305025, by rfl⟩ : syracuseStep 3073367 = 4610051) B4610051
theorem B2048911 : Blo 2047435 2048911 := bstep (se 1 (by rfl) ⟨1536683, by rfl⟩ : syracuseStep 2048911 = 3073367) B3073367
theorem B3073373 : Blo 2047435 3073373 := bbase (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) (by norm_num)
theorem B2048915 : Blo 2047435 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B4610069 : Blo 2047435 4610069 := bbase (se 6 (by rfl) ⟨108048, by rfl⟩ : syracuseStep 4610069 = 216097) (by norm_num)
theorem B3073379 : Blo 2047435 3073379 := bstep (se 1 (by rfl) ⟨2305034, by rfl⟩ : syracuseStep 3073379 = 4610069) B4610069
theorem B2048919 : Blo 2047435 2048919 := bstep (se 1 (by rfl) ⟨1536689, by rfl⟩ : syracuseStep 2048919 = 3073379) B3073379
theorem B7779509 : Blo 2047435 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B5186339 : Blo 2047435 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B3457559 : Blo 2047435 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B2305039 : Blo 2047435 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B3073385 : Blo 2047435 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B2048923 : Blo 2047435 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B4922981 : Blo 2047435 4922981 := bbase (se 4 (by rfl) ⟨461529, by rfl⟩ : syracuseStep 4922981 = 923059) (by norm_num)
theorem B3281987 : Blo 2047435 3281987 := bstep (se 1 (by rfl) ⟨2461490, by rfl⟩ : syracuseStep 3281987 = 4922981) B4922981
theorem B2187991 : Blo 2047435 2187991 := bstep (se 1 (by rfl) ⟨1640993, by rfl⟩ : syracuseStep 2187991 = 3281987) B3281987
theorem B11669285 : Blo 2047435 11669285 := bstep (se 4 (by rfl) ⟨1093995, by rfl⟩ : syracuseStep 11669285 = 2187991) B2187991
theorem B7779523 : Blo 2047435 7779523 := bstep (se 1 (by rfl) ⟨5834642, by rfl⟩ : syracuseStep 7779523 = 11669285) B11669285
theorem B10372697 : Blo 2047435 10372697 := bstep (se 2 (by rfl) ⟨3889761, by rfl⟩ : syracuseStep 10372697 = 7779523) B7779523
theorem B6915131 : Blo 2047435 6915131 := bstep (se 1 (by rfl) ⟨5186348, by rfl⟩ : syracuseStep 6915131 = 10372697) B10372697
theorem B4610087 : Blo 2047435 4610087 := bstep (se 1 (by rfl) ⟨3457565, by rfl⟩ : syracuseStep 4610087 = 6915131) B6915131
theorem B3073391 : Blo 2047435 3073391 := bstep (se 1 (by rfl) ⟨2305043, by rfl⟩ : syracuseStep 3073391 = 4610087) B4610087
theorem B2048927 : Blo 2047435 2048927 := bstep (se 1 (by rfl) ⟨1536695, by rfl⟩ : syracuseStep 2048927 = 3073391) B3073391
theorem B3073397 : Blo 2047435 3073397 := bbase (se 5 (by rfl) ⟨144065, by rfl⟩ : syracuseStep 3073397 = 288131) (by norm_num)
theorem B2048931 : Blo 2047435 2048931 := bstep (se 1 (by rfl) ⟨1536698, by rfl⟩ : syracuseStep 2048931 = 3073397) B3073397
theorem B2917333 : Blo 2047435 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B3889777 : Blo 2047435 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B5186369 : Blo 2047435 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B3457579 : Blo 2047435 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B4610105 : Blo 2047435 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B3073403 : Blo 2047435 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B2048935 : Blo 2047435 2048935 := bstep (se 1 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 2048935 = 3073403) B3073403
theorem B2305057 : Blo 2047435 2305057 := bbase (se 2 (by rfl) ⟨864396, by rfl⟩ : syracuseStep 2305057 = 1728793) (by norm_num)
theorem B3073409 : Blo 2047435 3073409 := bstep (se 2 (by rfl) ⟨1152528, by rfl⟩ : syracuseStep 3073409 = 2305057) B2305057
theorem B2048939 : Blo 2047435 2048939 := bstep (se 1 (by rfl) ⟨1536704, by rfl⟩ : syracuseStep 2048939 = 3073409) B3073409
theorem B5186389 : Blo 2047435 5186389 := bbase (se 9 (by rfl) ⟨15194, by rfl⟩ : syracuseStep 5186389 = 30389) (by norm_num)
theorem B6915185 : Blo 2047435 6915185 := bstep (se 2 (by rfl) ⟨2593194, by rfl⟩ : syracuseStep 6915185 = 5186389) B5186389
theorem B4610123 : Blo 2047435 4610123 := bstep (se 1 (by rfl) ⟨3457592, by rfl⟩ : syracuseStep 4610123 = 6915185) B6915185
theorem B3073415 : Blo 2047435 3073415 := bstep (se 1 (by rfl) ⟨2305061, by rfl⟩ : syracuseStep 3073415 = 4610123) B4610123
theorem B2048943 : Blo 2047435 2048943 := bstep (se 1 (by rfl) ⟨1536707, by rfl⟩ : syracuseStep 2048943 = 3073415) B3073415
theorem B3073421 : Blo 2047435 3073421 := bbase (se 3 (by rfl) ⟨576266, by rfl⟩ : syracuseStep 3073421 = 1152533) (by norm_num)
theorem B2048947 : Blo 2047435 2048947 := bstep (se 1 (by rfl) ⟨1536710, by rfl⟩ : syracuseStep 2048947 = 3073421) B3073421
theorem B4610141 : Blo 2047435 4610141 := bbase (se 3 (by rfl) ⟨864401, by rfl⟩ : syracuseStep 4610141 = 1728803) (by norm_num)
theorem B3073427 : Blo 2047435 3073427 := bstep (se 1 (by rfl) ⟨2305070, by rfl⟩ : syracuseStep 3073427 = 4610141) B4610141
theorem B2048951 : Blo 2047435 2048951 := bstep (se 1 (by rfl) ⟨1536713, by rfl⟩ : syracuseStep 2048951 = 3073427) B3073427
theorem B3457613 : Blo 2047435 3457613 := bbase (se 3 (by rfl) ⟨648302, by rfl⟩ : syracuseStep 3457613 = 1296605) (by norm_num)
theorem B2305075 : Blo 2047435 2305075 := bstep (se 1 (by rfl) ⟨1728806, by rfl⟩ : syracuseStep 2305075 = 3457613) B3457613
theorem B3073433 : Blo 2047435 3073433 := bstep (se 2 (by rfl) ⟨1152537, by rfl⟩ : syracuseStep 3073433 = 2305075) B2305075
theorem B2048955 : Blo 2047435 2048955 := bstep (se 1 (by rfl) ⟨1536716, by rfl⟩ : syracuseStep 2048955 = 3073433) B3073433
theorem B9346117 : Blo 2047435 9346117 := bbase (se 4 (by rfl) ⟨876198, by rfl⟩ : syracuseStep 9346117 = 1752397) (by norm_num)
theorem B12461489 : Blo 2047435 12461489 := bstep (se 2 (by rfl) ⟨4673058, by rfl⟩ : syracuseStep 12461489 = 9346117) B9346117
theorem B8307659 : Blo 2047435 8307659 := bstep (se 1 (by rfl) ⟨6230744, by rfl⟩ : syracuseStep 8307659 = 12461489) B12461489
theorem B5538439 : Blo 2047435 5538439 := bstep (se 1 (by rfl) ⟨4153829, by rfl⟩ : syracuseStep 5538439 = 8307659) B8307659
theorem B29538341 : Blo 2047435 29538341 := bstep (se 4 (by rfl) ⟨2769219, by rfl⟩ : syracuseStep 29538341 = 5538439) B5538439
theorem B19692227 : Blo 2047435 19692227 := bstep (se 1 (by rfl) ⟨14769170, by rfl⟩ : syracuseStep 19692227 = 29538341) B29538341
theorem B13128151 : Blo 2047435 13128151 := bstep (se 1 (by rfl) ⟨9846113, by rfl⟩ : syracuseStep 13128151 = 19692227) B19692227
theorem B17504201 : Blo 2047435 17504201 := bstep (se 2 (by rfl) ⟨6564075, by rfl⟩ : syracuseStep 17504201 = 13128151) B13128151
theorem B11669467 : Blo 2047435 11669467 := bstep (se 1 (by rfl) ⟨8752100, by rfl⟩ : syracuseStep 11669467 = 17504201) B17504201
theorem B15559289 : Blo 2047435 15559289 := bstep (se 2 (by rfl) ⟨5834733, by rfl⟩ : syracuseStep 15559289 = 11669467) B11669467
theorem B10372859 : Blo 2047435 10372859 := bstep (se 1 (by rfl) ⟨7779644, by rfl⟩ : syracuseStep 10372859 = 15559289) B15559289
theorem B6915239 : Blo 2047435 6915239 := bstep (se 1 (by rfl) ⟨5186429, by rfl⟩ : syracuseStep 6915239 = 10372859) B10372859
theorem B4610159 : Blo 2047435 4610159 := bstep (se 1 (by rfl) ⟨3457619, by rfl⟩ : syracuseStep 4610159 = 6915239) B6915239
theorem B3073439 : Blo 2047435 3073439 := bstep (se 1 (by rfl) ⟨2305079, by rfl⟩ : syracuseStep 3073439 = 4610159) B4610159
theorem B2048959 : Blo 2047435 2048959 := bstep (se 1 (by rfl) ⟨1536719, by rfl⟩ : syracuseStep 2048959 = 3073439) B3073439
theorem B3073445 : Blo 2047435 3073445 := bbase (se 4 (by rfl) ⟨288135, by rfl⟩ : syracuseStep 3073445 = 576271) (by norm_num)
theorem B2048963 : Blo 2047435 2048963 := bstep (se 1 (by rfl) ⟨1536722, by rfl⟩ : syracuseStep 2048963 = 3073445) B3073445
theorem B2593225 : Blo 2047435 2593225 := bbase (se 2 (by rfl) ⟨972459, by rfl⟩ : syracuseStep 2593225 = 1944919) (by norm_num)
theorem B3457633 : Blo 2047435 3457633 := bstep (se 2 (by rfl) ⟨1296612, by rfl⟩ : syracuseStep 3457633 = 2593225) B2593225
theorem B4610177 : Blo 2047435 4610177 := bstep (se 2 (by rfl) ⟨1728816, by rfl⟩ : syracuseStep 4610177 = 3457633) B3457633
theorem B3073451 : Blo 2047435 3073451 := bstep (se 1 (by rfl) ⟨2305088, by rfl⟩ : syracuseStep 3073451 = 4610177) B4610177
theorem B2048967 : Blo 2047435 2048967 := bstep (se 1 (by rfl) ⟨1536725, by rfl⟩ : syracuseStep 2048967 = 3073451) B3073451
theorem B2305093 : Blo 2047435 2305093 := bbase (se 4 (by rfl) ⟨216102, by rfl⟩ : syracuseStep 2305093 = 432205) (by norm_num)
theorem B3073457 : Blo 2047435 3073457 := bstep (se 2 (by rfl) ⟨1152546, by rfl⟩ : syracuseStep 3073457 = 2305093) B2305093
theorem B2048971 : Blo 2047435 2048971 := bstep (se 1 (by rfl) ⟨1536728, by rfl⟩ : syracuseStep 2048971 = 3073457) B3073457
theorem B3889853 : Blo 2047435 3889853 := bbase (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) (by norm_num)
theorem B2593235 : Blo 2047435 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B6915293 : Blo 2047435 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B4610195 : Blo 2047435 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B3073463 : Blo 2047435 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B2048975 : Blo 2047435 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B3073469 : Blo 2047435 3073469 := bbase (se 3 (by rfl) ⟨576275, by rfl⟩ : syracuseStep 3073469 = 1152551) (by norm_num)
theorem B2048979 : Blo 2047435 2048979 := bstep (se 1 (by rfl) ⟨1536734, by rfl⟩ : syracuseStep 2048979 = 3073469) B3073469
theorem B4610213 : Blo 2047435 4610213 := bbase (se 4 (by rfl) ⟨432207, by rfl⟩ : syracuseStep 4610213 = 864415) (by norm_num)
theorem B3073475 : Blo 2047435 3073475 := bstep (se 1 (by rfl) ⟨2305106, by rfl⟩ : syracuseStep 3073475 = 4610213) B4610213
theorem B2048983 : Blo 2047435 2048983 := bstep (se 1 (by rfl) ⟨1536737, by rfl⟩ : syracuseStep 2048983 = 3073475) B3073475
theorem B5186501 : Blo 2047435 5186501 := bbase (se 4 (by rfl) ⟨486234, by rfl⟩ : syracuseStep 5186501 = 972469) (by norm_num)
theorem B3457667 : Blo 2047435 3457667 := bstep (se 1 (by rfl) ⟨2593250, by rfl⟩ : syracuseStep 3457667 = 5186501) B5186501
theorem B2305111 : Blo 2047435 2305111 := bstep (se 1 (by rfl) ⟨1728833, by rfl⟩ : syracuseStep 2305111 = 3457667) B3457667
theorem B3073481 : Blo 2047435 3073481 := bstep (se 2 (by rfl) ⟨1152555, by rfl⟩ : syracuseStep 3073481 = 2305111) B2305111
theorem B2048987 : Blo 2047435 2048987 := bstep (se 1 (by rfl) ⟨1536740, by rfl⟩ : syracuseStep 2048987 = 3073481) B3073481
theorem B10514549 : Blo 2047435 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B28038797 : Blo 2047435 28038797 := bstep (se 3 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 28038797 = 10514549) B10514549
theorem B18692531 : Blo 2047435 18692531 := bstep (se 1 (by rfl) ⟨14019398, by rfl⟩ : syracuseStep 18692531 = 28038797) B28038797
theorem B12461687 : Blo 2047435 12461687 := bstep (se 1 (by rfl) ⟨9346265, by rfl⟩ : syracuseStep 12461687 = 18692531) B18692531
theorem B8307791 : Blo 2047435 8307791 := bstep (se 1 (by rfl) ⟨6230843, by rfl⟩ : syracuseStep 8307791 = 12461687) B12461687
theorem B5538527 : Blo 2047435 5538527 := bstep (se 1 (by rfl) ⟨4153895, by rfl⟩ : syracuseStep 5538527 = 8307791) B8307791
theorem B3692351 : Blo 2047435 3692351 := bstep (se 1 (by rfl) ⟨2769263, by rfl⟩ : syracuseStep 3692351 = 5538527) B5538527
theorem B9846269 : Blo 2047435 9846269 := bstep (se 3 (by rfl) ⟨1846175, by rfl⟩ : syracuseStep 9846269 = 3692351) B3692351
theorem B6564179 : Blo 2047435 6564179 := bstep (se 1 (by rfl) ⟨4923134, by rfl⟩ : syracuseStep 6564179 = 9846269) B9846269
theorem B4376119 : Blo 2047435 4376119 := bstep (se 1 (by rfl) ⟨3282089, by rfl⟩ : syracuseStep 4376119 = 6564179) B6564179
theorem B5834825 : Blo 2047435 5834825 := bstep (se 2 (by rfl) ⟨2188059, by rfl⟩ : syracuseStep 5834825 = 4376119) B4376119
theorem B3889883 : Blo 2047435 3889883 := bstep (se 1 (by rfl) ⟨2917412, by rfl⟩ : syracuseStep 3889883 = 5834825) B5834825
theorem B10373021 : Blo 2047435 10373021 := bstep (se 3 (by rfl) ⟨1944941, by rfl⟩ : syracuseStep 10373021 = 3889883) B3889883
theorem B6915347 : Blo 2047435 6915347 := bstep (se 1 (by rfl) ⟨5186510, by rfl⟩ : syracuseStep 6915347 = 10373021) B10373021
theorem B4610231 : Blo 2047435 4610231 := bstep (se 1 (by rfl) ⟨3457673, by rfl⟩ : syracuseStep 4610231 = 6915347) B6915347
theorem B3073487 : Blo 2047435 3073487 := bstep (se 1 (by rfl) ⟨2305115, by rfl⟩ : syracuseStep 3073487 = 4610231) B4610231
theorem B2048991 : Blo 2047435 2048991 := bstep (se 1 (by rfl) ⟨1536743, by rfl⟩ : syracuseStep 2048991 = 3073487) B3073487
theorem B3073493 : Blo 2047435 3073493 := bbase (se 7 (by rfl) ⟨36017, by rfl⟩ : syracuseStep 3073493 = 72035) (by norm_num)
theorem B2048995 : Blo 2047435 2048995 := bstep (se 1 (by rfl) ⟨1536746, by rfl⟩ : syracuseStep 2048995 = 3073493) B3073493
theorem B7779797 : Blo 2047435 7779797 := bbase (se 7 (by rfl) ⟨91169, by rfl⟩ : syracuseStep 7779797 = 182339) (by norm_num)
theorem B5186531 : Blo 2047435 5186531 := bstep (se 1 (by rfl) ⟨3889898, by rfl⟩ : syracuseStep 5186531 = 7779797) B7779797
theorem B3457687 : Blo 2047435 3457687 := bstep (se 1 (by rfl) ⟨2593265, by rfl⟩ : syracuseStep 3457687 = 5186531) B5186531
theorem B4610249 : Blo 2047435 4610249 := bstep (se 2 (by rfl) ⟨1728843, by rfl⟩ : syracuseStep 4610249 = 3457687) B3457687
theorem B3073499 : Blo 2047435 3073499 := bstep (se 1 (by rfl) ⟨2305124, by rfl⟩ : syracuseStep 3073499 = 4610249) B4610249
theorem B2048999 : Blo 2047435 2048999 := bstep (se 1 (by rfl) ⟨1536749, by rfl⟩ : syracuseStep 2048999 = 3073499) B3073499
theorem B2305129 : Blo 2047435 2305129 := bbase (se 2 (by rfl) ⟨864423, by rfl⟩ : syracuseStep 2305129 = 1728847) (by norm_num)
theorem B3073505 : Blo 2047435 3073505 := bstep (se 2 (by rfl) ⟨1152564, by rfl⟩ : syracuseStep 3073505 = 2305129) B2305129
theorem B2049003 : Blo 2047435 2049003 := bstep (se 1 (by rfl) ⟨1536752, by rfl⟩ : syracuseStep 2049003 = 3073505) B3073505
theorem B4923173 : Blo 2047435 4923173 := bbase (se 4 (by rfl) ⟨461547, by rfl⟩ : syracuseStep 4923173 = 923095) (by norm_num)
theorem B3282115 : Blo 2047435 3282115 := bstep (se 1 (by rfl) ⟨2461586, by rfl⟩ : syracuseStep 3282115 = 4923173) B4923173
theorem B4376153 : Blo 2047435 4376153 := bstep (se 2 (by rfl) ⟨1641057, by rfl⟩ : syracuseStep 4376153 = 3282115) B3282115
theorem B11669741 : Blo 2047435 11669741 := bstep (se 3 (by rfl) ⟨2188076, by rfl⟩ : syracuseStep 11669741 = 4376153) B4376153
theorem B7779827 : Blo 2047435 7779827 := bstep (se 1 (by rfl) ⟨5834870, by rfl⟩ : syracuseStep 7779827 = 11669741) B11669741
theorem B5186551 : Blo 2047435 5186551 := bstep (se 1 (by rfl) ⟨3889913, by rfl⟩ : syracuseStep 5186551 = 7779827) B7779827
theorem B6915401 : Blo 2047435 6915401 := bstep (se 2 (by rfl) ⟨2593275, by rfl⟩ : syracuseStep 6915401 = 5186551) B5186551
theorem B4610267 : Blo 2047435 4610267 := bstep (se 1 (by rfl) ⟨3457700, by rfl⟩ : syracuseStep 4610267 = 6915401) B6915401
theorem B3073511 : Blo 2047435 3073511 := bstep (se 1 (by rfl) ⟨2305133, by rfl⟩ : syracuseStep 3073511 = 4610267) B4610267
theorem B2049007 : Blo 2047435 2049007 := bstep (se 1 (by rfl) ⟨1536755, by rfl⟩ : syracuseStep 2049007 = 3073511) B3073511
theorem B3073517 : Blo 2047435 3073517 := bbase (se 3 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 3073517 = 1152569) (by norm_num)
theorem B2049011 : Blo 2047435 2049011 := bstep (se 1 (by rfl) ⟨1536758, by rfl⟩ : syracuseStep 2049011 = 3073517) B3073517
theorem B4610285 : Blo 2047435 4610285 := bbase (se 3 (by rfl) ⟨864428, by rfl⟩ : syracuseStep 4610285 = 1728857) (by norm_num)
theorem B3073523 : Blo 2047435 3073523 := bstep (se 1 (by rfl) ⟨2305142, by rfl⟩ : syracuseStep 3073523 = 4610285) B4610285
theorem B2049015 : Blo 2047435 2049015 := bstep (se 1 (by rfl) ⟨1536761, by rfl⟩ : syracuseStep 2049015 = 3073523) B3073523
theorem B2917453 : Blo 2047435 2917453 := bbase (se 3 (by rfl) ⟨547022, by rfl⟩ : syracuseStep 2917453 = 1094045) (by norm_num)
theorem B3889937 : Blo 2047435 3889937 := bstep (se 2 (by rfl) ⟨1458726, by rfl⟩ : syracuseStep 3889937 = 2917453) B2917453
theorem B2593291 : Blo 2047435 2593291 := bstep (se 1 (by rfl) ⟨1944968, by rfl⟩ : syracuseStep 2593291 = 3889937) B3889937
theorem B3457721 : Blo 2047435 3457721 := bstep (se 2 (by rfl) ⟨1296645, by rfl⟩ : syracuseStep 3457721 = 2593291) B2593291
theorem B2305147 : Blo 2047435 2305147 := bstep (se 1 (by rfl) ⟨1728860, by rfl⟩ : syracuseStep 2305147 = 3457721) B3457721
theorem B3073529 : Blo 2047435 3073529 := bstep (se 2 (by rfl) ⟨1152573, by rfl⟩ : syracuseStep 3073529 = 2305147) B2305147
theorem B2049019 : Blo 2047435 2049019 := bstep (se 1 (by rfl) ⟨1536764, by rfl⟩ : syracuseStep 2049019 = 3073529) B3073529
theorem B2368481 : Blo 2047435 2368481 := bbase (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) (by norm_num)
theorem B25263797 : Blo 2047435 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B67370125 : Blo 2047435 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B89826833 : Blo 2047435 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B59884555 : Blo 2047435 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B79846073 : Blo 2047435 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B53230715 : Blo 2047435 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B35487143 : Blo 2047435 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B23658095 : Blo 2047435 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B63088253 : Blo 2047435 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B42058835 : Blo 2047435 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B28039223 : Blo 2047435 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B74771261 : Blo 2047435 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B49847507 : Blo 2047435 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B33231671 : Blo 2047435 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B22154447 : Blo 2047435 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B14769631 : Blo 2047435 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B78771365 : Blo 2047435 78771365 := bstep (se 4 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 78771365 = 14769631) B14769631
theorem B52514243 : Blo 2047435 52514243 := bstep (se 1 (by rfl) ⟨39385682, by rfl⟩ : syracuseStep 52514243 = 78771365) B78771365
theorem B35009495 : Blo 2047435 35009495 := bstep (se 1 (by rfl) ⟨26257121, by rfl⟩ : syracuseStep 35009495 = 52514243) B52514243
theorem B23339663 : Blo 2047435 23339663 := bstep (se 1 (by rfl) ⟨17504747, by rfl⟩ : syracuseStep 23339663 = 35009495) B35009495
theorem B15559775 : Blo 2047435 15559775 := bstep (se 1 (by rfl) ⟨11669831, by rfl⟩ : syracuseStep 15559775 = 23339663) B23339663
theorem B10373183 : Blo 2047435 10373183 := bstep (se 1 (by rfl) ⟨7779887, by rfl⟩ : syracuseStep 10373183 = 15559775) B15559775
theorem B6915455 : Blo 2047435 6915455 := bstep (se 1 (by rfl) ⟨5186591, by rfl⟩ : syracuseStep 6915455 = 10373183) B10373183
theorem B4610303 : Blo 2047435 4610303 := bstep (se 1 (by rfl) ⟨3457727, by rfl⟩ : syracuseStep 4610303 = 6915455) B6915455
theorem B3073535 : Blo 2047435 3073535 := bstep (se 1 (by rfl) ⟨2305151, by rfl⟩ : syracuseStep 3073535 = 4610303) B4610303
theorem B2049023 : Blo 2047435 2049023 := bstep (se 1 (by rfl) ⟨1536767, by rfl⟩ : syracuseStep 2049023 = 3073535) B3073535
theorem B3073541 : Blo 2047435 3073541 := bbase (se 4 (by rfl) ⟨288144, by rfl⟩ : syracuseStep 3073541 = 576289) (by norm_num)
theorem B2049027 : Blo 2047435 2049027 := bstep (se 1 (by rfl) ⟨1536770, by rfl⟩ : syracuseStep 2049027 = 3073541) B3073541
theorem B3457741 : Blo 2047435 3457741 := bbase (se 3 (by rfl) ⟨648326, by rfl⟩ : syracuseStep 3457741 = 1296653) (by norm_num)
theorem B4610321 : Blo 2047435 4610321 := bstep (se 2 (by rfl) ⟨1728870, by rfl⟩ : syracuseStep 4610321 = 3457741) B3457741
theorem B3073547 : Blo 2047435 3073547 := bstep (se 1 (by rfl) ⟨2305160, by rfl⟩ : syracuseStep 3073547 = 4610321) B4610321
theorem B2049031 : Blo 2047435 2049031 := bstep (se 1 (by rfl) ⟨1536773, by rfl⟩ : syracuseStep 2049031 = 3073547) B3073547
theorem B2305165 : Blo 2047435 2305165 := bbase (se 3 (by rfl) ⟨432218, by rfl⟩ : syracuseStep 2305165 = 864437) (by norm_num)
theorem B3073553 : Blo 2047435 3073553 := bstep (se 2 (by rfl) ⟨1152582, by rfl⟩ : syracuseStep 3073553 = 2305165) B2305165
theorem B2049035 : Blo 2047435 2049035 := bstep (se 1 (by rfl) ⟨1536776, by rfl⟩ : syracuseStep 2049035 = 3073553) B3073553
theorem B6915509 : Blo 2047435 6915509 := bbase (se 5 (by rfl) ⟨324164, by rfl⟩ : syracuseStep 6915509 = 648329) (by norm_num)
theorem B4610339 : Blo 2047435 4610339 := bstep (se 1 (by rfl) ⟨3457754, by rfl⟩ : syracuseStep 4610339 = 6915509) B6915509
theorem B3073559 : Blo 2047435 3073559 := bstep (se 1 (by rfl) ⟨2305169, by rfl⟩ : syracuseStep 3073559 = 4610339) B4610339
theorem B2049039 : Blo 2047435 2049039 := bstep (se 1 (by rfl) ⟨1536779, by rfl⟩ : syracuseStep 2049039 = 3073559) B3073559
theorem B3073565 : Blo 2047435 3073565 := bbase (se 3 (by rfl) ⟨576293, by rfl⟩ : syracuseStep 3073565 = 1152587) (by norm_num)
theorem B2049043 : Blo 2047435 2049043 := bstep (se 1 (by rfl) ⟨1536782, by rfl⟩ : syracuseStep 2049043 = 3073565) B3073565
theorem B4610357 : Blo 2047435 4610357 := bbase (se 5 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 4610357 = 432221) (by norm_num)
theorem B3073571 : Blo 2047435 3073571 := bstep (se 1 (by rfl) ⟨2305178, by rfl⟩ : syracuseStep 3073571 = 4610357) B4610357
theorem B2049047 : Blo 2047435 2049047 := bstep (se 1 (by rfl) ⟨1536785, by rfl⟩ : syracuseStep 2049047 = 3073571) B3073571
theorem B4673269 : Blo 2047435 4673269 := bbase (se 5 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 4673269 = 438119) (by norm_num)
theorem B6231025 : Blo 2047435 6231025 := bstep (se 2 (by rfl) ⟨2336634, by rfl⟩ : syracuseStep 6231025 = 4673269) B4673269
theorem B33232133 : Blo 2047435 33232133 := bstep (se 4 (by rfl) ⟨3115512, by rfl⟩ : syracuseStep 33232133 = 6231025) B6231025
theorem B22154755 : Blo 2047435 22154755 := bstep (se 1 (by rfl) ⟨16616066, by rfl⟩ : syracuseStep 22154755 = 33232133) B33232133
theorem B29539673 : Blo 2047435 29539673 := bstep (se 2 (by rfl) ⟨11077377, by rfl⟩ : syracuseStep 29539673 = 22154755) B22154755
theorem B19693115 : Blo 2047435 19693115 := bstep (se 1 (by rfl) ⟨14769836, by rfl⟩ : syracuseStep 19693115 = 29539673) B29539673
theorem B13128743 : Blo 2047435 13128743 := bstep (se 1 (by rfl) ⟨9846557, by rfl⟩ : syracuseStep 13128743 = 19693115) B19693115
theorem B8752495 : Blo 2047435 8752495 := bstep (se 1 (by rfl) ⟨6564371, by rfl⟩ : syracuseStep 8752495 = 13128743) B13128743
theorem B11669993 : Blo 2047435 11669993 := bstep (se 2 (by rfl) ⟨4376247, by rfl⟩ : syracuseStep 11669993 = 8752495) B8752495
theorem B7779995 : Blo 2047435 7779995 := bstep (se 1 (by rfl) ⟨5834996, by rfl⟩ : syracuseStep 7779995 = 11669993) B11669993
theorem B5186663 : Blo 2047435 5186663 := bstep (se 1 (by rfl) ⟨3889997, by rfl⟩ : syracuseStep 5186663 = 7779995) B7779995
theorem B3457775 : Blo 2047435 3457775 := bstep (se 1 (by rfl) ⟨2593331, by rfl⟩ : syracuseStep 3457775 = 5186663) B5186663
theorem B2305183 : Blo 2047435 2305183 := bstep (se 1 (by rfl) ⟨1728887, by rfl⟩ : syracuseStep 2305183 = 3457775) B3457775
theorem B3073577 : Blo 2047435 3073577 := bstep (se 2 (by rfl) ⟨1152591, by rfl⟩ : syracuseStep 3073577 = 2305183) B2305183
theorem B2049051 : Blo 2047435 2049051 := bstep (se 1 (by rfl) ⟨1536788, by rfl⟩ : syracuseStep 2049051 = 3073577) B3073577
theorem B18693109 : Blo 2047435 18693109 := bbase (se 5 (by rfl) ⟨876239, by rfl⟩ : syracuseStep 18693109 = 1752479) (by norm_num)
theorem B99696581 : Blo 2047435 99696581 := bstep (se 4 (by rfl) ⟨9346554, by rfl⟩ : syracuseStep 99696581 = 18693109) B18693109
theorem B66464387 : Blo 2047435 66464387 := bstep (se 1 (by rfl) ⟨49848290, by rfl⟩ : syracuseStep 66464387 = 99696581) B99696581
theorem B44309591 : Blo 2047435 44309591 := bstep (se 1 (by rfl) ⟨33232193, by rfl⟩ : syracuseStep 44309591 = 66464387) B66464387
theorem B29539727 : Blo 2047435 29539727 := bstep (se 1 (by rfl) ⟨22154795, by rfl⟩ : syracuseStep 29539727 = 44309591) B44309591
theorem B19693151 : Blo 2047435 19693151 := bstep (se 1 (by rfl) ⟨14769863, by rfl⟩ : syracuseStep 19693151 = 29539727) B29539727
theorem B13128767 : Blo 2047435 13128767 := bstep (se 1 (by rfl) ⟨9846575, by rfl⟩ : syracuseStep 13128767 = 19693151) B19693151
theorem B8752511 : Blo 2047435 8752511 := bstep (se 1 (by rfl) ⟨6564383, by rfl⟩ : syracuseStep 8752511 = 13128767) B13128767
theorem B5835007 : Blo 2047435 5835007 := bstep (se 1 (by rfl) ⟨4376255, by rfl⟩ : syracuseStep 5835007 = 8752511) B8752511
theorem B7780009 : Blo 2047435 7780009 := bstep (se 2 (by rfl) ⟨2917503, by rfl⟩ : syracuseStep 7780009 = 5835007) B5835007
theorem B10373345 : Blo 2047435 10373345 := bstep (se 2 (by rfl) ⟨3890004, by rfl⟩ : syracuseStep 10373345 = 7780009) B7780009
theorem B6915563 : Blo 2047435 6915563 := bstep (se 1 (by rfl) ⟨5186672, by rfl⟩ : syracuseStep 6915563 = 10373345) B10373345
theorem B4610375 : Blo 2047435 4610375 := bstep (se 1 (by rfl) ⟨3457781, by rfl⟩ : syracuseStep 4610375 = 6915563) B6915563
theorem B3073583 : Blo 2047435 3073583 := bstep (se 1 (by rfl) ⟨2305187, by rfl⟩ : syracuseStep 3073583 = 4610375) B4610375
theorem B2049055 : Blo 2047435 2049055 := bstep (se 1 (by rfl) ⟨1536791, by rfl⟩ : syracuseStep 2049055 = 3073583) B3073583
theorem B3073589 : Blo 2047435 3073589 := bbase (se 5 (by rfl) ⟨144074, by rfl⟩ : syracuseStep 3073589 = 288149) (by norm_num)
theorem B2049059 : Blo 2047435 2049059 := bstep (se 1 (by rfl) ⟨1536794, by rfl⟩ : syracuseStep 2049059 = 3073589) B3073589
theorem B5186693 : Blo 2047435 5186693 := bbase (se 4 (by rfl) ⟨486252, by rfl⟩ : syracuseStep 5186693 = 972505) (by norm_num)
theorem B3457795 : Blo 2047435 3457795 := bstep (se 1 (by rfl) ⟨2593346, by rfl⟩ : syracuseStep 3457795 = 5186693) B5186693
theorem B4610393 : Blo 2047435 4610393 := bstep (se 2 (by rfl) ⟨1728897, by rfl⟩ : syracuseStep 4610393 = 3457795) B3457795
theorem B3073595 : Blo 2047435 3073595 := bstep (se 1 (by rfl) ⟨2305196, by rfl⟩ : syracuseStep 3073595 = 4610393) B4610393
theorem B2049063 : Blo 2047435 2049063 := bstep (se 1 (by rfl) ⟨1536797, by rfl⟩ : syracuseStep 2049063 = 3073595) B3073595
theorem B2305201 : Blo 2047435 2305201 := bbase (se 2 (by rfl) ⟨864450, by rfl⟩ : syracuseStep 2305201 = 1728901) (by norm_num)
theorem B3073601 : Blo 2047435 3073601 := bstep (se 2 (by rfl) ⟨1152600, by rfl⟩ : syracuseStep 3073601 = 2305201) B2305201
theorem B2049067 : Blo 2047435 2049067 := bstep (se 1 (by rfl) ⟨1536800, by rfl⟩ : syracuseStep 2049067 = 3073601) B3073601
theorem B2188145 : Blo 2047435 2188145 := bbase (se 2 (by rfl) ⟨820554, by rfl⟩ : syracuseStep 2188145 = 1641109) (by norm_num)
theorem B5835053 : Blo 2047435 5835053 := bstep (se 3 (by rfl) ⟨1094072, by rfl⟩ : syracuseStep 5835053 = 2188145) B2188145
theorem B3890035 : Blo 2047435 3890035 := bstep (se 1 (by rfl) ⟨2917526, by rfl⟩ : syracuseStep 3890035 = 5835053) B5835053
theorem B5186713 : Blo 2047435 5186713 := bstep (se 2 (by rfl) ⟨1945017, by rfl⟩ : syracuseStep 5186713 = 3890035) B3890035
theorem B6915617 : Blo 2047435 6915617 := bstep (se 2 (by rfl) ⟨2593356, by rfl⟩ : syracuseStep 6915617 = 5186713) B5186713
theorem B4610411 : Blo 2047435 4610411 := bstep (se 1 (by rfl) ⟨3457808, by rfl⟩ : syracuseStep 4610411 = 6915617) B6915617
theorem B3073607 : Blo 2047435 3073607 := bstep (se 1 (by rfl) ⟨2305205, by rfl⟩ : syracuseStep 3073607 = 4610411) B4610411
theorem B2049071 : Blo 2047435 2049071 := bstep (se 1 (by rfl) ⟨1536803, by rfl⟩ : syracuseStep 2049071 = 3073607) B3073607
theorem B3073613 : Blo 2047435 3073613 := bbase (se 3 (by rfl) ⟨576302, by rfl⟩ : syracuseStep 3073613 = 1152605) (by norm_num)
theorem B2049075 : Blo 2047435 2049075 := bstep (se 1 (by rfl) ⟨1536806, by rfl⟩ : syracuseStep 2049075 = 3073613) B3073613
theorem B4610429 : Blo 2047435 4610429 := bbase (se 3 (by rfl) ⟨864455, by rfl⟩ : syracuseStep 4610429 = 1728911) (by norm_num)
theorem B3073619 : Blo 2047435 3073619 := bstep (se 1 (by rfl) ⟨2305214, by rfl⟩ : syracuseStep 3073619 = 4610429) B4610429
theorem B2049079 : Blo 2047435 2049079 := bstep (se 1 (by rfl) ⟨1536809, by rfl⟩ : syracuseStep 2049079 = 3073619) B3073619
theorem B3457829 : Blo 2047435 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B2305219 : Blo 2047435 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B3073625 : Blo 2047435 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B2049083 : Blo 2047435 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B2917549 : Blo 2047435 2917549 := bbase (se 3 (by rfl) ⟨547040, by rfl⟩ : syracuseStep 2917549 = 1094081) (by norm_num)
theorem B15560261 : Blo 2047435 15560261 := bstep (se 4 (by rfl) ⟨1458774, by rfl⟩ : syracuseStep 15560261 = 2917549) B2917549
theorem B10373507 : Blo 2047435 10373507 := bstep (se 1 (by rfl) ⟨7780130, by rfl⟩ : syracuseStep 10373507 = 15560261) B15560261
theorem B6915671 : Blo 2047435 6915671 := bstep (se 1 (by rfl) ⟨5186753, by rfl⟩ : syracuseStep 6915671 = 10373507) B10373507
theorem B4610447 : Blo 2047435 4610447 := bstep (se 1 (by rfl) ⟨3457835, by rfl⟩ : syracuseStep 4610447 = 6915671) B6915671
theorem B3073631 : Blo 2047435 3073631 := bstep (se 1 (by rfl) ⟨2305223, by rfl⟩ : syracuseStep 3073631 = 4610447) B4610447
theorem B2049087 : Blo 2047435 2049087 := bstep (se 1 (by rfl) ⟨1536815, by rfl⟩ : syracuseStep 2049087 = 3073631) B3073631
theorem B3073637 : Blo 2047435 3073637 := bbase (se 4 (by rfl) ⟨288153, by rfl⟩ : syracuseStep 3073637 = 576307) (by norm_num)
theorem B2049091 : Blo 2047435 2049091 := bstep (se 1 (by rfl) ⟨1536818, by rfl⟩ : syracuseStep 2049091 = 3073637) B3073637
theorem B2461693 : Blo 2047435 2461693 := bbase (se 3 (by rfl) ⟨461567, by rfl⟩ : syracuseStep 2461693 = 923135) (by norm_num)
theorem B3282257 : Blo 2047435 3282257 := bstep (se 2 (by rfl) ⟨1230846, by rfl⟩ : syracuseStep 3282257 = 2461693) B2461693
theorem B2188171 : Blo 2047435 2188171 := bstep (se 1 (by rfl) ⟨1641128, by rfl⟩ : syracuseStep 2188171 = 3282257) B3282257
theorem B2917561 : Blo 2047435 2917561 := bstep (se 2 (by rfl) ⟨1094085, by rfl⟩ : syracuseStep 2917561 = 2188171) B2188171
theorem B3890081 : Blo 2047435 3890081 := bstep (se 2 (by rfl) ⟨1458780, by rfl⟩ : syracuseStep 3890081 = 2917561) B2917561
theorem B2593387 : Blo 2047435 2593387 := bstep (se 1 (by rfl) ⟨1945040, by rfl⟩ : syracuseStep 2593387 = 3890081) B3890081
theorem B3457849 : Blo 2047435 3457849 := bstep (se 2 (by rfl) ⟨1296693, by rfl⟩ : syracuseStep 3457849 = 2593387) B2593387
theorem B4610465 : Blo 2047435 4610465 := bstep (se 2 (by rfl) ⟨1728924, by rfl⟩ : syracuseStep 4610465 = 3457849) B3457849
theorem B3073643 : Blo 2047435 3073643 := bstep (se 1 (by rfl) ⟨2305232, by rfl⟩ : syracuseStep 3073643 = 4610465) B4610465
theorem B2049095 : Blo 2047435 2049095 := bstep (se 1 (by rfl) ⟨1536821, by rfl⟩ : syracuseStep 2049095 = 3073643) B3073643
theorem B2305237 : Blo 2047435 2305237 := bbase (se 7 (by rfl) ⟨27014, by rfl⟩ : syracuseStep 2305237 = 54029) (by norm_num)
theorem B3073649 : Blo 2047435 3073649 := bstep (se 2 (by rfl) ⟨1152618, by rfl⟩ : syracuseStep 3073649 = 2305237) B2305237
theorem B2049099 : Blo 2047435 2049099 := bstep (se 1 (by rfl) ⟨1536824, by rfl⟩ : syracuseStep 2049099 = 3073649) B3073649
theorem B2593397 : Blo 2047435 2593397 := bbase (se 5 (by rfl) ⟨121565, by rfl⟩ : syracuseStep 2593397 = 243131) (by norm_num)
theorem B6915725 : Blo 2047435 6915725 := bstep (se 3 (by rfl) ⟨1296698, by rfl⟩ : syracuseStep 6915725 = 2593397) B2593397
theorem B4610483 : Blo 2047435 4610483 := bstep (se 1 (by rfl) ⟨3457862, by rfl⟩ : syracuseStep 4610483 = 6915725) B6915725
theorem B3073655 : Blo 2047435 3073655 := bstep (se 1 (by rfl) ⟨2305241, by rfl⟩ : syracuseStep 3073655 = 4610483) B4610483
theorem B2049103 : Blo 2047435 2049103 := bstep (se 1 (by rfl) ⟨1536827, by rfl⟩ : syracuseStep 2049103 = 3073655) B3073655
theorem B3073661 : Blo 2047435 3073661 := bbase (se 3 (by rfl) ⟨576311, by rfl⟩ : syracuseStep 3073661 = 1152623) (by norm_num)
theorem B2049107 : Blo 2047435 2049107 := bstep (se 1 (by rfl) ⟨1536830, by rfl⟩ : syracuseStep 2049107 = 3073661) B3073661
theorem B4610501 : Blo 2047435 4610501 := bbase (se 4 (by rfl) ⟨432234, by rfl⟩ : syracuseStep 4610501 = 864469) (by norm_num)
theorem B3073667 : Blo 2047435 3073667 := bstep (se 1 (by rfl) ⟨2305250, by rfl⟩ : syracuseStep 3073667 = 4610501) B4610501
theorem B2049111 : Blo 2047435 2049111 := bstep (se 1 (by rfl) ⟨1536833, by rfl⟩ : syracuseStep 2049111 = 3073667) B3073667
theorem B37897429 : Blo 2047435 37897429 := bbase (se 7 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 37897429 = 888221) (by norm_num)
theorem B50529905 : Blo 2047435 50529905 := bstep (se 2 (by rfl) ⟨18948714, by rfl⟩ : syracuseStep 50529905 = 37897429) B37897429
theorem B33686603 : Blo 2047435 33686603 := bstep (se 1 (by rfl) ⟨25264952, by rfl⟩ : syracuseStep 33686603 = 50529905) B50529905
theorem B22457735 : Blo 2047435 22457735 := bstep (se 1 (by rfl) ⟨16843301, by rfl⟩ : syracuseStep 22457735 = 33686603) B33686603
theorem B14971823 : Blo 2047435 14971823 := bstep (se 1 (by rfl) ⟨11228867, by rfl⟩ : syracuseStep 14971823 = 22457735) B22457735
theorem B9981215 : Blo 2047435 9981215 := bstep (se 1 (by rfl) ⟨7485911, by rfl⟩ : syracuseStep 9981215 = 14971823) B14971823
theorem B6654143 : Blo 2047435 6654143 := bstep (se 1 (by rfl) ⟨4990607, by rfl⟩ : syracuseStep 6654143 = 9981215) B9981215
theorem B4436095 : Blo 2047435 4436095 := bstep (se 1 (by rfl) ⟨3327071, by rfl⟩ : syracuseStep 4436095 = 6654143) B6654143
theorem B5914793 : Blo 2047435 5914793 := bstep (se 2 (by rfl) ⟨2218047, by rfl⟩ : syracuseStep 5914793 = 4436095) B4436095
theorem B15772781 : Blo 2047435 15772781 := bstep (se 3 (by rfl) ⟨2957396, by rfl⟩ : syracuseStep 15772781 = 5914793) B5914793
theorem B10515187 : Blo 2047435 10515187 := bstep (se 1 (by rfl) ⟨7886390, by rfl⟩ : syracuseStep 10515187 = 15772781) B15772781
theorem B14020249 : Blo 2047435 14020249 := bstep (se 2 (by rfl) ⟨5257593, by rfl⟩ : syracuseStep 14020249 = 10515187) B10515187
theorem B18693665 : Blo 2047435 18693665 := bstep (se 2 (by rfl) ⟨7010124, by rfl⟩ : syracuseStep 18693665 = 14020249) B14020249
theorem B12462443 : Blo 2047435 12462443 := bstep (se 1 (by rfl) ⟨9346832, by rfl⟩ : syracuseStep 12462443 = 18693665) B18693665
theorem B8308295 : Blo 2047435 8308295 := bstep (se 1 (by rfl) ⟨6231221, by rfl⟩ : syracuseStep 8308295 = 12462443) B12462443
theorem B5538863 : Blo 2047435 5538863 := bstep (se 1 (by rfl) ⟨4154147, by rfl⟩ : syracuseStep 5538863 = 8308295) B8308295
theorem B3692575 : Blo 2047435 3692575 := bstep (se 1 (by rfl) ⟨2769431, by rfl⟩ : syracuseStep 3692575 = 5538863) B5538863
theorem B4923433 : Blo 2047435 4923433 := bstep (se 2 (by rfl) ⟨1846287, by rfl⟩ : syracuseStep 4923433 = 3692575) B3692575
theorem B6564577 : Blo 2047435 6564577 := bstep (se 2 (by rfl) ⟨2461716, by rfl⟩ : syracuseStep 6564577 = 4923433) B4923433
theorem B8752769 : Blo 2047435 8752769 := bstep (se 2 (by rfl) ⟨3282288, by rfl⟩ : syracuseStep 8752769 = 6564577) B6564577
theorem B5835179 : Blo 2047435 5835179 := bstep (se 1 (by rfl) ⟨4376384, by rfl⟩ : syracuseStep 5835179 = 8752769) B8752769
theorem B3890119 : Blo 2047435 3890119 := bstep (se 1 (by rfl) ⟨2917589, by rfl⟩ : syracuseStep 3890119 = 5835179) B5835179
theorem B5186825 : Blo 2047435 5186825 := bstep (se 2 (by rfl) ⟨1945059, by rfl⟩ : syracuseStep 5186825 = 3890119) B3890119
theorem B3457883 : Blo 2047435 3457883 := bstep (se 1 (by rfl) ⟨2593412, by rfl⟩ : syracuseStep 3457883 = 5186825) B5186825
theorem B2305255 : Blo 2047435 2305255 := bstep (se 1 (by rfl) ⟨1728941, by rfl⟩ : syracuseStep 2305255 = 3457883) B3457883
theorem B3073673 : Blo 2047435 3073673 := bstep (se 2 (by rfl) ⟨1152627, by rfl⟩ : syracuseStep 3073673 = 2305255) B2305255
theorem B2049115 : Blo 2047435 2049115 := bstep (se 1 (by rfl) ⟨1536836, by rfl⟩ : syracuseStep 2049115 = 3073673) B3073673
theorem B10373669 : Blo 2047435 10373669 := bbase (se 4 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 10373669 = 1945063) (by norm_num)
theorem B6915779 : Blo 2047435 6915779 := bstep (se 1 (by rfl) ⟨5186834, by rfl⟩ : syracuseStep 6915779 = 10373669) B10373669
theorem B4610519 : Blo 2047435 4610519 := bstep (se 1 (by rfl) ⟨3457889, by rfl⟩ : syracuseStep 4610519 = 6915779) B6915779
theorem B3073679 : Blo 2047435 3073679 := bstep (se 1 (by rfl) ⟨2305259, by rfl⟩ : syracuseStep 3073679 = 4610519) B4610519
theorem B2049119 : Blo 2047435 2049119 := bstep (se 1 (by rfl) ⟨1536839, by rfl⟩ : syracuseStep 2049119 = 3073679) B3073679
theorem B3073685 : Blo 2047435 3073685 := bbase (se 6 (by rfl) ⟨72039, by rfl⟩ : syracuseStep 3073685 = 144079) (by norm_num)
theorem B2049123 : Blo 2047435 2049123 := bstep (se 1 (by rfl) ⟨1536842, by rfl⟩ : syracuseStep 2049123 = 3073685) B3073685
theorem B4923461 : Blo 2047435 4923461 := bbase (se 4 (by rfl) ⟨461574, by rfl⟩ : syracuseStep 4923461 = 923149) (by norm_num)
theorem B13129229 : Blo 2047435 13129229 := bstep (se 3 (by rfl) ⟨2461730, by rfl⟩ : syracuseStep 13129229 = 4923461) B4923461
theorem B8752819 : Blo 2047435 8752819 := bstep (se 1 (by rfl) ⟨6564614, by rfl⟩ : syracuseStep 8752819 = 13129229) B13129229
theorem B11670425 : Blo 2047435 11670425 := bstep (se 2 (by rfl) ⟨4376409, by rfl⟩ : syracuseStep 11670425 = 8752819) B8752819
theorem B7780283 : Blo 2047435 7780283 := bstep (se 1 (by rfl) ⟨5835212, by rfl⟩ : syracuseStep 7780283 = 11670425) B11670425
theorem B5186855 : Blo 2047435 5186855 := bstep (se 1 (by rfl) ⟨3890141, by rfl⟩ : syracuseStep 5186855 = 7780283) B7780283
theorem B3457903 : Blo 2047435 3457903 := bstep (se 1 (by rfl) ⟨2593427, by rfl⟩ : syracuseStep 3457903 = 5186855) B5186855
theorem B4610537 : Blo 2047435 4610537 := bstep (se 2 (by rfl) ⟨1728951, by rfl⟩ : syracuseStep 4610537 = 3457903) B3457903
theorem B3073691 : Blo 2047435 3073691 := bstep (se 1 (by rfl) ⟨2305268, by rfl⟩ : syracuseStep 3073691 = 4610537) B4610537
theorem B2049127 : Blo 2047435 2049127 := bstep (se 1 (by rfl) ⟨1536845, by rfl⟩ : syracuseStep 2049127 = 3073691) B3073691
theorem B2305273 : Blo 2047435 2305273 := bbase (se 2 (by rfl) ⟨864477, by rfl⟩ : syracuseStep 2305273 = 1728955) (by norm_num)
theorem B3073697 : Blo 2047435 3073697 := bstep (se 2 (by rfl) ⟨1152636, by rfl⟩ : syracuseStep 3073697 = 2305273) B2305273
theorem B2049131 : Blo 2047435 2049131 := bstep (se 1 (by rfl) ⟨1536848, by rfl⟩ : syracuseStep 2049131 = 3073697) B3073697
theorem B8752853 : Blo 2047435 8752853 := bbase (se 7 (by rfl) ⟨102572, by rfl⟩ : syracuseStep 8752853 = 205145) (by norm_num)
theorem B5835235 : Blo 2047435 5835235 := bstep (se 1 (by rfl) ⟨4376426, by rfl⟩ : syracuseStep 5835235 = 8752853) B8752853
theorem B7780313 : Blo 2047435 7780313 := bstep (se 2 (by rfl) ⟨2917617, by rfl⟩ : syracuseStep 7780313 = 5835235) B5835235
theorem B5186875 : Blo 2047435 5186875 := bstep (se 1 (by rfl) ⟨3890156, by rfl⟩ : syracuseStep 5186875 = 7780313) B7780313
theorem B6915833 : Blo 2047435 6915833 := bstep (se 2 (by rfl) ⟨2593437, by rfl⟩ : syracuseStep 6915833 = 5186875) B5186875
theorem B4610555 : Blo 2047435 4610555 := bstep (se 1 (by rfl) ⟨3457916, by rfl⟩ : syracuseStep 4610555 = 6915833) B6915833
theorem B3073703 : Blo 2047435 3073703 := bstep (se 1 (by rfl) ⟨2305277, by rfl⟩ : syracuseStep 3073703 = 4610555) B4610555
theorem B2049135 : Blo 2047435 2049135 := bstep (se 1 (by rfl) ⟨1536851, by rfl⟩ : syracuseStep 2049135 = 3073703) B3073703
theorem B3073709 : Blo 2047435 3073709 := bbase (se 3 (by rfl) ⟨576320, by rfl⟩ : syracuseStep 3073709 = 1152641) (by norm_num)
theorem B2049139 : Blo 2047435 2049139 := bstep (se 1 (by rfl) ⟨1536854, by rfl⟩ : syracuseStep 2049139 = 3073709) B3073709
theorem B4610573 : Blo 2047435 4610573 := bbase (se 3 (by rfl) ⟨864482, by rfl⟩ : syracuseStep 4610573 = 1728965) (by norm_num)
theorem B3073715 : Blo 2047435 3073715 := bstep (se 1 (by rfl) ⟨2305286, by rfl⟩ : syracuseStep 3073715 = 4610573) B4610573
theorem B2049143 : Blo 2047435 2049143 := bstep (se 1 (by rfl) ⟨1536857, by rfl⟩ : syracuseStep 2049143 = 3073715) B3073715
theorem B2593453 : Blo 2047435 2593453 := bbase (se 3 (by rfl) ⟨486272, by rfl⟩ : syracuseStep 2593453 = 972545) (by norm_num)
theorem B3457937 : Blo 2047435 3457937 := bstep (se 2 (by rfl) ⟨1296726, by rfl⟩ : syracuseStep 3457937 = 2593453) B2593453
theorem B2305291 : Blo 2047435 2305291 := bstep (se 1 (by rfl) ⟨1728968, by rfl⟩ : syracuseStep 2305291 = 3457937) B3457937
theorem B3073721 : Blo 2047435 3073721 := bstep (se 2 (by rfl) ⟨1152645, by rfl⟩ : syracuseStep 3073721 = 2305291) B2305291
theorem B2049147 : Blo 2047435 2049147 := bstep (se 1 (by rfl) ⟨1536860, by rfl⟩ : syracuseStep 2049147 = 3073721) B3073721
theorem B5257685 : Blo 2047435 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B3505123 : Blo 2047435 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B18693989 : Blo 2047435 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B12462659 : Blo 2047435 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B8308439 : Blo 2047435 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B5538959 : Blo 2047435 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B3692639 : Blo 2047435 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B2461759 : Blo 2047435 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B13129381 : Blo 2047435 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B17505841 : Blo 2047435 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B23341121 : Blo 2047435 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B15560747 : Blo 2047435 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B10373831 : Blo 2047435 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B6915887 : Blo 2047435 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B4610591 : Blo 2047435 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B3073727 : Blo 2047435 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B2049151 : Blo 2047435 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3073733 : Blo 2047435 3073733 := bbase (se 4 (by rfl) ⟨288162, by rfl⟩ : syracuseStep 3073733 = 576325) (by norm_num)
theorem B2049155 : Blo 2047435 2049155 := bstep (se 1 (by rfl) ⟨1536866, by rfl⟩ : syracuseStep 2049155 = 3073733) B3073733
theorem B3457957 : Blo 2047435 3457957 := bbase (se 4 (by rfl) ⟨324183, by rfl⟩ : syracuseStep 3457957 = 648367) (by norm_num)
theorem B4610609 : Blo 2047435 4610609 := bstep (se 2 (by rfl) ⟨1728978, by rfl⟩ : syracuseStep 4610609 = 3457957) B3457957
theorem B3073739 : Blo 2047435 3073739 := bstep (se 1 (by rfl) ⟨2305304, by rfl⟩ : syracuseStep 3073739 = 4610609) B4610609
theorem B2049159 : Blo 2047435 2049159 := bstep (se 1 (by rfl) ⟨1536869, by rfl⟩ : syracuseStep 2049159 = 3073739) B3073739
theorem B2305309 : Blo 2047435 2305309 := bbase (se 3 (by rfl) ⟨432245, by rfl⟩ : syracuseStep 2305309 = 864491) (by norm_num)
theorem B3073745 : Blo 2047435 3073745 := bstep (se 2 (by rfl) ⟨1152654, by rfl⟩ : syracuseStep 3073745 = 2305309) B2305309
theorem B2049163 : Blo 2047435 2049163 := bstep (se 1 (by rfl) ⟨1536872, by rfl⟩ : syracuseStep 2049163 = 3073745) B3073745
theorem B6915941 : Blo 2047435 6915941 := bbase (se 4 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 6915941 = 1296739) (by norm_num)
theorem B4610627 : Blo 2047435 4610627 := bstep (se 1 (by rfl) ⟨3457970, by rfl⟩ : syracuseStep 4610627 = 6915941) B6915941
theorem B3073751 : Blo 2047435 3073751 := bstep (se 1 (by rfl) ⟨2305313, by rfl⟩ : syracuseStep 3073751 = 4610627) B4610627
theorem B2049167 : Blo 2047435 2049167 := bstep (se 1 (by rfl) ⟨1536875, by rfl⟩ : syracuseStep 2049167 = 3073751) B3073751
theorem B3073757 : Blo 2047435 3073757 := bbase (se 3 (by rfl) ⟨576329, by rfl⟩ : syracuseStep 3073757 = 1152659) (by norm_num)
theorem B2049171 : Blo 2047435 2049171 := bstep (se 1 (by rfl) ⟨1536878, by rfl⟩ : syracuseStep 2049171 = 3073757) B3073757
theorem B4610645 : Blo 2047435 4610645 := bbase (se 8 (by rfl) ⟨27015, by rfl⟩ : syracuseStep 4610645 = 54031) (by norm_num)
theorem B3073763 : Blo 2047435 3073763 := bstep (se 1 (by rfl) ⟨2305322, by rfl⟩ : syracuseStep 3073763 = 4610645) B4610645
theorem B2049175 : Blo 2047435 2049175 := bstep (se 1 (by rfl) ⟨1536881, by rfl⟩ : syracuseStep 2049175 = 3073763) B3073763
theorem B7385381 : Blo 2047435 7385381 := bbase (se 4 (by rfl) ⟨692379, by rfl⟩ : syracuseStep 7385381 = 1384759) (by norm_num)
theorem B4923587 : Blo 2047435 4923587 := bstep (se 1 (by rfl) ⟨3692690, by rfl⟩ : syracuseStep 4923587 = 7385381) B7385381
theorem B3282391 : Blo 2047435 3282391 := bstep (se 1 (by rfl) ⟨2461793, by rfl⟩ : syracuseStep 3282391 = 4923587) B4923587
theorem B4376521 : Blo 2047435 4376521 := bstep (se 2 (by rfl) ⟨1641195, by rfl⟩ : syracuseStep 4376521 = 3282391) B3282391
theorem B5835361 : Blo 2047435 5835361 := bstep (se 2 (by rfl) ⟨2188260, by rfl⟩ : syracuseStep 5835361 = 4376521) B4376521
theorem B7780481 : Blo 2047435 7780481 := bstep (se 2 (by rfl) ⟨2917680, by rfl⟩ : syracuseStep 7780481 = 5835361) B5835361
theorem B5186987 : Blo 2047435 5186987 := bstep (se 1 (by rfl) ⟨3890240, by rfl⟩ : syracuseStep 5186987 = 7780481) B7780481
theorem B3457991 : Blo 2047435 3457991 := bstep (se 1 (by rfl) ⟨2593493, by rfl⟩ : syracuseStep 3457991 = 5186987) B5186987
theorem B2305327 : Blo 2047435 2305327 := bstep (se 1 (by rfl) ⟨1728995, by rfl⟩ : syracuseStep 2305327 = 3457991) B3457991
theorem B3073769 : Blo 2047435 3073769 := bstep (se 2 (by rfl) ⟨1152663, by rfl⟩ : syracuseStep 3073769 = 2305327) B2305327
theorem B2049179 : Blo 2047435 2049179 := bstep (se 1 (by rfl) ⟨1536884, by rfl⟩ : syracuseStep 2049179 = 3073769) B3073769
theorem B5539045 : Blo 2047435 5539045 := bbase (se 4 (by rfl) ⟨519285, by rfl⟩ : syracuseStep 5539045 = 1038571) (by norm_num)
theorem B7385393 : Blo 2047435 7385393 := bstep (se 2 (by rfl) ⟨2769522, by rfl⟩ : syracuseStep 7385393 = 5539045) B5539045
theorem B4923595 : Blo 2047435 4923595 := bstep (se 1 (by rfl) ⟨3692696, by rfl⟩ : syracuseStep 4923595 = 7385393) B7385393
theorem B26259173 : Blo 2047435 26259173 := bstep (se 4 (by rfl) ⟨2461797, by rfl⟩ : syracuseStep 26259173 = 4923595) B4923595
theorem B17506115 : Blo 2047435 17506115 := bstep (se 1 (by rfl) ⟨13129586, by rfl⟩ : syracuseStep 17506115 = 26259173) B26259173
theorem B11670743 : Blo 2047435 11670743 := bstep (se 1 (by rfl) ⟨8753057, by rfl⟩ : syracuseStep 11670743 = 17506115) B17506115
theorem B7780495 : Blo 2047435 7780495 := bstep (se 1 (by rfl) ⟨5835371, by rfl⟩ : syracuseStep 7780495 = 11670743) B11670743
theorem B10373993 : Blo 2047435 10373993 := bstep (se 2 (by rfl) ⟨3890247, by rfl⟩ : syracuseStep 10373993 = 7780495) B7780495
theorem B6915995 : Blo 2047435 6915995 := bstep (se 1 (by rfl) ⟨5186996, by rfl⟩ : syracuseStep 6915995 = 10373993) B10373993
theorem B4610663 : Blo 2047435 4610663 := bstep (se 1 (by rfl) ⟨3457997, by rfl⟩ : syracuseStep 4610663 = 6915995) B6915995
theorem B3073775 : Blo 2047435 3073775 := bstep (se 1 (by rfl) ⟨2305331, by rfl⟩ : syracuseStep 3073775 = 4610663) B4610663
theorem B2049183 : Blo 2047435 2049183 := bstep (se 1 (by rfl) ⟨1536887, by rfl⟩ : syracuseStep 2049183 = 3073775) B3073775
theorem B3073781 : Blo 2047435 3073781 := bbase (se 5 (by rfl) ⟨144083, by rfl⟩ : syracuseStep 3073781 = 288167) (by norm_num)
theorem B2049187 : Blo 2047435 2049187 := bstep (se 1 (by rfl) ⟨1536890, by rfl⟩ : syracuseStep 2049187 = 3073781) B3073781
theorem B8753093 : Blo 2047435 8753093 := bbase (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) (by norm_num)
theorem B5835395 : Blo 2047435 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B3890263 : Blo 2047435 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B5187017 : Blo 2047435 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B3458011 : Blo 2047435 3458011 := bstep (se 1 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 3458011 = 5187017) B5187017
theorem B4610681 : Blo 2047435 4610681 := bstep (se 2 (by rfl) ⟨1729005, by rfl⟩ : syracuseStep 4610681 = 3458011) B3458011
theorem B3073787 : Blo 2047435 3073787 := bstep (se 1 (by rfl) ⟨2305340, by rfl⟩ : syracuseStep 3073787 = 4610681) B4610681
theorem B2049191 : Blo 2047435 2049191 := bstep (se 1 (by rfl) ⟨1536893, by rfl⟩ : syracuseStep 2049191 = 3073787) B3073787
theorem B2305345 : Blo 2047435 2305345 := bbase (se 2 (by rfl) ⟨864504, by rfl⟩ : syracuseStep 2305345 = 1729009) (by norm_num)
theorem B3073793 : Blo 2047435 3073793 := bstep (se 2 (by rfl) ⟨1152672, by rfl⟩ : syracuseStep 3073793 = 2305345) B2305345
theorem B2049195 : Blo 2047435 2049195 := bstep (se 1 (by rfl) ⟨1536896, by rfl⟩ : syracuseStep 2049195 = 3073793) B3073793
theorem B5187037 : Blo 2047435 5187037 := bbase (se 3 (by rfl) ⟨972569, by rfl⟩ : syracuseStep 5187037 = 1945139) (by norm_num)
theorem B6916049 : Blo 2047435 6916049 := bstep (se 2 (by rfl) ⟨2593518, by rfl⟩ : syracuseStep 6916049 = 5187037) B5187037
theorem B4610699 : Blo 2047435 4610699 := bstep (se 1 (by rfl) ⟨3458024, by rfl⟩ : syracuseStep 4610699 = 6916049) B6916049
theorem B3073799 : Blo 2047435 3073799 := bstep (se 1 (by rfl) ⟨2305349, by rfl⟩ : syracuseStep 3073799 = 4610699) B4610699
theorem B2049199 : Blo 2047435 2049199 := bstep (se 1 (by rfl) ⟨1536899, by rfl⟩ : syracuseStep 2049199 = 3073799) B3073799
theorem B3073805 : Blo 2047435 3073805 := bbase (se 3 (by rfl) ⟨576338, by rfl⟩ : syracuseStep 3073805 = 1152677) (by norm_num)
theorem B2049203 : Blo 2047435 2049203 := bstep (se 1 (by rfl) ⟨1536902, by rfl⟩ : syracuseStep 2049203 = 3073805) B3073805
theorem B4610717 : Blo 2047435 4610717 := bbase (se 3 (by rfl) ⟨864509, by rfl⟩ : syracuseStep 4610717 = 1729019) (by norm_num)
theorem B3073811 : Blo 2047435 3073811 := bstep (se 1 (by rfl) ⟨2305358, by rfl⟩ : syracuseStep 3073811 = 4610717) B4610717
theorem B2049207 : Blo 2047435 2049207 := bstep (se 1 (by rfl) ⟨1536905, by rfl⟩ : syracuseStep 2049207 = 3073811) B3073811
theorem B3458045 : Blo 2047435 3458045 := bbase (se 3 (by rfl) ⟨648383, by rfl⟩ : syracuseStep 3458045 = 1296767) (by norm_num)
theorem B2305363 : Blo 2047435 2305363 := bstep (se 1 (by rfl) ⟨1729022, by rfl⟩ : syracuseStep 2305363 = 3458045) B3458045
theorem B3073817 : Blo 2047435 3073817 := bstep (se 2 (by rfl) ⟨1152681, by rfl⟩ : syracuseStep 3073817 = 2305363) B2305363
theorem B2049211 : Blo 2047435 2049211 := bstep (se 1 (by rfl) ⟨1536908, by rfl⟩ : syracuseStep 2049211 = 3073817) B3073817
theorem B4376597 : Blo 2047435 4376597 := bbase (se 6 (by rfl) ⟨102576, by rfl⟩ : syracuseStep 4376597 = 205153) (by norm_num)
theorem B11670925 : Blo 2047435 11670925 := bstep (se 3 (by rfl) ⟨2188298, by rfl⟩ : syracuseStep 11670925 = 4376597) B4376597
theorem B15561233 : Blo 2047435 15561233 := bstep (se 2 (by rfl) ⟨5835462, by rfl⟩ : syracuseStep 15561233 = 11670925) B11670925
theorem B10374155 : Blo 2047435 10374155 := bstep (se 1 (by rfl) ⟨7780616, by rfl⟩ : syracuseStep 10374155 = 15561233) B15561233
theorem B6916103 : Blo 2047435 6916103 := bstep (se 1 (by rfl) ⟨5187077, by rfl⟩ : syracuseStep 6916103 = 10374155) B10374155
theorem B4610735 : Blo 2047435 4610735 := bstep (se 1 (by rfl) ⟨3458051, by rfl⟩ : syracuseStep 4610735 = 6916103) B6916103
theorem B3073823 : Blo 2047435 3073823 := bstep (se 1 (by rfl) ⟨2305367, by rfl⟩ : syracuseStep 3073823 = 4610735) B4610735
theorem B2049215 : Blo 2047435 2049215 := bstep (se 1 (by rfl) ⟨1536911, by rfl⟩ : syracuseStep 2049215 = 3073823) B3073823
theorem B3073829 : Blo 2047435 3073829 := bbase (se 4 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 3073829 = 576343) (by norm_num)
theorem B2049219 : Blo 2047435 2049219 := bstep (se 1 (by rfl) ⟨1536914, by rfl⟩ : syracuseStep 2049219 = 3073829) B3073829
theorem B2593549 : Blo 2047435 2593549 := bbase (se 3 (by rfl) ⟨486290, by rfl⟩ : syracuseStep 2593549 = 972581) (by norm_num)
theorem B3458065 : Blo 2047435 3458065 := bstep (se 2 (by rfl) ⟨1296774, by rfl⟩ : syracuseStep 3458065 = 2593549) B2593549
theorem B4610753 : Blo 2047435 4610753 := bstep (se 2 (by rfl) ⟨1729032, by rfl⟩ : syracuseStep 4610753 = 3458065) B3458065
theorem B3073835 : Blo 2047435 3073835 := bstep (se 1 (by rfl) ⟨2305376, by rfl⟩ : syracuseStep 3073835 = 4610753) B4610753
theorem B2049223 : Blo 2047435 2049223 := bstep (se 1 (by rfl) ⟨1536917, by rfl⟩ : syracuseStep 2049223 = 3073835) B3073835
theorem B2305381 : Blo 2047435 2305381 := bbase (se 4 (by rfl) ⟨216129, by rfl⟩ : syracuseStep 2305381 = 432259) (by norm_num)
theorem B3073841 : Blo 2047435 3073841 := bstep (se 2 (by rfl) ⟨1152690, by rfl⟩ : syracuseStep 3073841 = 2305381) B2305381
theorem B2049227 : Blo 2047435 2049227 := bstep (se 1 (by rfl) ⟨1536920, by rfl⟩ : syracuseStep 2049227 = 3073841) B3073841
theorem B5835509 : Blo 2047435 5835509 := bbase (se 5 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 5835509 = 547079) (by norm_num)
theorem B3890339 : Blo 2047435 3890339 := bstep (se 1 (by rfl) ⟨2917754, by rfl⟩ : syracuseStep 3890339 = 5835509) B5835509
theorem B2593559 : Blo 2047435 2593559 := bstep (se 1 (by rfl) ⟨1945169, by rfl⟩ : syracuseStep 2593559 = 3890339) B3890339
theorem B6916157 : Blo 2047435 6916157 := bstep (se 3 (by rfl) ⟨1296779, by rfl⟩ : syracuseStep 6916157 = 2593559) B2593559
theorem B4610771 : Blo 2047435 4610771 := bstep (se 1 (by rfl) ⟨3458078, by rfl⟩ : syracuseStep 4610771 = 6916157) B6916157
theorem B3073847 : Blo 2047435 3073847 := bstep (se 1 (by rfl) ⟨2305385, by rfl⟩ : syracuseStep 3073847 = 4610771) B4610771
theorem B2049231 : Blo 2047435 2049231 := bstep (se 1 (by rfl) ⟨1536923, by rfl⟩ : syracuseStep 2049231 = 3073847) B3073847
theorem B3073853 : Blo 2047435 3073853 := bbase (se 3 (by rfl) ⟨576347, by rfl⟩ : syracuseStep 3073853 = 1152695) (by norm_num)
theorem B2049235 : Blo 2047435 2049235 := bstep (se 1 (by rfl) ⟨1536926, by rfl⟩ : syracuseStep 2049235 = 3073853) B3073853
theorem B4610789 : Blo 2047435 4610789 := bbase (se 4 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 4610789 = 864523) (by norm_num)
theorem B3073859 : Blo 2047435 3073859 := bstep (se 1 (by rfl) ⟨2305394, by rfl⟩ : syracuseStep 3073859 = 4610789) B4610789
theorem B2049239 : Blo 2047435 2049239 := bstep (se 1 (by rfl) ⟨1536929, by rfl⟩ : syracuseStep 2049239 = 3073859) B3073859
theorem B5187149 : Blo 2047435 5187149 := bbase (se 3 (by rfl) ⟨972590, by rfl⟩ : syracuseStep 5187149 = 1945181) (by norm_num)
theorem B3458099 : Blo 2047435 3458099 := bstep (se 1 (by rfl) ⟨2593574, by rfl⟩ : syracuseStep 3458099 = 5187149) B5187149
theorem B2305399 : Blo 2047435 2305399 := bstep (se 1 (by rfl) ⟨1729049, by rfl⟩ : syracuseStep 2305399 = 3458099) B3458099
theorem B3073865 : Blo 2047435 3073865 := bstep (se 2 (by rfl) ⟨1152699, by rfl⟩ : syracuseStep 3073865 = 2305399) B2305399
theorem B2049243 : Blo 2047435 2049243 := bstep (se 1 (by rfl) ⟨1536932, by rfl⟩ : syracuseStep 2049243 = 3073865) B3073865
theorem B2188333 : Blo 2047435 2188333 := bbase (se 3 (by rfl) ⟨410312, by rfl⟩ : syracuseStep 2188333 = 820625) (by norm_num)
theorem B2917777 : Blo 2047435 2917777 := bstep (se 2 (by rfl) ⟨1094166, by rfl⟩ : syracuseStep 2917777 = 2188333) B2188333
theorem B3890369 : Blo 2047435 3890369 := bstep (se 2 (by rfl) ⟨1458888, by rfl⟩ : syracuseStep 3890369 = 2917777) B2917777
theorem B10374317 : Blo 2047435 10374317 := bstep (se 3 (by rfl) ⟨1945184, by rfl⟩ : syracuseStep 10374317 = 3890369) B3890369
theorem B6916211 : Blo 2047435 6916211 := bstep (se 1 (by rfl) ⟨5187158, by rfl⟩ : syracuseStep 6916211 = 10374317) B10374317
theorem B4610807 : Blo 2047435 4610807 := bstep (se 1 (by rfl) ⟨3458105, by rfl⟩ : syracuseStep 4610807 = 6916211) B6916211
theorem B3073871 : Blo 2047435 3073871 := bstep (se 1 (by rfl) ⟨2305403, by rfl⟩ : syracuseStep 3073871 = 4610807) B4610807
theorem B2049247 : Blo 2047435 2049247 := bstep (se 1 (by rfl) ⟨1536935, by rfl⟩ : syracuseStep 2049247 = 3073871) B3073871
theorem B3073877 : Blo 2047435 3073877 := bbase (se 9 (by rfl) ⟨9005, by rfl⟩ : syracuseStep 3073877 = 18011) (by norm_num)
theorem B2049251 : Blo 2047435 2049251 := bstep (se 1 (by rfl) ⟨1536938, by rfl⟩ : syracuseStep 2049251 = 3073877) B3073877
theorem B4990949 : Blo 2047435 4990949 := bbase (se 4 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 4990949 = 935803) (by norm_num)
theorem B3327299 : Blo 2047435 3327299 := bstep (se 1 (by rfl) ⟨2495474, by rfl⟩ : syracuseStep 3327299 = 4990949) B4990949
theorem B2218199 : Blo 2047435 2218199 := bstep (se 1 (by rfl) ⟨1663649, by rfl⟩ : syracuseStep 2218199 = 3327299) B3327299
theorem B5915197 : Blo 2047435 5915197 := bstep (se 3 (by rfl) ⟨1109099, by rfl⟩ : syracuseStep 5915197 = 2218199) B2218199
theorem B31547717 : Blo 2047435 31547717 := bstep (se 4 (by rfl) ⟨2957598, by rfl⟩ : syracuseStep 31547717 = 5915197) B5915197
theorem B21031811 : Blo 2047435 21031811 := bstep (se 1 (by rfl) ⟨15773858, by rfl⟩ : syracuseStep 21031811 = 31547717) B31547717
theorem B14021207 : Blo 2047435 14021207 := bstep (se 1 (by rfl) ⟨10515905, by rfl⟩ : syracuseStep 14021207 = 21031811) B21031811
theorem B9347471 : Blo 2047435 9347471 := bstep (se 1 (by rfl) ⟨7010603, by rfl⟩ : syracuseStep 9347471 = 14021207) B14021207
theorem B6231647 : Blo 2047435 6231647 := bstep (se 1 (by rfl) ⟨4673735, by rfl⟩ : syracuseStep 6231647 = 9347471) B9347471
theorem B4154431 : Blo 2047435 4154431 := bstep (se 1 (by rfl) ⟨3115823, by rfl⟩ : syracuseStep 4154431 = 6231647) B6231647
theorem B5539241 : Blo 2047435 5539241 := bstep (se 2 (by rfl) ⟨2077215, by rfl⟩ : syracuseStep 5539241 = 4154431) B4154431
theorem B3692827 : Blo 2047435 3692827 := bstep (se 1 (by rfl) ⟨2769620, by rfl⟩ : syracuseStep 3692827 = 5539241) B5539241
theorem B4923769 : Blo 2047435 4923769 := bstep (se 2 (by rfl) ⟨1846413, by rfl⟩ : syracuseStep 4923769 = 3692827) B3692827
theorem B6565025 : Blo 2047435 6565025 := bstep (se 2 (by rfl) ⟨2461884, by rfl⟩ : syracuseStep 6565025 = 4923769) B4923769
theorem B4376683 : Blo 2047435 4376683 := bstep (se 1 (by rfl) ⟨3282512, by rfl⟩ : syracuseStep 4376683 = 6565025) B6565025
theorem B5835577 : Blo 2047435 5835577 := bstep (se 2 (by rfl) ⟨2188341, by rfl⟩ : syracuseStep 5835577 = 4376683) B4376683
theorem B7780769 : Blo 2047435 7780769 := bstep (se 2 (by rfl) ⟨2917788, by rfl⟩ : syracuseStep 7780769 = 5835577) B5835577
theorem B5187179 : Blo 2047435 5187179 := bstep (se 1 (by rfl) ⟨3890384, by rfl⟩ : syracuseStep 5187179 = 7780769) B7780769
theorem B3458119 : Blo 2047435 3458119 := bstep (se 1 (by rfl) ⟨2593589, by rfl⟩ : syracuseStep 3458119 = 5187179) B5187179
theorem B4610825 : Blo 2047435 4610825 := bstep (se 2 (by rfl) ⟨1729059, by rfl⟩ : syracuseStep 4610825 = 3458119) B3458119
theorem B3073883 : Blo 2047435 3073883 := bstep (se 1 (by rfl) ⟨2305412, by rfl⟩ : syracuseStep 3073883 = 4610825) B4610825
theorem B2049255 : Blo 2047435 2049255 := bstep (se 1 (by rfl) ⟨1536941, by rfl⟩ : syracuseStep 2049255 = 3073883) B3073883
theorem B2305417 : Blo 2047435 2305417 := bbase (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) (by norm_num)
theorem B3073889 : Blo 2047435 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B2049259 : Blo 2047435 2049259 := bstep (se 1 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 2049259 = 3073889) B3073889
theorem B4496941 : Blo 2047435 4496941 := bbase (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) (by norm_num)
theorem B23983685 : Blo 2047435 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B15989123 : Blo 2047435 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B42637661 : Blo 2047435 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B28425107 : Blo 2047435 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B18950071 : Blo 2047435 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B25266761 : Blo 2047435 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B16844507 : Blo 2047435 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B11229671 : Blo 2047435 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B7486447 : Blo 2047435 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B9981929 : Blo 2047435 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B6654619 : Blo 2047435 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B35491301 : Blo 2047435 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B23660867 : Blo 2047435 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B63095645 : Blo 2047435 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B168255053 : Blo 2047435 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B112170035 : Blo 2047435 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B74780023 : Blo 2047435 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B99706697 : Blo 2047435 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B66471131 : Blo 2047435 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B44314087 : Blo 2047435 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B59085449 : Blo 2047435 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B39390299 : Blo 2047435 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B26260199 : Blo 2047435 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B17506799 : Blo 2047435 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B11671199 : Blo 2047435 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B7780799 : Blo 2047435 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B5187199 : Blo 2047435 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B6916265 : Blo 2047435 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B4610843 : Blo 2047435 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B3073895 : Blo 2047435 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B2049263 : Blo 2047435 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B3073901 : Blo 2047435 3073901 := bbase (se 3 (by rfl) ⟨576356, by rfl⟩ : syracuseStep 3073901 = 1152713) (by norm_num)
theorem B2049267 : Blo 2047435 2049267 := bstep (se 1 (by rfl) ⟨1536950, by rfl⟩ : syracuseStep 2049267 = 3073901) B3073901
theorem B4610861 : Blo 2047435 4610861 := bbase (se 3 (by rfl) ⟨864536, by rfl⟩ : syracuseStep 4610861 = 1729073) (by norm_num)
theorem B3073907 : Blo 2047435 3073907 := bstep (se 1 (by rfl) ⟨2305430, by rfl⟩ : syracuseStep 3073907 = 4610861) B4610861
theorem B2049271 : Blo 2047435 2049271 := bstep (se 1 (by rfl) ⟨1536953, by rfl⟩ : syracuseStep 2049271 = 3073907) B3073907
theorem B2461909 : Blo 2047435 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B3282545 : Blo 2047435 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B8753453 : Blo 2047435 8753453 := bstep (se 3 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 8753453 = 3282545) B3282545
theorem B5835635 : Blo 2047435 5835635 := bstep (se 1 (by rfl) ⟨4376726, by rfl⟩ : syracuseStep 5835635 = 8753453) B8753453
theorem B3890423 : Blo 2047435 3890423 := bstep (se 1 (by rfl) ⟨2917817, by rfl⟩ : syracuseStep 3890423 = 5835635) B5835635
theorem B2593615 : Blo 2047435 2593615 := bstep (se 1 (by rfl) ⟨1945211, by rfl⟩ : syracuseStep 2593615 = 3890423) B3890423
theorem B3458153 : Blo 2047435 3458153 := bstep (se 2 (by rfl) ⟨1296807, by rfl⟩ : syracuseStep 3458153 = 2593615) B2593615
theorem B2305435 : Blo 2047435 2305435 := bstep (se 1 (by rfl) ⟨1729076, by rfl⟩ : syracuseStep 2305435 = 3458153) B3458153
theorem B3073913 : Blo 2047435 3073913 := bstep (se 2 (by rfl) ⟨1152717, by rfl⟩ : syracuseStep 3073913 = 2305435) B2305435
theorem B2049275 : Blo 2047435 2049275 := bstep (se 1 (by rfl) ⟨1536956, by rfl⟩ : syracuseStep 2049275 = 3073913) B3073913
theorem B14771477 : Blo 2047435 14771477 := bbase (se 6 (by rfl) ⟨346206, by rfl⟩ : syracuseStep 14771477 = 692413) (by norm_num)
theorem B9847651 : Blo 2047435 9847651 := bstep (se 1 (by rfl) ⟨7385738, by rfl⟩ : syracuseStep 9847651 = 14771477) B14771477
theorem B13130201 : Blo 2047435 13130201 := bstep (se 2 (by rfl) ⟨4923825, by rfl⟩ : syracuseStep 13130201 = 9847651) B9847651
theorem B35013869 : Blo 2047435 35013869 := bstep (se 3 (by rfl) ⟨6565100, by rfl⟩ : syracuseStep 35013869 = 13130201) B13130201
theorem B23342579 : Blo 2047435 23342579 := bstep (se 1 (by rfl) ⟨17506934, by rfl⟩ : syracuseStep 23342579 = 35013869) B35013869
theorem B15561719 : Blo 2047435 15561719 := bstep (se 1 (by rfl) ⟨11671289, by rfl⟩ : syracuseStep 15561719 = 23342579) B23342579
theorem B10374479 : Blo 2047435 10374479 := bstep (se 1 (by rfl) ⟨7780859, by rfl⟩ : syracuseStep 10374479 = 15561719) B15561719
theorem B6916319 : Blo 2047435 6916319 := bstep (se 1 (by rfl) ⟨5187239, by rfl⟩ : syracuseStep 6916319 = 10374479) B10374479
theorem B4610879 : Blo 2047435 4610879 := bstep (se 1 (by rfl) ⟨3458159, by rfl⟩ : syracuseStep 4610879 = 6916319) B6916319
theorem B3073919 : Blo 2047435 3073919 := bstep (se 1 (by rfl) ⟨2305439, by rfl⟩ : syracuseStep 3073919 = 4610879) B4610879
theorem B2049279 : Blo 2047435 2049279 := bstep (se 1 (by rfl) ⟨1536959, by rfl⟩ : syracuseStep 2049279 = 3073919) B3073919
theorem B3073925 : Blo 2047435 3073925 := bbase (se 4 (by rfl) ⟨288180, by rfl⟩ : syracuseStep 3073925 = 576361) (by norm_num)
theorem B2049283 : Blo 2047435 2049283 := bstep (se 1 (by rfl) ⟨1536962, by rfl⟩ : syracuseStep 2049283 = 3073925) B3073925
theorem B3458173 : Blo 2047435 3458173 := bbase (se 3 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 3458173 = 1296815) (by norm_num)
theorem B4610897 : Blo 2047435 4610897 := bstep (se 2 (by rfl) ⟨1729086, by rfl⟩ : syracuseStep 4610897 = 3458173) B3458173
theorem B3073931 : Blo 2047435 3073931 := bstep (se 1 (by rfl) ⟨2305448, by rfl⟩ : syracuseStep 3073931 = 4610897) B4610897
theorem B2049287 : Blo 2047435 2049287 := bstep (se 1 (by rfl) ⟨1536965, by rfl⟩ : syracuseStep 2049287 = 3073931) B3073931
theorem B2305453 : Blo 2047435 2305453 := bbase (se 3 (by rfl) ⟨432272, by rfl⟩ : syracuseStep 2305453 = 864545) (by norm_num)
theorem B3073937 : Blo 2047435 3073937 := bstep (se 2 (by rfl) ⟨1152726, by rfl⟩ : syracuseStep 3073937 = 2305453) B2305453
theorem B2049291 : Blo 2047435 2049291 := bstep (se 1 (by rfl) ⟨1536968, by rfl⟩ : syracuseStep 2049291 = 3073937) B3073937
theorem B6916373 : Blo 2047435 6916373 := bbase (se 6 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 6916373 = 324205) (by norm_num)
theorem B4610915 : Blo 2047435 4610915 := bstep (se 1 (by rfl) ⟨3458186, by rfl⟩ : syracuseStep 4610915 = 6916373) B6916373
theorem B3073943 : Blo 2047435 3073943 := bstep (se 1 (by rfl) ⟨2305457, by rfl⟩ : syracuseStep 3073943 = 4610915) B4610915
theorem B2049295 : Blo 2047435 2049295 := bstep (se 1 (by rfl) ⟨1536971, by rfl⟩ : syracuseStep 2049295 = 3073943) B3073943
theorem B3073949 : Blo 2047435 3073949 := bbase (se 3 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 3073949 = 1152731) (by norm_num)
theorem B2049299 : Blo 2047435 2049299 := bstep (se 1 (by rfl) ⟨1536974, by rfl⟩ : syracuseStep 2049299 = 3073949) B3073949
theorem B4610933 : Blo 2047435 4610933 := bbase (se 5 (by rfl) ⟨216137, by rfl⟩ : syracuseStep 4610933 = 432275) (by norm_num)
theorem B3073955 : Blo 2047435 3073955 := bstep (se 1 (by rfl) ⟨2305466, by rfl⟩ : syracuseStep 3073955 = 4610933) B4610933
theorem B2049303 : Blo 2047435 2049303 := bstep (se 1 (by rfl) ⟨1536977, by rfl⟩ : syracuseStep 2049303 = 3073955) B3073955
theorem B17746037 : Blo 2047435 17746037 := bbase (se 5 (by rfl) ⟨831845, by rfl⟩ : syracuseStep 17746037 = 1663691) (by norm_num)
theorem B11830691 : Blo 2047435 11830691 := bstep (se 1 (by rfl) ⟨8873018, by rfl⟩ : syracuseStep 11830691 = 17746037) B17746037
theorem B7887127 : Blo 2047435 7887127 := bstep (se 1 (by rfl) ⟨5915345, by rfl⟩ : syracuseStep 7887127 = 11830691) B11830691
theorem B10516169 : Blo 2047435 10516169 := bstep (se 2 (by rfl) ⟨3943563, by rfl⟩ : syracuseStep 10516169 = 7887127) B7887127
theorem B28043117 : Blo 2047435 28043117 := bstep (se 3 (by rfl) ⟨5258084, by rfl⟩ : syracuseStep 28043117 = 10516169) B10516169
theorem B18695411 : Blo 2047435 18695411 := bstep (se 1 (by rfl) ⟨14021558, by rfl⟩ : syracuseStep 18695411 = 28043117) B28043117
theorem B12463607 : Blo 2047435 12463607 := bstep (se 1 (by rfl) ⟨9347705, by rfl⟩ : syracuseStep 12463607 = 18695411) B18695411
theorem B8309071 : Blo 2047435 8309071 := bstep (se 1 (by rfl) ⟨6231803, by rfl⟩ : syracuseStep 8309071 = 12463607) B12463607
theorem B44315045 : Blo 2047435 44315045 := bstep (se 4 (by rfl) ⟨4154535, by rfl⟩ : syracuseStep 44315045 = 8309071) B8309071
theorem B29543363 : Blo 2047435 29543363 := bstep (se 1 (by rfl) ⟨22157522, by rfl⟩ : syracuseStep 29543363 = 44315045) B44315045
theorem B19695575 : Blo 2047435 19695575 := bstep (se 1 (by rfl) ⟨14771681, by rfl⟩ : syracuseStep 19695575 = 29543363) B29543363
theorem B13130383 : Blo 2047435 13130383 := bstep (se 1 (by rfl) ⟨9847787, by rfl⟩ : syracuseStep 13130383 = 19695575) B19695575
theorem B17507177 : Blo 2047435 17507177 := bstep (se 2 (by rfl) ⟨6565191, by rfl⟩ : syracuseStep 17507177 = 13130383) B13130383
theorem B11671451 : Blo 2047435 11671451 := bstep (se 1 (by rfl) ⟨8753588, by rfl⟩ : syracuseStep 11671451 = 17507177) B17507177
theorem B7780967 : Blo 2047435 7780967 := bstep (se 1 (by rfl) ⟨5835725, by rfl⟩ : syracuseStep 7780967 = 11671451) B11671451
theorem B5187311 : Blo 2047435 5187311 := bstep (se 1 (by rfl) ⟨3890483, by rfl⟩ : syracuseStep 5187311 = 7780967) B7780967
theorem B3458207 : Blo 2047435 3458207 := bstep (se 1 (by rfl) ⟨2593655, by rfl⟩ : syracuseStep 3458207 = 5187311) B5187311
theorem B2305471 : Blo 2047435 2305471 := bstep (se 1 (by rfl) ⟨1729103, by rfl⟩ : syracuseStep 2305471 = 3458207) B3458207
theorem B3073961 : Blo 2047435 3073961 := bstep (se 2 (by rfl) ⟨1152735, by rfl⟩ : syracuseStep 3073961 = 2305471) B2305471
theorem B2049307 : Blo 2047435 2049307 := bstep (se 1 (by rfl) ⟨1536980, by rfl⟩ : syracuseStep 2049307 = 3073961) B3073961
theorem B7780981 : Blo 2047435 7780981 := bbase (se 5 (by rfl) ⟨364733, by rfl⟩ : syracuseStep 7780981 = 729467) (by norm_num)
theorem B10374641 : Blo 2047435 10374641 := bstep (se 2 (by rfl) ⟨3890490, by rfl⟩ : syracuseStep 10374641 = 7780981) B7780981
theorem B6916427 : Blo 2047435 6916427 := bstep (se 1 (by rfl) ⟨5187320, by rfl⟩ : syracuseStep 6916427 = 10374641) B10374641
theorem B4610951 : Blo 2047435 4610951 := bstep (se 1 (by rfl) ⟨3458213, by rfl⟩ : syracuseStep 4610951 = 6916427) B6916427
theorem B3073967 : Blo 2047435 3073967 := bstep (se 1 (by rfl) ⟨2305475, by rfl⟩ : syracuseStep 3073967 = 4610951) B4610951
theorem B2049311 : Blo 2047435 2049311 := bstep (se 1 (by rfl) ⟨1536983, by rfl⟩ : syracuseStep 2049311 = 3073967) B3073967
theorem B3073973 : Blo 2047435 3073973 := bbase (se 5 (by rfl) ⟨144092, by rfl⟩ : syracuseStep 3073973 = 288185) (by norm_num)
theorem B2049315 : Blo 2047435 2049315 := bstep (se 1 (by rfl) ⟨1536986, by rfl⟩ : syracuseStep 2049315 = 3073973) B3073973
theorem B5187341 : Blo 2047435 5187341 := bbase (se 3 (by rfl) ⟨972626, by rfl⟩ : syracuseStep 5187341 = 1945253) (by norm_num)
theorem B3458227 : Blo 2047435 3458227 := bstep (se 1 (by rfl) ⟨2593670, by rfl⟩ : syracuseStep 3458227 = 5187341) B5187341
theorem B4610969 : Blo 2047435 4610969 := bstep (se 2 (by rfl) ⟨1729113, by rfl⟩ : syracuseStep 4610969 = 3458227) B3458227
theorem B3073979 : Blo 2047435 3073979 := bstep (se 1 (by rfl) ⟨2305484, by rfl⟩ : syracuseStep 3073979 = 4610969) B4610969
theorem B2049319 : Blo 2047435 2049319 := bstep (se 1 (by rfl) ⟨1536989, by rfl⟩ : syracuseStep 2049319 = 3073979) B3073979
theorem B2305489 : Blo 2047435 2305489 := bbase (se 2 (by rfl) ⟨864558, by rfl⟩ : syracuseStep 2305489 = 1729117) (by norm_num)
theorem B3073985 : Blo 2047435 3073985 := bstep (se 2 (by rfl) ⟨1152744, by rfl⟩ : syracuseStep 3073985 = 2305489) B2305489
theorem B2049323 : Blo 2047435 2049323 := bstep (se 1 (by rfl) ⟨1536992, by rfl⟩ : syracuseStep 2049323 = 3073985) B3073985
theorem B4376837 : Blo 2047435 4376837 := bbase (se 4 (by rfl) ⟨410328, by rfl⟩ : syracuseStep 4376837 = 820657) (by norm_num)
theorem B2917891 : Blo 2047435 2917891 := bstep (se 1 (by rfl) ⟨2188418, by rfl⟩ : syracuseStep 2917891 = 4376837) B4376837
theorem B3890521 : Blo 2047435 3890521 := bstep (se 2 (by rfl) ⟨1458945, by rfl⟩ : syracuseStep 3890521 = 2917891) B2917891
theorem B5187361 : Blo 2047435 5187361 := bstep (se 2 (by rfl) ⟨1945260, by rfl⟩ : syracuseStep 5187361 = 3890521) B3890521
theorem B6916481 : Blo 2047435 6916481 := bstep (se 2 (by rfl) ⟨2593680, by rfl⟩ : syracuseStep 6916481 = 5187361) B5187361
theorem B4610987 : Blo 2047435 4610987 := bstep (se 1 (by rfl) ⟨3458240, by rfl⟩ : syracuseStep 4610987 = 6916481) B6916481
theorem B3073991 : Blo 2047435 3073991 := bstep (se 1 (by rfl) ⟨2305493, by rfl⟩ : syracuseStep 3073991 = 4610987) B4610987
theorem B2049327 : Blo 2047435 2049327 := bstep (se 1 (by rfl) ⟨1536995, by rfl⟩ : syracuseStep 2049327 = 3073991) B3073991
theorem B3073997 : Blo 2047435 3073997 := bbase (se 3 (by rfl) ⟨576374, by rfl⟩ : syracuseStep 3073997 = 1152749) (by norm_num)
theorem B2049331 : Blo 2047435 2049331 := bstep (se 1 (by rfl) ⟨1536998, by rfl⟩ : syracuseStep 2049331 = 3073997) B3073997
theorem B4611005 : Blo 2047435 4611005 := bbase (se 3 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 4611005 = 1729127) (by norm_num)
theorem B3074003 : Blo 2047435 3074003 := bstep (se 1 (by rfl) ⟨2305502, by rfl⟩ : syracuseStep 3074003 = 4611005) B4611005
theorem B2049335 : Blo 2047435 2049335 := bstep (se 1 (by rfl) ⟨1537001, by rfl⟩ : syracuseStep 2049335 = 3074003) B3074003
theorem B3458261 : Blo 2047435 3458261 := bbase (se 7 (by rfl) ⟨40526, by rfl⟩ : syracuseStep 3458261 = 81053) (by norm_num)
theorem B2305507 : Blo 2047435 2305507 := bstep (se 1 (by rfl) ⟨1729130, by rfl⟩ : syracuseStep 2305507 = 3458261) B3458261
theorem B3074009 : Blo 2047435 3074009 := bstep (se 2 (by rfl) ⟨1152753, by rfl⟩ : syracuseStep 3074009 = 2305507) B2305507
theorem B2049339 : Blo 2047435 2049339 := bstep (se 1 (by rfl) ⟨1537004, by rfl⟩ : syracuseStep 2049339 = 3074009) B3074009
theorem B3282653 : Blo 2047435 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B8753741 : Blo 2047435 8753741 := bstep (se 3 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 8753741 = 3282653) B3282653
theorem B5835827 : Blo 2047435 5835827 := bstep (se 1 (by rfl) ⟨4376870, by rfl⟩ : syracuseStep 5835827 = 8753741) B8753741
theorem B15562205 : Blo 2047435 15562205 := bstep (se 3 (by rfl) ⟨2917913, by rfl⟩ : syracuseStep 15562205 = 5835827) B5835827
theorem B10374803 : Blo 2047435 10374803 := bstep (se 1 (by rfl) ⟨7781102, by rfl⟩ : syracuseStep 10374803 = 15562205) B15562205
theorem B6916535 : Blo 2047435 6916535 := bstep (se 1 (by rfl) ⟨5187401, by rfl⟩ : syracuseStep 6916535 = 10374803) B10374803
theorem B4611023 : Blo 2047435 4611023 := bstep (se 1 (by rfl) ⟨3458267, by rfl⟩ : syracuseStep 4611023 = 6916535) B6916535
theorem B3074015 : Blo 2047435 3074015 := bstep (se 1 (by rfl) ⟨2305511, by rfl⟩ : syracuseStep 3074015 = 4611023) B4611023
theorem B2049343 : Blo 2047435 2049343 := bstep (se 1 (by rfl) ⟨1537007, by rfl⟩ : syracuseStep 2049343 = 3074015) B3074015
theorem B3074021 : Blo 2047435 3074021 := bbase (se 4 (by rfl) ⟨288189, by rfl⟩ : syracuseStep 3074021 = 576379) (by norm_num)
theorem B2049347 : Blo 2047435 2049347 := bstep (se 1 (by rfl) ⟨1537010, by rfl⟩ : syracuseStep 2049347 = 3074021) B3074021
theorem B6565333 : Blo 2047435 6565333 := bbase (se 7 (by rfl) ⟨76937, by rfl⟩ : syracuseStep 6565333 = 153875) (by norm_num)
theorem B8753777 : Blo 2047435 8753777 := bstep (se 2 (by rfl) ⟨3282666, by rfl⟩ : syracuseStep 8753777 = 6565333) B6565333
theorem B5835851 : Blo 2047435 5835851 := bstep (se 1 (by rfl) ⟨4376888, by rfl⟩ : syracuseStep 5835851 = 8753777) B8753777
theorem B3890567 : Blo 2047435 3890567 := bstep (se 1 (by rfl) ⟨2917925, by rfl⟩ : syracuseStep 3890567 = 5835851) B5835851
theorem B2593711 : Blo 2047435 2593711 := bstep (se 1 (by rfl) ⟨1945283, by rfl⟩ : syracuseStep 2593711 = 3890567) B3890567
theorem B3458281 : Blo 2047435 3458281 := bstep (se 2 (by rfl) ⟨1296855, by rfl⟩ : syracuseStep 3458281 = 2593711) B2593711
theorem B4611041 : Blo 2047435 4611041 := bstep (se 2 (by rfl) ⟨1729140, by rfl⟩ : syracuseStep 4611041 = 3458281) B3458281
theorem B3074027 : Blo 2047435 3074027 := bstep (se 1 (by rfl) ⟨2305520, by rfl⟩ : syracuseStep 3074027 = 4611041) B4611041
theorem B2049351 : Blo 2047435 2049351 := bstep (se 1 (by rfl) ⟨1537013, by rfl⟩ : syracuseStep 2049351 = 3074027) B3074027
theorem B2305525 : Blo 2047435 2305525 := bbase (se 5 (by rfl) ⟨108071, by rfl⟩ : syracuseStep 2305525 = 216143) (by norm_num)
theorem B3074033 : Blo 2047435 3074033 := bstep (se 2 (by rfl) ⟨1152762, by rfl⟩ : syracuseStep 3074033 = 2305525) B2305525
theorem B2049355 : Blo 2047435 2049355 := bstep (se 1 (by rfl) ⟨1537016, by rfl⟩ : syracuseStep 2049355 = 3074033) B3074033
theorem B2593721 : Blo 2047435 2593721 := bbase (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) (by norm_num)
theorem B6916589 : Blo 2047435 6916589 := bstep (se 3 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 6916589 = 2593721) B2593721
theorem B4611059 : Blo 2047435 4611059 := bstep (se 1 (by rfl) ⟨3458294, by rfl⟩ : syracuseStep 4611059 = 6916589) B6916589
theorem B3074039 : Blo 2047435 3074039 := bstep (se 1 (by rfl) ⟨2305529, by rfl⟩ : syracuseStep 3074039 = 4611059) B4611059
theorem B2049359 : Blo 2047435 2049359 := bstep (se 1 (by rfl) ⟨1537019, by rfl⟩ : syracuseStep 2049359 = 3074039) B3074039
theorem B3074045 : Blo 2047435 3074045 := bbase (se 3 (by rfl) ⟨576383, by rfl⟩ : syracuseStep 3074045 = 1152767) (by norm_num)
theorem B2049363 : Blo 2047435 2049363 := bstep (se 1 (by rfl) ⟨1537022, by rfl⟩ : syracuseStep 2049363 = 3074045) B3074045
theorem B4611077 : Blo 2047435 4611077 := bbase (se 4 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 4611077 = 864577) (by norm_num)
theorem B3074051 : Blo 2047435 3074051 := bstep (se 1 (by rfl) ⟨2305538, by rfl⟩ : syracuseStep 3074051 = 4611077) B4611077
theorem B2049367 : Blo 2047435 2049367 := bstep (se 1 (by rfl) ⟨1537025, by rfl⟩ : syracuseStep 2049367 = 3074051) B3074051
theorem B3890605 : Blo 2047435 3890605 := bbase (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) (by norm_num)
theorem B5187473 : Blo 2047435 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B3458315 : Blo 2047435 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B2305543 : Blo 2047435 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B3074057 : Blo 2047435 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B2049371 : Blo 2047435 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B10374965 : Blo 2047435 10374965 := bbase (se 5 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 10374965 = 972653) (by norm_num)
theorem B6916643 : Blo 2047435 6916643 := bstep (se 1 (by rfl) ⟨5187482, by rfl⟩ : syracuseStep 6916643 = 10374965) B10374965
theorem B4611095 : Blo 2047435 4611095 := bstep (se 1 (by rfl) ⟨3458321, by rfl⟩ : syracuseStep 4611095 = 6916643) B6916643
theorem B3074063 : Blo 2047435 3074063 := bstep (se 1 (by rfl) ⟨2305547, by rfl⟩ : syracuseStep 3074063 = 4611095) B4611095
theorem B2049375 : Blo 2047435 2049375 := bstep (se 1 (by rfl) ⟨1537031, by rfl⟩ : syracuseStep 2049375 = 3074063) B3074063
theorem B3074069 : Blo 2047435 3074069 := bbase (se 6 (by rfl) ⟨72048, by rfl⟩ : syracuseStep 3074069 = 144097) (by norm_num)
theorem B2049379 : Blo 2047435 2049379 := bstep (se 1 (by rfl) ⟨1537034, by rfl⟩ : syracuseStep 2049379 = 3074069) B3074069
theorem B13130869 : Blo 2047435 13130869 := bbase (se 5 (by rfl) ⟨615509, by rfl⟩ : syracuseStep 13130869 = 1231019) (by norm_num)
theorem B17507825 : Blo 2047435 17507825 := bstep (se 2 (by rfl) ⟨6565434, by rfl⟩ : syracuseStep 17507825 = 13130869) B13130869
theorem B11671883 : Blo 2047435 11671883 := bstep (se 1 (by rfl) ⟨8753912, by rfl⟩ : syracuseStep 11671883 = 17507825) B17507825
theorem B7781255 : Blo 2047435 7781255 := bstep (se 1 (by rfl) ⟨5835941, by rfl⟩ : syracuseStep 7781255 = 11671883) B11671883
theorem B5187503 : Blo 2047435 5187503 := bstep (se 1 (by rfl) ⟨3890627, by rfl⟩ : syracuseStep 5187503 = 7781255) B7781255
theorem B3458335 : Blo 2047435 3458335 := bstep (se 1 (by rfl) ⟨2593751, by rfl⟩ : syracuseStep 3458335 = 5187503) B5187503
theorem B4611113 : Blo 2047435 4611113 := bstep (se 2 (by rfl) ⟨1729167, by rfl⟩ : syracuseStep 4611113 = 3458335) B3458335
theorem B3074075 : Blo 2047435 3074075 := bstep (se 1 (by rfl) ⟨2305556, by rfl⟩ : syracuseStep 3074075 = 4611113) B4611113
theorem B2049383 : Blo 2047435 2049383 := bstep (se 1 (by rfl) ⟨1537037, by rfl⟩ : syracuseStep 2049383 = 3074075) B3074075
theorem B2305561 : Blo 2047435 2305561 := bbase (se 2 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 2305561 = 1729171) (by norm_num)
theorem B3074081 : Blo 2047435 3074081 := bstep (se 2 (by rfl) ⟨1152780, by rfl⟩ : syracuseStep 3074081 = 2305561) B2305561
theorem B2049387 : Blo 2047435 2049387 := bstep (se 1 (by rfl) ⟨1537040, by rfl⟩ : syracuseStep 2049387 = 3074081) B3074081
theorem B7781285 : Blo 2047435 7781285 := bbase (se 4 (by rfl) ⟨729495, by rfl⟩ : syracuseStep 7781285 = 1458991) (by norm_num)
theorem B5187523 : Blo 2047435 5187523 := bstep (se 1 (by rfl) ⟨3890642, by rfl⟩ : syracuseStep 5187523 = 7781285) B7781285
theorem B6916697 : Blo 2047435 6916697 := bstep (se 2 (by rfl) ⟨2593761, by rfl⟩ : syracuseStep 6916697 = 5187523) B5187523
theorem B4611131 : Blo 2047435 4611131 := bstep (se 1 (by rfl) ⟨3458348, by rfl⟩ : syracuseStep 4611131 = 6916697) B6916697
theorem B3074087 : Blo 2047435 3074087 := bstep (se 1 (by rfl) ⟨2305565, by rfl⟩ : syracuseStep 3074087 = 4611131) B4611131
theorem B2049391 : Blo 2047435 2049391 := bstep (se 1 (by rfl) ⟨1537043, by rfl⟩ : syracuseStep 2049391 = 3074087) B3074087
theorem B3074093 : Blo 2047435 3074093 := bbase (se 3 (by rfl) ⟨576392, by rfl⟩ : syracuseStep 3074093 = 1152785) (by norm_num)
theorem B2049395 : Blo 2047435 2049395 := bstep (se 1 (by rfl) ⟨1537046, by rfl⟩ : syracuseStep 2049395 = 3074093) B3074093
theorem B4611149 : Blo 2047435 4611149 := bbase (se 3 (by rfl) ⟨864590, by rfl⟩ : syracuseStep 4611149 = 1729181) (by norm_num)
theorem B3074099 : Blo 2047435 3074099 := bstep (se 1 (by rfl) ⟨2305574, by rfl⟩ : syracuseStep 3074099 = 4611149) B4611149
theorem B2049399 : Blo 2047435 2049399 := bstep (se 1 (by rfl) ⟨1537049, by rfl⟩ : syracuseStep 2049399 = 3074099) B3074099
theorem B2593777 : Blo 2047435 2593777 := bbase (se 2 (by rfl) ⟨972666, by rfl⟩ : syracuseStep 2593777 = 1945333) (by norm_num)
theorem B3458369 : Blo 2047435 3458369 := bstep (se 2 (by rfl) ⟨1296888, by rfl⟩ : syracuseStep 3458369 = 2593777) B2593777
theorem B2305579 : Blo 2047435 2305579 := bstep (se 1 (by rfl) ⟨1729184, by rfl⟩ : syracuseStep 2305579 = 3458369) B3458369
theorem B3074105 : Blo 2047435 3074105 := bstep (se 2 (by rfl) ⟨1152789, by rfl⟩ : syracuseStep 3074105 = 2305579) B2305579
theorem B2049403 : Blo 2047435 2049403 := bstep (se 1 (by rfl) ⟨1537052, by rfl⟩ : syracuseStep 2049403 = 3074105) B3074105
theorem B2077369 : Blo 2047435 2077369 := bbase (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) (by norm_num)
theorem B11079301 : Blo 2047435 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B14772401 : Blo 2047435 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B9848267 : Blo 2047435 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B6565511 : Blo 2047435 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B4377007 : Blo 2047435 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B23344037 : Blo 2047435 23344037 := bstep (se 4 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 23344037 = 4377007) B4377007
theorem B15562691 : Blo 2047435 15562691 := bstep (se 1 (by rfl) ⟨11672018, by rfl⟩ : syracuseStep 15562691 = 23344037) B23344037
theorem B10375127 : Blo 2047435 10375127 := bstep (se 1 (by rfl) ⟨7781345, by rfl⟩ : syracuseStep 10375127 = 15562691) B15562691
theorem B6916751 : Blo 2047435 6916751 := bstep (se 1 (by rfl) ⟨5187563, by rfl⟩ : syracuseStep 6916751 = 10375127) B10375127
theorem B4611167 : Blo 2047435 4611167 := bstep (se 1 (by rfl) ⟨3458375, by rfl⟩ : syracuseStep 4611167 = 6916751) B6916751
theorem B3074111 : Blo 2047435 3074111 := bstep (se 1 (by rfl) ⟨2305583, by rfl⟩ : syracuseStep 3074111 = 4611167) B4611167
theorem B2049407 : Blo 2047435 2049407 := bstep (se 1 (by rfl) ⟨1537055, by rfl⟩ : syracuseStep 2049407 = 3074111) B3074111
theorem B3074117 : Blo 2047435 3074117 := bbase (se 4 (by rfl) ⟨288198, by rfl⟩ : syracuseStep 3074117 = 576397) (by norm_num)
theorem B2049411 : Blo 2047435 2049411 := bstep (se 1 (by rfl) ⟨1537058, by rfl⟩ : syracuseStep 2049411 = 3074117) B3074117
theorem B3458389 : Blo 2047435 3458389 := bbase (se 12 (by rfl) ⟨1266, by rfl⟩ : syracuseStep 3458389 = 2533) (by norm_num)
theorem B4611185 : Blo 2047435 4611185 := bstep (se 2 (by rfl) ⟨1729194, by rfl⟩ : syracuseStep 4611185 = 3458389) B3458389
theorem B3074123 : Blo 2047435 3074123 := bstep (se 1 (by rfl) ⟨2305592, by rfl⟩ : syracuseStep 3074123 = 4611185) B4611185
theorem B2049415 : Blo 2047435 2049415 := bstep (se 1 (by rfl) ⟨1537061, by rfl⟩ : syracuseStep 2049415 = 3074123) B3074123
theorem B2305597 : Blo 2047435 2305597 := bbase (se 3 (by rfl) ⟨432299, by rfl⟩ : syracuseStep 2305597 = 864599) (by norm_num)
theorem B3074129 : Blo 2047435 3074129 := bstep (se 2 (by rfl) ⟨1152798, by rfl⟩ : syracuseStep 3074129 = 2305597) B2305597
theorem B2049419 : Blo 2047435 2049419 := bstep (se 1 (by rfl) ⟨1537064, by rfl⟩ : syracuseStep 2049419 = 3074129) B3074129
theorem B6916805 : Blo 2047435 6916805 := bbase (se 4 (by rfl) ⟨648450, by rfl⟩ : syracuseStep 6916805 = 1296901) (by norm_num)
theorem B4611203 : Blo 2047435 4611203 := bstep (se 1 (by rfl) ⟨3458402, by rfl⟩ : syracuseStep 4611203 = 6916805) B6916805
theorem B3074135 : Blo 2047435 3074135 := bstep (se 1 (by rfl) ⟨2305601, by rfl⟩ : syracuseStep 3074135 = 4611203) B4611203
theorem B2049423 : Blo 2047435 2049423 := bstep (se 1 (by rfl) ⟨1537067, by rfl⟩ : syracuseStep 2049423 = 3074135) B3074135
theorem B3074141 : Blo 2047435 3074141 := bbase (se 3 (by rfl) ⟨576401, by rfl⟩ : syracuseStep 3074141 = 1152803) (by norm_num)
theorem B2049427 : Blo 2047435 2049427 := bstep (se 1 (by rfl) ⟨1537070, by rfl⟩ : syracuseStep 2049427 = 3074141) B3074141
theorem B4611221 : Blo 2047435 4611221 := bbase (se 6 (by rfl) ⟨108075, by rfl⟩ : syracuseStep 4611221 = 216151) (by norm_num)
theorem B3074147 : Blo 2047435 3074147 := bstep (se 1 (by rfl) ⟨2305610, by rfl⟩ : syracuseStep 3074147 = 4611221) B4611221
theorem B2049431 : Blo 2047435 2049431 := bstep (se 1 (by rfl) ⟨1537073, by rfl⟩ : syracuseStep 2049431 = 3074147) B3074147
theorem B2918045 : Blo 2047435 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B7781453 : Blo 2047435 7781453 := bstep (se 3 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 7781453 = 2918045) B2918045
theorem B5187635 : Blo 2047435 5187635 := bstep (se 1 (by rfl) ⟨3890726, by rfl⟩ : syracuseStep 5187635 = 7781453) B7781453
theorem B3458423 : Blo 2047435 3458423 := bstep (se 1 (by rfl) ⟨2593817, by rfl⟩ : syracuseStep 3458423 = 5187635) B5187635
theorem B2305615 : Blo 2047435 2305615 := bstep (se 1 (by rfl) ⟨1729211, by rfl⟩ : syracuseStep 2305615 = 3458423) B3458423
theorem B3074153 : Blo 2047435 3074153 := bstep (se 2 (by rfl) ⟨1152807, by rfl⟩ : syracuseStep 3074153 = 2305615) B2305615
theorem B2049435 : Blo 2047435 2049435 := bstep (se 1 (by rfl) ⟨1537076, by rfl⟩ : syracuseStep 2049435 = 3074153) B3074153
theorem C0 (j : ℕ) (h1 : 511858 ≤ j) (h2 : j ≤ 512358) : Blo 2047435 (4 * j + 3) := by
  interval_cases j
  · exact B2047435
  · exact B2047439
  · exact B2047443
  · exact B2047447
  · exact B2047451
  · exact B2047455
  · exact B2047459
  · exact B2047463
  · exact B2047467
  · exact B2047471
  · exact B2047475
  · exact B2047479
  · exact B2047483
  · exact B2047487
  · exact B2047491
  · exact B2047495
  · exact B2047499
  · exact B2047503
  · exact B2047507
  · exact B2047511
  · exact B2047515
  · exact B2047519
  · exact B2047523
  · exact B2047527
  · exact B2047531
  · exact B2047535
  · exact B2047539
  · exact B2047543
  · exact B2047547
  · exact B2047551
  · exact B2047555
  · exact B2047559
  · exact B2047563
  · exact B2047567
  · exact B2047571
  · exact B2047575
  · exact B2047579
  · exact B2047583
  · exact B2047587
  · exact B2047591
  · exact B2047595
  · exact B2047599
  · exact B2047603
  · exact B2047607
  · exact B2047611
  · exact B2047615
  · exact B2047619
  · exact B2047623
  · exact B2047627
  · exact B2047631
  · exact B2047635
  · exact B2047639
  · exact B2047643
  · exact B2047647
  · exact B2047651
  · exact B2047655
  · exact B2047659
  · exact B2047663
  · exact B2047667
  · exact B2047671
  · exact B2047675
  · exact B2047679
  · exact B2047683
  · exact B2047687
  · exact B2047691
  · exact B2047695
  · exact B2047699
  · exact B2047703
  · exact B2047707
  · exact B2047711
  · exact B2047715
  · exact B2047719
  · exact B2047723
  · exact B2047727
  · exact B2047731
  · exact B2047735
  · exact B2047739
  · exact B2047743
  · exact B2047747
  · exact B2047751
  · exact B2047755
  · exact B2047759
  · exact B2047763
  · exact B2047767
  · exact B2047771
  · exact B2047775
  · exact B2047779
  · exact B2047783
  · exact B2047787
  · exact B2047791
  · exact B2047795
  · exact B2047799
  · exact B2047803
  · exact B2047807
  · exact B2047811
  · exact B2047815
  · exact B2047819
  · exact B2047823
  · exact B2047827
  · exact B2047831
  · exact B2047835
  · exact B2047839
  · exact B2047843
  · exact B2047847
  · exact B2047851
  · exact B2047855
  · exact B2047859
  · exact B2047863
  · exact B2047867
  · exact B2047871
  · exact B2047875
  · exact B2047879
  · exact B2047883
  · exact B2047887
  · exact B2047891
  · exact B2047895
  · exact B2047899
  · exact B2047903
  · exact B2047907
  · exact B2047911
  · exact B2047915
  · exact B2047919
  · exact B2047923
  · exact B2047927
  · exact B2047931
  · exact B2047935
  · exact B2047939
  · exact B2047943
  · exact B2047947
  · exact B2047951
  · exact B2047955
  · exact B2047959
  · exact B2047963
  · exact B2047967
  · exact B2047971
  · exact B2047975
  · exact B2047979
  · exact B2047983
  · exact B2047987
  · exact B2047991
  · exact B2047995
  · exact B2047999
  · exact B2048003
  · exact B2048007
  · exact B2048011
  · exact B2048015
  · exact B2048019
  · exact B2048023
  · exact B2048027
  · exact B2048031
  · exact B2048035
  · exact B2048039
  · exact B2048043
  · exact B2048047
  · exact B2048051
  · exact B2048055
  · exact B2048059
  · exact B2048063
  · exact B2048067
  · exact B2048071
  · exact B2048075
  · exact B2048079
  · exact B2048083
  · exact B2048087
  · exact B2048091
  · exact B2048095
  · exact B2048099
  · exact B2048103
  · exact B2048107
  · exact B2048111
  · exact B2048115
  · exact B2048119
  · exact B2048123
  · exact B2048127
  · exact B2048131
  · exact B2048135
  · exact B2048139
  · exact B2048143
  · exact B2048147
  · exact B2048151
  · exact B2048155
  · exact B2048159
  · exact B2048163
  · exact B2048167
  · exact B2048171
  · exact B2048175
  · exact B2048179
  · exact B2048183
  · exact B2048187
  · exact B2048191
  · exact B2048195
  · exact B2048199
  · exact B2048203
  · exact B2048207
  · exact B2048211
  · exact B2048215
  · exact B2048219
  · exact B2048223
  · exact B2048227
  · exact B2048231
  · exact B2048235
  · exact B2048239
  · exact B2048243
  · exact B2048247
  · exact B2048251
  · exact B2048255
  · exact B2048259
  · exact B2048263
  · exact B2048267
  · exact B2048271
  · exact B2048275
  · exact B2048279
  · exact B2048283
  · exact B2048287
  · exact B2048291
  · exact B2048295
  · exact B2048299
  · exact B2048303
  · exact B2048307
  · exact B2048311
  · exact B2048315
  · exact B2048319
  · exact B2048323
  · exact B2048327
  · exact B2048331
  · exact B2048335
  · exact B2048339
  · exact B2048343
  · exact B2048347
  · exact B2048351
  · exact B2048355
  · exact B2048359
  · exact B2048363
  · exact B2048367
  · exact B2048371
  · exact B2048375
  · exact B2048379
  · exact B2048383
  · exact B2048387
  · exact B2048391
  · exact B2048395
  · exact B2048399
  · exact B2048403
  · exact B2048407
  · exact B2048411
  · exact B2048415
  · exact B2048419
  · exact B2048423
  · exact B2048427
  · exact B2048431
  · exact B2048435
  · exact B2048439
  · exact B2048443
  · exact B2048447
  · exact B2048451
  · exact B2048455
  · exact B2048459
  · exact B2048463
  · exact B2048467
  · exact B2048471
  · exact B2048475
  · exact B2048479
  · exact B2048483
  · exact B2048487
  · exact B2048491
  · exact B2048495
  · exact B2048499
  · exact B2048503
  · exact B2048507
  · exact B2048511
  · exact B2048515
  · exact B2048519
  · exact B2048523
  · exact B2048527
  · exact B2048531
  · exact B2048535
  · exact B2048539
  · exact B2048543
  · exact B2048547
  · exact B2048551
  · exact B2048555
  · exact B2048559
  · exact B2048563
  · exact B2048567
  · exact B2048571
  · exact B2048575
  · exact B2048579
  · exact B2048583
  · exact B2048587
  · exact B2048591
  · exact B2048595
  · exact B2048599
  · exact B2048603
  · exact B2048607
  · exact B2048611
  · exact B2048615
  · exact B2048619
  · exact B2048623
  · exact B2048627
  · exact B2048631
  · exact B2048635
  · exact B2048639
  · exact B2048643
  · exact B2048647
  · exact B2048651
  · exact B2048655
  · exact B2048659
  · exact B2048663
  · exact B2048667
  · exact B2048671
  · exact B2048675
  · exact B2048679
  · exact B2048683
  · exact B2048687
  · exact B2048691
  · exact B2048695
  · exact B2048699
  · exact B2048703
  · exact B2048707
  · exact B2048711
  · exact B2048715
  · exact B2048719
  · exact B2048723
  · exact B2048727
  · exact B2048731
  · exact B2048735
  · exact B2048739
  · exact B2048743
  · exact B2048747
  · exact B2048751
  · exact B2048755
  · exact B2048759
  · exact B2048763
  · exact B2048767
  · exact B2048771
  · exact B2048775
  · exact B2048779
  · exact B2048783
  · exact B2048787
  · exact B2048791
  · exact B2048795
  · exact B2048799
  · exact B2048803
  · exact B2048807
  · exact B2048811
  · exact B2048815
  · exact B2048819
  · exact B2048823
  · exact B2048827
  · exact B2048831
  · exact B2048835
  · exact B2048839
  · exact B2048843
  · exact B2048847
  · exact B2048851
  · exact B2048855
  · exact B2048859
  · exact B2048863
  · exact B2048867
  · exact B2048871
  · exact B2048875
  · exact B2048879
  · exact B2048883
  · exact B2048887
  · exact B2048891
  · exact B2048895
  · exact B2048899
  · exact B2048903
  · exact B2048907
  · exact B2048911
  · exact B2048915
  · exact B2048919
  · exact B2048923
  · exact B2048927
  · exact B2048931
  · exact B2048935
  · exact B2048939
  · exact B2048943
  · exact B2048947
  · exact B2048951
  · exact B2048955
  · exact B2048959
  · exact B2048963
  · exact B2048967
  · exact B2048971
  · exact B2048975
  · exact B2048979
  · exact B2048983
  · exact B2048987
  · exact B2048991
  · exact B2048995
  · exact B2048999
  · exact B2049003
  · exact B2049007
  · exact B2049011
  · exact B2049015
  · exact B2049019
  · exact B2049023
  · exact B2049027
  · exact B2049031
  · exact B2049035
  · exact B2049039
  · exact B2049043
  · exact B2049047
  · exact B2049051
  · exact B2049055
  · exact B2049059
  · exact B2049063
  · exact B2049067
  · exact B2049071
  · exact B2049075
  · exact B2049079
  · exact B2049083
  · exact B2049087
  · exact B2049091
  · exact B2049095
  · exact B2049099
  · exact B2049103
  · exact B2049107
  · exact B2049111
  · exact B2049115
  · exact B2049119
  · exact B2049123
  · exact B2049127
  · exact B2049131
  · exact B2049135
  · exact B2049139
  · exact B2049143
  · exact B2049147
  · exact B2049151
  · exact B2049155
  · exact B2049159
  · exact B2049163
  · exact B2049167
  · exact B2049171
  · exact B2049175
  · exact B2049179
  · exact B2049183
  · exact B2049187
  · exact B2049191
  · exact B2049195
  · exact B2049199
  · exact B2049203
  · exact B2049207
  · exact B2049211
  · exact B2049215
  · exact B2049219
  · exact B2049223
  · exact B2049227
  · exact B2049231
  · exact B2049235
  · exact B2049239
  · exact B2049243
  · exact B2049247
  · exact B2049251
  · exact B2049255
  · exact B2049259
  · exact B2049263
  · exact B2049267
  · exact B2049271
  · exact B2049275
  · exact B2049279
  · exact B2049283
  · exact B2049287
  · exact B2049291
  · exact B2049295
  · exact B2049299
  · exact B2049303
  · exact B2049307
  · exact B2049311
  · exact B2049315
  · exact B2049319
  · exact B2049323
  · exact B2049327
  · exact B2049331
  · exact B2049335
  · exact B2049339
  · exact B2049343
  · exact B2049347
  · exact B2049351
  · exact B2049355
  · exact B2049359
  · exact B2049363
  · exact B2049367
  · exact B2049371
  · exact B2049375
  · exact B2049379
  · exact B2049383
  · exact B2049387
  · exact B2049391
  · exact B2049395
  · exact B2049399
  · exact B2049403
  · exact B2049407
  · exact B2049411
  · exact B2049415
  · exact B2049419
  · exact B2049423
  · exact B2049427
  · exact B2049431
  · exact B2049435
theorem solution (m : ℕ) (hlo : 2047435 ≤ m) (hhi : m ≤ 2049435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 511858 ≤ j := by omega
    have hj2 : j ≤ 512358 := by omega
    have hb : Blo 2047435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
