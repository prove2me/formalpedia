-- Prove2me | solution 1 for syracuse_descends_range_2161435_2163435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:38.085722+00:00
-- url     : https://prove2.me/submissions/408e1564-303a-4839-b822-dec77174dc41

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

theorem B31159829 : Blo 2161435 31159829 := bbase (se 6 (by rfl) ⟨730308, by rfl⟩ : syracuseStep 31159829 = 1460617) (by norm_num)
theorem B20773219 : Blo 2161435 20773219 := bstep (se 1 (by rfl) ⟨15579914, by rfl⟩ : syracuseStep 20773219 = 31159829) B31159829
theorem B27697625 : Blo 2161435 27697625 := bstep (se 2 (by rfl) ⟨10386609, by rfl⟩ : syracuseStep 27697625 = 20773219) B20773219
theorem B18465083 : Blo 2161435 18465083 := bstep (se 1 (by rfl) ⟨13848812, by rfl⟩ : syracuseStep 18465083 = 27697625) B27697625
theorem B12310055 : Blo 2161435 12310055 := bstep (se 1 (by rfl) ⟨9232541, by rfl⟩ : syracuseStep 12310055 = 18465083) B18465083
theorem B8206703 : Blo 2161435 8206703 := bstep (se 1 (by rfl) ⟨6155027, by rfl⟩ : syracuseStep 8206703 = 12310055) B12310055
theorem B5471135 : Blo 2161435 5471135 := bstep (se 1 (by rfl) ⟨4103351, by rfl⟩ : syracuseStep 5471135 = 8206703) B8206703
theorem B3647423 : Blo 2161435 3647423 := bstep (se 1 (by rfl) ⟨2735567, by rfl⟩ : syracuseStep 3647423 = 5471135) B5471135
theorem B2431615 : Blo 2161435 2431615 := bstep (se 1 (by rfl) ⟨1823711, by rfl⟩ : syracuseStep 2431615 = 3647423) B3647423
theorem B3242153 : Blo 2161435 3242153 := bstep (se 2 (by rfl) ⟨1215807, by rfl⟩ : syracuseStep 3242153 = 2431615) B2431615
theorem B2161435 : Blo 2161435 2161435 := bstep (se 1 (by rfl) ⟨1621076, by rfl⟩ : syracuseStep 2161435 = 3242153) B3242153
theorem B10386629 : Blo 2161435 10386629 := bbase (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) (by norm_num)
theorem B6924419 : Blo 2161435 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B4616279 : Blo 2161435 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B3077519 : Blo 2161435 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B8206717 : Blo 2161435 8206717 := bstep (se 3 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 8206717 = 3077519) B3077519
theorem B10942289 : Blo 2161435 10942289 := bstep (se 2 (by rfl) ⟨4103358, by rfl⟩ : syracuseStep 10942289 = 8206717) B8206717
theorem B7294859 : Blo 2161435 7294859 := bstep (se 1 (by rfl) ⟨5471144, by rfl⟩ : syracuseStep 7294859 = 10942289) B10942289
theorem B4863239 : Blo 2161435 4863239 := bstep (se 1 (by rfl) ⟨3647429, by rfl⟩ : syracuseStep 4863239 = 7294859) B7294859
theorem B3242159 : Blo 2161435 3242159 := bstep (se 1 (by rfl) ⟨2431619, by rfl⟩ : syracuseStep 3242159 = 4863239) B4863239
theorem B2161439 : Blo 2161435 2161439 := bstep (se 1 (by rfl) ⟨1621079, by rfl⟩ : syracuseStep 2161439 = 3242159) B3242159
theorem B3242165 : Blo 2161435 3242165 := bbase (se 5 (by rfl) ⟨151976, by rfl⟩ : syracuseStep 3242165 = 303953) (by norm_num)
theorem B2161443 : Blo 2161435 2161443 := bstep (se 1 (by rfl) ⟨1621082, by rfl⟩ : syracuseStep 2161443 = 3242165) B3242165
theorem B5471165 : Blo 2161435 5471165 := bbase (se 3 (by rfl) ⟨1025843, by rfl⟩ : syracuseStep 5471165 = 2051687) (by norm_num)
theorem B3647443 : Blo 2161435 3647443 := bstep (se 1 (by rfl) ⟨2735582, by rfl⟩ : syracuseStep 3647443 = 5471165) B5471165
theorem B4863257 : Blo 2161435 4863257 := bstep (se 2 (by rfl) ⟨1823721, by rfl⟩ : syracuseStep 4863257 = 3647443) B3647443
theorem B3242171 : Blo 2161435 3242171 := bstep (se 1 (by rfl) ⟨2431628, by rfl⟩ : syracuseStep 3242171 = 4863257) B4863257
theorem B2161447 : Blo 2161435 2161447 := bstep (se 1 (by rfl) ⟨1621085, by rfl⟩ : syracuseStep 2161447 = 3242171) B3242171
theorem B2431633 : Blo 2161435 2431633 := bbase (se 2 (by rfl) ⟨911862, by rfl⟩ : syracuseStep 2431633 = 1823725) (by norm_num)
theorem B3242177 : Blo 2161435 3242177 := bstep (se 2 (by rfl) ⟨1215816, by rfl⟩ : syracuseStep 3242177 = 2431633) B2431633
theorem B2161451 : Blo 2161435 2161451 := bstep (se 1 (by rfl) ⟨1621088, by rfl⟩ : syracuseStep 2161451 = 3242177) B3242177
theorem B4103389 : Blo 2161435 4103389 := bbase (se 3 (by rfl) ⟨769385, by rfl⟩ : syracuseStep 4103389 = 1538771) (by norm_num)
theorem B5471185 : Blo 2161435 5471185 := bstep (se 2 (by rfl) ⟨2051694, by rfl⟩ : syracuseStep 5471185 = 4103389) B4103389
theorem B7294913 : Blo 2161435 7294913 := bstep (se 2 (by rfl) ⟨2735592, by rfl⟩ : syracuseStep 7294913 = 5471185) B5471185
theorem B4863275 : Blo 2161435 4863275 := bstep (se 1 (by rfl) ⟨3647456, by rfl⟩ : syracuseStep 4863275 = 7294913) B7294913
theorem B3242183 : Blo 2161435 3242183 := bstep (se 1 (by rfl) ⟨2431637, by rfl⟩ : syracuseStep 3242183 = 4863275) B4863275
theorem B2161455 : Blo 2161435 2161455 := bstep (se 1 (by rfl) ⟨1621091, by rfl⟩ : syracuseStep 2161455 = 3242183) B3242183
theorem B3242189 : Blo 2161435 3242189 := bbase (se 3 (by rfl) ⟨607910, by rfl⟩ : syracuseStep 3242189 = 1215821) (by norm_num)
theorem B2161459 : Blo 2161435 2161459 := bstep (se 1 (by rfl) ⟨1621094, by rfl⟩ : syracuseStep 2161459 = 3242189) B3242189
theorem B4863293 : Blo 2161435 4863293 := bbase (se 3 (by rfl) ⟨911867, by rfl⟩ : syracuseStep 4863293 = 1823735) (by norm_num)
theorem B3242195 : Blo 2161435 3242195 := bstep (se 1 (by rfl) ⟨2431646, by rfl⟩ : syracuseStep 3242195 = 4863293) B4863293
theorem B2161463 : Blo 2161435 2161463 := bstep (se 1 (by rfl) ⟨1621097, by rfl⟩ : syracuseStep 2161463 = 3242195) B3242195
theorem B3647477 : Blo 2161435 3647477 := bbase (se 5 (by rfl) ⟨170975, by rfl⟩ : syracuseStep 3647477 = 341951) (by norm_num)
theorem B2431651 : Blo 2161435 2431651 := bstep (se 1 (by rfl) ⟨1823738, by rfl⟩ : syracuseStep 2431651 = 3647477) B3647477
theorem B3242201 : Blo 2161435 3242201 := bstep (se 2 (by rfl) ⟨1215825, by rfl⟩ : syracuseStep 3242201 = 2431651) B2431651
theorem B2161467 : Blo 2161435 2161467 := bstep (se 1 (by rfl) ⟨1621100, by rfl⟩ : syracuseStep 2161467 = 3242201) B3242201
theorem B2772937 : Blo 2161435 2772937 := bbase (se 2 (by rfl) ⟨1039851, by rfl⟩ : syracuseStep 2772937 = 2079703) (by norm_num)
theorem B3697249 : Blo 2161435 3697249 := bstep (se 2 (by rfl) ⟨1386468, by rfl⟩ : syracuseStep 3697249 = 2772937) B2772937
theorem B4929665 : Blo 2161435 4929665 := bstep (se 2 (by rfl) ⟨1848624, by rfl⟩ : syracuseStep 4929665 = 3697249) B3697249
theorem B13145773 : Blo 2161435 13145773 := bstep (se 3 (by rfl) ⟨2464832, by rfl⟩ : syracuseStep 13145773 = 4929665) B4929665
theorem B17527697 : Blo 2161435 17527697 := bstep (se 2 (by rfl) ⟨6572886, by rfl⟩ : syracuseStep 17527697 = 13145773) B13145773
theorem B11685131 : Blo 2161435 11685131 := bstep (se 1 (by rfl) ⟨8763848, by rfl⟩ : syracuseStep 11685131 = 17527697) B17527697
theorem B7790087 : Blo 2161435 7790087 := bstep (se 1 (by rfl) ⟨5842565, by rfl⟩ : syracuseStep 7790087 = 11685131) B11685131
theorem B5193391 : Blo 2161435 5193391 := bstep (se 1 (by rfl) ⟨3895043, by rfl⟩ : syracuseStep 5193391 = 7790087) B7790087
theorem B6924521 : Blo 2161435 6924521 := bstep (se 2 (by rfl) ⟨2596695, by rfl⟩ : syracuseStep 6924521 = 5193391) B5193391
theorem B4616347 : Blo 2161435 4616347 := bstep (se 1 (by rfl) ⟨3462260, by rfl⟩ : syracuseStep 4616347 = 6924521) B6924521
theorem B6155129 : Blo 2161435 6155129 := bstep (se 2 (by rfl) ⟨2308173, by rfl⟩ : syracuseStep 6155129 = 4616347) B4616347
theorem B16413677 : Blo 2161435 16413677 := bstep (se 3 (by rfl) ⟨3077564, by rfl⟩ : syracuseStep 16413677 = 6155129) B6155129
theorem B10942451 : Blo 2161435 10942451 := bstep (se 1 (by rfl) ⟨8206838, by rfl⟩ : syracuseStep 10942451 = 16413677) B16413677
theorem B7294967 : Blo 2161435 7294967 := bstep (se 1 (by rfl) ⟨5471225, by rfl⟩ : syracuseStep 7294967 = 10942451) B10942451
theorem B4863311 : Blo 2161435 4863311 := bstep (se 1 (by rfl) ⟨3647483, by rfl⟩ : syracuseStep 4863311 = 7294967) B7294967
theorem B3242207 : Blo 2161435 3242207 := bstep (se 1 (by rfl) ⟨2431655, by rfl⟩ : syracuseStep 3242207 = 4863311) B4863311
theorem B2161471 : Blo 2161435 2161471 := bstep (se 1 (by rfl) ⟨1621103, by rfl⟩ : syracuseStep 2161471 = 3242207) B3242207
theorem B3242213 : Blo 2161435 3242213 := bbase (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) (by norm_num)
theorem B2161475 : Blo 2161435 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B4616365 : Blo 2161435 4616365 := bbase (se 3 (by rfl) ⟨865568, by rfl⟩ : syracuseStep 4616365 = 1731137) (by norm_num)
theorem B6155153 : Blo 2161435 6155153 := bstep (se 2 (by rfl) ⟨2308182, by rfl⟩ : syracuseStep 6155153 = 4616365) B4616365
theorem B4103435 : Blo 2161435 4103435 := bstep (se 1 (by rfl) ⟨3077576, by rfl⟩ : syracuseStep 4103435 = 6155153) B6155153
theorem B2735623 : Blo 2161435 2735623 := bstep (se 1 (by rfl) ⟨2051717, by rfl⟩ : syracuseStep 2735623 = 4103435) B4103435
theorem B3647497 : Blo 2161435 3647497 := bstep (se 2 (by rfl) ⟨1367811, by rfl⟩ : syracuseStep 3647497 = 2735623) B2735623
theorem B4863329 : Blo 2161435 4863329 := bstep (se 2 (by rfl) ⟨1823748, by rfl⟩ : syracuseStep 4863329 = 3647497) B3647497
theorem B3242219 : Blo 2161435 3242219 := bstep (se 1 (by rfl) ⟨2431664, by rfl⟩ : syracuseStep 3242219 = 4863329) B4863329
theorem B2161479 : Blo 2161435 2161479 := bstep (se 1 (by rfl) ⟨1621109, by rfl⟩ : syracuseStep 2161479 = 3242219) B3242219
theorem B2431669 : Blo 2161435 2431669 := bbase (se 5 (by rfl) ⟨113984, by rfl⟩ : syracuseStep 2431669 = 227969) (by norm_num)
theorem B3242225 : Blo 2161435 3242225 := bstep (se 2 (by rfl) ⟨1215834, by rfl⟩ : syracuseStep 3242225 = 2431669) B2431669
theorem B2161483 : Blo 2161435 2161483 := bstep (se 1 (by rfl) ⟨1621112, by rfl⟩ : syracuseStep 2161483 = 3242225) B3242225
theorem B2735633 : Blo 2161435 2735633 := bbase (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) (by norm_num)
theorem B7295021 : Blo 2161435 7295021 := bstep (se 3 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 7295021 = 2735633) B2735633
theorem B4863347 : Blo 2161435 4863347 := bstep (se 1 (by rfl) ⟨3647510, by rfl⟩ : syracuseStep 4863347 = 7295021) B7295021
theorem B3242231 : Blo 2161435 3242231 := bstep (se 1 (by rfl) ⟨2431673, by rfl⟩ : syracuseStep 3242231 = 4863347) B4863347
theorem B2161487 : Blo 2161435 2161487 := bstep (se 1 (by rfl) ⟨1621115, by rfl⟩ : syracuseStep 2161487 = 3242231) B3242231
theorem B3242237 : Blo 2161435 3242237 := bbase (se 3 (by rfl) ⟨607919, by rfl⟩ : syracuseStep 3242237 = 1215839) (by norm_num)
theorem B2161491 : Blo 2161435 2161491 := bstep (se 1 (by rfl) ⟨1621118, by rfl⟩ : syracuseStep 2161491 = 3242237) B3242237
theorem B4863365 : Blo 2161435 4863365 := bbase (se 4 (by rfl) ⟨455940, by rfl⟩ : syracuseStep 4863365 = 911881) (by norm_num)
theorem B3242243 : Blo 2161435 3242243 := bstep (se 1 (by rfl) ⟨2431682, by rfl⟩ : syracuseStep 3242243 = 4863365) B4863365
theorem B2161495 : Blo 2161435 2161495 := bstep (se 1 (by rfl) ⟨1621121, by rfl⟩ : syracuseStep 2161495 = 3242243) B3242243
theorem B3077605 : Blo 2161435 3077605 := bbase (se 4 (by rfl) ⟨288525, by rfl⟩ : syracuseStep 3077605 = 577051) (by norm_num)
theorem B4103473 : Blo 2161435 4103473 := bstep (se 2 (by rfl) ⟨1538802, by rfl⟩ : syracuseStep 4103473 = 3077605) B3077605
theorem B5471297 : Blo 2161435 5471297 := bstep (se 2 (by rfl) ⟨2051736, by rfl⟩ : syracuseStep 5471297 = 4103473) B4103473
theorem B3647531 : Blo 2161435 3647531 := bstep (se 1 (by rfl) ⟨2735648, by rfl⟩ : syracuseStep 3647531 = 5471297) B5471297
theorem B2431687 : Blo 2161435 2431687 := bstep (se 1 (by rfl) ⟨1823765, by rfl⟩ : syracuseStep 2431687 = 3647531) B3647531
theorem B3242249 : Blo 2161435 3242249 := bstep (se 2 (by rfl) ⟨1215843, by rfl⟩ : syracuseStep 3242249 = 2431687) B2431687
theorem B2161499 : Blo 2161435 2161499 := bstep (se 1 (by rfl) ⟨1621124, by rfl⟩ : syracuseStep 2161499 = 3242249) B3242249
theorem B10942613 : Blo 2161435 10942613 := bbase (se 6 (by rfl) ⟨256467, by rfl⟩ : syracuseStep 10942613 = 512935) (by norm_num)
theorem B7295075 : Blo 2161435 7295075 := bstep (se 1 (by rfl) ⟨5471306, by rfl⟩ : syracuseStep 7295075 = 10942613) B10942613
theorem B4863383 : Blo 2161435 4863383 := bstep (se 1 (by rfl) ⟨3647537, by rfl⟩ : syracuseStep 4863383 = 7295075) B7295075
theorem B3242255 : Blo 2161435 3242255 := bstep (se 1 (by rfl) ⟨2431691, by rfl⟩ : syracuseStep 3242255 = 4863383) B4863383
theorem B2161503 : Blo 2161435 2161503 := bstep (se 1 (by rfl) ⟨1621127, by rfl⟩ : syracuseStep 2161503 = 3242255) B3242255
theorem B3242261 : Blo 2161435 3242261 := bbase (se 6 (by rfl) ⟨75990, by rfl⟩ : syracuseStep 3242261 = 151981) (by norm_num)
theorem B2161507 : Blo 2161435 2161507 := bstep (se 1 (by rfl) ⟨1621130, by rfl⟩ : syracuseStep 2161507 = 3242261) B3242261
theorem B17528021 : Blo 2161435 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B11685347 : Blo 2161435 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B7790231 : Blo 2161435 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B5193487 : Blo 2161435 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B27698597 : Blo 2161435 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B18465731 : Blo 2161435 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B12310487 : Blo 2161435 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B8206991 : Blo 2161435 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B5471327 : Blo 2161435 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B3647551 : Blo 2161435 3647551 := bstep (se 1 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 3647551 = 5471327) B5471327
theorem B4863401 : Blo 2161435 4863401 := bstep (se 2 (by rfl) ⟨1823775, by rfl⟩ : syracuseStep 4863401 = 3647551) B3647551
theorem B3242267 : Blo 2161435 3242267 := bstep (se 1 (by rfl) ⟨2431700, by rfl⟩ : syracuseStep 3242267 = 4863401) B4863401
theorem B2161511 : Blo 2161435 2161511 := bstep (se 1 (by rfl) ⟨1621133, by rfl⟩ : syracuseStep 2161511 = 3242267) B3242267
theorem B2431705 : Blo 2161435 2431705 := bbase (se 2 (by rfl) ⟨911889, by rfl⟩ : syracuseStep 2431705 = 1823779) (by norm_num)
theorem B3242273 : Blo 2161435 3242273 := bstep (se 2 (by rfl) ⟨1215852, by rfl⟩ : syracuseStep 3242273 = 2431705) B2431705
theorem B2161515 : Blo 2161435 2161515 := bstep (se 1 (by rfl) ⟨1621136, by rfl⟩ : syracuseStep 2161515 = 3242273) B3242273
theorem B2308225 : Blo 2161435 2308225 := bbase (se 2 (by rfl) ⟨865584, by rfl⟩ : syracuseStep 2308225 = 1731169) (by norm_num)
theorem B3077633 : Blo 2161435 3077633 := bstep (se 2 (by rfl) ⟨1154112, by rfl⟩ : syracuseStep 3077633 = 2308225) B2308225
theorem B8207021 : Blo 2161435 8207021 := bstep (se 3 (by rfl) ⟨1538816, by rfl⟩ : syracuseStep 8207021 = 3077633) B3077633
theorem B5471347 : Blo 2161435 5471347 := bstep (se 1 (by rfl) ⟨4103510, by rfl⟩ : syracuseStep 5471347 = 8207021) B8207021
theorem B7295129 : Blo 2161435 7295129 := bstep (se 2 (by rfl) ⟨2735673, by rfl⟩ : syracuseStep 7295129 = 5471347) B5471347
theorem B4863419 : Blo 2161435 4863419 := bstep (se 1 (by rfl) ⟨3647564, by rfl⟩ : syracuseStep 4863419 = 7295129) B7295129
theorem B3242279 : Blo 2161435 3242279 := bstep (se 1 (by rfl) ⟨2431709, by rfl⟩ : syracuseStep 3242279 = 4863419) B4863419
theorem B2161519 : Blo 2161435 2161519 := bstep (se 1 (by rfl) ⟨1621139, by rfl⟩ : syracuseStep 2161519 = 3242279) B3242279
theorem B3242285 : Blo 2161435 3242285 := bbase (se 3 (by rfl) ⟨607928, by rfl⟩ : syracuseStep 3242285 = 1215857) (by norm_num)
theorem B2161523 : Blo 2161435 2161523 := bstep (se 1 (by rfl) ⟨1621142, by rfl⟩ : syracuseStep 2161523 = 3242285) B3242285
theorem B4863437 : Blo 2161435 4863437 := bbase (se 3 (by rfl) ⟨911894, by rfl⟩ : syracuseStep 4863437 = 1823789) (by norm_num)
theorem B3242291 : Blo 2161435 3242291 := bstep (se 1 (by rfl) ⟨2431718, by rfl⟩ : syracuseStep 3242291 = 4863437) B4863437
theorem B2161527 : Blo 2161435 2161527 := bstep (se 1 (by rfl) ⟨1621145, by rfl⟩ : syracuseStep 2161527 = 3242291) B3242291
theorem B2735689 : Blo 2161435 2735689 := bbase (se 2 (by rfl) ⟨1025883, by rfl⟩ : syracuseStep 2735689 = 2051767) (by norm_num)
theorem B3647585 : Blo 2161435 3647585 := bstep (se 2 (by rfl) ⟨1367844, by rfl⟩ : syracuseStep 3647585 = 2735689) B2735689
theorem B2431723 : Blo 2161435 2431723 := bstep (se 1 (by rfl) ⟨1823792, by rfl⟩ : syracuseStep 2431723 = 3647585) B3647585
theorem B3242297 : Blo 2161435 3242297 := bstep (se 2 (by rfl) ⟨1215861, by rfl⟩ : syracuseStep 3242297 = 2431723) B2431723
theorem B2161531 : Blo 2161435 2161531 := bstep (se 1 (by rfl) ⟨1621148, by rfl⟩ : syracuseStep 2161531 = 3242297) B3242297
theorem B17528213 : Blo 2161435 17528213 := bbase (se 6 (by rfl) ⟨410817, by rfl⟩ : syracuseStep 17528213 = 821635) (by norm_num)
theorem B11685475 : Blo 2161435 11685475 := bstep (se 1 (by rfl) ⟨8764106, by rfl⟩ : syracuseStep 11685475 = 17528213) B17528213
theorem B15580633 : Blo 2161435 15580633 := bstep (se 2 (by rfl) ⟨5842737, by rfl⟩ : syracuseStep 15580633 = 11685475) B11685475
theorem B20774177 : Blo 2161435 20774177 := bstep (se 2 (by rfl) ⟨7790316, by rfl⟩ : syracuseStep 20774177 = 15580633) B15580633
theorem B13849451 : Blo 2161435 13849451 := bstep (se 1 (by rfl) ⟨10387088, by rfl⟩ : syracuseStep 13849451 = 20774177) B20774177
theorem B9232967 : Blo 2161435 9232967 := bstep (se 1 (by rfl) ⟨6924725, by rfl⟩ : syracuseStep 9232967 = 13849451) B13849451
theorem B24621245 : Blo 2161435 24621245 := bstep (se 3 (by rfl) ⟨4616483, by rfl⟩ : syracuseStep 24621245 = 9232967) B9232967
theorem B16414163 : Blo 2161435 16414163 := bstep (se 1 (by rfl) ⟨12310622, by rfl⟩ : syracuseStep 16414163 = 24621245) B24621245
theorem B10942775 : Blo 2161435 10942775 := bstep (se 1 (by rfl) ⟨8207081, by rfl⟩ : syracuseStep 10942775 = 16414163) B16414163
theorem B7295183 : Blo 2161435 7295183 := bstep (se 1 (by rfl) ⟨5471387, by rfl⟩ : syracuseStep 7295183 = 10942775) B10942775
theorem B4863455 : Blo 2161435 4863455 := bstep (se 1 (by rfl) ⟨3647591, by rfl⟩ : syracuseStep 4863455 = 7295183) B7295183
theorem B3242303 : Blo 2161435 3242303 := bstep (se 1 (by rfl) ⟨2431727, by rfl⟩ : syracuseStep 3242303 = 4863455) B4863455
theorem B2161535 : Blo 2161435 2161535 := bstep (se 1 (by rfl) ⟨1621151, by rfl⟩ : syracuseStep 2161535 = 3242303) B3242303
theorem B3242309 : Blo 2161435 3242309 := bbase (se 4 (by rfl) ⟨303966, by rfl⟩ : syracuseStep 3242309 = 607933) (by norm_num)
theorem B2161539 : Blo 2161435 2161539 := bstep (se 1 (by rfl) ⟨1621154, by rfl⟩ : syracuseStep 2161539 = 3242309) B3242309
theorem B3647605 : Blo 2161435 3647605 := bbase (se 5 (by rfl) ⟨170981, by rfl⟩ : syracuseStep 3647605 = 341963) (by norm_num)
theorem B4863473 : Blo 2161435 4863473 := bstep (se 2 (by rfl) ⟨1823802, by rfl⟩ : syracuseStep 4863473 = 3647605) B3647605
theorem B3242315 : Blo 2161435 3242315 := bstep (se 1 (by rfl) ⟨2431736, by rfl⟩ : syracuseStep 3242315 = 4863473) B4863473
theorem B2161543 : Blo 2161435 2161543 := bstep (se 1 (by rfl) ⟨1621157, by rfl⟩ : syracuseStep 2161543 = 3242315) B3242315
theorem B2431741 : Blo 2161435 2431741 := bbase (se 3 (by rfl) ⟨455951, by rfl⟩ : syracuseStep 2431741 = 911903) (by norm_num)
theorem B3242321 : Blo 2161435 3242321 := bstep (se 2 (by rfl) ⟨1215870, by rfl⟩ : syracuseStep 3242321 = 2431741) B2431741
theorem B2161547 : Blo 2161435 2161547 := bstep (se 1 (by rfl) ⟨1621160, by rfl⟩ : syracuseStep 2161547 = 3242321) B3242321
theorem B7295237 : Blo 2161435 7295237 := bbase (se 4 (by rfl) ⟨683928, by rfl⟩ : syracuseStep 7295237 = 1367857) (by norm_num)
theorem B4863491 : Blo 2161435 4863491 := bstep (se 1 (by rfl) ⟨3647618, by rfl⟩ : syracuseStep 4863491 = 7295237) B7295237
theorem B3242327 : Blo 2161435 3242327 := bstep (se 1 (by rfl) ⟨2431745, by rfl⟩ : syracuseStep 3242327 = 4863491) B4863491
theorem B2161551 : Blo 2161435 2161551 := bstep (se 1 (by rfl) ⟨1621163, by rfl⟩ : syracuseStep 2161551 = 3242327) B3242327
theorem B3242333 : Blo 2161435 3242333 := bbase (se 3 (by rfl) ⟨607937, by rfl⟩ : syracuseStep 3242333 = 1215875) (by norm_num)
theorem B2161555 : Blo 2161435 2161555 := bstep (se 1 (by rfl) ⟨1621166, by rfl⟩ : syracuseStep 2161555 = 3242333) B3242333
theorem B4863509 : Blo 2161435 4863509 := bbase (se 6 (by rfl) ⟨113988, by rfl⟩ : syracuseStep 4863509 = 227977) (by norm_num)
theorem B3242339 : Blo 2161435 3242339 := bstep (se 1 (by rfl) ⟨2431754, by rfl⟩ : syracuseStep 3242339 = 4863509) B4863509
theorem B2161559 : Blo 2161435 2161559 := bstep (se 1 (by rfl) ⟨1621169, by rfl⟩ : syracuseStep 2161559 = 3242339) B3242339
theorem B8207189 : Blo 2161435 8207189 := bbase (se 9 (by rfl) ⟨24044, by rfl⟩ : syracuseStep 8207189 = 48089) (by norm_num)
theorem B5471459 : Blo 2161435 5471459 := bstep (se 1 (by rfl) ⟨4103594, by rfl⟩ : syracuseStep 5471459 = 8207189) B8207189
theorem B3647639 : Blo 2161435 3647639 := bstep (se 1 (by rfl) ⟨2735729, by rfl⟩ : syracuseStep 3647639 = 5471459) B5471459
theorem B2431759 : Blo 2161435 2431759 := bstep (se 1 (by rfl) ⟨1823819, by rfl⟩ : syracuseStep 2431759 = 3647639) B3647639
theorem B3242345 : Blo 2161435 3242345 := bstep (se 2 (by rfl) ⟨1215879, by rfl⟩ : syracuseStep 3242345 = 2431759) B2431759
theorem B2161563 : Blo 2161435 2161563 := bstep (se 1 (by rfl) ⟨1621172, by rfl⟩ : syracuseStep 2161563 = 3242345) B3242345
theorem B12310805 : Blo 2161435 12310805 := bbase (se 6 (by rfl) ⟨288534, by rfl⟩ : syracuseStep 12310805 = 577069) (by norm_num)
theorem B8207203 : Blo 2161435 8207203 := bstep (se 1 (by rfl) ⟨6155402, by rfl⟩ : syracuseStep 8207203 = 12310805) B12310805
theorem B10942937 : Blo 2161435 10942937 := bstep (se 2 (by rfl) ⟨4103601, by rfl⟩ : syracuseStep 10942937 = 8207203) B8207203
theorem B7295291 : Blo 2161435 7295291 := bstep (se 1 (by rfl) ⟨5471468, by rfl⟩ : syracuseStep 7295291 = 10942937) B10942937
theorem B4863527 : Blo 2161435 4863527 := bstep (se 1 (by rfl) ⟨3647645, by rfl⟩ : syracuseStep 4863527 = 7295291) B7295291
theorem B3242351 : Blo 2161435 3242351 := bstep (se 1 (by rfl) ⟨2431763, by rfl⟩ : syracuseStep 3242351 = 4863527) B4863527
theorem B2161567 : Blo 2161435 2161567 := bstep (se 1 (by rfl) ⟨1621175, by rfl⟩ : syracuseStep 2161567 = 3242351) B3242351
theorem B3242357 : Blo 2161435 3242357 := bbase (se 5 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 3242357 = 303971) (by norm_num)
theorem B2161571 : Blo 2161435 2161571 := bstep (se 1 (by rfl) ⟨1621178, by rfl⟩ : syracuseStep 2161571 = 3242357) B3242357
theorem B2308285 : Blo 2161435 2308285 := bbase (se 3 (by rfl) ⟨432803, by rfl⟩ : syracuseStep 2308285 = 865607) (by norm_num)
theorem B3077713 : Blo 2161435 3077713 := bstep (se 2 (by rfl) ⟨1154142, by rfl⟩ : syracuseStep 3077713 = 2308285) B2308285
theorem B4103617 : Blo 2161435 4103617 := bstep (se 2 (by rfl) ⟨1538856, by rfl⟩ : syracuseStep 4103617 = 3077713) B3077713
theorem B5471489 : Blo 2161435 5471489 := bstep (se 2 (by rfl) ⟨2051808, by rfl⟩ : syracuseStep 5471489 = 4103617) B4103617
theorem B3647659 : Blo 2161435 3647659 := bstep (se 1 (by rfl) ⟨2735744, by rfl⟩ : syracuseStep 3647659 = 5471489) B5471489
theorem B4863545 : Blo 2161435 4863545 := bstep (se 2 (by rfl) ⟨1823829, by rfl⟩ : syracuseStep 4863545 = 3647659) B3647659
theorem B3242363 : Blo 2161435 3242363 := bstep (se 1 (by rfl) ⟨2431772, by rfl⟩ : syracuseStep 3242363 = 4863545) B4863545
theorem B2161575 : Blo 2161435 2161575 := bstep (se 1 (by rfl) ⟨1621181, by rfl⟩ : syracuseStep 2161575 = 3242363) B3242363
theorem B2431777 : Blo 2161435 2431777 := bbase (se 2 (by rfl) ⟨911916, by rfl⟩ : syracuseStep 2431777 = 1823833) (by norm_num)
theorem B3242369 : Blo 2161435 3242369 := bstep (se 2 (by rfl) ⟨1215888, by rfl⟩ : syracuseStep 3242369 = 2431777) B2431777
theorem B2161579 : Blo 2161435 2161579 := bstep (se 1 (by rfl) ⟨1621184, by rfl⟩ : syracuseStep 2161579 = 3242369) B3242369
theorem B5471509 : Blo 2161435 5471509 := bbase (se 6 (by rfl) ⟨128238, by rfl⟩ : syracuseStep 5471509 = 256477) (by norm_num)
theorem B7295345 : Blo 2161435 7295345 := bstep (se 2 (by rfl) ⟨2735754, by rfl⟩ : syracuseStep 7295345 = 5471509) B5471509
theorem B4863563 : Blo 2161435 4863563 := bstep (se 1 (by rfl) ⟨3647672, by rfl⟩ : syracuseStep 4863563 = 7295345) B7295345
theorem B3242375 : Blo 2161435 3242375 := bstep (se 1 (by rfl) ⟨2431781, by rfl⟩ : syracuseStep 3242375 = 4863563) B4863563
theorem B2161583 : Blo 2161435 2161583 := bstep (se 1 (by rfl) ⟨1621187, by rfl⟩ : syracuseStep 2161583 = 3242375) B3242375
theorem B3242381 : Blo 2161435 3242381 := bbase (se 3 (by rfl) ⟨607946, by rfl⟩ : syracuseStep 3242381 = 1215893) (by norm_num)
theorem B2161587 : Blo 2161435 2161587 := bstep (se 1 (by rfl) ⟨1621190, by rfl⟩ : syracuseStep 2161587 = 3242381) B3242381
theorem B4863581 : Blo 2161435 4863581 := bbase (se 3 (by rfl) ⟨911921, by rfl⟩ : syracuseStep 4863581 = 1823843) (by norm_num)
theorem B3242387 : Blo 2161435 3242387 := bstep (se 1 (by rfl) ⟨2431790, by rfl⟩ : syracuseStep 3242387 = 4863581) B4863581
theorem B2161591 : Blo 2161435 2161591 := bstep (se 1 (by rfl) ⟨1621193, by rfl⟩ : syracuseStep 2161591 = 3242387) B3242387
theorem B3647693 : Blo 2161435 3647693 := bbase (se 3 (by rfl) ⟨683942, by rfl⟩ : syracuseStep 3647693 = 1367885) (by norm_num)
theorem B2431795 : Blo 2161435 2431795 := bstep (se 1 (by rfl) ⟨1823846, by rfl⟩ : syracuseStep 2431795 = 3647693) B3647693
theorem B3242393 : Blo 2161435 3242393 := bstep (se 2 (by rfl) ⟨1215897, by rfl⟩ : syracuseStep 3242393 = 2431795) B2431795
theorem B2161595 : Blo 2161435 2161595 := bstep (se 1 (by rfl) ⟨1621196, by rfl⟩ : syracuseStep 2161595 = 3242393) B3242393
theorem B2596849 : Blo 2161435 2596849 := bbase (se 2 (by rfl) ⟨973818, by rfl⟩ : syracuseStep 2596849 = 1947637) (by norm_num)
theorem B13849861 : Blo 2161435 13849861 := bstep (se 4 (by rfl) ⟨1298424, by rfl⟩ : syracuseStep 13849861 = 2596849) B2596849
theorem B18466481 : Blo 2161435 18466481 := bstep (se 2 (by rfl) ⟨6924930, by rfl⟩ : syracuseStep 18466481 = 13849861) B13849861
theorem B12310987 : Blo 2161435 12310987 := bstep (se 1 (by rfl) ⟨9233240, by rfl⟩ : syracuseStep 12310987 = 18466481) B18466481
theorem B16414649 : Blo 2161435 16414649 := bstep (se 2 (by rfl) ⟨6155493, by rfl⟩ : syracuseStep 16414649 = 12310987) B12310987
theorem B10943099 : Blo 2161435 10943099 := bstep (se 1 (by rfl) ⟨8207324, by rfl⟩ : syracuseStep 10943099 = 16414649) B16414649
theorem B7295399 : Blo 2161435 7295399 := bstep (se 1 (by rfl) ⟨5471549, by rfl⟩ : syracuseStep 7295399 = 10943099) B10943099
theorem B4863599 : Blo 2161435 4863599 := bstep (se 1 (by rfl) ⟨3647699, by rfl⟩ : syracuseStep 4863599 = 7295399) B7295399
theorem B3242399 : Blo 2161435 3242399 := bstep (se 1 (by rfl) ⟨2431799, by rfl⟩ : syracuseStep 3242399 = 4863599) B4863599
theorem B2161599 : Blo 2161435 2161599 := bstep (se 1 (by rfl) ⟨1621199, by rfl⟩ : syracuseStep 2161599 = 3242399) B3242399
theorem B3242405 : Blo 2161435 3242405 := bbase (se 4 (by rfl) ⟨303975, by rfl⟩ : syracuseStep 3242405 = 607951) (by norm_num)
theorem B2161603 : Blo 2161435 2161603 := bstep (se 1 (by rfl) ⟨1621202, by rfl⟩ : syracuseStep 2161603 = 3242405) B3242405
theorem B2735785 : Blo 2161435 2735785 := bbase (se 2 (by rfl) ⟨1025919, by rfl⟩ : syracuseStep 2735785 = 2051839) (by norm_num)
theorem B3647713 : Blo 2161435 3647713 := bstep (se 2 (by rfl) ⟨1367892, by rfl⟩ : syracuseStep 3647713 = 2735785) B2735785
theorem B4863617 : Blo 2161435 4863617 := bstep (se 2 (by rfl) ⟨1823856, by rfl⟩ : syracuseStep 4863617 = 3647713) B3647713
theorem B3242411 : Blo 2161435 3242411 := bstep (se 1 (by rfl) ⟨2431808, by rfl⟩ : syracuseStep 3242411 = 4863617) B4863617
theorem B2161607 : Blo 2161435 2161607 := bstep (se 1 (by rfl) ⟨1621205, by rfl⟩ : syracuseStep 2161607 = 3242411) B3242411
theorem B2431813 : Blo 2161435 2431813 := bbase (se 4 (by rfl) ⟨227982, by rfl⟩ : syracuseStep 2431813 = 455965) (by norm_num)
theorem B3242417 : Blo 2161435 3242417 := bstep (se 2 (by rfl) ⟨1215906, by rfl⟩ : syracuseStep 3242417 = 2431813) B2431813
theorem B2161611 : Blo 2161435 2161611 := bstep (se 1 (by rfl) ⟨1621208, by rfl⟩ : syracuseStep 2161611 = 3242417) B3242417
theorem B4103693 : Blo 2161435 4103693 := bbase (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) (by norm_num)
theorem B2735795 : Blo 2161435 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B7295453 : Blo 2161435 7295453 := bstep (se 3 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 7295453 = 2735795) B2735795
theorem B4863635 : Blo 2161435 4863635 := bstep (se 1 (by rfl) ⟨3647726, by rfl⟩ : syracuseStep 4863635 = 7295453) B7295453
theorem B3242423 : Blo 2161435 3242423 := bstep (se 1 (by rfl) ⟨2431817, by rfl⟩ : syracuseStep 3242423 = 4863635) B4863635
theorem B2161615 : Blo 2161435 2161615 := bstep (se 1 (by rfl) ⟨1621211, by rfl⟩ : syracuseStep 2161615 = 3242423) B3242423
theorem B3242429 : Blo 2161435 3242429 := bbase (se 3 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 3242429 = 1215911) (by norm_num)
theorem B2161619 : Blo 2161435 2161619 := bstep (se 1 (by rfl) ⟨1621214, by rfl⟩ : syracuseStep 2161619 = 3242429) B3242429
theorem B4863653 : Blo 2161435 4863653 := bbase (se 4 (by rfl) ⟨455967, by rfl⟩ : syracuseStep 4863653 = 911935) (by norm_num)
theorem B3242435 : Blo 2161435 3242435 := bstep (se 1 (by rfl) ⟨2431826, by rfl⟩ : syracuseStep 3242435 = 4863653) B4863653
theorem B2161623 : Blo 2161435 2161623 := bstep (se 1 (by rfl) ⟨1621217, by rfl⟩ : syracuseStep 2161623 = 3242435) B3242435
theorem B5471621 : Blo 2161435 5471621 := bbase (se 4 (by rfl) ⟨512964, by rfl⟩ : syracuseStep 5471621 = 1025929) (by norm_num)
theorem B3647747 : Blo 2161435 3647747 := bstep (se 1 (by rfl) ⟨2735810, by rfl⟩ : syracuseStep 3647747 = 5471621) B5471621
theorem B2431831 : Blo 2161435 2431831 := bstep (se 1 (by rfl) ⟨1823873, by rfl⟩ : syracuseStep 2431831 = 3647747) B3647747
theorem B3242441 : Blo 2161435 3242441 := bstep (se 2 (by rfl) ⟨1215915, by rfl⟩ : syracuseStep 3242441 = 2431831) B2431831
theorem B2161627 : Blo 2161435 2161627 := bstep (se 1 (by rfl) ⟨1621220, by rfl⟩ : syracuseStep 2161627 = 3242441) B3242441
theorem B3462517 : Blo 2161435 3462517 := bbase (se 5 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 3462517 = 324611) (by norm_num)
theorem B4616689 : Blo 2161435 4616689 := bstep (se 2 (by rfl) ⟨1731258, by rfl⟩ : syracuseStep 4616689 = 3462517) B3462517
theorem B6155585 : Blo 2161435 6155585 := bstep (se 2 (by rfl) ⟨2308344, by rfl⟩ : syracuseStep 6155585 = 4616689) B4616689
theorem B4103723 : Blo 2161435 4103723 := bstep (se 1 (by rfl) ⟨3077792, by rfl⟩ : syracuseStep 4103723 = 6155585) B6155585
theorem B10943261 : Blo 2161435 10943261 := bstep (se 3 (by rfl) ⟨2051861, by rfl⟩ : syracuseStep 10943261 = 4103723) B4103723
theorem B7295507 : Blo 2161435 7295507 := bstep (se 1 (by rfl) ⟨5471630, by rfl⟩ : syracuseStep 7295507 = 10943261) B10943261
theorem B4863671 : Blo 2161435 4863671 := bstep (se 1 (by rfl) ⟨3647753, by rfl⟩ : syracuseStep 4863671 = 7295507) B7295507
theorem B3242447 : Blo 2161435 3242447 := bstep (se 1 (by rfl) ⟨2431835, by rfl⟩ : syracuseStep 3242447 = 4863671) B4863671
theorem B2161631 : Blo 2161435 2161631 := bstep (se 1 (by rfl) ⟨1621223, by rfl⟩ : syracuseStep 2161631 = 3242447) B3242447
theorem B3242453 : Blo 2161435 3242453 := bbase (se 7 (by rfl) ⟨37997, by rfl⟩ : syracuseStep 3242453 = 75995) (by norm_num)
theorem B2161635 : Blo 2161435 2161635 := bstep (se 1 (by rfl) ⟨1621226, by rfl⟩ : syracuseStep 2161635 = 3242453) B3242453
theorem B8207477 : Blo 2161435 8207477 := bbase (se 5 (by rfl) ⟨384725, by rfl⟩ : syracuseStep 8207477 = 769451) (by norm_num)
theorem B5471651 : Blo 2161435 5471651 := bstep (se 1 (by rfl) ⟨4103738, by rfl⟩ : syracuseStep 5471651 = 8207477) B8207477
theorem B3647767 : Blo 2161435 3647767 := bstep (se 1 (by rfl) ⟨2735825, by rfl⟩ : syracuseStep 3647767 = 5471651) B5471651
theorem B4863689 : Blo 2161435 4863689 := bstep (se 2 (by rfl) ⟨1823883, by rfl⟩ : syracuseStep 4863689 = 3647767) B3647767
theorem B3242459 : Blo 2161435 3242459 := bstep (se 1 (by rfl) ⟨2431844, by rfl⟩ : syracuseStep 3242459 = 4863689) B4863689
theorem B2161639 : Blo 2161435 2161639 := bstep (se 1 (by rfl) ⟨1621229, by rfl⟩ : syracuseStep 2161639 = 3242459) B3242459
theorem B2431849 : Blo 2161435 2431849 := bbase (se 2 (by rfl) ⟨911943, by rfl⟩ : syracuseStep 2431849 = 1823887) (by norm_num)
theorem B3242465 : Blo 2161435 3242465 := bstep (se 2 (by rfl) ⟨1215924, by rfl⟩ : syracuseStep 3242465 = 2431849) B2431849
theorem B2161643 : Blo 2161435 2161643 := bstep (se 1 (by rfl) ⟨1621232, by rfl⟩ : syracuseStep 2161643 = 3242465) B3242465
theorem B2191141 : Blo 2161435 2191141 := bbase (se 4 (by rfl) ⟨205419, by rfl⟩ : syracuseStep 2191141 = 410839) (by norm_num)
theorem B2921521 : Blo 2161435 2921521 := bstep (se 2 (by rfl) ⟨1095570, by rfl⟩ : syracuseStep 2921521 = 2191141) B2191141
theorem B3895361 : Blo 2161435 3895361 := bstep (se 2 (by rfl) ⟨1460760, by rfl⟩ : syracuseStep 3895361 = 2921521) B2921521
theorem B2596907 : Blo 2161435 2596907 := bstep (se 1 (by rfl) ⟨1947680, by rfl⟩ : syracuseStep 2596907 = 3895361) B3895361
theorem B6925085 : Blo 2161435 6925085 := bstep (se 3 (by rfl) ⟨1298453, by rfl⟩ : syracuseStep 6925085 = 2596907) B2596907
theorem B4616723 : Blo 2161435 4616723 := bstep (se 1 (by rfl) ⟨3462542, by rfl⟩ : syracuseStep 4616723 = 6925085) B6925085
theorem B12311261 : Blo 2161435 12311261 := bstep (se 3 (by rfl) ⟨2308361, by rfl⟩ : syracuseStep 12311261 = 4616723) B4616723
theorem B8207507 : Blo 2161435 8207507 := bstep (se 1 (by rfl) ⟨6155630, by rfl⟩ : syracuseStep 8207507 = 12311261) B12311261
theorem B5471671 : Blo 2161435 5471671 := bstep (se 1 (by rfl) ⟨4103753, by rfl⟩ : syracuseStep 5471671 = 8207507) B8207507
theorem B7295561 : Blo 2161435 7295561 := bstep (se 2 (by rfl) ⟨2735835, by rfl⟩ : syracuseStep 7295561 = 5471671) B5471671
theorem B4863707 : Blo 2161435 4863707 := bstep (se 1 (by rfl) ⟨3647780, by rfl⟩ : syracuseStep 4863707 = 7295561) B7295561
theorem B3242471 : Blo 2161435 3242471 := bstep (se 1 (by rfl) ⟨2431853, by rfl⟩ : syracuseStep 3242471 = 4863707) B4863707
theorem B2161647 : Blo 2161435 2161647 := bstep (se 1 (by rfl) ⟨1621235, by rfl⟩ : syracuseStep 2161647 = 3242471) B3242471
theorem B3242477 : Blo 2161435 3242477 := bbase (se 3 (by rfl) ⟨607964, by rfl⟩ : syracuseStep 3242477 = 1215929) (by norm_num)
theorem B2161651 : Blo 2161435 2161651 := bstep (se 1 (by rfl) ⟨1621238, by rfl⟩ : syracuseStep 2161651 = 3242477) B3242477
theorem B4863725 : Blo 2161435 4863725 := bbase (se 3 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 4863725 = 1823897) (by norm_num)
theorem B3242483 : Blo 2161435 3242483 := bstep (se 1 (by rfl) ⟨2431862, by rfl⟩ : syracuseStep 3242483 = 4863725) B4863725
theorem B2161655 : Blo 2161435 2161655 := bstep (se 1 (by rfl) ⟨1621241, by rfl⟩ : syracuseStep 2161655 = 3242483) B3242483
theorem B5193845 : Blo 2161435 5193845 := bbase (se 5 (by rfl) ⟨243461, by rfl⟩ : syracuseStep 5193845 = 486923) (by norm_num)
theorem B3462563 : Blo 2161435 3462563 := bstep (se 1 (by rfl) ⟨2596922, by rfl⟩ : syracuseStep 3462563 = 5193845) B5193845
theorem B2308375 : Blo 2161435 2308375 := bstep (se 1 (by rfl) ⟨1731281, by rfl⟩ : syracuseStep 2308375 = 3462563) B3462563
theorem B3077833 : Blo 2161435 3077833 := bstep (se 2 (by rfl) ⟨1154187, by rfl⟩ : syracuseStep 3077833 = 2308375) B2308375
theorem B4103777 : Blo 2161435 4103777 := bstep (se 2 (by rfl) ⟨1538916, by rfl⟩ : syracuseStep 4103777 = 3077833) B3077833
theorem B2735851 : Blo 2161435 2735851 := bstep (se 1 (by rfl) ⟨2051888, by rfl⟩ : syracuseStep 2735851 = 4103777) B4103777
theorem B3647801 : Blo 2161435 3647801 := bstep (se 2 (by rfl) ⟨1367925, by rfl⟩ : syracuseStep 3647801 = 2735851) B2735851
theorem B2431867 : Blo 2161435 2431867 := bstep (se 1 (by rfl) ⟨1823900, by rfl⟩ : syracuseStep 2431867 = 3647801) B3647801
theorem B3242489 : Blo 2161435 3242489 := bstep (se 2 (by rfl) ⟨1215933, by rfl⟩ : syracuseStep 3242489 = 2431867) B2431867
theorem B2161659 : Blo 2161435 2161659 := bstep (se 1 (by rfl) ⟨1621244, by rfl⟩ : syracuseStep 2161659 = 3242489) B3242489
theorem B2632357 : Blo 2161435 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B14039237 : Blo 2161435 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B9359491 : Blo 2161435 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B12479321 : Blo 2161435 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B8319547 : Blo 2161435 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B11092729 : Blo 2161435 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B14790305 : Blo 2161435 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B9860203 : Blo 2161435 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B13146937 : Blo 2161435 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B70116997 : Blo 2161435 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B93489329 : Blo 2161435 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B62326219 : Blo 2161435 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B83101625 : Blo 2161435 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B55401083 : Blo 2161435 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B36934055 : Blo 2161435 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B24622703 : Blo 2161435 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B16415135 : Blo 2161435 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B10943423 : Blo 2161435 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B7295615 : Blo 2161435 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B4863743 : Blo 2161435 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B3242495 : Blo 2161435 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B2161663 : Blo 2161435 2161663 := bstep (se 1 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 2161663 = 3242495) B3242495
theorem B3242501 : Blo 2161435 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B2161667 : Blo 2161435 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B3647821 : Blo 2161435 3647821 := bbase (se 3 (by rfl) ⟨683966, by rfl⟩ : syracuseStep 3647821 = 1367933) (by norm_num)
theorem B4863761 : Blo 2161435 4863761 := bstep (se 2 (by rfl) ⟨1823910, by rfl⟩ : syracuseStep 4863761 = 3647821) B3647821
theorem B3242507 : Blo 2161435 3242507 := bstep (se 1 (by rfl) ⟨2431880, by rfl⟩ : syracuseStep 3242507 = 4863761) B4863761
theorem B2161671 : Blo 2161435 2161671 := bstep (se 1 (by rfl) ⟨1621253, by rfl⟩ : syracuseStep 2161671 = 3242507) B3242507
theorem B2431885 : Blo 2161435 2431885 := bbase (se 3 (by rfl) ⟨455978, by rfl⟩ : syracuseStep 2431885 = 911957) (by norm_num)
theorem B3242513 : Blo 2161435 3242513 := bstep (se 2 (by rfl) ⟨1215942, by rfl⟩ : syracuseStep 3242513 = 2431885) B2431885
theorem B2161675 : Blo 2161435 2161675 := bstep (se 1 (by rfl) ⟨1621256, by rfl⟩ : syracuseStep 2161675 = 3242513) B3242513
theorem B7295669 : Blo 2161435 7295669 := bbase (se 5 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 7295669 = 683969) (by norm_num)
theorem B4863779 : Blo 2161435 4863779 := bstep (se 1 (by rfl) ⟨3647834, by rfl⟩ : syracuseStep 4863779 = 7295669) B7295669
theorem B3242519 : Blo 2161435 3242519 := bstep (se 1 (by rfl) ⟨2431889, by rfl⟩ : syracuseStep 3242519 = 4863779) B4863779
theorem B2161679 : Blo 2161435 2161679 := bstep (se 1 (by rfl) ⟨1621259, by rfl⟩ : syracuseStep 2161679 = 3242519) B3242519
theorem B3242525 : Blo 2161435 3242525 := bbase (se 3 (by rfl) ⟨607973, by rfl⟩ : syracuseStep 3242525 = 1215947) (by norm_num)
theorem B2161683 : Blo 2161435 2161683 := bstep (se 1 (by rfl) ⟨1621262, by rfl⟩ : syracuseStep 2161683 = 3242525) B3242525
theorem B4863797 : Blo 2161435 4863797 := bbase (se 5 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 4863797 = 455981) (by norm_num)
theorem B3242531 : Blo 2161435 3242531 := bstep (se 1 (by rfl) ⟨2431898, by rfl⟩ : syracuseStep 3242531 = 4863797) B4863797
theorem B2161687 : Blo 2161435 2161687 := bstep (se 1 (by rfl) ⟨1621265, by rfl⟩ : syracuseStep 2161687 = 3242531) B3242531
theorem B13850453 : Blo 2161435 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B9233635 : Blo 2161435 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B12311513 : Blo 2161435 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B8207675 : Blo 2161435 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B5471783 : Blo 2161435 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B3647855 : Blo 2161435 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B2431903 : Blo 2161435 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B3242537 : Blo 2161435 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B2161691 : Blo 2161435 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B8764757 : Blo 2161435 8764757 := bbase (se 11 (by rfl) ⟨6419, by rfl⟩ : syracuseStep 8764757 = 12839) (by norm_num)
theorem B5843171 : Blo 2161435 5843171 := bstep (se 1 (by rfl) ⟨4382378, by rfl⟩ : syracuseStep 5843171 = 8764757) B8764757
theorem B3895447 : Blo 2161435 3895447 := bstep (se 1 (by rfl) ⟨2921585, by rfl⟩ : syracuseStep 3895447 = 5843171) B5843171
theorem B5193929 : Blo 2161435 5193929 := bstep (se 2 (by rfl) ⟨1947723, by rfl⟩ : syracuseStep 5193929 = 3895447) B3895447
theorem B13850477 : Blo 2161435 13850477 := bstep (se 3 (by rfl) ⟨2596964, by rfl⟩ : syracuseStep 13850477 = 5193929) B5193929
theorem B9233651 : Blo 2161435 9233651 := bstep (se 1 (by rfl) ⟨6925238, by rfl⟩ : syracuseStep 9233651 = 13850477) B13850477
theorem B6155767 : Blo 2161435 6155767 := bstep (se 1 (by rfl) ⟨4616825, by rfl⟩ : syracuseStep 6155767 = 9233651) B9233651
theorem B8207689 : Blo 2161435 8207689 := bstep (se 2 (by rfl) ⟨3077883, by rfl⟩ : syracuseStep 8207689 = 6155767) B6155767
theorem B10943585 : Blo 2161435 10943585 := bstep (se 2 (by rfl) ⟨4103844, by rfl⟩ : syracuseStep 10943585 = 8207689) B8207689
theorem B7295723 : Blo 2161435 7295723 := bstep (se 1 (by rfl) ⟨5471792, by rfl⟩ : syracuseStep 7295723 = 10943585) B10943585
theorem B4863815 : Blo 2161435 4863815 := bstep (se 1 (by rfl) ⟨3647861, by rfl⟩ : syracuseStep 4863815 = 7295723) B7295723
theorem B3242543 : Blo 2161435 3242543 := bstep (se 1 (by rfl) ⟨2431907, by rfl⟩ : syracuseStep 3242543 = 4863815) B4863815
theorem B2161695 : Blo 2161435 2161695 := bstep (se 1 (by rfl) ⟨1621271, by rfl⟩ : syracuseStep 2161695 = 3242543) B3242543
theorem B3242549 : Blo 2161435 3242549 := bbase (se 5 (by rfl) ⟨151994, by rfl⟩ : syracuseStep 3242549 = 303989) (by norm_num)
theorem B2161699 : Blo 2161435 2161699 := bstep (se 1 (by rfl) ⟨1621274, by rfl⟩ : syracuseStep 2161699 = 3242549) B3242549
theorem B5471813 : Blo 2161435 5471813 := bbase (se 4 (by rfl) ⟨512982, by rfl⟩ : syracuseStep 5471813 = 1025965) (by norm_num)
theorem B3647875 : Blo 2161435 3647875 := bstep (se 1 (by rfl) ⟨2735906, by rfl⟩ : syracuseStep 3647875 = 5471813) B5471813
theorem B4863833 : Blo 2161435 4863833 := bstep (se 2 (by rfl) ⟨1823937, by rfl⟩ : syracuseStep 4863833 = 3647875) B3647875
theorem B3242555 : Blo 2161435 3242555 := bstep (se 1 (by rfl) ⟨2431916, by rfl⟩ : syracuseStep 3242555 = 4863833) B4863833
theorem B2161703 : Blo 2161435 2161703 := bstep (se 1 (by rfl) ⟨1621277, by rfl⟩ : syracuseStep 2161703 = 3242555) B3242555
theorem B2431921 : Blo 2161435 2431921 := bbase (se 2 (by rfl) ⟨911970, by rfl⟩ : syracuseStep 2431921 = 1823941) (by norm_num)
theorem B3242561 : Blo 2161435 3242561 := bstep (se 2 (by rfl) ⟨1215960, by rfl⟩ : syracuseStep 3242561 = 2431921) B2431921
theorem B2161707 : Blo 2161435 2161707 := bstep (se 1 (by rfl) ⟨1621280, by rfl⟩ : syracuseStep 2161707 = 3242561) B3242561
theorem B6155813 : Blo 2161435 6155813 := bbase (se 4 (by rfl) ⟨577107, by rfl⟩ : syracuseStep 6155813 = 1154215) (by norm_num)
theorem B4103875 : Blo 2161435 4103875 := bstep (se 1 (by rfl) ⟨3077906, by rfl⟩ : syracuseStep 4103875 = 6155813) B6155813
theorem B5471833 : Blo 2161435 5471833 := bstep (se 2 (by rfl) ⟨2051937, by rfl⟩ : syracuseStep 5471833 = 4103875) B4103875
theorem B7295777 : Blo 2161435 7295777 := bstep (se 2 (by rfl) ⟨2735916, by rfl⟩ : syracuseStep 7295777 = 5471833) B5471833
theorem B4863851 : Blo 2161435 4863851 := bstep (se 1 (by rfl) ⟨3647888, by rfl⟩ : syracuseStep 4863851 = 7295777) B7295777
theorem B3242567 : Blo 2161435 3242567 := bstep (se 1 (by rfl) ⟨2431925, by rfl⟩ : syracuseStep 3242567 = 4863851) B4863851
theorem B2161711 : Blo 2161435 2161711 := bstep (se 1 (by rfl) ⟨1621283, by rfl⟩ : syracuseStep 2161711 = 3242567) B3242567
theorem B3242573 : Blo 2161435 3242573 := bbase (se 3 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 3242573 = 1215965) (by norm_num)
theorem B2161715 : Blo 2161435 2161715 := bstep (se 1 (by rfl) ⟨1621286, by rfl⟩ : syracuseStep 2161715 = 3242573) B3242573
theorem B4863869 : Blo 2161435 4863869 := bbase (se 3 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 4863869 = 1823951) (by norm_num)
theorem B3242579 : Blo 2161435 3242579 := bstep (se 1 (by rfl) ⟨2431934, by rfl⟩ : syracuseStep 3242579 = 4863869) B4863869
theorem B2161719 : Blo 2161435 2161719 := bstep (se 1 (by rfl) ⟨1621289, by rfl⟩ : syracuseStep 2161719 = 3242579) B3242579
theorem B3647909 : Blo 2161435 3647909 := bbase (se 4 (by rfl) ⟨341991, by rfl⟩ : syracuseStep 3647909 = 683983) (by norm_num)
theorem B2431939 : Blo 2161435 2431939 := bstep (se 1 (by rfl) ⟨1823954, by rfl⟩ : syracuseStep 2431939 = 3647909) B3647909
theorem B3242585 : Blo 2161435 3242585 := bstep (se 2 (by rfl) ⟨1215969, by rfl⟩ : syracuseStep 3242585 = 2431939) B2431939
theorem B2161723 : Blo 2161435 2161723 := bstep (se 1 (by rfl) ⟨1621292, by rfl⟩ : syracuseStep 2161723 = 3242585) B3242585
theorem B11686517 : Blo 2161435 11686517 := bbase (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) (by norm_num)
theorem B7791011 : Blo 2161435 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B5194007 : Blo 2161435 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B3462671 : Blo 2161435 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B2308447 : Blo 2161435 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B3077929 : Blo 2161435 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B16415621 : Blo 2161435 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B10943747 : Blo 2161435 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B7295831 : Blo 2161435 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B4863887 : Blo 2161435 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B3242591 : Blo 2161435 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B2161727 : Blo 2161435 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B3242597 : Blo 2161435 3242597 := bbase (se 4 (by rfl) ⟨303993, by rfl⟩ : syracuseStep 3242597 = 607987) (by norm_num)
theorem B2161731 : Blo 2161435 2161731 := bstep (se 1 (by rfl) ⟨1621298, by rfl⟩ : syracuseStep 2161731 = 3242597) B3242597
theorem B3077941 : Blo 2161435 3077941 := bbase (se 5 (by rfl) ⟨144278, by rfl⟩ : syracuseStep 3077941 = 288557) (by norm_num)
theorem B4103921 : Blo 2161435 4103921 := bstep (se 2 (by rfl) ⟨1538970, by rfl⟩ : syracuseStep 4103921 = 3077941) B3077941
theorem B2735947 : Blo 2161435 2735947 := bstep (se 1 (by rfl) ⟨2051960, by rfl⟩ : syracuseStep 2735947 = 4103921) B4103921
theorem B3647929 : Blo 2161435 3647929 := bstep (se 2 (by rfl) ⟨1367973, by rfl⟩ : syracuseStep 3647929 = 2735947) B2735947
theorem B4863905 : Blo 2161435 4863905 := bstep (se 2 (by rfl) ⟨1823964, by rfl⟩ : syracuseStep 4863905 = 3647929) B3647929
theorem B3242603 : Blo 2161435 3242603 := bstep (se 1 (by rfl) ⟨2431952, by rfl⟩ : syracuseStep 3242603 = 4863905) B4863905
theorem B2161735 : Blo 2161435 2161735 := bstep (se 1 (by rfl) ⟨1621301, by rfl⟩ : syracuseStep 2161735 = 3242603) B3242603
theorem B2431957 : Blo 2161435 2431957 := bbase (se 7 (by rfl) ⟨28499, by rfl⟩ : syracuseStep 2431957 = 56999) (by norm_num)
theorem B3242609 : Blo 2161435 3242609 := bstep (se 2 (by rfl) ⟨1215978, by rfl⟩ : syracuseStep 3242609 = 2431957) B2431957
theorem B2161739 : Blo 2161435 2161739 := bstep (se 1 (by rfl) ⟨1621304, by rfl⟩ : syracuseStep 2161739 = 3242609) B3242609
theorem B2735957 : Blo 2161435 2735957 := bbase (se 9 (by rfl) ⟨8015, by rfl⟩ : syracuseStep 2735957 = 16031) (by norm_num)
theorem B7295885 : Blo 2161435 7295885 := bstep (se 3 (by rfl) ⟨1367978, by rfl⟩ : syracuseStep 7295885 = 2735957) B2735957
theorem B4863923 : Blo 2161435 4863923 := bstep (se 1 (by rfl) ⟨3647942, by rfl⟩ : syracuseStep 4863923 = 7295885) B7295885
theorem B3242615 : Blo 2161435 3242615 := bstep (se 1 (by rfl) ⟨2431961, by rfl⟩ : syracuseStep 3242615 = 4863923) B4863923
theorem B2161743 : Blo 2161435 2161743 := bstep (se 1 (by rfl) ⟨1621307, by rfl⟩ : syracuseStep 2161743 = 3242615) B3242615
theorem B3242621 : Blo 2161435 3242621 := bbase (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) (by norm_num)
theorem B2161747 : Blo 2161435 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B4863941 : Blo 2161435 4863941 := bbase (se 4 (by rfl) ⟨455994, by rfl⟩ : syracuseStep 4863941 = 911989) (by norm_num)
theorem B3242627 : Blo 2161435 3242627 := bstep (se 1 (by rfl) ⟨2431970, by rfl⟩ : syracuseStep 3242627 = 4863941) B4863941
theorem B2161751 : Blo 2161435 2161751 := bstep (se 1 (by rfl) ⟨1621313, by rfl⟩ : syracuseStep 2161751 = 3242627) B3242627
theorem B9233909 : Blo 2161435 9233909 := bbase (se 5 (by rfl) ⟨432839, by rfl⟩ : syracuseStep 9233909 = 865679) (by norm_num)
theorem B6155939 : Blo 2161435 6155939 := bstep (se 1 (by rfl) ⟨4616954, by rfl⟩ : syracuseStep 6155939 = 9233909) B9233909
theorem B4103959 : Blo 2161435 4103959 := bstep (se 1 (by rfl) ⟨3077969, by rfl⟩ : syracuseStep 4103959 = 6155939) B6155939
theorem B5471945 : Blo 2161435 5471945 := bstep (se 2 (by rfl) ⟨2051979, by rfl⟩ : syracuseStep 5471945 = 4103959) B4103959
theorem B3647963 : Blo 2161435 3647963 := bstep (se 1 (by rfl) ⟨2735972, by rfl⟩ : syracuseStep 3647963 = 5471945) B5471945
theorem B2431975 : Blo 2161435 2431975 := bstep (se 1 (by rfl) ⟨1823981, by rfl⟩ : syracuseStep 2431975 = 3647963) B3647963
theorem B3242633 : Blo 2161435 3242633 := bstep (se 2 (by rfl) ⟨1215987, by rfl⟩ : syracuseStep 3242633 = 2431975) B2431975
theorem B2161755 : Blo 2161435 2161755 := bstep (se 1 (by rfl) ⟨1621316, by rfl⟩ : syracuseStep 2161755 = 3242633) B3242633
theorem B10943909 : Blo 2161435 10943909 := bbase (se 4 (by rfl) ⟨1025991, by rfl⟩ : syracuseStep 10943909 = 2051983) (by norm_num)
theorem B7295939 : Blo 2161435 7295939 := bstep (se 1 (by rfl) ⟨5471954, by rfl⟩ : syracuseStep 7295939 = 10943909) B10943909
theorem B4863959 : Blo 2161435 4863959 := bstep (se 1 (by rfl) ⟨3647969, by rfl⟩ : syracuseStep 4863959 = 7295939) B7295939
theorem B3242639 : Blo 2161435 3242639 := bstep (se 1 (by rfl) ⟨2431979, by rfl⟩ : syracuseStep 3242639 = 4863959) B4863959
theorem B2161759 : Blo 2161435 2161759 := bstep (se 1 (by rfl) ⟨1621319, by rfl⟩ : syracuseStep 2161759 = 3242639) B3242639
theorem B3242645 : Blo 2161435 3242645 := bbase (se 6 (by rfl) ⟨75999, by rfl⟩ : syracuseStep 3242645 = 151999) (by norm_num)
theorem B2161763 : Blo 2161435 2161763 := bstep (se 1 (by rfl) ⟨1621322, by rfl⟩ : syracuseStep 2161763 = 3242645) B3242645
theorem B23373461 : Blo 2161435 23373461 := bbase (se 6 (by rfl) ⟨547815, by rfl⟩ : syracuseStep 23373461 = 1095631) (by norm_num)
theorem B15582307 : Blo 2161435 15582307 := bstep (se 1 (by rfl) ⟨11686730, by rfl⟩ : syracuseStep 15582307 = 23373461) B23373461
theorem B20776409 : Blo 2161435 20776409 := bstep (se 2 (by rfl) ⟨7791153, by rfl⟩ : syracuseStep 20776409 = 15582307) B15582307
theorem B13850939 : Blo 2161435 13850939 := bstep (se 1 (by rfl) ⟨10388204, by rfl⟩ : syracuseStep 13850939 = 20776409) B20776409
theorem B9233959 : Blo 2161435 9233959 := bstep (se 1 (by rfl) ⟨6925469, by rfl⟩ : syracuseStep 9233959 = 13850939) B13850939
theorem B12311945 : Blo 2161435 12311945 := bstep (se 2 (by rfl) ⟨4616979, by rfl⟩ : syracuseStep 12311945 = 9233959) B9233959
theorem B8207963 : Blo 2161435 8207963 := bstep (se 1 (by rfl) ⟨6155972, by rfl⟩ : syracuseStep 8207963 = 12311945) B12311945
theorem B5471975 : Blo 2161435 5471975 := bstep (se 1 (by rfl) ⟨4103981, by rfl⟩ : syracuseStep 5471975 = 8207963) B8207963
theorem B3647983 : Blo 2161435 3647983 := bstep (se 1 (by rfl) ⟨2735987, by rfl⟩ : syracuseStep 3647983 = 5471975) B5471975
theorem B4863977 : Blo 2161435 4863977 := bstep (se 2 (by rfl) ⟨1823991, by rfl⟩ : syracuseStep 4863977 = 3647983) B3647983
theorem B3242651 : Blo 2161435 3242651 := bstep (se 1 (by rfl) ⟨2431988, by rfl⟩ : syracuseStep 3242651 = 4863977) B4863977
theorem B2161767 : Blo 2161435 2161767 := bstep (se 1 (by rfl) ⟨1621325, by rfl⟩ : syracuseStep 2161767 = 3242651) B3242651
theorem B2431993 : Blo 2161435 2431993 := bbase (se 2 (by rfl) ⟨911997, by rfl⟩ : syracuseStep 2431993 = 1823995) (by norm_num)
theorem B3242657 : Blo 2161435 3242657 := bstep (se 2 (by rfl) ⟨1215996, by rfl⟩ : syracuseStep 3242657 = 2431993) B2431993
theorem B2161771 : Blo 2161435 2161771 := bstep (se 1 (by rfl) ⟨1621328, by rfl⟩ : syracuseStep 2161771 = 3242657) B3242657
theorem B4997629 : Blo 2161435 4997629 := bbase (se 3 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 4997629 = 1874111) (by norm_num)
theorem B6663505 : Blo 2161435 6663505 := bstep (se 2 (by rfl) ⟨2498814, by rfl⟩ : syracuseStep 6663505 = 4997629) B4997629
theorem B8884673 : Blo 2161435 8884673 := bstep (se 2 (by rfl) ⟨3331752, by rfl⟩ : syracuseStep 8884673 = 6663505) B6663505
theorem B5923115 : Blo 2161435 5923115 := bstep (se 1 (by rfl) ⟨4442336, by rfl⟩ : syracuseStep 5923115 = 8884673) B8884673
theorem B3948743 : Blo 2161435 3948743 := bstep (se 1 (by rfl) ⟨2961557, by rfl⟩ : syracuseStep 3948743 = 5923115) B5923115
theorem B2632495 : Blo 2161435 2632495 := bstep (se 1 (by rfl) ⟨1974371, by rfl⟩ : syracuseStep 2632495 = 3948743) B3948743
theorem B3509993 : Blo 2161435 3509993 := bstep (se 2 (by rfl) ⟨1316247, by rfl⟩ : syracuseStep 3509993 = 2632495) B2632495
theorem B9359981 : Blo 2161435 9359981 := bstep (se 3 (by rfl) ⟨1754996, by rfl⟩ : syracuseStep 9359981 = 3509993) B3509993
theorem B6239987 : Blo 2161435 6239987 := bstep (se 1 (by rfl) ⟨4679990, by rfl⟩ : syracuseStep 6239987 = 9359981) B9359981
theorem B4159991 : Blo 2161435 4159991 := bstep (se 1 (by rfl) ⟨3119993, by rfl⟩ : syracuseStep 4159991 = 6239987) B6239987
theorem B2773327 : Blo 2161435 2773327 := bstep (se 1 (by rfl) ⟨2079995, by rfl⟩ : syracuseStep 2773327 = 4159991) B4159991
theorem B3697769 : Blo 2161435 3697769 := bstep (se 2 (by rfl) ⟨1386663, by rfl⟩ : syracuseStep 3697769 = 2773327) B2773327
theorem B9860717 : Blo 2161435 9860717 := bstep (se 3 (by rfl) ⟨1848884, by rfl⟩ : syracuseStep 9860717 = 3697769) B3697769
theorem B6573811 : Blo 2161435 6573811 := bstep (se 1 (by rfl) ⟨4930358, by rfl⟩ : syracuseStep 6573811 = 9860717) B9860717
theorem B8765081 : Blo 2161435 8765081 := bstep (se 2 (by rfl) ⟨3286905, by rfl⟩ : syracuseStep 8765081 = 6573811) B6573811
theorem B5843387 : Blo 2161435 5843387 := bstep (se 1 (by rfl) ⟨4382540, by rfl⟩ : syracuseStep 5843387 = 8765081) B8765081
theorem B15582365 : Blo 2161435 15582365 := bstep (se 3 (by rfl) ⟨2921693, by rfl⟩ : syracuseStep 15582365 = 5843387) B5843387
theorem B10388243 : Blo 2161435 10388243 := bstep (se 1 (by rfl) ⟨7791182, by rfl⟩ : syracuseStep 10388243 = 15582365) B15582365
theorem B6925495 : Blo 2161435 6925495 := bstep (se 1 (by rfl) ⟨5194121, by rfl⟩ : syracuseStep 6925495 = 10388243) B10388243
theorem B9233993 : Blo 2161435 9233993 := bstep (se 2 (by rfl) ⟨3462747, by rfl⟩ : syracuseStep 9233993 = 6925495) B6925495
theorem B6155995 : Blo 2161435 6155995 := bstep (se 1 (by rfl) ⟨4616996, by rfl⟩ : syracuseStep 6155995 = 9233993) B9233993
theorem B8207993 : Blo 2161435 8207993 := bstep (se 2 (by rfl) ⟨3077997, by rfl⟩ : syracuseStep 8207993 = 6155995) B6155995
theorem B5471995 : Blo 2161435 5471995 := bstep (se 1 (by rfl) ⟨4103996, by rfl⟩ : syracuseStep 5471995 = 8207993) B8207993
theorem B7295993 : Blo 2161435 7295993 := bstep (se 2 (by rfl) ⟨2735997, by rfl⟩ : syracuseStep 7295993 = 5471995) B5471995
theorem B4863995 : Blo 2161435 4863995 := bstep (se 1 (by rfl) ⟨3647996, by rfl⟩ : syracuseStep 4863995 = 7295993) B7295993
theorem B3242663 : Blo 2161435 3242663 := bstep (se 1 (by rfl) ⟨2431997, by rfl⟩ : syracuseStep 3242663 = 4863995) B4863995
theorem B2161775 : Blo 2161435 2161775 := bstep (se 1 (by rfl) ⟨1621331, by rfl⟩ : syracuseStep 2161775 = 3242663) B3242663
theorem B3242669 : Blo 2161435 3242669 := bbase (se 3 (by rfl) ⟨608000, by rfl⟩ : syracuseStep 3242669 = 1216001) (by norm_num)
theorem B2161779 : Blo 2161435 2161779 := bstep (se 1 (by rfl) ⟨1621334, by rfl⟩ : syracuseStep 2161779 = 3242669) B3242669
theorem B4864013 : Blo 2161435 4864013 := bbase (se 3 (by rfl) ⟨912002, by rfl⟩ : syracuseStep 4864013 = 1824005) (by norm_num)
theorem B3242675 : Blo 2161435 3242675 := bstep (se 1 (by rfl) ⟨2432006, by rfl⟩ : syracuseStep 3242675 = 4864013) B4864013
theorem B2161783 : Blo 2161435 2161783 := bstep (se 1 (by rfl) ⟨1621337, by rfl⟩ : syracuseStep 2161783 = 3242675) B3242675
theorem B2736013 : Blo 2161435 2736013 := bbase (se 3 (by rfl) ⟨513002, by rfl⟩ : syracuseStep 2736013 = 1026005) (by norm_num)
theorem B3648017 : Blo 2161435 3648017 := bstep (se 2 (by rfl) ⟨1368006, by rfl⟩ : syracuseStep 3648017 = 2736013) B2736013
theorem B2432011 : Blo 2161435 2432011 := bstep (se 1 (by rfl) ⟨1824008, by rfl⟩ : syracuseStep 2432011 = 3648017) B3648017
theorem B3242681 : Blo 2161435 3242681 := bstep (se 2 (by rfl) ⟨1216005, by rfl⟩ : syracuseStep 3242681 = 2432011) B2432011
theorem B2161787 : Blo 2161435 2161787 := bstep (se 1 (by rfl) ⟨1621340, by rfl⟩ : syracuseStep 2161787 = 3242681) B3242681
theorem B2465197 : Blo 2161435 2465197 := bbase (se 3 (by rfl) ⟨462224, by rfl⟩ : syracuseStep 2465197 = 924449) (by norm_num)
theorem B13147717 : Blo 2161435 13147717 := bstep (se 4 (by rfl) ⟨1232598, by rfl⟩ : syracuseStep 13147717 = 2465197) B2465197
theorem B17530289 : Blo 2161435 17530289 := bstep (se 2 (by rfl) ⟨6573858, by rfl⟩ : syracuseStep 17530289 = 13147717) B13147717
theorem B11686859 : Blo 2161435 11686859 := bstep (se 1 (by rfl) ⟨8765144, by rfl⟩ : syracuseStep 11686859 = 17530289) B17530289
theorem B7791239 : Blo 2161435 7791239 := bstep (se 1 (by rfl) ⟨5843429, by rfl⟩ : syracuseStep 7791239 = 11686859) B11686859
theorem B20776637 : Blo 2161435 20776637 := bstep (se 3 (by rfl) ⟨3895619, by rfl⟩ : syracuseStep 20776637 = 7791239) B7791239
theorem B13851091 : Blo 2161435 13851091 := bstep (se 1 (by rfl) ⟨10388318, by rfl⟩ : syracuseStep 13851091 = 20776637) B20776637
theorem B18468121 : Blo 2161435 18468121 := bstep (se 2 (by rfl) ⟨6925545, by rfl⟩ : syracuseStep 18468121 = 13851091) B13851091
theorem B24624161 : Blo 2161435 24624161 := bstep (se 2 (by rfl) ⟨9234060, by rfl⟩ : syracuseStep 24624161 = 18468121) B18468121
theorem B16416107 : Blo 2161435 16416107 := bstep (se 1 (by rfl) ⟨12312080, by rfl⟩ : syracuseStep 16416107 = 24624161) B24624161
theorem B10944071 : Blo 2161435 10944071 := bstep (se 1 (by rfl) ⟨8208053, by rfl⟩ : syracuseStep 10944071 = 16416107) B16416107
theorem B7296047 : Blo 2161435 7296047 := bstep (se 1 (by rfl) ⟨5472035, by rfl⟩ : syracuseStep 7296047 = 10944071) B10944071
theorem B4864031 : Blo 2161435 4864031 := bstep (se 1 (by rfl) ⟨3648023, by rfl⟩ : syracuseStep 4864031 = 7296047) B7296047
theorem B3242687 : Blo 2161435 3242687 := bstep (se 1 (by rfl) ⟨2432015, by rfl⟩ : syracuseStep 3242687 = 4864031) B4864031
theorem B2161791 : Blo 2161435 2161791 := bstep (se 1 (by rfl) ⟨1621343, by rfl⟩ : syracuseStep 2161791 = 3242687) B3242687
theorem B3242693 : Blo 2161435 3242693 := bbase (se 4 (by rfl) ⟨304002, by rfl⟩ : syracuseStep 3242693 = 608005) (by norm_num)
theorem B2161795 : Blo 2161435 2161795 := bstep (se 1 (by rfl) ⟨1621346, by rfl⟩ : syracuseStep 2161795 = 3242693) B3242693
theorem B3648037 : Blo 2161435 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B4864049 : Blo 2161435 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B3242699 : Blo 2161435 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B2161799 : Blo 2161435 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B2432029 : Blo 2161435 2432029 := bbase (se 3 (by rfl) ⟨456005, by rfl⟩ : syracuseStep 2432029 = 912011) (by norm_num)
theorem B3242705 : Blo 2161435 3242705 := bstep (se 2 (by rfl) ⟨1216014, by rfl⟩ : syracuseStep 3242705 = 2432029) B2432029
theorem B2161803 : Blo 2161435 2161803 := bstep (se 1 (by rfl) ⟨1621352, by rfl⟩ : syracuseStep 2161803 = 3242705) B3242705
theorem B7296101 : Blo 2161435 7296101 := bbase (se 4 (by rfl) ⟨684009, by rfl⟩ : syracuseStep 7296101 = 1368019) (by norm_num)
theorem B4864067 : Blo 2161435 4864067 := bstep (se 1 (by rfl) ⟨3648050, by rfl⟩ : syracuseStep 4864067 = 7296101) B7296101
theorem B3242711 : Blo 2161435 3242711 := bstep (se 1 (by rfl) ⟨2432033, by rfl⟩ : syracuseStep 3242711 = 4864067) B4864067
theorem B2161807 : Blo 2161435 2161807 := bstep (se 1 (by rfl) ⟨1621355, by rfl⟩ : syracuseStep 2161807 = 3242711) B3242711
theorem B3242717 : Blo 2161435 3242717 := bbase (se 3 (by rfl) ⟨608009, by rfl⟩ : syracuseStep 3242717 = 1216019) (by norm_num)
theorem B2161811 : Blo 2161435 2161811 := bstep (se 1 (by rfl) ⟨1621358, by rfl⟩ : syracuseStep 2161811 = 3242717) B3242717
theorem B4864085 : Blo 2161435 4864085 := bbase (se 8 (by rfl) ⟨28500, by rfl⟩ : syracuseStep 4864085 = 57001) (by norm_num)
theorem B3242723 : Blo 2161435 3242723 := bstep (se 1 (by rfl) ⟨2432042, by rfl⟩ : syracuseStep 3242723 = 4864085) B4864085
theorem B2161815 : Blo 2161435 2161815 := bstep (se 1 (by rfl) ⟨1621361, by rfl⟩ : syracuseStep 2161815 = 3242723) B3242723
theorem B6925637 : Blo 2161435 6925637 := bbase (se 4 (by rfl) ⟨649278, by rfl⟩ : syracuseStep 6925637 = 1298557) (by norm_num)
theorem B4617091 : Blo 2161435 4617091 := bstep (se 1 (by rfl) ⟨3462818, by rfl⟩ : syracuseStep 4617091 = 6925637) B6925637
theorem B6156121 : Blo 2161435 6156121 := bstep (se 2 (by rfl) ⟨2308545, by rfl⟩ : syracuseStep 6156121 = 4617091) B4617091
theorem B8208161 : Blo 2161435 8208161 := bstep (se 2 (by rfl) ⟨3078060, by rfl⟩ : syracuseStep 8208161 = 6156121) B6156121
theorem B5472107 : Blo 2161435 5472107 := bstep (se 1 (by rfl) ⟨4104080, by rfl⟩ : syracuseStep 5472107 = 8208161) B8208161
theorem B3648071 : Blo 2161435 3648071 := bstep (se 1 (by rfl) ⟨2736053, by rfl⟩ : syracuseStep 3648071 = 5472107) B5472107
theorem B2432047 : Blo 2161435 2432047 := bstep (se 1 (by rfl) ⟨1824035, by rfl⟩ : syracuseStep 2432047 = 3648071) B3648071
theorem B3242729 : Blo 2161435 3242729 := bstep (se 2 (by rfl) ⟨1216023, by rfl⟩ : syracuseStep 3242729 = 2432047) B2432047
theorem B2161819 : Blo 2161435 2161819 := bstep (se 1 (by rfl) ⟨1621364, by rfl⟩ : syracuseStep 2161819 = 3242729) B3242729
theorem B15582709 : Blo 2161435 15582709 := bbase (se 5 (by rfl) ⟨730439, by rfl⟩ : syracuseStep 15582709 = 1460879) (by norm_num)
theorem B20776945 : Blo 2161435 20776945 := bstep (se 2 (by rfl) ⟨7791354, by rfl⟩ : syracuseStep 20776945 = 15582709) B15582709
theorem B27702593 : Blo 2161435 27702593 := bstep (se 2 (by rfl) ⟨10388472, by rfl⟩ : syracuseStep 27702593 = 20776945) B20776945
theorem B18468395 : Blo 2161435 18468395 := bstep (se 1 (by rfl) ⟨13851296, by rfl⟩ : syracuseStep 18468395 = 27702593) B27702593
theorem B12312263 : Blo 2161435 12312263 := bstep (se 1 (by rfl) ⟨9234197, by rfl⟩ : syracuseStep 12312263 = 18468395) B18468395
theorem B8208175 : Blo 2161435 8208175 := bstep (se 1 (by rfl) ⟨6156131, by rfl⟩ : syracuseStep 8208175 = 12312263) B12312263
theorem B10944233 : Blo 2161435 10944233 := bstep (se 2 (by rfl) ⟨4104087, by rfl⟩ : syracuseStep 10944233 = 8208175) B8208175
theorem B7296155 : Blo 2161435 7296155 := bstep (se 1 (by rfl) ⟨5472116, by rfl⟩ : syracuseStep 7296155 = 10944233) B10944233
theorem B4864103 : Blo 2161435 4864103 := bstep (se 1 (by rfl) ⟨3648077, by rfl⟩ : syracuseStep 4864103 = 7296155) B7296155
theorem B3242735 : Blo 2161435 3242735 := bstep (se 1 (by rfl) ⟨2432051, by rfl⟩ : syracuseStep 3242735 = 4864103) B4864103
theorem B2161823 : Blo 2161435 2161823 := bstep (se 1 (by rfl) ⟨1621367, by rfl⟩ : syracuseStep 2161823 = 3242735) B3242735
theorem B3242741 : Blo 2161435 3242741 := bbase (se 5 (by rfl) ⟨152003, by rfl⟩ : syracuseStep 3242741 = 304007) (by norm_num)
theorem B2161827 : Blo 2161435 2161827 := bstep (se 1 (by rfl) ⟨1621370, by rfl⟩ : syracuseStep 2161827 = 3242741) B3242741
theorem B6240149 : Blo 2161435 6240149 := bbase (se 6 (by rfl) ⟨146253, by rfl⟩ : syracuseStep 6240149 = 292507) (by norm_num)
theorem B4160099 : Blo 2161435 4160099 := bstep (se 1 (by rfl) ⟨3120074, by rfl⟩ : syracuseStep 4160099 = 6240149) B6240149
theorem B11093597 : Blo 2161435 11093597 := bstep (se 3 (by rfl) ⟨2080049, by rfl⟩ : syracuseStep 11093597 = 4160099) B4160099
theorem B7395731 : Blo 2161435 7395731 := bstep (se 1 (by rfl) ⟨5546798, by rfl⟩ : syracuseStep 7395731 = 11093597) B11093597
theorem B4930487 : Blo 2161435 4930487 := bstep (se 1 (by rfl) ⟨3697865, by rfl⟩ : syracuseStep 4930487 = 7395731) B7395731
theorem B3286991 : Blo 2161435 3286991 := bstep (se 1 (by rfl) ⟨2465243, by rfl⟩ : syracuseStep 3286991 = 4930487) B4930487
theorem B8765309 : Blo 2161435 8765309 := bstep (se 3 (by rfl) ⟨1643495, by rfl⟩ : syracuseStep 8765309 = 3286991) B3286991
theorem B5843539 : Blo 2161435 5843539 := bstep (se 1 (by rfl) ⟨4382654, by rfl⟩ : syracuseStep 5843539 = 8765309) B8765309
theorem B7791385 : Blo 2161435 7791385 := bstep (se 2 (by rfl) ⟨2921769, by rfl⟩ : syracuseStep 7791385 = 5843539) B5843539
theorem B10388513 : Blo 2161435 10388513 := bstep (se 2 (by rfl) ⟨3895692, by rfl⟩ : syracuseStep 10388513 = 7791385) B7791385
theorem B6925675 : Blo 2161435 6925675 := bstep (se 1 (by rfl) ⟨5194256, by rfl⟩ : syracuseStep 6925675 = 10388513) B10388513
theorem B9234233 : Blo 2161435 9234233 := bstep (se 2 (by rfl) ⟨3462837, by rfl⟩ : syracuseStep 9234233 = 6925675) B6925675
theorem B6156155 : Blo 2161435 6156155 := bstep (se 1 (by rfl) ⟨4617116, by rfl⟩ : syracuseStep 6156155 = 9234233) B9234233
theorem B4104103 : Blo 2161435 4104103 := bstep (se 1 (by rfl) ⟨3078077, by rfl⟩ : syracuseStep 4104103 = 6156155) B6156155
theorem B5472137 : Blo 2161435 5472137 := bstep (se 2 (by rfl) ⟨2052051, by rfl⟩ : syracuseStep 5472137 = 4104103) B4104103
theorem B3648091 : Blo 2161435 3648091 := bstep (se 1 (by rfl) ⟨2736068, by rfl⟩ : syracuseStep 3648091 = 5472137) B5472137
theorem B4864121 : Blo 2161435 4864121 := bstep (se 2 (by rfl) ⟨1824045, by rfl⟩ : syracuseStep 4864121 = 3648091) B3648091
theorem B3242747 : Blo 2161435 3242747 := bstep (se 1 (by rfl) ⟨2432060, by rfl⟩ : syracuseStep 3242747 = 4864121) B4864121
theorem B2161831 : Blo 2161435 2161831 := bstep (se 1 (by rfl) ⟨1621373, by rfl⟩ : syracuseStep 2161831 = 3242747) B3242747
theorem B2432065 : Blo 2161435 2432065 := bbase (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) (by norm_num)
theorem B3242753 : Blo 2161435 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B2161835 : Blo 2161435 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B5472157 : Blo 2161435 5472157 := bbase (se 3 (by rfl) ⟨1026029, by rfl⟩ : syracuseStep 5472157 = 2052059) (by norm_num)
theorem B7296209 : Blo 2161435 7296209 := bstep (se 2 (by rfl) ⟨2736078, by rfl⟩ : syracuseStep 7296209 = 5472157) B5472157
theorem B4864139 : Blo 2161435 4864139 := bstep (se 1 (by rfl) ⟨3648104, by rfl⟩ : syracuseStep 4864139 = 7296209) B7296209
theorem B3242759 : Blo 2161435 3242759 := bstep (se 1 (by rfl) ⟨2432069, by rfl⟩ : syracuseStep 3242759 = 4864139) B4864139
theorem B2161839 : Blo 2161435 2161839 := bstep (se 1 (by rfl) ⟨1621379, by rfl⟩ : syracuseStep 2161839 = 3242759) B3242759
theorem B3242765 : Blo 2161435 3242765 := bbase (se 3 (by rfl) ⟨608018, by rfl⟩ : syracuseStep 3242765 = 1216037) (by norm_num)
theorem B2161843 : Blo 2161435 2161843 := bstep (se 1 (by rfl) ⟨1621382, by rfl⟩ : syracuseStep 2161843 = 3242765) B3242765
theorem B4864157 : Blo 2161435 4864157 := bbase (se 3 (by rfl) ⟨912029, by rfl⟩ : syracuseStep 4864157 = 1824059) (by norm_num)
theorem B3242771 : Blo 2161435 3242771 := bstep (se 1 (by rfl) ⟨2432078, by rfl⟩ : syracuseStep 3242771 = 4864157) B4864157
theorem B2161847 : Blo 2161435 2161847 := bstep (se 1 (by rfl) ⟨1621385, by rfl⟩ : syracuseStep 2161847 = 3242771) B3242771
theorem B3648125 : Blo 2161435 3648125 := bbase (se 3 (by rfl) ⟨684023, by rfl⟩ : syracuseStep 3648125 = 1368047) (by norm_num)
theorem B2432083 : Blo 2161435 2432083 := bstep (se 1 (by rfl) ⟨1824062, by rfl⟩ : syracuseStep 2432083 = 3648125) B3648125
theorem B3242777 : Blo 2161435 3242777 := bstep (se 2 (by rfl) ⟨1216041, by rfl⟩ : syracuseStep 3242777 = 2432083) B2432083
theorem B2161851 : Blo 2161435 2161851 := bstep (se 1 (by rfl) ⟨1621388, by rfl⟩ : syracuseStep 2161851 = 3242777) B3242777
theorem B4930541 : Blo 2161435 4930541 := bbase (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) (by norm_num)
theorem B3287027 : Blo 2161435 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B8765405 : Blo 2161435 8765405 := bstep (se 3 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 8765405 = 3287027) B3287027
theorem B5843603 : Blo 2161435 5843603 := bstep (se 1 (by rfl) ⟨4382702, by rfl⟩ : syracuseStep 5843603 = 8765405) B8765405
theorem B15582941 : Blo 2161435 15582941 := bstep (se 3 (by rfl) ⟨2921801, by rfl⟩ : syracuseStep 15582941 = 5843603) B5843603
theorem B10388627 : Blo 2161435 10388627 := bstep (se 1 (by rfl) ⟨7791470, by rfl⟩ : syracuseStep 10388627 = 15582941) B15582941
theorem B6925751 : Blo 2161435 6925751 := bstep (se 1 (by rfl) ⟨5194313, by rfl⟩ : syracuseStep 6925751 = 10388627) B10388627
theorem B4617167 : Blo 2161435 4617167 := bstep (se 1 (by rfl) ⟨3462875, by rfl⟩ : syracuseStep 4617167 = 6925751) B6925751
theorem B12312445 : Blo 2161435 12312445 := bstep (se 3 (by rfl) ⟨2308583, by rfl⟩ : syracuseStep 12312445 = 4617167) B4617167
theorem B16416593 : Blo 2161435 16416593 := bstep (se 2 (by rfl) ⟨6156222, by rfl⟩ : syracuseStep 16416593 = 12312445) B12312445
theorem B10944395 : Blo 2161435 10944395 := bstep (se 1 (by rfl) ⟨8208296, by rfl⟩ : syracuseStep 10944395 = 16416593) B16416593
theorem B7296263 : Blo 2161435 7296263 := bstep (se 1 (by rfl) ⟨5472197, by rfl⟩ : syracuseStep 7296263 = 10944395) B10944395
theorem B4864175 : Blo 2161435 4864175 := bstep (se 1 (by rfl) ⟨3648131, by rfl⟩ : syracuseStep 4864175 = 7296263) B7296263
theorem B3242783 : Blo 2161435 3242783 := bstep (se 1 (by rfl) ⟨2432087, by rfl⟩ : syracuseStep 3242783 = 4864175) B4864175
theorem B2161855 : Blo 2161435 2161855 := bstep (se 1 (by rfl) ⟨1621391, by rfl⟩ : syracuseStep 2161855 = 3242783) B3242783
theorem B3242789 : Blo 2161435 3242789 := bbase (se 4 (by rfl) ⟨304011, by rfl⟩ : syracuseStep 3242789 = 608023) (by norm_num)
theorem B2161859 : Blo 2161435 2161859 := bstep (se 1 (by rfl) ⟨1621394, by rfl⟩ : syracuseStep 2161859 = 3242789) B3242789
theorem B2736109 : Blo 2161435 2736109 := bbase (se 3 (by rfl) ⟨513020, by rfl⟩ : syracuseStep 2736109 = 1026041) (by norm_num)
theorem B3648145 : Blo 2161435 3648145 := bstep (se 2 (by rfl) ⟨1368054, by rfl⟩ : syracuseStep 3648145 = 2736109) B2736109
theorem B4864193 : Blo 2161435 4864193 := bstep (se 2 (by rfl) ⟨1824072, by rfl⟩ : syracuseStep 4864193 = 3648145) B3648145
theorem B3242795 : Blo 2161435 3242795 := bstep (se 1 (by rfl) ⟨2432096, by rfl⟩ : syracuseStep 3242795 = 4864193) B4864193
theorem B2161863 : Blo 2161435 2161863 := bstep (se 1 (by rfl) ⟨1621397, by rfl⟩ : syracuseStep 2161863 = 3242795) B3242795
theorem B2432101 : Blo 2161435 2432101 := bbase (se 4 (by rfl) ⟨228009, by rfl⟩ : syracuseStep 2432101 = 456019) (by norm_num)
theorem B3242801 : Blo 2161435 3242801 := bstep (se 2 (by rfl) ⟨1216050, by rfl⟩ : syracuseStep 3242801 = 2432101) B2432101
theorem B2161867 : Blo 2161435 2161867 := bstep (se 1 (by rfl) ⟨1621400, by rfl⟩ : syracuseStep 2161867 = 3242801) B3242801
theorem B2308601 : Blo 2161435 2308601 := bbase (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) (by norm_num)
theorem B6156269 : Blo 2161435 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B4104179 : Blo 2161435 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B2736119 : Blo 2161435 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B7296317 : Blo 2161435 7296317 := bstep (se 3 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 7296317 = 2736119) B2736119
theorem B4864211 : Blo 2161435 4864211 := bstep (se 1 (by rfl) ⟨3648158, by rfl⟩ : syracuseStep 4864211 = 7296317) B7296317
theorem B3242807 : Blo 2161435 3242807 := bstep (se 1 (by rfl) ⟨2432105, by rfl⟩ : syracuseStep 3242807 = 4864211) B4864211
theorem B2161871 : Blo 2161435 2161871 := bstep (se 1 (by rfl) ⟨1621403, by rfl⟩ : syracuseStep 2161871 = 3242807) B3242807
theorem B3242813 : Blo 2161435 3242813 := bbase (se 3 (by rfl) ⟨608027, by rfl⟩ : syracuseStep 3242813 = 1216055) (by norm_num)
theorem B2161875 : Blo 2161435 2161875 := bstep (se 1 (by rfl) ⟨1621406, by rfl⟩ : syracuseStep 2161875 = 3242813) B3242813
theorem B4864229 : Blo 2161435 4864229 := bbase (se 4 (by rfl) ⟨456021, by rfl⟩ : syracuseStep 4864229 = 912043) (by norm_num)
theorem B3242819 : Blo 2161435 3242819 := bstep (se 1 (by rfl) ⟨2432114, by rfl⟩ : syracuseStep 3242819 = 4864229) B4864229
theorem B2161879 : Blo 2161435 2161879 := bstep (se 1 (by rfl) ⟨1621409, by rfl⟩ : syracuseStep 2161879 = 3242819) B3242819
theorem B5472269 : Blo 2161435 5472269 := bbase (se 3 (by rfl) ⟨1026050, by rfl⟩ : syracuseStep 5472269 = 2052101) (by norm_num)
theorem B3648179 : Blo 2161435 3648179 := bstep (se 1 (by rfl) ⟨2736134, by rfl⟩ : syracuseStep 3648179 = 5472269) B5472269
theorem B2432119 : Blo 2161435 2432119 := bstep (se 1 (by rfl) ⟨1824089, by rfl⟩ : syracuseStep 2432119 = 3648179) B3648179
theorem B3242825 : Blo 2161435 3242825 := bstep (se 2 (by rfl) ⟨1216059, by rfl⟩ : syracuseStep 3242825 = 2432119) B2432119
theorem B2161883 : Blo 2161435 2161883 := bstep (se 1 (by rfl) ⟨1621412, by rfl⟩ : syracuseStep 2161883 = 3242825) B3242825
theorem B3078157 : Blo 2161435 3078157 := bbase (se 3 (by rfl) ⟨577154, by rfl⟩ : syracuseStep 3078157 = 1154309) (by norm_num)
theorem B4104209 : Blo 2161435 4104209 := bstep (se 2 (by rfl) ⟨1539078, by rfl⟩ : syracuseStep 4104209 = 3078157) B3078157
theorem B10944557 : Blo 2161435 10944557 := bstep (se 3 (by rfl) ⟨2052104, by rfl⟩ : syracuseStep 10944557 = 4104209) B4104209
theorem B7296371 : Blo 2161435 7296371 := bstep (se 1 (by rfl) ⟨5472278, by rfl⟩ : syracuseStep 7296371 = 10944557) B10944557
theorem B4864247 : Blo 2161435 4864247 := bstep (se 1 (by rfl) ⟨3648185, by rfl⟩ : syracuseStep 4864247 = 7296371) B7296371
theorem B3242831 : Blo 2161435 3242831 := bstep (se 1 (by rfl) ⟨2432123, by rfl⟩ : syracuseStep 3242831 = 4864247) B4864247
theorem B2161887 : Blo 2161435 2161887 := bstep (se 1 (by rfl) ⟨1621415, by rfl⟩ : syracuseStep 2161887 = 3242831) B3242831
theorem B3242837 : Blo 2161435 3242837 := bbase (se 9 (by rfl) ⟨9500, by rfl⟩ : syracuseStep 3242837 = 19001) (by norm_num)
theorem B2161891 : Blo 2161435 2161891 := bstep (se 1 (by rfl) ⟨1621418, by rfl⟩ : syracuseStep 2161891 = 3242837) B3242837
theorem B4617253 : Blo 2161435 4617253 := bbase (se 4 (by rfl) ⟨432867, by rfl⟩ : syracuseStep 4617253 = 865735) (by norm_num)
theorem B6156337 : Blo 2161435 6156337 := bstep (se 2 (by rfl) ⟨2308626, by rfl⟩ : syracuseStep 6156337 = 4617253) B4617253
theorem B8208449 : Blo 2161435 8208449 := bstep (se 2 (by rfl) ⟨3078168, by rfl⟩ : syracuseStep 8208449 = 6156337) B6156337
theorem B5472299 : Blo 2161435 5472299 := bstep (se 1 (by rfl) ⟨4104224, by rfl⟩ : syracuseStep 5472299 = 8208449) B8208449
theorem B3648199 : Blo 2161435 3648199 := bstep (se 1 (by rfl) ⟨2736149, by rfl⟩ : syracuseStep 3648199 = 5472299) B5472299
theorem B4864265 : Blo 2161435 4864265 := bstep (se 2 (by rfl) ⟨1824099, by rfl⟩ : syracuseStep 4864265 = 3648199) B3648199
theorem B3242843 : Blo 2161435 3242843 := bstep (se 1 (by rfl) ⟨2432132, by rfl⟩ : syracuseStep 3242843 = 4864265) B4864265
theorem B2161895 : Blo 2161435 2161895 := bstep (se 1 (by rfl) ⟨1621421, by rfl⟩ : syracuseStep 2161895 = 3242843) B3242843
theorem B2432137 : Blo 2161435 2432137 := bbase (se 2 (by rfl) ⟨912051, by rfl⟩ : syracuseStep 2432137 = 1824103) (by norm_num)
theorem B3242849 : Blo 2161435 3242849 := bstep (se 2 (by rfl) ⟨1216068, by rfl⟩ : syracuseStep 3242849 = 2432137) B2432137
theorem B2161899 : Blo 2161435 2161899 := bstep (se 1 (by rfl) ⟨1621424, by rfl⟩ : syracuseStep 2161899 = 3242849) B3242849
theorem B168489557 : Blo 2161435 168489557 := bbase (se 8 (by rfl) ⟨987243, by rfl⟩ : syracuseStep 168489557 = 1974487) (by norm_num)
theorem B112326371 : Blo 2161435 112326371 := bstep (se 1 (by rfl) ⟨84244778, by rfl⟩ : syracuseStep 112326371 = 168489557) B168489557
theorem B74884247 : Blo 2161435 74884247 := bstep (se 1 (by rfl) ⟨56163185, by rfl⟩ : syracuseStep 74884247 = 112326371) B112326371
theorem B49922831 : Blo 2161435 49922831 := bstep (se 1 (by rfl) ⟨37442123, by rfl⟩ : syracuseStep 49922831 = 74884247) B74884247
theorem B33281887 : Blo 2161435 33281887 := bstep (se 1 (by rfl) ⟨24961415, by rfl⟩ : syracuseStep 33281887 = 49922831) B49922831
theorem B44375849 : Blo 2161435 44375849 := bstep (se 2 (by rfl) ⟨16640943, by rfl⟩ : syracuseStep 44375849 = 33281887) B33281887
theorem B29583899 : Blo 2161435 29583899 := bstep (se 1 (by rfl) ⟨22187924, by rfl⟩ : syracuseStep 29583899 = 44375849) B44375849
theorem B19722599 : Blo 2161435 19722599 := bstep (se 1 (by rfl) ⟨14791949, by rfl⟩ : syracuseStep 19722599 = 29583899) B29583899
theorem B13148399 : Blo 2161435 13148399 := bstep (se 1 (by rfl) ⟨9861299, by rfl⟩ : syracuseStep 13148399 = 19722599) B19722599
theorem B8765599 : Blo 2161435 8765599 := bstep (se 1 (by rfl) ⟨6574199, by rfl⟩ : syracuseStep 8765599 = 13148399) B13148399
theorem B11687465 : Blo 2161435 11687465 := bstep (se 2 (by rfl) ⟨4382799, by rfl⟩ : syracuseStep 11687465 = 8765599) B8765599
theorem B7791643 : Blo 2161435 7791643 := bstep (se 1 (by rfl) ⟨5843732, by rfl⟩ : syracuseStep 7791643 = 11687465) B11687465
theorem B41555429 : Blo 2161435 41555429 := bstep (se 4 (by rfl) ⟨3895821, by rfl⟩ : syracuseStep 41555429 = 7791643) B7791643
theorem B27703619 : Blo 2161435 27703619 := bstep (se 1 (by rfl) ⟨20777714, by rfl⟩ : syracuseStep 27703619 = 41555429) B41555429
theorem B18469079 : Blo 2161435 18469079 := bstep (se 1 (by rfl) ⟨13851809, by rfl⟩ : syracuseStep 18469079 = 27703619) B27703619
theorem B12312719 : Blo 2161435 12312719 := bstep (se 1 (by rfl) ⟨9234539, by rfl⟩ : syracuseStep 12312719 = 18469079) B18469079
theorem B8208479 : Blo 2161435 8208479 := bstep (se 1 (by rfl) ⟨6156359, by rfl⟩ : syracuseStep 8208479 = 12312719) B12312719
theorem B5472319 : Blo 2161435 5472319 := bstep (se 1 (by rfl) ⟨4104239, by rfl⟩ : syracuseStep 5472319 = 8208479) B8208479
theorem B7296425 : Blo 2161435 7296425 := bstep (se 2 (by rfl) ⟨2736159, by rfl⟩ : syracuseStep 7296425 = 5472319) B5472319
theorem B4864283 : Blo 2161435 4864283 := bstep (se 1 (by rfl) ⟨3648212, by rfl⟩ : syracuseStep 4864283 = 7296425) B7296425
theorem B3242855 : Blo 2161435 3242855 := bstep (se 1 (by rfl) ⟨2432141, by rfl⟩ : syracuseStep 3242855 = 4864283) B4864283
theorem B2161903 : Blo 2161435 2161903 := bstep (se 1 (by rfl) ⟨1621427, by rfl⟩ : syracuseStep 2161903 = 3242855) B3242855
theorem B3242861 : Blo 2161435 3242861 := bbase (se 3 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 3242861 = 1216073) (by norm_num)
theorem B2161907 : Blo 2161435 2161907 := bstep (se 1 (by rfl) ⟨1621430, by rfl⟩ : syracuseStep 2161907 = 3242861) B3242861
theorem B4864301 : Blo 2161435 4864301 := bbase (se 3 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 4864301 = 1824113) (by norm_num)
theorem B3242867 : Blo 2161435 3242867 := bstep (se 1 (by rfl) ⟨2432150, by rfl⟩ : syracuseStep 3242867 = 4864301) B4864301
theorem B2161911 : Blo 2161435 2161911 := bstep (se 1 (by rfl) ⟨1621433, by rfl⟩ : syracuseStep 2161911 = 3242867) B3242867
theorem B4160261 : Blo 2161435 4160261 := bbase (se 4 (by rfl) ⟨390024, by rfl⟩ : syracuseStep 4160261 = 780049) (by norm_num)
theorem B11094029 : Blo 2161435 11094029 := bstep (se 3 (by rfl) ⟨2080130, by rfl⟩ : syracuseStep 11094029 = 4160261) B4160261
theorem B7396019 : Blo 2161435 7396019 := bstep (se 1 (by rfl) ⟨5547014, by rfl⟩ : syracuseStep 7396019 = 11094029) B11094029
theorem B4930679 : Blo 2161435 4930679 := bstep (se 1 (by rfl) ⟨3698009, by rfl⟩ : syracuseStep 4930679 = 7396019) B7396019
theorem B13148477 : Blo 2161435 13148477 := bstep (se 3 (by rfl) ⟨2465339, by rfl⟩ : syracuseStep 13148477 = 4930679) B4930679
theorem B8765651 : Blo 2161435 8765651 := bstep (se 1 (by rfl) ⟨6574238, by rfl⟩ : syracuseStep 8765651 = 13148477) B13148477
theorem B5843767 : Blo 2161435 5843767 := bstep (se 1 (by rfl) ⟨4382825, by rfl⟩ : syracuseStep 5843767 = 8765651) B8765651
theorem B7791689 : Blo 2161435 7791689 := bstep (se 2 (by rfl) ⟨2921883, by rfl⟩ : syracuseStep 7791689 = 5843767) B5843767
theorem B5194459 : Blo 2161435 5194459 := bstep (se 1 (by rfl) ⟨3895844, by rfl⟩ : syracuseStep 5194459 = 7791689) B7791689
theorem B6925945 : Blo 2161435 6925945 := bstep (se 2 (by rfl) ⟨2597229, by rfl⟩ : syracuseStep 6925945 = 5194459) B5194459
theorem B9234593 : Blo 2161435 9234593 := bstep (se 2 (by rfl) ⟨3462972, by rfl⟩ : syracuseStep 9234593 = 6925945) B6925945
theorem B6156395 : Blo 2161435 6156395 := bstep (se 1 (by rfl) ⟨4617296, by rfl⟩ : syracuseStep 6156395 = 9234593) B9234593
theorem B4104263 : Blo 2161435 4104263 := bstep (se 1 (by rfl) ⟨3078197, by rfl⟩ : syracuseStep 4104263 = 6156395) B6156395
theorem B2736175 : Blo 2161435 2736175 := bstep (se 1 (by rfl) ⟨2052131, by rfl⟩ : syracuseStep 2736175 = 4104263) B4104263
theorem B3648233 : Blo 2161435 3648233 := bstep (se 2 (by rfl) ⟨1368087, by rfl⟩ : syracuseStep 3648233 = 2736175) B2736175
theorem B2432155 : Blo 2161435 2432155 := bstep (se 1 (by rfl) ⟨1824116, by rfl⟩ : syracuseStep 2432155 = 3648233) B3648233
theorem B3242873 : Blo 2161435 3242873 := bstep (se 2 (by rfl) ⟨1216077, by rfl⟩ : syracuseStep 3242873 = 2432155) B2432155
theorem B2161915 : Blo 2161435 2161915 := bstep (se 1 (by rfl) ⟨1621436, by rfl⟩ : syracuseStep 2161915 = 3242873) B3242873
theorem B6325541 : Blo 2161435 6325541 := bbase (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) (by norm_num)
theorem B4217027 : Blo 2161435 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B11245405 : Blo 2161435 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B14993873 : Blo 2161435 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B9995915 : Blo 2161435 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B6663943 : Blo 2161435 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B8885257 : Blo 2161435 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B47388037 : Blo 2161435 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B63184049 : Blo 2161435 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B42122699 : Blo 2161435 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B28081799 : Blo 2161435 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B18721199 : Blo 2161435 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B12480799 : Blo 2161435 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B16641065 : Blo 2161435 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B44376173 : Blo 2161435 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B29584115 : Blo 2161435 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B19722743 : Blo 2161435 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B13148495 : Blo 2161435 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B8765663 : Blo 2161435 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B23375101 : Blo 2161435 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B31166801 : Blo 2161435 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B20777867 : Blo 2161435 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B13851911 : Blo 2161435 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B36938429 : Blo 2161435 36938429 := bstep (se 3 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 36938429 = 13851911) B13851911
theorem B24625619 : Blo 2161435 24625619 := bstep (se 1 (by rfl) ⟨18469214, by rfl⟩ : syracuseStep 24625619 = 36938429) B36938429
theorem B16417079 : Blo 2161435 16417079 := bstep (se 1 (by rfl) ⟨12312809, by rfl⟩ : syracuseStep 16417079 = 24625619) B24625619
theorem B10944719 : Blo 2161435 10944719 := bstep (se 1 (by rfl) ⟨8208539, by rfl⟩ : syracuseStep 10944719 = 16417079) B16417079
theorem B7296479 : Blo 2161435 7296479 := bstep (se 1 (by rfl) ⟨5472359, by rfl⟩ : syracuseStep 7296479 = 10944719) B10944719
theorem B4864319 : Blo 2161435 4864319 := bstep (se 1 (by rfl) ⟨3648239, by rfl⟩ : syracuseStep 4864319 = 7296479) B7296479
theorem B3242879 : Blo 2161435 3242879 := bstep (se 1 (by rfl) ⟨2432159, by rfl⟩ : syracuseStep 3242879 = 4864319) B4864319
theorem B2161919 : Blo 2161435 2161919 := bstep (se 1 (by rfl) ⟨1621439, by rfl⟩ : syracuseStep 2161919 = 3242879) B3242879
theorem B3242885 : Blo 2161435 3242885 := bbase (se 4 (by rfl) ⟨304020, by rfl⟩ : syracuseStep 3242885 = 608041) (by norm_num)
theorem B2161923 : Blo 2161435 2161923 := bstep (se 1 (by rfl) ⟨1621442, by rfl⟩ : syracuseStep 2161923 = 3242885) B3242885
theorem B3648253 : Blo 2161435 3648253 := bbase (se 3 (by rfl) ⟨684047, by rfl⟩ : syracuseStep 3648253 = 1368095) (by norm_num)
theorem B4864337 : Blo 2161435 4864337 := bstep (se 2 (by rfl) ⟨1824126, by rfl⟩ : syracuseStep 4864337 = 3648253) B3648253
theorem B3242891 : Blo 2161435 3242891 := bstep (se 1 (by rfl) ⟨2432168, by rfl⟩ : syracuseStep 3242891 = 4864337) B4864337
theorem B2161927 : Blo 2161435 2161927 := bstep (se 1 (by rfl) ⟨1621445, by rfl⟩ : syracuseStep 2161927 = 3242891) B3242891
theorem B2432173 : Blo 2161435 2432173 := bbase (se 3 (by rfl) ⟨456032, by rfl⟩ : syracuseStep 2432173 = 912065) (by norm_num)
theorem B3242897 : Blo 2161435 3242897 := bstep (se 2 (by rfl) ⟨1216086, by rfl⟩ : syracuseStep 3242897 = 2432173) B2432173
theorem B2161931 : Blo 2161435 2161931 := bstep (se 1 (by rfl) ⟨1621448, by rfl⟩ : syracuseStep 2161931 = 3242897) B3242897
theorem B7296533 : Blo 2161435 7296533 := bbase (se 6 (by rfl) ⟨171012, by rfl⟩ : syracuseStep 7296533 = 342025) (by norm_num)
theorem B4864355 : Blo 2161435 4864355 := bstep (se 1 (by rfl) ⟨3648266, by rfl⟩ : syracuseStep 4864355 = 7296533) B7296533
theorem B3242903 : Blo 2161435 3242903 := bstep (se 1 (by rfl) ⟨2432177, by rfl⟩ : syracuseStep 3242903 = 4864355) B4864355
theorem B2161935 : Blo 2161435 2161935 := bstep (se 1 (by rfl) ⟨1621451, by rfl⟩ : syracuseStep 2161935 = 3242903) B3242903
theorem B3242909 : Blo 2161435 3242909 := bbase (se 3 (by rfl) ⟨608045, by rfl⟩ : syracuseStep 3242909 = 1216091) (by norm_num)
theorem B2161939 : Blo 2161435 2161939 := bstep (se 1 (by rfl) ⟨1621454, by rfl⟩ : syracuseStep 2161939 = 3242909) B3242909
theorem B4864373 : Blo 2161435 4864373 := bbase (se 5 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 4864373 = 456035) (by norm_num)
theorem B3242915 : Blo 2161435 3242915 := bstep (se 1 (by rfl) ⟨2432186, by rfl⟩ : syracuseStep 3242915 = 4864373) B4864373
theorem B2161943 : Blo 2161435 2161943 := bstep (se 1 (by rfl) ⟨1621457, by rfl⟩ : syracuseStep 2161943 = 3242915) B3242915
theorem B3606709 : Blo 2161435 3606709 := bbase (se 5 (by rfl) ⟨169064, by rfl⟩ : syracuseStep 3606709 = 338129) (by norm_num)
theorem B4808945 : Blo 2161435 4808945 := bstep (se 2 (by rfl) ⟨1803354, by rfl⟩ : syracuseStep 4808945 = 3606709) B3606709
theorem B12823853 : Blo 2161435 12823853 := bstep (se 3 (by rfl) ⟨2404472, by rfl⟩ : syracuseStep 12823853 = 4808945) B4808945
theorem B34196941 : Blo 2161435 34196941 := bstep (se 3 (by rfl) ⟨6411926, by rfl⟩ : syracuseStep 34196941 = 12823853) B12823853
theorem B45595921 : Blo 2161435 45595921 := bstep (se 2 (by rfl) ⟨17098470, by rfl⟩ : syracuseStep 45595921 = 34196941) B34196941
theorem B60794561 : Blo 2161435 60794561 := bstep (se 2 (by rfl) ⟨22797960, by rfl⟩ : syracuseStep 60794561 = 45595921) B45595921
theorem B162118829 : Blo 2161435 162118829 := bstep (se 3 (by rfl) ⟨30397280, by rfl⟩ : syracuseStep 162118829 = 60794561) B60794561
theorem B108079219 : Blo 2161435 108079219 := bstep (se 1 (by rfl) ⟨81059414, by rfl⟩ : syracuseStep 108079219 = 162118829) B162118829
theorem B144105625 : Blo 2161435 144105625 := bstep (se 2 (by rfl) ⟨54039609, by rfl⟩ : syracuseStep 144105625 = 108079219) B108079219
theorem B192140833 : Blo 2161435 192140833 := bstep (se 2 (by rfl) ⟨72052812, by rfl⟩ : syracuseStep 192140833 = 144105625) B144105625
theorem B256187777 : Blo 2161435 256187777 := bstep (se 2 (by rfl) ⟨96070416, by rfl⟩ : syracuseStep 256187777 = 192140833) B192140833
theorem B683167405 : Blo 2161435 683167405 := bstep (se 3 (by rfl) ⟨128093888, by rfl⟩ : syracuseStep 683167405 = 256187777) B256187777
theorem B910889873 : Blo 2161435 910889873 := bstep (se 2 (by rfl) ⟨341583702, by rfl⟩ : syracuseStep 910889873 = 683167405) B683167405
theorem B607259915 : Blo 2161435 607259915 := bstep (se 1 (by rfl) ⟨455444936, by rfl⟩ : syracuseStep 607259915 = 910889873) B910889873
theorem B404839943 : Blo 2161435 404839943 := bstep (se 1 (by rfl) ⟨303629957, by rfl⟩ : syracuseStep 404839943 = 607259915) B607259915
theorem B269893295 : Blo 2161435 269893295 := bstep (se 1 (by rfl) ⟨202419971, by rfl⟩ : syracuseStep 269893295 = 404839943) B404839943
theorem B179928863 : Blo 2161435 179928863 := bstep (se 1 (by rfl) ⟨134946647, by rfl⟩ : syracuseStep 179928863 = 269893295) B269893295
theorem B119952575 : Blo 2161435 119952575 := bstep (se 1 (by rfl) ⟨89964431, by rfl⟩ : syracuseStep 119952575 = 179928863) B179928863
theorem B79968383 : Blo 2161435 79968383 := bstep (se 1 (by rfl) ⟨59976287, by rfl⟩ : syracuseStep 79968383 = 119952575) B119952575
theorem B53312255 : Blo 2161435 53312255 := bstep (se 1 (by rfl) ⟨39984191, by rfl⟩ : syracuseStep 53312255 = 79968383) B79968383
theorem B35541503 : Blo 2161435 35541503 := bstep (se 1 (by rfl) ⟨26656127, by rfl⟩ : syracuseStep 35541503 = 53312255) B53312255
theorem B23694335 : Blo 2161435 23694335 := bstep (se 1 (by rfl) ⟨17770751, by rfl⟩ : syracuseStep 23694335 = 35541503) B35541503
theorem B15796223 : Blo 2161435 15796223 := bstep (se 1 (by rfl) ⟨11847167, by rfl⟩ : syracuseStep 15796223 = 23694335) B23694335
theorem B10530815 : Blo 2161435 10530815 := bstep (se 1 (by rfl) ⟨7898111, by rfl⟩ : syracuseStep 10530815 = 15796223) B15796223
theorem B28082173 : Blo 2161435 28082173 := bstep (se 3 (by rfl) ⟨5265407, by rfl⟩ : syracuseStep 28082173 = 10530815) B10530815
theorem B37442897 : Blo 2161435 37442897 := bstep (se 2 (by rfl) ⟨14041086, by rfl⟩ : syracuseStep 37442897 = 28082173) B28082173
theorem B24961931 : Blo 2161435 24961931 := bstep (se 1 (by rfl) ⟨18721448, by rfl⟩ : syracuseStep 24961931 = 37442897) B37442897
theorem B16641287 : Blo 2161435 16641287 := bstep (se 1 (by rfl) ⟨12480965, by rfl⟩ : syracuseStep 16641287 = 24961931) B24961931
theorem B11094191 : Blo 2161435 11094191 := bstep (se 1 (by rfl) ⟨8320643, by rfl⟩ : syracuseStep 11094191 = 16641287) B16641287
theorem B7396127 : Blo 2161435 7396127 := bstep (se 1 (by rfl) ⟨5547095, by rfl⟩ : syracuseStep 7396127 = 11094191) B11094191
theorem B4930751 : Blo 2161435 4930751 := bstep (se 1 (by rfl) ⟨3698063, by rfl⟩ : syracuseStep 4930751 = 7396127) B7396127
theorem B13148669 : Blo 2161435 13148669 := bstep (se 3 (by rfl) ⟨2465375, by rfl⟩ : syracuseStep 13148669 = 4930751) B4930751
theorem B8765779 : Blo 2161435 8765779 := bstep (se 1 (by rfl) ⟨6574334, by rfl⟩ : syracuseStep 8765779 = 13148669) B13148669
theorem B11687705 : Blo 2161435 11687705 := bstep (se 2 (by rfl) ⟨4382889, by rfl⟩ : syracuseStep 11687705 = 8765779) B8765779
theorem B7791803 : Blo 2161435 7791803 := bstep (se 1 (by rfl) ⟨5843852, by rfl⟩ : syracuseStep 7791803 = 11687705) B11687705
theorem B5194535 : Blo 2161435 5194535 := bstep (se 1 (by rfl) ⟨3895901, by rfl⟩ : syracuseStep 5194535 = 7791803) B7791803
theorem B13852093 : Blo 2161435 13852093 := bstep (se 3 (by rfl) ⟨2597267, by rfl⟩ : syracuseStep 13852093 = 5194535) B5194535
theorem B18469457 : Blo 2161435 18469457 := bstep (se 2 (by rfl) ⟨6926046, by rfl⟩ : syracuseStep 18469457 = 13852093) B13852093
theorem B12312971 : Blo 2161435 12312971 := bstep (se 1 (by rfl) ⟨9234728, by rfl⟩ : syracuseStep 12312971 = 18469457) B18469457
theorem B8208647 : Blo 2161435 8208647 := bstep (se 1 (by rfl) ⟨6156485, by rfl⟩ : syracuseStep 8208647 = 12312971) B12312971
theorem B5472431 : Blo 2161435 5472431 := bstep (se 1 (by rfl) ⟨4104323, by rfl⟩ : syracuseStep 5472431 = 8208647) B8208647
theorem B3648287 : Blo 2161435 3648287 := bstep (se 1 (by rfl) ⟨2736215, by rfl⟩ : syracuseStep 3648287 = 5472431) B5472431
theorem B2432191 : Blo 2161435 2432191 := bstep (se 1 (by rfl) ⟨1824143, by rfl⟩ : syracuseStep 2432191 = 3648287) B3648287
theorem B3242921 : Blo 2161435 3242921 := bstep (se 2 (by rfl) ⟨1216095, by rfl⟩ : syracuseStep 3242921 = 2432191) B2432191
theorem B2161947 : Blo 2161435 2161947 := bstep (se 1 (by rfl) ⟨1621460, by rfl⟩ : syracuseStep 2161947 = 3242921) B3242921
theorem B8208661 : Blo 2161435 8208661 := bbase (se 6 (by rfl) ⟨192390, by rfl⟩ : syracuseStep 8208661 = 384781) (by norm_num)
theorem B10944881 : Blo 2161435 10944881 := bstep (se 2 (by rfl) ⟨4104330, by rfl⟩ : syracuseStep 10944881 = 8208661) B8208661
theorem B7296587 : Blo 2161435 7296587 := bstep (se 1 (by rfl) ⟨5472440, by rfl⟩ : syracuseStep 7296587 = 10944881) B10944881
theorem B4864391 : Blo 2161435 4864391 := bstep (se 1 (by rfl) ⟨3648293, by rfl⟩ : syracuseStep 4864391 = 7296587) B7296587
theorem B3242927 : Blo 2161435 3242927 := bstep (se 1 (by rfl) ⟨2432195, by rfl⟩ : syracuseStep 3242927 = 4864391) B4864391
theorem B2161951 : Blo 2161435 2161951 := bstep (se 1 (by rfl) ⟨1621463, by rfl⟩ : syracuseStep 2161951 = 3242927) B3242927
theorem B3242933 : Blo 2161435 3242933 := bbase (se 5 (by rfl) ⟨152012, by rfl⟩ : syracuseStep 3242933 = 304025) (by norm_num)
theorem B2161955 : Blo 2161435 2161955 := bstep (se 1 (by rfl) ⟨1621466, by rfl⟩ : syracuseStep 2161955 = 3242933) B3242933
theorem B5472461 : Blo 2161435 5472461 := bbase (se 3 (by rfl) ⟨1026086, by rfl⟩ : syracuseStep 5472461 = 2052173) (by norm_num)
theorem B3648307 : Blo 2161435 3648307 := bstep (se 1 (by rfl) ⟨2736230, by rfl⟩ : syracuseStep 3648307 = 5472461) B5472461
theorem B4864409 : Blo 2161435 4864409 := bstep (se 2 (by rfl) ⟨1824153, by rfl⟩ : syracuseStep 4864409 = 3648307) B3648307
theorem B3242939 : Blo 2161435 3242939 := bstep (se 1 (by rfl) ⟨2432204, by rfl⟩ : syracuseStep 3242939 = 4864409) B4864409
theorem B2161959 : Blo 2161435 2161959 := bstep (se 1 (by rfl) ⟨1621469, by rfl⟩ : syracuseStep 2161959 = 3242939) B3242939
theorem B2432209 : Blo 2161435 2432209 := bbase (se 2 (by rfl) ⟨912078, by rfl⟩ : syracuseStep 2432209 = 1824157) (by norm_num)
theorem B3242945 : Blo 2161435 3242945 := bstep (se 2 (by rfl) ⟨1216104, by rfl⟩ : syracuseStep 3242945 = 2432209) B2432209
theorem B2161963 : Blo 2161435 2161963 := bstep (se 1 (by rfl) ⟨1621472, by rfl⟩ : syracuseStep 2161963 = 3242945) B3242945
theorem B11094293 : Blo 2161435 11094293 := bbase (se 6 (by rfl) ⟨260022, by rfl⟩ : syracuseStep 11094293 = 520045) (by norm_num)
theorem B7396195 : Blo 2161435 7396195 := bstep (se 1 (by rfl) ⟨5547146, by rfl⟩ : syracuseStep 7396195 = 11094293) B11094293
theorem B9861593 : Blo 2161435 9861593 := bstep (se 2 (by rfl) ⟨3698097, by rfl⟩ : syracuseStep 9861593 = 7396195) B7396195
theorem B26297581 : Blo 2161435 26297581 := bstep (se 3 (by rfl) ⟨4930796, by rfl⟩ : syracuseStep 26297581 = 9861593) B9861593
theorem B35063441 : Blo 2161435 35063441 := bstep (se 2 (by rfl) ⟨13148790, by rfl⟩ : syracuseStep 35063441 = 26297581) B26297581
theorem B23375627 : Blo 2161435 23375627 := bstep (se 1 (by rfl) ⟨17531720, by rfl⟩ : syracuseStep 23375627 = 35063441) B35063441
theorem B15583751 : Blo 2161435 15583751 := bstep (se 1 (by rfl) ⟨11687813, by rfl⟩ : syracuseStep 15583751 = 23375627) B23375627
theorem B10389167 : Blo 2161435 10389167 := bstep (se 1 (by rfl) ⟨7791875, by rfl⟩ : syracuseStep 10389167 = 15583751) B15583751
theorem B6926111 : Blo 2161435 6926111 := bstep (se 1 (by rfl) ⟨5194583, by rfl⟩ : syracuseStep 6926111 = 10389167) B10389167
theorem B4617407 : Blo 2161435 4617407 := bstep (se 1 (by rfl) ⟨3463055, by rfl⟩ : syracuseStep 4617407 = 6926111) B6926111
theorem B3078271 : Blo 2161435 3078271 := bstep (se 1 (by rfl) ⟨2308703, by rfl⟩ : syracuseStep 3078271 = 4617407) B4617407
theorem B4104361 : Blo 2161435 4104361 := bstep (se 2 (by rfl) ⟨1539135, by rfl⟩ : syracuseStep 4104361 = 3078271) B3078271
theorem B5472481 : Blo 2161435 5472481 := bstep (se 2 (by rfl) ⟨2052180, by rfl⟩ : syracuseStep 5472481 = 4104361) B4104361
theorem B7296641 : Blo 2161435 7296641 := bstep (se 2 (by rfl) ⟨2736240, by rfl⟩ : syracuseStep 7296641 = 5472481) B5472481
theorem B4864427 : Blo 2161435 4864427 := bstep (se 1 (by rfl) ⟨3648320, by rfl⟩ : syracuseStep 4864427 = 7296641) B7296641
theorem B3242951 : Blo 2161435 3242951 := bstep (se 1 (by rfl) ⟨2432213, by rfl⟩ : syracuseStep 3242951 = 4864427) B4864427
theorem B2161967 : Blo 2161435 2161967 := bstep (se 1 (by rfl) ⟨1621475, by rfl⟩ : syracuseStep 2161967 = 3242951) B3242951
theorem B3242957 : Blo 2161435 3242957 := bbase (se 3 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 3242957 = 1216109) (by norm_num)
theorem B2161971 : Blo 2161435 2161971 := bstep (se 1 (by rfl) ⟨1621478, by rfl⟩ : syracuseStep 2161971 = 3242957) B3242957
theorem B4864445 : Blo 2161435 4864445 := bbase (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) (by norm_num)
theorem B3242963 : Blo 2161435 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B2161975 : Blo 2161435 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B3648341 : Blo 2161435 3648341 := bbase (se 9 (by rfl) ⟨10688, by rfl⟩ : syracuseStep 3648341 = 21377) (by norm_num)
theorem B2432227 : Blo 2161435 2432227 := bstep (se 1 (by rfl) ⟨1824170, by rfl⟩ : syracuseStep 2432227 = 3648341) B3648341
theorem B3242969 : Blo 2161435 3242969 := bstep (se 2 (by rfl) ⟨1216113, by rfl⟩ : syracuseStep 3242969 = 2432227) B2432227
theorem B2161979 : Blo 2161435 2161979 := bstep (se 1 (by rfl) ⟨1621484, by rfl⟩ : syracuseStep 2161979 = 3242969) B3242969
theorem B5194621 : Blo 2161435 5194621 := bbase (se 3 (by rfl) ⟨973991, by rfl⟩ : syracuseStep 5194621 = 1947983) (by norm_num)
theorem B6926161 : Blo 2161435 6926161 := bstep (se 2 (by rfl) ⟨2597310, by rfl⟩ : syracuseStep 6926161 = 5194621) B5194621
theorem B9234881 : Blo 2161435 9234881 := bstep (se 2 (by rfl) ⟨3463080, by rfl⟩ : syracuseStep 9234881 = 6926161) B6926161
theorem B6156587 : Blo 2161435 6156587 := bstep (se 1 (by rfl) ⟨4617440, by rfl⟩ : syracuseStep 6156587 = 9234881) B9234881
theorem B16417565 : Blo 2161435 16417565 := bstep (se 3 (by rfl) ⟨3078293, by rfl⟩ : syracuseStep 16417565 = 6156587) B6156587
theorem B10945043 : Blo 2161435 10945043 := bstep (se 1 (by rfl) ⟨8208782, by rfl⟩ : syracuseStep 10945043 = 16417565) B16417565
theorem B7296695 : Blo 2161435 7296695 := bstep (se 1 (by rfl) ⟨5472521, by rfl⟩ : syracuseStep 7296695 = 10945043) B10945043
theorem B4864463 : Blo 2161435 4864463 := bstep (se 1 (by rfl) ⟨3648347, by rfl⟩ : syracuseStep 4864463 = 7296695) B7296695
theorem B3242975 : Blo 2161435 3242975 := bstep (se 1 (by rfl) ⟨2432231, by rfl⟩ : syracuseStep 3242975 = 4864463) B4864463
theorem B2161983 : Blo 2161435 2161983 := bstep (se 1 (by rfl) ⟨1621487, by rfl⟩ : syracuseStep 2161983 = 3242975) B3242975
theorem B3242981 : Blo 2161435 3242981 := bbase (se 4 (by rfl) ⟨304029, by rfl⟩ : syracuseStep 3242981 = 608059) (by norm_num)
theorem B2161987 : Blo 2161435 2161987 := bstep (se 1 (by rfl) ⟨1621490, by rfl⟩ : syracuseStep 2161987 = 3242981) B3242981
theorem B9234917 : Blo 2161435 9234917 := bbase (se 4 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 9234917 = 1731547) (by norm_num)
theorem B6156611 : Blo 2161435 6156611 := bstep (se 1 (by rfl) ⟨4617458, by rfl⟩ : syracuseStep 6156611 = 9234917) B9234917
theorem B4104407 : Blo 2161435 4104407 := bstep (se 1 (by rfl) ⟨3078305, by rfl⟩ : syracuseStep 4104407 = 6156611) B6156611
theorem B2736271 : Blo 2161435 2736271 := bstep (se 1 (by rfl) ⟨2052203, by rfl⟩ : syracuseStep 2736271 = 4104407) B4104407
theorem B3648361 : Blo 2161435 3648361 := bstep (se 2 (by rfl) ⟨1368135, by rfl⟩ : syracuseStep 3648361 = 2736271) B2736271
theorem B4864481 : Blo 2161435 4864481 := bstep (se 2 (by rfl) ⟨1824180, by rfl⟩ : syracuseStep 4864481 = 3648361) B3648361
theorem B3242987 : Blo 2161435 3242987 := bstep (se 1 (by rfl) ⟨2432240, by rfl⟩ : syracuseStep 3242987 = 4864481) B4864481
theorem B2161991 : Blo 2161435 2161991 := bstep (se 1 (by rfl) ⟨1621493, by rfl⟩ : syracuseStep 2161991 = 3242987) B3242987
theorem B2432245 : Blo 2161435 2432245 := bbase (se 5 (by rfl) ⟨114011, by rfl⟩ : syracuseStep 2432245 = 228023) (by norm_num)
theorem B3242993 : Blo 2161435 3242993 := bstep (se 2 (by rfl) ⟨1216122, by rfl⟩ : syracuseStep 3242993 = 2432245) B2432245
theorem B2161995 : Blo 2161435 2161995 := bstep (se 1 (by rfl) ⟨1621496, by rfl⟩ : syracuseStep 2161995 = 3242993) B3242993
theorem B2736281 : Blo 2161435 2736281 := bbase (se 2 (by rfl) ⟨1026105, by rfl⟩ : syracuseStep 2736281 = 2052211) (by norm_num)
theorem B7296749 : Blo 2161435 7296749 := bstep (se 3 (by rfl) ⟨1368140, by rfl⟩ : syracuseStep 7296749 = 2736281) B2736281
theorem B4864499 : Blo 2161435 4864499 := bstep (se 1 (by rfl) ⟨3648374, by rfl⟩ : syracuseStep 4864499 = 7296749) B7296749
theorem B3242999 : Blo 2161435 3242999 := bstep (se 1 (by rfl) ⟨2432249, by rfl⟩ : syracuseStep 3242999 = 4864499) B4864499
theorem B2161999 : Blo 2161435 2161999 := bstep (se 1 (by rfl) ⟨1621499, by rfl⟩ : syracuseStep 2161999 = 3242999) B3242999
theorem B3243005 : Blo 2161435 3243005 := bbase (se 3 (by rfl) ⟨608063, by rfl⟩ : syracuseStep 3243005 = 1216127) (by norm_num)
theorem B2162003 : Blo 2161435 2162003 := bstep (se 1 (by rfl) ⟨1621502, by rfl⟩ : syracuseStep 2162003 = 3243005) B3243005
theorem B4864517 : Blo 2161435 4864517 := bbase (se 4 (by rfl) ⟨456048, by rfl⟩ : syracuseStep 4864517 = 912097) (by norm_num)
theorem B3243011 : Blo 2161435 3243011 := bstep (se 1 (by rfl) ⟨2432258, by rfl⟩ : syracuseStep 3243011 = 4864517) B4864517
theorem B2162007 : Blo 2161435 2162007 := bstep (se 1 (by rfl) ⟨1621505, by rfl⟩ : syracuseStep 2162007 = 3243011) B3243011
theorem B4104445 : Blo 2161435 4104445 := bbase (se 3 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 4104445 = 1539167) (by norm_num)
theorem B5472593 : Blo 2161435 5472593 := bstep (se 2 (by rfl) ⟨2052222, by rfl⟩ : syracuseStep 5472593 = 4104445) B4104445
theorem B3648395 : Blo 2161435 3648395 := bstep (se 1 (by rfl) ⟨2736296, by rfl⟩ : syracuseStep 3648395 = 5472593) B5472593
theorem B2432263 : Blo 2161435 2432263 := bstep (se 1 (by rfl) ⟨1824197, by rfl⟩ : syracuseStep 2432263 = 3648395) B3648395
theorem B3243017 : Blo 2161435 3243017 := bstep (se 2 (by rfl) ⟨1216131, by rfl⟩ : syracuseStep 3243017 = 2432263) B2432263
theorem B2162011 : Blo 2161435 2162011 := bstep (se 1 (by rfl) ⟨1621508, by rfl⟩ : syracuseStep 2162011 = 3243017) B3243017
theorem B10945205 : Blo 2161435 10945205 := bbase (se 5 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 10945205 = 1026113) (by norm_num)
theorem B7296803 : Blo 2161435 7296803 := bstep (se 1 (by rfl) ⟨5472602, by rfl⟩ : syracuseStep 7296803 = 10945205) B10945205
theorem B4864535 : Blo 2161435 4864535 := bstep (se 1 (by rfl) ⟨3648401, by rfl⟩ : syracuseStep 4864535 = 7296803) B7296803
theorem B3243023 : Blo 2161435 3243023 := bstep (se 1 (by rfl) ⟨2432267, by rfl⟩ : syracuseStep 3243023 = 4864535) B4864535
theorem B2162015 : Blo 2161435 2162015 := bstep (se 1 (by rfl) ⟨1621511, by rfl⟩ : syracuseStep 2162015 = 3243023) B3243023
theorem B3243029 : Blo 2161435 3243029 := bbase (se 6 (by rfl) ⟨76008, by rfl⟩ : syracuseStep 3243029 = 152017) (by norm_num)
theorem B2162019 : Blo 2161435 2162019 := bstep (se 1 (by rfl) ⟨1621514, by rfl⟩ : syracuseStep 2162019 = 3243029) B3243029
theorem B20778869 : Blo 2161435 20778869 := bbase (se 5 (by rfl) ⟨974009, by rfl⟩ : syracuseStep 20778869 = 1948019) (by norm_num)
theorem B13852579 : Blo 2161435 13852579 := bstep (se 1 (by rfl) ⟨10389434, by rfl⟩ : syracuseStep 13852579 = 20778869) B20778869
theorem B18470105 : Blo 2161435 18470105 := bstep (se 2 (by rfl) ⟨6926289, by rfl⟩ : syracuseStep 18470105 = 13852579) B13852579
theorem B12313403 : Blo 2161435 12313403 := bstep (se 1 (by rfl) ⟨9235052, by rfl⟩ : syracuseStep 12313403 = 18470105) B18470105
theorem B8208935 : Blo 2161435 8208935 := bstep (se 1 (by rfl) ⟨6156701, by rfl⟩ : syracuseStep 8208935 = 12313403) B12313403
theorem B5472623 : Blo 2161435 5472623 := bstep (se 1 (by rfl) ⟨4104467, by rfl⟩ : syracuseStep 5472623 = 8208935) B8208935
theorem B3648415 : Blo 2161435 3648415 := bstep (se 1 (by rfl) ⟨2736311, by rfl⟩ : syracuseStep 3648415 = 5472623) B5472623
theorem B4864553 : Blo 2161435 4864553 := bstep (se 2 (by rfl) ⟨1824207, by rfl⟩ : syracuseStep 4864553 = 3648415) B3648415
theorem B3243035 : Blo 2161435 3243035 := bstep (se 1 (by rfl) ⟨2432276, by rfl⟩ : syracuseStep 3243035 = 4864553) B4864553
theorem B2162023 : Blo 2161435 2162023 := bstep (se 1 (by rfl) ⟨1621517, by rfl⟩ : syracuseStep 2162023 = 3243035) B3243035
theorem B2432281 : Blo 2161435 2432281 := bbase (se 2 (by rfl) ⟨912105, by rfl⟩ : syracuseStep 2432281 = 1824211) (by norm_num)
theorem B3243041 : Blo 2161435 3243041 := bstep (se 2 (by rfl) ⟨1216140, by rfl⟩ : syracuseStep 3243041 = 2432281) B2432281
theorem B2162027 : Blo 2161435 2162027 := bstep (se 1 (by rfl) ⟨1621520, by rfl⟩ : syracuseStep 2162027 = 3243041) B3243041
theorem B8208965 : Blo 2161435 8208965 := bbase (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) (by norm_num)
theorem B5472643 : Blo 2161435 5472643 := bstep (se 1 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 5472643 = 8208965) B8208965
theorem B7296857 : Blo 2161435 7296857 := bstep (se 2 (by rfl) ⟨2736321, by rfl⟩ : syracuseStep 7296857 = 5472643) B5472643
theorem B4864571 : Blo 2161435 4864571 := bstep (se 1 (by rfl) ⟨3648428, by rfl⟩ : syracuseStep 4864571 = 7296857) B7296857
theorem B3243047 : Blo 2161435 3243047 := bstep (se 1 (by rfl) ⟨2432285, by rfl⟩ : syracuseStep 3243047 = 4864571) B4864571
theorem B2162031 : Blo 2161435 2162031 := bstep (se 1 (by rfl) ⟨1621523, by rfl⟩ : syracuseStep 2162031 = 3243047) B3243047
theorem B3243053 : Blo 2161435 3243053 := bbase (se 3 (by rfl) ⟨608072, by rfl⟩ : syracuseStep 3243053 = 1216145) (by norm_num)
theorem B2162035 : Blo 2161435 2162035 := bstep (se 1 (by rfl) ⟨1621526, by rfl⟩ : syracuseStep 2162035 = 3243053) B3243053
theorem B4864589 : Blo 2161435 4864589 := bbase (se 3 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 4864589 = 1824221) (by norm_num)
theorem B3243059 : Blo 2161435 3243059 := bstep (se 1 (by rfl) ⟨2432294, by rfl⟩ : syracuseStep 3243059 = 4864589) B4864589
theorem B2162039 : Blo 2161435 2162039 := bstep (se 1 (by rfl) ⟨1621529, by rfl⟩ : syracuseStep 2162039 = 3243059) B3243059
theorem B2736337 : Blo 2161435 2736337 := bbase (se 2 (by rfl) ⟨1026126, by rfl⟩ : syracuseStep 2736337 = 2052253) (by norm_num)
theorem B3648449 : Blo 2161435 3648449 := bstep (se 2 (by rfl) ⟨1368168, by rfl⟩ : syracuseStep 3648449 = 2736337) B2736337
theorem B2432299 : Blo 2161435 2432299 := bstep (se 1 (by rfl) ⟨1824224, by rfl⟩ : syracuseStep 2432299 = 3648449) B3648449
theorem B3243065 : Blo 2161435 3243065 := bstep (se 2 (by rfl) ⟨1216149, by rfl⟩ : syracuseStep 3243065 = 2432299) B2432299
theorem B2162043 : Blo 2161435 2162043 := bstep (se 1 (by rfl) ⟨1621532, by rfl⟩ : syracuseStep 2162043 = 3243065) B3243065
theorem B11688245 : Blo 2161435 11688245 := bbase (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) (by norm_num)
theorem B7792163 : Blo 2161435 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B5194775 : Blo 2161435 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B3463183 : Blo 2161435 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B4617577 : Blo 2161435 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B24627077 : Blo 2161435 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B16418051 : Blo 2161435 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B10945367 : Blo 2161435 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B7296911 : Blo 2161435 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B4864607 : Blo 2161435 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B3243071 : Blo 2161435 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B2162047 : Blo 2161435 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B3243077 : Blo 2161435 3243077 := bbase (se 4 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 3243077 = 608077) (by norm_num)
theorem B2162051 : Blo 2161435 2162051 := bstep (se 1 (by rfl) ⟨1621538, by rfl⟩ : syracuseStep 2162051 = 3243077) B3243077
theorem B3648469 : Blo 2161435 3648469 := bbase (se 7 (by rfl) ⟨42755, by rfl⟩ : syracuseStep 3648469 = 85511) (by norm_num)
theorem B4864625 : Blo 2161435 4864625 := bstep (se 2 (by rfl) ⟨1824234, by rfl⟩ : syracuseStep 4864625 = 3648469) B3648469
theorem B3243083 : Blo 2161435 3243083 := bstep (se 1 (by rfl) ⟨2432312, by rfl⟩ : syracuseStep 3243083 = 4864625) B4864625
theorem B2162055 : Blo 2161435 2162055 := bstep (se 1 (by rfl) ⟨1621541, by rfl⟩ : syracuseStep 2162055 = 3243083) B3243083
theorem B2432317 : Blo 2161435 2432317 := bbase (se 3 (by rfl) ⟨456059, by rfl⟩ : syracuseStep 2432317 = 912119) (by norm_num)
theorem B3243089 : Blo 2161435 3243089 := bstep (se 2 (by rfl) ⟨1216158, by rfl⟩ : syracuseStep 3243089 = 2432317) B2432317
theorem B2162059 : Blo 2161435 2162059 := bstep (se 1 (by rfl) ⟨1621544, by rfl⟩ : syracuseStep 2162059 = 3243089) B3243089
theorem B7296965 : Blo 2161435 7296965 := bbase (se 4 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 7296965 = 1368181) (by norm_num)
theorem B4864643 : Blo 2161435 4864643 := bstep (se 1 (by rfl) ⟨3648482, by rfl⟩ : syracuseStep 4864643 = 7296965) B7296965
theorem B3243095 : Blo 2161435 3243095 := bstep (se 1 (by rfl) ⟨2432321, by rfl⟩ : syracuseStep 3243095 = 4864643) B4864643
theorem B2162063 : Blo 2161435 2162063 := bstep (se 1 (by rfl) ⟨1621547, by rfl⟩ : syracuseStep 2162063 = 3243095) B3243095
theorem B3243101 : Blo 2161435 3243101 := bbase (se 3 (by rfl) ⟨608081, by rfl⟩ : syracuseStep 3243101 = 1216163) (by norm_num)
theorem B2162067 : Blo 2161435 2162067 := bstep (se 1 (by rfl) ⟨1621550, by rfl⟩ : syracuseStep 2162067 = 3243101) B3243101
theorem B4864661 : Blo 2161435 4864661 := bbase (se 6 (by rfl) ⟨114015, by rfl⟩ : syracuseStep 4864661 = 228031) (by norm_num)
theorem B3243107 : Blo 2161435 3243107 := bstep (se 1 (by rfl) ⟨2432330, by rfl⟩ : syracuseStep 3243107 = 4864661) B4864661
theorem B2162071 : Blo 2161435 2162071 := bstep (se 1 (by rfl) ⟨1621553, by rfl⟩ : syracuseStep 2162071 = 3243107) B3243107
theorem B3463229 : Blo 2161435 3463229 := bbase (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) (by norm_num)
theorem B2308819 : Blo 2161435 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B3078425 : Blo 2161435 3078425 := bstep (se 2 (by rfl) ⟨1154409, by rfl⟩ : syracuseStep 3078425 = 2308819) B2308819
theorem B8209133 : Blo 2161435 8209133 := bstep (se 3 (by rfl) ⟨1539212, by rfl⟩ : syracuseStep 8209133 = 3078425) B3078425
theorem B5472755 : Blo 2161435 5472755 := bstep (se 1 (by rfl) ⟨4104566, by rfl⟩ : syracuseStep 5472755 = 8209133) B8209133
theorem B3648503 : Blo 2161435 3648503 := bstep (se 1 (by rfl) ⟨2736377, by rfl⟩ : syracuseStep 3648503 = 5472755) B5472755
theorem B2432335 : Blo 2161435 2432335 := bstep (se 1 (by rfl) ⟨1824251, by rfl⟩ : syracuseStep 2432335 = 3648503) B3648503
theorem B3243113 : Blo 2161435 3243113 := bstep (se 2 (by rfl) ⟨1216167, by rfl⟩ : syracuseStep 3243113 = 2432335) B2432335
theorem B2162075 : Blo 2161435 2162075 := bstep (se 1 (by rfl) ⟨1621556, by rfl⟩ : syracuseStep 2162075 = 3243113) B3243113
theorem B4217341 : Blo 2161435 4217341 := bbase (se 3 (by rfl) ⟨790751, by rfl⟩ : syracuseStep 4217341 = 1581503) (by norm_num)
theorem B5623121 : Blo 2161435 5623121 := bstep (se 2 (by rfl) ⟨2108670, by rfl⟩ : syracuseStep 5623121 = 4217341) B4217341
theorem B14994989 : Blo 2161435 14994989 := bstep (se 3 (by rfl) ⟨2811560, by rfl⟩ : syracuseStep 14994989 = 5623121) B5623121
theorem B9996659 : Blo 2161435 9996659 := bstep (se 1 (by rfl) ⟨7497494, by rfl⟩ : syracuseStep 9996659 = 14994989) B14994989
theorem B6664439 : Blo 2161435 6664439 := bstep (se 1 (by rfl) ⟨4998329, by rfl⟩ : syracuseStep 6664439 = 9996659) B9996659
theorem B4442959 : Blo 2161435 4442959 := bstep (se 1 (by rfl) ⟨3332219, by rfl⟩ : syracuseStep 4442959 = 6664439) B6664439
theorem B5923945 : Blo 2161435 5923945 := bstep (se 2 (by rfl) ⟨2221479, by rfl⟩ : syracuseStep 5923945 = 4442959) B4442959
theorem B31594373 : Blo 2161435 31594373 := bstep (se 4 (by rfl) ⟨2961972, by rfl⟩ : syracuseStep 31594373 = 5923945) B5923945
theorem B21062915 : Blo 2161435 21062915 := bstep (se 1 (by rfl) ⟨15797186, by rfl⟩ : syracuseStep 21062915 = 31594373) B31594373
theorem B14041943 : Blo 2161435 14041943 := bstep (se 1 (by rfl) ⟨10531457, by rfl⟩ : syracuseStep 14041943 = 21062915) B21062915
theorem B9361295 : Blo 2161435 9361295 := bstep (se 1 (by rfl) ⟨7020971, by rfl⟩ : syracuseStep 9361295 = 14041943) B14041943
theorem B6240863 : Blo 2161435 6240863 := bstep (se 1 (by rfl) ⟨4680647, by rfl⟩ : syracuseStep 6240863 = 9361295) B9361295
theorem B4160575 : Blo 2161435 4160575 := bstep (se 1 (by rfl) ⟨3120431, by rfl⟩ : syracuseStep 4160575 = 6240863) B6240863
theorem B5547433 : Blo 2161435 5547433 := bstep (se 2 (by rfl) ⟨2080287, by rfl⟩ : syracuseStep 5547433 = 4160575) B4160575
theorem B7396577 : Blo 2161435 7396577 := bstep (se 2 (by rfl) ⟨2773716, by rfl⟩ : syracuseStep 7396577 = 5547433) B5547433
theorem B4931051 : Blo 2161435 4931051 := bstep (se 1 (by rfl) ⟨3698288, by rfl⟩ : syracuseStep 4931051 = 7396577) B7396577
theorem B13149469 : Blo 2161435 13149469 := bstep (se 3 (by rfl) ⟨2465525, by rfl⟩ : syracuseStep 13149469 = 4931051) B4931051
theorem B17532625 : Blo 2161435 17532625 := bstep (se 2 (by rfl) ⟨6574734, by rfl⟩ : syracuseStep 17532625 = 13149469) B13149469
theorem B23376833 : Blo 2161435 23376833 := bstep (se 2 (by rfl) ⟨8766312, by rfl⟩ : syracuseStep 23376833 = 17532625) B17532625
theorem B15584555 : Blo 2161435 15584555 := bstep (se 1 (by rfl) ⟨11688416, by rfl⟩ : syracuseStep 15584555 = 23376833) B23376833
theorem B10389703 : Blo 2161435 10389703 := bstep (se 1 (by rfl) ⟨7792277, by rfl⟩ : syracuseStep 10389703 = 15584555) B15584555
theorem B13852937 : Blo 2161435 13852937 := bstep (se 2 (by rfl) ⟨5194851, by rfl⟩ : syracuseStep 13852937 = 10389703) B10389703
theorem B9235291 : Blo 2161435 9235291 := bstep (se 1 (by rfl) ⟨6926468, by rfl⟩ : syracuseStep 9235291 = 13852937) B13852937
theorem B12313721 : Blo 2161435 12313721 := bstep (se 2 (by rfl) ⟨4617645, by rfl⟩ : syracuseStep 12313721 = 9235291) B9235291
theorem B8209147 : Blo 2161435 8209147 := bstep (se 1 (by rfl) ⟨6156860, by rfl⟩ : syracuseStep 8209147 = 12313721) B12313721
theorem B10945529 : Blo 2161435 10945529 := bstep (se 2 (by rfl) ⟨4104573, by rfl⟩ : syracuseStep 10945529 = 8209147) B8209147
theorem B7297019 : Blo 2161435 7297019 := bstep (se 1 (by rfl) ⟨5472764, by rfl⟩ : syracuseStep 7297019 = 10945529) B10945529
theorem B4864679 : Blo 2161435 4864679 := bstep (se 1 (by rfl) ⟨3648509, by rfl⟩ : syracuseStep 4864679 = 7297019) B7297019
theorem B3243119 : Blo 2161435 3243119 := bstep (se 1 (by rfl) ⟨2432339, by rfl⟩ : syracuseStep 3243119 = 4864679) B4864679
theorem B2162079 : Blo 2161435 2162079 := bstep (se 1 (by rfl) ⟨1621559, by rfl⟩ : syracuseStep 2162079 = 3243119) B3243119
theorem B3243125 : Blo 2161435 3243125 := bbase (se 5 (by rfl) ⟨152021, by rfl⟩ : syracuseStep 3243125 = 304043) (by norm_num)
theorem B2162083 : Blo 2161435 2162083 := bstep (se 1 (by rfl) ⟨1621562, by rfl⟩ : syracuseStep 2162083 = 3243125) B3243125
theorem B4104589 : Blo 2161435 4104589 := bbase (se 3 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 4104589 = 1539221) (by norm_num)
theorem B5472785 : Blo 2161435 5472785 := bstep (se 2 (by rfl) ⟨2052294, by rfl⟩ : syracuseStep 5472785 = 4104589) B4104589
theorem B3648523 : Blo 2161435 3648523 := bstep (se 1 (by rfl) ⟨2736392, by rfl⟩ : syracuseStep 3648523 = 5472785) B5472785
theorem B4864697 : Blo 2161435 4864697 := bstep (se 2 (by rfl) ⟨1824261, by rfl⟩ : syracuseStep 4864697 = 3648523) B3648523
theorem B3243131 : Blo 2161435 3243131 := bstep (se 1 (by rfl) ⟨2432348, by rfl⟩ : syracuseStep 3243131 = 4864697) B4864697
theorem B2162087 : Blo 2161435 2162087 := bstep (se 1 (by rfl) ⟨1621565, by rfl⟩ : syracuseStep 2162087 = 3243131) B3243131
theorem B2432353 : Blo 2161435 2432353 := bbase (se 2 (by rfl) ⟨912132, by rfl⟩ : syracuseStep 2432353 = 1824265) (by norm_num)
theorem B3243137 : Blo 2161435 3243137 := bstep (se 2 (by rfl) ⟨1216176, by rfl⟩ : syracuseStep 3243137 = 2432353) B2432353
theorem B2162091 : Blo 2161435 2162091 := bstep (se 1 (by rfl) ⟨1621568, by rfl⟩ : syracuseStep 2162091 = 3243137) B3243137
theorem B5472805 : Blo 2161435 5472805 := bbase (se 4 (by rfl) ⟨513075, by rfl⟩ : syracuseStep 5472805 = 1026151) (by norm_num)
theorem B7297073 : Blo 2161435 7297073 := bstep (se 2 (by rfl) ⟨2736402, by rfl⟩ : syracuseStep 7297073 = 5472805) B5472805
theorem B4864715 : Blo 2161435 4864715 := bstep (se 1 (by rfl) ⟨3648536, by rfl⟩ : syracuseStep 4864715 = 7297073) B7297073
theorem B3243143 : Blo 2161435 3243143 := bstep (se 1 (by rfl) ⟨2432357, by rfl⟩ : syracuseStep 3243143 = 4864715) B4864715
theorem B2162095 : Blo 2161435 2162095 := bstep (se 1 (by rfl) ⟨1621571, by rfl⟩ : syracuseStep 2162095 = 3243143) B3243143
theorem B3243149 : Blo 2161435 3243149 := bbase (se 3 (by rfl) ⟨608090, by rfl⟩ : syracuseStep 3243149 = 1216181) (by norm_num)
theorem B2162099 : Blo 2161435 2162099 := bstep (se 1 (by rfl) ⟨1621574, by rfl⟩ : syracuseStep 2162099 = 3243149) B3243149
theorem B4864733 : Blo 2161435 4864733 := bbase (se 3 (by rfl) ⟨912137, by rfl⟩ : syracuseStep 4864733 = 1824275) (by norm_num)
theorem B3243155 : Blo 2161435 3243155 := bstep (se 1 (by rfl) ⟨2432366, by rfl⟩ : syracuseStep 3243155 = 4864733) B4864733
theorem B2162103 : Blo 2161435 2162103 := bstep (se 1 (by rfl) ⟨1621577, by rfl⟩ : syracuseStep 2162103 = 3243155) B3243155
theorem B3648557 : Blo 2161435 3648557 := bbase (se 3 (by rfl) ⟨684104, by rfl⟩ : syracuseStep 3648557 = 1368209) (by norm_num)
theorem B2432371 : Blo 2161435 2432371 := bstep (se 1 (by rfl) ⟨1824278, by rfl⟩ : syracuseStep 2432371 = 3648557) B3648557
theorem B3243161 : Blo 2161435 3243161 := bstep (se 2 (by rfl) ⟨1216185, by rfl⟩ : syracuseStep 3243161 = 2432371) B2432371
theorem B2162107 : Blo 2161435 2162107 := bstep (se 1 (by rfl) ⟨1621580, by rfl⟩ : syracuseStep 2162107 = 3243161) B3243161
theorem B7615781 : Blo 2161435 7615781 := bbase (se 4 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 7615781 = 1427959) (by norm_num)
theorem B5077187 : Blo 2161435 5077187 := bstep (se 1 (by rfl) ⟨3807890, by rfl⟩ : syracuseStep 5077187 = 7615781) B7615781
theorem B3384791 : Blo 2161435 3384791 := bstep (se 1 (by rfl) ⟨2538593, by rfl⟩ : syracuseStep 3384791 = 5077187) B5077187
theorem B36104437 : Blo 2161435 36104437 := bstep (se 5 (by rfl) ⟨1692395, by rfl⟩ : syracuseStep 36104437 = 3384791) B3384791
theorem B192556997 : Blo 2161435 192556997 := bstep (se 4 (by rfl) ⟨18052218, by rfl⟩ : syracuseStep 192556997 = 36104437) B36104437
theorem B128371331 : Blo 2161435 128371331 := bstep (se 1 (by rfl) ⟨96278498, by rfl⟩ : syracuseStep 128371331 = 192556997) B192556997
theorem B85580887 : Blo 2161435 85580887 := bstep (se 1 (by rfl) ⟨64185665, by rfl⟩ : syracuseStep 85580887 = 128371331) B128371331
theorem B114107849 : Blo 2161435 114107849 := bstep (se 2 (by rfl) ⟨42790443, by rfl⟩ : syracuseStep 114107849 = 85580887) B85580887
theorem B76071899 : Blo 2161435 76071899 := bstep (se 1 (by rfl) ⟨57053924, by rfl⟩ : syracuseStep 76071899 = 114107849) B114107849
theorem B50714599 : Blo 2161435 50714599 := bstep (se 1 (by rfl) ⟨38035949, by rfl⟩ : syracuseStep 50714599 = 76071899) B76071899
theorem B67619465 : Blo 2161435 67619465 := bstep (se 2 (by rfl) ⟨25357299, by rfl⟩ : syracuseStep 67619465 = 50714599) B50714599
theorem B45079643 : Blo 2161435 45079643 := bstep (se 1 (by rfl) ⟨33809732, by rfl⟩ : syracuseStep 45079643 = 67619465) B67619465
theorem B120212381 : Blo 2161435 120212381 := bstep (se 3 (by rfl) ⟨22539821, by rfl⟩ : syracuseStep 120212381 = 45079643) B45079643
theorem B320566349 : Blo 2161435 320566349 := bstep (se 3 (by rfl) ⟨60106190, by rfl⟩ : syracuseStep 320566349 = 120212381) B120212381
theorem B213710899 : Blo 2161435 213710899 := bstep (se 1 (by rfl) ⟨160283174, by rfl⟩ : syracuseStep 213710899 = 320566349) B320566349
theorem B284947865 : Blo 2161435 284947865 := bstep (se 2 (by rfl) ⟨106855449, by rfl⟩ : syracuseStep 284947865 = 213710899) B213710899
theorem B189965243 : Blo 2161435 189965243 := bstep (se 1 (by rfl) ⟨142473932, by rfl⟩ : syracuseStep 189965243 = 284947865) B284947865
theorem B126643495 : Blo 2161435 126643495 := bstep (se 1 (by rfl) ⟨94982621, by rfl⟩ : syracuseStep 126643495 = 189965243) B189965243
theorem B168857993 : Blo 2161435 168857993 := bstep (se 2 (by rfl) ⟨63321747, by rfl⟩ : syracuseStep 168857993 = 126643495) B126643495
theorem B450287981 : Blo 2161435 450287981 := bstep (se 3 (by rfl) ⟨84428996, by rfl⟩ : syracuseStep 450287981 = 168857993) B168857993
theorem B300191987 : Blo 2161435 300191987 := bstep (se 1 (by rfl) ⟨225143990, by rfl⟩ : syracuseStep 300191987 = 450287981) B450287981
theorem B200127991 : Blo 2161435 200127991 := bstep (se 1 (by rfl) ⟨150095993, by rfl⟩ : syracuseStep 200127991 = 300191987) B300191987
theorem B266837321 : Blo 2161435 266837321 := bstep (se 2 (by rfl) ⟨100063995, by rfl⟩ : syracuseStep 266837321 = 200127991) B200127991
theorem B711566189 : Blo 2161435 711566189 := bstep (se 3 (by rfl) ⟨133418660, by rfl⟩ : syracuseStep 711566189 = 266837321) B266837321
theorem B30360157397 : Blo 2161435 30360157397 := bstep (se 7 (by rfl) ⟨355783094, by rfl⟩ : syracuseStep 30360157397 = 711566189) B711566189
theorem B20240104931 : Blo 2161435 20240104931 := bstep (se 1 (by rfl) ⟨15180078698, by rfl⟩ : syracuseStep 20240104931 = 30360157397) B30360157397
theorem B13493403287 : Blo 2161435 13493403287 := bstep (se 1 (by rfl) ⟨10120052465, by rfl⟩ : syracuseStep 13493403287 = 20240104931) B20240104931
theorem B8995602191 : Blo 2161435 8995602191 := bstep (se 1 (by rfl) ⟨6746701643, by rfl⟩ : syracuseStep 8995602191 = 13493403287) B13493403287
theorem B23988272509 : Blo 2161435 23988272509 := bstep (se 3 (by rfl) ⟨4497801095, by rfl⟩ : syracuseStep 23988272509 = 8995602191) B8995602191
theorem B31984363345 : Blo 2161435 31984363345 := bstep (se 2 (by rfl) ⟨11994136254, by rfl⟩ : syracuseStep 31984363345 = 23988272509) B23988272509
theorem B42645817793 : Blo 2161435 42645817793 := bstep (se 2 (by rfl) ⟨15992181672, by rfl⟩ : syracuseStep 42645817793 = 31984363345) B31984363345
theorem B28430545195 : Blo 2161435 28430545195 := bstep (se 1 (by rfl) ⟨21322908896, by rfl⟩ : syracuseStep 28430545195 = 42645817793) B42645817793
theorem B37907393593 : Blo 2161435 37907393593 := bstep (se 2 (by rfl) ⟨14215272597, by rfl⟩ : syracuseStep 37907393593 = 28430545195) B28430545195
theorem B50543191457 : Blo 2161435 50543191457 := bstep (se 2 (by rfl) ⟨18953696796, by rfl⟩ : syracuseStep 50543191457 = 37907393593) B37907393593
theorem B33695460971 : Blo 2161435 33695460971 := bstep (se 1 (by rfl) ⟨25271595728, by rfl⟩ : syracuseStep 33695460971 = 50543191457) B50543191457
theorem B22463640647 : Blo 2161435 22463640647 := bstep (se 1 (by rfl) ⟨16847730485, by rfl⟩ : syracuseStep 22463640647 = 33695460971) B33695460971
theorem B14975760431 : Blo 2161435 14975760431 := bstep (se 1 (by rfl) ⟨11231820323, by rfl⟩ : syracuseStep 14975760431 = 22463640647) B22463640647
theorem B9983840287 : Blo 2161435 9983840287 := bstep (se 1 (by rfl) ⟨7487880215, by rfl⟩ : syracuseStep 9983840287 = 14975760431) B14975760431
theorem B13311787049 : Blo 2161435 13311787049 := bstep (se 2 (by rfl) ⟨4991920143, by rfl⟩ : syracuseStep 13311787049 = 9983840287) B9983840287
theorem B8874524699 : Blo 2161435 8874524699 := bstep (se 1 (by rfl) ⟨6655893524, by rfl⟩ : syracuseStep 8874524699 = 13311787049) B13311787049
theorem B5916349799 : Blo 2161435 5916349799 := bstep (se 1 (by rfl) ⟨4437262349, by rfl⟩ : syracuseStep 5916349799 = 8874524699) B8874524699
theorem B3944233199 : Blo 2161435 3944233199 := bstep (se 1 (by rfl) ⟨2958174899, by rfl⟩ : syracuseStep 3944233199 = 5916349799) B5916349799
theorem B2629488799 : Blo 2161435 2629488799 := bstep (se 1 (by rfl) ⟨1972116599, by rfl⟩ : syracuseStep 2629488799 = 3944233199) B3944233199
theorem B3505985065 : Blo 2161435 3505985065 := bstep (se 2 (by rfl) ⟨1314744399, by rfl⟩ : syracuseStep 3505985065 = 2629488799) B2629488799
theorem B18698587013 : Blo 2161435 18698587013 := bstep (se 4 (by rfl) ⟨1752992532, by rfl⟩ : syracuseStep 18698587013 = 3505985065) B3505985065
theorem B12465724675 : Blo 2161435 12465724675 := bstep (se 1 (by rfl) ⟨9349293506, by rfl⟩ : syracuseStep 12465724675 = 18698587013) B18698587013
theorem B16620966233 : Blo 2161435 16620966233 := bstep (se 2 (by rfl) ⟨6232862337, by rfl⟩ : syracuseStep 16620966233 = 12465724675) B12465724675
theorem B11080644155 : Blo 2161435 11080644155 := bstep (se 1 (by rfl) ⟨8310483116, by rfl⟩ : syracuseStep 11080644155 = 16620966233) B16620966233
theorem B7387096103 : Blo 2161435 7387096103 := bstep (se 1 (by rfl) ⟨5540322077, by rfl⟩ : syracuseStep 7387096103 = 11080644155) B11080644155
theorem B4924730735 : Blo 2161435 4924730735 := bstep (se 1 (by rfl) ⟨3693548051, by rfl⟩ : syracuseStep 4924730735 = 7387096103) B7387096103
theorem B3283153823 : Blo 2161435 3283153823 := bstep (se 1 (by rfl) ⟨2462365367, by rfl⟩ : syracuseStep 3283153823 = 4924730735) B4924730735
theorem B2188769215 : Blo 2161435 2188769215 := bstep (se 1 (by rfl) ⟨1641576911, by rfl⟩ : syracuseStep 2188769215 = 3283153823) B3283153823
theorem B2918358953 : Blo 2161435 2918358953 := bstep (se 2 (by rfl) ⟨1094384607, by rfl⟩ : syracuseStep 2918358953 = 2188769215) B2188769215
theorem B1945572635 : Blo 2161435 1945572635 := bstep (se 1 (by rfl) ⟨1459179476, by rfl⟩ : syracuseStep 1945572635 = 2918358953) B2918358953
theorem B1297048423 : Blo 2161435 1297048423 := bstep (se 1 (by rfl) ⟨972786317, by rfl⟩ : syracuseStep 1297048423 = 1945572635) B1945572635
theorem B1729397897 : Blo 2161435 1729397897 := bstep (se 2 (by rfl) ⟨648524211, by rfl⟩ : syracuseStep 1729397897 = 1297048423) B1297048423
theorem B1152931931 : Blo 2161435 1152931931 := bstep (se 1 (by rfl) ⟨864698948, by rfl⟩ : syracuseStep 1152931931 = 1729397897) B1729397897
theorem B768621287 : Blo 2161435 768621287 := bstep (se 1 (by rfl) ⟨576465965, by rfl⟩ : syracuseStep 768621287 = 1152931931) B1152931931
theorem B512414191 : Blo 2161435 512414191 := bstep (se 1 (by rfl) ⟨384310643, by rfl⟩ : syracuseStep 512414191 = 768621287) B768621287
theorem B683218921 : Blo 2161435 683218921 := bstep (se 2 (by rfl) ⟨256207095, by rfl⟩ : syracuseStep 683218921 = 512414191) B512414191
theorem B910958561 : Blo 2161435 910958561 := bstep (se 2 (by rfl) ⟨341609460, by rfl⟩ : syracuseStep 910958561 = 683218921) B683218921
theorem B607305707 : Blo 2161435 607305707 := bstep (se 1 (by rfl) ⟨455479280, by rfl⟩ : syracuseStep 607305707 = 910958561) B910958561
theorem B404870471 : Blo 2161435 404870471 := bstep (se 1 (by rfl) ⟨303652853, by rfl⟩ : syracuseStep 404870471 = 607305707) B607305707
theorem B269913647 : Blo 2161435 269913647 := bstep (se 1 (by rfl) ⟨202435235, by rfl⟩ : syracuseStep 269913647 = 404870471) B404870471
theorem B179942431 : Blo 2161435 179942431 := bstep (se 1 (by rfl) ⟨134956823, by rfl⟩ : syracuseStep 179942431 = 269913647) B269913647
theorem B239923241 : Blo 2161435 239923241 := bstep (se 2 (by rfl) ⟨89971215, by rfl⟩ : syracuseStep 239923241 = 179942431) B179942431
theorem B159948827 : Blo 2161435 159948827 := bstep (se 1 (by rfl) ⟨119961620, by rfl⟩ : syracuseStep 159948827 = 239923241) B239923241
theorem B106632551 : Blo 2161435 106632551 := bstep (se 1 (by rfl) ⟨79974413, by rfl⟩ : syracuseStep 106632551 = 159948827) B159948827
theorem B71088367 : Blo 2161435 71088367 := bstep (se 1 (by rfl) ⟨53316275, by rfl⟩ : syracuseStep 71088367 = 106632551) B106632551
theorem B94784489 : Blo 2161435 94784489 := bstep (se 2 (by rfl) ⟨35544183, by rfl⟩ : syracuseStep 94784489 = 71088367) B71088367
theorem B63189659 : Blo 2161435 63189659 := bstep (se 1 (by rfl) ⟨47392244, by rfl⟩ : syracuseStep 63189659 = 94784489) B94784489
theorem B42126439 : Blo 2161435 42126439 := bstep (se 1 (by rfl) ⟨31594829, by rfl⟩ : syracuseStep 42126439 = 63189659) B63189659
theorem B56168585 : Blo 2161435 56168585 := bstep (se 2 (by rfl) ⟨21063219, by rfl⟩ : syracuseStep 56168585 = 42126439) B42126439
theorem B37445723 : Blo 2161435 37445723 := bstep (se 1 (by rfl) ⟨28084292, by rfl⟩ : syracuseStep 37445723 = 56168585) B56168585
theorem B24963815 : Blo 2161435 24963815 := bstep (se 1 (by rfl) ⟨18722861, by rfl⟩ : syracuseStep 24963815 = 37445723) B37445723
theorem B16642543 : Blo 2161435 16642543 := bstep (se 1 (by rfl) ⟨12481907, by rfl⟩ : syracuseStep 16642543 = 24963815) B24963815
theorem B22190057 : Blo 2161435 22190057 := bstep (se 2 (by rfl) ⟨8321271, by rfl⟩ : syracuseStep 22190057 = 16642543) B16642543
theorem B14793371 : Blo 2161435 14793371 := bstep (se 1 (by rfl) ⟨11095028, by rfl⟩ : syracuseStep 14793371 = 22190057) B22190057
theorem B9862247 : Blo 2161435 9862247 := bstep (se 1 (by rfl) ⟨7396685, by rfl⟩ : syracuseStep 9862247 = 14793371) B14793371
theorem B26299325 : Blo 2161435 26299325 := bstep (se 3 (by rfl) ⟨4931123, by rfl⟩ : syracuseStep 26299325 = 9862247) B9862247
theorem B17532883 : Blo 2161435 17532883 := bstep (se 1 (by rfl) ⟨13149662, by rfl⟩ : syracuseStep 17532883 = 26299325) B26299325
theorem B23377177 : Blo 2161435 23377177 := bstep (se 2 (by rfl) ⟨8766441, by rfl⟩ : syracuseStep 23377177 = 17532883) B17532883
theorem B31169569 : Blo 2161435 31169569 := bstep (se 2 (by rfl) ⟨11688588, by rfl⟩ : syracuseStep 31169569 = 23377177) B23377177
theorem B41559425 : Blo 2161435 41559425 := bstep (se 2 (by rfl) ⟨15584784, by rfl⟩ : syracuseStep 41559425 = 31169569) B31169569
theorem B27706283 : Blo 2161435 27706283 := bstep (se 1 (by rfl) ⟨20779712, by rfl⟩ : syracuseStep 27706283 = 41559425) B41559425
theorem B18470855 : Blo 2161435 18470855 := bstep (se 1 (by rfl) ⟨13853141, by rfl⟩ : syracuseStep 18470855 = 27706283) B27706283
theorem B12313903 : Blo 2161435 12313903 := bstep (se 1 (by rfl) ⟨9235427, by rfl⟩ : syracuseStep 12313903 = 18470855) B18470855
theorem B16418537 : Blo 2161435 16418537 := bstep (se 2 (by rfl) ⟨6156951, by rfl⟩ : syracuseStep 16418537 = 12313903) B12313903
theorem B10945691 : Blo 2161435 10945691 := bstep (se 1 (by rfl) ⟨8209268, by rfl⟩ : syracuseStep 10945691 = 16418537) B16418537
theorem B7297127 : Blo 2161435 7297127 := bstep (se 1 (by rfl) ⟨5472845, by rfl⟩ : syracuseStep 7297127 = 10945691) B10945691
theorem B4864751 : Blo 2161435 4864751 := bstep (se 1 (by rfl) ⟨3648563, by rfl⟩ : syracuseStep 4864751 = 7297127) B7297127
theorem B3243167 : Blo 2161435 3243167 := bstep (se 1 (by rfl) ⟨2432375, by rfl⟩ : syracuseStep 3243167 = 4864751) B4864751
theorem B2162111 : Blo 2161435 2162111 := bstep (se 1 (by rfl) ⟨1621583, by rfl⟩ : syracuseStep 2162111 = 3243167) B3243167
theorem B3243173 : Blo 2161435 3243173 := bbase (se 4 (by rfl) ⟨304047, by rfl⟩ : syracuseStep 3243173 = 608095) (by norm_num)
theorem B2162115 : Blo 2161435 2162115 := bstep (se 1 (by rfl) ⟨1621586, by rfl⟩ : syracuseStep 2162115 = 3243173) B3243173
theorem B2736433 : Blo 2161435 2736433 := bbase (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) (by norm_num)
theorem B3648577 : Blo 2161435 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B4864769 : Blo 2161435 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B3243179 : Blo 2161435 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B2162119 : Blo 2161435 2162119 := bstep (se 1 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 2162119 = 3243179) B3243179
theorem B2432389 : Blo 2161435 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B3243185 : Blo 2161435 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B2162123 : Blo 2161435 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B4617749 : Blo 2161435 4617749 := bbase (se 6 (by rfl) ⟨108228, by rfl⟩ : syracuseStep 4617749 = 216457) (by norm_num)
theorem B3078499 : Blo 2161435 3078499 := bstep (se 1 (by rfl) ⟨2308874, by rfl⟩ : syracuseStep 3078499 = 4617749) B4617749
theorem B4104665 : Blo 2161435 4104665 := bstep (se 2 (by rfl) ⟨1539249, by rfl⟩ : syracuseStep 4104665 = 3078499) B3078499
theorem B2736443 : Blo 2161435 2736443 := bstep (se 1 (by rfl) ⟨2052332, by rfl⟩ : syracuseStep 2736443 = 4104665) B4104665
theorem B7297181 : Blo 2161435 7297181 := bstep (se 3 (by rfl) ⟨1368221, by rfl⟩ : syracuseStep 7297181 = 2736443) B2736443
theorem B4864787 : Blo 2161435 4864787 := bstep (se 1 (by rfl) ⟨3648590, by rfl⟩ : syracuseStep 4864787 = 7297181) B7297181
theorem B3243191 : Blo 2161435 3243191 := bstep (se 1 (by rfl) ⟨2432393, by rfl⟩ : syracuseStep 3243191 = 4864787) B4864787
theorem B2162127 : Blo 2161435 2162127 := bstep (se 1 (by rfl) ⟨1621595, by rfl⟩ : syracuseStep 2162127 = 3243191) B3243191
theorem B3243197 : Blo 2161435 3243197 := bbase (se 3 (by rfl) ⟨608099, by rfl⟩ : syracuseStep 3243197 = 1216199) (by norm_num)
theorem B2162131 : Blo 2161435 2162131 := bstep (se 1 (by rfl) ⟨1621598, by rfl⟩ : syracuseStep 2162131 = 3243197) B3243197
theorem B4864805 : Blo 2161435 4864805 := bbase (se 4 (by rfl) ⟨456075, by rfl⟩ : syracuseStep 4864805 = 912151) (by norm_num)
theorem B3243203 : Blo 2161435 3243203 := bstep (se 1 (by rfl) ⟨2432402, by rfl⟩ : syracuseStep 3243203 = 4864805) B4864805
theorem B2162135 : Blo 2161435 2162135 := bstep (se 1 (by rfl) ⟨1621601, by rfl⟩ : syracuseStep 2162135 = 3243203) B3243203
theorem B5472917 : Blo 2161435 5472917 := bbase (se 6 (by rfl) ⟨128271, by rfl⟩ : syracuseStep 5472917 = 256543) (by norm_num)
theorem B3648611 : Blo 2161435 3648611 := bstep (se 1 (by rfl) ⟨2736458, by rfl⟩ : syracuseStep 3648611 = 5472917) B5472917
theorem B2432407 : Blo 2161435 2432407 := bstep (se 1 (by rfl) ⟨1824305, by rfl⟩ : syracuseStep 2432407 = 3648611) B3648611
theorem B3243209 : Blo 2161435 3243209 := bstep (se 2 (by rfl) ⟨1216203, by rfl⟩ : syracuseStep 3243209 = 2432407) B2432407
theorem B2162139 : Blo 2161435 2162139 := bstep (se 1 (by rfl) ⟨1621604, by rfl⟩ : syracuseStep 2162139 = 3243209) B3243209
theorem B37446293 : Blo 2161435 37446293 := bbase (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) (by norm_num)
theorem B24964195 : Blo 2161435 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B33285593 : Blo 2161435 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B22190395 : Blo 2161435 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B29587193 : Blo 2161435 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B19724795 : Blo 2161435 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B13149863 : Blo 2161435 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B8766575 : Blo 2161435 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B5844383 : Blo 2161435 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B3896255 : Blo 2161435 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B2597503 : Blo 2161435 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B3463337 : Blo 2161435 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B9235565 : Blo 2161435 9235565 := bstep (se 3 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 9235565 = 3463337) B3463337
theorem B6157043 : Blo 2161435 6157043 := bstep (se 1 (by rfl) ⟨4617782, by rfl⟩ : syracuseStep 6157043 = 9235565) B9235565
theorem B4104695 : Blo 2161435 4104695 := bstep (se 1 (by rfl) ⟨3078521, by rfl⟩ : syracuseStep 4104695 = 6157043) B6157043
theorem B10945853 : Blo 2161435 10945853 := bstep (se 3 (by rfl) ⟨2052347, by rfl⟩ : syracuseStep 10945853 = 4104695) B4104695
theorem B7297235 : Blo 2161435 7297235 := bstep (se 1 (by rfl) ⟨5472926, by rfl⟩ : syracuseStep 7297235 = 10945853) B10945853
theorem B4864823 : Blo 2161435 4864823 := bstep (se 1 (by rfl) ⟨3648617, by rfl⟩ : syracuseStep 4864823 = 7297235) B7297235
theorem B3243215 : Blo 2161435 3243215 := bstep (se 1 (by rfl) ⟨2432411, by rfl⟩ : syracuseStep 3243215 = 4864823) B4864823
theorem B2162143 : Blo 2161435 2162143 := bstep (se 1 (by rfl) ⟨1621607, by rfl⟩ : syracuseStep 2162143 = 3243215) B3243215
theorem B3243221 : Blo 2161435 3243221 := bbase (se 7 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 3243221 = 76013) (by norm_num)
theorem B2162147 : Blo 2161435 2162147 := bstep (se 1 (by rfl) ⟨1621610, by rfl⟩ : syracuseStep 2162147 = 3243221) B3243221
theorem B3078533 : Blo 2161435 3078533 := bbase (se 4 (by rfl) ⟨288612, by rfl⟩ : syracuseStep 3078533 = 577225) (by norm_num)
theorem B8209421 : Blo 2161435 8209421 := bstep (se 3 (by rfl) ⟨1539266, by rfl⟩ : syracuseStep 8209421 = 3078533) B3078533
theorem B5472947 : Blo 2161435 5472947 := bstep (se 1 (by rfl) ⟨4104710, by rfl⟩ : syracuseStep 5472947 = 8209421) B8209421
theorem B3648631 : Blo 2161435 3648631 := bstep (se 1 (by rfl) ⟨2736473, by rfl⟩ : syracuseStep 3648631 = 5472947) B5472947
theorem B4864841 : Blo 2161435 4864841 := bstep (se 2 (by rfl) ⟨1824315, by rfl⟩ : syracuseStep 4864841 = 3648631) B3648631
theorem B3243227 : Blo 2161435 3243227 := bstep (se 1 (by rfl) ⟨2432420, by rfl⟩ : syracuseStep 3243227 = 4864841) B4864841
theorem B2162151 : Blo 2161435 2162151 := bstep (se 1 (by rfl) ⟨1621613, by rfl⟩ : syracuseStep 2162151 = 3243227) B3243227
theorem B2432425 : Blo 2161435 2432425 := bbase (se 2 (by rfl) ⟨912159, by rfl⟩ : syracuseStep 2432425 = 1824319) (by norm_num)
theorem B3243233 : Blo 2161435 3243233 := bstep (se 2 (by rfl) ⟨1216212, by rfl⟩ : syracuseStep 3243233 = 2432425) B2432425
theorem B2162155 : Blo 2161435 2162155 := bstep (se 1 (by rfl) ⟨1621616, by rfl⟩ : syracuseStep 2162155 = 3243233) B3243233
theorem B6926725 : Blo 2161435 6926725 := bbase (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) (by norm_num)
theorem B9235633 : Blo 2161435 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B12314177 : Blo 2161435 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B8209451 : Blo 2161435 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B5472967 : Blo 2161435 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B7297289 : Blo 2161435 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B4864859 : Blo 2161435 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B3243239 : Blo 2161435 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B2162159 : Blo 2161435 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B3243245 : Blo 2161435 3243245 := bbase (se 3 (by rfl) ⟨608108, by rfl⟩ : syracuseStep 3243245 = 1216217) (by norm_num)
theorem B2162163 : Blo 2161435 2162163 := bstep (se 1 (by rfl) ⟨1621622, by rfl⟩ : syracuseStep 2162163 = 3243245) B3243245
theorem B4864877 : Blo 2161435 4864877 := bbase (se 3 (by rfl) ⟨912164, by rfl⟩ : syracuseStep 4864877 = 1824329) (by norm_num)
theorem B3243251 : Blo 2161435 3243251 := bstep (se 1 (by rfl) ⟨2432438, by rfl⟩ : syracuseStep 3243251 = 4864877) B4864877
theorem B2162167 : Blo 2161435 2162167 := bstep (se 1 (by rfl) ⟨1621625, by rfl⟩ : syracuseStep 2162167 = 3243251) B3243251
theorem B4104749 : Blo 2161435 4104749 := bbase (se 3 (by rfl) ⟨769640, by rfl⟩ : syracuseStep 4104749 = 1539281) (by norm_num)
theorem B2736499 : Blo 2161435 2736499 := bstep (se 1 (by rfl) ⟨2052374, by rfl⟩ : syracuseStep 2736499 = 4104749) B4104749
theorem B3648665 : Blo 2161435 3648665 := bstep (se 2 (by rfl) ⟨1368249, by rfl⟩ : syracuseStep 3648665 = 2736499) B2736499
theorem B2432443 : Blo 2161435 2432443 := bstep (se 1 (by rfl) ⟨1824332, by rfl⟩ : syracuseStep 2432443 = 3648665) B3648665
theorem B3243257 : Blo 2161435 3243257 := bstep (se 2 (by rfl) ⟨1216221, by rfl⟩ : syracuseStep 3243257 = 2432443) B2432443
theorem B2162171 : Blo 2161435 2162171 := bstep (se 1 (by rfl) ⟨1621628, by rfl⟩ : syracuseStep 2162171 = 3243257) B3243257
theorem B19725077 : Blo 2161435 19725077 := bbase (se 6 (by rfl) ⟨462306, by rfl⟩ : syracuseStep 19725077 = 924613) (by norm_num)
theorem B52600205 : Blo 2161435 52600205 := bstep (se 3 (by rfl) ⟨9862538, by rfl⟩ : syracuseStep 52600205 = 19725077) B19725077
theorem B35066803 : Blo 2161435 35066803 := bstep (se 1 (by rfl) ⟨26300102, by rfl⟩ : syracuseStep 35066803 = 52600205) B52600205
theorem B46755737 : Blo 2161435 46755737 := bstep (se 2 (by rfl) ⟨17533401, by rfl⟩ : syracuseStep 46755737 = 35066803) B35066803
theorem B31170491 : Blo 2161435 31170491 := bstep (se 1 (by rfl) ⟨23377868, by rfl⟩ : syracuseStep 31170491 = 46755737) B46755737
theorem B20780327 : Blo 2161435 20780327 := bstep (se 1 (by rfl) ⟨15585245, by rfl⟩ : syracuseStep 20780327 = 31170491) B31170491
theorem B55414205 : Blo 2161435 55414205 := bstep (se 3 (by rfl) ⟨10390163, by rfl⟩ : syracuseStep 55414205 = 20780327) B20780327
theorem B36942803 : Blo 2161435 36942803 := bstep (se 1 (by rfl) ⟨27707102, by rfl⟩ : syracuseStep 36942803 = 55414205) B55414205
theorem B24628535 : Blo 2161435 24628535 := bstep (se 1 (by rfl) ⟨18471401, by rfl⟩ : syracuseStep 24628535 = 36942803) B36942803
theorem B16419023 : Blo 2161435 16419023 := bstep (se 1 (by rfl) ⟨12314267, by rfl⟩ : syracuseStep 16419023 = 24628535) B24628535
theorem B10946015 : Blo 2161435 10946015 := bstep (se 1 (by rfl) ⟨8209511, by rfl⟩ : syracuseStep 10946015 = 16419023) B16419023
theorem B7297343 : Blo 2161435 7297343 := bstep (se 1 (by rfl) ⟨5473007, by rfl⟩ : syracuseStep 7297343 = 10946015) B10946015
theorem B4864895 : Blo 2161435 4864895 := bstep (se 1 (by rfl) ⟨3648671, by rfl⟩ : syracuseStep 4864895 = 7297343) B7297343
theorem B3243263 : Blo 2161435 3243263 := bstep (se 1 (by rfl) ⟨2432447, by rfl⟩ : syracuseStep 3243263 = 4864895) B4864895
theorem B2162175 : Blo 2161435 2162175 := bstep (se 1 (by rfl) ⟨1621631, by rfl⟩ : syracuseStep 2162175 = 3243263) B3243263
theorem B3243269 : Blo 2161435 3243269 := bbase (se 4 (by rfl) ⟨304056, by rfl⟩ : syracuseStep 3243269 = 608113) (by norm_num)
theorem B2162179 : Blo 2161435 2162179 := bstep (se 1 (by rfl) ⟨1621634, by rfl⟩ : syracuseStep 2162179 = 3243269) B3243269
theorem B3648685 : Blo 2161435 3648685 := bbase (se 3 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 3648685 = 1368257) (by norm_num)
theorem B4864913 : Blo 2161435 4864913 := bstep (se 2 (by rfl) ⟨1824342, by rfl⟩ : syracuseStep 4864913 = 3648685) B3648685
theorem B3243275 : Blo 2161435 3243275 := bstep (se 1 (by rfl) ⟨2432456, by rfl⟩ : syracuseStep 3243275 = 4864913) B4864913
theorem B2162183 : Blo 2161435 2162183 := bstep (se 1 (by rfl) ⟨1621637, by rfl⟩ : syracuseStep 2162183 = 3243275) B3243275
theorem B2432461 : Blo 2161435 2432461 := bbase (se 3 (by rfl) ⟨456086, by rfl⟩ : syracuseStep 2432461 = 912173) (by norm_num)
theorem B3243281 : Blo 2161435 3243281 := bstep (se 2 (by rfl) ⟨1216230, by rfl⟩ : syracuseStep 3243281 = 2432461) B2432461
theorem B2162187 : Blo 2161435 2162187 := bstep (se 1 (by rfl) ⟨1621640, by rfl⟩ : syracuseStep 2162187 = 3243281) B3243281
theorem B7297397 : Blo 2161435 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B4864931 : Blo 2161435 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B3243287 : Blo 2161435 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B2162191 : Blo 2161435 2162191 := bstep (se 1 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 2162191 = 3243287) B3243287
theorem B3243293 : Blo 2161435 3243293 := bbase (se 3 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 3243293 = 1216235) (by norm_num)
theorem B2162195 : Blo 2161435 2162195 := bstep (se 1 (by rfl) ⟨1621646, by rfl⟩ : syracuseStep 2162195 = 3243293) B3243293
theorem B4864949 : Blo 2161435 4864949 := bbase (se 5 (by rfl) ⟨228044, by rfl⟩ : syracuseStep 4864949 = 456089) (by norm_num)
theorem B3243299 : Blo 2161435 3243299 := bstep (se 1 (by rfl) ⟨2432474, by rfl⟩ : syracuseStep 3243299 = 4864949) B4864949
theorem B2162199 : Blo 2161435 2162199 := bstep (se 1 (by rfl) ⟨1621649, by rfl⟩ : syracuseStep 2162199 = 3243299) B3243299
theorem B3287557 : Blo 2161435 3287557 := bbase (se 4 (by rfl) ⟨308208, by rfl⟩ : syracuseStep 3287557 = 616417) (by norm_num)
theorem B4383409 : Blo 2161435 4383409 := bstep (se 2 (by rfl) ⟨1643778, by rfl⟩ : syracuseStep 4383409 = 3287557) B3287557
theorem B5844545 : Blo 2161435 5844545 := bstep (se 2 (by rfl) ⟨2191704, by rfl⟩ : syracuseStep 5844545 = 4383409) B4383409
theorem B3896363 : Blo 2161435 3896363 := bstep (se 1 (by rfl) ⟨2922272, by rfl⟩ : syracuseStep 3896363 = 5844545) B5844545
theorem B10390301 : Blo 2161435 10390301 := bstep (se 3 (by rfl) ⟨1948181, by rfl⟩ : syracuseStep 10390301 = 3896363) B3896363
theorem B6926867 : Blo 2161435 6926867 := bstep (se 1 (by rfl) ⟨5195150, by rfl⟩ : syracuseStep 6926867 = 10390301) B10390301
theorem B4617911 : Blo 2161435 4617911 := bstep (se 1 (by rfl) ⟨3463433, by rfl⟩ : syracuseStep 4617911 = 6926867) B6926867
theorem B12314429 : Blo 2161435 12314429 := bstep (se 3 (by rfl) ⟨2308955, by rfl⟩ : syracuseStep 12314429 = 4617911) B4617911
theorem B8209619 : Blo 2161435 8209619 := bstep (se 1 (by rfl) ⟨6157214, by rfl⟩ : syracuseStep 8209619 = 12314429) B12314429
theorem B5473079 : Blo 2161435 5473079 := bstep (se 1 (by rfl) ⟨4104809, by rfl⟩ : syracuseStep 5473079 = 8209619) B8209619
theorem B3648719 : Blo 2161435 3648719 := bstep (se 1 (by rfl) ⟨2736539, by rfl⟩ : syracuseStep 3648719 = 5473079) B5473079
theorem B2432479 : Blo 2161435 2432479 := bstep (se 1 (by rfl) ⟨1824359, by rfl⟩ : syracuseStep 2432479 = 3648719) B3648719
theorem B3243305 : Blo 2161435 3243305 := bstep (se 2 (by rfl) ⟨1216239, by rfl⟩ : syracuseStep 3243305 = 2432479) B2432479
theorem B2162203 : Blo 2161435 2162203 := bstep (se 1 (by rfl) ⟨1621652, by rfl⟩ : syracuseStep 2162203 = 3243305) B3243305
theorem B16643285 : Blo 2161435 16643285 := bbase (se 7 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 16643285 = 390077) (by norm_num)
theorem B11095523 : Blo 2161435 11095523 := bstep (se 1 (by rfl) ⟨8321642, by rfl⟩ : syracuseStep 11095523 = 16643285) B16643285
theorem B7397015 : Blo 2161435 7397015 := bstep (se 1 (by rfl) ⟨5547761, by rfl⟩ : syracuseStep 7397015 = 11095523) B11095523
theorem B19725373 : Blo 2161435 19725373 := bstep (se 3 (by rfl) ⟨3698507, by rfl⟩ : syracuseStep 19725373 = 7397015) B7397015
theorem B26300497 : Blo 2161435 26300497 := bstep (se 2 (by rfl) ⟨9862686, by rfl⟩ : syracuseStep 26300497 = 19725373) B19725373
theorem B35067329 : Blo 2161435 35067329 := bstep (se 2 (by rfl) ⟨13150248, by rfl⟩ : syracuseStep 35067329 = 26300497) B26300497
theorem B23378219 : Blo 2161435 23378219 := bstep (se 1 (by rfl) ⟨17533664, by rfl⟩ : syracuseStep 23378219 = 35067329) B35067329
theorem B15585479 : Blo 2161435 15585479 := bstep (se 1 (by rfl) ⟨11689109, by rfl⟩ : syracuseStep 15585479 = 23378219) B23378219
theorem B10390319 : Blo 2161435 10390319 := bstep (se 1 (by rfl) ⟨7792739, by rfl⟩ : syracuseStep 10390319 = 15585479) B15585479
theorem B6926879 : Blo 2161435 6926879 := bstep (se 1 (by rfl) ⟨5195159, by rfl⟩ : syracuseStep 6926879 = 10390319) B10390319
theorem B4617919 : Blo 2161435 4617919 := bstep (se 1 (by rfl) ⟨3463439, by rfl⟩ : syracuseStep 4617919 = 6926879) B6926879
theorem B6157225 : Blo 2161435 6157225 := bstep (se 2 (by rfl) ⟨2308959, by rfl⟩ : syracuseStep 6157225 = 4617919) B4617919
theorem B8209633 : Blo 2161435 8209633 := bstep (se 2 (by rfl) ⟨3078612, by rfl⟩ : syracuseStep 8209633 = 6157225) B6157225
theorem B10946177 : Blo 2161435 10946177 := bstep (se 2 (by rfl) ⟨4104816, by rfl⟩ : syracuseStep 10946177 = 8209633) B8209633
theorem B7297451 : Blo 2161435 7297451 := bstep (se 1 (by rfl) ⟨5473088, by rfl⟩ : syracuseStep 7297451 = 10946177) B10946177
theorem B4864967 : Blo 2161435 4864967 := bstep (se 1 (by rfl) ⟨3648725, by rfl⟩ : syracuseStep 4864967 = 7297451) B7297451
theorem B3243311 : Blo 2161435 3243311 := bstep (se 1 (by rfl) ⟨2432483, by rfl⟩ : syracuseStep 3243311 = 4864967) B4864967
theorem B2162207 : Blo 2161435 2162207 := bstep (se 1 (by rfl) ⟨1621655, by rfl⟩ : syracuseStep 2162207 = 3243311) B3243311
theorem B3243317 : Blo 2161435 3243317 := bbase (se 5 (by rfl) ⟨152030, by rfl⟩ : syracuseStep 3243317 = 304061) (by norm_num)
theorem B2162211 : Blo 2161435 2162211 := bstep (se 1 (by rfl) ⟨1621658, by rfl⟩ : syracuseStep 2162211 = 3243317) B3243317
theorem B5473109 : Blo 2161435 5473109 := bbase (se 9 (by rfl) ⟨16034, by rfl⟩ : syracuseStep 5473109 = 32069) (by norm_num)
theorem B3648739 : Blo 2161435 3648739 := bstep (se 1 (by rfl) ⟨2736554, by rfl⟩ : syracuseStep 3648739 = 5473109) B5473109
theorem B4864985 : Blo 2161435 4864985 := bstep (se 2 (by rfl) ⟨1824369, by rfl⟩ : syracuseStep 4864985 = 3648739) B3648739
theorem B3243323 : Blo 2161435 3243323 := bstep (se 1 (by rfl) ⟨2432492, by rfl⟩ : syracuseStep 3243323 = 4864985) B4864985
theorem B2162215 : Blo 2161435 2162215 := bstep (se 1 (by rfl) ⟨1621661, by rfl⟩ : syracuseStep 2162215 = 3243323) B3243323
theorem B2432497 : Blo 2161435 2432497 := bbase (se 2 (by rfl) ⟨912186, by rfl⟩ : syracuseStep 2432497 = 1824373) (by norm_num)
theorem B3243329 : Blo 2161435 3243329 := bstep (se 2 (by rfl) ⟨1216248, by rfl⟩ : syracuseStep 3243329 = 2432497) B2432497
theorem B2162219 : Blo 2161435 2162219 := bstep (se 1 (by rfl) ⟨1621664, by rfl⟩ : syracuseStep 2162219 = 3243329) B3243329
theorem B4931381 : Blo 2161435 4931381 := bbase (se 5 (by rfl) ⟨231158, by rfl⟩ : syracuseStep 4931381 = 462317) (by norm_num)
theorem B13150349 : Blo 2161435 13150349 := bstep (se 3 (by rfl) ⟨2465690, by rfl⟩ : syracuseStep 13150349 = 4931381) B4931381
theorem B8766899 : Blo 2161435 8766899 := bstep (se 1 (by rfl) ⟨6575174, by rfl⟩ : syracuseStep 8766899 = 13150349) B13150349
theorem B5844599 : Blo 2161435 5844599 := bstep (se 1 (by rfl) ⟨4383449, by rfl⟩ : syracuseStep 5844599 = 8766899) B8766899
theorem B3896399 : Blo 2161435 3896399 := bstep (se 1 (by rfl) ⟨2922299, by rfl⟩ : syracuseStep 3896399 = 5844599) B5844599
theorem B2597599 : Blo 2161435 2597599 := bstep (se 1 (by rfl) ⟨1948199, by rfl⟩ : syracuseStep 2597599 = 3896399) B3896399
theorem B13853861 : Blo 2161435 13853861 := bstep (se 4 (by rfl) ⟨1298799, by rfl⟩ : syracuseStep 13853861 = 2597599) B2597599
theorem B9235907 : Blo 2161435 9235907 := bstep (se 1 (by rfl) ⟨6926930, by rfl⟩ : syracuseStep 9235907 = 13853861) B13853861
theorem B6157271 : Blo 2161435 6157271 := bstep (se 1 (by rfl) ⟨4617953, by rfl⟩ : syracuseStep 6157271 = 9235907) B9235907
theorem B4104847 : Blo 2161435 4104847 := bstep (se 1 (by rfl) ⟨3078635, by rfl⟩ : syracuseStep 4104847 = 6157271) B6157271
theorem B5473129 : Blo 2161435 5473129 := bstep (se 2 (by rfl) ⟨2052423, by rfl⟩ : syracuseStep 5473129 = 4104847) B4104847
theorem B7297505 : Blo 2161435 7297505 := bstep (se 2 (by rfl) ⟨2736564, by rfl⟩ : syracuseStep 7297505 = 5473129) B5473129
theorem B4865003 : Blo 2161435 4865003 := bstep (se 1 (by rfl) ⟨3648752, by rfl⟩ : syracuseStep 4865003 = 7297505) B7297505
theorem B3243335 : Blo 2161435 3243335 := bstep (se 1 (by rfl) ⟨2432501, by rfl⟩ : syracuseStep 3243335 = 4865003) B4865003
theorem B2162223 : Blo 2161435 2162223 := bstep (se 1 (by rfl) ⟨1621667, by rfl⟩ : syracuseStep 2162223 = 3243335) B3243335
theorem B3243341 : Blo 2161435 3243341 := bbase (se 3 (by rfl) ⟨608126, by rfl⟩ : syracuseStep 3243341 = 1216253) (by norm_num)
theorem B2162227 : Blo 2161435 2162227 := bstep (se 1 (by rfl) ⟨1621670, by rfl⟩ : syracuseStep 2162227 = 3243341) B3243341
theorem B4865021 : Blo 2161435 4865021 := bbase (se 3 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 4865021 = 1824383) (by norm_num)
theorem B3243347 : Blo 2161435 3243347 := bstep (se 1 (by rfl) ⟨2432510, by rfl⟩ : syracuseStep 3243347 = 4865021) B4865021
theorem B2162231 : Blo 2161435 2162231 := bstep (se 1 (by rfl) ⟨1621673, by rfl⟩ : syracuseStep 2162231 = 3243347) B3243347
theorem B3648773 : Blo 2161435 3648773 := bbase (se 4 (by rfl) ⟨342072, by rfl⟩ : syracuseStep 3648773 = 684145) (by norm_num)
theorem B2432515 : Blo 2161435 2432515 := bstep (se 1 (by rfl) ⟨1824386, by rfl⟩ : syracuseStep 2432515 = 3648773) B3648773
theorem B3243353 : Blo 2161435 3243353 := bstep (se 2 (by rfl) ⟨1216257, by rfl⟩ : syracuseStep 3243353 = 2432515) B2432515
theorem B2162235 : Blo 2161435 2162235 := bstep (se 1 (by rfl) ⟨1621676, by rfl⟩ : syracuseStep 2162235 = 3243353) B3243353
theorem B16419509 : Blo 2161435 16419509 := bbase (se 5 (by rfl) ⟨769664, by rfl⟩ : syracuseStep 16419509 = 1539329) (by norm_num)
theorem B10946339 : Blo 2161435 10946339 := bstep (se 1 (by rfl) ⟨8209754, by rfl⟩ : syracuseStep 10946339 = 16419509) B16419509
theorem B7297559 : Blo 2161435 7297559 := bstep (se 1 (by rfl) ⟨5473169, by rfl⟩ : syracuseStep 7297559 = 10946339) B10946339
theorem B4865039 : Blo 2161435 4865039 := bstep (se 1 (by rfl) ⟨3648779, by rfl⟩ : syracuseStep 4865039 = 7297559) B7297559
theorem B3243359 : Blo 2161435 3243359 := bstep (se 1 (by rfl) ⟨2432519, by rfl⟩ : syracuseStep 3243359 = 4865039) B4865039
theorem B2162239 : Blo 2161435 2162239 := bstep (se 1 (by rfl) ⟨1621679, by rfl⟩ : syracuseStep 2162239 = 3243359) B3243359
theorem B3243365 : Blo 2161435 3243365 := bbase (se 4 (by rfl) ⟨304065, by rfl⟩ : syracuseStep 3243365 = 608131) (by norm_num)
theorem B2162243 : Blo 2161435 2162243 := bstep (se 1 (by rfl) ⟨1621682, by rfl⟩ : syracuseStep 2162243 = 3243365) B3243365
theorem B4104893 : Blo 2161435 4104893 := bbase (se 3 (by rfl) ⟨769667, by rfl⟩ : syracuseStep 4104893 = 1539335) (by norm_num)
theorem B2736595 : Blo 2161435 2736595 := bstep (se 1 (by rfl) ⟨2052446, by rfl⟩ : syracuseStep 2736595 = 4104893) B4104893
theorem B3648793 : Blo 2161435 3648793 := bstep (se 2 (by rfl) ⟨1368297, by rfl⟩ : syracuseStep 3648793 = 2736595) B2736595
theorem B4865057 : Blo 2161435 4865057 := bstep (se 2 (by rfl) ⟨1824396, by rfl⟩ : syracuseStep 4865057 = 3648793) B3648793
theorem B3243371 : Blo 2161435 3243371 := bstep (se 1 (by rfl) ⟨2432528, by rfl⟩ : syracuseStep 3243371 = 4865057) B4865057
theorem B2162247 : Blo 2161435 2162247 := bstep (se 1 (by rfl) ⟨1621685, by rfl⟩ : syracuseStep 2162247 = 3243371) B3243371
theorem B2432533 : Blo 2161435 2432533 := bbase (se 6 (by rfl) ⟨57012, by rfl⟩ : syracuseStep 2432533 = 114025) (by norm_num)
theorem B3243377 : Blo 2161435 3243377 := bstep (se 2 (by rfl) ⟨1216266, by rfl⟩ : syracuseStep 3243377 = 2432533) B2432533
theorem B2162251 : Blo 2161435 2162251 := bstep (se 1 (by rfl) ⟨1621688, by rfl⟩ : syracuseStep 2162251 = 3243377) B3243377
theorem B2736605 : Blo 2161435 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B7297613 : Blo 2161435 7297613 := bstep (se 3 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 7297613 = 2736605) B2736605
theorem B4865075 : Blo 2161435 4865075 := bstep (se 1 (by rfl) ⟨3648806, by rfl⟩ : syracuseStep 4865075 = 7297613) B7297613
theorem B3243383 : Blo 2161435 3243383 := bstep (se 1 (by rfl) ⟨2432537, by rfl⟩ : syracuseStep 3243383 = 4865075) B4865075
theorem B2162255 : Blo 2161435 2162255 := bstep (se 1 (by rfl) ⟨1621691, by rfl⟩ : syracuseStep 2162255 = 3243383) B3243383
theorem B3243389 : Blo 2161435 3243389 := bbase (se 3 (by rfl) ⟨608135, by rfl⟩ : syracuseStep 3243389 = 1216271) (by norm_num)
theorem B2162259 : Blo 2161435 2162259 := bstep (se 1 (by rfl) ⟨1621694, by rfl⟩ : syracuseStep 2162259 = 3243389) B3243389
theorem B4865093 : Blo 2161435 4865093 := bbase (se 4 (by rfl) ⟨456102, by rfl⟩ : syracuseStep 4865093 = 912205) (by norm_num)
theorem B3243395 : Blo 2161435 3243395 := bstep (se 1 (by rfl) ⟨2432546, by rfl⟩ : syracuseStep 3243395 = 4865093) B4865093
theorem B2162263 : Blo 2161435 2162263 := bstep (se 1 (by rfl) ⟨1621697, by rfl⟩ : syracuseStep 2162263 = 3243395) B3243395
theorem B6157397 : Blo 2161435 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B4104931 : Blo 2161435 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B5473241 : Blo 2161435 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B3648827 : Blo 2161435 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B2432551 : Blo 2161435 2432551 := bstep (se 1 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 2432551 = 3648827) B3648827
theorem B3243401 : Blo 2161435 3243401 := bstep (se 2 (by rfl) ⟨1216275, by rfl⟩ : syracuseStep 3243401 = 2432551) B2432551
theorem B2162267 : Blo 2161435 2162267 := bstep (se 1 (by rfl) ⟨1621700, by rfl⟩ : syracuseStep 2162267 = 3243401) B3243401
theorem B10946501 : Blo 2161435 10946501 := bbase (se 4 (by rfl) ⟨1026234, by rfl⟩ : syracuseStep 10946501 = 2052469) (by norm_num)
theorem B7297667 : Blo 2161435 7297667 := bstep (se 1 (by rfl) ⟨5473250, by rfl⟩ : syracuseStep 7297667 = 10946501) B10946501
theorem B4865111 : Blo 2161435 4865111 := bstep (se 1 (by rfl) ⟨3648833, by rfl⟩ : syracuseStep 4865111 = 7297667) B7297667
theorem B3243407 : Blo 2161435 3243407 := bstep (se 1 (by rfl) ⟨2432555, by rfl⟩ : syracuseStep 3243407 = 4865111) B4865111
theorem B2162271 : Blo 2161435 2162271 := bstep (se 1 (by rfl) ⟨1621703, by rfl⟩ : syracuseStep 2162271 = 3243407) B3243407
theorem B3243413 : Blo 2161435 3243413 := bbase (se 6 (by rfl) ⟨76017, by rfl⟩ : syracuseStep 3243413 = 152035) (by norm_num)
theorem B2162275 : Blo 2161435 2162275 := bstep (se 1 (by rfl) ⟨1621706, by rfl⟩ : syracuseStep 2162275 = 3243413) B3243413
theorem B5195333 : Blo 2161435 5195333 := bbase (se 4 (by rfl) ⟨487062, by rfl⟩ : syracuseStep 5195333 = 974125) (by norm_num)
theorem B3463555 : Blo 2161435 3463555 := bstep (se 1 (by rfl) ⟨2597666, by rfl⟩ : syracuseStep 3463555 = 5195333) B5195333
theorem B4618073 : Blo 2161435 4618073 := bstep (se 2 (by rfl) ⟨1731777, by rfl⟩ : syracuseStep 4618073 = 3463555) B3463555
theorem B12314861 : Blo 2161435 12314861 := bstep (se 3 (by rfl) ⟨2309036, by rfl⟩ : syracuseStep 12314861 = 4618073) B4618073
theorem B8209907 : Blo 2161435 8209907 := bstep (se 1 (by rfl) ⟨6157430, by rfl⟩ : syracuseStep 8209907 = 12314861) B12314861
theorem B5473271 : Blo 2161435 5473271 := bstep (se 1 (by rfl) ⟨4104953, by rfl⟩ : syracuseStep 5473271 = 8209907) B8209907
theorem B3648847 : Blo 2161435 3648847 := bstep (se 1 (by rfl) ⟨2736635, by rfl⟩ : syracuseStep 3648847 = 5473271) B5473271
theorem B4865129 : Blo 2161435 4865129 := bstep (se 2 (by rfl) ⟨1824423, by rfl⟩ : syracuseStep 4865129 = 3648847) B3648847
theorem B3243419 : Blo 2161435 3243419 := bstep (se 1 (by rfl) ⟨2432564, by rfl⟩ : syracuseStep 3243419 = 4865129) B4865129
theorem B2162279 : Blo 2161435 2162279 := bstep (se 1 (by rfl) ⟨1621709, by rfl⟩ : syracuseStep 2162279 = 3243419) B3243419
theorem B2432569 : Blo 2161435 2432569 := bbase (se 2 (by rfl) ⟨912213, by rfl⟩ : syracuseStep 2432569 = 1824427) (by norm_num)
theorem B3243425 : Blo 2161435 3243425 := bstep (se 2 (by rfl) ⟨1216284, by rfl⟩ : syracuseStep 3243425 = 2432569) B2432569
theorem B2162283 : Blo 2161435 2162283 := bstep (se 1 (by rfl) ⟨1621712, by rfl⟩ : syracuseStep 2162283 = 3243425) B3243425
theorem B2309045 : Blo 2161435 2309045 := bbase (se 5 (by rfl) ⟨108236, by rfl⟩ : syracuseStep 2309045 = 216473) (by norm_num)
theorem B6157453 : Blo 2161435 6157453 := bstep (se 3 (by rfl) ⟨1154522, by rfl⟩ : syracuseStep 6157453 = 2309045) B2309045
theorem B8209937 : Blo 2161435 8209937 := bstep (se 2 (by rfl) ⟨3078726, by rfl⟩ : syracuseStep 8209937 = 6157453) B6157453
theorem B5473291 : Blo 2161435 5473291 := bstep (se 1 (by rfl) ⟨4104968, by rfl⟩ : syracuseStep 5473291 = 8209937) B8209937
theorem B7297721 : Blo 2161435 7297721 := bstep (se 2 (by rfl) ⟨2736645, by rfl⟩ : syracuseStep 7297721 = 5473291) B5473291
theorem B4865147 : Blo 2161435 4865147 := bstep (se 1 (by rfl) ⟨3648860, by rfl⟩ : syracuseStep 4865147 = 7297721) B7297721
theorem B3243431 : Blo 2161435 3243431 := bstep (se 1 (by rfl) ⟨2432573, by rfl⟩ : syracuseStep 3243431 = 4865147) B4865147
theorem B2162287 : Blo 2161435 2162287 := bstep (se 1 (by rfl) ⟨1621715, by rfl⟩ : syracuseStep 2162287 = 3243431) B3243431
theorem B3243437 : Blo 2161435 3243437 := bbase (se 3 (by rfl) ⟨608144, by rfl⟩ : syracuseStep 3243437 = 1216289) (by norm_num)
theorem B2162291 : Blo 2161435 2162291 := bstep (se 1 (by rfl) ⟨1621718, by rfl⟩ : syracuseStep 2162291 = 3243437) B3243437
theorem B4865165 : Blo 2161435 4865165 := bbase (se 3 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 4865165 = 1824437) (by norm_num)
theorem B3243443 : Blo 2161435 3243443 := bstep (se 1 (by rfl) ⟨2432582, by rfl⟩ : syracuseStep 3243443 = 4865165) B4865165
theorem B2162295 : Blo 2161435 2162295 := bstep (se 1 (by rfl) ⟨1621721, by rfl⟩ : syracuseStep 2162295 = 3243443) B3243443
theorem B2736661 : Blo 2161435 2736661 := bbase (se 6 (by rfl) ⟨64140, by rfl⟩ : syracuseStep 2736661 = 128281) (by norm_num)
theorem B3648881 : Blo 2161435 3648881 := bstep (se 2 (by rfl) ⟨1368330, by rfl⟩ : syracuseStep 3648881 = 2736661) B2736661
theorem B2432587 : Blo 2161435 2432587 := bstep (se 1 (by rfl) ⟨1824440, by rfl⟩ : syracuseStep 2432587 = 3648881) B3648881
theorem B3243449 : Blo 2161435 3243449 := bstep (se 2 (by rfl) ⟨1216293, by rfl⟩ : syracuseStep 3243449 = 2432587) B2432587
theorem B2162299 : Blo 2161435 2162299 := bstep (se 1 (by rfl) ⟨1621724, by rfl⟩ : syracuseStep 2162299 = 3243449) B3243449
theorem B9362261 : Blo 2161435 9362261 := bbase (se 9 (by rfl) ⟨27428, by rfl⟩ : syracuseStep 9362261 = 54857) (by norm_num)
theorem B24966029 : Blo 2161435 24966029 := bstep (se 3 (by rfl) ⟨4681130, by rfl⟩ : syracuseStep 24966029 = 9362261) B9362261
theorem B66576077 : Blo 2161435 66576077 := bstep (se 3 (by rfl) ⟨12483014, by rfl⟩ : syracuseStep 66576077 = 24966029) B24966029
theorem B44384051 : Blo 2161435 44384051 := bstep (se 1 (by rfl) ⟨33288038, by rfl⟩ : syracuseStep 44384051 = 66576077) B66576077
theorem B118357469 : Blo 2161435 118357469 := bstep (se 3 (by rfl) ⟨22192025, by rfl⟩ : syracuseStep 118357469 = 44384051) B44384051
theorem B78904979 : Blo 2161435 78904979 := bstep (se 1 (by rfl) ⟨59178734, by rfl⟩ : syracuseStep 78904979 = 118357469) B118357469
theorem B52603319 : Blo 2161435 52603319 := bstep (se 1 (by rfl) ⟨39452489, by rfl⟩ : syracuseStep 52603319 = 78904979) B78904979
theorem B35068879 : Blo 2161435 35068879 := bstep (se 1 (by rfl) ⟨26301659, by rfl⟩ : syracuseStep 35068879 = 52603319) B52603319
theorem B46758505 : Blo 2161435 46758505 := bstep (se 2 (by rfl) ⟨17534439, by rfl⟩ : syracuseStep 46758505 = 35068879) B35068879
theorem B62344673 : Blo 2161435 62344673 := bstep (se 2 (by rfl) ⟨23379252, by rfl⟩ : syracuseStep 62344673 = 46758505) B46758505
theorem B41563115 : Blo 2161435 41563115 := bstep (se 1 (by rfl) ⟨31172336, by rfl⟩ : syracuseStep 41563115 = 62344673) B62344673
theorem B27708743 : Blo 2161435 27708743 := bstep (se 1 (by rfl) ⟨20781557, by rfl⟩ : syracuseStep 27708743 = 41563115) B41563115
theorem B18472495 : Blo 2161435 18472495 := bstep (se 1 (by rfl) ⟨13854371, by rfl⟩ : syracuseStep 18472495 = 27708743) B27708743
theorem B24629993 : Blo 2161435 24629993 := bstep (se 2 (by rfl) ⟨9236247, by rfl⟩ : syracuseStep 24629993 = 18472495) B18472495
theorem B16419995 : Blo 2161435 16419995 := bstep (se 1 (by rfl) ⟨12314996, by rfl⟩ : syracuseStep 16419995 = 24629993) B24629993
theorem B10946663 : Blo 2161435 10946663 := bstep (se 1 (by rfl) ⟨8209997, by rfl⟩ : syracuseStep 10946663 = 16419995) B16419995
theorem B7297775 : Blo 2161435 7297775 := bstep (se 1 (by rfl) ⟨5473331, by rfl⟩ : syracuseStep 7297775 = 10946663) B10946663
theorem B4865183 : Blo 2161435 4865183 := bstep (se 1 (by rfl) ⟨3648887, by rfl⟩ : syracuseStep 4865183 = 7297775) B7297775
theorem B3243455 : Blo 2161435 3243455 := bstep (se 1 (by rfl) ⟨2432591, by rfl⟩ : syracuseStep 3243455 = 4865183) B4865183
theorem B2162303 : Blo 2161435 2162303 := bstep (se 1 (by rfl) ⟨1621727, by rfl⟩ : syracuseStep 2162303 = 3243455) B3243455
theorem B3243461 : Blo 2161435 3243461 := bbase (se 4 (by rfl) ⟨304074, by rfl⟩ : syracuseStep 3243461 = 608149) (by norm_num)
theorem B2162307 : Blo 2161435 2162307 := bstep (se 1 (by rfl) ⟨1621730, by rfl⟩ : syracuseStep 2162307 = 3243461) B3243461
theorem B3648901 : Blo 2161435 3648901 := bbase (se 4 (by rfl) ⟨342084, by rfl⟩ : syracuseStep 3648901 = 684169) (by norm_num)
theorem B4865201 : Blo 2161435 4865201 := bstep (se 2 (by rfl) ⟨1824450, by rfl⟩ : syracuseStep 4865201 = 3648901) B3648901
theorem B3243467 : Blo 2161435 3243467 := bstep (se 1 (by rfl) ⟨2432600, by rfl⟩ : syracuseStep 3243467 = 4865201) B4865201
theorem B2162311 : Blo 2161435 2162311 := bstep (se 1 (by rfl) ⟨1621733, by rfl⟩ : syracuseStep 2162311 = 3243467) B3243467
theorem B2432605 : Blo 2161435 2432605 := bbase (se 3 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 2432605 = 912227) (by norm_num)
theorem B3243473 : Blo 2161435 3243473 := bstep (se 2 (by rfl) ⟨1216302, by rfl⟩ : syracuseStep 3243473 = 2432605) B2432605
theorem B2162315 : Blo 2161435 2162315 := bstep (se 1 (by rfl) ⟨1621736, by rfl⟩ : syracuseStep 2162315 = 3243473) B3243473
theorem B7297829 : Blo 2161435 7297829 := bbase (se 4 (by rfl) ⟨684171, by rfl⟩ : syracuseStep 7297829 = 1368343) (by norm_num)
theorem B4865219 : Blo 2161435 4865219 := bstep (se 1 (by rfl) ⟨3648914, by rfl⟩ : syracuseStep 4865219 = 7297829) B7297829
theorem B3243479 : Blo 2161435 3243479 := bstep (se 1 (by rfl) ⟨2432609, by rfl⟩ : syracuseStep 3243479 = 4865219) B4865219
theorem B2162319 : Blo 2161435 2162319 := bstep (se 1 (by rfl) ⟨1621739, by rfl⟩ : syracuseStep 2162319 = 3243479) B3243479
theorem B3243485 : Blo 2161435 3243485 := bbase (se 3 (by rfl) ⟨608153, by rfl⟩ : syracuseStep 3243485 = 1216307) (by norm_num)
theorem B2162323 : Blo 2161435 2162323 := bstep (se 1 (by rfl) ⟨1621742, by rfl⟩ : syracuseStep 2162323 = 3243485) B3243485
theorem B4865237 : Blo 2161435 4865237 := bbase (se 7 (by rfl) ⟨57014, by rfl⟩ : syracuseStep 4865237 = 114029) (by norm_num)
theorem B3243491 : Blo 2161435 3243491 := bstep (se 1 (by rfl) ⟨2432618, by rfl⟩ : syracuseStep 3243491 = 4865237) B4865237
theorem B2162327 : Blo 2161435 2162327 := bstep (se 1 (by rfl) ⟨1621745, by rfl⟩ : syracuseStep 2162327 = 3243491) B3243491
theorem B2597729 : Blo 2161435 2597729 := bbase (se 2 (by rfl) ⟨974148, by rfl⟩ : syracuseStep 2597729 = 1948297) (by norm_num)
theorem B6927277 : Blo 2161435 6927277 := bstep (se 3 (by rfl) ⟨1298864, by rfl⟩ : syracuseStep 6927277 = 2597729) B2597729
theorem B9236369 : Blo 2161435 9236369 := bstep (se 2 (by rfl) ⟨3463638, by rfl⟩ : syracuseStep 9236369 = 6927277) B6927277
theorem B6157579 : Blo 2161435 6157579 := bstep (se 1 (by rfl) ⟨4618184, by rfl⟩ : syracuseStep 6157579 = 9236369) B9236369
theorem B8210105 : Blo 2161435 8210105 := bstep (se 2 (by rfl) ⟨3078789, by rfl⟩ : syracuseStep 8210105 = 6157579) B6157579
theorem B5473403 : Blo 2161435 5473403 := bstep (se 1 (by rfl) ⟨4105052, by rfl⟩ : syracuseStep 5473403 = 8210105) B8210105
theorem B3648935 : Blo 2161435 3648935 := bstep (se 1 (by rfl) ⟨2736701, by rfl⟩ : syracuseStep 3648935 = 5473403) B5473403
theorem B2432623 : Blo 2161435 2432623 := bstep (se 1 (by rfl) ⟨1824467, by rfl⟩ : syracuseStep 2432623 = 3648935) B3648935
theorem B3243497 : Blo 2161435 3243497 := bstep (se 2 (by rfl) ⟨1216311, by rfl⟩ : syracuseStep 3243497 = 2432623) B2432623
theorem B2162331 : Blo 2161435 2162331 := bstep (se 1 (by rfl) ⟨1621748, by rfl⟩ : syracuseStep 2162331 = 3243497) B3243497
theorem B10390933 : Blo 2161435 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B13854577 : Blo 2161435 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B18472769 : Blo 2161435 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B12315179 : Blo 2161435 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B8210119 : Blo 2161435 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B10946825 : Blo 2161435 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B7297883 : Blo 2161435 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B4865255 : Blo 2161435 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B3243503 : Blo 2161435 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B2162335 : Blo 2161435 2162335 := bstep (se 1 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 2162335 = 3243503) B3243503
theorem B3243509 : Blo 2161435 3243509 := bbase (se 5 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 3243509 = 304079) (by norm_num)
theorem B2162339 : Blo 2161435 2162339 := bstep (se 1 (by rfl) ⟨1621754, by rfl⟩ : syracuseStep 2162339 = 3243509) B3243509
theorem B2309105 : Blo 2161435 2309105 := bbase (se 2 (by rfl) ⟨865914, by rfl⟩ : syracuseStep 2309105 = 1731829) (by norm_num)
theorem B6157613 : Blo 2161435 6157613 := bstep (se 3 (by rfl) ⟨1154552, by rfl⟩ : syracuseStep 6157613 = 2309105) B2309105
theorem B4105075 : Blo 2161435 4105075 := bstep (se 1 (by rfl) ⟨3078806, by rfl⟩ : syracuseStep 4105075 = 6157613) B6157613
theorem B5473433 : Blo 2161435 5473433 := bstep (se 2 (by rfl) ⟨2052537, by rfl⟩ : syracuseStep 5473433 = 4105075) B4105075
theorem B3648955 : Blo 2161435 3648955 := bstep (se 1 (by rfl) ⟨2736716, by rfl⟩ : syracuseStep 3648955 = 5473433) B5473433
theorem B4865273 : Blo 2161435 4865273 := bstep (se 2 (by rfl) ⟨1824477, by rfl⟩ : syracuseStep 4865273 = 3648955) B3648955
theorem B3243515 : Blo 2161435 3243515 := bstep (se 1 (by rfl) ⟨2432636, by rfl⟩ : syracuseStep 3243515 = 4865273) B4865273
theorem B2162343 : Blo 2161435 2162343 := bstep (se 1 (by rfl) ⟨1621757, by rfl⟩ : syracuseStep 2162343 = 3243515) B3243515
theorem B2432641 : Blo 2161435 2432641 := bbase (se 2 (by rfl) ⟨912240, by rfl⟩ : syracuseStep 2432641 = 1824481) (by norm_num)
theorem B3243521 : Blo 2161435 3243521 := bstep (se 2 (by rfl) ⟨1216320, by rfl⟩ : syracuseStep 3243521 = 2432641) B2432641
theorem B2162347 : Blo 2161435 2162347 := bstep (se 1 (by rfl) ⟨1621760, by rfl⟩ : syracuseStep 2162347 = 3243521) B3243521
theorem B5473453 : Blo 2161435 5473453 := bbase (se 3 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 5473453 = 2052545) (by norm_num)
theorem B7297937 : Blo 2161435 7297937 := bstep (se 2 (by rfl) ⟨2736726, by rfl⟩ : syracuseStep 7297937 = 5473453) B5473453
theorem B4865291 : Blo 2161435 4865291 := bstep (se 1 (by rfl) ⟨3648968, by rfl⟩ : syracuseStep 4865291 = 7297937) B7297937
theorem B3243527 : Blo 2161435 3243527 := bstep (se 1 (by rfl) ⟨2432645, by rfl⟩ : syracuseStep 3243527 = 4865291) B4865291
theorem B2162351 : Blo 2161435 2162351 := bstep (se 1 (by rfl) ⟨1621763, by rfl⟩ : syracuseStep 2162351 = 3243527) B3243527
theorem B3243533 : Blo 2161435 3243533 := bbase (se 3 (by rfl) ⟨608162, by rfl⟩ : syracuseStep 3243533 = 1216325) (by norm_num)
theorem B2162355 : Blo 2161435 2162355 := bstep (se 1 (by rfl) ⟨1621766, by rfl⟩ : syracuseStep 2162355 = 3243533) B3243533
theorem B4865309 : Blo 2161435 4865309 := bbase (se 3 (by rfl) ⟨912245, by rfl⟩ : syracuseStep 4865309 = 1824491) (by norm_num)
theorem B3243539 : Blo 2161435 3243539 := bstep (se 1 (by rfl) ⟨2432654, by rfl⟩ : syracuseStep 3243539 = 4865309) B4865309
theorem B2162359 : Blo 2161435 2162359 := bstep (se 1 (by rfl) ⟨1621769, by rfl⟩ : syracuseStep 2162359 = 3243539) B3243539
theorem B3648989 : Blo 2161435 3648989 := bbase (se 3 (by rfl) ⟨684185, by rfl⟩ : syracuseStep 3648989 = 1368371) (by norm_num)
theorem B2432659 : Blo 2161435 2432659 := bstep (se 1 (by rfl) ⟨1824494, by rfl⟩ : syracuseStep 2432659 = 3648989) B3648989
theorem B3243545 : Blo 2161435 3243545 := bstep (se 2 (by rfl) ⟨1216329, by rfl⟩ : syracuseStep 3243545 = 2432659) B2432659
theorem B2162363 : Blo 2161435 2162363 := bstep (se 1 (by rfl) ⟨1621772, by rfl⟩ : syracuseStep 2162363 = 3243545) B3243545
theorem B5067197 : Blo 2161435 5067197 := bbase (se 3 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 5067197 = 1900199) (by norm_num)
theorem B3378131 : Blo 2161435 3378131 := bstep (se 1 (by rfl) ⟨2533598, by rfl⟩ : syracuseStep 3378131 = 5067197) B5067197
theorem B2252087 : Blo 2161435 2252087 := bstep (se 1 (by rfl) ⟨1689065, by rfl⟩ : syracuseStep 2252087 = 3378131) B3378131
theorem B24022261 : Blo 2161435 24022261 := bstep (se 5 (by rfl) ⟨1126043, by rfl⟩ : syracuseStep 24022261 = 2252087) B2252087
theorem B32029681 : Blo 2161435 32029681 := bstep (se 2 (by rfl) ⟨12011130, by rfl⟩ : syracuseStep 32029681 = 24022261) B24022261
theorem B42706241 : Blo 2161435 42706241 := bstep (se 2 (by rfl) ⟨16014840, by rfl⟩ : syracuseStep 42706241 = 32029681) B32029681
theorem B28470827 : Blo 2161435 28470827 := bstep (se 1 (by rfl) ⟨21353120, by rfl⟩ : syracuseStep 28470827 = 42706241) B42706241
theorem B18980551 : Blo 2161435 18980551 := bstep (se 1 (by rfl) ⟨14235413, by rfl⟩ : syracuseStep 18980551 = 28470827) B28470827
theorem B25307401 : Blo 2161435 25307401 := bstep (se 2 (by rfl) ⟨9490275, by rfl⟩ : syracuseStep 25307401 = 18980551) B18980551
theorem B33743201 : Blo 2161435 33743201 := bstep (se 2 (by rfl) ⟨12653700, by rfl⟩ : syracuseStep 33743201 = 25307401) B25307401
theorem B89981869 : Blo 2161435 89981869 := bstep (se 3 (by rfl) ⟨16871600, by rfl⟩ : syracuseStep 89981869 = 33743201) B33743201
theorem B119975825 : Blo 2161435 119975825 := bstep (se 2 (by rfl) ⟨44990934, by rfl⟩ : syracuseStep 119975825 = 89981869) B89981869
theorem B79983883 : Blo 2161435 79983883 := bstep (se 1 (by rfl) ⟨59987912, by rfl⟩ : syracuseStep 79983883 = 119975825) B119975825
theorem B106645177 : Blo 2161435 106645177 := bstep (se 2 (by rfl) ⟨39991941, by rfl⟩ : syracuseStep 106645177 = 79983883) B79983883
theorem B142193569 : Blo 2161435 142193569 := bstep (se 2 (by rfl) ⟨53322588, by rfl⟩ : syracuseStep 142193569 = 106645177) B106645177
theorem B189591425 : Blo 2161435 189591425 := bstep (se 2 (by rfl) ⟨71096784, by rfl⟩ : syracuseStep 189591425 = 142193569) B142193569
theorem B126394283 : Blo 2161435 126394283 := bstep (se 1 (by rfl) ⟨94795712, by rfl⟩ : syracuseStep 126394283 = 189591425) B189591425
theorem B84262855 : Blo 2161435 84262855 := bstep (se 1 (by rfl) ⟨63197141, by rfl⟩ : syracuseStep 84262855 = 126394283) B126394283
theorem B112350473 : Blo 2161435 112350473 := bstep (se 2 (by rfl) ⟨42131427, by rfl⟩ : syracuseStep 112350473 = 84262855) B84262855
theorem B74900315 : Blo 2161435 74900315 := bstep (se 1 (by rfl) ⟨56175236, by rfl⟩ : syracuseStep 74900315 = 112350473) B112350473
theorem B49933543 : Blo 2161435 49933543 := bstep (se 1 (by rfl) ⟨37450157, by rfl⟩ : syracuseStep 49933543 = 74900315) B74900315
theorem B66578057 : Blo 2161435 66578057 := bstep (se 2 (by rfl) ⟨24966771, by rfl⟩ : syracuseStep 66578057 = 49933543) B49933543
theorem B44385371 : Blo 2161435 44385371 := bstep (se 1 (by rfl) ⟨33289028, by rfl⟩ : syracuseStep 44385371 = 66578057) B66578057
theorem B29590247 : Blo 2161435 29590247 := bstep (se 1 (by rfl) ⟨22192685, by rfl⟩ : syracuseStep 29590247 = 44385371) B44385371
theorem B19726831 : Blo 2161435 19726831 := bstep (se 1 (by rfl) ⟨14795123, by rfl⟩ : syracuseStep 19726831 = 29590247) B29590247
theorem B26302441 : Blo 2161435 26302441 := bstep (se 2 (by rfl) ⟨9863415, by rfl⟩ : syracuseStep 26302441 = 19726831) B19726831
theorem B35069921 : Blo 2161435 35069921 := bstep (se 2 (by rfl) ⟨13151220, by rfl⟩ : syracuseStep 35069921 = 26302441) B26302441
theorem B23379947 : Blo 2161435 23379947 := bstep (se 1 (by rfl) ⟨17534960, by rfl⟩ : syracuseStep 23379947 = 35069921) B35069921
theorem B15586631 : Blo 2161435 15586631 := bstep (se 1 (by rfl) ⟨11689973, by rfl⟩ : syracuseStep 15586631 = 23379947) B23379947
theorem B10391087 : Blo 2161435 10391087 := bstep (se 1 (by rfl) ⟨7793315, by rfl⟩ : syracuseStep 10391087 = 15586631) B15586631
theorem B6927391 : Blo 2161435 6927391 := bstep (se 1 (by rfl) ⟨5195543, by rfl⟩ : syracuseStep 6927391 = 10391087) B10391087
theorem B9236521 : Blo 2161435 9236521 := bstep (se 2 (by rfl) ⟨3463695, by rfl⟩ : syracuseStep 9236521 = 6927391) B6927391
theorem B12315361 : Blo 2161435 12315361 := bstep (se 2 (by rfl) ⟨4618260, by rfl⟩ : syracuseStep 12315361 = 9236521) B9236521
theorem B16420481 : Blo 2161435 16420481 := bstep (se 2 (by rfl) ⟨6157680, by rfl⟩ : syracuseStep 16420481 = 12315361) B12315361
theorem B10946987 : Blo 2161435 10946987 := bstep (se 1 (by rfl) ⟨8210240, by rfl⟩ : syracuseStep 10946987 = 16420481) B16420481
theorem B7297991 : Blo 2161435 7297991 := bstep (se 1 (by rfl) ⟨5473493, by rfl⟩ : syracuseStep 7297991 = 10946987) B10946987
theorem B4865327 : Blo 2161435 4865327 := bstep (se 1 (by rfl) ⟨3648995, by rfl⟩ : syracuseStep 4865327 = 7297991) B7297991
theorem B3243551 : Blo 2161435 3243551 := bstep (se 1 (by rfl) ⟨2432663, by rfl⟩ : syracuseStep 3243551 = 4865327) B4865327
theorem B2162367 : Blo 2161435 2162367 := bstep (se 1 (by rfl) ⟨1621775, by rfl⟩ : syracuseStep 2162367 = 3243551) B3243551
theorem B3243557 : Blo 2161435 3243557 := bbase (se 4 (by rfl) ⟨304083, by rfl⟩ : syracuseStep 3243557 = 608167) (by norm_num)
theorem B2162371 : Blo 2161435 2162371 := bstep (se 1 (by rfl) ⟨1621778, by rfl⟩ : syracuseStep 2162371 = 3243557) B3243557
theorem B2736757 : Blo 2161435 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B3649009 : Blo 2161435 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B4865345 : Blo 2161435 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B3243563 : Blo 2161435 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B2162375 : Blo 2161435 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B2432677 : Blo 2161435 2432677 := bbase (se 4 (by rfl) ⟨228063, by rfl⟩ : syracuseStep 2432677 = 456127) (by norm_num)
theorem B3243569 : Blo 2161435 3243569 := bstep (se 2 (by rfl) ⟨1216338, by rfl⟩ : syracuseStep 3243569 = 2432677) B2432677
theorem B2162379 : Blo 2161435 2162379 := bstep (se 1 (by rfl) ⟨1621784, by rfl⟩ : syracuseStep 2162379 = 3243569) B3243569
theorem B4217933 : Blo 2161435 4217933 := bbase (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) (by norm_num)
theorem B11247821 : Blo 2161435 11247821 := bstep (se 3 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 11247821 = 4217933) B4217933
theorem B7498547 : Blo 2161435 7498547 := bstep (se 1 (by rfl) ⟨5623910, by rfl⟩ : syracuseStep 7498547 = 11247821) B11247821
theorem B4999031 : Blo 2161435 4999031 := bstep (se 1 (by rfl) ⟨3749273, by rfl⟩ : syracuseStep 4999031 = 7498547) B7498547
theorem B3332687 : Blo 2161435 3332687 := bstep (se 1 (by rfl) ⟨2499515, by rfl⟩ : syracuseStep 3332687 = 4999031) B4999031
theorem B8887165 : Blo 2161435 8887165 := bstep (se 3 (by rfl) ⟨1666343, by rfl⟩ : syracuseStep 8887165 = 3332687) B3332687
theorem B47398213 : Blo 2161435 47398213 := bstep (se 4 (by rfl) ⟨4443582, by rfl⟩ : syracuseStep 47398213 = 8887165) B8887165
theorem B63197617 : Blo 2161435 63197617 := bstep (se 2 (by rfl) ⟨23699106, by rfl⟩ : syracuseStep 63197617 = 47398213) B47398213
theorem B84263489 : Blo 2161435 84263489 := bstep (se 2 (by rfl) ⟨31598808, by rfl⟩ : syracuseStep 84263489 = 63197617) B63197617
theorem B56175659 : Blo 2161435 56175659 := bstep (se 1 (by rfl) ⟨42131744, by rfl⟩ : syracuseStep 56175659 = 84263489) B84263489
theorem B37450439 : Blo 2161435 37450439 := bstep (se 1 (by rfl) ⟨28087829, by rfl⟩ : syracuseStep 37450439 = 56175659) B56175659
theorem B24966959 : Blo 2161435 24966959 := bstep (se 1 (by rfl) ⟨18725219, by rfl⟩ : syracuseStep 24966959 = 37450439) B37450439
theorem B66578557 : Blo 2161435 66578557 := bstep (se 3 (by rfl) ⟨12483479, by rfl⟩ : syracuseStep 66578557 = 24966959) B24966959
theorem B88771409 : Blo 2161435 88771409 := bstep (se 2 (by rfl) ⟨33289278, by rfl⟩ : syracuseStep 88771409 = 66578557) B66578557
theorem B59180939 : Blo 2161435 59180939 := bstep (se 1 (by rfl) ⟨44385704, by rfl⟩ : syracuseStep 59180939 = 88771409) B88771409
theorem B39453959 : Blo 2161435 39453959 := bstep (se 1 (by rfl) ⟨29590469, by rfl⟩ : syracuseStep 39453959 = 59180939) B59180939
theorem B26302639 : Blo 2161435 26302639 := bstep (se 1 (by rfl) ⟨19726979, by rfl⟩ : syracuseStep 26302639 = 39453959) B39453959
theorem B35070185 : Blo 2161435 35070185 := bstep (se 2 (by rfl) ⟨13151319, by rfl⟩ : syracuseStep 35070185 = 26302639) B26302639
theorem B23380123 : Blo 2161435 23380123 := bstep (se 1 (by rfl) ⟨17535092, by rfl⟩ : syracuseStep 23380123 = 35070185) B35070185
theorem B31173497 : Blo 2161435 31173497 := bstep (se 2 (by rfl) ⟨11690061, by rfl⟩ : syracuseStep 31173497 = 23380123) B23380123
theorem B20782331 : Blo 2161435 20782331 := bstep (se 1 (by rfl) ⟨15586748, by rfl⟩ : syracuseStep 20782331 = 31173497) B31173497
theorem B13854887 : Blo 2161435 13854887 := bstep (se 1 (by rfl) ⟨10391165, by rfl⟩ : syracuseStep 13854887 = 20782331) B20782331
theorem B9236591 : Blo 2161435 9236591 := bstep (se 1 (by rfl) ⟨6927443, by rfl⟩ : syracuseStep 9236591 = 13854887) B13854887
theorem B6157727 : Blo 2161435 6157727 := bstep (se 1 (by rfl) ⟨4618295, by rfl⟩ : syracuseStep 6157727 = 9236591) B9236591
theorem B4105151 : Blo 2161435 4105151 := bstep (se 1 (by rfl) ⟨3078863, by rfl⟩ : syracuseStep 4105151 = 6157727) B6157727
theorem B2736767 : Blo 2161435 2736767 := bstep (se 1 (by rfl) ⟨2052575, by rfl⟩ : syracuseStep 2736767 = 4105151) B4105151
theorem B7298045 : Blo 2161435 7298045 := bstep (se 3 (by rfl) ⟨1368383, by rfl⟩ : syracuseStep 7298045 = 2736767) B2736767
theorem B4865363 : Blo 2161435 4865363 := bstep (se 1 (by rfl) ⟨3649022, by rfl⟩ : syracuseStep 4865363 = 7298045) B7298045
theorem B3243575 : Blo 2161435 3243575 := bstep (se 1 (by rfl) ⟨2432681, by rfl⟩ : syracuseStep 3243575 = 4865363) B4865363
theorem B2162383 : Blo 2161435 2162383 := bstep (se 1 (by rfl) ⟨1621787, by rfl⟩ : syracuseStep 2162383 = 3243575) B3243575
theorem B3243581 : Blo 2161435 3243581 := bbase (se 3 (by rfl) ⟨608171, by rfl⟩ : syracuseStep 3243581 = 1216343) (by norm_num)
theorem B2162387 : Blo 2161435 2162387 := bstep (se 1 (by rfl) ⟨1621790, by rfl⟩ : syracuseStep 2162387 = 3243581) B3243581
theorem B4865381 : Blo 2161435 4865381 := bbase (se 4 (by rfl) ⟨456129, by rfl⟩ : syracuseStep 4865381 = 912259) (by norm_num)
theorem B3243587 : Blo 2161435 3243587 := bstep (se 1 (by rfl) ⟨2432690, by rfl⟩ : syracuseStep 3243587 = 4865381) B4865381
theorem B2162391 : Blo 2161435 2162391 := bstep (se 1 (by rfl) ⟨1621793, by rfl⟩ : syracuseStep 2162391 = 3243587) B3243587
theorem B5473565 : Blo 2161435 5473565 := bbase (se 3 (by rfl) ⟨1026293, by rfl⟩ : syracuseStep 5473565 = 2052587) (by norm_num)
theorem B3649043 : Blo 2161435 3649043 := bstep (se 1 (by rfl) ⟨2736782, by rfl⟩ : syracuseStep 3649043 = 5473565) B5473565
theorem B2432695 : Blo 2161435 2432695 := bstep (se 1 (by rfl) ⟨1824521, by rfl⟩ : syracuseStep 2432695 = 3649043) B3649043
theorem B3243593 : Blo 2161435 3243593 := bstep (se 2 (by rfl) ⟨1216347, by rfl⟩ : syracuseStep 3243593 = 2432695) B2432695
theorem B2162395 : Blo 2161435 2162395 := bstep (se 1 (by rfl) ⟨1621796, by rfl⟩ : syracuseStep 2162395 = 3243593) B3243593
theorem B4105181 : Blo 2161435 4105181 := bbase (se 3 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 4105181 = 1539443) (by norm_num)
theorem B10947149 : Blo 2161435 10947149 := bstep (se 3 (by rfl) ⟨2052590, by rfl⟩ : syracuseStep 10947149 = 4105181) B4105181
theorem B7298099 : Blo 2161435 7298099 := bstep (se 1 (by rfl) ⟨5473574, by rfl⟩ : syracuseStep 7298099 = 10947149) B10947149
theorem B4865399 : Blo 2161435 4865399 := bstep (se 1 (by rfl) ⟨3649049, by rfl⟩ : syracuseStep 4865399 = 7298099) B7298099
theorem B3243599 : Blo 2161435 3243599 := bstep (se 1 (by rfl) ⟨2432699, by rfl⟩ : syracuseStep 3243599 = 4865399) B4865399
theorem B2162399 : Blo 2161435 2162399 := bstep (se 1 (by rfl) ⟨1621799, by rfl⟩ : syracuseStep 2162399 = 3243599) B3243599
theorem B3243605 : Blo 2161435 3243605 := bbase (se 8 (by rfl) ⟨19005, by rfl⟩ : syracuseStep 3243605 = 38011) (by norm_num)
theorem B2162403 : Blo 2161435 2162403 := bstep (se 1 (by rfl) ⟨1621802, by rfl⟩ : syracuseStep 2162403 = 3243605) B3243605
theorem B9236693 : Blo 2161435 9236693 := bbase (se 7 (by rfl) ⟨108242, by rfl⟩ : syracuseStep 9236693 = 216485) (by norm_num)
theorem B6157795 : Blo 2161435 6157795 := bstep (se 1 (by rfl) ⟨4618346, by rfl⟩ : syracuseStep 6157795 = 9236693) B9236693
theorem B8210393 : Blo 2161435 8210393 := bstep (se 2 (by rfl) ⟨3078897, by rfl⟩ : syracuseStep 8210393 = 6157795) B6157795
theorem B5473595 : Blo 2161435 5473595 := bstep (se 1 (by rfl) ⟨4105196, by rfl⟩ : syracuseStep 5473595 = 8210393) B8210393
theorem B3649063 : Blo 2161435 3649063 := bstep (se 1 (by rfl) ⟨2736797, by rfl⟩ : syracuseStep 3649063 = 5473595) B5473595
theorem B4865417 : Blo 2161435 4865417 := bstep (se 2 (by rfl) ⟨1824531, by rfl⟩ : syracuseStep 4865417 = 3649063) B3649063
theorem B3243611 : Blo 2161435 3243611 := bstep (se 1 (by rfl) ⟨2432708, by rfl⟩ : syracuseStep 3243611 = 4865417) B4865417
theorem B2162407 : Blo 2161435 2162407 := bstep (se 1 (by rfl) ⟨1621805, by rfl⟩ : syracuseStep 2162407 = 3243611) B3243611
theorem B2432713 : Blo 2161435 2432713 := bbase (se 2 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 2432713 = 1824535) (by norm_num)
theorem B3243617 : Blo 2161435 3243617 := bstep (se 2 (by rfl) ⟨1216356, by rfl⟩ : syracuseStep 3243617 = 2432713) B2432713
theorem B2162411 : Blo 2161435 2162411 := bstep (se 1 (by rfl) ⟨1621808, by rfl⟩ : syracuseStep 2162411 = 3243617) B3243617
theorem B5266549 : Blo 2161435 5266549 := bbase (se 5 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 5266549 = 493739) (by norm_num)
theorem B7022065 : Blo 2161435 7022065 := bstep (se 2 (by rfl) ⟨2633274, by rfl⟩ : syracuseStep 7022065 = 5266549) B5266549
theorem B9362753 : Blo 2161435 9362753 := bstep (se 2 (by rfl) ⟨3511032, by rfl⟩ : syracuseStep 9362753 = 7022065) B7022065
theorem B6241835 : Blo 2161435 6241835 := bstep (se 1 (by rfl) ⟨4681376, by rfl⟩ : syracuseStep 6241835 = 9362753) B9362753
theorem B4161223 : Blo 2161435 4161223 := bstep (se 1 (by rfl) ⟨3120917, by rfl⟩ : syracuseStep 4161223 = 6241835) B6241835
theorem B5548297 : Blo 2161435 5548297 := bstep (se 2 (by rfl) ⟨2080611, by rfl⟩ : syracuseStep 5548297 = 4161223) B4161223
theorem B7397729 : Blo 2161435 7397729 := bstep (se 2 (by rfl) ⟨2774148, by rfl⟩ : syracuseStep 7397729 = 5548297) B5548297
theorem B4931819 : Blo 2161435 4931819 := bstep (se 1 (by rfl) ⟨3698864, by rfl⟩ : syracuseStep 4931819 = 7397729) B7397729
theorem B3287879 : Blo 2161435 3287879 := bstep (se 1 (by rfl) ⟨2465909, by rfl⟩ : syracuseStep 3287879 = 4931819) B4931819
theorem B2191919 : Blo 2161435 2191919 := bstep (se 1 (by rfl) ⟨1643939, by rfl⟩ : syracuseStep 2191919 = 3287879) B3287879
theorem B5845117 : Blo 2161435 5845117 := bstep (se 3 (by rfl) ⟨1095959, by rfl⟩ : syracuseStep 5845117 = 2191919) B2191919
theorem B7793489 : Blo 2161435 7793489 := bstep (se 2 (by rfl) ⟨2922558, by rfl⟩ : syracuseStep 7793489 = 5845117) B5845117
theorem B5195659 : Blo 2161435 5195659 := bstep (se 1 (by rfl) ⟨3896744, by rfl⟩ : syracuseStep 5195659 = 7793489) B7793489
theorem B6927545 : Blo 2161435 6927545 := bstep (se 2 (by rfl) ⟨2597829, by rfl⟩ : syracuseStep 6927545 = 5195659) B5195659
theorem B18473453 : Blo 2161435 18473453 := bstep (se 3 (by rfl) ⟨3463772, by rfl⟩ : syracuseStep 18473453 = 6927545) B6927545
theorem B12315635 : Blo 2161435 12315635 := bstep (se 1 (by rfl) ⟨9236726, by rfl⟩ : syracuseStep 12315635 = 18473453) B18473453
theorem B8210423 : Blo 2161435 8210423 := bstep (se 1 (by rfl) ⟨6157817, by rfl⟩ : syracuseStep 8210423 = 12315635) B12315635
theorem B5473615 : Blo 2161435 5473615 := bstep (se 1 (by rfl) ⟨4105211, by rfl⟩ : syracuseStep 5473615 = 8210423) B8210423
theorem B7298153 : Blo 2161435 7298153 := bstep (se 2 (by rfl) ⟨2736807, by rfl⟩ : syracuseStep 7298153 = 5473615) B5473615
theorem B4865435 : Blo 2161435 4865435 := bstep (se 1 (by rfl) ⟨3649076, by rfl⟩ : syracuseStep 4865435 = 7298153) B7298153
theorem B3243623 : Blo 2161435 3243623 := bstep (se 1 (by rfl) ⟨2432717, by rfl⟩ : syracuseStep 3243623 = 4865435) B4865435
theorem B2162415 : Blo 2161435 2162415 := bstep (se 1 (by rfl) ⟨1621811, by rfl⟩ : syracuseStep 2162415 = 3243623) B3243623
theorem B3243629 : Blo 2161435 3243629 := bbase (se 3 (by rfl) ⟨608180, by rfl⟩ : syracuseStep 3243629 = 1216361) (by norm_num)
theorem B2162419 : Blo 2161435 2162419 := bstep (se 1 (by rfl) ⟨1621814, by rfl⟩ : syracuseStep 2162419 = 3243629) B3243629
theorem B4865453 : Blo 2161435 4865453 := bbase (se 3 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 4865453 = 1824545) (by norm_num)
theorem B3243635 : Blo 2161435 3243635 := bstep (se 1 (by rfl) ⟨2432726, by rfl⟩ : syracuseStep 3243635 = 4865453) B4865453
theorem B2162423 : Blo 2161435 2162423 := bstep (se 1 (by rfl) ⟨1621817, by rfl⟩ : syracuseStep 2162423 = 3243635) B3243635
theorem B2597845 : Blo 2161435 2597845 := bbase (se 7 (by rfl) ⟨30443, by rfl⟩ : syracuseStep 2597845 = 60887) (by norm_num)
theorem B3463793 : Blo 2161435 3463793 := bstep (se 2 (by rfl) ⟨1298922, by rfl⟩ : syracuseStep 3463793 = 2597845) B2597845
theorem B2309195 : Blo 2161435 2309195 := bstep (se 1 (by rfl) ⟨1731896, by rfl⟩ : syracuseStep 2309195 = 3463793) B3463793
theorem B6157853 : Blo 2161435 6157853 := bstep (se 3 (by rfl) ⟨1154597, by rfl⟩ : syracuseStep 6157853 = 2309195) B2309195
theorem B4105235 : Blo 2161435 4105235 := bstep (se 1 (by rfl) ⟨3078926, by rfl⟩ : syracuseStep 4105235 = 6157853) B6157853
theorem B2736823 : Blo 2161435 2736823 := bstep (se 1 (by rfl) ⟨2052617, by rfl⟩ : syracuseStep 2736823 = 4105235) B4105235
theorem B3649097 : Blo 2161435 3649097 := bstep (se 2 (by rfl) ⟨1368411, by rfl⟩ : syracuseStep 3649097 = 2736823) B2736823
theorem B2432731 : Blo 2161435 2432731 := bstep (se 1 (by rfl) ⟨1824548, by rfl⟩ : syracuseStep 2432731 = 3649097) B3649097
theorem B3243641 : Blo 2161435 3243641 := bstep (se 2 (by rfl) ⟨1216365, by rfl⟩ : syracuseStep 3243641 = 2432731) B2432731
theorem B2162427 : Blo 2161435 2162427 := bstep (se 1 (by rfl) ⟨1621820, by rfl⟩ : syracuseStep 2162427 = 3243641) B3243641
theorem B70141909 : Blo 2161435 70141909 := bbase (se 7 (by rfl) ⟨821975, by rfl⟩ : syracuseStep 70141909 = 1643951) (by norm_num)
theorem B93522545 : Blo 2161435 93522545 := bstep (se 2 (by rfl) ⟨35070954, by rfl⟩ : syracuseStep 93522545 = 70141909) B70141909
theorem B62348363 : Blo 2161435 62348363 := bstep (se 1 (by rfl) ⟨46761272, by rfl⟩ : syracuseStep 62348363 = 93522545) B93522545
theorem B41565575 : Blo 2161435 41565575 := bstep (se 1 (by rfl) ⟨31174181, by rfl⟩ : syracuseStep 41565575 = 62348363) B62348363
theorem B27710383 : Blo 2161435 27710383 := bstep (se 1 (by rfl) ⟨20782787, by rfl⟩ : syracuseStep 27710383 = 41565575) B41565575
theorem B36947177 : Blo 2161435 36947177 := bstep (se 2 (by rfl) ⟨13855191, by rfl⟩ : syracuseStep 36947177 = 27710383) B27710383
theorem B24631451 : Blo 2161435 24631451 := bstep (se 1 (by rfl) ⟨18473588, by rfl⟩ : syracuseStep 24631451 = 36947177) B36947177
theorem B16420967 : Blo 2161435 16420967 := bstep (se 1 (by rfl) ⟨12315725, by rfl⟩ : syracuseStep 16420967 = 24631451) B24631451
theorem B10947311 : Blo 2161435 10947311 := bstep (se 1 (by rfl) ⟨8210483, by rfl⟩ : syracuseStep 10947311 = 16420967) B16420967
theorem B7298207 : Blo 2161435 7298207 := bstep (se 1 (by rfl) ⟨5473655, by rfl⟩ : syracuseStep 7298207 = 10947311) B10947311
theorem B4865471 : Blo 2161435 4865471 := bstep (se 1 (by rfl) ⟨3649103, by rfl⟩ : syracuseStep 4865471 = 7298207) B7298207
theorem B3243647 : Blo 2161435 3243647 := bstep (se 1 (by rfl) ⟨2432735, by rfl⟩ : syracuseStep 3243647 = 4865471) B4865471
theorem B2162431 : Blo 2161435 2162431 := bstep (se 1 (by rfl) ⟨1621823, by rfl⟩ : syracuseStep 2162431 = 3243647) B3243647
theorem B3243653 : Blo 2161435 3243653 := bbase (se 4 (by rfl) ⟨304092, by rfl⟩ : syracuseStep 3243653 = 608185) (by norm_num)
theorem B2162435 : Blo 2161435 2162435 := bstep (se 1 (by rfl) ⟨1621826, by rfl⟩ : syracuseStep 2162435 = 3243653) B3243653
theorem B3649117 : Blo 2161435 3649117 := bbase (se 3 (by rfl) ⟨684209, by rfl⟩ : syracuseStep 3649117 = 1368419) (by norm_num)
theorem B4865489 : Blo 2161435 4865489 := bstep (se 2 (by rfl) ⟨1824558, by rfl⟩ : syracuseStep 4865489 = 3649117) B3649117
theorem B3243659 : Blo 2161435 3243659 := bstep (se 1 (by rfl) ⟨2432744, by rfl⟩ : syracuseStep 3243659 = 4865489) B4865489
theorem B2162439 : Blo 2161435 2162439 := bstep (se 1 (by rfl) ⟨1621829, by rfl⟩ : syracuseStep 2162439 = 3243659) B3243659
theorem B2432749 : Blo 2161435 2432749 := bbase (se 3 (by rfl) ⟨456140, by rfl⟩ : syracuseStep 2432749 = 912281) (by norm_num)
theorem B3243665 : Blo 2161435 3243665 := bstep (se 2 (by rfl) ⟨1216374, by rfl⟩ : syracuseStep 3243665 = 2432749) B2432749
theorem B2162443 : Blo 2161435 2162443 := bstep (se 1 (by rfl) ⟨1621832, by rfl⟩ : syracuseStep 2162443 = 3243665) B3243665
theorem B7298261 : Blo 2161435 7298261 := bbase (se 7 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 7298261 = 171053) (by norm_num)
theorem B4865507 : Blo 2161435 4865507 := bstep (se 1 (by rfl) ⟨3649130, by rfl⟩ : syracuseStep 4865507 = 7298261) B7298261
theorem B3243671 : Blo 2161435 3243671 := bstep (se 1 (by rfl) ⟨2432753, by rfl⟩ : syracuseStep 3243671 = 4865507) B4865507
theorem B2162447 : Blo 2161435 2162447 := bstep (se 1 (by rfl) ⟨1621835, by rfl⟩ : syracuseStep 2162447 = 3243671) B3243671
theorem B3243677 : Blo 2161435 3243677 := bbase (se 3 (by rfl) ⟨608189, by rfl⟩ : syracuseStep 3243677 = 1216379) (by norm_num)
theorem B2162451 : Blo 2161435 2162451 := bstep (se 1 (by rfl) ⟨1621838, by rfl⟩ : syracuseStep 2162451 = 3243677) B3243677
theorem B4865525 : Blo 2161435 4865525 := bbase (se 5 (by rfl) ⟨228071, by rfl⟩ : syracuseStep 4865525 = 456143) (by norm_num)
theorem B3243683 : Blo 2161435 3243683 := bstep (se 1 (by rfl) ⟨2432762, by rfl⟩ : syracuseStep 3243683 = 4865525) B4865525
theorem B2162455 : Blo 2161435 2162455 := bstep (se 1 (by rfl) ⟨1621841, by rfl⟩ : syracuseStep 2162455 = 3243683) B3243683
theorem B11248213 : Blo 2161435 11248213 := bbase (se 8 (by rfl) ⟨65907, by rfl⟩ : syracuseStep 11248213 = 131815) (by norm_num)
theorem B14997617 : Blo 2161435 14997617 := bstep (se 2 (by rfl) ⟨5624106, by rfl⟩ : syracuseStep 14997617 = 11248213) B11248213
theorem B9998411 : Blo 2161435 9998411 := bstep (se 1 (by rfl) ⟨7498808, by rfl⟩ : syracuseStep 9998411 = 14997617) B14997617
theorem B26662429 : Blo 2161435 26662429 := bstep (se 3 (by rfl) ⟨4999205, by rfl⟩ : syracuseStep 26662429 = 9998411) B9998411
theorem B142199621 : Blo 2161435 142199621 := bstep (se 4 (by rfl) ⟨13331214, by rfl⟩ : syracuseStep 142199621 = 26662429) B26662429
theorem B94799747 : Blo 2161435 94799747 := bstep (se 1 (by rfl) ⟨71099810, by rfl⟩ : syracuseStep 94799747 = 142199621) B142199621
theorem B252799325 : Blo 2161435 252799325 := bstep (se 3 (by rfl) ⟨47399873, by rfl⟩ : syracuseStep 252799325 = 94799747) B94799747
theorem B168532883 : Blo 2161435 168532883 := bstep (se 1 (by rfl) ⟨126399662, by rfl⟩ : syracuseStep 168532883 = 252799325) B252799325
theorem B112355255 : Blo 2161435 112355255 := bstep (se 1 (by rfl) ⟨84266441, by rfl⟩ : syracuseStep 112355255 = 168532883) B168532883
theorem B74903503 : Blo 2161435 74903503 := bstep (se 1 (by rfl) ⟨56177627, by rfl⟩ : syracuseStep 74903503 = 112355255) B112355255
theorem B99871337 : Blo 2161435 99871337 := bstep (se 2 (by rfl) ⟨37451751, by rfl⟩ : syracuseStep 99871337 = 74903503) B74903503
theorem B266323565 : Blo 2161435 266323565 := bstep (se 3 (by rfl) ⟨49935668, by rfl⟩ : syracuseStep 266323565 = 99871337) B99871337
theorem B177549043 : Blo 2161435 177549043 := bstep (se 1 (by rfl) ⟨133161782, by rfl⟩ : syracuseStep 177549043 = 266323565) B266323565
theorem B236732057 : Blo 2161435 236732057 := bstep (se 2 (by rfl) ⟨88774521, by rfl⟩ : syracuseStep 236732057 = 177549043) B177549043
theorem B157821371 : Blo 2161435 157821371 := bstep (se 1 (by rfl) ⟨118366028, by rfl⟩ : syracuseStep 157821371 = 236732057) B236732057
theorem B105214247 : Blo 2161435 105214247 := bstep (se 1 (by rfl) ⟨78910685, by rfl⟩ : syracuseStep 105214247 = 157821371) B157821371
theorem B70142831 : Blo 2161435 70142831 := bstep (se 1 (by rfl) ⟨52607123, by rfl⟩ : syracuseStep 70142831 = 105214247) B105214247
theorem B46761887 : Blo 2161435 46761887 := bstep (se 1 (by rfl) ⟨35071415, by rfl⟩ : syracuseStep 46761887 = 70142831) B70142831
theorem B31174591 : Blo 2161435 31174591 := bstep (se 1 (by rfl) ⟨23380943, by rfl⟩ : syracuseStep 31174591 = 46761887) B46761887
theorem B41566121 : Blo 2161435 41566121 := bstep (se 2 (by rfl) ⟨15587295, by rfl⟩ : syracuseStep 41566121 = 31174591) B31174591
theorem B27710747 : Blo 2161435 27710747 := bstep (se 1 (by rfl) ⟨20783060, by rfl⟩ : syracuseStep 27710747 = 41566121) B41566121
theorem B18473831 : Blo 2161435 18473831 := bstep (se 1 (by rfl) ⟨13855373, by rfl⟩ : syracuseStep 18473831 = 27710747) B27710747
theorem B12315887 : Blo 2161435 12315887 := bstep (se 1 (by rfl) ⟨9236915, by rfl⟩ : syracuseStep 12315887 = 18473831) B18473831
theorem B8210591 : Blo 2161435 8210591 := bstep (se 1 (by rfl) ⟨6157943, by rfl⟩ : syracuseStep 8210591 = 12315887) B12315887
theorem B5473727 : Blo 2161435 5473727 := bstep (se 1 (by rfl) ⟨4105295, by rfl⟩ : syracuseStep 5473727 = 8210591) B8210591
theorem B3649151 : Blo 2161435 3649151 := bstep (se 1 (by rfl) ⟨2736863, by rfl⟩ : syracuseStep 3649151 = 5473727) B5473727
theorem B2432767 : Blo 2161435 2432767 := bstep (se 1 (by rfl) ⟨1824575, by rfl⟩ : syracuseStep 2432767 = 3649151) B3649151
theorem B3243689 : Blo 2161435 3243689 := bstep (se 2 (by rfl) ⟨1216383, by rfl⟩ : syracuseStep 3243689 = 2432767) B2432767
theorem B2162459 : Blo 2161435 2162459 := bstep (se 1 (by rfl) ⟨1621844, by rfl⟩ : syracuseStep 2162459 = 3243689) B3243689
theorem B2309233 : Blo 2161435 2309233 := bbase (se 2 (by rfl) ⟨865962, by rfl⟩ : syracuseStep 2309233 = 1731925) (by norm_num)
theorem B3078977 : Blo 2161435 3078977 := bstep (se 2 (by rfl) ⟨1154616, by rfl⟩ : syracuseStep 3078977 = 2309233) B2309233
theorem B8210605 : Blo 2161435 8210605 := bstep (se 3 (by rfl) ⟨1539488, by rfl⟩ : syracuseStep 8210605 = 3078977) B3078977
theorem B10947473 : Blo 2161435 10947473 := bstep (se 2 (by rfl) ⟨4105302, by rfl⟩ : syracuseStep 10947473 = 8210605) B8210605
theorem B7298315 : Blo 2161435 7298315 := bstep (se 1 (by rfl) ⟨5473736, by rfl⟩ : syracuseStep 7298315 = 10947473) B10947473
theorem B4865543 : Blo 2161435 4865543 := bstep (se 1 (by rfl) ⟨3649157, by rfl⟩ : syracuseStep 4865543 = 7298315) B7298315
theorem B3243695 : Blo 2161435 3243695 := bstep (se 1 (by rfl) ⟨2432771, by rfl⟩ : syracuseStep 3243695 = 4865543) B4865543
theorem B2162463 : Blo 2161435 2162463 := bstep (se 1 (by rfl) ⟨1621847, by rfl⟩ : syracuseStep 2162463 = 3243695) B3243695
theorem B3243701 : Blo 2161435 3243701 := bbase (se 5 (by rfl) ⟨152048, by rfl⟩ : syracuseStep 3243701 = 304097) (by norm_num)
theorem B2162467 : Blo 2161435 2162467 := bstep (se 1 (by rfl) ⟨1621850, by rfl⟩ : syracuseStep 2162467 = 3243701) B3243701
theorem B5473757 : Blo 2161435 5473757 := bbase (se 3 (by rfl) ⟨1026329, by rfl⟩ : syracuseStep 5473757 = 2052659) (by norm_num)
theorem B3649171 : Blo 2161435 3649171 := bstep (se 1 (by rfl) ⟨2736878, by rfl⟩ : syracuseStep 3649171 = 5473757) B5473757
theorem B4865561 : Blo 2161435 4865561 := bstep (se 2 (by rfl) ⟨1824585, by rfl⟩ : syracuseStep 4865561 = 3649171) B3649171
theorem B3243707 : Blo 2161435 3243707 := bstep (se 1 (by rfl) ⟨2432780, by rfl⟩ : syracuseStep 3243707 = 4865561) B4865561
theorem B2162471 : Blo 2161435 2162471 := bstep (se 1 (by rfl) ⟨1621853, by rfl⟩ : syracuseStep 2162471 = 3243707) B3243707
theorem B2432785 : Blo 2161435 2432785 := bbase (se 2 (by rfl) ⟨912294, by rfl⟩ : syracuseStep 2432785 = 1824589) (by norm_num)
theorem B3243713 : Blo 2161435 3243713 := bstep (se 2 (by rfl) ⟨1216392, by rfl⟩ : syracuseStep 3243713 = 2432785) B2432785
theorem B2162475 : Blo 2161435 2162475 := bstep (se 1 (by rfl) ⟨1621856, by rfl⟩ : syracuseStep 2162475 = 3243713) B3243713
theorem B4105333 : Blo 2161435 4105333 := bbase (se 5 (by rfl) ⟨192437, by rfl⟩ : syracuseStep 4105333 = 384875) (by norm_num)
theorem B5473777 : Blo 2161435 5473777 := bstep (se 2 (by rfl) ⟨2052666, by rfl⟩ : syracuseStep 5473777 = 4105333) B4105333
theorem B7298369 : Blo 2161435 7298369 := bstep (se 2 (by rfl) ⟨2736888, by rfl⟩ : syracuseStep 7298369 = 5473777) B5473777
theorem B4865579 : Blo 2161435 4865579 := bstep (se 1 (by rfl) ⟨3649184, by rfl⟩ : syracuseStep 4865579 = 7298369) B7298369
theorem B3243719 : Blo 2161435 3243719 := bstep (se 1 (by rfl) ⟨2432789, by rfl⟩ : syracuseStep 3243719 = 4865579) B4865579
theorem B2162479 : Blo 2161435 2162479 := bstep (se 1 (by rfl) ⟨1621859, by rfl⟩ : syracuseStep 2162479 = 3243719) B3243719
theorem B3243725 : Blo 2161435 3243725 := bbase (se 3 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 3243725 = 1216397) (by norm_num)
theorem B2162483 : Blo 2161435 2162483 := bstep (se 1 (by rfl) ⟨1621862, by rfl⟩ : syracuseStep 2162483 = 3243725) B3243725
theorem B4865597 : Blo 2161435 4865597 := bbase (se 3 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 4865597 = 1824599) (by norm_num)
theorem B3243731 : Blo 2161435 3243731 := bstep (se 1 (by rfl) ⟨2432798, by rfl⟩ : syracuseStep 3243731 = 4865597) B4865597
theorem B2162487 : Blo 2161435 2162487 := bstep (se 1 (by rfl) ⟨1621865, by rfl⟩ : syracuseStep 2162487 = 3243731) B3243731
theorem B3649205 : Blo 2161435 3649205 := bbase (se 5 (by rfl) ⟨171056, by rfl⟩ : syracuseStep 3649205 = 342113) (by norm_num)
theorem B2432803 : Blo 2161435 2432803 := bstep (se 1 (by rfl) ⟨1824602, by rfl⟩ : syracuseStep 2432803 = 3649205) B3649205
theorem B3243737 : Blo 2161435 3243737 := bstep (se 2 (by rfl) ⟨1216401, by rfl⟩ : syracuseStep 3243737 = 2432803) B2432803
theorem B2162491 : Blo 2161435 2162491 := bstep (se 1 (by rfl) ⟨1621868, by rfl⟩ : syracuseStep 2162491 = 3243737) B3243737
theorem B3463901 : Blo 2161435 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B2309267 : Blo 2161435 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B6158045 : Blo 2161435 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B16421453 : Blo 2161435 16421453 := bstep (se 3 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 16421453 = 6158045) B6158045
theorem B10947635 : Blo 2161435 10947635 := bstep (se 1 (by rfl) ⟨8210726, by rfl⟩ : syracuseStep 10947635 = 16421453) B16421453
theorem B7298423 : Blo 2161435 7298423 := bstep (se 1 (by rfl) ⟨5473817, by rfl⟩ : syracuseStep 7298423 = 10947635) B10947635
theorem B4865615 : Blo 2161435 4865615 := bstep (se 1 (by rfl) ⟨3649211, by rfl⟩ : syracuseStep 4865615 = 7298423) B7298423
theorem B3243743 : Blo 2161435 3243743 := bstep (se 1 (by rfl) ⟨2432807, by rfl⟩ : syracuseStep 3243743 = 4865615) B4865615
theorem B2162495 : Blo 2161435 2162495 := bstep (se 1 (by rfl) ⟨1621871, by rfl⟩ : syracuseStep 2162495 = 3243743) B3243743
theorem B3243749 : Blo 2161435 3243749 := bbase (se 4 (by rfl) ⟨304101, by rfl⟩ : syracuseStep 3243749 = 608203) (by norm_num)
theorem B2162499 : Blo 2161435 2162499 := bstep (se 1 (by rfl) ⟨1621874, by rfl⟩ : syracuseStep 2162499 = 3243749) B3243749
theorem B6158069 : Blo 2161435 6158069 := bbase (se 5 (by rfl) ⟨288659, by rfl⟩ : syracuseStep 6158069 = 577319) (by norm_num)
theorem B4105379 : Blo 2161435 4105379 := bstep (se 1 (by rfl) ⟨3079034, by rfl⟩ : syracuseStep 4105379 = 6158069) B6158069
theorem B2736919 : Blo 2161435 2736919 := bstep (se 1 (by rfl) ⟨2052689, by rfl⟩ : syracuseStep 2736919 = 4105379) B4105379
theorem B3649225 : Blo 2161435 3649225 := bstep (se 2 (by rfl) ⟨1368459, by rfl⟩ : syracuseStep 3649225 = 2736919) B2736919
theorem B4865633 : Blo 2161435 4865633 := bstep (se 2 (by rfl) ⟨1824612, by rfl⟩ : syracuseStep 4865633 = 3649225) B3649225
theorem B3243755 : Blo 2161435 3243755 := bstep (se 1 (by rfl) ⟨2432816, by rfl⟩ : syracuseStep 3243755 = 4865633) B4865633
theorem B2162503 : Blo 2161435 2162503 := bstep (se 1 (by rfl) ⟨1621877, by rfl⟩ : syracuseStep 2162503 = 3243755) B3243755
theorem B2432821 : Blo 2161435 2432821 := bbase (se 5 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 2432821 = 228077) (by norm_num)
theorem B3243761 : Blo 2161435 3243761 := bstep (se 2 (by rfl) ⟨1216410, by rfl⟩ : syracuseStep 3243761 = 2432821) B2432821
theorem B2162507 : Blo 2161435 2162507 := bstep (se 1 (by rfl) ⟨1621880, by rfl⟩ : syracuseStep 2162507 = 3243761) B3243761
theorem B2736929 : Blo 2161435 2736929 := bbase (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) (by norm_num)
theorem B7298477 : Blo 2161435 7298477 := bstep (se 3 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 7298477 = 2736929) B2736929
theorem B4865651 : Blo 2161435 4865651 := bstep (se 1 (by rfl) ⟨3649238, by rfl⟩ : syracuseStep 4865651 = 7298477) B7298477
theorem B3243767 : Blo 2161435 3243767 := bstep (se 1 (by rfl) ⟨2432825, by rfl⟩ : syracuseStep 3243767 = 4865651) B4865651
theorem B2162511 : Blo 2161435 2162511 := bstep (se 1 (by rfl) ⟨1621883, by rfl⟩ : syracuseStep 2162511 = 3243767) B3243767
theorem B3243773 : Blo 2161435 3243773 := bbase (se 3 (by rfl) ⟨608207, by rfl⟩ : syracuseStep 3243773 = 1216415) (by norm_num)
theorem B2162515 : Blo 2161435 2162515 := bstep (se 1 (by rfl) ⟨1621886, by rfl⟩ : syracuseStep 2162515 = 3243773) B3243773
theorem B4865669 : Blo 2161435 4865669 := bbase (se 4 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 4865669 = 912313) (by norm_num)
theorem B3243779 : Blo 2161435 3243779 := bstep (se 1 (by rfl) ⟨2432834, by rfl⟩ : syracuseStep 3243779 = 4865669) B4865669
theorem B2162519 : Blo 2161435 2162519 := bstep (se 1 (by rfl) ⟨1621889, by rfl⟩ : syracuseStep 2162519 = 3243779) B3243779
theorem B6927893 : Blo 2161435 6927893 := bbase (se 6 (by rfl) ⟨162372, by rfl⟩ : syracuseStep 6927893 = 324745) (by norm_num)
theorem B4618595 : Blo 2161435 4618595 := bstep (se 1 (by rfl) ⟨3463946, by rfl⟩ : syracuseStep 4618595 = 6927893) B6927893
theorem B3079063 : Blo 2161435 3079063 := bstep (se 1 (by rfl) ⟨2309297, by rfl⟩ : syracuseStep 3079063 = 4618595) B4618595
theorem B4105417 : Blo 2161435 4105417 := bstep (se 2 (by rfl) ⟨1539531, by rfl⟩ : syracuseStep 4105417 = 3079063) B3079063
theorem B5473889 : Blo 2161435 5473889 := bstep (se 2 (by rfl) ⟨2052708, by rfl⟩ : syracuseStep 5473889 = 4105417) B4105417
theorem B3649259 : Blo 2161435 3649259 := bstep (se 1 (by rfl) ⟨2736944, by rfl⟩ : syracuseStep 3649259 = 5473889) B5473889
theorem B2432839 : Blo 2161435 2432839 := bstep (se 1 (by rfl) ⟨1824629, by rfl⟩ : syracuseStep 2432839 = 3649259) B3649259
theorem B3243785 : Blo 2161435 3243785 := bstep (se 2 (by rfl) ⟨1216419, by rfl⟩ : syracuseStep 3243785 = 2432839) B2432839
theorem B2162523 : Blo 2161435 2162523 := bstep (se 1 (by rfl) ⟨1621892, by rfl⟩ : syracuseStep 2162523 = 3243785) B3243785
theorem B10947797 : Blo 2161435 10947797 := bbase (se 7 (by rfl) ⟨128294, by rfl⟩ : syracuseStep 10947797 = 256589) (by norm_num)
theorem B7298531 : Blo 2161435 7298531 := bstep (se 1 (by rfl) ⟨5473898, by rfl⟩ : syracuseStep 7298531 = 10947797) B10947797
theorem B4865687 : Blo 2161435 4865687 := bstep (se 1 (by rfl) ⟨3649265, by rfl⟩ : syracuseStep 4865687 = 7298531) B7298531
theorem B3243791 : Blo 2161435 3243791 := bstep (se 1 (by rfl) ⟨2432843, by rfl⟩ : syracuseStep 3243791 = 4865687) B4865687
theorem B2162527 : Blo 2161435 2162527 := bstep (se 1 (by rfl) ⟨1621895, by rfl⟩ : syracuseStep 2162527 = 3243791) B3243791
theorem B3243797 : Blo 2161435 3243797 := bbase (se 6 (by rfl) ⟨76026, by rfl⟩ : syracuseStep 3243797 = 152053) (by norm_num)
theorem B2162531 : Blo 2161435 2162531 := bstep (se 1 (by rfl) ⟨1621898, by rfl⟩ : syracuseStep 2162531 = 3243797) B3243797
theorem B2812153 : Blo 2161435 2812153 := bbase (se 2 (by rfl) ⟨1054557, by rfl⟩ : syracuseStep 2812153 = 2109115) (by norm_num)
theorem B3749537 : Blo 2161435 3749537 := bstep (se 2 (by rfl) ⟨1406076, by rfl⟩ : syracuseStep 3749537 = 2812153) B2812153
theorem B2499691 : Blo 2161435 2499691 := bstep (se 1 (by rfl) ⟨1874768, by rfl⟩ : syracuseStep 2499691 = 3749537) B3749537
theorem B3332921 : Blo 2161435 3332921 := bstep (se 2 (by rfl) ⟨1249845, by rfl⟩ : syracuseStep 3332921 = 2499691) B2499691
theorem B8887789 : Blo 2161435 8887789 := bstep (se 3 (by rfl) ⟨1666460, by rfl⟩ : syracuseStep 8887789 = 3332921) B3332921
theorem B11850385 : Blo 2161435 11850385 := bstep (se 2 (by rfl) ⟨4443894, by rfl⟩ : syracuseStep 11850385 = 8887789) B8887789
theorem B15800513 : Blo 2161435 15800513 := bstep (se 2 (by rfl) ⟨5925192, by rfl⟩ : syracuseStep 15800513 = 11850385) B11850385
theorem B42134701 : Blo 2161435 42134701 := bstep (se 3 (by rfl) ⟨7900256, by rfl⟩ : syracuseStep 42134701 = 15800513) B15800513
theorem B56179601 : Blo 2161435 56179601 := bstep (se 2 (by rfl) ⟨21067350, by rfl⟩ : syracuseStep 56179601 = 42134701) B42134701
theorem B37453067 : Blo 2161435 37453067 := bstep (se 1 (by rfl) ⟨28089800, by rfl⟩ : syracuseStep 37453067 = 56179601) B56179601
theorem B24968711 : Blo 2161435 24968711 := bstep (se 1 (by rfl) ⟨18726533, by rfl⟩ : syracuseStep 24968711 = 37453067) B37453067
theorem B16645807 : Blo 2161435 16645807 := bstep (se 1 (by rfl) ⟨12484355, by rfl⟩ : syracuseStep 16645807 = 24968711) B24968711
theorem B22194409 : Blo 2161435 22194409 := bstep (se 2 (by rfl) ⟨8322903, by rfl⟩ : syracuseStep 22194409 = 16645807) B16645807
theorem B29592545 : Blo 2161435 29592545 := bstep (se 2 (by rfl) ⟨11097204, by rfl⟩ : syracuseStep 29592545 = 22194409) B22194409
theorem B78913453 : Blo 2161435 78913453 := bstep (se 3 (by rfl) ⟨14796272, by rfl⟩ : syracuseStep 78913453 = 29592545) B29592545
theorem B105217937 : Blo 2161435 105217937 := bstep (se 2 (by rfl) ⟨39456726, by rfl⟩ : syracuseStep 105217937 = 78913453) B78913453
theorem B70145291 : Blo 2161435 70145291 := bstep (se 1 (by rfl) ⟨52608968, by rfl⟩ : syracuseStep 70145291 = 105217937) B105217937
theorem B46763527 : Blo 2161435 46763527 := bstep (se 1 (by rfl) ⟨35072645, by rfl⟩ : syracuseStep 46763527 = 70145291) B70145291
theorem B62351369 : Blo 2161435 62351369 := bstep (se 2 (by rfl) ⟨23381763, by rfl⟩ : syracuseStep 62351369 = 46763527) B46763527
theorem B41567579 : Blo 2161435 41567579 := bstep (se 1 (by rfl) ⟨31175684, by rfl⟩ : syracuseStep 41567579 = 62351369) B62351369
theorem B27711719 : Blo 2161435 27711719 := bstep (se 1 (by rfl) ⟨20783789, by rfl⟩ : syracuseStep 27711719 = 41567579) B41567579
theorem B18474479 : Blo 2161435 18474479 := bstep (se 1 (by rfl) ⟨13855859, by rfl⟩ : syracuseStep 18474479 = 27711719) B27711719
theorem B12316319 : Blo 2161435 12316319 := bstep (se 1 (by rfl) ⟨9237239, by rfl⟩ : syracuseStep 12316319 = 18474479) B18474479
theorem B8210879 : Blo 2161435 8210879 := bstep (se 1 (by rfl) ⟨6158159, by rfl⟩ : syracuseStep 8210879 = 12316319) B12316319
theorem B5473919 : Blo 2161435 5473919 := bstep (se 1 (by rfl) ⟨4105439, by rfl⟩ : syracuseStep 5473919 = 8210879) B8210879
theorem B3649279 : Blo 2161435 3649279 := bstep (se 1 (by rfl) ⟨2736959, by rfl⟩ : syracuseStep 3649279 = 5473919) B5473919
theorem B4865705 : Blo 2161435 4865705 := bstep (se 2 (by rfl) ⟨1824639, by rfl⟩ : syracuseStep 4865705 = 3649279) B3649279
theorem B3243803 : Blo 2161435 3243803 := bstep (se 1 (by rfl) ⟨2432852, by rfl⟩ : syracuseStep 3243803 = 4865705) B4865705
theorem B2162535 : Blo 2161435 2162535 := bstep (se 1 (by rfl) ⟨1621901, by rfl⟩ : syracuseStep 2162535 = 3243803) B3243803
theorem B2432857 : Blo 2161435 2432857 := bbase (se 2 (by rfl) ⟨912321, by rfl⟩ : syracuseStep 2432857 = 1824643) (by norm_num)
theorem B3243809 : Blo 2161435 3243809 := bstep (se 2 (by rfl) ⟨1216428, by rfl⟩ : syracuseStep 3243809 = 2432857) B2432857
theorem B2162539 : Blo 2161435 2162539 := bstep (se 1 (by rfl) ⟨1621904, by rfl⟩ : syracuseStep 2162539 = 3243809) B3243809
theorem B4618637 : Blo 2161435 4618637 := bbase (se 3 (by rfl) ⟨865994, by rfl⟩ : syracuseStep 4618637 = 1731989) (by norm_num)
theorem B3079091 : Blo 2161435 3079091 := bstep (se 1 (by rfl) ⟨2309318, by rfl⟩ : syracuseStep 3079091 = 4618637) B4618637
theorem B8210909 : Blo 2161435 8210909 := bstep (se 3 (by rfl) ⟨1539545, by rfl⟩ : syracuseStep 8210909 = 3079091) B3079091
theorem B5473939 : Blo 2161435 5473939 := bstep (se 1 (by rfl) ⟨4105454, by rfl⟩ : syracuseStep 5473939 = 8210909) B8210909
theorem B7298585 : Blo 2161435 7298585 := bstep (se 2 (by rfl) ⟨2736969, by rfl⟩ : syracuseStep 7298585 = 5473939) B5473939
theorem B4865723 : Blo 2161435 4865723 := bstep (se 1 (by rfl) ⟨3649292, by rfl⟩ : syracuseStep 4865723 = 7298585) B7298585
theorem B3243815 : Blo 2161435 3243815 := bstep (se 1 (by rfl) ⟨2432861, by rfl⟩ : syracuseStep 3243815 = 4865723) B4865723
theorem B2162543 : Blo 2161435 2162543 := bstep (se 1 (by rfl) ⟨1621907, by rfl⟩ : syracuseStep 2162543 = 3243815) B3243815
theorem B3243821 : Blo 2161435 3243821 := bbase (se 3 (by rfl) ⟨608216, by rfl⟩ : syracuseStep 3243821 = 1216433) (by norm_num)
theorem B2162547 : Blo 2161435 2162547 := bstep (se 1 (by rfl) ⟨1621910, by rfl⟩ : syracuseStep 2162547 = 3243821) B3243821
theorem B4865741 : Blo 2161435 4865741 := bbase (se 3 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 4865741 = 1824653) (by norm_num)
theorem B3243827 : Blo 2161435 3243827 := bstep (se 1 (by rfl) ⟨2432870, by rfl⟩ : syracuseStep 3243827 = 4865741) B4865741
theorem B2162551 : Blo 2161435 2162551 := bstep (se 1 (by rfl) ⟨1621913, by rfl⟩ : syracuseStep 2162551 = 3243827) B3243827
theorem B2736985 : Blo 2161435 2736985 := bbase (se 2 (by rfl) ⟨1026369, by rfl⟩ : syracuseStep 2736985 = 2052739) (by norm_num)
theorem B3649313 : Blo 2161435 3649313 := bstep (se 2 (by rfl) ⟨1368492, by rfl⟩ : syracuseStep 3649313 = 2736985) B2736985
theorem B2432875 : Blo 2161435 2432875 := bstep (se 1 (by rfl) ⟨1824656, by rfl⟩ : syracuseStep 2432875 = 3649313) B3649313
theorem B3243833 : Blo 2161435 3243833 := bstep (se 2 (by rfl) ⟨1216437, by rfl⟩ : syracuseStep 3243833 = 2432875) B2432875
theorem B2162555 : Blo 2161435 2162555 := bstep (se 1 (by rfl) ⟨1621916, by rfl⟩ : syracuseStep 2162555 = 3243833) B3243833
theorem B5196005 : Blo 2161435 5196005 := bbase (se 4 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 5196005 = 974251) (by norm_num)
theorem B3464003 : Blo 2161435 3464003 := bstep (se 1 (by rfl) ⟨2598002, by rfl⟩ : syracuseStep 3464003 = 5196005) B5196005
theorem B9237341 : Blo 2161435 9237341 := bstep (se 3 (by rfl) ⟨1732001, by rfl⟩ : syracuseStep 9237341 = 3464003) B3464003
theorem B24632909 : Blo 2161435 24632909 := bstep (se 3 (by rfl) ⟨4618670, by rfl⟩ : syracuseStep 24632909 = 9237341) B9237341
theorem B16421939 : Blo 2161435 16421939 := bstep (se 1 (by rfl) ⟨12316454, by rfl⟩ : syracuseStep 16421939 = 24632909) B24632909
theorem B10947959 : Blo 2161435 10947959 := bstep (se 1 (by rfl) ⟨8210969, by rfl⟩ : syracuseStep 10947959 = 16421939) B16421939
theorem B7298639 : Blo 2161435 7298639 := bstep (se 1 (by rfl) ⟨5473979, by rfl⟩ : syracuseStep 7298639 = 10947959) B10947959
theorem B4865759 : Blo 2161435 4865759 := bstep (se 1 (by rfl) ⟨3649319, by rfl⟩ : syracuseStep 4865759 = 7298639) B7298639
theorem B3243839 : Blo 2161435 3243839 := bstep (se 1 (by rfl) ⟨2432879, by rfl⟩ : syracuseStep 3243839 = 4865759) B4865759
theorem B2162559 : Blo 2161435 2162559 := bstep (se 1 (by rfl) ⟨1621919, by rfl⟩ : syracuseStep 2162559 = 3243839) B3243839
theorem B3243845 : Blo 2161435 3243845 := bbase (se 4 (by rfl) ⟨304110, by rfl⟩ : syracuseStep 3243845 = 608221) (by norm_num)
theorem B2162563 : Blo 2161435 2162563 := bstep (se 1 (by rfl) ⟨1621922, by rfl⟩ : syracuseStep 2162563 = 3243845) B3243845
theorem B3649333 : Blo 2161435 3649333 := bbase (se 5 (by rfl) ⟨171062, by rfl⟩ : syracuseStep 3649333 = 342125) (by norm_num)
theorem B4865777 : Blo 2161435 4865777 := bstep (se 2 (by rfl) ⟨1824666, by rfl⟩ : syracuseStep 4865777 = 3649333) B3649333
theorem B3243851 : Blo 2161435 3243851 := bstep (se 1 (by rfl) ⟨2432888, by rfl⟩ : syracuseStep 3243851 = 4865777) B4865777
theorem B2162567 : Blo 2161435 2162567 := bstep (se 1 (by rfl) ⟨1621925, by rfl⟩ : syracuseStep 2162567 = 3243851) B3243851
theorem B2432893 : Blo 2161435 2432893 := bbase (se 3 (by rfl) ⟨456167, by rfl⟩ : syracuseStep 2432893 = 912335) (by norm_num)
theorem B3243857 : Blo 2161435 3243857 := bstep (se 2 (by rfl) ⟨1216446, by rfl⟩ : syracuseStep 3243857 = 2432893) B2432893
theorem B2162571 : Blo 2161435 2162571 := bstep (se 1 (by rfl) ⟨1621928, by rfl⟩ : syracuseStep 2162571 = 3243857) B3243857
theorem B7298693 : Blo 2161435 7298693 := bbase (se 4 (by rfl) ⟨684252, by rfl⟩ : syracuseStep 7298693 = 1368505) (by norm_num)
theorem B4865795 : Blo 2161435 4865795 := bstep (se 1 (by rfl) ⟨3649346, by rfl⟩ : syracuseStep 4865795 = 7298693) B7298693
theorem B3243863 : Blo 2161435 3243863 := bstep (se 1 (by rfl) ⟨2432897, by rfl⟩ : syracuseStep 3243863 = 4865795) B4865795
theorem B2162575 : Blo 2161435 2162575 := bstep (se 1 (by rfl) ⟨1621931, by rfl⟩ : syracuseStep 2162575 = 3243863) B3243863
theorem B3243869 : Blo 2161435 3243869 := bbase (se 3 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 3243869 = 1216451) (by norm_num)
theorem B2162579 : Blo 2161435 2162579 := bstep (se 1 (by rfl) ⟨1621934, by rfl⟩ : syracuseStep 2162579 = 3243869) B3243869
theorem B4865813 : Blo 2161435 4865813 := bbase (se 6 (by rfl) ⟨114042, by rfl⟩ : syracuseStep 4865813 = 228085) (by norm_num)
theorem B3243875 : Blo 2161435 3243875 := bstep (se 1 (by rfl) ⟨2432906, by rfl⟩ : syracuseStep 3243875 = 4865813) B4865813
theorem B2162583 : Blo 2161435 2162583 := bstep (se 1 (by rfl) ⟨1621937, by rfl⟩ : syracuseStep 2162583 = 3243875) B3243875
theorem B8211077 : Blo 2161435 8211077 := bbase (se 4 (by rfl) ⟨769788, by rfl⟩ : syracuseStep 8211077 = 1539577) (by norm_num)
theorem B5474051 : Blo 2161435 5474051 := bstep (se 1 (by rfl) ⟨4105538, by rfl⟩ : syracuseStep 5474051 = 8211077) B8211077
theorem B3649367 : Blo 2161435 3649367 := bstep (se 1 (by rfl) ⟨2737025, by rfl⟩ : syracuseStep 3649367 = 5474051) B5474051
theorem B2432911 : Blo 2161435 2432911 := bstep (se 1 (by rfl) ⟨1824683, by rfl⟩ : syracuseStep 2432911 = 3649367) B3649367
theorem B3243881 : Blo 2161435 3243881 := bstep (se 2 (by rfl) ⟨1216455, by rfl⟩ : syracuseStep 3243881 = 2432911) B2432911
theorem B2162587 : Blo 2161435 2162587 := bstep (se 1 (by rfl) ⟨1621940, by rfl⟩ : syracuseStep 2162587 = 3243881) B3243881
theorem B2598041 : Blo 2161435 2598041 := bbase (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) (by norm_num)
theorem B6928109 : Blo 2161435 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B4618739 : Blo 2161435 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B12316637 : Blo 2161435 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B8211091 : Blo 2161435 8211091 := bstep (se 1 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 8211091 = 12316637) B12316637
theorem B10948121 : Blo 2161435 10948121 := bstep (se 2 (by rfl) ⟨4105545, by rfl⟩ : syracuseStep 10948121 = 8211091) B8211091
theorem B7298747 : Blo 2161435 7298747 := bstep (se 1 (by rfl) ⟨5474060, by rfl⟩ : syracuseStep 7298747 = 10948121) B10948121
theorem B4865831 : Blo 2161435 4865831 := bstep (se 1 (by rfl) ⟨3649373, by rfl⟩ : syracuseStep 4865831 = 7298747) B7298747
theorem B3243887 : Blo 2161435 3243887 := bstep (se 1 (by rfl) ⟨2432915, by rfl⟩ : syracuseStep 3243887 = 4865831) B4865831
theorem B2162591 : Blo 2161435 2162591 := bstep (se 1 (by rfl) ⟨1621943, by rfl⟩ : syracuseStep 2162591 = 3243887) B3243887
theorem B3243893 : Blo 2161435 3243893 := bbase (se 5 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 3243893 = 304115) (by norm_num)
theorem B2162595 : Blo 2161435 2162595 := bstep (se 1 (by rfl) ⟨1621946, by rfl⟩ : syracuseStep 2162595 = 3243893) B3243893
theorem B4618757 : Blo 2161435 4618757 := bbase (se 4 (by rfl) ⟨433008, by rfl⟩ : syracuseStep 4618757 = 866017) (by norm_num)
theorem B3079171 : Blo 2161435 3079171 := bstep (se 1 (by rfl) ⟨2309378, by rfl⟩ : syracuseStep 3079171 = 4618757) B4618757
theorem B4105561 : Blo 2161435 4105561 := bstep (se 2 (by rfl) ⟨1539585, by rfl⟩ : syracuseStep 4105561 = 3079171) B3079171
theorem B5474081 : Blo 2161435 5474081 := bstep (se 2 (by rfl) ⟨2052780, by rfl⟩ : syracuseStep 5474081 = 4105561) B4105561
theorem B3649387 : Blo 2161435 3649387 := bstep (se 1 (by rfl) ⟨2737040, by rfl⟩ : syracuseStep 3649387 = 5474081) B5474081
theorem B4865849 : Blo 2161435 4865849 := bstep (se 2 (by rfl) ⟨1824693, by rfl⟩ : syracuseStep 4865849 = 3649387) B3649387
theorem B3243899 : Blo 2161435 3243899 := bstep (se 1 (by rfl) ⟨2432924, by rfl⟩ : syracuseStep 3243899 = 4865849) B4865849
theorem B2162599 : Blo 2161435 2162599 := bstep (se 1 (by rfl) ⟨1621949, by rfl⟩ : syracuseStep 2162599 = 3243899) B3243899
theorem B2432929 : Blo 2161435 2432929 := bbase (se 2 (by rfl) ⟨912348, by rfl⟩ : syracuseStep 2432929 = 1824697) (by norm_num)
theorem B3243905 : Blo 2161435 3243905 := bstep (se 2 (by rfl) ⟨1216464, by rfl⟩ : syracuseStep 3243905 = 2432929) B2432929
theorem B2162603 : Blo 2161435 2162603 := bstep (se 1 (by rfl) ⟨1621952, by rfl⟩ : syracuseStep 2162603 = 3243905) B3243905
theorem B5474101 : Blo 2161435 5474101 := bbase (se 5 (by rfl) ⟨256598, by rfl⟩ : syracuseStep 5474101 = 513197) (by norm_num)
theorem B7298801 : Blo 2161435 7298801 := bstep (se 2 (by rfl) ⟨2737050, by rfl⟩ : syracuseStep 7298801 = 5474101) B5474101
theorem B4865867 : Blo 2161435 4865867 := bstep (se 1 (by rfl) ⟨3649400, by rfl⟩ : syracuseStep 4865867 = 7298801) B7298801
theorem B3243911 : Blo 2161435 3243911 := bstep (se 1 (by rfl) ⟨2432933, by rfl⟩ : syracuseStep 3243911 = 4865867) B4865867
theorem B2162607 : Blo 2161435 2162607 := bstep (se 1 (by rfl) ⟨1621955, by rfl⟩ : syracuseStep 2162607 = 3243911) B3243911
theorem B3243917 : Blo 2161435 3243917 := bbase (se 3 (by rfl) ⟨608234, by rfl⟩ : syracuseStep 3243917 = 1216469) (by norm_num)
theorem B2162611 : Blo 2161435 2162611 := bstep (se 1 (by rfl) ⟨1621958, by rfl⟩ : syracuseStep 2162611 = 3243917) B3243917
theorem B4865885 : Blo 2161435 4865885 := bbase (se 3 (by rfl) ⟨912353, by rfl⟩ : syracuseStep 4865885 = 1824707) (by norm_num)
theorem B3243923 : Blo 2161435 3243923 := bstep (se 1 (by rfl) ⟨2432942, by rfl⟩ : syracuseStep 3243923 = 4865885) B4865885
theorem B2162615 : Blo 2161435 2162615 := bstep (se 1 (by rfl) ⟨1621961, by rfl⟩ : syracuseStep 2162615 = 3243923) B3243923
theorem B3649421 : Blo 2161435 3649421 := bbase (se 3 (by rfl) ⟨684266, by rfl⟩ : syracuseStep 3649421 = 1368533) (by norm_num)
theorem B2432947 : Blo 2161435 2432947 := bstep (se 1 (by rfl) ⟨1824710, by rfl⟩ : syracuseStep 2432947 = 3649421) B3649421
theorem B3243929 : Blo 2161435 3243929 := bstep (se 2 (by rfl) ⟨1216473, by rfl⟩ : syracuseStep 3243929 = 2432947) B2432947
theorem B2162619 : Blo 2161435 2162619 := bstep (se 1 (by rfl) ⟨1621964, by rfl⟩ : syracuseStep 2162619 = 3243929) B3243929
theorem B5548829 : Blo 2161435 5548829 := bbase (se 3 (by rfl) ⟨1040405, by rfl⟩ : syracuseStep 5548829 = 2080811) (by norm_num)
theorem B14796877 : Blo 2161435 14796877 := bstep (se 3 (by rfl) ⟨2774414, by rfl⟩ : syracuseStep 14796877 = 5548829) B5548829
theorem B19729169 : Blo 2161435 19729169 := bstep (se 2 (by rfl) ⟨7398438, by rfl⟩ : syracuseStep 19729169 = 14796877) B14796877
theorem B13152779 : Blo 2161435 13152779 := bstep (se 1 (by rfl) ⟨9864584, by rfl⟩ : syracuseStep 13152779 = 19729169) B19729169
theorem B8768519 : Blo 2161435 8768519 := bstep (se 1 (by rfl) ⟨6576389, by rfl⟩ : syracuseStep 8768519 = 13152779) B13152779
theorem B5845679 : Blo 2161435 5845679 := bstep (se 1 (by rfl) ⟨4384259, by rfl⟩ : syracuseStep 5845679 = 8768519) B8768519
theorem B3897119 : Blo 2161435 3897119 := bstep (se 1 (by rfl) ⟨2922839, by rfl⟩ : syracuseStep 3897119 = 5845679) B5845679
theorem B10392317 : Blo 2161435 10392317 := bstep (se 3 (by rfl) ⟨1948559, by rfl⟩ : syracuseStep 10392317 = 3897119) B3897119
theorem B6928211 : Blo 2161435 6928211 := bstep (se 1 (by rfl) ⟨5196158, by rfl⟩ : syracuseStep 6928211 = 10392317) B10392317
theorem B18475229 : Blo 2161435 18475229 := bstep (se 3 (by rfl) ⟨3464105, by rfl⟩ : syracuseStep 18475229 = 6928211) B6928211
theorem B12316819 : Blo 2161435 12316819 := bstep (se 1 (by rfl) ⟨9237614, by rfl⟩ : syracuseStep 12316819 = 18475229) B18475229
theorem B16422425 : Blo 2161435 16422425 := bstep (se 2 (by rfl) ⟨6158409, by rfl⟩ : syracuseStep 16422425 = 12316819) B12316819
theorem B10948283 : Blo 2161435 10948283 := bstep (se 1 (by rfl) ⟨8211212, by rfl⟩ : syracuseStep 10948283 = 16422425) B16422425
theorem B7298855 : Blo 2161435 7298855 := bstep (se 1 (by rfl) ⟨5474141, by rfl⟩ : syracuseStep 7298855 = 10948283) B10948283
theorem B4865903 : Blo 2161435 4865903 := bstep (se 1 (by rfl) ⟨3649427, by rfl⟩ : syracuseStep 4865903 = 7298855) B7298855
theorem B3243935 : Blo 2161435 3243935 := bstep (se 1 (by rfl) ⟨2432951, by rfl⟩ : syracuseStep 3243935 = 4865903) B4865903
theorem B2162623 : Blo 2161435 2162623 := bstep (se 1 (by rfl) ⟨1621967, by rfl⟩ : syracuseStep 2162623 = 3243935) B3243935
theorem B3243941 : Blo 2161435 3243941 := bbase (se 4 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 3243941 = 608239) (by norm_num)
theorem B2162627 : Blo 2161435 2162627 := bstep (se 1 (by rfl) ⟨1621970, by rfl⟩ : syracuseStep 2162627 = 3243941) B3243941
theorem B2737081 : Blo 2161435 2737081 := bbase (se 2 (by rfl) ⟨1026405, by rfl⟩ : syracuseStep 2737081 = 2052811) (by norm_num)
theorem B3649441 : Blo 2161435 3649441 := bstep (se 2 (by rfl) ⟨1368540, by rfl⟩ : syracuseStep 3649441 = 2737081) B2737081
theorem B4865921 : Blo 2161435 4865921 := bstep (se 2 (by rfl) ⟨1824720, by rfl⟩ : syracuseStep 4865921 = 3649441) B3649441
theorem B3243947 : Blo 2161435 3243947 := bstep (se 1 (by rfl) ⟨2432960, by rfl⟩ : syracuseStep 3243947 = 4865921) B4865921
theorem B2162631 : Blo 2161435 2162631 := bstep (se 1 (by rfl) ⟨1621973, by rfl⟩ : syracuseStep 2162631 = 3243947) B3243947
theorem B2432965 : Blo 2161435 2432965 := bbase (se 4 (by rfl) ⟨228090, by rfl⟩ : syracuseStep 2432965 = 456181) (by norm_num)
theorem B3243953 : Blo 2161435 3243953 := bstep (se 2 (by rfl) ⟨1216482, by rfl⟩ : syracuseStep 3243953 = 2432965) B2432965
theorem B2162635 : Blo 2161435 2162635 := bstep (se 1 (by rfl) ⟨1621976, by rfl⟩ : syracuseStep 2162635 = 3243953) B3243953
theorem B4105637 : Blo 2161435 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2737091 : Blo 2161435 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B7298909 : Blo 2161435 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B4865939 : Blo 2161435 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B3243959 : Blo 2161435 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B2162639 : Blo 2161435 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B3243965 : Blo 2161435 3243965 := bbase (se 3 (by rfl) ⟨608243, by rfl⟩ : syracuseStep 3243965 = 1216487) (by norm_num)
theorem B2162643 : Blo 2161435 2162643 := bstep (se 1 (by rfl) ⟨1621982, by rfl⟩ : syracuseStep 2162643 = 3243965) B3243965
theorem B4865957 : Blo 2161435 4865957 := bbase (se 4 (by rfl) ⟨456183, by rfl⟩ : syracuseStep 4865957 = 912367) (by norm_num)
theorem B3243971 : Blo 2161435 3243971 := bstep (se 1 (by rfl) ⟨2432978, by rfl⟩ : syracuseStep 3243971 = 4865957) B4865957
theorem B2162647 : Blo 2161435 2162647 := bstep (se 1 (by rfl) ⟨1621985, by rfl⟩ : syracuseStep 2162647 = 3243971) B3243971
theorem B5474213 : Blo 2161435 5474213 := bbase (se 4 (by rfl) ⟨513207, by rfl⟩ : syracuseStep 5474213 = 1026415) (by norm_num)
theorem B3649475 : Blo 2161435 3649475 := bstep (se 1 (by rfl) ⟨2737106, by rfl⟩ : syracuseStep 3649475 = 5474213) B5474213
theorem B2432983 : Blo 2161435 2432983 := bstep (se 1 (by rfl) ⟨1824737, by rfl⟩ : syracuseStep 2432983 = 3649475) B3649475
theorem B3243977 : Blo 2161435 3243977 := bstep (se 2 (by rfl) ⟨1216491, by rfl⟩ : syracuseStep 3243977 = 2432983) B2432983
theorem B2162651 : Blo 2161435 2162651 := bstep (se 1 (by rfl) ⟨1621988, by rfl⟩ : syracuseStep 2162651 = 3243977) B3243977
theorem B6158501 : Blo 2161435 6158501 := bbase (se 4 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 6158501 = 1154719) (by norm_num)
theorem B4105667 : Blo 2161435 4105667 := bstep (se 1 (by rfl) ⟨3079250, by rfl⟩ : syracuseStep 4105667 = 6158501) B6158501
theorem B10948445 : Blo 2161435 10948445 := bstep (se 3 (by rfl) ⟨2052833, by rfl⟩ : syracuseStep 10948445 = 4105667) B4105667
theorem B7298963 : Blo 2161435 7298963 := bstep (se 1 (by rfl) ⟨5474222, by rfl⟩ : syracuseStep 7298963 = 10948445) B10948445
theorem B4865975 : Blo 2161435 4865975 := bstep (se 1 (by rfl) ⟨3649481, by rfl⟩ : syracuseStep 4865975 = 7298963) B7298963
theorem B3243983 : Blo 2161435 3243983 := bstep (se 1 (by rfl) ⟨2432987, by rfl⟩ : syracuseStep 3243983 = 4865975) B4865975
theorem B2162655 : Blo 2161435 2162655 := bstep (se 1 (by rfl) ⟨1621991, by rfl⟩ : syracuseStep 2162655 = 3243983) B3243983
theorem B3243989 : Blo 2161435 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B2162659 : Blo 2161435 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B8211365 : Blo 2161435 8211365 := bbase (se 4 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 8211365 = 1539631) (by norm_num)
theorem B5474243 : Blo 2161435 5474243 := bstep (se 1 (by rfl) ⟨4105682, by rfl⟩ : syracuseStep 5474243 = 8211365) B8211365
theorem B3649495 : Blo 2161435 3649495 := bstep (se 1 (by rfl) ⟨2737121, by rfl⟩ : syracuseStep 3649495 = 5474243) B5474243
theorem B4865993 : Blo 2161435 4865993 := bstep (se 2 (by rfl) ⟨1824747, by rfl⟩ : syracuseStep 4865993 = 3649495) B3649495
theorem B3243995 : Blo 2161435 3243995 := bstep (se 1 (by rfl) ⟨2432996, by rfl⟩ : syracuseStep 3243995 = 4865993) B4865993
theorem B2162663 : Blo 2161435 2162663 := bstep (se 1 (by rfl) ⟨1621997, by rfl⟩ : syracuseStep 2162663 = 3243995) B3243995
theorem B2433001 : Blo 2161435 2433001 := bbase (se 2 (by rfl) ⟨912375, by rfl⟩ : syracuseStep 2433001 = 1824751) (by norm_num)
theorem B3244001 : Blo 2161435 3244001 := bstep (se 2 (by rfl) ⟨1216500, by rfl⟩ : syracuseStep 3244001 = 2433001) B2433001
theorem B2162667 : Blo 2161435 2162667 := bstep (se 1 (by rfl) ⟨1622000, by rfl⟩ : syracuseStep 2162667 = 3244001) B3244001
theorem B3288269 : Blo 2161435 3288269 := bbase (se 3 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 3288269 = 1233101) (by norm_num)
theorem B2192179 : Blo 2161435 2192179 := bstep (se 1 (by rfl) ⟨1644134, by rfl⟩ : syracuseStep 2192179 = 3288269) B3288269
theorem B2922905 : Blo 2161435 2922905 := bstep (se 2 (by rfl) ⟨1096089, by rfl⟩ : syracuseStep 2922905 = 2192179) B2192179
theorem B7794413 : Blo 2161435 7794413 := bstep (se 3 (by rfl) ⟨1461452, by rfl⟩ : syracuseStep 7794413 = 2922905) B2922905
theorem B5196275 : Blo 2161435 5196275 := bstep (se 1 (by rfl) ⟨3897206, by rfl⟩ : syracuseStep 5196275 = 7794413) B7794413
theorem B3464183 : Blo 2161435 3464183 := bstep (se 1 (by rfl) ⟨2598137, by rfl⟩ : syracuseStep 3464183 = 5196275) B5196275
theorem B2309455 : Blo 2161435 2309455 := bstep (se 1 (by rfl) ⟨1732091, by rfl⟩ : syracuseStep 2309455 = 3464183) B3464183
theorem B12317093 : Blo 2161435 12317093 := bstep (se 4 (by rfl) ⟨1154727, by rfl⟩ : syracuseStep 12317093 = 2309455) B2309455
theorem B8211395 : Blo 2161435 8211395 := bstep (se 1 (by rfl) ⟨6158546, by rfl⟩ : syracuseStep 8211395 = 12317093) B12317093
theorem B5474263 : Blo 2161435 5474263 := bstep (se 1 (by rfl) ⟨4105697, by rfl⟩ : syracuseStep 5474263 = 8211395) B8211395
theorem B7299017 : Blo 2161435 7299017 := bstep (se 2 (by rfl) ⟨2737131, by rfl⟩ : syracuseStep 7299017 = 5474263) B5474263
theorem B4866011 : Blo 2161435 4866011 := bstep (se 1 (by rfl) ⟨3649508, by rfl⟩ : syracuseStep 4866011 = 7299017) B7299017
theorem B3244007 : Blo 2161435 3244007 := bstep (se 1 (by rfl) ⟨2433005, by rfl⟩ : syracuseStep 3244007 = 4866011) B4866011
theorem B2162671 : Blo 2161435 2162671 := bstep (se 1 (by rfl) ⟨1622003, by rfl⟩ : syracuseStep 2162671 = 3244007) B3244007
theorem B3244013 : Blo 2161435 3244013 := bbase (se 3 (by rfl) ⟨608252, by rfl⟩ : syracuseStep 3244013 = 1216505) (by norm_num)
theorem B2162675 : Blo 2161435 2162675 := bstep (se 1 (by rfl) ⟨1622006, by rfl⟩ : syracuseStep 2162675 = 3244013) B3244013
theorem B4866029 : Blo 2161435 4866029 := bbase (se 3 (by rfl) ⟨912380, by rfl⟩ : syracuseStep 4866029 = 1824761) (by norm_num)
theorem B3244019 : Blo 2161435 3244019 := bstep (se 1 (by rfl) ⟨2433014, by rfl⟩ : syracuseStep 3244019 = 4866029) B4866029
theorem B2162679 : Blo 2161435 2162679 := bstep (se 1 (by rfl) ⟨1622009, by rfl⟩ : syracuseStep 2162679 = 3244019) B3244019
theorem B3897229 : Blo 2161435 3897229 := bbase (se 3 (by rfl) ⟨730730, by rfl⟩ : syracuseStep 3897229 = 1461461) (by norm_num)
theorem B5196305 : Blo 2161435 5196305 := bstep (se 2 (by rfl) ⟨1948614, by rfl⟩ : syracuseStep 5196305 = 3897229) B3897229
theorem B3464203 : Blo 2161435 3464203 := bstep (se 1 (by rfl) ⟨2598152, by rfl⟩ : syracuseStep 3464203 = 5196305) B5196305
theorem B4618937 : Blo 2161435 4618937 := bstep (se 2 (by rfl) ⟨1732101, by rfl⟩ : syracuseStep 4618937 = 3464203) B3464203
theorem B3079291 : Blo 2161435 3079291 := bstep (se 1 (by rfl) ⟨2309468, by rfl⟩ : syracuseStep 3079291 = 4618937) B4618937
theorem B4105721 : Blo 2161435 4105721 := bstep (se 2 (by rfl) ⟨1539645, by rfl⟩ : syracuseStep 4105721 = 3079291) B3079291
theorem B2737147 : Blo 2161435 2737147 := bstep (se 1 (by rfl) ⟨2052860, by rfl⟩ : syracuseStep 2737147 = 4105721) B4105721
theorem B3649529 : Blo 2161435 3649529 := bstep (se 2 (by rfl) ⟨1368573, by rfl⟩ : syracuseStep 3649529 = 2737147) B2737147
theorem B2433019 : Blo 2161435 2433019 := bstep (se 1 (by rfl) ⟨1824764, by rfl⟩ : syracuseStep 2433019 = 3649529) B3649529
theorem B3244025 : Blo 2161435 3244025 := bstep (se 2 (by rfl) ⟨1216509, by rfl⟩ : syracuseStep 3244025 = 2433019) B2433019
theorem B2162683 : Blo 2161435 2162683 := bstep (se 1 (by rfl) ⟨1622012, by rfl⟩ : syracuseStep 2162683 = 3244025) B3244025
theorem B7705637 : Blo 2161435 7705637 := bbase (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) (by norm_num)
theorem B5137091 : Blo 2161435 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B3424727 : Blo 2161435 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B9132605 : Blo 2161435 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B6088403 : Blo 2161435 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B16235741 : Blo 2161435 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B43295309 : Blo 2161435 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B28863539 : Blo 2161435 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B19242359 : Blo 2161435 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B12828239 : Blo 2161435 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B8552159 : Blo 2161435 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B5701439 : Blo 2161435 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B15203837 : Blo 2161435 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B10135891 : Blo 2161435 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B13514521 : Blo 2161435 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B18019361 : Blo 2161435 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B12012907 : Blo 2161435 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B16017209 : Blo 2161435 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B10678139 : Blo 2161435 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B7118759 : Blo 2161435 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B18983357 : Blo 2161435 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B12655571 : Blo 2161435 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B134992757 : Blo 2161435 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B89995171 : Blo 2161435 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B119993561 : Blo 2161435 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B79995707 : Blo 2161435 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B53330471 : Blo 2161435 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B35553647 : Blo 2161435 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B23702431 : Blo 2161435 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B31603241 : Blo 2161435 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B84275309 : Blo 2161435 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B56183539 : Blo 2161435 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B74911385 : Blo 2161435 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B49940923 : Blo 2161435 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B66587897 : Blo 2161435 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B44391931 : Blo 2161435 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B947027861 : Blo 2161435 947027861 := bstep (se 6 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 947027861 = 44391931) B44391931
theorem B631351907 : Blo 2161435 631351907 := bstep (se 1 (by rfl) ⟨473513930, by rfl⟩ : syracuseStep 631351907 = 947027861) B947027861
theorem B420901271 : Blo 2161435 420901271 := bstep (se 1 (by rfl) ⟨315675953, by rfl⟩ : syracuseStep 420901271 = 631351907) B631351907
theorem B280600847 : Blo 2161435 280600847 := bstep (se 1 (by rfl) ⟨210450635, by rfl⟩ : syracuseStep 280600847 = 420901271) B420901271
theorem B187067231 : Blo 2161435 187067231 := bstep (se 1 (by rfl) ⟨140300423, by rfl⟩ : syracuseStep 187067231 = 280600847) B280600847
theorem B124711487 : Blo 2161435 124711487 := bstep (se 1 (by rfl) ⟨93533615, by rfl⟩ : syracuseStep 124711487 = 187067231) B187067231
theorem B83140991 : Blo 2161435 83140991 := bstep (se 1 (by rfl) ⟨62355743, by rfl⟩ : syracuseStep 83140991 = 124711487) B124711487
theorem B55427327 : Blo 2161435 55427327 := bstep (se 1 (by rfl) ⟨41570495, by rfl⟩ : syracuseStep 55427327 = 83140991) B83140991
theorem B36951551 : Blo 2161435 36951551 := bstep (se 1 (by rfl) ⟨27713663, by rfl⟩ : syracuseStep 36951551 = 55427327) B55427327
theorem B24634367 : Blo 2161435 24634367 := bstep (se 1 (by rfl) ⟨18475775, by rfl⟩ : syracuseStep 24634367 = 36951551) B36951551
theorem B16422911 : Blo 2161435 16422911 := bstep (se 1 (by rfl) ⟨12317183, by rfl⟩ : syracuseStep 16422911 = 24634367) B24634367
theorem B10948607 : Blo 2161435 10948607 := bstep (se 1 (by rfl) ⟨8211455, by rfl⟩ : syracuseStep 10948607 = 16422911) B16422911
theorem B7299071 : Blo 2161435 7299071 := bstep (se 1 (by rfl) ⟨5474303, by rfl⟩ : syracuseStep 7299071 = 10948607) B10948607
theorem B4866047 : Blo 2161435 4866047 := bstep (se 1 (by rfl) ⟨3649535, by rfl⟩ : syracuseStep 4866047 = 7299071) B7299071
theorem B3244031 : Blo 2161435 3244031 := bstep (se 1 (by rfl) ⟨2433023, by rfl⟩ : syracuseStep 3244031 = 4866047) B4866047
theorem B2162687 : Blo 2161435 2162687 := bstep (se 1 (by rfl) ⟨1622015, by rfl⟩ : syracuseStep 2162687 = 3244031) B3244031
theorem B3244037 : Blo 2161435 3244037 := bbase (se 4 (by rfl) ⟨304128, by rfl⟩ : syracuseStep 3244037 = 608257) (by norm_num)
theorem B2162691 : Blo 2161435 2162691 := bstep (se 1 (by rfl) ⟨1622018, by rfl⟩ : syracuseStep 2162691 = 3244037) B3244037
theorem B3649549 : Blo 2161435 3649549 := bbase (se 3 (by rfl) ⟨684290, by rfl⟩ : syracuseStep 3649549 = 1368581) (by norm_num)
theorem B4866065 : Blo 2161435 4866065 := bstep (se 2 (by rfl) ⟨1824774, by rfl⟩ : syracuseStep 4866065 = 3649549) B3649549
theorem B3244043 : Blo 2161435 3244043 := bstep (se 1 (by rfl) ⟨2433032, by rfl⟩ : syracuseStep 3244043 = 4866065) B4866065
theorem B2162695 : Blo 2161435 2162695 := bstep (se 1 (by rfl) ⟨1622021, by rfl⟩ : syracuseStep 2162695 = 3244043) B3244043
theorem B2433037 : Blo 2161435 2433037 := bbase (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) (by norm_num)
theorem B3244049 : Blo 2161435 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B2162699 : Blo 2161435 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B7299125 : Blo 2161435 7299125 := bbase (se 5 (by rfl) ⟨342146, by rfl⟩ : syracuseStep 7299125 = 684293) (by norm_num)
theorem B4866083 : Blo 2161435 4866083 := bstep (se 1 (by rfl) ⟨3649562, by rfl⟩ : syracuseStep 4866083 = 7299125) B7299125
theorem B3244055 : Blo 2161435 3244055 := bstep (se 1 (by rfl) ⟨2433041, by rfl⟩ : syracuseStep 3244055 = 4866083) B4866083
theorem B2162703 : Blo 2161435 2162703 := bstep (se 1 (by rfl) ⟨1622027, by rfl⟩ : syracuseStep 2162703 = 3244055) B3244055
theorem B3244061 : Blo 2161435 3244061 := bbase (se 3 (by rfl) ⟨608261, by rfl⟩ : syracuseStep 3244061 = 1216523) (by norm_num)
theorem B2162707 : Blo 2161435 2162707 := bstep (se 1 (by rfl) ⟨1622030, by rfl⟩ : syracuseStep 2162707 = 3244061) B3244061
theorem B4866101 : Blo 2161435 4866101 := bbase (se 5 (by rfl) ⟨228098, by rfl⟩ : syracuseStep 4866101 = 456197) (by norm_num)
theorem B3244067 : Blo 2161435 3244067 := bstep (se 1 (by rfl) ⟨2433050, by rfl⟩ : syracuseStep 3244067 = 4866101) B4866101
theorem B2162711 : Blo 2161435 2162711 := bstep (se 1 (by rfl) ⟨1622033, by rfl⟩ : syracuseStep 2162711 = 3244067) B3244067
theorem B11098133 : Blo 2161435 11098133 := bbase (se 6 (by rfl) ⟨260112, by rfl⟩ : syracuseStep 11098133 = 520225) (by norm_num)
theorem B7398755 : Blo 2161435 7398755 := bstep (se 1 (by rfl) ⟨5549066, by rfl⟩ : syracuseStep 7398755 = 11098133) B11098133
theorem B4932503 : Blo 2161435 4932503 := bstep (se 1 (by rfl) ⟨3699377, by rfl⟩ : syracuseStep 4932503 = 7398755) B7398755
theorem B3288335 : Blo 2161435 3288335 := bstep (se 1 (by rfl) ⟨2466251, by rfl⟩ : syracuseStep 3288335 = 4932503) B4932503
theorem B8768893 : Blo 2161435 8768893 := bstep (se 3 (by rfl) ⟨1644167, by rfl⟩ : syracuseStep 8768893 = 3288335) B3288335
theorem B11691857 : Blo 2161435 11691857 := bstep (se 2 (by rfl) ⟨4384446, by rfl⟩ : syracuseStep 11691857 = 8768893) B8768893
theorem B7794571 : Blo 2161435 7794571 := bstep (se 1 (by rfl) ⟨5845928, by rfl⟩ : syracuseStep 7794571 = 11691857) B11691857
theorem B10392761 : Blo 2161435 10392761 := bstep (se 2 (by rfl) ⟨3897285, by rfl⟩ : syracuseStep 10392761 = 7794571) B7794571
theorem B6928507 : Blo 2161435 6928507 := bstep (se 1 (by rfl) ⟨5196380, by rfl⟩ : syracuseStep 6928507 = 10392761) B10392761
theorem B9238009 : Blo 2161435 9238009 := bstep (se 2 (by rfl) ⟨3464253, by rfl⟩ : syracuseStep 9238009 = 6928507) B6928507
theorem B12317345 : Blo 2161435 12317345 := bstep (se 2 (by rfl) ⟨4619004, by rfl⟩ : syracuseStep 12317345 = 9238009) B9238009
theorem B8211563 : Blo 2161435 8211563 := bstep (se 1 (by rfl) ⟨6158672, by rfl⟩ : syracuseStep 8211563 = 12317345) B12317345
theorem B5474375 : Blo 2161435 5474375 := bstep (se 1 (by rfl) ⟨4105781, by rfl⟩ : syracuseStep 5474375 = 8211563) B8211563
theorem B3649583 : Blo 2161435 3649583 := bstep (se 1 (by rfl) ⟨2737187, by rfl⟩ : syracuseStep 3649583 = 5474375) B5474375
theorem B2433055 : Blo 2161435 2433055 := bstep (se 1 (by rfl) ⟨1824791, by rfl⟩ : syracuseStep 2433055 = 3649583) B3649583
theorem B3244073 : Blo 2161435 3244073 := bstep (se 2 (by rfl) ⟨1216527, by rfl⟩ : syracuseStep 3244073 = 2433055) B2433055
theorem B2162715 : Blo 2161435 2162715 := bstep (se 1 (by rfl) ⟨1622036, by rfl⟩ : syracuseStep 2162715 = 3244073) B3244073
theorem B3288341 : Blo 2161435 3288341 := bbase (se 6 (by rfl) ⟨77070, by rfl⟩ : syracuseStep 3288341 = 154141) (by norm_num)
theorem B2192227 : Blo 2161435 2192227 := bstep (se 1 (by rfl) ⟨1644170, by rfl⟩ : syracuseStep 2192227 = 3288341) B3288341
theorem B11691877 : Blo 2161435 11691877 := bstep (se 4 (by rfl) ⟨1096113, by rfl⟩ : syracuseStep 11691877 = 2192227) B2192227
theorem B15589169 : Blo 2161435 15589169 := bstep (se 2 (by rfl) ⟨5845938, by rfl⟩ : syracuseStep 15589169 = 11691877) B11691877
theorem B10392779 : Blo 2161435 10392779 := bstep (se 1 (by rfl) ⟨7794584, by rfl⟩ : syracuseStep 10392779 = 15589169) B15589169
theorem B6928519 : Blo 2161435 6928519 := bstep (se 1 (by rfl) ⟨5196389, by rfl⟩ : syracuseStep 6928519 = 10392779) B10392779
theorem B9238025 : Blo 2161435 9238025 := bstep (se 2 (by rfl) ⟨3464259, by rfl⟩ : syracuseStep 9238025 = 6928519) B6928519
theorem B6158683 : Blo 2161435 6158683 := bstep (se 1 (by rfl) ⟨4619012, by rfl⟩ : syracuseStep 6158683 = 9238025) B9238025
theorem B8211577 : Blo 2161435 8211577 := bstep (se 2 (by rfl) ⟨3079341, by rfl⟩ : syracuseStep 8211577 = 6158683) B6158683
theorem B10948769 : Blo 2161435 10948769 := bstep (se 2 (by rfl) ⟨4105788, by rfl⟩ : syracuseStep 10948769 = 8211577) B8211577
theorem B7299179 : Blo 2161435 7299179 := bstep (se 1 (by rfl) ⟨5474384, by rfl⟩ : syracuseStep 7299179 = 10948769) B10948769
theorem B4866119 : Blo 2161435 4866119 := bstep (se 1 (by rfl) ⟨3649589, by rfl⟩ : syracuseStep 4866119 = 7299179) B7299179
theorem B3244079 : Blo 2161435 3244079 := bstep (se 1 (by rfl) ⟨2433059, by rfl⟩ : syracuseStep 3244079 = 4866119) B4866119
theorem B2162719 : Blo 2161435 2162719 := bstep (se 1 (by rfl) ⟨1622039, by rfl⟩ : syracuseStep 2162719 = 3244079) B3244079
theorem B3244085 : Blo 2161435 3244085 := bbase (se 5 (by rfl) ⟨152066, by rfl⟩ : syracuseStep 3244085 = 304133) (by norm_num)
theorem B2162723 : Blo 2161435 2162723 := bstep (se 1 (by rfl) ⟨1622042, by rfl⟩ : syracuseStep 2162723 = 3244085) B3244085
theorem B5474405 : Blo 2161435 5474405 := bbase (se 4 (by rfl) ⟨513225, by rfl⟩ : syracuseStep 5474405 = 1026451) (by norm_num)
theorem B3649603 : Blo 2161435 3649603 := bstep (se 1 (by rfl) ⟨2737202, by rfl⟩ : syracuseStep 3649603 = 5474405) B5474405
theorem B4866137 : Blo 2161435 4866137 := bstep (se 2 (by rfl) ⟨1824801, by rfl⟩ : syracuseStep 4866137 = 3649603) B3649603
theorem B3244091 : Blo 2161435 3244091 := bstep (se 1 (by rfl) ⟨2433068, by rfl⟩ : syracuseStep 3244091 = 4866137) B4866137
theorem B2162727 : Blo 2161435 2162727 := bstep (se 1 (by rfl) ⟨1622045, by rfl⟩ : syracuseStep 2162727 = 3244091) B3244091
theorem B2433073 : Blo 2161435 2433073 := bbase (se 2 (by rfl) ⟨912402, by rfl⟩ : syracuseStep 2433073 = 1824805) (by norm_num)
theorem B3244097 : Blo 2161435 3244097 := bstep (se 2 (by rfl) ⟨1216536, by rfl⟩ : syracuseStep 3244097 = 2433073) B2433073
theorem B2162731 : Blo 2161435 2162731 := bstep (se 1 (by rfl) ⟨1622048, by rfl⟩ : syracuseStep 2162731 = 3244097) B3244097
theorem B8008789 : Blo 2161435 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B10678385 : Blo 2161435 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B7118923 : Blo 2161435 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B9491897 : Blo 2161435 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B6327931 : Blo 2161435 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B8437241 : Blo 2161435 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B22499309 : Blo 2161435 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B59998157 : Blo 2161435 59998157 := bstep (se 3 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 59998157 = 22499309) B22499309
theorem B39998771 : Blo 2161435 39998771 := bstep (se 1 (by rfl) ⟨29999078, by rfl⟩ : syracuseStep 39998771 = 59998157) B59998157
theorem B26665847 : Blo 2161435 26665847 := bstep (se 1 (by rfl) ⟨19999385, by rfl⟩ : syracuseStep 26665847 = 39998771) B39998771
theorem B17777231 : Blo 2161435 17777231 := bstep (se 1 (by rfl) ⟨13332923, by rfl⟩ : syracuseStep 17777231 = 26665847) B26665847
theorem B11851487 : Blo 2161435 11851487 := bstep (se 1 (by rfl) ⟨8888615, by rfl⟩ : syracuseStep 11851487 = 17777231) B17777231
theorem B7900991 : Blo 2161435 7900991 := bstep (se 1 (by rfl) ⟨5925743, by rfl⟩ : syracuseStep 7900991 = 11851487) B11851487
theorem B5267327 : Blo 2161435 5267327 := bstep (se 1 (by rfl) ⟨3950495, by rfl⟩ : syracuseStep 5267327 = 7900991) B7900991
theorem B14046205 : Blo 2161435 14046205 := bstep (se 3 (by rfl) ⟨2633663, by rfl⟩ : syracuseStep 14046205 = 5267327) B5267327
theorem B18728273 : Blo 2161435 18728273 := bstep (se 2 (by rfl) ⟨7023102, by rfl⟩ : syracuseStep 18728273 = 14046205) B14046205
theorem B12485515 : Blo 2161435 12485515 := bstep (se 1 (by rfl) ⟨9364136, by rfl⟩ : syracuseStep 12485515 = 18728273) B18728273
theorem B16647353 : Blo 2161435 16647353 := bstep (se 2 (by rfl) ⟨6242757, by rfl⟩ : syracuseStep 16647353 = 12485515) B12485515
theorem B11098235 : Blo 2161435 11098235 := bstep (se 1 (by rfl) ⟨8323676, by rfl⟩ : syracuseStep 11098235 = 16647353) B16647353
theorem B7398823 : Blo 2161435 7398823 := bstep (se 1 (by rfl) ⟨5549117, by rfl⟩ : syracuseStep 7398823 = 11098235) B11098235
theorem B9865097 : Blo 2161435 9865097 := bstep (se 2 (by rfl) ⟨3699411, by rfl⟩ : syracuseStep 9865097 = 7398823) B7398823
theorem B6576731 : Blo 2161435 6576731 := bstep (se 1 (by rfl) ⟨4932548, by rfl⟩ : syracuseStep 6576731 = 9865097) B9865097
theorem B4384487 : Blo 2161435 4384487 := bstep (se 1 (by rfl) ⟨3288365, by rfl⟩ : syracuseStep 4384487 = 6576731) B6576731
theorem B11691965 : Blo 2161435 11691965 := bstep (se 3 (by rfl) ⟨2192243, by rfl⟩ : syracuseStep 11691965 = 4384487) B4384487
theorem B7794643 : Blo 2161435 7794643 := bstep (se 1 (by rfl) ⟨5845982, by rfl⟩ : syracuseStep 7794643 = 11691965) B11691965
theorem B10392857 : Blo 2161435 10392857 := bstep (se 2 (by rfl) ⟨3897321, by rfl⟩ : syracuseStep 10392857 = 7794643) B7794643
theorem B6928571 : Blo 2161435 6928571 := bstep (se 1 (by rfl) ⟨5196428, by rfl⟩ : syracuseStep 6928571 = 10392857) B10392857
theorem B4619047 : Blo 2161435 4619047 := bstep (se 1 (by rfl) ⟨3464285, by rfl⟩ : syracuseStep 4619047 = 6928571) B6928571
theorem B6158729 : Blo 2161435 6158729 := bstep (se 2 (by rfl) ⟨2309523, by rfl⟩ : syracuseStep 6158729 = 4619047) B4619047
theorem B4105819 : Blo 2161435 4105819 := bstep (se 1 (by rfl) ⟨3079364, by rfl⟩ : syracuseStep 4105819 = 6158729) B6158729
theorem B5474425 : Blo 2161435 5474425 := bstep (se 2 (by rfl) ⟨2052909, by rfl⟩ : syracuseStep 5474425 = 4105819) B4105819
theorem B7299233 : Blo 2161435 7299233 := bstep (se 2 (by rfl) ⟨2737212, by rfl⟩ : syracuseStep 7299233 = 5474425) B5474425
theorem B4866155 : Blo 2161435 4866155 := bstep (se 1 (by rfl) ⟨3649616, by rfl⟩ : syracuseStep 4866155 = 7299233) B7299233
theorem B3244103 : Blo 2161435 3244103 := bstep (se 1 (by rfl) ⟨2433077, by rfl⟩ : syracuseStep 3244103 = 4866155) B4866155
theorem B2162735 : Blo 2161435 2162735 := bstep (se 1 (by rfl) ⟨1622051, by rfl⟩ : syracuseStep 2162735 = 3244103) B3244103
theorem B3244109 : Blo 2161435 3244109 := bbase (se 3 (by rfl) ⟨608270, by rfl⟩ : syracuseStep 3244109 = 1216541) (by norm_num)
theorem B2162739 : Blo 2161435 2162739 := bstep (se 1 (by rfl) ⟨1622054, by rfl⟩ : syracuseStep 2162739 = 3244109) B3244109
theorem B4866173 : Blo 2161435 4866173 := bbase (se 3 (by rfl) ⟨912407, by rfl⟩ : syracuseStep 4866173 = 1824815) (by norm_num)
theorem B3244115 : Blo 2161435 3244115 := bstep (se 1 (by rfl) ⟨2433086, by rfl⟩ : syracuseStep 3244115 = 4866173) B4866173
theorem B2162743 : Blo 2161435 2162743 := bstep (se 1 (by rfl) ⟨1622057, by rfl⟩ : syracuseStep 2162743 = 3244115) B3244115
theorem B3649637 : Blo 2161435 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B2433091 : Blo 2161435 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B3244121 : Blo 2161435 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B2162747 : Blo 2161435 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B2923013 : Blo 2161435 2923013 := bbase (se 4 (by rfl) ⟨274032, by rfl⟩ : syracuseStep 2923013 = 548065) (by norm_num)
theorem B7794701 : Blo 2161435 7794701 := bstep (se 3 (by rfl) ⟨1461506, by rfl⟩ : syracuseStep 7794701 = 2923013) B2923013
theorem B5196467 : Blo 2161435 5196467 := bstep (se 1 (by rfl) ⟨3897350, by rfl⟩ : syracuseStep 5196467 = 7794701) B7794701
theorem B3464311 : Blo 2161435 3464311 := bstep (se 1 (by rfl) ⟨2598233, by rfl⟩ : syracuseStep 3464311 = 5196467) B5196467
theorem B4619081 : Blo 2161435 4619081 := bstep (se 2 (by rfl) ⟨1732155, by rfl⟩ : syracuseStep 4619081 = 3464311) B3464311
theorem B3079387 : Blo 2161435 3079387 := bstep (se 1 (by rfl) ⟨2309540, by rfl⟩ : syracuseStep 3079387 = 4619081) B4619081
theorem B16423397 : Blo 2161435 16423397 := bstep (se 4 (by rfl) ⟨1539693, by rfl⟩ : syracuseStep 16423397 = 3079387) B3079387
theorem B10948931 : Blo 2161435 10948931 := bstep (se 1 (by rfl) ⟨8211698, by rfl⟩ : syracuseStep 10948931 = 16423397) B16423397
theorem B7299287 : Blo 2161435 7299287 := bstep (se 1 (by rfl) ⟨5474465, by rfl⟩ : syracuseStep 7299287 = 10948931) B10948931
theorem B4866191 : Blo 2161435 4866191 := bstep (se 1 (by rfl) ⟨3649643, by rfl⟩ : syracuseStep 4866191 = 7299287) B7299287
theorem B3244127 : Blo 2161435 3244127 := bstep (se 1 (by rfl) ⟨2433095, by rfl⟩ : syracuseStep 3244127 = 4866191) B4866191
theorem B2162751 : Blo 2161435 2162751 := bstep (se 1 (by rfl) ⟨1622063, by rfl⟩ : syracuseStep 2162751 = 3244127) B3244127
theorem B3244133 : Blo 2161435 3244133 := bbase (se 4 (by rfl) ⟨304137, by rfl⟩ : syracuseStep 3244133 = 608275) (by norm_num)
theorem B2162755 : Blo 2161435 2162755 := bstep (se 1 (by rfl) ⟨1622066, by rfl⟩ : syracuseStep 2162755 = 3244133) B3244133
theorem B6576805 : Blo 2161435 6576805 := bbase (se 4 (by rfl) ⟨616575, by rfl⟩ : syracuseStep 6576805 = 1233151) (by norm_num)
theorem B8769073 : Blo 2161435 8769073 := bstep (se 2 (by rfl) ⟨3288402, by rfl⟩ : syracuseStep 8769073 = 6576805) B6576805
theorem B11692097 : Blo 2161435 11692097 := bstep (se 2 (by rfl) ⟨4384536, by rfl⟩ : syracuseStep 11692097 = 8769073) B8769073
theorem B7794731 : Blo 2161435 7794731 := bstep (se 1 (by rfl) ⟨5846048, by rfl⟩ : syracuseStep 7794731 = 11692097) B11692097
theorem B5196487 : Blo 2161435 5196487 := bstep (se 1 (by rfl) ⟨3897365, by rfl⟩ : syracuseStep 5196487 = 7794731) B7794731
theorem B6928649 : Blo 2161435 6928649 := bstep (se 2 (by rfl) ⟨2598243, by rfl⟩ : syracuseStep 6928649 = 5196487) B5196487
theorem B4619099 : Blo 2161435 4619099 := bstep (se 1 (by rfl) ⟨3464324, by rfl⟩ : syracuseStep 4619099 = 6928649) B6928649
theorem B3079399 : Blo 2161435 3079399 := bstep (se 1 (by rfl) ⟨2309549, by rfl⟩ : syracuseStep 3079399 = 4619099) B4619099
theorem B4105865 : Blo 2161435 4105865 := bstep (se 2 (by rfl) ⟨1539699, by rfl⟩ : syracuseStep 4105865 = 3079399) B3079399
theorem B2737243 : Blo 2161435 2737243 := bstep (se 1 (by rfl) ⟨2052932, by rfl⟩ : syracuseStep 2737243 = 4105865) B4105865
theorem B3649657 : Blo 2161435 3649657 := bstep (se 2 (by rfl) ⟨1368621, by rfl⟩ : syracuseStep 3649657 = 2737243) B2737243
theorem B4866209 : Blo 2161435 4866209 := bstep (se 2 (by rfl) ⟨1824828, by rfl⟩ : syracuseStep 4866209 = 3649657) B3649657
theorem B3244139 : Blo 2161435 3244139 := bstep (se 1 (by rfl) ⟨2433104, by rfl⟩ : syracuseStep 3244139 = 4866209) B4866209
theorem B2162759 : Blo 2161435 2162759 := bstep (se 1 (by rfl) ⟨1622069, by rfl⟩ : syracuseStep 2162759 = 3244139) B3244139
theorem B2433109 : Blo 2161435 2433109 := bbase (se 8 (by rfl) ⟨14256, by rfl⟩ : syracuseStep 2433109 = 28513) (by norm_num)
theorem B3244145 : Blo 2161435 3244145 := bstep (se 2 (by rfl) ⟨1216554, by rfl⟩ : syracuseStep 3244145 = 2433109) B2433109
theorem B2162763 : Blo 2161435 2162763 := bstep (se 1 (by rfl) ⟨1622072, by rfl⟩ : syracuseStep 2162763 = 3244145) B3244145
theorem B2737253 : Blo 2161435 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B7299341 : Blo 2161435 7299341 := bstep (se 3 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 7299341 = 2737253) B2737253
theorem B4866227 : Blo 2161435 4866227 := bstep (se 1 (by rfl) ⟨3649670, by rfl⟩ : syracuseStep 4866227 = 7299341) B7299341
theorem B3244151 : Blo 2161435 3244151 := bstep (se 1 (by rfl) ⟨2433113, by rfl⟩ : syracuseStep 3244151 = 4866227) B4866227
theorem B2162767 : Blo 2161435 2162767 := bstep (se 1 (by rfl) ⟨1622075, by rfl⟩ : syracuseStep 2162767 = 3244151) B3244151
theorem B3244157 : Blo 2161435 3244157 := bbase (se 3 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 3244157 = 1216559) (by norm_num)
theorem B2162771 : Blo 2161435 2162771 := bstep (se 1 (by rfl) ⟨1622078, by rfl⟩ : syracuseStep 2162771 = 3244157) B3244157
theorem B4866245 : Blo 2161435 4866245 := bbase (se 4 (by rfl) ⟨456210, by rfl⟩ : syracuseStep 4866245 = 912421) (by norm_num)
theorem B3244163 : Blo 2161435 3244163 := bstep (se 1 (by rfl) ⟨2433122, by rfl⟩ : syracuseStep 3244163 = 4866245) B4866245
theorem B2162775 : Blo 2161435 2162775 := bstep (se 1 (by rfl) ⟨1622081, by rfl⟩ : syracuseStep 2162775 = 3244163) B3244163
theorem B2466325 : Blo 2161435 2466325 := bbase (se 6 (by rfl) ⟨57804, by rfl⟩ : syracuseStep 2466325 = 115609) (by norm_num)
theorem B3288433 : Blo 2161435 3288433 := bstep (se 2 (by rfl) ⟨1233162, by rfl⟩ : syracuseStep 3288433 = 2466325) B2466325
theorem B4384577 : Blo 2161435 4384577 := bstep (se 2 (by rfl) ⟨1644216, by rfl⟩ : syracuseStep 4384577 = 3288433) B3288433
theorem B2923051 : Blo 2161435 2923051 := bstep (se 1 (by rfl) ⟨2192288, by rfl⟩ : syracuseStep 2923051 = 4384577) B4384577
theorem B3897401 : Blo 2161435 3897401 := bstep (se 2 (by rfl) ⟨1461525, by rfl⟩ : syracuseStep 3897401 = 2923051) B2923051
theorem B10393069 : Blo 2161435 10393069 := bstep (se 3 (by rfl) ⟨1948700, by rfl⟩ : syracuseStep 10393069 = 3897401) B3897401
theorem B13857425 : Blo 2161435 13857425 := bstep (se 2 (by rfl) ⟨5196534, by rfl⟩ : syracuseStep 13857425 = 10393069) B10393069
theorem B9238283 : Blo 2161435 9238283 := bstep (se 1 (by rfl) ⟨6928712, by rfl⟩ : syracuseStep 9238283 = 13857425) B13857425
theorem B6158855 : Blo 2161435 6158855 := bstep (se 1 (by rfl) ⟨4619141, by rfl⟩ : syracuseStep 6158855 = 9238283) B9238283
theorem B4105903 : Blo 2161435 4105903 := bstep (se 1 (by rfl) ⟨3079427, by rfl⟩ : syracuseStep 4105903 = 6158855) B6158855
theorem B5474537 : Blo 2161435 5474537 := bstep (se 2 (by rfl) ⟨2052951, by rfl⟩ : syracuseStep 5474537 = 4105903) B4105903
theorem B3649691 : Blo 2161435 3649691 := bstep (se 1 (by rfl) ⟨2737268, by rfl⟩ : syracuseStep 3649691 = 5474537) B5474537
theorem B2433127 : Blo 2161435 2433127 := bstep (se 1 (by rfl) ⟨1824845, by rfl⟩ : syracuseStep 2433127 = 3649691) B3649691
theorem B3244169 : Blo 2161435 3244169 := bstep (se 2 (by rfl) ⟨1216563, by rfl⟩ : syracuseStep 3244169 = 2433127) B2433127
theorem B2162779 : Blo 2161435 2162779 := bstep (se 1 (by rfl) ⟨1622084, by rfl⟩ : syracuseStep 2162779 = 3244169) B3244169
theorem B10949093 : Blo 2161435 10949093 := bbase (se 4 (by rfl) ⟨1026477, by rfl⟩ : syracuseStep 10949093 = 2052955) (by norm_num)
theorem B7299395 : Blo 2161435 7299395 := bstep (se 1 (by rfl) ⟨5474546, by rfl⟩ : syracuseStep 7299395 = 10949093) B10949093
theorem B4866263 : Blo 2161435 4866263 := bstep (se 1 (by rfl) ⟨3649697, by rfl⟩ : syracuseStep 4866263 = 7299395) B7299395
theorem B3244175 : Blo 2161435 3244175 := bstep (se 1 (by rfl) ⟨2433131, by rfl⟩ : syracuseStep 3244175 = 4866263) B4866263
theorem B2162783 : Blo 2161435 2162783 := bstep (se 1 (by rfl) ⟨1622087, by rfl⟩ : syracuseStep 2162783 = 3244175) B3244175
theorem B3244181 : Blo 2161435 3244181 := bbase (se 6 (by rfl) ⟨76035, by rfl⟩ : syracuseStep 3244181 = 152071) (by norm_num)
theorem B2162787 : Blo 2161435 2162787 := bstep (se 1 (by rfl) ⟨1622090, by rfl⟩ : syracuseStep 2162787 = 3244181) B3244181
theorem B4932677 : Blo 2161435 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B3288451 : Blo 2161435 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B4384601 : Blo 2161435 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B2923067 : Blo 2161435 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B7794845 : Blo 2161435 7794845 := bstep (se 3 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 7794845 = 2923067) B2923067
theorem B5196563 : Blo 2161435 5196563 := bstep (se 1 (by rfl) ⟨3897422, by rfl⟩ : syracuseStep 5196563 = 7794845) B7794845
theorem B3464375 : Blo 2161435 3464375 := bstep (se 1 (by rfl) ⟨2598281, by rfl⟩ : syracuseStep 3464375 = 5196563) B5196563
theorem B9238333 : Blo 2161435 9238333 := bstep (se 3 (by rfl) ⟨1732187, by rfl⟩ : syracuseStep 9238333 = 3464375) B3464375
theorem B12317777 : Blo 2161435 12317777 := bstep (se 2 (by rfl) ⟨4619166, by rfl⟩ : syracuseStep 12317777 = 9238333) B9238333
theorem B8211851 : Blo 2161435 8211851 := bstep (se 1 (by rfl) ⟨6158888, by rfl⟩ : syracuseStep 8211851 = 12317777) B12317777
theorem B5474567 : Blo 2161435 5474567 := bstep (se 1 (by rfl) ⟨4105925, by rfl⟩ : syracuseStep 5474567 = 8211851) B8211851
theorem B3649711 : Blo 2161435 3649711 := bstep (se 1 (by rfl) ⟨2737283, by rfl⟩ : syracuseStep 3649711 = 5474567) B5474567
theorem B4866281 : Blo 2161435 4866281 := bstep (se 2 (by rfl) ⟨1824855, by rfl⟩ : syracuseStep 4866281 = 3649711) B3649711
theorem B3244187 : Blo 2161435 3244187 := bstep (se 1 (by rfl) ⟨2433140, by rfl⟩ : syracuseStep 3244187 = 4866281) B4866281
theorem B2162791 : Blo 2161435 2162791 := bstep (se 1 (by rfl) ⟨1622093, by rfl⟩ : syracuseStep 2162791 = 3244187) B3244187
theorem B2433145 : Blo 2161435 2433145 := bbase (se 2 (by rfl) ⟨912429, by rfl⟩ : syracuseStep 2433145 = 1824859) (by norm_num)
theorem B3244193 : Blo 2161435 3244193 := bstep (se 2 (by rfl) ⟨1216572, by rfl⟩ : syracuseStep 3244193 = 2433145) B2433145
theorem B2162795 : Blo 2161435 2162795 := bstep (se 1 (by rfl) ⟨1622096, by rfl⟩ : syracuseStep 2162795 = 3244193) B3244193
theorem B46769237 : Blo 2161435 46769237 := bbase (se 8 (by rfl) ⟨274038, by rfl⟩ : syracuseStep 46769237 = 548077) (by norm_num)
theorem B31179491 : Blo 2161435 31179491 := bstep (se 1 (by rfl) ⟨23384618, by rfl⟩ : syracuseStep 31179491 = 46769237) B46769237
theorem B20786327 : Blo 2161435 20786327 := bstep (se 1 (by rfl) ⟨15589745, by rfl⟩ : syracuseStep 20786327 = 31179491) B31179491
theorem B13857551 : Blo 2161435 13857551 := bstep (se 1 (by rfl) ⟨10393163, by rfl⟩ : syracuseStep 13857551 = 20786327) B20786327
theorem B9238367 : Blo 2161435 9238367 := bstep (se 1 (by rfl) ⟨6928775, by rfl⟩ : syracuseStep 9238367 = 13857551) B13857551
theorem B6158911 : Blo 2161435 6158911 := bstep (se 1 (by rfl) ⟨4619183, by rfl⟩ : syracuseStep 6158911 = 9238367) B9238367
theorem B8211881 : Blo 2161435 8211881 := bstep (se 2 (by rfl) ⟨3079455, by rfl⟩ : syracuseStep 8211881 = 6158911) B6158911
theorem B5474587 : Blo 2161435 5474587 := bstep (se 1 (by rfl) ⟨4105940, by rfl⟩ : syracuseStep 5474587 = 8211881) B8211881
theorem B7299449 : Blo 2161435 7299449 := bstep (se 2 (by rfl) ⟨2737293, by rfl⟩ : syracuseStep 7299449 = 5474587) B5474587
theorem B4866299 : Blo 2161435 4866299 := bstep (se 1 (by rfl) ⟨3649724, by rfl⟩ : syracuseStep 4866299 = 7299449) B7299449
theorem B3244199 : Blo 2161435 3244199 := bstep (se 1 (by rfl) ⟨2433149, by rfl⟩ : syracuseStep 3244199 = 4866299) B4866299
theorem B2162799 : Blo 2161435 2162799 := bstep (se 1 (by rfl) ⟨1622099, by rfl⟩ : syracuseStep 2162799 = 3244199) B3244199
theorem B3244205 : Blo 2161435 3244205 := bbase (se 3 (by rfl) ⟨608288, by rfl⟩ : syracuseStep 3244205 = 1216577) (by norm_num)
theorem B2162803 : Blo 2161435 2162803 := bstep (se 1 (by rfl) ⟨1622102, by rfl⟩ : syracuseStep 2162803 = 3244205) B3244205
theorem B4866317 : Blo 2161435 4866317 := bbase (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) (by norm_num)
theorem B3244211 : Blo 2161435 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B2162807 : Blo 2161435 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B2737309 : Blo 2161435 2737309 := bbase (se 3 (by rfl) ⟨513245, by rfl⟩ : syracuseStep 2737309 = 1026491) (by norm_num)
theorem B3649745 : Blo 2161435 3649745 := bstep (se 2 (by rfl) ⟨1368654, by rfl⟩ : syracuseStep 3649745 = 2737309) B2737309
theorem B2433163 : Blo 2161435 2433163 := bstep (se 1 (by rfl) ⟨1824872, by rfl⟩ : syracuseStep 2433163 = 3649745) B3649745
theorem B3244217 : Blo 2161435 3244217 := bstep (se 2 (by rfl) ⟨1216581, by rfl⟩ : syracuseStep 3244217 = 2433163) B2433163
theorem B2162811 : Blo 2161435 2162811 := bstep (se 1 (by rfl) ⟨1622108, by rfl⟩ : syracuseStep 2162811 = 3244217) B3244217
theorem B3464413 : Blo 2161435 3464413 := bbase (se 3 (by rfl) ⟨649577, by rfl⟩ : syracuseStep 3464413 = 1299155) (by norm_num)
theorem B18476869 : Blo 2161435 18476869 := bstep (se 4 (by rfl) ⟨1732206, by rfl⟩ : syracuseStep 18476869 = 3464413) B3464413
theorem B24635825 : Blo 2161435 24635825 := bstep (se 2 (by rfl) ⟨9238434, by rfl⟩ : syracuseStep 24635825 = 18476869) B18476869
theorem B16423883 : Blo 2161435 16423883 := bstep (se 1 (by rfl) ⟨12317912, by rfl⟩ : syracuseStep 16423883 = 24635825) B24635825
theorem B10949255 : Blo 2161435 10949255 := bstep (se 1 (by rfl) ⟨8211941, by rfl⟩ : syracuseStep 10949255 = 16423883) B16423883
theorem B7299503 : Blo 2161435 7299503 := bstep (se 1 (by rfl) ⟨5474627, by rfl⟩ : syracuseStep 7299503 = 10949255) B10949255
theorem B4866335 : Blo 2161435 4866335 := bstep (se 1 (by rfl) ⟨3649751, by rfl⟩ : syracuseStep 4866335 = 7299503) B7299503
theorem B3244223 : Blo 2161435 3244223 := bstep (se 1 (by rfl) ⟨2433167, by rfl⟩ : syracuseStep 3244223 = 4866335) B4866335
theorem B2162815 : Blo 2161435 2162815 := bstep (se 1 (by rfl) ⟨1622111, by rfl⟩ : syracuseStep 2162815 = 3244223) B3244223
theorem B3244229 : Blo 2161435 3244229 := bbase (se 4 (by rfl) ⟨304146, by rfl⟩ : syracuseStep 3244229 = 608293) (by norm_num)
theorem B2162819 : Blo 2161435 2162819 := bstep (se 1 (by rfl) ⟨1622114, by rfl⟩ : syracuseStep 2162819 = 3244229) B3244229
theorem B3649765 : Blo 2161435 3649765 := bbase (se 4 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 3649765 = 684331) (by norm_num)
theorem B4866353 : Blo 2161435 4866353 := bstep (se 2 (by rfl) ⟨1824882, by rfl⟩ : syracuseStep 4866353 = 3649765) B3649765
theorem B3244235 : Blo 2161435 3244235 := bstep (se 1 (by rfl) ⟨2433176, by rfl⟩ : syracuseStep 3244235 = 4866353) B4866353
theorem B2162823 : Blo 2161435 2162823 := bstep (se 1 (by rfl) ⟨1622117, by rfl⟩ : syracuseStep 2162823 = 3244235) B3244235
theorem B2433181 : Blo 2161435 2433181 := bbase (se 3 (by rfl) ⟨456221, by rfl⟩ : syracuseStep 2433181 = 912443) (by norm_num)
theorem B3244241 : Blo 2161435 3244241 := bstep (se 2 (by rfl) ⟨1216590, by rfl⟩ : syracuseStep 3244241 = 2433181) B2433181
theorem B2162827 : Blo 2161435 2162827 := bstep (se 1 (by rfl) ⟨1622120, by rfl⟩ : syracuseStep 2162827 = 3244241) B3244241
theorem B7299557 : Blo 2161435 7299557 := bbase (se 4 (by rfl) ⟨684333, by rfl⟩ : syracuseStep 7299557 = 1368667) (by norm_num)
theorem B4866371 : Blo 2161435 4866371 := bstep (se 1 (by rfl) ⟨3649778, by rfl⟩ : syracuseStep 4866371 = 7299557) B7299557
theorem B3244247 : Blo 2161435 3244247 := bstep (se 1 (by rfl) ⟨2433185, by rfl⟩ : syracuseStep 3244247 = 4866371) B4866371
theorem B2162831 : Blo 2161435 2162831 := bstep (se 1 (by rfl) ⟨1622123, by rfl⟩ : syracuseStep 2162831 = 3244247) B3244247
theorem B3244253 : Blo 2161435 3244253 := bbase (se 3 (by rfl) ⟨608297, by rfl⟩ : syracuseStep 3244253 = 1216595) (by norm_num)
theorem B2162835 : Blo 2161435 2162835 := bstep (se 1 (by rfl) ⟨1622126, by rfl⟩ : syracuseStep 2162835 = 3244253) B3244253
theorem B4866389 : Blo 2161435 4866389 := bbase (se 10 (by rfl) ⟨7128, by rfl⟩ : syracuseStep 4866389 = 14257) (by norm_num)
theorem B3244259 : Blo 2161435 3244259 := bstep (se 1 (by rfl) ⟨2433194, by rfl⟩ : syracuseStep 3244259 = 4866389) B4866389
theorem B2162839 : Blo 2161435 2162839 := bstep (se 1 (by rfl) ⟨1622129, by rfl⟩ : syracuseStep 2162839 = 3244259) B3244259
theorem B3897517 : Blo 2161435 3897517 := bbase (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) (by norm_num)
theorem B5196689 : Blo 2161435 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B3464459 : Blo 2161435 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B2309639 : Blo 2161435 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B6159037 : Blo 2161435 6159037 := bstep (se 3 (by rfl) ⟨1154819, by rfl⟩ : syracuseStep 6159037 = 2309639) B2309639
theorem B8212049 : Blo 2161435 8212049 := bstep (se 2 (by rfl) ⟨3079518, by rfl⟩ : syracuseStep 8212049 = 6159037) B6159037
theorem B5474699 : Blo 2161435 5474699 := bstep (se 1 (by rfl) ⟨4106024, by rfl⟩ : syracuseStep 5474699 = 8212049) B8212049
theorem B3649799 : Blo 2161435 3649799 := bstep (se 1 (by rfl) ⟨2737349, by rfl⟩ : syracuseStep 3649799 = 5474699) B5474699
theorem B2433199 : Blo 2161435 2433199 := bstep (se 1 (by rfl) ⟨1824899, by rfl⟩ : syracuseStep 2433199 = 3649799) B3649799
theorem B3244265 : Blo 2161435 3244265 := bstep (se 2 (by rfl) ⟨1216599, by rfl⟩ : syracuseStep 3244265 = 2433199) B2433199
theorem B2162843 : Blo 2161435 2162843 := bstep (se 1 (by rfl) ⟨1622132, by rfl⟩ : syracuseStep 2162843 = 3244265) B3244265
theorem B7795045 : Blo 2161435 7795045 := bbase (se 4 (by rfl) ⟨730785, by rfl⟩ : syracuseStep 7795045 = 1461571) (by norm_num)
theorem B41573573 : Blo 2161435 41573573 := bstep (se 4 (by rfl) ⟨3897522, by rfl⟩ : syracuseStep 41573573 = 7795045) B7795045
theorem B27715715 : Blo 2161435 27715715 := bstep (se 1 (by rfl) ⟨20786786, by rfl⟩ : syracuseStep 27715715 = 41573573) B41573573
theorem B18477143 : Blo 2161435 18477143 := bstep (se 1 (by rfl) ⟨13857857, by rfl⟩ : syracuseStep 18477143 = 27715715) B27715715
theorem B12318095 : Blo 2161435 12318095 := bstep (se 1 (by rfl) ⟨9238571, by rfl⟩ : syracuseStep 12318095 = 18477143) B18477143
theorem B8212063 : Blo 2161435 8212063 := bstep (se 1 (by rfl) ⟨6159047, by rfl⟩ : syracuseStep 8212063 = 12318095) B12318095
theorem B10949417 : Blo 2161435 10949417 := bstep (se 2 (by rfl) ⟨4106031, by rfl⟩ : syracuseStep 10949417 = 8212063) B8212063
theorem B7299611 : Blo 2161435 7299611 := bstep (se 1 (by rfl) ⟨5474708, by rfl⟩ : syracuseStep 7299611 = 10949417) B10949417
theorem B4866407 : Blo 2161435 4866407 := bstep (se 1 (by rfl) ⟨3649805, by rfl⟩ : syracuseStep 4866407 = 7299611) B7299611
theorem B3244271 : Blo 2161435 3244271 := bstep (se 1 (by rfl) ⟨2433203, by rfl⟩ : syracuseStep 3244271 = 4866407) B4866407
theorem B2162847 : Blo 2161435 2162847 := bstep (se 1 (by rfl) ⟨1622135, by rfl⟩ : syracuseStep 2162847 = 3244271) B3244271
theorem B3244277 : Blo 2161435 3244277 := bbase (se 5 (by rfl) ⟨152075, by rfl⟩ : syracuseStep 3244277 = 304151) (by norm_num)
theorem B2162851 : Blo 2161435 2162851 := bstep (se 1 (by rfl) ⟨1622138, by rfl⟩ : syracuseStep 2162851 = 3244277) B3244277
theorem B2192365 : Blo 2161435 2192365 := bbase (se 3 (by rfl) ⟨411068, by rfl⟩ : syracuseStep 2192365 = 822137) (by norm_num)
theorem B11692613 : Blo 2161435 11692613 := bstep (se 4 (by rfl) ⟨1096182, by rfl⟩ : syracuseStep 11692613 = 2192365) B2192365
theorem B31180301 : Blo 2161435 31180301 := bstep (se 3 (by rfl) ⟨5846306, by rfl⟩ : syracuseStep 31180301 = 11692613) B11692613
theorem B20786867 : Blo 2161435 20786867 := bstep (se 1 (by rfl) ⟨15590150, by rfl⟩ : syracuseStep 20786867 = 31180301) B31180301
theorem B13857911 : Blo 2161435 13857911 := bstep (se 1 (by rfl) ⟨10393433, by rfl⟩ : syracuseStep 13857911 = 20786867) B20786867
theorem B9238607 : Blo 2161435 9238607 := bstep (se 1 (by rfl) ⟨6928955, by rfl⟩ : syracuseStep 9238607 = 13857911) B13857911
theorem B6159071 : Blo 2161435 6159071 := bstep (se 1 (by rfl) ⟨4619303, by rfl⟩ : syracuseStep 6159071 = 9238607) B9238607
theorem B4106047 : Blo 2161435 4106047 := bstep (se 1 (by rfl) ⟨3079535, by rfl⟩ : syracuseStep 4106047 = 6159071) B6159071
theorem B5474729 : Blo 2161435 5474729 := bstep (se 2 (by rfl) ⟨2053023, by rfl⟩ : syracuseStep 5474729 = 4106047) B4106047
theorem B3649819 : Blo 2161435 3649819 := bstep (se 1 (by rfl) ⟨2737364, by rfl⟩ : syracuseStep 3649819 = 5474729) B5474729
theorem B4866425 : Blo 2161435 4866425 := bstep (se 2 (by rfl) ⟨1824909, by rfl⟩ : syracuseStep 4866425 = 3649819) B3649819
theorem B3244283 : Blo 2161435 3244283 := bstep (se 1 (by rfl) ⟨2433212, by rfl⟩ : syracuseStep 3244283 = 4866425) B4866425
theorem B2162855 : Blo 2161435 2162855 := bstep (se 1 (by rfl) ⟨1622141, by rfl⟩ : syracuseStep 2162855 = 3244283) B3244283
theorem B2433217 : Blo 2161435 2433217 := bbase (se 2 (by rfl) ⟨912456, by rfl⟩ : syracuseStep 2433217 = 1824913) (by norm_num)
theorem B3244289 : Blo 2161435 3244289 := bstep (se 2 (by rfl) ⟨1216608, by rfl⟩ : syracuseStep 3244289 = 2433217) B2433217
theorem B2162859 : Blo 2161435 2162859 := bstep (se 1 (by rfl) ⟨1622144, by rfl⟩ : syracuseStep 2162859 = 3244289) B3244289
theorem B5474749 : Blo 2161435 5474749 := bbase (se 3 (by rfl) ⟨1026515, by rfl⟩ : syracuseStep 5474749 = 2053031) (by norm_num)
theorem B7299665 : Blo 2161435 7299665 := bstep (se 2 (by rfl) ⟨2737374, by rfl⟩ : syracuseStep 7299665 = 5474749) B5474749
theorem B4866443 : Blo 2161435 4866443 := bstep (se 1 (by rfl) ⟨3649832, by rfl⟩ : syracuseStep 4866443 = 7299665) B7299665
theorem B3244295 : Blo 2161435 3244295 := bstep (se 1 (by rfl) ⟨2433221, by rfl⟩ : syracuseStep 3244295 = 4866443) B4866443
theorem B2162863 : Blo 2161435 2162863 := bstep (se 1 (by rfl) ⟨1622147, by rfl⟩ : syracuseStep 2162863 = 3244295) B3244295
theorem B3244301 : Blo 2161435 3244301 := bbase (se 3 (by rfl) ⟨608306, by rfl⟩ : syracuseStep 3244301 = 1216613) (by norm_num)
theorem B2162867 : Blo 2161435 2162867 := bstep (se 1 (by rfl) ⟨1622150, by rfl⟩ : syracuseStep 2162867 = 3244301) B3244301
theorem B4866461 : Blo 2161435 4866461 := bbase (se 3 (by rfl) ⟨912461, by rfl⟩ : syracuseStep 4866461 = 1824923) (by norm_num)
theorem B3244307 : Blo 2161435 3244307 := bstep (se 1 (by rfl) ⟨2433230, by rfl⟩ : syracuseStep 3244307 = 4866461) B4866461
theorem B2162871 : Blo 2161435 2162871 := bstep (se 1 (by rfl) ⟨1622153, by rfl⟩ : syracuseStep 2162871 = 3244307) B3244307
theorem B3649853 : Blo 2161435 3649853 := bbase (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) (by norm_num)
theorem B2433235 : Blo 2161435 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B3244313 : Blo 2161435 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B2162875 : Blo 2161435 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2309677 : Blo 2161435 2309677 := bbase (se 3 (by rfl) ⟨433064, by rfl⟩ : syracuseStep 2309677 = 866129) (by norm_num)
theorem B12318277 : Blo 2161435 12318277 := bstep (se 4 (by rfl) ⟨1154838, by rfl⟩ : syracuseStep 12318277 = 2309677) B2309677
theorem B16424369 : Blo 2161435 16424369 := bstep (se 2 (by rfl) ⟨6159138, by rfl⟩ : syracuseStep 16424369 = 12318277) B12318277
theorem B10949579 : Blo 2161435 10949579 := bstep (se 1 (by rfl) ⟨8212184, by rfl⟩ : syracuseStep 10949579 = 16424369) B16424369
theorem B7299719 : Blo 2161435 7299719 := bstep (se 1 (by rfl) ⟨5474789, by rfl⟩ : syracuseStep 7299719 = 10949579) B10949579
theorem B4866479 : Blo 2161435 4866479 := bstep (se 1 (by rfl) ⟨3649859, by rfl⟩ : syracuseStep 4866479 = 7299719) B7299719
theorem B3244319 : Blo 2161435 3244319 := bstep (se 1 (by rfl) ⟨2433239, by rfl⟩ : syracuseStep 3244319 = 4866479) B4866479
theorem B2162879 : Blo 2161435 2162879 := bstep (se 1 (by rfl) ⟨1622159, by rfl⟩ : syracuseStep 2162879 = 3244319) B3244319
theorem B3244325 : Blo 2161435 3244325 := bbase (se 4 (by rfl) ⟨304155, by rfl⟩ : syracuseStep 3244325 = 608311) (by norm_num)
theorem B2162883 : Blo 2161435 2162883 := bstep (se 1 (by rfl) ⟨1622162, by rfl⟩ : syracuseStep 2162883 = 3244325) B3244325
theorem B2737405 : Blo 2161435 2737405 := bbase (se 3 (by rfl) ⟨513263, by rfl⟩ : syracuseStep 2737405 = 1026527) (by norm_num)
theorem B3649873 : Blo 2161435 3649873 := bstep (se 2 (by rfl) ⟨1368702, by rfl⟩ : syracuseStep 3649873 = 2737405) B2737405
theorem B4866497 : Blo 2161435 4866497 := bstep (se 2 (by rfl) ⟨1824936, by rfl⟩ : syracuseStep 4866497 = 3649873) B3649873
theorem B3244331 : Blo 2161435 3244331 := bstep (se 1 (by rfl) ⟨2433248, by rfl⟩ : syracuseStep 3244331 = 4866497) B4866497
theorem B2162887 : Blo 2161435 2162887 := bstep (se 1 (by rfl) ⟨1622165, by rfl⟩ : syracuseStep 2162887 = 3244331) B3244331
theorem B2433253 : Blo 2161435 2433253 := bbase (se 4 (by rfl) ⟨228117, by rfl⟩ : syracuseStep 2433253 = 456235) (by norm_num)
theorem B3244337 : Blo 2161435 3244337 := bstep (se 2 (by rfl) ⟨1216626, by rfl⟩ : syracuseStep 3244337 = 2433253) B2433253
theorem B2162891 : Blo 2161435 2162891 := bstep (se 1 (by rfl) ⟨1622168, by rfl⟩ : syracuseStep 2162891 = 3244337) B3244337
theorem B4619389 : Blo 2161435 4619389 := bbase (se 3 (by rfl) ⟨866135, by rfl⟩ : syracuseStep 4619389 = 1732271) (by norm_num)
theorem B6159185 : Blo 2161435 6159185 := bstep (se 2 (by rfl) ⟨2309694, by rfl⟩ : syracuseStep 6159185 = 4619389) B4619389
theorem B4106123 : Blo 2161435 4106123 := bstep (se 1 (by rfl) ⟨3079592, by rfl⟩ : syracuseStep 4106123 = 6159185) B6159185
theorem B2737415 : Blo 2161435 2737415 := bstep (se 1 (by rfl) ⟨2053061, by rfl⟩ : syracuseStep 2737415 = 4106123) B4106123
theorem B7299773 : Blo 2161435 7299773 := bstep (se 3 (by rfl) ⟨1368707, by rfl⟩ : syracuseStep 7299773 = 2737415) B2737415
theorem B4866515 : Blo 2161435 4866515 := bstep (se 1 (by rfl) ⟨3649886, by rfl⟩ : syracuseStep 4866515 = 7299773) B7299773
theorem B3244343 : Blo 2161435 3244343 := bstep (se 1 (by rfl) ⟨2433257, by rfl⟩ : syracuseStep 3244343 = 4866515) B4866515
theorem B2162895 : Blo 2161435 2162895 := bstep (se 1 (by rfl) ⟨1622171, by rfl⟩ : syracuseStep 2162895 = 3244343) B3244343
theorem B3244349 : Blo 2161435 3244349 := bbase (se 3 (by rfl) ⟨608315, by rfl⟩ : syracuseStep 3244349 = 1216631) (by norm_num)
theorem B2162899 : Blo 2161435 2162899 := bstep (se 1 (by rfl) ⟨1622174, by rfl⟩ : syracuseStep 2162899 = 3244349) B3244349
theorem B4866533 : Blo 2161435 4866533 := bbase (se 4 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 4866533 = 912475) (by norm_num)
theorem B3244355 : Blo 2161435 3244355 := bstep (se 1 (by rfl) ⟨2433266, by rfl⟩ : syracuseStep 3244355 = 4866533) B4866533
theorem B2162903 : Blo 2161435 2162903 := bstep (se 1 (by rfl) ⟨1622177, by rfl⟩ : syracuseStep 2162903 = 3244355) B3244355
theorem B5474861 : Blo 2161435 5474861 := bbase (se 3 (by rfl) ⟨1026536, by rfl⟩ : syracuseStep 5474861 = 2053073) (by norm_num)
theorem B3649907 : Blo 2161435 3649907 := bstep (se 1 (by rfl) ⟨2737430, by rfl⟩ : syracuseStep 3649907 = 5474861) B5474861
theorem B2433271 : Blo 2161435 2433271 := bstep (se 1 (by rfl) ⟨1824953, by rfl⟩ : syracuseStep 2433271 = 3649907) B3649907
theorem B3244361 : Blo 2161435 3244361 := bstep (se 2 (by rfl) ⟨1216635, by rfl⟩ : syracuseStep 3244361 = 2433271) B2433271
theorem B2162907 : Blo 2161435 2162907 := bstep (se 1 (by rfl) ⟨1622180, by rfl⟩ : syracuseStep 2162907 = 3244361) B3244361
theorem B10535509 : Blo 2161435 10535509 := bbase (se 8 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 10535509 = 123463) (by norm_num)
theorem B14047345 : Blo 2161435 14047345 := bstep (se 2 (by rfl) ⟨5267754, by rfl⟩ : syracuseStep 14047345 = 10535509) B10535509
theorem B18729793 : Blo 2161435 18729793 := bstep (se 2 (by rfl) ⟨7023672, by rfl⟩ : syracuseStep 18729793 = 14047345) B14047345
theorem B24973057 : Blo 2161435 24973057 := bstep (se 2 (by rfl) ⟨9364896, by rfl⟩ : syracuseStep 24973057 = 18729793) B18729793
theorem B33297409 : Blo 2161435 33297409 := bstep (se 2 (by rfl) ⟨12486528, by rfl⟩ : syracuseStep 33297409 = 24973057) B24973057
theorem B44396545 : Blo 2161435 44396545 := bstep (se 2 (by rfl) ⟨16648704, by rfl⟩ : syracuseStep 44396545 = 33297409) B33297409
theorem B59195393 : Blo 2161435 59195393 := bstep (se 2 (by rfl) ⟨22198272, by rfl⟩ : syracuseStep 59195393 = 44396545) B44396545
theorem B39463595 : Blo 2161435 39463595 := bstep (se 1 (by rfl) ⟨29597696, by rfl⟩ : syracuseStep 39463595 = 59195393) B59195393
theorem B26309063 : Blo 2161435 26309063 := bstep (se 1 (by rfl) ⟨19731797, by rfl⟩ : syracuseStep 26309063 = 39463595) B39463595
theorem B17539375 : Blo 2161435 17539375 := bstep (se 1 (by rfl) ⟨13154531, by rfl⟩ : syracuseStep 17539375 = 26309063) B26309063
theorem B23385833 : Blo 2161435 23385833 := bstep (se 2 (by rfl) ⟨8769687, by rfl⟩ : syracuseStep 23385833 = 17539375) B17539375
theorem B15590555 : Blo 2161435 15590555 := bstep (se 1 (by rfl) ⟨11692916, by rfl⟩ : syracuseStep 15590555 = 23385833) B23385833
theorem B10393703 : Blo 2161435 10393703 := bstep (se 1 (by rfl) ⟨7795277, by rfl⟩ : syracuseStep 10393703 = 15590555) B15590555
theorem B6929135 : Blo 2161435 6929135 := bstep (se 1 (by rfl) ⟨5196851, by rfl⟩ : syracuseStep 6929135 = 10393703) B10393703
theorem B4619423 : Blo 2161435 4619423 := bstep (se 1 (by rfl) ⟨3464567, by rfl⟩ : syracuseStep 4619423 = 6929135) B6929135
theorem B3079615 : Blo 2161435 3079615 := bstep (se 1 (by rfl) ⟨2309711, by rfl⟩ : syracuseStep 3079615 = 4619423) B4619423
theorem B4106153 : Blo 2161435 4106153 := bstep (se 2 (by rfl) ⟨1539807, by rfl⟩ : syracuseStep 4106153 = 3079615) B3079615
theorem B10949741 : Blo 2161435 10949741 := bstep (se 3 (by rfl) ⟨2053076, by rfl⟩ : syracuseStep 10949741 = 4106153) B4106153
theorem B7299827 : Blo 2161435 7299827 := bstep (se 1 (by rfl) ⟨5474870, by rfl⟩ : syracuseStep 7299827 = 10949741) B10949741
theorem B4866551 : Blo 2161435 4866551 := bstep (se 1 (by rfl) ⟨3649913, by rfl⟩ : syracuseStep 4866551 = 7299827) B7299827
theorem B3244367 : Blo 2161435 3244367 := bstep (se 1 (by rfl) ⟨2433275, by rfl⟩ : syracuseStep 3244367 = 4866551) B4866551
theorem B2162911 : Blo 2161435 2162911 := bstep (se 1 (by rfl) ⟨1622183, by rfl⟩ : syracuseStep 2162911 = 3244367) B3244367
theorem B3244373 : Blo 2161435 3244373 := bbase (se 10 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 3244373 = 9505) (by norm_num)
theorem B2162915 : Blo 2161435 2162915 := bstep (se 1 (by rfl) ⟨1622186, by rfl⟩ : syracuseStep 2162915 = 3244373) B3244373
theorem B6159253 : Blo 2161435 6159253 := bbase (se 6 (by rfl) ⟨144357, by rfl⟩ : syracuseStep 6159253 = 288715) (by norm_num)
theorem B8212337 : Blo 2161435 8212337 := bstep (se 2 (by rfl) ⟨3079626, by rfl⟩ : syracuseStep 8212337 = 6159253) B6159253
theorem B5474891 : Blo 2161435 5474891 := bstep (se 1 (by rfl) ⟨4106168, by rfl⟩ : syracuseStep 5474891 = 8212337) B8212337
theorem B3649927 : Blo 2161435 3649927 := bstep (se 1 (by rfl) ⟨2737445, by rfl⟩ : syracuseStep 3649927 = 5474891) B5474891
theorem B4866569 : Blo 2161435 4866569 := bstep (se 2 (by rfl) ⟨1824963, by rfl⟩ : syracuseStep 4866569 = 3649927) B3649927
theorem B3244379 : Blo 2161435 3244379 := bstep (se 1 (by rfl) ⟨2433284, by rfl⟩ : syracuseStep 3244379 = 4866569) B4866569
theorem B2162919 : Blo 2161435 2162919 := bstep (se 1 (by rfl) ⟨1622189, by rfl⟩ : syracuseStep 2162919 = 3244379) B3244379
theorem B2433289 : Blo 2161435 2433289 := bbase (se 2 (by rfl) ⟨912483, by rfl⟩ : syracuseStep 2433289 = 1824967) (by norm_num)
theorem B3244385 : Blo 2161435 3244385 := bstep (se 2 (by rfl) ⟨1216644, by rfl⟩ : syracuseStep 3244385 = 2433289) B2433289
theorem B2162923 : Blo 2161435 2162923 := bstep (se 1 (by rfl) ⟨1622192, by rfl⟩ : syracuseStep 2162923 = 3244385) B3244385
theorem B5846501 : Blo 2161435 5846501 := bbase (se 4 (by rfl) ⟨548109, by rfl⟩ : syracuseStep 5846501 = 1096219) (by norm_num)
theorem B3897667 : Blo 2161435 3897667 := bstep (se 1 (by rfl) ⟨2923250, by rfl⟩ : syracuseStep 3897667 = 5846501) B5846501
theorem B5196889 : Blo 2161435 5196889 := bstep (se 2 (by rfl) ⟨1948833, by rfl⟩ : syracuseStep 5196889 = 3897667) B3897667
theorem B27716741 : Blo 2161435 27716741 := bstep (se 4 (by rfl) ⟨2598444, by rfl⟩ : syracuseStep 27716741 = 5196889) B5196889
theorem B18477827 : Blo 2161435 18477827 := bstep (se 1 (by rfl) ⟨13858370, by rfl⟩ : syracuseStep 18477827 = 27716741) B27716741
theorem B12318551 : Blo 2161435 12318551 := bstep (se 1 (by rfl) ⟨9238913, by rfl⟩ : syracuseStep 12318551 = 18477827) B18477827
theorem B8212367 : Blo 2161435 8212367 := bstep (se 1 (by rfl) ⟨6159275, by rfl⟩ : syracuseStep 8212367 = 12318551) B12318551
theorem B5474911 : Blo 2161435 5474911 := bstep (se 1 (by rfl) ⟨4106183, by rfl⟩ : syracuseStep 5474911 = 8212367) B8212367
theorem B7299881 : Blo 2161435 7299881 := bstep (se 2 (by rfl) ⟨2737455, by rfl⟩ : syracuseStep 7299881 = 5474911) B5474911
theorem B4866587 : Blo 2161435 4866587 := bstep (se 1 (by rfl) ⟨3649940, by rfl⟩ : syracuseStep 4866587 = 7299881) B7299881
theorem B3244391 : Blo 2161435 3244391 := bstep (se 1 (by rfl) ⟨2433293, by rfl⟩ : syracuseStep 3244391 = 4866587) B4866587
theorem B2162927 : Blo 2161435 2162927 := bstep (se 1 (by rfl) ⟨1622195, by rfl⟩ : syracuseStep 2162927 = 3244391) B3244391
theorem B3244397 : Blo 2161435 3244397 := bbase (se 3 (by rfl) ⟨608324, by rfl⟩ : syracuseStep 3244397 = 1216649) (by norm_num)
theorem B2162931 : Blo 2161435 2162931 := bstep (se 1 (by rfl) ⟨1622198, by rfl⟩ : syracuseStep 2162931 = 3244397) B3244397
theorem B4866605 : Blo 2161435 4866605 := bbase (se 3 (by rfl) ⟨912488, by rfl⟩ : syracuseStep 4866605 = 1824977) (by norm_num)
theorem B3244403 : Blo 2161435 3244403 := bstep (se 1 (by rfl) ⟨2433302, by rfl⟩ : syracuseStep 3244403 = 4866605) B4866605
theorem B2162935 : Blo 2161435 2162935 := bstep (se 1 (by rfl) ⟨1622201, by rfl⟩ : syracuseStep 2162935 = 3244403) B3244403
theorem B4384901 : Blo 2161435 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B11693069 : Blo 2161435 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B7795379 : Blo 2161435 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B20787677 : Blo 2161435 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B13858451 : Blo 2161435 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B9238967 : Blo 2161435 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B6159311 : Blo 2161435 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B4106207 : Blo 2161435 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B2737471 : Blo 2161435 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B3649961 : Blo 2161435 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B2433307 : Blo 2161435 2433307 := bstep (se 1 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 2433307 = 3649961) B3649961
theorem B3244409 : Blo 2161435 3244409 := bstep (se 2 (by rfl) ⟨1216653, by rfl⟩ : syracuseStep 3244409 = 2433307) B2433307
theorem B2162939 : Blo 2161435 2162939 := bstep (se 1 (by rfl) ⟨1622204, by rfl⟩ : syracuseStep 2162939 = 3244409) B3244409
theorem B36955925 : Blo 2161435 36955925 := bbase (se 6 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 36955925 = 1732309) (by norm_num)
theorem B24637283 : Blo 2161435 24637283 := bstep (se 1 (by rfl) ⟨18477962, by rfl⟩ : syracuseStep 24637283 = 36955925) B36955925
theorem B16424855 : Blo 2161435 16424855 := bstep (se 1 (by rfl) ⟨12318641, by rfl⟩ : syracuseStep 16424855 = 24637283) B24637283
theorem B10949903 : Blo 2161435 10949903 := bstep (se 1 (by rfl) ⟨8212427, by rfl⟩ : syracuseStep 10949903 = 16424855) B16424855
theorem B7299935 : Blo 2161435 7299935 := bstep (se 1 (by rfl) ⟨5474951, by rfl⟩ : syracuseStep 7299935 = 10949903) B10949903
theorem B4866623 : Blo 2161435 4866623 := bstep (se 1 (by rfl) ⟨3649967, by rfl⟩ : syracuseStep 4866623 = 7299935) B7299935
theorem B3244415 : Blo 2161435 3244415 := bstep (se 1 (by rfl) ⟨2433311, by rfl⟩ : syracuseStep 3244415 = 4866623) B4866623
theorem B2162943 : Blo 2161435 2162943 := bstep (se 1 (by rfl) ⟨1622207, by rfl⟩ : syracuseStep 2162943 = 3244415) B3244415
theorem B3244421 : Blo 2161435 3244421 := bbase (se 4 (by rfl) ⟨304164, by rfl⟩ : syracuseStep 3244421 = 608329) (by norm_num)
theorem B2162947 : Blo 2161435 2162947 := bstep (se 1 (by rfl) ⟨1622210, by rfl⟩ : syracuseStep 2162947 = 3244421) B3244421
theorem B3649981 : Blo 2161435 3649981 := bbase (se 3 (by rfl) ⟨684371, by rfl⟩ : syracuseStep 3649981 = 1368743) (by norm_num)
theorem B4866641 : Blo 2161435 4866641 := bstep (se 2 (by rfl) ⟨1824990, by rfl⟩ : syracuseStep 4866641 = 3649981) B3649981
theorem B3244427 : Blo 2161435 3244427 := bstep (se 1 (by rfl) ⟨2433320, by rfl⟩ : syracuseStep 3244427 = 4866641) B4866641
theorem B2162951 : Blo 2161435 2162951 := bstep (se 1 (by rfl) ⟨1622213, by rfl⟩ : syracuseStep 2162951 = 3244427) B3244427
theorem B2433325 : Blo 2161435 2433325 := bbase (se 3 (by rfl) ⟨456248, by rfl⟩ : syracuseStep 2433325 = 912497) (by norm_num)
theorem B3244433 : Blo 2161435 3244433 := bstep (se 2 (by rfl) ⟨1216662, by rfl⟩ : syracuseStep 3244433 = 2433325) B2433325
theorem B2162955 : Blo 2161435 2162955 := bstep (se 1 (by rfl) ⟨1622216, by rfl⟩ : syracuseStep 2162955 = 3244433) B3244433
theorem B7299989 : Blo 2161435 7299989 := bbase (se 6 (by rfl) ⟨171093, by rfl⟩ : syracuseStep 7299989 = 342187) (by norm_num)
theorem B4866659 : Blo 2161435 4866659 := bstep (se 1 (by rfl) ⟨3649994, by rfl⟩ : syracuseStep 4866659 = 7299989) B7299989
theorem B3244439 : Blo 2161435 3244439 := bstep (se 1 (by rfl) ⟨2433329, by rfl⟩ : syracuseStep 3244439 = 4866659) B4866659
theorem B2162959 : Blo 2161435 2162959 := bstep (se 1 (by rfl) ⟨1622219, by rfl⟩ : syracuseStep 2162959 = 3244439) B3244439
theorem B3244445 : Blo 2161435 3244445 := bbase (se 3 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 3244445 = 1216667) (by norm_num)
theorem B2162963 : Blo 2161435 2162963 := bstep (se 1 (by rfl) ⟨1622222, by rfl⟩ : syracuseStep 2162963 = 3244445) B3244445
theorem B4866677 : Blo 2161435 4866677 := bbase (se 5 (by rfl) ⟨228125, by rfl⟩ : syracuseStep 4866677 = 456251) (by norm_num)
theorem B3244451 : Blo 2161435 3244451 := bstep (se 1 (by rfl) ⟨2433338, by rfl⟩ : syracuseStep 3244451 = 4866677) B4866677
theorem B2162967 : Blo 2161435 2162967 := bstep (se 1 (by rfl) ⟨1622225, by rfl⟩ : syracuseStep 2162967 = 3244451) B3244451
theorem B17539861 : Blo 2161435 17539861 := bbase (se 6 (by rfl) ⟨411090, by rfl⟩ : syracuseStep 17539861 = 822181) (by norm_num)
theorem B23386481 : Blo 2161435 23386481 := bstep (se 2 (by rfl) ⟨8769930, by rfl⟩ : syracuseStep 23386481 = 17539861) B17539861
theorem B15590987 : Blo 2161435 15590987 := bstep (se 1 (by rfl) ⟨11693240, by rfl⟩ : syracuseStep 15590987 = 23386481) B23386481
theorem B10393991 : Blo 2161435 10393991 := bstep (se 1 (by rfl) ⟨7795493, by rfl⟩ : syracuseStep 10393991 = 15590987) B15590987
theorem B6929327 : Blo 2161435 6929327 := bstep (se 1 (by rfl) ⟨5196995, by rfl⟩ : syracuseStep 6929327 = 10393991) B10393991
theorem B18478205 : Blo 2161435 18478205 := bstep (se 3 (by rfl) ⟨3464663, by rfl⟩ : syracuseStep 18478205 = 6929327) B6929327
theorem B12318803 : Blo 2161435 12318803 := bstep (se 1 (by rfl) ⟨9239102, by rfl⟩ : syracuseStep 12318803 = 18478205) B18478205
theorem B8212535 : Blo 2161435 8212535 := bstep (se 1 (by rfl) ⟨6159401, by rfl⟩ : syracuseStep 8212535 = 12318803) B12318803
theorem B5475023 : Blo 2161435 5475023 := bstep (se 1 (by rfl) ⟨4106267, by rfl⟩ : syracuseStep 5475023 = 8212535) B8212535
theorem B3650015 : Blo 2161435 3650015 := bstep (se 1 (by rfl) ⟨2737511, by rfl⟩ : syracuseStep 3650015 = 5475023) B5475023
theorem B2433343 : Blo 2161435 2433343 := bstep (se 1 (by rfl) ⟨1825007, by rfl⟩ : syracuseStep 2433343 = 3650015) B3650015
theorem B3244457 : Blo 2161435 3244457 := bstep (se 2 (by rfl) ⟨1216671, by rfl⟩ : syracuseStep 3244457 = 2433343) B2433343
theorem B2162971 : Blo 2161435 2162971 := bstep (se 1 (by rfl) ⟨1622228, by rfl⟩ : syracuseStep 2162971 = 3244457) B3244457
theorem B8212549 : Blo 2161435 8212549 := bbase (se 4 (by rfl) ⟨769926, by rfl⟩ : syracuseStep 8212549 = 1539853) (by norm_num)
theorem B10950065 : Blo 2161435 10950065 := bstep (se 2 (by rfl) ⟨4106274, by rfl⟩ : syracuseStep 10950065 = 8212549) B8212549
theorem B7300043 : Blo 2161435 7300043 := bstep (se 1 (by rfl) ⟨5475032, by rfl⟩ : syracuseStep 7300043 = 10950065) B10950065
theorem B4866695 : Blo 2161435 4866695 := bstep (se 1 (by rfl) ⟨3650021, by rfl⟩ : syracuseStep 4866695 = 7300043) B7300043
theorem B3244463 : Blo 2161435 3244463 := bstep (se 1 (by rfl) ⟨2433347, by rfl⟩ : syracuseStep 3244463 = 4866695) B4866695
theorem B2162975 : Blo 2161435 2162975 := bstep (se 1 (by rfl) ⟨1622231, by rfl⟩ : syracuseStep 2162975 = 3244463) B3244463
theorem B3244469 : Blo 2161435 3244469 := bbase (se 5 (by rfl) ⟨152084, by rfl⟩ : syracuseStep 3244469 = 304169) (by norm_num)
theorem B2162979 : Blo 2161435 2162979 := bstep (se 1 (by rfl) ⟨1622234, by rfl⟩ : syracuseStep 2162979 = 3244469) B3244469
theorem B5475053 : Blo 2161435 5475053 := bbase (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) (by norm_num)
theorem B3650035 : Blo 2161435 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B4866713 : Blo 2161435 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B3244475 : Blo 2161435 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B2162983 : Blo 2161435 2162983 := bstep (se 1 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 2162983 = 3244475) B3244475
theorem B2433361 : Blo 2161435 2433361 := bbase (se 2 (by rfl) ⟨912510, by rfl⟩ : syracuseStep 2433361 = 1825021) (by norm_num)
theorem B3244481 : Blo 2161435 3244481 := bstep (se 2 (by rfl) ⟨1216680, by rfl⟩ : syracuseStep 3244481 = 2433361) B2433361
theorem B2162987 : Blo 2161435 2162987 := bstep (se 1 (by rfl) ⟨1622240, by rfl⟩ : syracuseStep 2162987 = 3244481) B3244481
theorem B2309797 : Blo 2161435 2309797 := bbase (se 4 (by rfl) ⟨216543, by rfl⟩ : syracuseStep 2309797 = 433087) (by norm_num)
theorem B3079729 : Blo 2161435 3079729 := bstep (se 2 (by rfl) ⟨1154898, by rfl⟩ : syracuseStep 3079729 = 2309797) B2309797
theorem B4106305 : Blo 2161435 4106305 := bstep (se 2 (by rfl) ⟨1539864, by rfl⟩ : syracuseStep 4106305 = 3079729) B3079729
theorem B5475073 : Blo 2161435 5475073 := bstep (se 2 (by rfl) ⟨2053152, by rfl⟩ : syracuseStep 5475073 = 4106305) B4106305
theorem B7300097 : Blo 2161435 7300097 := bstep (se 2 (by rfl) ⟨2737536, by rfl⟩ : syracuseStep 7300097 = 5475073) B5475073
theorem B4866731 : Blo 2161435 4866731 := bstep (se 1 (by rfl) ⟨3650048, by rfl⟩ : syracuseStep 4866731 = 7300097) B7300097
theorem B3244487 : Blo 2161435 3244487 := bstep (se 1 (by rfl) ⟨2433365, by rfl⟩ : syracuseStep 3244487 = 4866731) B4866731
theorem B2162991 : Blo 2161435 2162991 := bstep (se 1 (by rfl) ⟨1622243, by rfl⟩ : syracuseStep 2162991 = 3244487) B3244487
theorem B3244493 : Blo 2161435 3244493 := bbase (se 3 (by rfl) ⟨608342, by rfl⟩ : syracuseStep 3244493 = 1216685) (by norm_num)
theorem B2162995 : Blo 2161435 2162995 := bstep (se 1 (by rfl) ⟨1622246, by rfl⟩ : syracuseStep 2162995 = 3244493) B3244493
theorem B4866749 : Blo 2161435 4866749 := bbase (se 3 (by rfl) ⟨912515, by rfl⟩ : syracuseStep 4866749 = 1825031) (by norm_num)
theorem B3244499 : Blo 2161435 3244499 := bstep (se 1 (by rfl) ⟨2433374, by rfl⟩ : syracuseStep 3244499 = 4866749) B4866749
theorem B2162999 : Blo 2161435 2162999 := bstep (se 1 (by rfl) ⟨1622249, by rfl⟩ : syracuseStep 2162999 = 3244499) B3244499
theorem B3650069 : Blo 2161435 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B2433379 : Blo 2161435 2433379 := bstep (se 1 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 2433379 = 3650069) B3650069
theorem B3244505 : Blo 2161435 3244505 := bstep (se 2 (by rfl) ⟨1216689, by rfl⟩ : syracuseStep 3244505 = 2433379) B2433379
theorem B2163003 : Blo 2161435 2163003 := bstep (se 1 (by rfl) ⟨1622252, by rfl⟩ : syracuseStep 2163003 = 3244505) B3244505
theorem B3699877 : Blo 2161435 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B4933169 : Blo 2161435 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B3288779 : Blo 2161435 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B2192519 : Blo 2161435 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B5846717 : Blo 2161435 5846717 := bstep (se 3 (by rfl) ⟨1096259, by rfl⟩ : syracuseStep 5846717 = 2192519) B2192519
theorem B3897811 : Blo 2161435 3897811 := bstep (se 1 (by rfl) ⟨2923358, by rfl⟩ : syracuseStep 3897811 = 5846717) B5846717
theorem B20788325 : Blo 2161435 20788325 := bstep (se 4 (by rfl) ⟨1948905, by rfl⟩ : syracuseStep 20788325 = 3897811) B3897811
theorem B13858883 : Blo 2161435 13858883 := bstep (se 1 (by rfl) ⟨10394162, by rfl⟩ : syracuseStep 13858883 = 20788325) B20788325
theorem B9239255 : Blo 2161435 9239255 := bstep (se 1 (by rfl) ⟨6929441, by rfl⟩ : syracuseStep 9239255 = 13858883) B13858883
theorem B6159503 : Blo 2161435 6159503 := bstep (se 1 (by rfl) ⟨4619627, by rfl⟩ : syracuseStep 6159503 = 9239255) B9239255
theorem B16425341 : Blo 2161435 16425341 := bstep (se 3 (by rfl) ⟨3079751, by rfl⟩ : syracuseStep 16425341 = 6159503) B6159503
theorem B10950227 : Blo 2161435 10950227 := bstep (se 1 (by rfl) ⟨8212670, by rfl⟩ : syracuseStep 10950227 = 16425341) B16425341
theorem B7300151 : Blo 2161435 7300151 := bstep (se 1 (by rfl) ⟨5475113, by rfl⟩ : syracuseStep 7300151 = 10950227) B10950227
theorem B4866767 : Blo 2161435 4866767 := bstep (se 1 (by rfl) ⟨3650075, by rfl⟩ : syracuseStep 4866767 = 7300151) B7300151
theorem B3244511 : Blo 2161435 3244511 := bstep (se 1 (by rfl) ⟨2433383, by rfl⟩ : syracuseStep 3244511 = 4866767) B4866767
theorem B2163007 : Blo 2161435 2163007 := bstep (se 1 (by rfl) ⟨1622255, by rfl⟩ : syracuseStep 2163007 = 3244511) B3244511
theorem B3244517 : Blo 2161435 3244517 := bbase (se 4 (by rfl) ⟨304173, by rfl⟩ : syracuseStep 3244517 = 608347) (by norm_num)
theorem B2163011 : Blo 2161435 2163011 := bstep (se 1 (by rfl) ⟨1622258, by rfl⟩ : syracuseStep 2163011 = 3244517) B3244517
theorem B2341337 : Blo 2161435 2341337 := bbase (se 2 (by rfl) ⟨878001, by rfl⟩ : syracuseStep 2341337 = 1756003) (by norm_num)
theorem B6243565 : Blo 2161435 6243565 := bstep (se 3 (by rfl) ⟨1170668, by rfl⟩ : syracuseStep 6243565 = 2341337) B2341337
theorem B8324753 : Blo 2161435 8324753 := bstep (se 2 (by rfl) ⟨3121782, by rfl⟩ : syracuseStep 8324753 = 6243565) B6243565
theorem B22199341 : Blo 2161435 22199341 := bstep (se 3 (by rfl) ⟨4162376, by rfl⟩ : syracuseStep 22199341 = 8324753) B8324753
theorem B29599121 : Blo 2161435 29599121 := bstep (se 2 (by rfl) ⟨11099670, by rfl⟩ : syracuseStep 29599121 = 22199341) B22199341
theorem B19732747 : Blo 2161435 19732747 := bstep (se 1 (by rfl) ⟨14799560, by rfl⟩ : syracuseStep 19732747 = 29599121) B29599121
theorem B26310329 : Blo 2161435 26310329 := bstep (se 2 (by rfl) ⟨9866373, by rfl⟩ : syracuseStep 26310329 = 19732747) B19732747
theorem B17540219 : Blo 2161435 17540219 := bstep (se 1 (by rfl) ⟨13155164, by rfl⟩ : syracuseStep 17540219 = 26310329) B26310329
theorem B11693479 : Blo 2161435 11693479 := bstep (se 1 (by rfl) ⟨8770109, by rfl⟩ : syracuseStep 11693479 = 17540219) B17540219
theorem B15591305 : Blo 2161435 15591305 := bstep (se 2 (by rfl) ⟨5846739, by rfl⟩ : syracuseStep 15591305 = 11693479) B11693479
theorem B10394203 : Blo 2161435 10394203 := bstep (se 1 (by rfl) ⟨7795652, by rfl⟩ : syracuseStep 10394203 = 15591305) B15591305
theorem B13858937 : Blo 2161435 13858937 := bstep (se 2 (by rfl) ⟨5197101, by rfl⟩ : syracuseStep 13858937 = 10394203) B10394203
theorem B9239291 : Blo 2161435 9239291 := bstep (se 1 (by rfl) ⟨6929468, by rfl⟩ : syracuseStep 9239291 = 13858937) B13858937
theorem B6159527 : Blo 2161435 6159527 := bstep (se 1 (by rfl) ⟨4619645, by rfl⟩ : syracuseStep 6159527 = 9239291) B9239291
theorem B4106351 : Blo 2161435 4106351 := bstep (se 1 (by rfl) ⟨3079763, by rfl⟩ : syracuseStep 4106351 = 6159527) B6159527
theorem B2737567 : Blo 2161435 2737567 := bstep (se 1 (by rfl) ⟨2053175, by rfl⟩ : syracuseStep 2737567 = 4106351) B4106351
theorem B3650089 : Blo 2161435 3650089 := bstep (se 2 (by rfl) ⟨1368783, by rfl⟩ : syracuseStep 3650089 = 2737567) B2737567
theorem B4866785 : Blo 2161435 4866785 := bstep (se 2 (by rfl) ⟨1825044, by rfl⟩ : syracuseStep 4866785 = 3650089) B3650089
theorem B3244523 : Blo 2161435 3244523 := bstep (se 1 (by rfl) ⟨2433392, by rfl⟩ : syracuseStep 3244523 = 4866785) B4866785
theorem B2163015 : Blo 2161435 2163015 := bstep (se 1 (by rfl) ⟨1622261, by rfl⟩ : syracuseStep 2163015 = 3244523) B3244523
theorem B2433397 : Blo 2161435 2433397 := bbase (se 5 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 2433397 = 228131) (by norm_num)
theorem B3244529 : Blo 2161435 3244529 := bstep (se 2 (by rfl) ⟨1216698, by rfl⟩ : syracuseStep 3244529 = 2433397) B2433397
theorem B2163019 : Blo 2161435 2163019 := bstep (se 1 (by rfl) ⟨1622264, by rfl⟩ : syracuseStep 2163019 = 3244529) B3244529
theorem B2737577 : Blo 2161435 2737577 := bbase (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) (by norm_num)
theorem B7300205 : Blo 2161435 7300205 := bstep (se 3 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 7300205 = 2737577) B2737577
theorem B4866803 : Blo 2161435 4866803 := bstep (se 1 (by rfl) ⟨3650102, by rfl⟩ : syracuseStep 4866803 = 7300205) B7300205
theorem B3244535 : Blo 2161435 3244535 := bstep (se 1 (by rfl) ⟨2433401, by rfl⟩ : syracuseStep 3244535 = 4866803) B4866803
theorem B2163023 : Blo 2161435 2163023 := bstep (se 1 (by rfl) ⟨1622267, by rfl⟩ : syracuseStep 2163023 = 3244535) B3244535
theorem B3244541 : Blo 2161435 3244541 := bbase (se 3 (by rfl) ⟨608351, by rfl⟩ : syracuseStep 3244541 = 1216703) (by norm_num)
theorem B2163027 : Blo 2161435 2163027 := bstep (se 1 (by rfl) ⟨1622270, by rfl⟩ : syracuseStep 2163027 = 3244541) B3244541
theorem B4866821 : Blo 2161435 4866821 := bbase (se 4 (by rfl) ⟨456264, by rfl⟩ : syracuseStep 4866821 = 912529) (by norm_num)
theorem B3244547 : Blo 2161435 3244547 := bstep (se 1 (by rfl) ⟨2433410, by rfl⟩ : syracuseStep 3244547 = 4866821) B4866821
theorem B2163031 : Blo 2161435 2163031 := bstep (se 1 (by rfl) ⟨1622273, by rfl⟩ : syracuseStep 2163031 = 3244547) B3244547
theorem B4106389 : Blo 2161435 4106389 := bbase (se 6 (by rfl) ⟨96243, by rfl⟩ : syracuseStep 4106389 = 192487) (by norm_num)
theorem B5475185 : Blo 2161435 5475185 := bstep (se 2 (by rfl) ⟨2053194, by rfl⟩ : syracuseStep 5475185 = 4106389) B4106389
theorem B3650123 : Blo 2161435 3650123 := bstep (se 1 (by rfl) ⟨2737592, by rfl⟩ : syracuseStep 3650123 = 5475185) B5475185
theorem B2433415 : Blo 2161435 2433415 := bstep (se 1 (by rfl) ⟨1825061, by rfl⟩ : syracuseStep 2433415 = 3650123) B3650123
theorem B3244553 : Blo 2161435 3244553 := bstep (se 2 (by rfl) ⟨1216707, by rfl⟩ : syracuseStep 3244553 = 2433415) B2433415
theorem B2163035 : Blo 2161435 2163035 := bstep (se 1 (by rfl) ⟨1622276, by rfl⟩ : syracuseStep 2163035 = 3244553) B3244553
theorem B10950389 : Blo 2161435 10950389 := bbase (se 5 (by rfl) ⟨513299, by rfl⟩ : syracuseStep 10950389 = 1026599) (by norm_num)
theorem B7300259 : Blo 2161435 7300259 := bstep (se 1 (by rfl) ⟨5475194, by rfl⟩ : syracuseStep 7300259 = 10950389) B10950389
theorem B4866839 : Blo 2161435 4866839 := bstep (se 1 (by rfl) ⟨3650129, by rfl⟩ : syracuseStep 4866839 = 7300259) B7300259
theorem B3244559 : Blo 2161435 3244559 := bstep (se 1 (by rfl) ⟨2433419, by rfl⟩ : syracuseStep 3244559 = 4866839) B4866839
theorem B2163039 : Blo 2161435 2163039 := bstep (se 1 (by rfl) ⟨1622279, by rfl⟩ : syracuseStep 2163039 = 3244559) B3244559
theorem B3244565 : Blo 2161435 3244565 := bbase (se 6 (by rfl) ⟨76044, by rfl⟩ : syracuseStep 3244565 = 152089) (by norm_num)
theorem B2163043 : Blo 2161435 2163043 := bstep (se 1 (by rfl) ⟨1622282, by rfl⟩ : syracuseStep 2163043 = 3244565) B3244565
theorem B2598589 : Blo 2161435 2598589 := bbase (se 3 (by rfl) ⟨487235, by rfl⟩ : syracuseStep 2598589 = 974471) (by norm_num)
theorem B3464785 : Blo 2161435 3464785 := bstep (se 2 (by rfl) ⟨1299294, by rfl⟩ : syracuseStep 3464785 = 2598589) B2598589
theorem B18478853 : Blo 2161435 18478853 := bstep (se 4 (by rfl) ⟨1732392, by rfl⟩ : syracuseStep 18478853 = 3464785) B3464785
theorem B12319235 : Blo 2161435 12319235 := bstep (se 1 (by rfl) ⟨9239426, by rfl⟩ : syracuseStep 12319235 = 18478853) B18478853
theorem B8212823 : Blo 2161435 8212823 := bstep (se 1 (by rfl) ⟨6159617, by rfl⟩ : syracuseStep 8212823 = 12319235) B12319235
theorem B5475215 : Blo 2161435 5475215 := bstep (se 1 (by rfl) ⟨4106411, by rfl⟩ : syracuseStep 5475215 = 8212823) B8212823
theorem B3650143 : Blo 2161435 3650143 := bstep (se 1 (by rfl) ⟨2737607, by rfl⟩ : syracuseStep 3650143 = 5475215) B5475215
theorem B4866857 : Blo 2161435 4866857 := bstep (se 2 (by rfl) ⟨1825071, by rfl⟩ : syracuseStep 4866857 = 3650143) B3650143
theorem B3244571 : Blo 2161435 3244571 := bstep (se 1 (by rfl) ⟨2433428, by rfl⟩ : syracuseStep 3244571 = 4866857) B4866857
theorem B2163047 : Blo 2161435 2163047 := bstep (se 1 (by rfl) ⟨1622285, by rfl⟩ : syracuseStep 2163047 = 3244571) B3244571
theorem B2433433 : Blo 2161435 2433433 := bbase (se 2 (by rfl) ⟨912537, by rfl⟩ : syracuseStep 2433433 = 1825075) (by norm_num)
theorem B3244577 : Blo 2161435 3244577 := bstep (se 2 (by rfl) ⟨1216716, by rfl⟩ : syracuseStep 3244577 = 2433433) B2433433
theorem B2163051 : Blo 2161435 2163051 := bstep (se 1 (by rfl) ⟨1622288, by rfl⟩ : syracuseStep 2163051 = 3244577) B3244577
theorem B8212853 : Blo 2161435 8212853 := bbase (se 5 (by rfl) ⟨384977, by rfl⟩ : syracuseStep 8212853 = 769955) (by norm_num)
theorem B5475235 : Blo 2161435 5475235 := bstep (se 1 (by rfl) ⟨4106426, by rfl⟩ : syracuseStep 5475235 = 8212853) B8212853
theorem B7300313 : Blo 2161435 7300313 := bstep (se 2 (by rfl) ⟨2737617, by rfl⟩ : syracuseStep 7300313 = 5475235) B5475235
theorem B4866875 : Blo 2161435 4866875 := bstep (se 1 (by rfl) ⟨3650156, by rfl⟩ : syracuseStep 4866875 = 7300313) B7300313
theorem B3244583 : Blo 2161435 3244583 := bstep (se 1 (by rfl) ⟨2433437, by rfl⟩ : syracuseStep 3244583 = 4866875) B4866875
theorem B2163055 : Blo 2161435 2163055 := bstep (se 1 (by rfl) ⟨1622291, by rfl⟩ : syracuseStep 2163055 = 3244583) B3244583
theorem B3244589 : Blo 2161435 3244589 := bbase (se 3 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 3244589 = 1216721) (by norm_num)
theorem B2163059 : Blo 2161435 2163059 := bstep (se 1 (by rfl) ⟨1622294, by rfl⟩ : syracuseStep 2163059 = 3244589) B3244589
theorem B4866893 : Blo 2161435 4866893 := bbase (se 3 (by rfl) ⟨912542, by rfl⟩ : syracuseStep 4866893 = 1825085) (by norm_num)
theorem B3244595 : Blo 2161435 3244595 := bstep (se 1 (by rfl) ⟨2433446, by rfl⟩ : syracuseStep 3244595 = 4866893) B4866893
theorem B2163063 : Blo 2161435 2163063 := bstep (se 1 (by rfl) ⟨1622297, by rfl⟩ : syracuseStep 2163063 = 3244595) B3244595
theorem B2737633 : Blo 2161435 2737633 := bbase (se 2 (by rfl) ⟨1026612, by rfl⟩ : syracuseStep 2737633 = 2053225) (by norm_num)
theorem B3650177 : Blo 2161435 3650177 := bstep (se 2 (by rfl) ⟨1368816, by rfl⟩ : syracuseStep 3650177 = 2737633) B2737633
theorem B2433451 : Blo 2161435 2433451 := bstep (se 1 (by rfl) ⟨1825088, by rfl⟩ : syracuseStep 2433451 = 3650177) B3650177
theorem B3244601 : Blo 2161435 3244601 := bstep (se 2 (by rfl) ⟨1216725, by rfl⟩ : syracuseStep 3244601 = 2433451) B2433451
theorem B2163067 : Blo 2161435 2163067 := bstep (se 1 (by rfl) ⟨1622300, by rfl⟩ : syracuseStep 2163067 = 3244601) B3244601
theorem B24638741 : Blo 2161435 24638741 := bbase (se 6 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 24638741 = 1154941) (by norm_num)
theorem B16425827 : Blo 2161435 16425827 := bstep (se 1 (by rfl) ⟨12319370, by rfl⟩ : syracuseStep 16425827 = 24638741) B24638741
theorem B10950551 : Blo 2161435 10950551 := bstep (se 1 (by rfl) ⟨8212913, by rfl⟩ : syracuseStep 10950551 = 16425827) B16425827
theorem B7300367 : Blo 2161435 7300367 := bstep (se 1 (by rfl) ⟨5475275, by rfl⟩ : syracuseStep 7300367 = 10950551) B10950551
theorem B4866911 : Blo 2161435 4866911 := bstep (se 1 (by rfl) ⟨3650183, by rfl⟩ : syracuseStep 4866911 = 7300367) B7300367
theorem B3244607 : Blo 2161435 3244607 := bstep (se 1 (by rfl) ⟨2433455, by rfl⟩ : syracuseStep 3244607 = 4866911) B4866911
theorem B2163071 : Blo 2161435 2163071 := bstep (se 1 (by rfl) ⟨1622303, by rfl⟩ : syracuseStep 2163071 = 3244607) B3244607
theorem B3244613 : Blo 2161435 3244613 := bbase (se 4 (by rfl) ⟨304182, by rfl⟩ : syracuseStep 3244613 = 608365) (by norm_num)
theorem B2163075 : Blo 2161435 2163075 := bstep (se 1 (by rfl) ⟨1622306, by rfl⟩ : syracuseStep 2163075 = 3244613) B3244613
theorem B3650197 : Blo 2161435 3650197 := bbase (se 6 (by rfl) ⟨85551, by rfl⟩ : syracuseStep 3650197 = 171103) (by norm_num)
theorem B4866929 : Blo 2161435 4866929 := bstep (se 2 (by rfl) ⟨1825098, by rfl⟩ : syracuseStep 4866929 = 3650197) B3650197
theorem B3244619 : Blo 2161435 3244619 := bstep (se 1 (by rfl) ⟨2433464, by rfl⟩ : syracuseStep 3244619 = 4866929) B4866929
theorem B2163079 : Blo 2161435 2163079 := bstep (se 1 (by rfl) ⟨1622309, by rfl⟩ : syracuseStep 2163079 = 3244619) B3244619
theorem B2433469 : Blo 2161435 2433469 := bbase (se 3 (by rfl) ⟨456275, by rfl⟩ : syracuseStep 2433469 = 912551) (by norm_num)
theorem B3244625 : Blo 2161435 3244625 := bstep (se 2 (by rfl) ⟨1216734, by rfl⟩ : syracuseStep 3244625 = 2433469) B2433469
theorem B2163083 : Blo 2161435 2163083 := bstep (se 1 (by rfl) ⟨1622312, by rfl⟩ : syracuseStep 2163083 = 3244625) B3244625
theorem B7300421 : Blo 2161435 7300421 := bbase (se 4 (by rfl) ⟨684414, by rfl⟩ : syracuseStep 7300421 = 1368829) (by norm_num)
theorem B4866947 : Blo 2161435 4866947 := bstep (se 1 (by rfl) ⟨3650210, by rfl⟩ : syracuseStep 4866947 = 7300421) B7300421
theorem B3244631 : Blo 2161435 3244631 := bstep (se 1 (by rfl) ⟨2433473, by rfl⟩ : syracuseStep 3244631 = 4866947) B4866947
theorem B2163087 : Blo 2161435 2163087 := bstep (se 1 (by rfl) ⟨1622315, by rfl⟩ : syracuseStep 2163087 = 3244631) B3244631
theorem B3244637 : Blo 2161435 3244637 := bbase (se 3 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 3244637 = 1216739) (by norm_num)
theorem B2163091 : Blo 2161435 2163091 := bstep (se 1 (by rfl) ⟨1622318, by rfl⟩ : syracuseStep 2163091 = 3244637) B3244637
theorem B4866965 : Blo 2161435 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B3244643 : Blo 2161435 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B2163095 : Blo 2161435 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B3464869 : Blo 2161435 3464869 := bbase (se 4 (by rfl) ⟨324831, by rfl⟩ : syracuseStep 3464869 = 649663) (by norm_num)
theorem B4619825 : Blo 2161435 4619825 := bstep (se 2 (by rfl) ⟨1732434, by rfl⟩ : syracuseStep 4619825 = 3464869) B3464869
theorem B3079883 : Blo 2161435 3079883 := bstep (se 1 (by rfl) ⟨2309912, by rfl⟩ : syracuseStep 3079883 = 4619825) B4619825
theorem B8213021 : Blo 2161435 8213021 := bstep (se 3 (by rfl) ⟨1539941, by rfl⟩ : syracuseStep 8213021 = 3079883) B3079883
theorem B5475347 : Blo 2161435 5475347 := bstep (se 1 (by rfl) ⟨4106510, by rfl⟩ : syracuseStep 5475347 = 8213021) B8213021
theorem B3650231 : Blo 2161435 3650231 := bstep (se 1 (by rfl) ⟨2737673, by rfl⟩ : syracuseStep 3650231 = 5475347) B5475347
theorem B2433487 : Blo 2161435 2433487 := bstep (se 1 (by rfl) ⟨1825115, by rfl⟩ : syracuseStep 2433487 = 3650231) B3650231
theorem B3244649 : Blo 2161435 3244649 := bstep (se 2 (by rfl) ⟨1216743, by rfl⟩ : syracuseStep 3244649 = 2433487) B2433487
theorem B2163099 : Blo 2161435 2163099 := bstep (se 1 (by rfl) ⟨1622324, by rfl⟩ : syracuseStep 2163099 = 3244649) B3244649
theorem B6929749 : Blo 2161435 6929749 := bbase (se 11 (by rfl) ⟨5075, by rfl⟩ : syracuseStep 6929749 = 10151) (by norm_num)
theorem B9239665 : Blo 2161435 9239665 := bstep (se 2 (by rfl) ⟨3464874, by rfl⟩ : syracuseStep 9239665 = 6929749) B6929749
theorem B12319553 : Blo 2161435 12319553 := bstep (se 2 (by rfl) ⟨4619832, by rfl⟩ : syracuseStep 12319553 = 9239665) B9239665
theorem B8213035 : Blo 2161435 8213035 := bstep (se 1 (by rfl) ⟨6159776, by rfl⟩ : syracuseStep 8213035 = 12319553) B12319553
theorem B10950713 : Blo 2161435 10950713 := bstep (se 2 (by rfl) ⟨4106517, by rfl⟩ : syracuseStep 10950713 = 8213035) B8213035
theorem B7300475 : Blo 2161435 7300475 := bstep (se 1 (by rfl) ⟨5475356, by rfl⟩ : syracuseStep 7300475 = 10950713) B10950713
theorem B4866983 : Blo 2161435 4866983 := bstep (se 1 (by rfl) ⟨3650237, by rfl⟩ : syracuseStep 4866983 = 7300475) B7300475
theorem B3244655 : Blo 2161435 3244655 := bstep (se 1 (by rfl) ⟨2433491, by rfl⟩ : syracuseStep 3244655 = 4866983) B4866983
theorem B2163103 : Blo 2161435 2163103 := bstep (se 1 (by rfl) ⟨1622327, by rfl⟩ : syracuseStep 2163103 = 3244655) B3244655
theorem B3244661 : Blo 2161435 3244661 := bbase (se 5 (by rfl) ⟨152093, by rfl⟩ : syracuseStep 3244661 = 304187) (by norm_num)
theorem B2163107 : Blo 2161435 2163107 := bstep (se 1 (by rfl) ⟨1622330, by rfl⟩ : syracuseStep 2163107 = 3244661) B3244661
theorem B4106533 : Blo 2161435 4106533 := bbase (se 4 (by rfl) ⟨384987, by rfl⟩ : syracuseStep 4106533 = 769975) (by norm_num)
theorem B5475377 : Blo 2161435 5475377 := bstep (se 2 (by rfl) ⟨2053266, by rfl⟩ : syracuseStep 5475377 = 4106533) B4106533
theorem B3650251 : Blo 2161435 3650251 := bstep (se 1 (by rfl) ⟨2737688, by rfl⟩ : syracuseStep 3650251 = 5475377) B5475377
theorem B4867001 : Blo 2161435 4867001 := bstep (se 2 (by rfl) ⟨1825125, by rfl⟩ : syracuseStep 4867001 = 3650251) B3650251
theorem B3244667 : Blo 2161435 3244667 := bstep (se 1 (by rfl) ⟨2433500, by rfl⟩ : syracuseStep 3244667 = 4867001) B4867001
theorem B2163111 : Blo 2161435 2163111 := bstep (se 1 (by rfl) ⟨1622333, by rfl⟩ : syracuseStep 2163111 = 3244667) B3244667
theorem B2433505 : Blo 2161435 2433505 := bbase (se 2 (by rfl) ⟨912564, by rfl⟩ : syracuseStep 2433505 = 1825129) (by norm_num)
theorem B3244673 : Blo 2161435 3244673 := bstep (se 2 (by rfl) ⟨1216752, by rfl⟩ : syracuseStep 3244673 = 2433505) B2433505
theorem B2163115 : Blo 2161435 2163115 := bstep (se 1 (by rfl) ⟨1622336, by rfl⟩ : syracuseStep 2163115 = 3244673) B3244673
theorem B5475397 : Blo 2161435 5475397 := bbase (se 4 (by rfl) ⟨513318, by rfl⟩ : syracuseStep 5475397 = 1026637) (by norm_num)
theorem B7300529 : Blo 2161435 7300529 := bstep (se 2 (by rfl) ⟨2737698, by rfl⟩ : syracuseStep 7300529 = 5475397) B5475397
theorem B4867019 : Blo 2161435 4867019 := bstep (se 1 (by rfl) ⟨3650264, by rfl⟩ : syracuseStep 4867019 = 7300529) B7300529
theorem B3244679 : Blo 2161435 3244679 := bstep (se 1 (by rfl) ⟨2433509, by rfl⟩ : syracuseStep 3244679 = 4867019) B4867019
theorem B2163119 : Blo 2161435 2163119 := bstep (se 1 (by rfl) ⟨1622339, by rfl⟩ : syracuseStep 2163119 = 3244679) B3244679
theorem B3244685 : Blo 2161435 3244685 := bbase (se 3 (by rfl) ⟨608378, by rfl⟩ : syracuseStep 3244685 = 1216757) (by norm_num)
theorem B2163123 : Blo 2161435 2163123 := bstep (se 1 (by rfl) ⟨1622342, by rfl⟩ : syracuseStep 2163123 = 3244685) B3244685
theorem B4867037 : Blo 2161435 4867037 := bbase (se 3 (by rfl) ⟨912569, by rfl⟩ : syracuseStep 4867037 = 1825139) (by norm_num)
theorem B3244691 : Blo 2161435 3244691 := bstep (se 1 (by rfl) ⟨2433518, by rfl⟩ : syracuseStep 3244691 = 4867037) B4867037
theorem B2163127 : Blo 2161435 2163127 := bstep (se 1 (by rfl) ⟨1622345, by rfl⟩ : syracuseStep 2163127 = 3244691) B3244691
theorem B3650285 : Blo 2161435 3650285 := bbase (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) (by norm_num)
theorem B2433523 : Blo 2161435 2433523 := bstep (se 1 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 2433523 = 3650285) B3650285
theorem B3244697 : Blo 2161435 3244697 := bstep (se 2 (by rfl) ⟨1216761, by rfl⟩ : syracuseStep 3244697 = 2433523) B2433523
theorem B2163131 : Blo 2161435 2163131 := bstep (se 1 (by rfl) ⟨1622348, by rfl⟩ : syracuseStep 2163131 = 3244697) B3244697
theorem B3288973 : Blo 2161435 3288973 := bbase (se 3 (by rfl) ⟨616682, by rfl⟩ : syracuseStep 3288973 = 1233365) (by norm_num)
theorem B4385297 : Blo 2161435 4385297 := bstep (se 2 (by rfl) ⟨1644486, by rfl⟩ : syracuseStep 4385297 = 3288973) B3288973
theorem B11694125 : Blo 2161435 11694125 := bstep (se 3 (by rfl) ⟨2192648, by rfl⟩ : syracuseStep 11694125 = 4385297) B4385297
theorem B7796083 : Blo 2161435 7796083 := bstep (se 1 (by rfl) ⟨5847062, by rfl⟩ : syracuseStep 7796083 = 11694125) B11694125
theorem B10394777 : Blo 2161435 10394777 := bstep (se 2 (by rfl) ⟨3898041, by rfl⟩ : syracuseStep 10394777 = 7796083) B7796083
theorem B27719405 : Blo 2161435 27719405 := bstep (se 3 (by rfl) ⟨5197388, by rfl⟩ : syracuseStep 27719405 = 10394777) B10394777
theorem B18479603 : Blo 2161435 18479603 := bstep (se 1 (by rfl) ⟨13859702, by rfl⟩ : syracuseStep 18479603 = 27719405) B27719405
theorem B12319735 : Blo 2161435 12319735 := bstep (se 1 (by rfl) ⟨9239801, by rfl⟩ : syracuseStep 12319735 = 18479603) B18479603
theorem B16426313 : Blo 2161435 16426313 := bstep (se 2 (by rfl) ⟨6159867, by rfl⟩ : syracuseStep 16426313 = 12319735) B12319735
theorem B10950875 : Blo 2161435 10950875 := bstep (se 1 (by rfl) ⟨8213156, by rfl⟩ : syracuseStep 10950875 = 16426313) B16426313
theorem B7300583 : Blo 2161435 7300583 := bstep (se 1 (by rfl) ⟨5475437, by rfl⟩ : syracuseStep 7300583 = 10950875) B10950875
theorem B4867055 : Blo 2161435 4867055 := bstep (se 1 (by rfl) ⟨3650291, by rfl⟩ : syracuseStep 4867055 = 7300583) B7300583
theorem B3244703 : Blo 2161435 3244703 := bstep (se 1 (by rfl) ⟨2433527, by rfl⟩ : syracuseStep 3244703 = 4867055) B4867055
theorem B2163135 : Blo 2161435 2163135 := bstep (se 1 (by rfl) ⟨1622351, by rfl⟩ : syracuseStep 2163135 = 3244703) B3244703
theorem B3244709 : Blo 2161435 3244709 := bbase (se 4 (by rfl) ⟨304191, by rfl⟩ : syracuseStep 3244709 = 608383) (by norm_num)
theorem B2163139 : Blo 2161435 2163139 := bstep (se 1 (by rfl) ⟨1622354, by rfl⟩ : syracuseStep 2163139 = 3244709) B3244709
theorem B2737729 : Blo 2161435 2737729 := bbase (se 2 (by rfl) ⟨1026648, by rfl⟩ : syracuseStep 2737729 = 2053297) (by norm_num)
theorem B3650305 : Blo 2161435 3650305 := bstep (se 2 (by rfl) ⟨1368864, by rfl⟩ : syracuseStep 3650305 = 2737729) B2737729
theorem B4867073 : Blo 2161435 4867073 := bstep (se 2 (by rfl) ⟨1825152, by rfl⟩ : syracuseStep 4867073 = 3650305) B3650305
theorem B3244715 : Blo 2161435 3244715 := bstep (se 1 (by rfl) ⟨2433536, by rfl⟩ : syracuseStep 3244715 = 4867073) B4867073
theorem B2163143 : Blo 2161435 2163143 := bstep (se 1 (by rfl) ⟨1622357, by rfl⟩ : syracuseStep 2163143 = 3244715) B3244715
theorem B2433541 : Blo 2161435 2433541 := bbase (se 4 (by rfl) ⟨228144, by rfl⟩ : syracuseStep 2433541 = 456289) (by norm_num)
theorem B3244721 : Blo 2161435 3244721 := bstep (se 2 (by rfl) ⟨1216770, by rfl⟩ : syracuseStep 3244721 = 2433541) B2433541
theorem B2163147 : Blo 2161435 2163147 := bstep (se 1 (by rfl) ⟨1622360, by rfl⟩ : syracuseStep 2163147 = 3244721) B3244721
theorem B3079957 : Blo 2161435 3079957 := bbase (se 6 (by rfl) ⟨72186, by rfl⟩ : syracuseStep 3079957 = 144373) (by norm_num)
theorem B4106609 : Blo 2161435 4106609 := bstep (se 2 (by rfl) ⟨1539978, by rfl⟩ : syracuseStep 4106609 = 3079957) B3079957
theorem B2737739 : Blo 2161435 2737739 := bstep (se 1 (by rfl) ⟨2053304, by rfl⟩ : syracuseStep 2737739 = 4106609) B4106609
theorem B7300637 : Blo 2161435 7300637 := bstep (se 3 (by rfl) ⟨1368869, by rfl⟩ : syracuseStep 7300637 = 2737739) B2737739
theorem B4867091 : Blo 2161435 4867091 := bstep (se 1 (by rfl) ⟨3650318, by rfl⟩ : syracuseStep 4867091 = 7300637) B7300637
theorem B3244727 : Blo 2161435 3244727 := bstep (se 1 (by rfl) ⟨2433545, by rfl⟩ : syracuseStep 3244727 = 4867091) B4867091
theorem B2163151 : Blo 2161435 2163151 := bstep (se 1 (by rfl) ⟨1622363, by rfl⟩ : syracuseStep 2163151 = 3244727) B3244727
theorem B3244733 : Blo 2161435 3244733 := bbase (se 3 (by rfl) ⟨608387, by rfl⟩ : syracuseStep 3244733 = 1216775) (by norm_num)
theorem B2163155 : Blo 2161435 2163155 := bstep (se 1 (by rfl) ⟨1622366, by rfl⟩ : syracuseStep 2163155 = 3244733) B3244733
theorem B4867109 : Blo 2161435 4867109 := bbase (se 4 (by rfl) ⟨456291, by rfl⟩ : syracuseStep 4867109 = 912583) (by norm_num)
theorem B3244739 : Blo 2161435 3244739 := bstep (se 1 (by rfl) ⟨2433554, by rfl⟩ : syracuseStep 3244739 = 4867109) B4867109
theorem B2163159 : Blo 2161435 2163159 := bstep (se 1 (by rfl) ⟨1622369, by rfl⟩ : syracuseStep 2163159 = 3244739) B3244739
theorem B5475509 : Blo 2161435 5475509 := bbase (se 5 (by rfl) ⟨256664, by rfl⟩ : syracuseStep 5475509 = 513329) (by norm_num)
theorem B3650339 : Blo 2161435 3650339 := bstep (se 1 (by rfl) ⟨2737754, by rfl⟩ : syracuseStep 3650339 = 5475509) B5475509
theorem B2433559 : Blo 2161435 2433559 := bstep (se 1 (by rfl) ⟨1825169, by rfl⟩ : syracuseStep 2433559 = 3650339) B3650339
theorem B3244745 : Blo 2161435 3244745 := bstep (se 2 (by rfl) ⟨1216779, by rfl⟩ : syracuseStep 3244745 = 2433559) B2433559
theorem B2163163 : Blo 2161435 2163163 := bstep (se 1 (by rfl) ⟨1622372, by rfl⟩ : syracuseStep 2163163 = 3244745) B3244745
theorem B2598733 : Blo 2161435 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B13859909 : Blo 2161435 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B9239939 : Blo 2161435 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B6159959 : Blo 2161435 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B4106639 : Blo 2161435 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B10951037 : Blo 2161435 10951037 := bstep (se 3 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 10951037 = 4106639) B4106639
theorem B7300691 : Blo 2161435 7300691 := bstep (se 1 (by rfl) ⟨5475518, by rfl⟩ : syracuseStep 7300691 = 10951037) B10951037
theorem B4867127 : Blo 2161435 4867127 := bstep (se 1 (by rfl) ⟨3650345, by rfl⟩ : syracuseStep 4867127 = 7300691) B7300691
theorem B3244751 : Blo 2161435 3244751 := bstep (se 1 (by rfl) ⟨2433563, by rfl⟩ : syracuseStep 3244751 = 4867127) B4867127
theorem B2163167 : Blo 2161435 2163167 := bstep (se 1 (by rfl) ⟨1622375, by rfl⟩ : syracuseStep 2163167 = 3244751) B3244751
theorem B3244757 : Blo 2161435 3244757 := bbase (se 7 (by rfl) ⟨38024, by rfl⟩ : syracuseStep 3244757 = 76049) (by norm_num)
theorem B2163171 : Blo 2161435 2163171 := bstep (se 1 (by rfl) ⟨1622378, by rfl⟩ : syracuseStep 2163171 = 3244757) B3244757
theorem B5847173 : Blo 2161435 5847173 := bbase (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) (by norm_num)
theorem B3898115 : Blo 2161435 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B2598743 : Blo 2161435 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B6929981 : Blo 2161435 6929981 := bstep (se 3 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 6929981 = 2598743) B2598743
theorem B4619987 : Blo 2161435 4619987 := bstep (se 1 (by rfl) ⟨3464990, by rfl⟩ : syracuseStep 4619987 = 6929981) B6929981
theorem B3079991 : Blo 2161435 3079991 := bstep (se 1 (by rfl) ⟨2309993, by rfl⟩ : syracuseStep 3079991 = 4619987) B4619987
theorem B8213309 : Blo 2161435 8213309 := bstep (se 3 (by rfl) ⟨1539995, by rfl⟩ : syracuseStep 8213309 = 3079991) B3079991
theorem B5475539 : Blo 2161435 5475539 := bstep (se 1 (by rfl) ⟨4106654, by rfl⟩ : syracuseStep 5475539 = 8213309) B8213309
theorem B3650359 : Blo 2161435 3650359 := bstep (se 1 (by rfl) ⟨2737769, by rfl⟩ : syracuseStep 3650359 = 5475539) B5475539
theorem B4867145 : Blo 2161435 4867145 := bstep (se 2 (by rfl) ⟨1825179, by rfl⟩ : syracuseStep 4867145 = 3650359) B3650359
theorem B3244763 : Blo 2161435 3244763 := bstep (se 1 (by rfl) ⟨2433572, by rfl⟩ : syracuseStep 3244763 = 4867145) B4867145
theorem B2163175 : Blo 2161435 2163175 := bstep (se 1 (by rfl) ⟨1622381, by rfl⟩ : syracuseStep 2163175 = 3244763) B3244763
theorem B2433577 : Blo 2161435 2433577 := bbase (se 2 (by rfl) ⟨912591, by rfl⟩ : syracuseStep 2433577 = 1825183) (by norm_num)
theorem B3244769 : Blo 2161435 3244769 := bstep (se 2 (by rfl) ⟨1216788, by rfl⟩ : syracuseStep 3244769 = 2433577) B2433577
theorem B2163179 : Blo 2161435 2163179 := bstep (se 1 (by rfl) ⟨1622384, by rfl⟩ : syracuseStep 2163179 = 3244769) B3244769
theorem B8770789 : Blo 2161435 8770789 := bbase (se 4 (by rfl) ⟨822261, by rfl⟩ : syracuseStep 8770789 = 1644523) (by norm_num)
theorem B11694385 : Blo 2161435 11694385 := bstep (se 2 (by rfl) ⟨4385394, by rfl⟩ : syracuseStep 11694385 = 8770789) B8770789
theorem B15592513 : Blo 2161435 15592513 := bstep (se 2 (by rfl) ⟨5847192, by rfl⟩ : syracuseStep 15592513 = 11694385) B11694385
theorem B20790017 : Blo 2161435 20790017 := bstep (se 2 (by rfl) ⟨7796256, by rfl⟩ : syracuseStep 20790017 = 15592513) B15592513
theorem B13860011 : Blo 2161435 13860011 := bstep (se 1 (by rfl) ⟨10395008, by rfl⟩ : syracuseStep 13860011 = 20790017) B20790017
theorem B9240007 : Blo 2161435 9240007 := bstep (se 1 (by rfl) ⟨6930005, by rfl⟩ : syracuseStep 9240007 = 13860011) B13860011
theorem B12320009 : Blo 2161435 12320009 := bstep (se 2 (by rfl) ⟨4620003, by rfl⟩ : syracuseStep 12320009 = 9240007) B9240007
theorem B8213339 : Blo 2161435 8213339 := bstep (se 1 (by rfl) ⟨6160004, by rfl⟩ : syracuseStep 8213339 = 12320009) B12320009
theorem B5475559 : Blo 2161435 5475559 := bstep (se 1 (by rfl) ⟨4106669, by rfl⟩ : syracuseStep 5475559 = 8213339) B8213339
theorem B7300745 : Blo 2161435 7300745 := bstep (se 2 (by rfl) ⟨2737779, by rfl⟩ : syracuseStep 7300745 = 5475559) B5475559
theorem B4867163 : Blo 2161435 4867163 := bstep (se 1 (by rfl) ⟨3650372, by rfl⟩ : syracuseStep 4867163 = 7300745) B7300745
theorem B3244775 : Blo 2161435 3244775 := bstep (se 1 (by rfl) ⟨2433581, by rfl⟩ : syracuseStep 3244775 = 4867163) B4867163
theorem B2163183 : Blo 2161435 2163183 := bstep (se 1 (by rfl) ⟨1622387, by rfl⟩ : syracuseStep 2163183 = 3244775) B3244775
theorem B3244781 : Blo 2161435 3244781 := bbase (se 3 (by rfl) ⟨608396, by rfl⟩ : syracuseStep 3244781 = 1216793) (by norm_num)
theorem B2163187 : Blo 2161435 2163187 := bstep (se 1 (by rfl) ⟨1622390, by rfl⟩ : syracuseStep 2163187 = 3244781) B3244781
theorem B4867181 : Blo 2161435 4867181 := bbase (se 3 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 4867181 = 1825193) (by norm_num)
theorem B3244787 : Blo 2161435 3244787 := bstep (se 1 (by rfl) ⟨2433590, by rfl⟩ : syracuseStep 3244787 = 4867181) B4867181
theorem B2163191 : Blo 2161435 2163191 := bstep (se 1 (by rfl) ⟨1622393, by rfl⟩ : syracuseStep 2163191 = 3244787) B3244787
theorem B4106693 : Blo 2161435 4106693 := bbase (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) (by norm_num)
theorem B2737795 : Blo 2161435 2737795 := bstep (se 1 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 2737795 = 4106693) B4106693
theorem B3650393 : Blo 2161435 3650393 := bstep (se 2 (by rfl) ⟨1368897, by rfl⟩ : syracuseStep 3650393 = 2737795) B2737795
theorem B2433595 : Blo 2161435 2433595 := bstep (se 1 (by rfl) ⟨1825196, by rfl⟩ : syracuseStep 2433595 = 3650393) B3650393
theorem B3244793 : Blo 2161435 3244793 := bstep (se 2 (by rfl) ⟨1216797, by rfl⟩ : syracuseStep 3244793 = 2433595) B2433595
theorem B2163195 : Blo 2161435 2163195 := bstep (se 1 (by rfl) ⟨1622396, by rfl⟩ : syracuseStep 2163195 = 3244793) B3244793
theorem B8770853 : Blo 2161435 8770853 := bbase (se 4 (by rfl) ⟨822267, by rfl⟩ : syracuseStep 8770853 = 1644535) (by norm_num)
theorem B5847235 : Blo 2161435 5847235 := bstep (se 1 (by rfl) ⟨4385426, by rfl⟩ : syracuseStep 5847235 = 8770853) B8770853
theorem B31185253 : Blo 2161435 31185253 := bstep (se 4 (by rfl) ⟨2923617, by rfl⟩ : syracuseStep 31185253 = 5847235) B5847235
theorem B41580337 : Blo 2161435 41580337 := bstep (se 2 (by rfl) ⟨15592626, by rfl⟩ : syracuseStep 41580337 = 31185253) B31185253
theorem B55440449 : Blo 2161435 55440449 := bstep (se 2 (by rfl) ⟨20790168, by rfl⟩ : syracuseStep 55440449 = 41580337) B41580337
theorem B36960299 : Blo 2161435 36960299 := bstep (se 1 (by rfl) ⟨27720224, by rfl⟩ : syracuseStep 36960299 = 55440449) B55440449
theorem B24640199 : Blo 2161435 24640199 := bstep (se 1 (by rfl) ⟨18480149, by rfl⟩ : syracuseStep 24640199 = 36960299) B36960299
theorem B16426799 : Blo 2161435 16426799 := bstep (se 1 (by rfl) ⟨12320099, by rfl⟩ : syracuseStep 16426799 = 24640199) B24640199
theorem B10951199 : Blo 2161435 10951199 := bstep (se 1 (by rfl) ⟨8213399, by rfl⟩ : syracuseStep 10951199 = 16426799) B16426799
theorem B7300799 : Blo 2161435 7300799 := bstep (se 1 (by rfl) ⟨5475599, by rfl⟩ : syracuseStep 7300799 = 10951199) B10951199
theorem B4867199 : Blo 2161435 4867199 := bstep (se 1 (by rfl) ⟨3650399, by rfl⟩ : syracuseStep 4867199 = 7300799) B7300799
theorem B3244799 : Blo 2161435 3244799 := bstep (se 1 (by rfl) ⟨2433599, by rfl⟩ : syracuseStep 3244799 = 4867199) B4867199
theorem B2163199 : Blo 2161435 2163199 := bstep (se 1 (by rfl) ⟨1622399, by rfl⟩ : syracuseStep 2163199 = 3244799) B3244799
theorem B3244805 : Blo 2161435 3244805 := bbase (se 4 (by rfl) ⟨304200, by rfl⟩ : syracuseStep 3244805 = 608401) (by norm_num)
theorem B2163203 : Blo 2161435 2163203 := bstep (se 1 (by rfl) ⟨1622402, by rfl⟩ : syracuseStep 2163203 = 3244805) B3244805
theorem B3650413 : Blo 2161435 3650413 := bbase (se 3 (by rfl) ⟨684452, by rfl⟩ : syracuseStep 3650413 = 1368905) (by norm_num)
theorem B4867217 : Blo 2161435 4867217 := bstep (se 2 (by rfl) ⟨1825206, by rfl⟩ : syracuseStep 4867217 = 3650413) B3650413
theorem B3244811 : Blo 2161435 3244811 := bstep (se 1 (by rfl) ⟨2433608, by rfl⟩ : syracuseStep 3244811 = 4867217) B4867217
theorem B2163207 : Blo 2161435 2163207 := bstep (se 1 (by rfl) ⟨1622405, by rfl⟩ : syracuseStep 2163207 = 3244811) B3244811
theorem B2433613 : Blo 2161435 2433613 := bbase (se 3 (by rfl) ⟨456302, by rfl⟩ : syracuseStep 2433613 = 912605) (by norm_num)
theorem B3244817 : Blo 2161435 3244817 := bstep (se 2 (by rfl) ⟨1216806, by rfl⟩ : syracuseStep 3244817 = 2433613) B2433613
theorem B2163211 : Blo 2161435 2163211 := bstep (se 1 (by rfl) ⟨1622408, by rfl⟩ : syracuseStep 2163211 = 3244817) B3244817
theorem B7300853 : Blo 2161435 7300853 := bbase (se 5 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 7300853 = 684455) (by norm_num)
theorem B4867235 : Blo 2161435 4867235 := bstep (se 1 (by rfl) ⟨3650426, by rfl⟩ : syracuseStep 4867235 = 7300853) B7300853
theorem B3244823 : Blo 2161435 3244823 := bstep (se 1 (by rfl) ⟨2433617, by rfl⟩ : syracuseStep 3244823 = 4867235) B4867235
theorem B2163215 : Blo 2161435 2163215 := bstep (se 1 (by rfl) ⟨1622411, by rfl⟩ : syracuseStep 2163215 = 3244823) B3244823
theorem B3244829 : Blo 2161435 3244829 := bbase (se 3 (by rfl) ⟨608405, by rfl⟩ : syracuseStep 3244829 = 1216811) (by norm_num)
theorem B2163219 : Blo 2161435 2163219 := bstep (se 1 (by rfl) ⟨1622414, by rfl⟩ : syracuseStep 2163219 = 3244829) B3244829
theorem B4867253 : Blo 2161435 4867253 := bbase (se 5 (by rfl) ⟨228152, by rfl⟩ : syracuseStep 4867253 = 456305) (by norm_num)
theorem B3244835 : Blo 2161435 3244835 := bstep (se 1 (by rfl) ⟨2433626, by rfl⟩ : syracuseStep 3244835 = 4867253) B4867253
theorem B2163223 : Blo 2161435 2163223 := bstep (se 1 (by rfl) ⟨1622417, by rfl⟩ : syracuseStep 2163223 = 3244835) B3244835
theorem B2310049 : Blo 2161435 2310049 := bbase (se 2 (by rfl) ⟨866268, by rfl⟩ : syracuseStep 2310049 = 1732537) (by norm_num)
theorem B12320261 : Blo 2161435 12320261 := bstep (se 4 (by rfl) ⟨1155024, by rfl⟩ : syracuseStep 12320261 = 2310049) B2310049
theorem B8213507 : Blo 2161435 8213507 := bstep (se 1 (by rfl) ⟨6160130, by rfl⟩ : syracuseStep 8213507 = 12320261) B12320261
theorem B5475671 : Blo 2161435 5475671 := bstep (se 1 (by rfl) ⟨4106753, by rfl⟩ : syracuseStep 5475671 = 8213507) B8213507
theorem B3650447 : Blo 2161435 3650447 := bstep (se 1 (by rfl) ⟨2737835, by rfl⟩ : syracuseStep 3650447 = 5475671) B5475671
theorem B2433631 : Blo 2161435 2433631 := bstep (se 1 (by rfl) ⟨1825223, by rfl⟩ : syracuseStep 2433631 = 3650447) B3650447
theorem B3244841 : Blo 2161435 3244841 := bstep (se 2 (by rfl) ⟨1216815, by rfl⟩ : syracuseStep 3244841 = 2433631) B2433631
theorem B2163227 : Blo 2161435 2163227 := bstep (se 1 (by rfl) ⟨1622420, by rfl⟩ : syracuseStep 2163227 = 3244841) B3244841
theorem B2310053 : Blo 2161435 2310053 := bbase (se 4 (by rfl) ⟨216567, by rfl⟩ : syracuseStep 2310053 = 433135) (by norm_num)
theorem B6160141 : Blo 2161435 6160141 := bstep (se 3 (by rfl) ⟨1155026, by rfl⟩ : syracuseStep 6160141 = 2310053) B2310053
theorem B8213521 : Blo 2161435 8213521 := bstep (se 2 (by rfl) ⟨3080070, by rfl⟩ : syracuseStep 8213521 = 6160141) B6160141
theorem B10951361 : Blo 2161435 10951361 := bstep (se 2 (by rfl) ⟨4106760, by rfl⟩ : syracuseStep 10951361 = 8213521) B8213521
theorem B7300907 : Blo 2161435 7300907 := bstep (se 1 (by rfl) ⟨5475680, by rfl⟩ : syracuseStep 7300907 = 10951361) B10951361
theorem B4867271 : Blo 2161435 4867271 := bstep (se 1 (by rfl) ⟨3650453, by rfl⟩ : syracuseStep 4867271 = 7300907) B7300907
theorem B3244847 : Blo 2161435 3244847 := bstep (se 1 (by rfl) ⟨2433635, by rfl⟩ : syracuseStep 3244847 = 4867271) B4867271
theorem B2163231 : Blo 2161435 2163231 := bstep (se 1 (by rfl) ⟨1622423, by rfl⟩ : syracuseStep 2163231 = 3244847) B3244847
theorem B3244853 : Blo 2161435 3244853 := bbase (se 5 (by rfl) ⟨152102, by rfl⟩ : syracuseStep 3244853 = 304205) (by norm_num)
theorem B2163235 : Blo 2161435 2163235 := bstep (se 1 (by rfl) ⟨1622426, by rfl⟩ : syracuseStep 2163235 = 3244853) B3244853
theorem B5475701 : Blo 2161435 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B3650467 : Blo 2161435 3650467 := bstep (se 1 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 3650467 = 5475701) B5475701
theorem B4867289 : Blo 2161435 4867289 := bstep (se 2 (by rfl) ⟨1825233, by rfl⟩ : syracuseStep 4867289 = 3650467) B3650467
theorem B3244859 : Blo 2161435 3244859 := bstep (se 1 (by rfl) ⟨2433644, by rfl⟩ : syracuseStep 3244859 = 4867289) B4867289
theorem B2163239 : Blo 2161435 2163239 := bstep (se 1 (by rfl) ⟨1622429, by rfl⟩ : syracuseStep 2163239 = 3244859) B3244859
theorem B2433649 : Blo 2161435 2433649 := bbase (se 2 (by rfl) ⟨912618, by rfl⟩ : syracuseStep 2433649 = 1825237) (by norm_num)
theorem B3244865 : Blo 2161435 3244865 := bstep (se 2 (by rfl) ⟨1216824, by rfl⟩ : syracuseStep 3244865 = 2433649) B2433649
theorem B2163243 : Blo 2161435 2163243 := bstep (se 1 (by rfl) ⟨1622432, by rfl⟩ : syracuseStep 2163243 = 3244865) B3244865
theorem B10395317 : Blo 2161435 10395317 := bbase (se 5 (by rfl) ⟨487280, by rfl⟩ : syracuseStep 10395317 = 974561) (by norm_num)
theorem B6930211 : Blo 2161435 6930211 := bstep (se 1 (by rfl) ⟨5197658, by rfl⟩ : syracuseStep 6930211 = 10395317) B10395317
theorem B9240281 : Blo 2161435 9240281 := bstep (se 2 (by rfl) ⟨3465105, by rfl⟩ : syracuseStep 9240281 = 6930211) B6930211
theorem B6160187 : Blo 2161435 6160187 := bstep (se 1 (by rfl) ⟨4620140, by rfl⟩ : syracuseStep 6160187 = 9240281) B9240281
theorem B4106791 : Blo 2161435 4106791 := bstep (se 1 (by rfl) ⟨3080093, by rfl⟩ : syracuseStep 4106791 = 6160187) B6160187
theorem B5475721 : Blo 2161435 5475721 := bstep (se 2 (by rfl) ⟨2053395, by rfl⟩ : syracuseStep 5475721 = 4106791) B4106791
theorem B7300961 : Blo 2161435 7300961 := bstep (se 2 (by rfl) ⟨2737860, by rfl⟩ : syracuseStep 7300961 = 5475721) B5475721
theorem B4867307 : Blo 2161435 4867307 := bstep (se 1 (by rfl) ⟨3650480, by rfl⟩ : syracuseStep 4867307 = 7300961) B7300961
theorem B3244871 : Blo 2161435 3244871 := bstep (se 1 (by rfl) ⟨2433653, by rfl⟩ : syracuseStep 3244871 = 4867307) B4867307
theorem B2163247 : Blo 2161435 2163247 := bstep (se 1 (by rfl) ⟨1622435, by rfl⟩ : syracuseStep 2163247 = 3244871) B3244871
theorem B3244877 : Blo 2161435 3244877 := bbase (se 3 (by rfl) ⟨608414, by rfl⟩ : syracuseStep 3244877 = 1216829) (by norm_num)
theorem B2163251 : Blo 2161435 2163251 := bstep (se 1 (by rfl) ⟨1622438, by rfl⟩ : syracuseStep 2163251 = 3244877) B3244877
theorem B4867325 : Blo 2161435 4867325 := bbase (se 3 (by rfl) ⟨912623, by rfl⟩ : syracuseStep 4867325 = 1825247) (by norm_num)
theorem B3244883 : Blo 2161435 3244883 := bstep (se 1 (by rfl) ⟨2433662, by rfl⟩ : syracuseStep 3244883 = 4867325) B4867325
theorem B2163255 : Blo 2161435 2163255 := bstep (se 1 (by rfl) ⟨1622441, by rfl⟩ : syracuseStep 2163255 = 3244883) B3244883
theorem B3650501 : Blo 2161435 3650501 := bbase (se 4 (by rfl) ⟨342234, by rfl⟩ : syracuseStep 3650501 = 684469) (by norm_num)
theorem B2433667 : Blo 2161435 2433667 := bstep (se 1 (by rfl) ⟨1825250, by rfl⟩ : syracuseStep 2433667 = 3650501) B3650501
theorem B3244889 : Blo 2161435 3244889 := bstep (se 2 (by rfl) ⟨1216833, by rfl⟩ : syracuseStep 3244889 = 2433667) B2433667
theorem B2163259 : Blo 2161435 2163259 := bstep (se 1 (by rfl) ⟨1622444, by rfl⟩ : syracuseStep 2163259 = 3244889) B3244889
theorem B16427285 : Blo 2161435 16427285 := bbase (se 6 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 16427285 = 770029) (by norm_num)
theorem B10951523 : Blo 2161435 10951523 := bstep (se 1 (by rfl) ⟨8213642, by rfl⟩ : syracuseStep 10951523 = 16427285) B16427285
theorem B7301015 : Blo 2161435 7301015 := bstep (se 1 (by rfl) ⟨5475761, by rfl⟩ : syracuseStep 7301015 = 10951523) B10951523
theorem B4867343 : Blo 2161435 4867343 := bstep (se 1 (by rfl) ⟨3650507, by rfl⟩ : syracuseStep 4867343 = 7301015) B7301015
theorem B3244895 : Blo 2161435 3244895 := bstep (se 1 (by rfl) ⟨2433671, by rfl⟩ : syracuseStep 3244895 = 4867343) B4867343
theorem B2163263 : Blo 2161435 2163263 := bstep (se 1 (by rfl) ⟨1622447, by rfl⟩ : syracuseStep 2163263 = 3244895) B3244895
theorem B3244901 : Blo 2161435 3244901 := bbase (se 4 (by rfl) ⟨304209, by rfl⟩ : syracuseStep 3244901 = 608419) (by norm_num)
theorem B2163267 : Blo 2161435 2163267 := bstep (se 1 (by rfl) ⟨1622450, by rfl⟩ : syracuseStep 2163267 = 3244901) B3244901
theorem B4106837 : Blo 2161435 4106837 := bbase (se 8 (by rfl) ⟨24063, by rfl⟩ : syracuseStep 4106837 = 48127) (by norm_num)
theorem B2737891 : Blo 2161435 2737891 := bstep (se 1 (by rfl) ⟨2053418, by rfl⟩ : syracuseStep 2737891 = 4106837) B4106837
theorem B3650521 : Blo 2161435 3650521 := bstep (se 2 (by rfl) ⟨1368945, by rfl⟩ : syracuseStep 3650521 = 2737891) B2737891
theorem B4867361 : Blo 2161435 4867361 := bstep (se 2 (by rfl) ⟨1825260, by rfl⟩ : syracuseStep 4867361 = 3650521) B3650521
theorem B3244907 : Blo 2161435 3244907 := bstep (se 1 (by rfl) ⟨2433680, by rfl⟩ : syracuseStep 3244907 = 4867361) B4867361
theorem B2163271 : Blo 2161435 2163271 := bstep (se 1 (by rfl) ⟨1622453, by rfl⟩ : syracuseStep 2163271 = 3244907) B3244907
theorem B2433685 : Blo 2161435 2433685 := bbase (se 6 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 2433685 = 114079) (by norm_num)
theorem B3244913 : Blo 2161435 3244913 := bstep (se 2 (by rfl) ⟨1216842, by rfl⟩ : syracuseStep 3244913 = 2433685) B2433685
theorem B2163275 : Blo 2161435 2163275 := bstep (se 1 (by rfl) ⟨1622456, by rfl⟩ : syracuseStep 2163275 = 3244913) B3244913
theorem B2737901 : Blo 2161435 2737901 := bbase (se 3 (by rfl) ⟨513356, by rfl⟩ : syracuseStep 2737901 = 1026713) (by norm_num)
theorem B7301069 : Blo 2161435 7301069 := bstep (se 3 (by rfl) ⟨1368950, by rfl⟩ : syracuseStep 7301069 = 2737901) B2737901
theorem B4867379 : Blo 2161435 4867379 := bstep (se 1 (by rfl) ⟨3650534, by rfl⟩ : syracuseStep 4867379 = 7301069) B7301069
theorem B3244919 : Blo 2161435 3244919 := bstep (se 1 (by rfl) ⟨2433689, by rfl⟩ : syracuseStep 3244919 = 4867379) B4867379
theorem B2163279 : Blo 2161435 2163279 := bstep (se 1 (by rfl) ⟨1622459, by rfl⟩ : syracuseStep 2163279 = 3244919) B3244919
theorem B3244925 : Blo 2161435 3244925 := bbase (se 3 (by rfl) ⟨608423, by rfl⟩ : syracuseStep 3244925 = 1216847) (by norm_num)
theorem B2163283 : Blo 2161435 2163283 := bstep (se 1 (by rfl) ⟨1622462, by rfl⟩ : syracuseStep 2163283 = 3244925) B3244925
theorem B4867397 : Blo 2161435 4867397 := bbase (se 4 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 4867397 = 912637) (by norm_num)
theorem B3244931 : Blo 2161435 3244931 := bstep (se 1 (by rfl) ⟨2433698, by rfl⟩ : syracuseStep 3244931 = 4867397) B4867397
theorem B2163287 : Blo 2161435 2163287 := bstep (se 1 (by rfl) ⟨1622465, by rfl⟩ : syracuseStep 2163287 = 3244931) B3244931
theorem B5197765 : Blo 2161435 5197765 := bbase (se 4 (by rfl) ⟨487290, by rfl⟩ : syracuseStep 5197765 = 974581) (by norm_num)
theorem B6930353 : Blo 2161435 6930353 := bstep (se 2 (by rfl) ⟨2598882, by rfl⟩ : syracuseStep 6930353 = 5197765) B5197765
theorem B4620235 : Blo 2161435 4620235 := bstep (se 1 (by rfl) ⟨3465176, by rfl⟩ : syracuseStep 4620235 = 6930353) B6930353
theorem B6160313 : Blo 2161435 6160313 := bstep (se 2 (by rfl) ⟨2310117, by rfl⟩ : syracuseStep 6160313 = 4620235) B4620235
theorem B4106875 : Blo 2161435 4106875 := bstep (se 1 (by rfl) ⟨3080156, by rfl⟩ : syracuseStep 4106875 = 6160313) B6160313
theorem B5475833 : Blo 2161435 5475833 := bstep (se 2 (by rfl) ⟨2053437, by rfl⟩ : syracuseStep 5475833 = 4106875) B4106875
theorem B3650555 : Blo 2161435 3650555 := bstep (se 1 (by rfl) ⟨2737916, by rfl⟩ : syracuseStep 3650555 = 5475833) B5475833
theorem B2433703 : Blo 2161435 2433703 := bstep (se 1 (by rfl) ⟨1825277, by rfl⟩ : syracuseStep 2433703 = 3650555) B3650555
theorem B3244937 : Blo 2161435 3244937 := bstep (se 2 (by rfl) ⟨1216851, by rfl⟩ : syracuseStep 3244937 = 2433703) B2433703
theorem B2163291 : Blo 2161435 2163291 := bstep (se 1 (by rfl) ⟨1622468, by rfl⟩ : syracuseStep 2163291 = 3244937) B3244937
theorem B10951685 : Blo 2161435 10951685 := bbase (se 4 (by rfl) ⟨1026720, by rfl⟩ : syracuseStep 10951685 = 2053441) (by norm_num)
theorem B7301123 : Blo 2161435 7301123 := bstep (se 1 (by rfl) ⟨5475842, by rfl⟩ : syracuseStep 7301123 = 10951685) B10951685
theorem B4867415 : Blo 2161435 4867415 := bstep (se 1 (by rfl) ⟨3650561, by rfl⟩ : syracuseStep 4867415 = 7301123) B7301123
theorem B3244943 : Blo 2161435 3244943 := bstep (se 1 (by rfl) ⟨2433707, by rfl⟩ : syracuseStep 3244943 = 4867415) B4867415
theorem B2163295 : Blo 2161435 2163295 := bstep (se 1 (by rfl) ⟨1622471, by rfl⟩ : syracuseStep 2163295 = 3244943) B3244943
theorem B3244949 : Blo 2161435 3244949 := bbase (se 6 (by rfl) ⟨76053, by rfl⟩ : syracuseStep 3244949 = 152107) (by norm_num)
theorem B2163299 : Blo 2161435 2163299 := bstep (se 1 (by rfl) ⟨1622474, by rfl⟩ : syracuseStep 2163299 = 3244949) B3244949
theorem B12320693 : Blo 2161435 12320693 := bbase (se 5 (by rfl) ⟨577532, by rfl⟩ : syracuseStep 12320693 = 1155065) (by norm_num)
theorem B8213795 : Blo 2161435 8213795 := bstep (se 1 (by rfl) ⟨6160346, by rfl⟩ : syracuseStep 8213795 = 12320693) B12320693
theorem B5475863 : Blo 2161435 5475863 := bstep (se 1 (by rfl) ⟨4106897, by rfl⟩ : syracuseStep 5475863 = 8213795) B8213795
theorem B3650575 : Blo 2161435 3650575 := bstep (se 1 (by rfl) ⟨2737931, by rfl⟩ : syracuseStep 3650575 = 5475863) B5475863
theorem B4867433 : Blo 2161435 4867433 := bstep (se 2 (by rfl) ⟨1825287, by rfl⟩ : syracuseStep 4867433 = 3650575) B3650575
theorem B3244955 : Blo 2161435 3244955 := bstep (se 1 (by rfl) ⟨2433716, by rfl⟩ : syracuseStep 3244955 = 4867433) B4867433
theorem B2163303 : Blo 2161435 2163303 := bstep (se 1 (by rfl) ⟨1622477, by rfl⟩ : syracuseStep 2163303 = 3244955) B3244955
theorem B2433721 : Blo 2161435 2433721 := bbase (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) (by norm_num)
theorem B3244961 : Blo 2161435 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2163307 : Blo 2161435 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B4620277 : Blo 2161435 4620277 := bbase (se 5 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 4620277 = 433151) (by norm_num)
theorem B6160369 : Blo 2161435 6160369 := bstep (se 2 (by rfl) ⟨2310138, by rfl⟩ : syracuseStep 6160369 = 4620277) B4620277
theorem B8213825 : Blo 2161435 8213825 := bstep (se 2 (by rfl) ⟨3080184, by rfl⟩ : syracuseStep 8213825 = 6160369) B6160369
theorem B5475883 : Blo 2161435 5475883 := bstep (se 1 (by rfl) ⟨4106912, by rfl⟩ : syracuseStep 5475883 = 8213825) B8213825
theorem B7301177 : Blo 2161435 7301177 := bstep (se 2 (by rfl) ⟨2737941, by rfl⟩ : syracuseStep 7301177 = 5475883) B5475883
theorem B4867451 : Blo 2161435 4867451 := bstep (se 1 (by rfl) ⟨3650588, by rfl⟩ : syracuseStep 4867451 = 7301177) B7301177
theorem B3244967 : Blo 2161435 3244967 := bstep (se 1 (by rfl) ⟨2433725, by rfl⟩ : syracuseStep 3244967 = 4867451) B4867451
theorem B2163311 : Blo 2161435 2163311 := bstep (se 1 (by rfl) ⟨1622483, by rfl⟩ : syracuseStep 2163311 = 3244967) B3244967
theorem B3244973 : Blo 2161435 3244973 := bbase (se 3 (by rfl) ⟨608432, by rfl⟩ : syracuseStep 3244973 = 1216865) (by norm_num)
theorem B2163315 : Blo 2161435 2163315 := bstep (se 1 (by rfl) ⟨1622486, by rfl⟩ : syracuseStep 2163315 = 3244973) B3244973
theorem B4867469 : Blo 2161435 4867469 := bbase (se 3 (by rfl) ⟨912650, by rfl⟩ : syracuseStep 4867469 = 1825301) (by norm_num)
theorem B3244979 : Blo 2161435 3244979 := bstep (se 1 (by rfl) ⟨2433734, by rfl⟩ : syracuseStep 3244979 = 4867469) B4867469
theorem B2163319 : Blo 2161435 2163319 := bstep (se 1 (by rfl) ⟨1622489, by rfl⟩ : syracuseStep 2163319 = 3244979) B3244979
theorem B2737957 : Blo 2161435 2737957 := bbase (se 4 (by rfl) ⟨256683, by rfl⟩ : syracuseStep 2737957 = 513367) (by norm_num)
theorem B3650609 : Blo 2161435 3650609 := bstep (se 2 (by rfl) ⟨1368978, by rfl⟩ : syracuseStep 3650609 = 2737957) B2737957
theorem B2433739 : Blo 2161435 2433739 := bstep (se 1 (by rfl) ⟨1825304, by rfl⟩ : syracuseStep 2433739 = 3650609) B3650609
theorem B3244985 : Blo 2161435 3244985 := bstep (se 2 (by rfl) ⟨1216869, by rfl⟩ : syracuseStep 3244985 = 2433739) B2433739
theorem B2163323 : Blo 2161435 2163323 := bstep (se 1 (by rfl) ⟨1622492, by rfl⟩ : syracuseStep 2163323 = 3244985) B3244985
theorem B10827029 : Blo 2161435 10827029 := bbase (se 6 (by rfl) ⟨253758, by rfl⟩ : syracuseStep 10827029 = 507517) (by norm_num)
theorem B7218019 : Blo 2161435 7218019 := bstep (se 1 (by rfl) ⟨5413514, by rfl⟩ : syracuseStep 7218019 = 10827029) B10827029
theorem B9624025 : Blo 2161435 9624025 := bstep (se 2 (by rfl) ⟨3609009, by rfl⟩ : syracuseStep 9624025 = 7218019) B7218019
theorem B12832033 : Blo 2161435 12832033 := bstep (se 2 (by rfl) ⟨4812012, by rfl⟩ : syracuseStep 12832033 = 9624025) B9624025
theorem B17109377 : Blo 2161435 17109377 := bstep (se 2 (by rfl) ⟨6416016, by rfl⟩ : syracuseStep 17109377 = 12832033) B12832033
theorem B11406251 : Blo 2161435 11406251 := bstep (se 1 (by rfl) ⟨8554688, by rfl⟩ : syracuseStep 11406251 = 17109377) B17109377
theorem B7604167 : Blo 2161435 7604167 := bstep (se 1 (by rfl) ⟨5703125, by rfl⟩ : syracuseStep 7604167 = 11406251) B11406251
theorem B10138889 : Blo 2161435 10138889 := bstep (se 2 (by rfl) ⟨3802083, by rfl⟩ : syracuseStep 10138889 = 7604167) B7604167
theorem B27037037 : Blo 2161435 27037037 := bstep (se 3 (by rfl) ⟨5069444, by rfl⟩ : syracuseStep 27037037 = 10138889) B10138889
theorem B72098765 : Blo 2161435 72098765 := bstep (se 3 (by rfl) ⟨13518518, by rfl⟩ : syracuseStep 72098765 = 27037037) B27037037
theorem B48065843 : Blo 2161435 48065843 := bstep (se 1 (by rfl) ⟨36049382, by rfl⟩ : syracuseStep 48065843 = 72098765) B72098765
theorem B128175581 : Blo 2161435 128175581 := bstep (se 3 (by rfl) ⟨24032921, by rfl⟩ : syracuseStep 128175581 = 48065843) B48065843
theorem B341801549 : Blo 2161435 341801549 := bstep (se 3 (by rfl) ⟨64087790, by rfl⟩ : syracuseStep 341801549 = 128175581) B128175581
theorem B227867699 : Blo 2161435 227867699 := bstep (se 1 (by rfl) ⟨170900774, by rfl⟩ : syracuseStep 227867699 = 341801549) B341801549
theorem B607647197 : Blo 2161435 607647197 := bstep (se 3 (by rfl) ⟨113933849, by rfl⟩ : syracuseStep 607647197 = 227867699) B227867699
theorem B405098131 : Blo 2161435 405098131 := bstep (se 1 (by rfl) ⟨303823598, by rfl⟩ : syracuseStep 405098131 = 607647197) B607647197
theorem B540130841 : Blo 2161435 540130841 := bstep (se 2 (by rfl) ⟨202549065, by rfl⟩ : syracuseStep 540130841 = 405098131) B405098131
theorem B360087227 : Blo 2161435 360087227 := bstep (se 1 (by rfl) ⟨270065420, by rfl⟩ : syracuseStep 360087227 = 540130841) B540130841
theorem B240058151 : Blo 2161435 240058151 := bstep (se 1 (by rfl) ⟨180043613, by rfl⟩ : syracuseStep 240058151 = 360087227) B360087227
theorem B160038767 : Blo 2161435 160038767 := bstep (se 1 (by rfl) ⟨120029075, by rfl⟩ : syracuseStep 160038767 = 240058151) B240058151
theorem B106692511 : Blo 2161435 106692511 := bstep (se 1 (by rfl) ⟨80019383, by rfl⟩ : syracuseStep 106692511 = 160038767) B160038767
theorem B142256681 : Blo 2161435 142256681 := bstep (se 2 (by rfl) ⟨53346255, by rfl⟩ : syracuseStep 142256681 = 106692511) B106692511
theorem B94837787 : Blo 2161435 94837787 := bstep (se 1 (by rfl) ⟨71128340, by rfl⟩ : syracuseStep 94837787 = 142256681) B142256681
theorem B63225191 : Blo 2161435 63225191 := bstep (se 1 (by rfl) ⟨47418893, by rfl⟩ : syracuseStep 63225191 = 94837787) B94837787
theorem B42150127 : Blo 2161435 42150127 := bstep (se 1 (by rfl) ⟨31612595, by rfl⟩ : syracuseStep 42150127 = 63225191) B63225191
theorem B56200169 : Blo 2161435 56200169 := bstep (se 2 (by rfl) ⟨21075063, by rfl⟩ : syracuseStep 56200169 = 42150127) B42150127
theorem B37466779 : Blo 2161435 37466779 := bstep (se 1 (by rfl) ⟨28100084, by rfl⟩ : syracuseStep 37466779 = 56200169) B56200169
theorem B49955705 : Blo 2161435 49955705 := bstep (se 2 (by rfl) ⟨18733389, by rfl⟩ : syracuseStep 49955705 = 37466779) B37466779
theorem B33303803 : Blo 2161435 33303803 := bstep (se 1 (by rfl) ⟨24977852, by rfl⟩ : syracuseStep 33303803 = 49955705) B49955705
theorem B88810141 : Blo 2161435 88810141 := bstep (se 3 (by rfl) ⟨16651901, by rfl⟩ : syracuseStep 88810141 = 33303803) B33303803
theorem B118413521 : Blo 2161435 118413521 := bstep (se 2 (by rfl) ⟨44405070, by rfl⟩ : syracuseStep 118413521 = 88810141) B88810141
theorem B78942347 : Blo 2161435 78942347 := bstep (se 1 (by rfl) ⟨59206760, by rfl⟩ : syracuseStep 78942347 = 118413521) B118413521
theorem B52628231 : Blo 2161435 52628231 := bstep (se 1 (by rfl) ⟨39471173, by rfl⟩ : syracuseStep 52628231 = 78942347) B78942347
theorem B35085487 : Blo 2161435 35085487 := bstep (se 1 (by rfl) ⟨26314115, by rfl⟩ : syracuseStep 35085487 = 52628231) B52628231
theorem B46780649 : Blo 2161435 46780649 := bstep (se 2 (by rfl) ⟨17542743, by rfl⟩ : syracuseStep 46780649 = 35085487) B35085487
theorem B31187099 : Blo 2161435 31187099 := bstep (se 1 (by rfl) ⟨23390324, by rfl⟩ : syracuseStep 31187099 = 46780649) B46780649
theorem B20791399 : Blo 2161435 20791399 := bstep (se 1 (by rfl) ⟨15593549, by rfl⟩ : syracuseStep 20791399 = 31187099) B31187099
theorem B27721865 : Blo 2161435 27721865 := bstep (se 2 (by rfl) ⟨10395699, by rfl⟩ : syracuseStep 27721865 = 20791399) B20791399
theorem B18481243 : Blo 2161435 18481243 := bstep (se 1 (by rfl) ⟨13860932, by rfl⟩ : syracuseStep 18481243 = 27721865) B27721865
theorem B24641657 : Blo 2161435 24641657 := bstep (se 2 (by rfl) ⟨9240621, by rfl⟩ : syracuseStep 24641657 = 18481243) B18481243
theorem B16427771 : Blo 2161435 16427771 := bstep (se 1 (by rfl) ⟨12320828, by rfl⟩ : syracuseStep 16427771 = 24641657) B24641657
theorem B10951847 : Blo 2161435 10951847 := bstep (se 1 (by rfl) ⟨8213885, by rfl⟩ : syracuseStep 10951847 = 16427771) B16427771
theorem B7301231 : Blo 2161435 7301231 := bstep (se 1 (by rfl) ⟨5475923, by rfl⟩ : syracuseStep 7301231 = 10951847) B10951847
theorem B4867487 : Blo 2161435 4867487 := bstep (se 1 (by rfl) ⟨3650615, by rfl⟩ : syracuseStep 4867487 = 7301231) B7301231
theorem B3244991 : Blo 2161435 3244991 := bstep (se 1 (by rfl) ⟨2433743, by rfl⟩ : syracuseStep 3244991 = 4867487) B4867487
theorem B2163327 : Blo 2161435 2163327 := bstep (se 1 (by rfl) ⟨1622495, by rfl⟩ : syracuseStep 2163327 = 3244991) B3244991
theorem B3244997 : Blo 2161435 3244997 := bbase (se 4 (by rfl) ⟨304218, by rfl⟩ : syracuseStep 3244997 = 608437) (by norm_num)
theorem B2163331 : Blo 2161435 2163331 := bstep (se 1 (by rfl) ⟨1622498, by rfl⟩ : syracuseStep 2163331 = 3244997) B3244997
theorem B3650629 : Blo 2161435 3650629 := bbase (se 4 (by rfl) ⟨342246, by rfl⟩ : syracuseStep 3650629 = 684493) (by norm_num)
theorem B4867505 : Blo 2161435 4867505 := bstep (se 2 (by rfl) ⟨1825314, by rfl⟩ : syracuseStep 4867505 = 3650629) B3650629
theorem B3245003 : Blo 2161435 3245003 := bstep (se 1 (by rfl) ⟨2433752, by rfl⟩ : syracuseStep 3245003 = 4867505) B4867505
theorem B2163335 : Blo 2161435 2163335 := bstep (se 1 (by rfl) ⟨1622501, by rfl⟩ : syracuseStep 2163335 = 3245003) B3245003
theorem B2433757 : Blo 2161435 2433757 := bbase (se 3 (by rfl) ⟨456329, by rfl⟩ : syracuseStep 2433757 = 912659) (by norm_num)
theorem B3245009 : Blo 2161435 3245009 := bstep (se 2 (by rfl) ⟨1216878, by rfl⟩ : syracuseStep 3245009 = 2433757) B2433757
theorem B2163339 : Blo 2161435 2163339 := bstep (se 1 (by rfl) ⟨1622504, by rfl⟩ : syracuseStep 2163339 = 3245009) B3245009
theorem B7301285 : Blo 2161435 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B4867523 : Blo 2161435 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B3245015 : Blo 2161435 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B2163343 : Blo 2161435 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B3245021 : Blo 2161435 3245021 := bbase (se 3 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 3245021 = 1216883) (by norm_num)
theorem B2163347 : Blo 2161435 2163347 := bstep (se 1 (by rfl) ⟨1622510, by rfl⟩ : syracuseStep 2163347 = 3245021) B3245021
theorem B4867541 : Blo 2161435 4867541 := bbase (se 7 (by rfl) ⟨57041, by rfl⟩ : syracuseStep 4867541 = 114083) (by norm_num)
theorem B3245027 : Blo 2161435 3245027 := bstep (se 1 (by rfl) ⟨2433770, by rfl⟩ : syracuseStep 3245027 = 4867541) B4867541
theorem B2163351 : Blo 2161435 2163351 := bstep (se 1 (by rfl) ⟨1622513, by rfl⟩ : syracuseStep 2163351 = 3245027) B3245027
theorem B3512557 : Blo 2161435 3512557 := bbase (se 3 (by rfl) ⟨658604, by rfl⟩ : syracuseStep 3512557 = 1317209) (by norm_num)
theorem B18733637 : Blo 2161435 18733637 := bstep (se 4 (by rfl) ⟨1756278, by rfl⟩ : syracuseStep 18733637 = 3512557) B3512557
theorem B49956365 : Blo 2161435 49956365 := bstep (se 3 (by rfl) ⟨9366818, by rfl⟩ : syracuseStep 49956365 = 18733637) B18733637
theorem B133216973 : Blo 2161435 133216973 := bstep (se 3 (by rfl) ⟨24978182, by rfl⟩ : syracuseStep 133216973 = 49956365) B49956365
theorem B88811315 : Blo 2161435 88811315 := bstep (se 1 (by rfl) ⟨66608486, by rfl⟩ : syracuseStep 88811315 = 133216973) B133216973
theorem B59207543 : Blo 2161435 59207543 := bstep (se 1 (by rfl) ⟨44405657, by rfl⟩ : syracuseStep 59207543 = 88811315) B88811315
theorem B39471695 : Blo 2161435 39471695 := bstep (se 1 (by rfl) ⟨29603771, by rfl⟩ : syracuseStep 39471695 = 59207543) B59207543
theorem B26314463 : Blo 2161435 26314463 := bstep (se 1 (by rfl) ⟨19735847, by rfl⟩ : syracuseStep 26314463 = 39471695) B39471695
theorem B17542975 : Blo 2161435 17542975 := bstep (se 1 (by rfl) ⟨13157231, by rfl⟩ : syracuseStep 17542975 = 26314463) B26314463
theorem B23390633 : Blo 2161435 23390633 := bstep (se 2 (by rfl) ⟨8771487, by rfl⟩ : syracuseStep 23390633 = 17542975) B17542975
theorem B15593755 : Blo 2161435 15593755 := bstep (se 1 (by rfl) ⟨11695316, by rfl⟩ : syracuseStep 15593755 = 23390633) B23390633
theorem B20791673 : Blo 2161435 20791673 := bstep (se 2 (by rfl) ⟨7796877, by rfl⟩ : syracuseStep 20791673 = 15593755) B15593755
theorem B13861115 : Blo 2161435 13861115 := bstep (se 1 (by rfl) ⟨10395836, by rfl⟩ : syracuseStep 13861115 = 20791673) B20791673
theorem B9240743 : Blo 2161435 9240743 := bstep (se 1 (by rfl) ⟨6930557, by rfl⟩ : syracuseStep 9240743 = 13861115) B13861115
theorem B6160495 : Blo 2161435 6160495 := bstep (se 1 (by rfl) ⟨4620371, by rfl⟩ : syracuseStep 6160495 = 9240743) B9240743
theorem B8213993 : Blo 2161435 8213993 := bstep (se 2 (by rfl) ⟨3080247, by rfl⟩ : syracuseStep 8213993 = 6160495) B6160495
theorem B5475995 : Blo 2161435 5475995 := bstep (se 1 (by rfl) ⟨4106996, by rfl⟩ : syracuseStep 5475995 = 8213993) B8213993
theorem B3650663 : Blo 2161435 3650663 := bstep (se 1 (by rfl) ⟨2737997, by rfl⟩ : syracuseStep 3650663 = 5475995) B5475995
theorem B2433775 : Blo 2161435 2433775 := bstep (se 1 (by rfl) ⟨1825331, by rfl⟩ : syracuseStep 2433775 = 3650663) B3650663
theorem B3245033 : Blo 2161435 3245033 := bstep (se 2 (by rfl) ⟨1216887, by rfl⟩ : syracuseStep 3245033 = 2433775) B2433775
theorem B2163355 : Blo 2161435 2163355 := bstep (se 1 (by rfl) ⟨1622516, by rfl⟩ : syracuseStep 2163355 = 3245033) B3245033
theorem B22202869 : Blo 2161435 22202869 := bbase (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) (by norm_num)
theorem B29603825 : Blo 2161435 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B19735883 : Blo 2161435 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B13157255 : Blo 2161435 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B8771503 : Blo 2161435 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B11695337 : Blo 2161435 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B7796891 : Blo 2161435 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B5197927 : Blo 2161435 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B6930569 : Blo 2161435 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B18481517 : Blo 2161435 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B12321011 : Blo 2161435 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B8214007 : Blo 2161435 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B10952009 : Blo 2161435 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B7301339 : Blo 2161435 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B4867559 : Blo 2161435 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B3245039 : Blo 2161435 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B2163359 : Blo 2161435 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B3245045 : Blo 2161435 3245045 := bbase (se 5 (by rfl) ⟨152111, by rfl⟩ : syracuseStep 3245045 = 304223) (by norm_num)
theorem B2163363 : Blo 2161435 2163363 := bstep (se 1 (by rfl) ⟨1622522, by rfl⟩ : syracuseStep 2163363 = 3245045) B3245045
theorem B4620397 : Blo 2161435 4620397 := bbase (se 3 (by rfl) ⟨866324, by rfl⟩ : syracuseStep 4620397 = 1732649) (by norm_num)
theorem B6160529 : Blo 2161435 6160529 := bstep (se 2 (by rfl) ⟨2310198, by rfl⟩ : syracuseStep 6160529 = 4620397) B4620397
theorem B4107019 : Blo 2161435 4107019 := bstep (se 1 (by rfl) ⟨3080264, by rfl⟩ : syracuseStep 4107019 = 6160529) B6160529
theorem B5476025 : Blo 2161435 5476025 := bstep (se 2 (by rfl) ⟨2053509, by rfl⟩ : syracuseStep 5476025 = 4107019) B4107019
theorem B3650683 : Blo 2161435 3650683 := bstep (se 1 (by rfl) ⟨2738012, by rfl⟩ : syracuseStep 3650683 = 5476025) B5476025
theorem B4867577 : Blo 2161435 4867577 := bstep (se 2 (by rfl) ⟨1825341, by rfl⟩ : syracuseStep 4867577 = 3650683) B3650683
theorem B3245051 : Blo 2161435 3245051 := bstep (se 1 (by rfl) ⟨2433788, by rfl⟩ : syracuseStep 3245051 = 4867577) B4867577
theorem B2163367 : Blo 2161435 2163367 := bstep (se 1 (by rfl) ⟨1622525, by rfl⟩ : syracuseStep 2163367 = 3245051) B3245051
theorem B2433793 : Blo 2161435 2433793 := bbase (se 2 (by rfl) ⟨912672, by rfl⟩ : syracuseStep 2433793 = 1825345) (by norm_num)
theorem B3245057 : Blo 2161435 3245057 := bstep (se 2 (by rfl) ⟨1216896, by rfl⟩ : syracuseStep 3245057 = 2433793) B2433793
theorem B2163371 : Blo 2161435 2163371 := bstep (se 1 (by rfl) ⟨1622528, by rfl⟩ : syracuseStep 2163371 = 3245057) B3245057
theorem B5476045 : Blo 2161435 5476045 := bbase (se 3 (by rfl) ⟨1026758, by rfl⟩ : syracuseStep 5476045 = 2053517) (by norm_num)
theorem B7301393 : Blo 2161435 7301393 := bstep (se 2 (by rfl) ⟨2738022, by rfl⟩ : syracuseStep 7301393 = 5476045) B5476045
theorem B4867595 : Blo 2161435 4867595 := bstep (se 1 (by rfl) ⟨3650696, by rfl⟩ : syracuseStep 4867595 = 7301393) B7301393
theorem B3245063 : Blo 2161435 3245063 := bstep (se 1 (by rfl) ⟨2433797, by rfl⟩ : syracuseStep 3245063 = 4867595) B4867595
theorem B2163375 : Blo 2161435 2163375 := bstep (se 1 (by rfl) ⟨1622531, by rfl⟩ : syracuseStep 2163375 = 3245063) B3245063
theorem B3245069 : Blo 2161435 3245069 := bbase (se 3 (by rfl) ⟨608450, by rfl⟩ : syracuseStep 3245069 = 1216901) (by norm_num)
theorem B2163379 : Blo 2161435 2163379 := bstep (se 1 (by rfl) ⟨1622534, by rfl⟩ : syracuseStep 2163379 = 3245069) B3245069
theorem B4867613 : Blo 2161435 4867613 := bbase (se 3 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 4867613 = 1825355) (by norm_num)
theorem B3245075 : Blo 2161435 3245075 := bstep (se 1 (by rfl) ⟨2433806, by rfl⟩ : syracuseStep 3245075 = 4867613) B4867613
theorem B2163383 : Blo 2161435 2163383 := bstep (se 1 (by rfl) ⟨1622537, by rfl⟩ : syracuseStep 2163383 = 3245075) B3245075
theorem B3650717 : Blo 2161435 3650717 := bbase (se 3 (by rfl) ⟨684509, by rfl⟩ : syracuseStep 3650717 = 1369019) (by norm_num)
theorem B2433811 : Blo 2161435 2433811 := bstep (se 1 (by rfl) ⟨1825358, by rfl⟩ : syracuseStep 2433811 = 3650717) B3650717
theorem B3245081 : Blo 2161435 3245081 := bstep (se 2 (by rfl) ⟨1216905, by rfl⟩ : syracuseStep 3245081 = 2433811) B2433811
theorem B2163387 : Blo 2161435 2163387 := bstep (se 1 (by rfl) ⟨1622540, by rfl⟩ : syracuseStep 2163387 = 3245081) B3245081
theorem B6759461 : Blo 2161435 6759461 := bbase (se 4 (by rfl) ⟨633699, by rfl⟩ : syracuseStep 6759461 = 1267399) (by norm_num)
theorem B18025229 : Blo 2161435 18025229 := bstep (se 3 (by rfl) ⟨3379730, by rfl⟩ : syracuseStep 18025229 = 6759461) B6759461
theorem B12016819 : Blo 2161435 12016819 := bstep (se 1 (by rfl) ⟨9012614, by rfl⟩ : syracuseStep 12016819 = 18025229) B18025229
theorem B64089701 : Blo 2161435 64089701 := bstep (se 4 (by rfl) ⟨6008409, by rfl⟩ : syracuseStep 64089701 = 12016819) B12016819
theorem B42726467 : Blo 2161435 42726467 := bstep (se 1 (by rfl) ⟨32044850, by rfl⟩ : syracuseStep 42726467 = 64089701) B64089701
theorem B28484311 : Blo 2161435 28484311 := bstep (se 1 (by rfl) ⟨21363233, by rfl⟩ : syracuseStep 28484311 = 42726467) B42726467
theorem B37979081 : Blo 2161435 37979081 := bstep (se 2 (by rfl) ⟨14242155, by rfl⟩ : syracuseStep 37979081 = 28484311) B28484311
theorem B25319387 : Blo 2161435 25319387 := bstep (se 1 (by rfl) ⟨18989540, by rfl⟩ : syracuseStep 25319387 = 37979081) B37979081
theorem B16879591 : Blo 2161435 16879591 := bstep (se 1 (by rfl) ⟨12659693, by rfl⟩ : syracuseStep 16879591 = 25319387) B25319387
theorem B22506121 : Blo 2161435 22506121 := bstep (se 2 (by rfl) ⟨8439795, by rfl⟩ : syracuseStep 22506121 = 16879591) B16879591
theorem B30008161 : Blo 2161435 30008161 := bstep (se 2 (by rfl) ⟨11253060, by rfl⟩ : syracuseStep 30008161 = 22506121) B22506121
theorem B40010881 : Blo 2161435 40010881 := bstep (se 2 (by rfl) ⟨15004080, by rfl⟩ : syracuseStep 40010881 = 30008161) B30008161
theorem B53347841 : Blo 2161435 53347841 := bstep (se 2 (by rfl) ⟨20005440, by rfl⟩ : syracuseStep 53347841 = 40010881) B40010881
theorem B35565227 : Blo 2161435 35565227 := bstep (se 1 (by rfl) ⟨26673920, by rfl⟩ : syracuseStep 35565227 = 53347841) B53347841
theorem B23710151 : Blo 2161435 23710151 := bstep (se 1 (by rfl) ⟨17782613, by rfl⟩ : syracuseStep 23710151 = 35565227) B35565227
theorem B15806767 : Blo 2161435 15806767 := bstep (se 1 (by rfl) ⟨11855075, by rfl⟩ : syracuseStep 15806767 = 23710151) B23710151
theorem B21075689 : Blo 2161435 21075689 := bstep (se 2 (by rfl) ⟨7903383, by rfl⟩ : syracuseStep 21075689 = 15806767) B15806767
theorem B14050459 : Blo 2161435 14050459 := bstep (se 1 (by rfl) ⟨10537844, by rfl⟩ : syracuseStep 14050459 = 21075689) B21075689
theorem B18733945 : Blo 2161435 18733945 := bstep (se 2 (by rfl) ⟨7025229, by rfl⟩ : syracuseStep 18733945 = 14050459) B14050459
theorem B24978593 : Blo 2161435 24978593 := bstep (se 2 (by rfl) ⟨9366972, by rfl⟩ : syracuseStep 24978593 = 18733945) B18733945
theorem B16652395 : Blo 2161435 16652395 := bstep (se 1 (by rfl) ⟨12489296, by rfl⟩ : syracuseStep 16652395 = 24978593) B24978593
theorem B88812773 : Blo 2161435 88812773 := bstep (se 4 (by rfl) ⟨8326197, by rfl⟩ : syracuseStep 88812773 = 16652395) B16652395
theorem B59208515 : Blo 2161435 59208515 := bstep (se 1 (by rfl) ⟨44406386, by rfl⟩ : syracuseStep 59208515 = 88812773) B88812773
theorem B39472343 : Blo 2161435 39472343 := bstep (se 1 (by rfl) ⟨29604257, by rfl⟩ : syracuseStep 39472343 = 59208515) B59208515
theorem B26314895 : Blo 2161435 26314895 := bstep (se 1 (by rfl) ⟨19736171, by rfl⟩ : syracuseStep 26314895 = 39472343) B39472343
theorem B70173053 : Blo 2161435 70173053 := bstep (se 3 (by rfl) ⟨13157447, by rfl⟩ : syracuseStep 70173053 = 26314895) B26314895
theorem B46782035 : Blo 2161435 46782035 := bstep (se 1 (by rfl) ⟨35086526, by rfl⟩ : syracuseStep 46782035 = 70173053) B70173053
theorem B31188023 : Blo 2161435 31188023 := bstep (se 1 (by rfl) ⟨23391017, by rfl⟩ : syracuseStep 31188023 = 46782035) B46782035
theorem B20792015 : Blo 2161435 20792015 := bstep (se 1 (by rfl) ⟨15594011, by rfl⟩ : syracuseStep 20792015 = 31188023) B31188023
theorem B13861343 : Blo 2161435 13861343 := bstep (se 1 (by rfl) ⟨10396007, by rfl⟩ : syracuseStep 13861343 = 20792015) B20792015
theorem B9240895 : Blo 2161435 9240895 := bstep (se 1 (by rfl) ⟨6930671, by rfl⟩ : syracuseStep 9240895 = 13861343) B13861343
theorem B12321193 : Blo 2161435 12321193 := bstep (se 2 (by rfl) ⟨4620447, by rfl⟩ : syracuseStep 12321193 = 9240895) B9240895
theorem B16428257 : Blo 2161435 16428257 := bstep (se 2 (by rfl) ⟨6160596, by rfl⟩ : syracuseStep 16428257 = 12321193) B12321193
theorem B10952171 : Blo 2161435 10952171 := bstep (se 1 (by rfl) ⟨8214128, by rfl⟩ : syracuseStep 10952171 = 16428257) B16428257
theorem B7301447 : Blo 2161435 7301447 := bstep (se 1 (by rfl) ⟨5476085, by rfl⟩ : syracuseStep 7301447 = 10952171) B10952171
theorem B4867631 : Blo 2161435 4867631 := bstep (se 1 (by rfl) ⟨3650723, by rfl⟩ : syracuseStep 4867631 = 7301447) B7301447
theorem B3245087 : Blo 2161435 3245087 := bstep (se 1 (by rfl) ⟨2433815, by rfl⟩ : syracuseStep 3245087 = 4867631) B4867631
theorem B2163391 : Blo 2161435 2163391 := bstep (se 1 (by rfl) ⟨1622543, by rfl⟩ : syracuseStep 2163391 = 3245087) B3245087
theorem B3245093 : Blo 2161435 3245093 := bbase (se 4 (by rfl) ⟨304227, by rfl⟩ : syracuseStep 3245093 = 608455) (by norm_num)
theorem B2163395 : Blo 2161435 2163395 := bstep (se 1 (by rfl) ⟨1622546, by rfl⟩ : syracuseStep 2163395 = 3245093) B3245093
theorem B2738053 : Blo 2161435 2738053 := bbase (se 4 (by rfl) ⟨256692, by rfl⟩ : syracuseStep 2738053 = 513385) (by norm_num)
theorem B3650737 : Blo 2161435 3650737 := bstep (se 2 (by rfl) ⟨1369026, by rfl⟩ : syracuseStep 3650737 = 2738053) B2738053
theorem B4867649 : Blo 2161435 4867649 := bstep (se 2 (by rfl) ⟨1825368, by rfl⟩ : syracuseStep 4867649 = 3650737) B3650737
theorem B3245099 : Blo 2161435 3245099 := bstep (se 1 (by rfl) ⟨2433824, by rfl⟩ : syracuseStep 3245099 = 4867649) B4867649
theorem B2163399 : Blo 2161435 2163399 := bstep (se 1 (by rfl) ⟨1622549, by rfl⟩ : syracuseStep 2163399 = 3245099) B3245099
theorem B2433829 : Blo 2161435 2433829 := bbase (se 4 (by rfl) ⟨228171, by rfl⟩ : syracuseStep 2433829 = 456343) (by norm_num)
theorem B3245105 : Blo 2161435 3245105 := bstep (se 2 (by rfl) ⟨1216914, by rfl⟩ : syracuseStep 3245105 = 2433829) B2433829
theorem B2163403 : Blo 2161435 2163403 := bstep (se 1 (by rfl) ⟨1622552, by rfl⟩ : syracuseStep 2163403 = 3245105) B3245105
theorem B9240965 : Blo 2161435 9240965 := bbase (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) (by norm_num)
theorem B6160643 : Blo 2161435 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B4107095 : Blo 2161435 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B2738063 : Blo 2161435 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B7301501 : Blo 2161435 7301501 := bstep (se 3 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 7301501 = 2738063) B2738063
theorem B4867667 : Blo 2161435 4867667 := bstep (se 1 (by rfl) ⟨3650750, by rfl⟩ : syracuseStep 4867667 = 7301501) B7301501
theorem B3245111 : Blo 2161435 3245111 := bstep (se 1 (by rfl) ⟨2433833, by rfl⟩ : syracuseStep 3245111 = 4867667) B4867667
theorem B2163407 : Blo 2161435 2163407 := bstep (se 1 (by rfl) ⟨1622555, by rfl⟩ : syracuseStep 2163407 = 3245111) B3245111
theorem B3245117 : Blo 2161435 3245117 := bbase (se 3 (by rfl) ⟨608459, by rfl⟩ : syracuseStep 3245117 = 1216919) (by norm_num)
theorem B2163411 : Blo 2161435 2163411 := bstep (se 1 (by rfl) ⟨1622558, by rfl⟩ : syracuseStep 2163411 = 3245117) B3245117
theorem B4867685 : Blo 2161435 4867685 := bbase (se 4 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 4867685 = 912691) (by norm_num)
theorem B3245123 : Blo 2161435 3245123 := bstep (se 1 (by rfl) ⟨2433842, by rfl⟩ : syracuseStep 3245123 = 4867685) B4867685
theorem B2163415 : Blo 2161435 2163415 := bstep (se 1 (by rfl) ⟨1622561, by rfl⟩ : syracuseStep 2163415 = 3245123) B3245123
theorem B5476157 : Blo 2161435 5476157 := bbase (se 3 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 5476157 = 2053559) (by norm_num)
theorem B3650771 : Blo 2161435 3650771 := bstep (se 1 (by rfl) ⟨2738078, by rfl⟩ : syracuseStep 3650771 = 5476157) B5476157
theorem B2433847 : Blo 2161435 2433847 := bstep (se 1 (by rfl) ⟨1825385, by rfl⟩ : syracuseStep 2433847 = 3650771) B3650771
theorem B3245129 : Blo 2161435 3245129 := bstep (se 2 (by rfl) ⟨1216923, by rfl⟩ : syracuseStep 3245129 = 2433847) B2433847
theorem B2163419 : Blo 2161435 2163419 := bstep (se 1 (by rfl) ⟨1622564, by rfl⟩ : syracuseStep 2163419 = 3245129) B3245129
theorem B4107125 : Blo 2161435 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B10952333 : Blo 2161435 10952333 := bstep (se 3 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 10952333 = 4107125) B4107125
theorem B7301555 : Blo 2161435 7301555 := bstep (se 1 (by rfl) ⟨5476166, by rfl⟩ : syracuseStep 7301555 = 10952333) B10952333
theorem B4867703 : Blo 2161435 4867703 := bstep (se 1 (by rfl) ⟨3650777, by rfl⟩ : syracuseStep 4867703 = 7301555) B7301555
theorem B3245135 : Blo 2161435 3245135 := bstep (se 1 (by rfl) ⟨2433851, by rfl⟩ : syracuseStep 3245135 = 4867703) B4867703
theorem B2163423 : Blo 2161435 2163423 := bstep (se 1 (by rfl) ⟨1622567, by rfl⟩ : syracuseStep 2163423 = 3245135) B3245135
theorem B3245141 : Blo 2161435 3245141 := bbase (se 8 (by rfl) ⟨19014, by rfl⟩ : syracuseStep 3245141 = 38029) (by norm_num)
theorem B2163427 : Blo 2161435 2163427 := bstep (se 1 (by rfl) ⟨1622570, by rfl⟩ : syracuseStep 2163427 = 3245141) B3245141
theorem B8891477 : Blo 2161435 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B5927651 : Blo 2161435 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B3951767 : Blo 2161435 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B2634511 : Blo 2161435 2634511 := bstep (se 1 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 2634511 = 3951767) B3951767
theorem B3512681 : Blo 2161435 3512681 := bstep (se 2 (by rfl) ⟨1317255, by rfl⟩ : syracuseStep 3512681 = 2634511) B2634511
theorem B2341787 : Blo 2161435 2341787 := bstep (se 1 (by rfl) ⟨1756340, by rfl⟩ : syracuseStep 2341787 = 3512681) B3512681
theorem B6244765 : Blo 2161435 6244765 := bstep (se 3 (by rfl) ⟨1170893, by rfl⟩ : syracuseStep 6244765 = 2341787) B2341787
theorem B33305413 : Blo 2161435 33305413 := bstep (se 4 (by rfl) ⟨3122382, by rfl⟩ : syracuseStep 33305413 = 6244765) B6244765
theorem B44407217 : Blo 2161435 44407217 := bstep (se 2 (by rfl) ⟨16652706, by rfl⟩ : syracuseStep 44407217 = 33305413) B33305413
theorem B29604811 : Blo 2161435 29604811 := bstep (se 1 (by rfl) ⟨22203608, by rfl⟩ : syracuseStep 29604811 = 44407217) B44407217
theorem B39473081 : Blo 2161435 39473081 := bstep (se 2 (by rfl) ⟨14802405, by rfl⟩ : syracuseStep 39473081 = 29604811) B29604811
theorem B26315387 : Blo 2161435 26315387 := bstep (se 1 (by rfl) ⟨19736540, by rfl⟩ : syracuseStep 26315387 = 39473081) B39473081
theorem B17543591 : Blo 2161435 17543591 := bstep (se 1 (by rfl) ⟨13157693, by rfl⟩ : syracuseStep 17543591 = 26315387) B26315387
theorem B11695727 : Blo 2161435 11695727 := bstep (se 1 (by rfl) ⟨8771795, by rfl⟩ : syracuseStep 11695727 = 17543591) B17543591
theorem B7797151 : Blo 2161435 7797151 := bstep (se 1 (by rfl) ⟨5847863, by rfl⟩ : syracuseStep 7797151 = 11695727) B11695727
theorem B10396201 : Blo 2161435 10396201 := bstep (se 2 (by rfl) ⟨3898575, by rfl⟩ : syracuseStep 10396201 = 7797151) B7797151
theorem B13861601 : Blo 2161435 13861601 := bstep (se 2 (by rfl) ⟨5198100, by rfl⟩ : syracuseStep 13861601 = 10396201) B10396201
theorem B9241067 : Blo 2161435 9241067 := bstep (se 1 (by rfl) ⟨6930800, by rfl⟩ : syracuseStep 9241067 = 13861601) B13861601
theorem B6160711 : Blo 2161435 6160711 := bstep (se 1 (by rfl) ⟨4620533, by rfl⟩ : syracuseStep 6160711 = 9241067) B9241067
theorem B8214281 : Blo 2161435 8214281 := bstep (se 2 (by rfl) ⟨3080355, by rfl⟩ : syracuseStep 8214281 = 6160711) B6160711
theorem B5476187 : Blo 2161435 5476187 := bstep (se 1 (by rfl) ⟨4107140, by rfl⟩ : syracuseStep 5476187 = 8214281) B8214281
theorem B3650791 : Blo 2161435 3650791 := bstep (se 1 (by rfl) ⟨2738093, by rfl⟩ : syracuseStep 3650791 = 5476187) B5476187
theorem B4867721 : Blo 2161435 4867721 := bstep (se 2 (by rfl) ⟨1825395, by rfl⟩ : syracuseStep 4867721 = 3650791) B3650791
theorem B3245147 : Blo 2161435 3245147 := bstep (se 1 (by rfl) ⟨2433860, by rfl⟩ : syracuseStep 3245147 = 4867721) B4867721
theorem B2163431 : Blo 2161435 2163431 := bstep (se 1 (by rfl) ⟨1622573, by rfl⟩ : syracuseStep 2163431 = 3245147) B3245147
theorem B2433865 : Blo 2161435 2433865 := bbase (se 2 (by rfl) ⟨912699, by rfl⟩ : syracuseStep 2433865 = 1825399) (by norm_num)
theorem B3245153 : Blo 2161435 3245153 := bstep (se 2 (by rfl) ⟨1216932, by rfl⟩ : syracuseStep 3245153 = 2433865) B2433865
theorem B2163435 : Blo 2161435 2163435 := bstep (se 1 (by rfl) ⟨1622576, by rfl⟩ : syracuseStep 2163435 = 3245153) B3245153
theorem C0 (j : ℕ) (h1 : 540358 ≤ j) (h2 : j ≤ 540858) : Blo 2161435 (4 * j + 3) := by
  interval_cases j
  · exact B2161435
  · exact B2161439
  · exact B2161443
  · exact B2161447
  · exact B2161451
  · exact B2161455
  · exact B2161459
  · exact B2161463
  · exact B2161467
  · exact B2161471
  · exact B2161475
  · exact B2161479
  · exact B2161483
  · exact B2161487
  · exact B2161491
  · exact B2161495
  · exact B2161499
  · exact B2161503
  · exact B2161507
  · exact B2161511
  · exact B2161515
  · exact B2161519
  · exact B2161523
  · exact B2161527
  · exact B2161531
  · exact B2161535
  · exact B2161539
  · exact B2161543
  · exact B2161547
  · exact B2161551
  · exact B2161555
  · exact B2161559
  · exact B2161563
  · exact B2161567
  · exact B2161571
  · exact B2161575
  · exact B2161579
  · exact B2161583
  · exact B2161587
  · exact B2161591
  · exact B2161595
  · exact B2161599
  · exact B2161603
  · exact B2161607
  · exact B2161611
  · exact B2161615
  · exact B2161619
  · exact B2161623
  · exact B2161627
  · exact B2161631
  · exact B2161635
  · exact B2161639
  · exact B2161643
  · exact B2161647
  · exact B2161651
  · exact B2161655
  · exact B2161659
  · exact B2161663
  · exact B2161667
  · exact B2161671
  · exact B2161675
  · exact B2161679
  · exact B2161683
  · exact B2161687
  · exact B2161691
  · exact B2161695
  · exact B2161699
  · exact B2161703
  · exact B2161707
  · exact B2161711
  · exact B2161715
  · exact B2161719
  · exact B2161723
  · exact B2161727
  · exact B2161731
  · exact B2161735
  · exact B2161739
  · exact B2161743
  · exact B2161747
  · exact B2161751
  · exact B2161755
  · exact B2161759
  · exact B2161763
  · exact B2161767
  · exact B2161771
  · exact B2161775
  · exact B2161779
  · exact B2161783
  · exact B2161787
  · exact B2161791
  · exact B2161795
  · exact B2161799
  · exact B2161803
  · exact B2161807
  · exact B2161811
  · exact B2161815
  · exact B2161819
  · exact B2161823
  · exact B2161827
  · exact B2161831
  · exact B2161835
  · exact B2161839
  · exact B2161843
  · exact B2161847
  · exact B2161851
  · exact B2161855
  · exact B2161859
  · exact B2161863
  · exact B2161867
  · exact B2161871
  · exact B2161875
  · exact B2161879
  · exact B2161883
  · exact B2161887
  · exact B2161891
  · exact B2161895
  · exact B2161899
  · exact B2161903
  · exact B2161907
  · exact B2161911
  · exact B2161915
  · exact B2161919
  · exact B2161923
  · exact B2161927
  · exact B2161931
  · exact B2161935
  · exact B2161939
  · exact B2161943
  · exact B2161947
  · exact B2161951
  · exact B2161955
  · exact B2161959
  · exact B2161963
  · exact B2161967
  · exact B2161971
  · exact B2161975
  · exact B2161979
  · exact B2161983
  · exact B2161987
  · exact B2161991
  · exact B2161995
  · exact B2161999
  · exact B2162003
  · exact B2162007
  · exact B2162011
  · exact B2162015
  · exact B2162019
  · exact B2162023
  · exact B2162027
  · exact B2162031
  · exact B2162035
  · exact B2162039
  · exact B2162043
  · exact B2162047
  · exact B2162051
  · exact B2162055
  · exact B2162059
  · exact B2162063
  · exact B2162067
  · exact B2162071
  · exact B2162075
  · exact B2162079
  · exact B2162083
  · exact B2162087
  · exact B2162091
  · exact B2162095
  · exact B2162099
  · exact B2162103
  · exact B2162107
  · exact B2162111
  · exact B2162115
  · exact B2162119
  · exact B2162123
  · exact B2162127
  · exact B2162131
  · exact B2162135
  · exact B2162139
  · exact B2162143
  · exact B2162147
  · exact B2162151
  · exact B2162155
  · exact B2162159
  · exact B2162163
  · exact B2162167
  · exact B2162171
  · exact B2162175
  · exact B2162179
  · exact B2162183
  · exact B2162187
  · exact B2162191
  · exact B2162195
  · exact B2162199
  · exact B2162203
  · exact B2162207
  · exact B2162211
  · exact B2162215
  · exact B2162219
  · exact B2162223
  · exact B2162227
  · exact B2162231
  · exact B2162235
  · exact B2162239
  · exact B2162243
  · exact B2162247
  · exact B2162251
  · exact B2162255
  · exact B2162259
  · exact B2162263
  · exact B2162267
  · exact B2162271
  · exact B2162275
  · exact B2162279
  · exact B2162283
  · exact B2162287
  · exact B2162291
  · exact B2162295
  · exact B2162299
  · exact B2162303
  · exact B2162307
  · exact B2162311
  · exact B2162315
  · exact B2162319
  · exact B2162323
  · exact B2162327
  · exact B2162331
  · exact B2162335
  · exact B2162339
  · exact B2162343
  · exact B2162347
  · exact B2162351
  · exact B2162355
  · exact B2162359
  · exact B2162363
  · exact B2162367
  · exact B2162371
  · exact B2162375
  · exact B2162379
  · exact B2162383
  · exact B2162387
  · exact B2162391
  · exact B2162395
  · exact B2162399
  · exact B2162403
  · exact B2162407
  · exact B2162411
  · exact B2162415
  · exact B2162419
  · exact B2162423
  · exact B2162427
  · exact B2162431
  · exact B2162435
  · exact B2162439
  · exact B2162443
  · exact B2162447
  · exact B2162451
  · exact B2162455
  · exact B2162459
  · exact B2162463
  · exact B2162467
  · exact B2162471
  · exact B2162475
  · exact B2162479
  · exact B2162483
  · exact B2162487
  · exact B2162491
  · exact B2162495
  · exact B2162499
  · exact B2162503
  · exact B2162507
  · exact B2162511
  · exact B2162515
  · exact B2162519
  · exact B2162523
  · exact B2162527
  · exact B2162531
  · exact B2162535
  · exact B2162539
  · exact B2162543
  · exact B2162547
  · exact B2162551
  · exact B2162555
  · exact B2162559
  · exact B2162563
  · exact B2162567
  · exact B2162571
  · exact B2162575
  · exact B2162579
  · exact B2162583
  · exact B2162587
  · exact B2162591
  · exact B2162595
  · exact B2162599
  · exact B2162603
  · exact B2162607
  · exact B2162611
  · exact B2162615
  · exact B2162619
  · exact B2162623
  · exact B2162627
  · exact B2162631
  · exact B2162635
  · exact B2162639
  · exact B2162643
  · exact B2162647
  · exact B2162651
  · exact B2162655
  · exact B2162659
  · exact B2162663
  · exact B2162667
  · exact B2162671
  · exact B2162675
  · exact B2162679
  · exact B2162683
  · exact B2162687
  · exact B2162691
  · exact B2162695
  · exact B2162699
  · exact B2162703
  · exact B2162707
  · exact B2162711
  · exact B2162715
  · exact B2162719
  · exact B2162723
  · exact B2162727
  · exact B2162731
  · exact B2162735
  · exact B2162739
  · exact B2162743
  · exact B2162747
  · exact B2162751
  · exact B2162755
  · exact B2162759
  · exact B2162763
  · exact B2162767
  · exact B2162771
  · exact B2162775
  · exact B2162779
  · exact B2162783
  · exact B2162787
  · exact B2162791
  · exact B2162795
  · exact B2162799
  · exact B2162803
  · exact B2162807
  · exact B2162811
  · exact B2162815
  · exact B2162819
  · exact B2162823
  · exact B2162827
  · exact B2162831
  · exact B2162835
  · exact B2162839
  · exact B2162843
  · exact B2162847
  · exact B2162851
  · exact B2162855
  · exact B2162859
  · exact B2162863
  · exact B2162867
  · exact B2162871
  · exact B2162875
  · exact B2162879
  · exact B2162883
  · exact B2162887
  · exact B2162891
  · exact B2162895
  · exact B2162899
  · exact B2162903
  · exact B2162907
  · exact B2162911
  · exact B2162915
  · exact B2162919
  · exact B2162923
  · exact B2162927
  · exact B2162931
  · exact B2162935
  · exact B2162939
  · exact B2162943
  · exact B2162947
  · exact B2162951
  · exact B2162955
  · exact B2162959
  · exact B2162963
  · exact B2162967
  · exact B2162971
  · exact B2162975
  · exact B2162979
  · exact B2162983
  · exact B2162987
  · exact B2162991
  · exact B2162995
  · exact B2162999
  · exact B2163003
  · exact B2163007
  · exact B2163011
  · exact B2163015
  · exact B2163019
  · exact B2163023
  · exact B2163027
  · exact B2163031
  · exact B2163035
  · exact B2163039
  · exact B2163043
  · exact B2163047
  · exact B2163051
  · exact B2163055
  · exact B2163059
  · exact B2163063
  · exact B2163067
  · exact B2163071
  · exact B2163075
  · exact B2163079
  · exact B2163083
  · exact B2163087
  · exact B2163091
  · exact B2163095
  · exact B2163099
  · exact B2163103
  · exact B2163107
  · exact B2163111
  · exact B2163115
  · exact B2163119
  · exact B2163123
  · exact B2163127
  · exact B2163131
  · exact B2163135
  · exact B2163139
  · exact B2163143
  · exact B2163147
  · exact B2163151
  · exact B2163155
  · exact B2163159
  · exact B2163163
  · exact B2163167
  · exact B2163171
  · exact B2163175
  · exact B2163179
  · exact B2163183
  · exact B2163187
  · exact B2163191
  · exact B2163195
  · exact B2163199
  · exact B2163203
  · exact B2163207
  · exact B2163211
  · exact B2163215
  · exact B2163219
  · exact B2163223
  · exact B2163227
  · exact B2163231
  · exact B2163235
  · exact B2163239
  · exact B2163243
  · exact B2163247
  · exact B2163251
  · exact B2163255
  · exact B2163259
  · exact B2163263
  · exact B2163267
  · exact B2163271
  · exact B2163275
  · exact B2163279
  · exact B2163283
  · exact B2163287
  · exact B2163291
  · exact B2163295
  · exact B2163299
  · exact B2163303
  · exact B2163307
  · exact B2163311
  · exact B2163315
  · exact B2163319
  · exact B2163323
  · exact B2163327
  · exact B2163331
  · exact B2163335
  · exact B2163339
  · exact B2163343
  · exact B2163347
  · exact B2163351
  · exact B2163355
  · exact B2163359
  · exact B2163363
  · exact B2163367
  · exact B2163371
  · exact B2163375
  · exact B2163379
  · exact B2163383
  · exact B2163387
  · exact B2163391
  · exact B2163395
  · exact B2163399
  · exact B2163403
  · exact B2163407
  · exact B2163411
  · exact B2163415
  · exact B2163419
  · exact B2163423
  · exact B2163427
  · exact B2163431
  · exact B2163435
theorem solution (m : ℕ) (hlo : 2161435 ≤ m) (hhi : m ≤ 2163435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 540358 ≤ j := by omega
    have hj2 : j ≤ 540858 := by omega
    have hb : Blo 2161435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
