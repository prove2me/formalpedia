-- Prove2me | solution 1 for syracuse_descends_range_2265435_2267435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:22.423437+00:00
-- url     : https://prove2.me/submissions/40a797da-349b-4dc3-bc51-8f44563a5563

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

theorem B4300789 : Blo 2265435 4300789 := bbase (se 5 (by rfl) ⟨201599, by rfl⟩ : syracuseStep 4300789 = 403199) (by norm_num)
theorem B5734385 : Blo 2265435 5734385 := bstep (se 2 (by rfl) ⟨2150394, by rfl⟩ : syracuseStep 5734385 = 4300789) B4300789
theorem B3822923 : Blo 2265435 3822923 := bstep (se 1 (by rfl) ⟨2867192, by rfl⟩ : syracuseStep 3822923 = 5734385) B5734385
theorem B2548615 : Blo 2265435 2548615 := bstep (se 1 (by rfl) ⟨1911461, by rfl⟩ : syracuseStep 2548615 = 3822923) B3822923
theorem B3398153 : Blo 2265435 3398153 := bstep (se 2 (by rfl) ⟨1274307, by rfl⟩ : syracuseStep 3398153 = 2548615) B2548615
theorem B2265435 : Blo 2265435 2265435 := bstep (se 1 (by rfl) ⟨1699076, by rfl⟩ : syracuseStep 2265435 = 3398153) B3398153
theorem B11468789 : Blo 2265435 11468789 := bbase (se 5 (by rfl) ⟨537599, by rfl⟩ : syracuseStep 11468789 = 1075199) (by norm_num)
theorem B7645859 : Blo 2265435 7645859 := bstep (se 1 (by rfl) ⟨5734394, by rfl⟩ : syracuseStep 7645859 = 11468789) B11468789
theorem B5097239 : Blo 2265435 5097239 := bstep (se 1 (by rfl) ⟨3822929, by rfl⟩ : syracuseStep 5097239 = 7645859) B7645859
theorem B3398159 : Blo 2265435 3398159 := bstep (se 1 (by rfl) ⟨2548619, by rfl⟩ : syracuseStep 3398159 = 5097239) B5097239
theorem B2265439 : Blo 2265435 2265439 := bstep (se 1 (by rfl) ⟨1699079, by rfl⟩ : syracuseStep 2265439 = 3398159) B3398159
theorem B3398165 : Blo 2265435 3398165 := bbase (se 6 (by rfl) ⟨79644, by rfl⟩ : syracuseStep 3398165 = 159289) (by norm_num)
theorem B2265443 : Blo 2265435 2265443 := bstep (se 1 (by rfl) ⟨1699082, by rfl⟩ : syracuseStep 2265443 = 3398165) B3398165
theorem B19353653 : Blo 2265435 19353653 := bbase (se 5 (by rfl) ⟨907202, by rfl⟩ : syracuseStep 19353653 = 1814405) (by norm_num)
theorem B12902435 : Blo 2265435 12902435 := bstep (se 1 (by rfl) ⟨9676826, by rfl⟩ : syracuseStep 12902435 = 19353653) B19353653
theorem B8601623 : Blo 2265435 8601623 := bstep (se 1 (by rfl) ⟨6451217, by rfl⟩ : syracuseStep 8601623 = 12902435) B12902435
theorem B5734415 : Blo 2265435 5734415 := bstep (se 1 (by rfl) ⟨4300811, by rfl⟩ : syracuseStep 5734415 = 8601623) B8601623
theorem B3822943 : Blo 2265435 3822943 := bstep (se 1 (by rfl) ⟨2867207, by rfl⟩ : syracuseStep 3822943 = 5734415) B5734415
theorem B5097257 : Blo 2265435 5097257 := bstep (se 2 (by rfl) ⟨1911471, by rfl⟩ : syracuseStep 5097257 = 3822943) B3822943
theorem B3398171 : Blo 2265435 3398171 := bstep (se 1 (by rfl) ⟨2548628, by rfl⟩ : syracuseStep 3398171 = 5097257) B5097257
theorem B2265447 : Blo 2265435 2265447 := bstep (se 1 (by rfl) ⟨1699085, by rfl⟩ : syracuseStep 2265447 = 3398171) B3398171
theorem B2548633 : Blo 2265435 2548633 := bbase (se 2 (by rfl) ⟨955737, by rfl⟩ : syracuseStep 2548633 = 1911475) (by norm_num)
theorem B3398177 : Blo 2265435 3398177 := bstep (se 2 (by rfl) ⟨1274316, by rfl⟩ : syracuseStep 3398177 = 2548633) B2548633
theorem B2265451 : Blo 2265435 2265451 := bstep (se 1 (by rfl) ⟨1699088, by rfl⟩ : syracuseStep 2265451 = 3398177) B3398177
theorem B8601653 : Blo 2265435 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B5734435 : Blo 2265435 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B7645913 : Blo 2265435 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B5097275 : Blo 2265435 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B3398183 : Blo 2265435 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B2265455 : Blo 2265435 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B3398189 : Blo 2265435 3398189 := bbase (se 3 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 3398189 = 1274321) (by norm_num)
theorem B2265459 : Blo 2265435 2265459 := bstep (se 1 (by rfl) ⟨1699094, by rfl⟩ : syracuseStep 2265459 = 3398189) B3398189
theorem B5097293 : Blo 2265435 5097293 := bbase (se 3 (by rfl) ⟨955742, by rfl⟩ : syracuseStep 5097293 = 1911485) (by norm_num)
theorem B3398195 : Blo 2265435 3398195 := bstep (se 1 (by rfl) ⟨2548646, by rfl⟩ : syracuseStep 3398195 = 5097293) B5097293
theorem B2265463 : Blo 2265435 2265463 := bstep (se 1 (by rfl) ⟨1699097, by rfl⟩ : syracuseStep 2265463 = 3398195) B3398195
theorem B2867233 : Blo 2265435 2867233 := bbase (se 2 (by rfl) ⟨1075212, by rfl⟩ : syracuseStep 2867233 = 2150425) (by norm_num)
theorem B3822977 : Blo 2265435 3822977 := bstep (se 2 (by rfl) ⟨1433616, by rfl⟩ : syracuseStep 3822977 = 2867233) B2867233
theorem B2548651 : Blo 2265435 2548651 := bstep (se 1 (by rfl) ⟨1911488, by rfl⟩ : syracuseStep 2548651 = 3822977) B3822977
theorem B3398201 : Blo 2265435 3398201 := bstep (se 2 (by rfl) ⟨1274325, by rfl⟩ : syracuseStep 3398201 = 2548651) B2548651
theorem B2265467 : Blo 2265435 2265467 := bstep (se 1 (by rfl) ⟨1699100, by rfl⟩ : syracuseStep 2265467 = 3398201) B3398201
theorem B25805141 : Blo 2265435 25805141 := bbase (se 10 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 25805141 = 75601) (by norm_num)
theorem B17203427 : Blo 2265435 17203427 := bstep (se 1 (by rfl) ⟨12902570, by rfl⟩ : syracuseStep 17203427 = 25805141) B25805141
theorem B11468951 : Blo 2265435 11468951 := bstep (se 1 (by rfl) ⟨8601713, by rfl⟩ : syracuseStep 11468951 = 17203427) B17203427
theorem B7645967 : Blo 2265435 7645967 := bstep (se 1 (by rfl) ⟨5734475, by rfl⟩ : syracuseStep 7645967 = 11468951) B11468951
theorem B5097311 : Blo 2265435 5097311 := bstep (se 1 (by rfl) ⟨3822983, by rfl⟩ : syracuseStep 5097311 = 7645967) B7645967
theorem B3398207 : Blo 2265435 3398207 := bstep (se 1 (by rfl) ⟨2548655, by rfl⟩ : syracuseStep 3398207 = 5097311) B5097311
theorem B2265471 : Blo 2265435 2265471 := bstep (se 1 (by rfl) ⟨1699103, by rfl⟩ : syracuseStep 2265471 = 3398207) B3398207
theorem B3398213 : Blo 2265435 3398213 := bbase (se 4 (by rfl) ⟨318582, by rfl⟩ : syracuseStep 3398213 = 637165) (by norm_num)
theorem B2265475 : Blo 2265435 2265475 := bstep (se 1 (by rfl) ⟨1699106, by rfl⟩ : syracuseStep 2265475 = 3398213) B3398213
theorem B3822997 : Blo 2265435 3822997 := bbase (se 6 (by rfl) ⟨89601, by rfl⟩ : syracuseStep 3822997 = 179203) (by norm_num)
theorem B5097329 : Blo 2265435 5097329 := bstep (se 2 (by rfl) ⟨1911498, by rfl⟩ : syracuseStep 5097329 = 3822997) B3822997
theorem B3398219 : Blo 2265435 3398219 := bstep (se 1 (by rfl) ⟨2548664, by rfl⟩ : syracuseStep 3398219 = 5097329) B5097329
theorem B2265479 : Blo 2265435 2265479 := bstep (se 1 (by rfl) ⟨1699109, by rfl⟩ : syracuseStep 2265479 = 3398219) B3398219
theorem B2548669 : Blo 2265435 2548669 := bbase (se 3 (by rfl) ⟨477875, by rfl⟩ : syracuseStep 2548669 = 955751) (by norm_num)
theorem B3398225 : Blo 2265435 3398225 := bstep (se 2 (by rfl) ⟨1274334, by rfl⟩ : syracuseStep 3398225 = 2548669) B2548669
theorem B2265483 : Blo 2265435 2265483 := bstep (se 1 (by rfl) ⟨1699112, by rfl⟩ : syracuseStep 2265483 = 3398225) B3398225
theorem B7646021 : Blo 2265435 7646021 := bbase (se 4 (by rfl) ⟨716814, by rfl⟩ : syracuseStep 7646021 = 1433629) (by norm_num)
theorem B5097347 : Blo 2265435 5097347 := bstep (se 1 (by rfl) ⟨3823010, by rfl⟩ : syracuseStep 5097347 = 7646021) B7646021
theorem B3398231 : Blo 2265435 3398231 := bstep (se 1 (by rfl) ⟨2548673, by rfl⟩ : syracuseStep 3398231 = 5097347) B5097347
theorem B2265487 : Blo 2265435 2265487 := bstep (se 1 (by rfl) ⟨1699115, by rfl⟩ : syracuseStep 2265487 = 3398231) B3398231
theorem B3398237 : Blo 2265435 3398237 := bbase (se 3 (by rfl) ⟨637169, by rfl⟩ : syracuseStep 3398237 = 1274339) (by norm_num)
theorem B2265491 : Blo 2265435 2265491 := bstep (se 1 (by rfl) ⟨1699118, by rfl⟩ : syracuseStep 2265491 = 3398237) B3398237
theorem B5097365 : Blo 2265435 5097365 := bbase (se 6 (by rfl) ⟨119469, by rfl⟩ : syracuseStep 5097365 = 238939) (by norm_num)
theorem B3398243 : Blo 2265435 3398243 := bstep (se 1 (by rfl) ⟨2548682, by rfl⟩ : syracuseStep 3398243 = 5097365) B5097365
theorem B2265495 : Blo 2265435 2265495 := bstep (se 1 (by rfl) ⟨1699121, by rfl⟩ : syracuseStep 2265495 = 3398243) B3398243
theorem B4838525 : Blo 2265435 4838525 := bbase (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) (by norm_num)
theorem B3225683 : Blo 2265435 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B8601821 : Blo 2265435 8601821 := bstep (se 3 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 8601821 = 3225683) B3225683
theorem B5734547 : Blo 2265435 5734547 := bstep (se 1 (by rfl) ⟨4300910, by rfl⟩ : syracuseStep 5734547 = 8601821) B8601821
theorem B3823031 : Blo 2265435 3823031 := bstep (se 1 (by rfl) ⟨2867273, by rfl⟩ : syracuseStep 3823031 = 5734547) B5734547
theorem B2548687 : Blo 2265435 2548687 := bstep (se 1 (by rfl) ⟨1911515, by rfl⟩ : syracuseStep 2548687 = 3823031) B3823031
theorem B3398249 : Blo 2265435 3398249 := bstep (se 2 (by rfl) ⟨1274343, by rfl⟩ : syracuseStep 3398249 = 2548687) B2548687
theorem B2265499 : Blo 2265435 2265499 := bstep (se 1 (by rfl) ⟨1699124, by rfl⟩ : syracuseStep 2265499 = 3398249) B3398249
theorem B9185653 : Blo 2265435 9185653 := bbase (se 5 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 9185653 = 861155) (by norm_num)
theorem B12247537 : Blo 2265435 12247537 := bstep (se 2 (by rfl) ⟨4592826, by rfl⟩ : syracuseStep 12247537 = 9185653) B9185653
theorem B16330049 : Blo 2265435 16330049 := bstep (se 2 (by rfl) ⟨6123768, by rfl⟩ : syracuseStep 16330049 = 12247537) B12247537
theorem B10886699 : Blo 2265435 10886699 := bstep (se 1 (by rfl) ⟨8165024, by rfl⟩ : syracuseStep 10886699 = 16330049) B16330049
theorem B7257799 : Blo 2265435 7257799 := bstep (se 1 (by rfl) ⟨5443349, by rfl⟩ : syracuseStep 7257799 = 10886699) B10886699
theorem B9677065 : Blo 2265435 9677065 := bstep (se 2 (by rfl) ⟨3628899, by rfl⟩ : syracuseStep 9677065 = 7257799) B7257799
theorem B12902753 : Blo 2265435 12902753 := bstep (se 2 (by rfl) ⟨4838532, by rfl⟩ : syracuseStep 12902753 = 9677065) B9677065
theorem B8601835 : Blo 2265435 8601835 := bstep (se 1 (by rfl) ⟨6451376, by rfl⟩ : syracuseStep 8601835 = 12902753) B12902753
theorem B11469113 : Blo 2265435 11469113 := bstep (se 2 (by rfl) ⟨4300917, by rfl⟩ : syracuseStep 11469113 = 8601835) B8601835
theorem B7646075 : Blo 2265435 7646075 := bstep (se 1 (by rfl) ⟨5734556, by rfl⟩ : syracuseStep 7646075 = 11469113) B11469113
theorem B5097383 : Blo 2265435 5097383 := bstep (se 1 (by rfl) ⟨3823037, by rfl⟩ : syracuseStep 5097383 = 7646075) B7646075
theorem B3398255 : Blo 2265435 3398255 := bstep (se 1 (by rfl) ⟨2548691, by rfl⟩ : syracuseStep 3398255 = 5097383) B5097383
theorem B2265503 : Blo 2265435 2265503 := bstep (se 1 (by rfl) ⟨1699127, by rfl⟩ : syracuseStep 2265503 = 3398255) B3398255
theorem B3398261 : Blo 2265435 3398261 := bbase (se 5 (by rfl) ⟨159293, by rfl⟩ : syracuseStep 3398261 = 318587) (by norm_num)
theorem B2265507 : Blo 2265435 2265507 := bstep (se 1 (by rfl) ⟨1699130, by rfl⟩ : syracuseStep 2265507 = 3398261) B3398261
theorem B4300933 : Blo 2265435 4300933 := bbase (se 4 (by rfl) ⟨403212, by rfl⟩ : syracuseStep 4300933 = 806425) (by norm_num)
theorem B5734577 : Blo 2265435 5734577 := bstep (se 2 (by rfl) ⟨2150466, by rfl⟩ : syracuseStep 5734577 = 4300933) B4300933
theorem B3823051 : Blo 2265435 3823051 := bstep (se 1 (by rfl) ⟨2867288, by rfl⟩ : syracuseStep 3823051 = 5734577) B5734577
theorem B5097401 : Blo 2265435 5097401 := bstep (se 2 (by rfl) ⟨1911525, by rfl⟩ : syracuseStep 5097401 = 3823051) B3823051
theorem B3398267 : Blo 2265435 3398267 := bstep (se 1 (by rfl) ⟨2548700, by rfl⟩ : syracuseStep 3398267 = 5097401) B5097401
theorem B2265511 : Blo 2265435 2265511 := bstep (se 1 (by rfl) ⟨1699133, by rfl⟩ : syracuseStep 2265511 = 3398267) B3398267
theorem B2548705 : Blo 2265435 2548705 := bbase (se 2 (by rfl) ⟨955764, by rfl⟩ : syracuseStep 2548705 = 1911529) (by norm_num)
theorem B3398273 : Blo 2265435 3398273 := bstep (se 2 (by rfl) ⟨1274352, by rfl⟩ : syracuseStep 3398273 = 2548705) B2548705
theorem B2265515 : Blo 2265435 2265515 := bstep (se 1 (by rfl) ⟨1699136, by rfl⟩ : syracuseStep 2265515 = 3398273) B3398273
theorem B5734597 : Blo 2265435 5734597 := bbase (se 4 (by rfl) ⟨537618, by rfl⟩ : syracuseStep 5734597 = 1075237) (by norm_num)
theorem B7646129 : Blo 2265435 7646129 := bstep (se 2 (by rfl) ⟨2867298, by rfl⟩ : syracuseStep 7646129 = 5734597) B5734597
theorem B5097419 : Blo 2265435 5097419 := bstep (se 1 (by rfl) ⟨3823064, by rfl⟩ : syracuseStep 5097419 = 7646129) B7646129
theorem B3398279 : Blo 2265435 3398279 := bstep (se 1 (by rfl) ⟨2548709, by rfl⟩ : syracuseStep 3398279 = 5097419) B5097419
theorem B2265519 : Blo 2265435 2265519 := bstep (se 1 (by rfl) ⟨1699139, by rfl⟩ : syracuseStep 2265519 = 3398279) B3398279
theorem B3398285 : Blo 2265435 3398285 := bbase (se 3 (by rfl) ⟨637178, by rfl⟩ : syracuseStep 3398285 = 1274357) (by norm_num)
theorem B2265523 : Blo 2265435 2265523 := bstep (se 1 (by rfl) ⟨1699142, by rfl⟩ : syracuseStep 2265523 = 3398285) B3398285
theorem B5097437 : Blo 2265435 5097437 := bbase (se 3 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 5097437 = 1911539) (by norm_num)
theorem B3398291 : Blo 2265435 3398291 := bstep (se 1 (by rfl) ⟨2548718, by rfl⟩ : syracuseStep 3398291 = 5097437) B5097437
theorem B2265527 : Blo 2265435 2265527 := bstep (se 1 (by rfl) ⟨1699145, by rfl⟩ : syracuseStep 2265527 = 3398291) B3398291
theorem B3823085 : Blo 2265435 3823085 := bbase (se 3 (by rfl) ⟨716828, by rfl⟩ : syracuseStep 3823085 = 1433657) (by norm_num)
theorem B2548723 : Blo 2265435 2548723 := bstep (se 1 (by rfl) ⟨1911542, by rfl⟩ : syracuseStep 2548723 = 3823085) B3823085
theorem B3398297 : Blo 2265435 3398297 := bstep (se 2 (by rfl) ⟨1274361, by rfl⟩ : syracuseStep 3398297 = 2548723) B2548723
theorem B2265531 : Blo 2265435 2265531 := bstep (se 1 (by rfl) ⟨1699148, by rfl⟩ : syracuseStep 2265531 = 3398297) B3398297
theorem B2721713 : Blo 2265435 2721713 := bbase (se 2 (by rfl) ⟨1020642, by rfl⟩ : syracuseStep 2721713 = 2041285) (by norm_num)
theorem B29031605 : Blo 2265435 29031605 := bstep (se 5 (by rfl) ⟨1360856, by rfl⟩ : syracuseStep 29031605 = 2721713) B2721713
theorem B19354403 : Blo 2265435 19354403 := bstep (se 1 (by rfl) ⟨14515802, by rfl⟩ : syracuseStep 19354403 = 29031605) B29031605
theorem B12902935 : Blo 2265435 12902935 := bstep (se 1 (by rfl) ⟨9677201, by rfl⟩ : syracuseStep 12902935 = 19354403) B19354403
theorem B17203913 : Blo 2265435 17203913 := bstep (se 2 (by rfl) ⟨6451467, by rfl⟩ : syracuseStep 17203913 = 12902935) B12902935
theorem B11469275 : Blo 2265435 11469275 := bstep (se 1 (by rfl) ⟨8601956, by rfl⟩ : syracuseStep 11469275 = 17203913) B17203913
theorem B7646183 : Blo 2265435 7646183 := bstep (se 1 (by rfl) ⟨5734637, by rfl⟩ : syracuseStep 7646183 = 11469275) B11469275
theorem B5097455 : Blo 2265435 5097455 := bstep (se 1 (by rfl) ⟨3823091, by rfl⟩ : syracuseStep 5097455 = 7646183) B7646183
theorem B3398303 : Blo 2265435 3398303 := bstep (se 1 (by rfl) ⟨2548727, by rfl⟩ : syracuseStep 3398303 = 5097455) B5097455
theorem B2265535 : Blo 2265435 2265535 := bstep (se 1 (by rfl) ⟨1699151, by rfl⟩ : syracuseStep 2265535 = 3398303) B3398303
theorem B3398309 : Blo 2265435 3398309 := bbase (se 4 (by rfl) ⟨318591, by rfl⟩ : syracuseStep 3398309 = 637183) (by norm_num)
theorem B2265539 : Blo 2265435 2265539 := bstep (se 1 (by rfl) ⟨1699154, by rfl⟩ : syracuseStep 2265539 = 3398309) B3398309
theorem B2867329 : Blo 2265435 2867329 := bbase (se 2 (by rfl) ⟨1075248, by rfl⟩ : syracuseStep 2867329 = 2150497) (by norm_num)
theorem B3823105 : Blo 2265435 3823105 := bstep (se 2 (by rfl) ⟨1433664, by rfl⟩ : syracuseStep 3823105 = 2867329) B2867329
theorem B5097473 : Blo 2265435 5097473 := bstep (se 2 (by rfl) ⟨1911552, by rfl⟩ : syracuseStep 5097473 = 3823105) B3823105
theorem B3398315 : Blo 2265435 3398315 := bstep (se 1 (by rfl) ⟨2548736, by rfl⟩ : syracuseStep 3398315 = 5097473) B5097473
theorem B2265543 : Blo 2265435 2265543 := bstep (se 1 (by rfl) ⟨1699157, by rfl⟩ : syracuseStep 2265543 = 3398315) B3398315
theorem B2548741 : Blo 2265435 2548741 := bbase (se 4 (by rfl) ⟨238944, by rfl⟩ : syracuseStep 2548741 = 477889) (by norm_num)
theorem B3398321 : Blo 2265435 3398321 := bstep (se 2 (by rfl) ⟨1274370, by rfl⟩ : syracuseStep 3398321 = 2548741) B2548741
theorem B2265547 : Blo 2265435 2265547 := bstep (se 1 (by rfl) ⟨1699160, by rfl⟩ : syracuseStep 2265547 = 3398321) B3398321
theorem B3225757 : Blo 2265435 3225757 := bbase (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) (by norm_num)
theorem B4301009 : Blo 2265435 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2867339 : Blo 2265435 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B7646237 : Blo 2265435 7646237 := bstep (se 3 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 7646237 = 2867339) B2867339
theorem B5097491 : Blo 2265435 5097491 := bstep (se 1 (by rfl) ⟨3823118, by rfl⟩ : syracuseStep 5097491 = 7646237) B7646237
theorem B3398327 : Blo 2265435 3398327 := bstep (se 1 (by rfl) ⟨2548745, by rfl⟩ : syracuseStep 3398327 = 5097491) B5097491
theorem B2265551 : Blo 2265435 2265551 := bstep (se 1 (by rfl) ⟨1699163, by rfl⟩ : syracuseStep 2265551 = 3398327) B3398327
theorem B3398333 : Blo 2265435 3398333 := bbase (se 3 (by rfl) ⟨637187, by rfl⟩ : syracuseStep 3398333 = 1274375) (by norm_num)
theorem B2265555 : Blo 2265435 2265555 := bstep (se 1 (by rfl) ⟨1699166, by rfl⟩ : syracuseStep 2265555 = 3398333) B3398333
theorem B5097509 : Blo 2265435 5097509 := bbase (se 4 (by rfl) ⟨477891, by rfl⟩ : syracuseStep 5097509 = 955783) (by norm_num)
theorem B3398339 : Blo 2265435 3398339 := bstep (se 1 (by rfl) ⟨2548754, by rfl⟩ : syracuseStep 3398339 = 5097509) B5097509
theorem B2265559 : Blo 2265435 2265559 := bstep (se 1 (by rfl) ⟨1699169, by rfl⟩ : syracuseStep 2265559 = 3398339) B3398339
theorem B5734709 : Blo 2265435 5734709 := bbase (se 5 (by rfl) ⟨268814, by rfl⟩ : syracuseStep 5734709 = 537629) (by norm_num)
theorem B3823139 : Blo 2265435 3823139 := bstep (se 1 (by rfl) ⟨2867354, by rfl⟩ : syracuseStep 3823139 = 5734709) B5734709
theorem B2548759 : Blo 2265435 2548759 := bstep (se 1 (by rfl) ⟨1911569, by rfl⟩ : syracuseStep 2548759 = 3823139) B3823139
theorem B3398345 : Blo 2265435 3398345 := bstep (se 2 (by rfl) ⟨1274379, by rfl⟩ : syracuseStep 3398345 = 2548759) B2548759
theorem B2265563 : Blo 2265435 2265563 := bstep (se 1 (by rfl) ⟨1699172, by rfl⟩ : syracuseStep 2265563 = 3398345) B3398345
theorem B55115477 : Blo 2265435 55115477 := bbase (se 7 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 55115477 = 1291769) (by norm_num)
theorem B36743651 : Blo 2265435 36743651 := bstep (se 1 (by rfl) ⟨27557738, by rfl⟩ : syracuseStep 36743651 = 55115477) B55115477
theorem B24495767 : Blo 2265435 24495767 := bstep (se 1 (by rfl) ⟨18371825, by rfl⟩ : syracuseStep 24495767 = 36743651) B36743651
theorem B16330511 : Blo 2265435 16330511 := bstep (se 1 (by rfl) ⟨12247883, by rfl⟩ : syracuseStep 16330511 = 24495767) B24495767
theorem B10887007 : Blo 2265435 10887007 := bstep (se 1 (by rfl) ⟨8165255, by rfl⟩ : syracuseStep 10887007 = 16330511) B16330511
theorem B14516009 : Blo 2265435 14516009 := bstep (se 2 (by rfl) ⟨5443503, by rfl⟩ : syracuseStep 14516009 = 10887007) B10887007
theorem B9677339 : Blo 2265435 9677339 := bstep (se 1 (by rfl) ⟨7258004, by rfl⟩ : syracuseStep 9677339 = 14516009) B14516009
theorem B6451559 : Blo 2265435 6451559 := bstep (se 1 (by rfl) ⟨4838669, by rfl⟩ : syracuseStep 6451559 = 9677339) B9677339
theorem B4301039 : Blo 2265435 4301039 := bstep (se 1 (by rfl) ⟨3225779, by rfl⟩ : syracuseStep 4301039 = 6451559) B6451559
theorem B11469437 : Blo 2265435 11469437 := bstep (se 3 (by rfl) ⟨2150519, by rfl⟩ : syracuseStep 11469437 = 4301039) B4301039
theorem B7646291 : Blo 2265435 7646291 := bstep (se 1 (by rfl) ⟨5734718, by rfl⟩ : syracuseStep 7646291 = 11469437) B11469437
theorem B5097527 : Blo 2265435 5097527 := bstep (se 1 (by rfl) ⟨3823145, by rfl⟩ : syracuseStep 5097527 = 7646291) B7646291
theorem B3398351 : Blo 2265435 3398351 := bstep (se 1 (by rfl) ⟨2548763, by rfl⟩ : syracuseStep 3398351 = 5097527) B5097527
theorem B2265567 : Blo 2265435 2265567 := bstep (se 1 (by rfl) ⟨1699175, by rfl⟩ : syracuseStep 2265567 = 3398351) B3398351
theorem B3398357 : Blo 2265435 3398357 := bbase (se 7 (by rfl) ⟨39824, by rfl⟩ : syracuseStep 3398357 = 79649) (by norm_num)
theorem B2265571 : Blo 2265435 2265571 := bstep (se 1 (by rfl) ⟨1699178, by rfl⟩ : syracuseStep 2265571 = 3398357) B3398357
theorem B18371893 : Blo 2265435 18371893 := bbase (se 5 (by rfl) ⟨861182, by rfl⟩ : syracuseStep 18371893 = 1722365) (by norm_num)
theorem B24495857 : Blo 2265435 24495857 := bstep (se 2 (by rfl) ⟨9185946, by rfl⟩ : syracuseStep 24495857 = 18371893) B18371893
theorem B16330571 : Blo 2265435 16330571 := bstep (se 1 (by rfl) ⟨12247928, by rfl⟩ : syracuseStep 16330571 = 24495857) B24495857
theorem B10887047 : Blo 2265435 10887047 := bstep (se 1 (by rfl) ⟨8165285, by rfl⟩ : syracuseStep 10887047 = 16330571) B16330571
theorem B7258031 : Blo 2265435 7258031 := bstep (se 1 (by rfl) ⟨5443523, by rfl⟩ : syracuseStep 7258031 = 10887047) B10887047
theorem B4838687 : Blo 2265435 4838687 := bstep (se 1 (by rfl) ⟨3629015, by rfl⟩ : syracuseStep 4838687 = 7258031) B7258031
theorem B3225791 : Blo 2265435 3225791 := bstep (se 1 (by rfl) ⟨2419343, by rfl⟩ : syracuseStep 3225791 = 4838687) B4838687
theorem B8602109 : Blo 2265435 8602109 := bstep (se 3 (by rfl) ⟨1612895, by rfl⟩ : syracuseStep 8602109 = 3225791) B3225791
theorem B5734739 : Blo 2265435 5734739 := bstep (se 1 (by rfl) ⟨4301054, by rfl⟩ : syracuseStep 5734739 = 8602109) B8602109
theorem B3823159 : Blo 2265435 3823159 := bstep (se 1 (by rfl) ⟨2867369, by rfl⟩ : syracuseStep 3823159 = 5734739) B5734739
theorem B5097545 : Blo 2265435 5097545 := bstep (se 2 (by rfl) ⟨1911579, by rfl⟩ : syracuseStep 5097545 = 3823159) B3823159
theorem B3398363 : Blo 2265435 3398363 := bstep (se 1 (by rfl) ⟨2548772, by rfl⟩ : syracuseStep 3398363 = 5097545) B5097545
theorem B2265575 : Blo 2265435 2265575 := bstep (se 1 (by rfl) ⟨1699181, by rfl⟩ : syracuseStep 2265575 = 3398363) B3398363
theorem B2548777 : Blo 2265435 2548777 := bbase (se 2 (by rfl) ⟨955791, by rfl⟩ : syracuseStep 2548777 = 1911583) (by norm_num)
theorem B3398369 : Blo 2265435 3398369 := bstep (se 2 (by rfl) ⟨1274388, by rfl⟩ : syracuseStep 3398369 = 2548777) B2548777
theorem B2265579 : Blo 2265435 2265579 := bstep (se 1 (by rfl) ⟨1699184, by rfl⟩ : syracuseStep 2265579 = 3398369) B3398369
theorem B2906501 : Blo 2265435 2906501 := bbase (se 4 (by rfl) ⟨272484, by rfl⟩ : syracuseStep 2906501 = 544969) (by norm_num)
theorem B7750669 : Blo 2265435 7750669 := bstep (se 3 (by rfl) ⟨1453250, by rfl⟩ : syracuseStep 7750669 = 2906501) B2906501
theorem B10334225 : Blo 2265435 10334225 := bstep (se 2 (by rfl) ⟨3875334, by rfl⟩ : syracuseStep 10334225 = 7750669) B7750669
theorem B6889483 : Blo 2265435 6889483 := bstep (se 1 (by rfl) ⟨5167112, by rfl⟩ : syracuseStep 6889483 = 10334225) B10334225
theorem B9185977 : Blo 2265435 9185977 := bstep (se 2 (by rfl) ⟨3444741, by rfl⟩ : syracuseStep 9185977 = 6889483) B6889483
theorem B48991877 : Blo 2265435 48991877 := bstep (se 4 (by rfl) ⟨4592988, by rfl⟩ : syracuseStep 48991877 = 9185977) B9185977
theorem B32661251 : Blo 2265435 32661251 := bstep (se 1 (by rfl) ⟨24495938, by rfl⟩ : syracuseStep 32661251 = 48991877) B48991877
theorem B21774167 : Blo 2265435 21774167 := bstep (se 1 (by rfl) ⟨16330625, by rfl⟩ : syracuseStep 21774167 = 32661251) B32661251
theorem B14516111 : Blo 2265435 14516111 := bstep (se 1 (by rfl) ⟨10887083, by rfl⟩ : syracuseStep 14516111 = 21774167) B21774167
theorem B9677407 : Blo 2265435 9677407 := bstep (se 1 (by rfl) ⟨7258055, by rfl⟩ : syracuseStep 9677407 = 14516111) B14516111
theorem B12903209 : Blo 2265435 12903209 := bstep (se 2 (by rfl) ⟨4838703, by rfl⟩ : syracuseStep 12903209 = 9677407) B9677407
theorem B8602139 : Blo 2265435 8602139 := bstep (se 1 (by rfl) ⟨6451604, by rfl⟩ : syracuseStep 8602139 = 12903209) B12903209
theorem B5734759 : Blo 2265435 5734759 := bstep (se 1 (by rfl) ⟨4301069, by rfl⟩ : syracuseStep 5734759 = 8602139) B8602139
theorem B7646345 : Blo 2265435 7646345 := bstep (se 2 (by rfl) ⟨2867379, by rfl⟩ : syracuseStep 7646345 = 5734759) B5734759
theorem B5097563 : Blo 2265435 5097563 := bstep (se 1 (by rfl) ⟨3823172, by rfl⟩ : syracuseStep 5097563 = 7646345) B7646345
theorem B3398375 : Blo 2265435 3398375 := bstep (se 1 (by rfl) ⟨2548781, by rfl⟩ : syracuseStep 3398375 = 5097563) B5097563
theorem B2265583 : Blo 2265435 2265583 := bstep (se 1 (by rfl) ⟨1699187, by rfl⟩ : syracuseStep 2265583 = 3398375) B3398375
theorem B3398381 : Blo 2265435 3398381 := bbase (se 3 (by rfl) ⟨637196, by rfl⟩ : syracuseStep 3398381 = 1274393) (by norm_num)
theorem B2265587 : Blo 2265435 2265587 := bstep (se 1 (by rfl) ⟨1699190, by rfl⟩ : syracuseStep 2265587 = 3398381) B3398381
theorem B5097581 : Blo 2265435 5097581 := bbase (se 3 (by rfl) ⟨955796, by rfl⟩ : syracuseStep 5097581 = 1911593) (by norm_num)
theorem B3398387 : Blo 2265435 3398387 := bstep (se 1 (by rfl) ⟨2548790, by rfl⟩ : syracuseStep 3398387 = 5097581) B5097581
theorem B2265591 : Blo 2265435 2265591 := bstep (se 1 (by rfl) ⟨1699193, by rfl⟩ : syracuseStep 2265591 = 3398387) B3398387
theorem B4301093 : Blo 2265435 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B2867395 : Blo 2265435 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B3823193 : Blo 2265435 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B2548795 : Blo 2265435 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B3398393 : Blo 2265435 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B2265595 : Blo 2265435 2265595 := bstep (se 1 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 2265595 = 3398393) B3398393
theorem B11626085 : Blo 2265435 11626085 := bbase (se 4 (by rfl) ⟨1089945, by rfl⟩ : syracuseStep 11626085 = 2179891) (by norm_num)
theorem B7750723 : Blo 2265435 7750723 := bstep (se 1 (by rfl) ⟨5813042, by rfl⟩ : syracuseStep 7750723 = 11626085) B11626085
theorem B10334297 : Blo 2265435 10334297 := bstep (se 2 (by rfl) ⟨3875361, by rfl⟩ : syracuseStep 10334297 = 7750723) B7750723
theorem B6889531 : Blo 2265435 6889531 := bstep (se 1 (by rfl) ⟨5167148, by rfl⟩ : syracuseStep 6889531 = 10334297) B10334297
theorem B9186041 : Blo 2265435 9186041 := bstep (se 2 (by rfl) ⟨3444765, by rfl⟩ : syracuseStep 9186041 = 6889531) B6889531
theorem B24496109 : Blo 2265435 24496109 := bstep (se 3 (by rfl) ⟨4593020, by rfl⟩ : syracuseStep 24496109 = 9186041) B9186041
theorem B16330739 : Blo 2265435 16330739 := bstep (se 1 (by rfl) ⟨12248054, by rfl⟩ : syracuseStep 16330739 = 24496109) B24496109
theorem B43548637 : Blo 2265435 43548637 := bstep (se 3 (by rfl) ⟨8165369, by rfl⟩ : syracuseStep 43548637 = 16330739) B16330739
theorem B58064849 : Blo 2265435 58064849 := bstep (se 2 (by rfl) ⟨21774318, by rfl⟩ : syracuseStep 58064849 = 43548637) B43548637
theorem B38709899 : Blo 2265435 38709899 := bstep (se 1 (by rfl) ⟨29032424, by rfl⟩ : syracuseStep 38709899 = 58064849) B58064849
theorem B25806599 : Blo 2265435 25806599 := bstep (se 1 (by rfl) ⟨19354949, by rfl⟩ : syracuseStep 25806599 = 38709899) B38709899
theorem B17204399 : Blo 2265435 17204399 := bstep (se 1 (by rfl) ⟨12903299, by rfl⟩ : syracuseStep 17204399 = 25806599) B25806599
theorem B11469599 : Blo 2265435 11469599 := bstep (se 1 (by rfl) ⟨8602199, by rfl⟩ : syracuseStep 11469599 = 17204399) B17204399
theorem B7646399 : Blo 2265435 7646399 := bstep (se 1 (by rfl) ⟨5734799, by rfl⟩ : syracuseStep 7646399 = 11469599) B11469599
theorem B5097599 : Blo 2265435 5097599 := bstep (se 1 (by rfl) ⟨3823199, by rfl⟩ : syracuseStep 5097599 = 7646399) B7646399
theorem B3398399 : Blo 2265435 3398399 := bstep (se 1 (by rfl) ⟨2548799, by rfl⟩ : syracuseStep 3398399 = 5097599) B5097599
theorem B2265599 : Blo 2265435 2265599 := bstep (se 1 (by rfl) ⟨1699199, by rfl⟩ : syracuseStep 2265599 = 3398399) B3398399
theorem B3398405 : Blo 2265435 3398405 := bbase (se 4 (by rfl) ⟨318600, by rfl⟩ : syracuseStep 3398405 = 637201) (by norm_num)
theorem B2265603 : Blo 2265435 2265603 := bstep (se 1 (by rfl) ⟨1699202, by rfl⟩ : syracuseStep 2265603 = 3398405) B3398405
theorem B3823213 : Blo 2265435 3823213 := bbase (se 3 (by rfl) ⟨716852, by rfl⟩ : syracuseStep 3823213 = 1433705) (by norm_num)
theorem B5097617 : Blo 2265435 5097617 := bstep (se 2 (by rfl) ⟨1911606, by rfl⟩ : syracuseStep 5097617 = 3823213) B3823213
theorem B3398411 : Blo 2265435 3398411 := bstep (se 1 (by rfl) ⟨2548808, by rfl⟩ : syracuseStep 3398411 = 5097617) B5097617
theorem B2265607 : Blo 2265435 2265607 := bstep (se 1 (by rfl) ⟨1699205, by rfl⟩ : syracuseStep 2265607 = 3398411) B3398411
theorem B2548813 : Blo 2265435 2548813 := bbase (se 3 (by rfl) ⟨477902, by rfl⟩ : syracuseStep 2548813 = 955805) (by norm_num)
theorem B3398417 : Blo 2265435 3398417 := bstep (se 2 (by rfl) ⟨1274406, by rfl⟩ : syracuseStep 3398417 = 2548813) B2548813
theorem B2265611 : Blo 2265435 2265611 := bstep (se 1 (by rfl) ⟨1699208, by rfl⟩ : syracuseStep 2265611 = 3398417) B3398417
theorem B7646453 : Blo 2265435 7646453 := bbase (se 5 (by rfl) ⟨358427, by rfl⟩ : syracuseStep 7646453 = 716855) (by norm_num)
theorem B5097635 : Blo 2265435 5097635 := bstep (se 1 (by rfl) ⟨3823226, by rfl⟩ : syracuseStep 5097635 = 7646453) B7646453
theorem B3398423 : Blo 2265435 3398423 := bstep (se 1 (by rfl) ⟨2548817, by rfl⟩ : syracuseStep 3398423 = 5097635) B5097635
theorem B2265615 : Blo 2265435 2265615 := bstep (se 1 (by rfl) ⟨1699211, by rfl⟩ : syracuseStep 2265615 = 3398423) B3398423
theorem B3398429 : Blo 2265435 3398429 := bbase (se 3 (by rfl) ⟨637205, by rfl⟩ : syracuseStep 3398429 = 1274411) (by norm_num)
theorem B2265619 : Blo 2265435 2265619 := bstep (se 1 (by rfl) ⟨1699214, by rfl⟩ : syracuseStep 2265619 = 3398429) B3398429
theorem B5097653 : Blo 2265435 5097653 := bbase (se 5 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 5097653 = 477905) (by norm_num)
theorem B3398435 : Blo 2265435 3398435 := bstep (se 1 (by rfl) ⟨2548826, by rfl⟩ : syracuseStep 3398435 = 5097653) B5097653
theorem B2265623 : Blo 2265435 2265623 := bstep (se 1 (by rfl) ⟨1699217, by rfl⟩ : syracuseStep 2265623 = 3398435) B3398435
theorem B3062053 : Blo 2265435 3062053 := bbase (se 4 (by rfl) ⟨287067, by rfl⟩ : syracuseStep 3062053 = 574135) (by norm_num)
theorem B4082737 : Blo 2265435 4082737 := bstep (se 2 (by rfl) ⟨1531026, by rfl⟩ : syracuseStep 4082737 = 3062053) B3062053
theorem B5443649 : Blo 2265435 5443649 := bstep (se 2 (by rfl) ⟨2041368, by rfl⟩ : syracuseStep 5443649 = 4082737) B4082737
theorem B3629099 : Blo 2265435 3629099 := bstep (se 1 (by rfl) ⟨2721824, by rfl⟩ : syracuseStep 3629099 = 5443649) B5443649
theorem B2419399 : Blo 2265435 2419399 := bstep (se 1 (by rfl) ⟨1814549, by rfl⟩ : syracuseStep 2419399 = 3629099) B3629099
theorem B12903461 : Blo 2265435 12903461 := bstep (se 4 (by rfl) ⟨1209699, by rfl⟩ : syracuseStep 12903461 = 2419399) B2419399
theorem B8602307 : Blo 2265435 8602307 := bstep (se 1 (by rfl) ⟨6451730, by rfl⟩ : syracuseStep 8602307 = 12903461) B12903461
theorem B5734871 : Blo 2265435 5734871 := bstep (se 1 (by rfl) ⟨4301153, by rfl⟩ : syracuseStep 5734871 = 8602307) B8602307
theorem B3823247 : Blo 2265435 3823247 := bstep (se 1 (by rfl) ⟨2867435, by rfl⟩ : syracuseStep 3823247 = 5734871) B5734871
theorem B2548831 : Blo 2265435 2548831 := bstep (se 1 (by rfl) ⟨1911623, by rfl⟩ : syracuseStep 2548831 = 3823247) B3823247
theorem B3398441 : Blo 2265435 3398441 := bstep (se 2 (by rfl) ⟨1274415, by rfl⟩ : syracuseStep 3398441 = 2548831) B2548831
theorem B2265627 : Blo 2265435 2265627 := bstep (se 1 (by rfl) ⟨1699220, by rfl⟩ : syracuseStep 2265627 = 3398441) B3398441
theorem B2721829 : Blo 2265435 2721829 := bbase (se 4 (by rfl) ⟨255171, by rfl⟩ : syracuseStep 2721829 = 510343) (by norm_num)
theorem B3629105 : Blo 2265435 3629105 := bstep (se 2 (by rfl) ⟨1360914, by rfl⟩ : syracuseStep 3629105 = 2721829) B2721829
theorem B2419403 : Blo 2265435 2419403 := bstep (se 1 (by rfl) ⟨1814552, by rfl⟩ : syracuseStep 2419403 = 3629105) B3629105
theorem B6451741 : Blo 2265435 6451741 := bstep (se 3 (by rfl) ⟨1209701, by rfl⟩ : syracuseStep 6451741 = 2419403) B2419403
theorem B8602321 : Blo 2265435 8602321 := bstep (se 2 (by rfl) ⟨3225870, by rfl⟩ : syracuseStep 8602321 = 6451741) B6451741
theorem B11469761 : Blo 2265435 11469761 := bstep (se 2 (by rfl) ⟨4301160, by rfl⟩ : syracuseStep 11469761 = 8602321) B8602321
theorem B7646507 : Blo 2265435 7646507 := bstep (se 1 (by rfl) ⟨5734880, by rfl⟩ : syracuseStep 7646507 = 11469761) B11469761
theorem B5097671 : Blo 2265435 5097671 := bstep (se 1 (by rfl) ⟨3823253, by rfl⟩ : syracuseStep 5097671 = 7646507) B7646507
theorem B3398447 : Blo 2265435 3398447 := bstep (se 1 (by rfl) ⟨2548835, by rfl⟩ : syracuseStep 3398447 = 5097671) B5097671
theorem B2265631 : Blo 2265435 2265631 := bstep (se 1 (by rfl) ⟨1699223, by rfl⟩ : syracuseStep 2265631 = 3398447) B3398447
theorem B3398453 : Blo 2265435 3398453 := bbase (se 5 (by rfl) ⟨159302, by rfl⟩ : syracuseStep 3398453 = 318605) (by norm_num)
theorem B2265635 : Blo 2265435 2265635 := bstep (se 1 (by rfl) ⟨1699226, by rfl⟩ : syracuseStep 2265635 = 3398453) B3398453
theorem B5734901 : Blo 2265435 5734901 := bbase (se 5 (by rfl) ⟨268823, by rfl⟩ : syracuseStep 5734901 = 537647) (by norm_num)
theorem B3823267 : Blo 2265435 3823267 := bstep (se 1 (by rfl) ⟨2867450, by rfl⟩ : syracuseStep 3823267 = 5734901) B5734901
theorem B5097689 : Blo 2265435 5097689 := bstep (se 2 (by rfl) ⟨1911633, by rfl⟩ : syracuseStep 5097689 = 3823267) B3823267
theorem B3398459 : Blo 2265435 3398459 := bstep (se 1 (by rfl) ⟨2548844, by rfl⟩ : syracuseStep 3398459 = 5097689) B5097689
theorem B2265639 : Blo 2265435 2265639 := bstep (se 1 (by rfl) ⟨1699229, by rfl⟩ : syracuseStep 2265639 = 3398459) B3398459
theorem B2548849 : Blo 2265435 2548849 := bbase (se 2 (by rfl) ⟨955818, by rfl⟩ : syracuseStep 2548849 = 1911637) (by norm_num)
theorem B3398465 : Blo 2265435 3398465 := bstep (se 2 (by rfl) ⟨1274424, by rfl⟩ : syracuseStep 3398465 = 2548849) B2548849
theorem B2265643 : Blo 2265435 2265643 := bstep (se 1 (by rfl) ⟨1699232, by rfl⟩ : syracuseStep 2265643 = 3398465) B3398465
theorem B7258261 : Blo 2265435 7258261 := bbase (se 6 (by rfl) ⟨170115, by rfl⟩ : syracuseStep 7258261 = 340231) (by norm_num)
theorem B9677681 : Blo 2265435 9677681 := bstep (se 2 (by rfl) ⟨3629130, by rfl⟩ : syracuseStep 9677681 = 7258261) B7258261
theorem B6451787 : Blo 2265435 6451787 := bstep (se 1 (by rfl) ⟨4838840, by rfl⟩ : syracuseStep 6451787 = 9677681) B9677681
theorem B4301191 : Blo 2265435 4301191 := bstep (se 1 (by rfl) ⟨3225893, by rfl⟩ : syracuseStep 4301191 = 6451787) B6451787
theorem B5734921 : Blo 2265435 5734921 := bstep (se 2 (by rfl) ⟨2150595, by rfl⟩ : syracuseStep 5734921 = 4301191) B4301191
theorem B7646561 : Blo 2265435 7646561 := bstep (se 2 (by rfl) ⟨2867460, by rfl⟩ : syracuseStep 7646561 = 5734921) B5734921
theorem B5097707 : Blo 2265435 5097707 := bstep (se 1 (by rfl) ⟨3823280, by rfl⟩ : syracuseStep 5097707 = 7646561) B7646561
theorem B3398471 : Blo 2265435 3398471 := bstep (se 1 (by rfl) ⟨2548853, by rfl⟩ : syracuseStep 3398471 = 5097707) B5097707
theorem B2265647 : Blo 2265435 2265647 := bstep (se 1 (by rfl) ⟨1699235, by rfl⟩ : syracuseStep 2265647 = 3398471) B3398471
theorem B3398477 : Blo 2265435 3398477 := bbase (se 3 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 3398477 = 1274429) (by norm_num)
theorem B2265651 : Blo 2265435 2265651 := bstep (se 1 (by rfl) ⟨1699238, by rfl⟩ : syracuseStep 2265651 = 3398477) B3398477
theorem B5097725 : Blo 2265435 5097725 := bbase (se 3 (by rfl) ⟨955823, by rfl⟩ : syracuseStep 5097725 = 1911647) (by norm_num)
theorem B3398483 : Blo 2265435 3398483 := bstep (se 1 (by rfl) ⟨2548862, by rfl⟩ : syracuseStep 3398483 = 5097725) B5097725
theorem B2265655 : Blo 2265435 2265655 := bstep (se 1 (by rfl) ⟨1699241, by rfl⟩ : syracuseStep 2265655 = 3398483) B3398483
theorem B3823301 : Blo 2265435 3823301 := bbase (se 4 (by rfl) ⟨358434, by rfl⟩ : syracuseStep 3823301 = 716869) (by norm_num)
theorem B2548867 : Blo 2265435 2548867 := bstep (se 1 (by rfl) ⟨1911650, by rfl⟩ : syracuseStep 2548867 = 3823301) B3823301
theorem B3398489 : Blo 2265435 3398489 := bstep (se 2 (by rfl) ⟨1274433, by rfl⟩ : syracuseStep 3398489 = 2548867) B2548867
theorem B2265659 : Blo 2265435 2265659 := bstep (se 1 (by rfl) ⟨1699244, by rfl⟩ : syracuseStep 2265659 = 3398489) B3398489
theorem B17204885 : Blo 2265435 17204885 := bbase (se 6 (by rfl) ⟨403239, by rfl⟩ : syracuseStep 17204885 = 806479) (by norm_num)
theorem B11469923 : Blo 2265435 11469923 := bstep (se 1 (by rfl) ⟨8602442, by rfl⟩ : syracuseStep 11469923 = 17204885) B17204885
theorem B7646615 : Blo 2265435 7646615 := bstep (se 1 (by rfl) ⟨5734961, by rfl⟩ : syracuseStep 7646615 = 11469923) B11469923
theorem B5097743 : Blo 2265435 5097743 := bstep (se 1 (by rfl) ⟨3823307, by rfl⟩ : syracuseStep 5097743 = 7646615) B7646615
theorem B3398495 : Blo 2265435 3398495 := bstep (se 1 (by rfl) ⟨2548871, by rfl⟩ : syracuseStep 3398495 = 5097743) B5097743
theorem B2265663 : Blo 2265435 2265663 := bstep (se 1 (by rfl) ⟨1699247, by rfl⟩ : syracuseStep 2265663 = 3398495) B3398495
theorem B3398501 : Blo 2265435 3398501 := bbase (se 4 (by rfl) ⟨318609, by rfl⟩ : syracuseStep 3398501 = 637219) (by norm_num)
theorem B2265667 : Blo 2265435 2265667 := bstep (se 1 (by rfl) ⟨1699250, by rfl⟩ : syracuseStep 2265667 = 3398501) B3398501
theorem B4301237 : Blo 2265435 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B2867491 : Blo 2265435 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B3823321 : Blo 2265435 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B5097761 : Blo 2265435 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B3398507 : Blo 2265435 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B2265671 : Blo 2265435 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B2548885 : Blo 2265435 2548885 := bbase (se 6 (by rfl) ⟨59739, by rfl⟩ : syracuseStep 2548885 = 119479) (by norm_num)
theorem B3398513 : Blo 2265435 3398513 := bstep (se 2 (by rfl) ⟨1274442, by rfl⟩ : syracuseStep 3398513 = 2548885) B2548885
theorem B2265675 : Blo 2265435 2265675 := bstep (se 1 (by rfl) ⟨1699256, by rfl⟩ : syracuseStep 2265675 = 3398513) B3398513
theorem B2867501 : Blo 2265435 2867501 := bbase (se 3 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 2867501 = 1075313) (by norm_num)
theorem B7646669 : Blo 2265435 7646669 := bstep (se 3 (by rfl) ⟨1433750, by rfl⟩ : syracuseStep 7646669 = 2867501) B2867501
theorem B5097779 : Blo 2265435 5097779 := bstep (se 1 (by rfl) ⟨3823334, by rfl⟩ : syracuseStep 5097779 = 7646669) B7646669
theorem B3398519 : Blo 2265435 3398519 := bstep (se 1 (by rfl) ⟨2548889, by rfl⟩ : syracuseStep 3398519 = 5097779) B5097779
theorem B2265679 : Blo 2265435 2265679 := bstep (se 1 (by rfl) ⟨1699259, by rfl⟩ : syracuseStep 2265679 = 3398519) B3398519
theorem B3398525 : Blo 2265435 3398525 := bbase (se 3 (by rfl) ⟨637223, by rfl⟩ : syracuseStep 3398525 = 1274447) (by norm_num)
theorem B2265683 : Blo 2265435 2265683 := bstep (se 1 (by rfl) ⟨1699262, by rfl⟩ : syracuseStep 2265683 = 3398525) B3398525
theorem B5097797 : Blo 2265435 5097797 := bbase (se 4 (by rfl) ⟨477918, by rfl⟩ : syracuseStep 5097797 = 955837) (by norm_num)
theorem B3398531 : Blo 2265435 3398531 := bstep (se 1 (by rfl) ⟨2548898, by rfl⟩ : syracuseStep 3398531 = 5097797) B5097797
theorem B2265687 : Blo 2265435 2265687 := bstep (se 1 (by rfl) ⟨1699265, by rfl⟩ : syracuseStep 2265687 = 3398531) B3398531
theorem B10887605 : Blo 2265435 10887605 := bbase (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) (by norm_num)
theorem B7258403 : Blo 2265435 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B4838935 : Blo 2265435 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B6451913 : Blo 2265435 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B4301275 : Blo 2265435 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B5735033 : Blo 2265435 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B3823355 : Blo 2265435 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B2548903 : Blo 2265435 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B3398537 : Blo 2265435 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B2265691 : Blo 2265435 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B11470085 : Blo 2265435 11470085 := bbase (se 4 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 11470085 = 2150641) (by norm_num)
theorem B7646723 : Blo 2265435 7646723 := bstep (se 1 (by rfl) ⟨5735042, by rfl⟩ : syracuseStep 7646723 = 11470085) B11470085
theorem B5097815 : Blo 2265435 5097815 := bstep (se 1 (by rfl) ⟨3823361, by rfl⟩ : syracuseStep 5097815 = 7646723) B7646723
theorem B3398543 : Blo 2265435 3398543 := bstep (se 1 (by rfl) ⟨2548907, by rfl⟩ : syracuseStep 3398543 = 5097815) B5097815
theorem B2265695 : Blo 2265435 2265695 := bstep (se 1 (by rfl) ⟨1699271, by rfl⟩ : syracuseStep 2265695 = 3398543) B3398543
theorem B3398549 : Blo 2265435 3398549 := bbase (se 6 (by rfl) ⟨79653, by rfl⟩ : syracuseStep 3398549 = 159307) (by norm_num)
theorem B2265699 : Blo 2265435 2265699 := bstep (se 1 (by rfl) ⟨1699274, by rfl⟩ : syracuseStep 2265699 = 3398549) B3398549
theorem B12903893 : Blo 2265435 12903893 := bbase (se 7 (by rfl) ⟨151217, by rfl⟩ : syracuseStep 12903893 = 302435) (by norm_num)
theorem B8602595 : Blo 2265435 8602595 := bstep (se 1 (by rfl) ⟨6451946, by rfl⟩ : syracuseStep 8602595 = 12903893) B12903893
theorem B5735063 : Blo 2265435 5735063 := bstep (se 1 (by rfl) ⟨4301297, by rfl⟩ : syracuseStep 5735063 = 8602595) B8602595
theorem B3823375 : Blo 2265435 3823375 := bstep (se 1 (by rfl) ⟨2867531, by rfl⟩ : syracuseStep 3823375 = 5735063) B5735063
theorem B5097833 : Blo 2265435 5097833 := bstep (se 2 (by rfl) ⟨1911687, by rfl⟩ : syracuseStep 5097833 = 3823375) B3823375
theorem B3398555 : Blo 2265435 3398555 := bstep (se 1 (by rfl) ⟨2548916, by rfl⟩ : syracuseStep 3398555 = 5097833) B5097833
theorem B2265703 : Blo 2265435 2265703 := bstep (se 1 (by rfl) ⟨1699277, by rfl⟩ : syracuseStep 2265703 = 3398555) B3398555
theorem B2548921 : Blo 2265435 2548921 := bbase (se 2 (by rfl) ⟨955845, by rfl⟩ : syracuseStep 2548921 = 1911691) (by norm_num)
theorem B3398561 : Blo 2265435 3398561 := bstep (se 2 (by rfl) ⟨1274460, by rfl⟩ : syracuseStep 3398561 = 2548921) B2548921
theorem B2265707 : Blo 2265435 2265707 := bstep (se 1 (by rfl) ⟨1699280, by rfl⟩ : syracuseStep 2265707 = 3398561) B3398561
theorem B2721925 : Blo 2265435 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B3629233 : Blo 2265435 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B4838977 : Blo 2265435 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B6451969 : Blo 2265435 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B8602625 : Blo 2265435 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B5735083 : Blo 2265435 5735083 := bstep (se 1 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 5735083 = 8602625) B8602625
theorem B7646777 : Blo 2265435 7646777 := bstep (se 2 (by rfl) ⟨2867541, by rfl⟩ : syracuseStep 7646777 = 5735083) B5735083
theorem B5097851 : Blo 2265435 5097851 := bstep (se 1 (by rfl) ⟨3823388, by rfl⟩ : syracuseStep 5097851 = 7646777) B7646777
theorem B3398567 : Blo 2265435 3398567 := bstep (se 1 (by rfl) ⟨2548925, by rfl⟩ : syracuseStep 3398567 = 5097851) B5097851
theorem B2265711 : Blo 2265435 2265711 := bstep (se 1 (by rfl) ⟨1699283, by rfl⟩ : syracuseStep 2265711 = 3398567) B3398567
theorem B3398573 : Blo 2265435 3398573 := bbase (se 3 (by rfl) ⟨637232, by rfl⟩ : syracuseStep 3398573 = 1274465) (by norm_num)
theorem B2265715 : Blo 2265435 2265715 := bstep (se 1 (by rfl) ⟨1699286, by rfl⟩ : syracuseStep 2265715 = 3398573) B3398573
theorem B5097869 : Blo 2265435 5097869 := bbase (se 3 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 5097869 = 1911701) (by norm_num)
theorem B3398579 : Blo 2265435 3398579 := bstep (se 1 (by rfl) ⟨2548934, by rfl⟩ : syracuseStep 3398579 = 5097869) B5097869
theorem B2265719 : Blo 2265435 2265719 := bstep (se 1 (by rfl) ⟨1699289, by rfl⟩ : syracuseStep 2265719 = 3398579) B3398579
theorem B2867557 : Blo 2265435 2867557 := bbase (se 4 (by rfl) ⟨268833, by rfl⟩ : syracuseStep 2867557 = 537667) (by norm_num)
theorem B3823409 : Blo 2265435 3823409 := bstep (se 2 (by rfl) ⟨1433778, by rfl⟩ : syracuseStep 3823409 = 2867557) B2867557
theorem B2548939 : Blo 2265435 2548939 := bstep (se 1 (by rfl) ⟨1911704, by rfl⟩ : syracuseStep 2548939 = 3823409) B3823409
theorem B3398585 : Blo 2265435 3398585 := bstep (se 2 (by rfl) ⟨1274469, by rfl⟩ : syracuseStep 3398585 = 2548939) B2548939
theorem B2265723 : Blo 2265435 2265723 := bstep (se 1 (by rfl) ⟨1699292, by rfl⟩ : syracuseStep 2265723 = 3398585) B3398585
theorem B2759081 : Blo 2265435 2759081 := bbase (se 2 (by rfl) ⟨1034655, by rfl⟩ : syracuseStep 2759081 = 2069311) (by norm_num)
theorem B7357549 : Blo 2265435 7357549 := bstep (se 3 (by rfl) ⟨1379540, by rfl⟩ : syracuseStep 7357549 = 2759081) B2759081
theorem B9810065 : Blo 2265435 9810065 := bstep (se 2 (by rfl) ⟨3678774, by rfl⟩ : syracuseStep 9810065 = 7357549) B7357549
theorem B6540043 : Blo 2265435 6540043 := bstep (se 1 (by rfl) ⟨4905032, by rfl⟩ : syracuseStep 6540043 = 9810065) B9810065
theorem B8720057 : Blo 2265435 8720057 := bstep (se 2 (by rfl) ⟨3270021, by rfl⟩ : syracuseStep 8720057 = 6540043) B6540043
theorem B5813371 : Blo 2265435 5813371 := bstep (se 1 (by rfl) ⟨4360028, by rfl⟩ : syracuseStep 5813371 = 8720057) B8720057
theorem B7751161 : Blo 2265435 7751161 := bstep (se 2 (by rfl) ⟨2906685, by rfl⟩ : syracuseStep 7751161 = 5813371) B5813371
theorem B10334881 : Blo 2265435 10334881 := bstep (se 2 (by rfl) ⟨3875580, by rfl⟩ : syracuseStep 10334881 = 7751161) B7751161
theorem B13779841 : Blo 2265435 13779841 := bstep (se 2 (by rfl) ⟨5167440, by rfl⟩ : syracuseStep 13779841 = 10334881) B10334881
theorem B18373121 : Blo 2265435 18373121 := bstep (se 2 (by rfl) ⟨6889920, by rfl⟩ : syracuseStep 18373121 = 13779841) B13779841
theorem B12248747 : Blo 2265435 12248747 := bstep (se 1 (by rfl) ⟨9186560, by rfl⟩ : syracuseStep 12248747 = 18373121) B18373121
theorem B8165831 : Blo 2265435 8165831 := bstep (se 1 (by rfl) ⟨6124373, by rfl⟩ : syracuseStep 8165831 = 12248747) B12248747
theorem B21775549 : Blo 2265435 21775549 := bstep (se 3 (by rfl) ⟨4082915, by rfl⟩ : syracuseStep 21775549 = 8165831) B8165831
theorem B29034065 : Blo 2265435 29034065 := bstep (se 2 (by rfl) ⟨10887774, by rfl⟩ : syracuseStep 29034065 = 21775549) B21775549
theorem B19356043 : Blo 2265435 19356043 := bstep (se 1 (by rfl) ⟨14517032, by rfl⟩ : syracuseStep 19356043 = 29034065) B29034065
theorem B25808057 : Blo 2265435 25808057 := bstep (se 2 (by rfl) ⟨9678021, by rfl⟩ : syracuseStep 25808057 = 19356043) B19356043
theorem B17205371 : Blo 2265435 17205371 := bstep (se 1 (by rfl) ⟨12904028, by rfl⟩ : syracuseStep 17205371 = 25808057) B25808057
theorem B11470247 : Blo 2265435 11470247 := bstep (se 1 (by rfl) ⟨8602685, by rfl⟩ : syracuseStep 11470247 = 17205371) B17205371
theorem B7646831 : Blo 2265435 7646831 := bstep (se 1 (by rfl) ⟨5735123, by rfl⟩ : syracuseStep 7646831 = 11470247) B11470247
theorem B5097887 : Blo 2265435 5097887 := bstep (se 1 (by rfl) ⟨3823415, by rfl⟩ : syracuseStep 5097887 = 7646831) B7646831
theorem B3398591 : Blo 2265435 3398591 := bstep (se 1 (by rfl) ⟨2548943, by rfl⟩ : syracuseStep 3398591 = 5097887) B5097887
theorem B2265727 : Blo 2265435 2265727 := bstep (se 1 (by rfl) ⟨1699295, by rfl⟩ : syracuseStep 2265727 = 3398591) B3398591
theorem B3398597 : Blo 2265435 3398597 := bbase (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) (by norm_num)
theorem B2265731 : Blo 2265435 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B3823429 : Blo 2265435 3823429 := bbase (se 4 (by rfl) ⟨358446, by rfl⟩ : syracuseStep 3823429 = 716893) (by norm_num)
theorem B5097905 : Blo 2265435 5097905 := bstep (se 2 (by rfl) ⟨1911714, by rfl⟩ : syracuseStep 5097905 = 3823429) B3823429
theorem B3398603 : Blo 2265435 3398603 := bstep (se 1 (by rfl) ⟨2548952, by rfl⟩ : syracuseStep 3398603 = 5097905) B5097905
theorem B2265735 : Blo 2265435 2265735 := bstep (se 1 (by rfl) ⟨1699301, by rfl⟩ : syracuseStep 2265735 = 3398603) B3398603
theorem B2548957 : Blo 2265435 2548957 := bbase (se 3 (by rfl) ⟨477929, by rfl⟩ : syracuseStep 2548957 = 955859) (by norm_num)
theorem B3398609 : Blo 2265435 3398609 := bstep (se 2 (by rfl) ⟨1274478, by rfl⟩ : syracuseStep 3398609 = 2548957) B2548957
theorem B2265739 : Blo 2265435 2265739 := bstep (se 1 (by rfl) ⟨1699304, by rfl⟩ : syracuseStep 2265739 = 3398609) B3398609
theorem B7646885 : Blo 2265435 7646885 := bbase (se 4 (by rfl) ⟨716895, by rfl⟩ : syracuseStep 7646885 = 1433791) (by norm_num)
theorem B5097923 : Blo 2265435 5097923 := bstep (se 1 (by rfl) ⟨3823442, by rfl⟩ : syracuseStep 5097923 = 7646885) B7646885
theorem B3398615 : Blo 2265435 3398615 := bstep (se 1 (by rfl) ⟨2548961, by rfl⟩ : syracuseStep 3398615 = 5097923) B5097923
theorem B2265743 : Blo 2265435 2265743 := bstep (se 1 (by rfl) ⟨1699307, by rfl⟩ : syracuseStep 2265743 = 3398615) B3398615
theorem B3398621 : Blo 2265435 3398621 := bbase (se 3 (by rfl) ⟨637241, by rfl⟩ : syracuseStep 3398621 = 1274483) (by norm_num)
theorem B2265747 : Blo 2265435 2265747 := bstep (se 1 (by rfl) ⟨1699310, by rfl⟩ : syracuseStep 2265747 = 3398621) B3398621
theorem B5097941 : Blo 2265435 5097941 := bbase (se 7 (by rfl) ⟨59741, by rfl⟩ : syracuseStep 5097941 = 119483) (by norm_num)
theorem B3398627 : Blo 2265435 3398627 := bstep (se 1 (by rfl) ⟨2548970, by rfl⟩ : syracuseStep 3398627 = 5097941) B5097941
theorem B2265751 : Blo 2265435 2265751 := bstep (se 1 (by rfl) ⟨1699313, by rfl⟩ : syracuseStep 2265751 = 3398627) B3398627
theorem B3314677 : Blo 2265435 3314677 := bbase (se 5 (by rfl) ⟨155375, by rfl⟩ : syracuseStep 3314677 = 310751) (by norm_num)
theorem B4419569 : Blo 2265435 4419569 := bstep (se 2 (by rfl) ⟨1657338, by rfl⟩ : syracuseStep 4419569 = 3314677) B3314677
theorem B11785517 : Blo 2265435 11785517 := bstep (se 3 (by rfl) ⟨2209784, by rfl⟩ : syracuseStep 11785517 = 4419569) B4419569
theorem B7857011 : Blo 2265435 7857011 := bstep (se 1 (by rfl) ⟨5892758, by rfl⟩ : syracuseStep 7857011 = 11785517) B11785517
theorem B20952029 : Blo 2265435 20952029 := bstep (se 3 (by rfl) ⟨3928505, by rfl⟩ : syracuseStep 20952029 = 7857011) B7857011
theorem B13968019 : Blo 2265435 13968019 := bstep (se 1 (by rfl) ⟨10476014, by rfl⟩ : syracuseStep 13968019 = 20952029) B20952029
theorem B18624025 : Blo 2265435 18624025 := bstep (se 2 (by rfl) ⟨6984009, by rfl⟩ : syracuseStep 18624025 = 13968019) B13968019
theorem B99328133 : Blo 2265435 99328133 := bstep (se 4 (by rfl) ⟨9312012, by rfl⟩ : syracuseStep 99328133 = 18624025) B18624025
theorem B264875021 : Blo 2265435 264875021 := bstep (se 3 (by rfl) ⟨49664066, by rfl⟩ : syracuseStep 264875021 = 99328133) B99328133
theorem B176583347 : Blo 2265435 176583347 := bstep (se 1 (by rfl) ⟨132437510, by rfl⟩ : syracuseStep 176583347 = 264875021) B264875021
theorem B117722231 : Blo 2265435 117722231 := bstep (se 1 (by rfl) ⟨88291673, by rfl⟩ : syracuseStep 117722231 = 176583347) B176583347
theorem B78481487 : Blo 2265435 78481487 := bstep (se 1 (by rfl) ⟨58861115, by rfl⟩ : syracuseStep 78481487 = 117722231) B117722231
theorem B52320991 : Blo 2265435 52320991 := bstep (se 1 (by rfl) ⟨39240743, by rfl⟩ : syracuseStep 52320991 = 78481487) B78481487
theorem B69761321 : Blo 2265435 69761321 := bstep (se 2 (by rfl) ⟨26160495, by rfl⟩ : syracuseStep 69761321 = 52320991) B52320991
theorem B46507547 : Blo 2265435 46507547 := bstep (se 1 (by rfl) ⟨34880660, by rfl⟩ : syracuseStep 46507547 = 69761321) B69761321
theorem B31005031 : Blo 2265435 31005031 := bstep (se 1 (by rfl) ⟨23253773, by rfl⟩ : syracuseStep 31005031 = 46507547) B46507547
theorem B41340041 : Blo 2265435 41340041 := bstep (se 2 (by rfl) ⟨15502515, by rfl⟩ : syracuseStep 41340041 = 31005031) B31005031
theorem B27560027 : Blo 2265435 27560027 := bstep (se 1 (by rfl) ⟨20670020, by rfl⟩ : syracuseStep 27560027 = 41340041) B41340041
theorem B73493405 : Blo 2265435 73493405 := bstep (se 3 (by rfl) ⟨13780013, by rfl⟩ : syracuseStep 73493405 = 27560027) B27560027
theorem B48995603 : Blo 2265435 48995603 := bstep (se 1 (by rfl) ⟨36746702, by rfl⟩ : syracuseStep 48995603 = 73493405) B73493405
theorem B32663735 : Blo 2265435 32663735 := bstep (se 1 (by rfl) ⟨24497801, by rfl⟩ : syracuseStep 32663735 = 48995603) B48995603
theorem B21775823 : Blo 2265435 21775823 := bstep (se 1 (by rfl) ⟨16331867, by rfl⟩ : syracuseStep 21775823 = 32663735) B32663735
theorem B14517215 : Blo 2265435 14517215 := bstep (se 1 (by rfl) ⟨10887911, by rfl⟩ : syracuseStep 14517215 = 21775823) B21775823
theorem B9678143 : Blo 2265435 9678143 := bstep (se 1 (by rfl) ⟨7258607, by rfl⟩ : syracuseStep 9678143 = 14517215) B14517215
theorem B6452095 : Blo 2265435 6452095 := bstep (se 1 (by rfl) ⟨4839071, by rfl⟩ : syracuseStep 6452095 = 9678143) B9678143
theorem B8602793 : Blo 2265435 8602793 := bstep (se 2 (by rfl) ⟨3226047, by rfl⟩ : syracuseStep 8602793 = 6452095) B6452095
theorem B5735195 : Blo 2265435 5735195 := bstep (se 1 (by rfl) ⟨4301396, by rfl⟩ : syracuseStep 5735195 = 8602793) B8602793
theorem B3823463 : Blo 2265435 3823463 := bstep (se 1 (by rfl) ⟨2867597, by rfl⟩ : syracuseStep 3823463 = 5735195) B5735195
theorem B2548975 : Blo 2265435 2548975 := bstep (se 1 (by rfl) ⟨1911731, by rfl⟩ : syracuseStep 2548975 = 3823463) B3823463
theorem B3398633 : Blo 2265435 3398633 := bstep (se 2 (by rfl) ⟨1274487, by rfl⟩ : syracuseStep 3398633 = 2548975) B2548975
theorem B2265755 : Blo 2265435 2265755 := bstep (se 1 (by rfl) ⟨1699316, by rfl⟩ : syracuseStep 2265755 = 3398633) B3398633
theorem B2583757 : Blo 2265435 2583757 := bbase (se 3 (by rfl) ⟨484454, by rfl⟩ : syracuseStep 2583757 = 968909) (by norm_num)
theorem B13780037 : Blo 2265435 13780037 := bstep (se 4 (by rfl) ⟨1291878, by rfl⟩ : syracuseStep 13780037 = 2583757) B2583757
theorem B9186691 : Blo 2265435 9186691 := bstep (se 1 (by rfl) ⟨6890018, by rfl⟩ : syracuseStep 9186691 = 13780037) B13780037
theorem B12248921 : Blo 2265435 12248921 := bstep (se 2 (by rfl) ⟨4593345, by rfl⟩ : syracuseStep 12248921 = 9186691) B9186691
theorem B8165947 : Blo 2265435 8165947 := bstep (se 1 (by rfl) ⟨6124460, by rfl⟩ : syracuseStep 8165947 = 12248921) B12248921
theorem B10887929 : Blo 2265435 10887929 := bstep (se 2 (by rfl) ⟨4082973, by rfl⟩ : syracuseStep 10887929 = 8165947) B8165947
theorem B7258619 : Blo 2265435 7258619 := bstep (se 1 (by rfl) ⟨5443964, by rfl⟩ : syracuseStep 7258619 = 10887929) B10887929
theorem B19356317 : Blo 2265435 19356317 := bstep (se 3 (by rfl) ⟨3629309, by rfl⟩ : syracuseStep 19356317 = 7258619) B7258619
theorem B12904211 : Blo 2265435 12904211 := bstep (se 1 (by rfl) ⟨9678158, by rfl⟩ : syracuseStep 12904211 = 19356317) B19356317
theorem B8602807 : Blo 2265435 8602807 := bstep (se 1 (by rfl) ⟨6452105, by rfl⟩ : syracuseStep 8602807 = 12904211) B12904211
theorem B11470409 : Blo 2265435 11470409 := bstep (se 2 (by rfl) ⟨4301403, by rfl⟩ : syracuseStep 11470409 = 8602807) B8602807
theorem B7646939 : Blo 2265435 7646939 := bstep (se 1 (by rfl) ⟨5735204, by rfl⟩ : syracuseStep 7646939 = 11470409) B11470409
theorem B5097959 : Blo 2265435 5097959 := bstep (se 1 (by rfl) ⟨3823469, by rfl⟩ : syracuseStep 5097959 = 7646939) B7646939
theorem B3398639 : Blo 2265435 3398639 := bstep (se 1 (by rfl) ⟨2548979, by rfl⟩ : syracuseStep 3398639 = 5097959) B5097959
theorem B2265759 : Blo 2265435 2265759 := bstep (se 1 (by rfl) ⟨1699319, by rfl⟩ : syracuseStep 2265759 = 3398639) B3398639
theorem B3398645 : Blo 2265435 3398645 := bbase (se 5 (by rfl) ⟨159311, by rfl⟩ : syracuseStep 3398645 = 318623) (by norm_num)
theorem B2265763 : Blo 2265435 2265763 := bstep (se 1 (by rfl) ⟨1699322, by rfl⟩ : syracuseStep 2265763 = 3398645) B3398645
theorem B4082989 : Blo 2265435 4082989 := bbase (se 3 (by rfl) ⟨765560, by rfl⟩ : syracuseStep 4082989 = 1531121) (by norm_num)
theorem B5443985 : Blo 2265435 5443985 := bstep (se 2 (by rfl) ⟨2041494, by rfl⟩ : syracuseStep 5443985 = 4082989) B4082989
theorem B3629323 : Blo 2265435 3629323 := bstep (se 1 (by rfl) ⟨2721992, by rfl⟩ : syracuseStep 3629323 = 5443985) B5443985
theorem B4839097 : Blo 2265435 4839097 := bstep (se 2 (by rfl) ⟨1814661, by rfl⟩ : syracuseStep 4839097 = 3629323) B3629323
theorem B6452129 : Blo 2265435 6452129 := bstep (se 2 (by rfl) ⟨2419548, by rfl⟩ : syracuseStep 6452129 = 4839097) B4839097
theorem B4301419 : Blo 2265435 4301419 := bstep (se 1 (by rfl) ⟨3226064, by rfl⟩ : syracuseStep 4301419 = 6452129) B6452129
theorem B5735225 : Blo 2265435 5735225 := bstep (se 2 (by rfl) ⟨2150709, by rfl⟩ : syracuseStep 5735225 = 4301419) B4301419
theorem B3823483 : Blo 2265435 3823483 := bstep (se 1 (by rfl) ⟨2867612, by rfl⟩ : syracuseStep 3823483 = 5735225) B5735225
theorem B5097977 : Blo 2265435 5097977 := bstep (se 2 (by rfl) ⟨1911741, by rfl⟩ : syracuseStep 5097977 = 3823483) B3823483
theorem B3398651 : Blo 2265435 3398651 := bstep (se 1 (by rfl) ⟨2548988, by rfl⟩ : syracuseStep 3398651 = 5097977) B5097977
theorem B2265767 : Blo 2265435 2265767 := bstep (se 1 (by rfl) ⟨1699325, by rfl⟩ : syracuseStep 2265767 = 3398651) B3398651
theorem B2548993 : Blo 2265435 2548993 := bbase (se 2 (by rfl) ⟨955872, by rfl⟩ : syracuseStep 2548993 = 1911745) (by norm_num)
theorem B3398657 : Blo 2265435 3398657 := bstep (se 2 (by rfl) ⟨1274496, by rfl⟩ : syracuseStep 3398657 = 2548993) B2548993
theorem B2265771 : Blo 2265435 2265771 := bstep (se 1 (by rfl) ⟨1699328, by rfl⟩ : syracuseStep 2265771 = 3398657) B3398657
theorem B5735245 : Blo 2265435 5735245 := bbase (se 3 (by rfl) ⟨1075358, by rfl⟩ : syracuseStep 5735245 = 2150717) (by norm_num)
theorem B7646993 : Blo 2265435 7646993 := bstep (se 2 (by rfl) ⟨2867622, by rfl⟩ : syracuseStep 7646993 = 5735245) B5735245
theorem B5097995 : Blo 2265435 5097995 := bstep (se 1 (by rfl) ⟨3823496, by rfl⟩ : syracuseStep 5097995 = 7646993) B7646993
theorem B3398663 : Blo 2265435 3398663 := bstep (se 1 (by rfl) ⟨2548997, by rfl⟩ : syracuseStep 3398663 = 5097995) B5097995
theorem B2265775 : Blo 2265435 2265775 := bstep (se 1 (by rfl) ⟨1699331, by rfl⟩ : syracuseStep 2265775 = 3398663) B3398663
theorem B3398669 : Blo 2265435 3398669 := bbase (se 3 (by rfl) ⟨637250, by rfl⟩ : syracuseStep 3398669 = 1274501) (by norm_num)
theorem B2265779 : Blo 2265435 2265779 := bstep (se 1 (by rfl) ⟨1699334, by rfl⟩ : syracuseStep 2265779 = 3398669) B3398669
theorem B5098013 : Blo 2265435 5098013 := bbase (se 3 (by rfl) ⟨955877, by rfl⟩ : syracuseStep 5098013 = 1911755) (by norm_num)
theorem B3398675 : Blo 2265435 3398675 := bstep (se 1 (by rfl) ⟨2549006, by rfl⟩ : syracuseStep 3398675 = 5098013) B5098013
theorem B2265783 : Blo 2265435 2265783 := bstep (se 1 (by rfl) ⟨1699337, by rfl⟩ : syracuseStep 2265783 = 3398675) B3398675
theorem B3823517 : Blo 2265435 3823517 := bbase (se 3 (by rfl) ⟨716909, by rfl⟩ : syracuseStep 3823517 = 1433819) (by norm_num)
theorem B2549011 : Blo 2265435 2549011 := bstep (se 1 (by rfl) ⟨1911758, by rfl⟩ : syracuseStep 2549011 = 3823517) B3823517
theorem B3398681 : Blo 2265435 3398681 := bstep (se 2 (by rfl) ⟨1274505, by rfl⟩ : syracuseStep 3398681 = 2549011) B2549011
theorem B2265787 : Blo 2265435 2265787 := bstep (se 1 (by rfl) ⟨1699340, by rfl⟩ : syracuseStep 2265787 = 3398681) B3398681
theorem B9186821 : Blo 2265435 9186821 := bbase (se 4 (by rfl) ⟨861264, by rfl⟩ : syracuseStep 9186821 = 1722529) (by norm_num)
theorem B6124547 : Blo 2265435 6124547 := bstep (se 1 (by rfl) ⟨4593410, by rfl⟩ : syracuseStep 6124547 = 9186821) B9186821
theorem B4083031 : Blo 2265435 4083031 := bstep (se 1 (by rfl) ⟨3062273, by rfl⟩ : syracuseStep 4083031 = 6124547) B6124547
theorem B21776165 : Blo 2265435 21776165 := bstep (se 4 (by rfl) ⟨2041515, by rfl⟩ : syracuseStep 21776165 = 4083031) B4083031
theorem B14517443 : Blo 2265435 14517443 := bstep (se 1 (by rfl) ⟨10888082, by rfl⟩ : syracuseStep 14517443 = 21776165) B21776165
theorem B9678295 : Blo 2265435 9678295 := bstep (se 1 (by rfl) ⟨7258721, by rfl⟩ : syracuseStep 9678295 = 14517443) B14517443
theorem B12904393 : Blo 2265435 12904393 := bstep (se 2 (by rfl) ⟨4839147, by rfl⟩ : syracuseStep 12904393 = 9678295) B9678295
theorem B17205857 : Blo 2265435 17205857 := bstep (se 2 (by rfl) ⟨6452196, by rfl⟩ : syracuseStep 17205857 = 12904393) B12904393
theorem B11470571 : Blo 2265435 11470571 := bstep (se 1 (by rfl) ⟨8602928, by rfl⟩ : syracuseStep 11470571 = 17205857) B17205857
theorem B7647047 : Blo 2265435 7647047 := bstep (se 1 (by rfl) ⟨5735285, by rfl⟩ : syracuseStep 7647047 = 11470571) B11470571
theorem B5098031 : Blo 2265435 5098031 := bstep (se 1 (by rfl) ⟨3823523, by rfl⟩ : syracuseStep 5098031 = 7647047) B7647047
theorem B3398687 : Blo 2265435 3398687 := bstep (se 1 (by rfl) ⟨2549015, by rfl⟩ : syracuseStep 3398687 = 5098031) B5098031
theorem B2265791 : Blo 2265435 2265791 := bstep (se 1 (by rfl) ⟨1699343, by rfl⟩ : syracuseStep 2265791 = 3398687) B3398687
theorem B3398693 : Blo 2265435 3398693 := bbase (se 4 (by rfl) ⟨318627, by rfl⟩ : syracuseStep 3398693 = 637255) (by norm_num)
theorem B2265795 : Blo 2265435 2265795 := bstep (se 1 (by rfl) ⟨1699346, by rfl⟩ : syracuseStep 2265795 = 3398693) B3398693
theorem B2867653 : Blo 2265435 2867653 := bbase (se 4 (by rfl) ⟨268842, by rfl⟩ : syracuseStep 2867653 = 537685) (by norm_num)
theorem B3823537 : Blo 2265435 3823537 := bstep (se 2 (by rfl) ⟨1433826, by rfl⟩ : syracuseStep 3823537 = 2867653) B2867653
theorem B5098049 : Blo 2265435 5098049 := bstep (se 2 (by rfl) ⟨1911768, by rfl⟩ : syracuseStep 5098049 = 3823537) B3823537
theorem B3398699 : Blo 2265435 3398699 := bstep (se 1 (by rfl) ⟨2549024, by rfl⟩ : syracuseStep 3398699 = 5098049) B5098049
theorem B2265799 : Blo 2265435 2265799 := bstep (se 1 (by rfl) ⟨1699349, by rfl⟩ : syracuseStep 2265799 = 3398699) B3398699
theorem B2549029 : Blo 2265435 2549029 := bbase (se 4 (by rfl) ⟨238971, by rfl⟩ : syracuseStep 2549029 = 477943) (by norm_num)
theorem B3398705 : Blo 2265435 3398705 := bstep (se 2 (by rfl) ⟨1274514, by rfl⟩ : syracuseStep 3398705 = 2549029) B2549029
theorem B2265803 : Blo 2265435 2265803 := bstep (se 1 (by rfl) ⟨1699352, by rfl⟩ : syracuseStep 2265803 = 3398705) B3398705
theorem B4083061 : Blo 2265435 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B5444081 : Blo 2265435 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B3629387 : Blo 2265435 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B9678365 : Blo 2265435 9678365 := bstep (se 3 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 9678365 = 3629387) B3629387
theorem B6452243 : Blo 2265435 6452243 := bstep (se 1 (by rfl) ⟨4839182, by rfl⟩ : syracuseStep 6452243 = 9678365) B9678365
theorem B4301495 : Blo 2265435 4301495 := bstep (se 1 (by rfl) ⟨3226121, by rfl⟩ : syracuseStep 4301495 = 6452243) B6452243
theorem B2867663 : Blo 2265435 2867663 := bstep (se 1 (by rfl) ⟨2150747, by rfl⟩ : syracuseStep 2867663 = 4301495) B4301495
theorem B7647101 : Blo 2265435 7647101 := bstep (se 3 (by rfl) ⟨1433831, by rfl⟩ : syracuseStep 7647101 = 2867663) B2867663
theorem B5098067 : Blo 2265435 5098067 := bstep (se 1 (by rfl) ⟨3823550, by rfl⟩ : syracuseStep 5098067 = 7647101) B7647101
theorem B3398711 : Blo 2265435 3398711 := bstep (se 1 (by rfl) ⟨2549033, by rfl⟩ : syracuseStep 3398711 = 5098067) B5098067
theorem B2265807 : Blo 2265435 2265807 := bstep (se 1 (by rfl) ⟨1699355, by rfl⟩ : syracuseStep 2265807 = 3398711) B3398711
theorem B3398717 : Blo 2265435 3398717 := bbase (se 3 (by rfl) ⟨637259, by rfl⟩ : syracuseStep 3398717 = 1274519) (by norm_num)
theorem B2265811 : Blo 2265435 2265811 := bstep (se 1 (by rfl) ⟨1699358, by rfl⟩ : syracuseStep 2265811 = 3398717) B3398717
theorem B5098085 : Blo 2265435 5098085 := bbase (se 4 (by rfl) ⟨477945, by rfl⟩ : syracuseStep 5098085 = 955891) (by norm_num)
theorem B3398723 : Blo 2265435 3398723 := bstep (se 1 (by rfl) ⟨2549042, by rfl⟩ : syracuseStep 3398723 = 5098085) B5098085
theorem B2265815 : Blo 2265435 2265815 := bstep (se 1 (by rfl) ⟨1699361, by rfl⟩ : syracuseStep 2265815 = 3398723) B3398723
theorem B5735357 : Blo 2265435 5735357 := bbase (se 3 (by rfl) ⟨1075379, by rfl⟩ : syracuseStep 5735357 = 2150759) (by norm_num)
theorem B3823571 : Blo 2265435 3823571 := bstep (se 1 (by rfl) ⟨2867678, by rfl⟩ : syracuseStep 3823571 = 5735357) B5735357
theorem B2549047 : Blo 2265435 2549047 := bstep (se 1 (by rfl) ⟨1911785, by rfl⟩ : syracuseStep 2549047 = 3823571) B3823571
theorem B3398729 : Blo 2265435 3398729 := bstep (se 2 (by rfl) ⟨1274523, by rfl⟩ : syracuseStep 3398729 = 2549047) B2549047
theorem B2265819 : Blo 2265435 2265819 := bstep (se 1 (by rfl) ⟨1699364, by rfl⟩ : syracuseStep 2265819 = 3398729) B3398729
theorem B4301525 : Blo 2265435 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B11470733 : Blo 2265435 11470733 := bstep (se 3 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 11470733 = 4301525) B4301525
theorem B7647155 : Blo 2265435 7647155 := bstep (se 1 (by rfl) ⟨5735366, by rfl⟩ : syracuseStep 7647155 = 11470733) B11470733
theorem B5098103 : Blo 2265435 5098103 := bstep (se 1 (by rfl) ⟨3823577, by rfl⟩ : syracuseStep 5098103 = 7647155) B7647155
theorem B3398735 : Blo 2265435 3398735 := bstep (se 1 (by rfl) ⟨2549051, by rfl⟩ : syracuseStep 3398735 = 5098103) B5098103
theorem B2265823 : Blo 2265435 2265823 := bstep (se 1 (by rfl) ⟨1699367, by rfl⟩ : syracuseStep 2265823 = 3398735) B3398735
theorem B3398741 : Blo 2265435 3398741 := bbase (se 8 (by rfl) ⟨19914, by rfl⟩ : syracuseStep 3398741 = 39829) (by norm_num)
theorem B2265827 : Blo 2265435 2265827 := bstep (se 1 (by rfl) ⟨1699370, by rfl⟩ : syracuseStep 2265827 = 3398741) B3398741
theorem B2722069 : Blo 2265435 2722069 := bbase (se 6 (by rfl) ⟨63798, by rfl⟩ : syracuseStep 2722069 = 127597) (by norm_num)
theorem B14517701 : Blo 2265435 14517701 := bstep (se 4 (by rfl) ⟨1361034, by rfl⟩ : syracuseStep 14517701 = 2722069) B2722069
theorem B9678467 : Blo 2265435 9678467 := bstep (se 1 (by rfl) ⟨7258850, by rfl⟩ : syracuseStep 9678467 = 14517701) B14517701
theorem B6452311 : Blo 2265435 6452311 := bstep (se 1 (by rfl) ⟨4839233, by rfl⟩ : syracuseStep 6452311 = 9678467) B9678467
theorem B8603081 : Blo 2265435 8603081 := bstep (se 2 (by rfl) ⟨3226155, by rfl⟩ : syracuseStep 8603081 = 6452311) B6452311
theorem B5735387 : Blo 2265435 5735387 := bstep (se 1 (by rfl) ⟨4301540, by rfl⟩ : syracuseStep 5735387 = 8603081) B8603081
theorem B3823591 : Blo 2265435 3823591 := bstep (se 1 (by rfl) ⟨2867693, by rfl⟩ : syracuseStep 3823591 = 5735387) B5735387
theorem B5098121 : Blo 2265435 5098121 := bstep (se 2 (by rfl) ⟨1911795, by rfl⟩ : syracuseStep 5098121 = 3823591) B3823591
theorem B3398747 : Blo 2265435 3398747 := bstep (se 1 (by rfl) ⟨2549060, by rfl⟩ : syracuseStep 3398747 = 5098121) B5098121
theorem B2265831 : Blo 2265435 2265831 := bstep (se 1 (by rfl) ⟨1699373, by rfl⟩ : syracuseStep 2265831 = 3398747) B3398747
theorem B2549065 : Blo 2265435 2549065 := bbase (se 2 (by rfl) ⟨955899, by rfl⟩ : syracuseStep 2549065 = 1911799) (by norm_num)
theorem B3398753 : Blo 2265435 3398753 := bstep (se 2 (by rfl) ⟨1274532, by rfl⟩ : syracuseStep 3398753 = 2549065) B2549065
theorem B2265835 : Blo 2265435 2265835 := bstep (se 1 (by rfl) ⟨1699376, by rfl⟩ : syracuseStep 2265835 = 3398753) B3398753
theorem B11627317 : Blo 2265435 11627317 := bbase (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) (by norm_num)
theorem B15503089 : Blo 2265435 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B20670785 : Blo 2265435 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B13780523 : Blo 2265435 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B9187015 : Blo 2265435 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B12249353 : Blo 2265435 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B32664941 : Blo 2265435 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B21776627 : Blo 2265435 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B14517751 : Blo 2265435 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B19357001 : Blo 2265435 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B12904667 : Blo 2265435 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B8603111 : Blo 2265435 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B5735407 : Blo 2265435 5735407 := bstep (se 1 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 5735407 = 8603111) B8603111
theorem B7647209 : Blo 2265435 7647209 := bstep (se 2 (by rfl) ⟨2867703, by rfl⟩ : syracuseStep 7647209 = 5735407) B5735407
theorem B5098139 : Blo 2265435 5098139 := bstep (se 1 (by rfl) ⟨3823604, by rfl⟩ : syracuseStep 5098139 = 7647209) B7647209
theorem B3398759 : Blo 2265435 3398759 := bstep (se 1 (by rfl) ⟨2549069, by rfl⟩ : syracuseStep 3398759 = 5098139) B5098139
theorem B2265839 : Blo 2265435 2265839 := bstep (se 1 (by rfl) ⟨1699379, by rfl⟩ : syracuseStep 2265839 = 3398759) B3398759
theorem B3398765 : Blo 2265435 3398765 := bbase (se 3 (by rfl) ⟨637268, by rfl⟩ : syracuseStep 3398765 = 1274537) (by norm_num)
theorem B2265843 : Blo 2265435 2265843 := bstep (se 1 (by rfl) ⟨1699382, by rfl⟩ : syracuseStep 2265843 = 3398765) B3398765
theorem B5098157 : Blo 2265435 5098157 := bbase (se 3 (by rfl) ⟨955904, by rfl⟩ : syracuseStep 5098157 = 1911809) (by norm_num)
theorem B3398771 : Blo 2265435 3398771 := bstep (se 1 (by rfl) ⟨2549078, by rfl⟩ : syracuseStep 3398771 = 5098157) B5098157
theorem B2265847 : Blo 2265435 2265847 := bstep (se 1 (by rfl) ⟨1699385, by rfl⟩ : syracuseStep 2265847 = 3398771) B3398771
theorem B4839277 : Blo 2265435 4839277 := bbase (se 3 (by rfl) ⟨907364, by rfl⟩ : syracuseStep 4839277 = 1814729) (by norm_num)
theorem B6452369 : Blo 2265435 6452369 := bstep (se 2 (by rfl) ⟨2419638, by rfl⟩ : syracuseStep 6452369 = 4839277) B4839277
theorem B4301579 : Blo 2265435 4301579 := bstep (se 1 (by rfl) ⟨3226184, by rfl⟩ : syracuseStep 4301579 = 6452369) B6452369
theorem B2867719 : Blo 2265435 2867719 := bstep (se 1 (by rfl) ⟨2150789, by rfl⟩ : syracuseStep 2867719 = 4301579) B4301579
theorem B3823625 : Blo 2265435 3823625 := bstep (se 2 (by rfl) ⟨1433859, by rfl⟩ : syracuseStep 3823625 = 2867719) B2867719
theorem B2549083 : Blo 2265435 2549083 := bstep (se 1 (by rfl) ⟨1911812, by rfl⟩ : syracuseStep 2549083 = 3823625) B3823625
theorem B3398777 : Blo 2265435 3398777 := bstep (se 2 (by rfl) ⟨1274541, by rfl⟩ : syracuseStep 3398777 = 2549083) B2549083
theorem B2265851 : Blo 2265435 2265851 := bstep (se 1 (by rfl) ⟨1699388, by rfl⟩ : syracuseStep 2265851 = 3398777) B3398777
theorem B8720549 : Blo 2265435 8720549 := bbase (se 4 (by rfl) ⟨817551, by rfl⟩ : syracuseStep 8720549 = 1635103) (by norm_num)
theorem B5813699 : Blo 2265435 5813699 := bstep (se 1 (by rfl) ⟨4360274, by rfl⟩ : syracuseStep 5813699 = 8720549) B8720549
theorem B15503197 : Blo 2265435 15503197 := bstep (se 3 (by rfl) ⟨2906849, by rfl⟩ : syracuseStep 15503197 = 5813699) B5813699
theorem B20670929 : Blo 2265435 20670929 := bstep (se 2 (by rfl) ⟨7751598, by rfl⟩ : syracuseStep 20670929 = 15503197) B15503197
theorem B13780619 : Blo 2265435 13780619 := bstep (se 1 (by rfl) ⟨10335464, by rfl⟩ : syracuseStep 13780619 = 20670929) B20670929
theorem B9187079 : Blo 2265435 9187079 := bstep (se 1 (by rfl) ⟨6890309, by rfl⟩ : syracuseStep 9187079 = 13780619) B13780619
theorem B24498877 : Blo 2265435 24498877 := bstep (se 3 (by rfl) ⟨4593539, by rfl⟩ : syracuseStep 24498877 = 9187079) B9187079
theorem B32665169 : Blo 2265435 32665169 := bstep (se 2 (by rfl) ⟨12249438, by rfl⟩ : syracuseStep 32665169 = 24498877) B24498877
theorem B21776779 : Blo 2265435 21776779 := bstep (se 1 (by rfl) ⟨16332584, by rfl⟩ : syracuseStep 21776779 = 32665169) B32665169
theorem B29035705 : Blo 2265435 29035705 := bstep (se 2 (by rfl) ⟨10888389, by rfl⟩ : syracuseStep 29035705 = 21776779) B21776779
theorem B38714273 : Blo 2265435 38714273 := bstep (se 2 (by rfl) ⟨14517852, by rfl⟩ : syracuseStep 38714273 = 29035705) B29035705
theorem B25809515 : Blo 2265435 25809515 := bstep (se 1 (by rfl) ⟨19357136, by rfl⟩ : syracuseStep 25809515 = 38714273) B38714273
theorem B17206343 : Blo 2265435 17206343 := bstep (se 1 (by rfl) ⟨12904757, by rfl⟩ : syracuseStep 17206343 = 25809515) B25809515
theorem B11470895 : Blo 2265435 11470895 := bstep (se 1 (by rfl) ⟨8603171, by rfl⟩ : syracuseStep 11470895 = 17206343) B17206343
theorem B7647263 : Blo 2265435 7647263 := bstep (se 1 (by rfl) ⟨5735447, by rfl⟩ : syracuseStep 7647263 = 11470895) B11470895
theorem B5098175 : Blo 2265435 5098175 := bstep (se 1 (by rfl) ⟨3823631, by rfl⟩ : syracuseStep 5098175 = 7647263) B7647263
theorem B3398783 : Blo 2265435 3398783 := bstep (se 1 (by rfl) ⟨2549087, by rfl⟩ : syracuseStep 3398783 = 5098175) B5098175
theorem B2265855 : Blo 2265435 2265855 := bstep (se 1 (by rfl) ⟨1699391, by rfl⟩ : syracuseStep 2265855 = 3398783) B3398783
theorem B3398789 : Blo 2265435 3398789 := bbase (se 4 (by rfl) ⟨318636, by rfl⟩ : syracuseStep 3398789 = 637273) (by norm_num)
theorem B2265859 : Blo 2265435 2265859 := bstep (se 1 (by rfl) ⟨1699394, by rfl⟩ : syracuseStep 2265859 = 3398789) B3398789
theorem B3823645 : Blo 2265435 3823645 := bbase (se 3 (by rfl) ⟨716933, by rfl⟩ : syracuseStep 3823645 = 1433867) (by norm_num)
theorem B5098193 : Blo 2265435 5098193 := bstep (se 2 (by rfl) ⟨1911822, by rfl⟩ : syracuseStep 5098193 = 3823645) B3823645
theorem B3398795 : Blo 2265435 3398795 := bstep (se 1 (by rfl) ⟨2549096, by rfl⟩ : syracuseStep 3398795 = 5098193) B5098193
theorem B2265863 : Blo 2265435 2265863 := bstep (se 1 (by rfl) ⟨1699397, by rfl⟩ : syracuseStep 2265863 = 3398795) B3398795
theorem B2549101 : Blo 2265435 2549101 := bbase (se 3 (by rfl) ⟨477956, by rfl⟩ : syracuseStep 2549101 = 955913) (by norm_num)
theorem B3398801 : Blo 2265435 3398801 := bstep (se 2 (by rfl) ⟨1274550, by rfl⟩ : syracuseStep 3398801 = 2549101) B2549101
theorem B2265867 : Blo 2265435 2265867 := bstep (se 1 (by rfl) ⟨1699400, by rfl⟩ : syracuseStep 2265867 = 3398801) B3398801
theorem B7647317 : Blo 2265435 7647317 := bbase (se 8 (by rfl) ⟨44808, by rfl⟩ : syracuseStep 7647317 = 89617) (by norm_num)
theorem B5098211 : Blo 2265435 5098211 := bstep (se 1 (by rfl) ⟨3823658, by rfl⟩ : syracuseStep 5098211 = 7647317) B7647317
theorem B3398807 : Blo 2265435 3398807 := bstep (se 1 (by rfl) ⟨2549105, by rfl⟩ : syracuseStep 3398807 = 5098211) B5098211
theorem B2265871 : Blo 2265435 2265871 := bstep (se 1 (by rfl) ⟨1699403, by rfl⟩ : syracuseStep 2265871 = 3398807) B3398807
theorem B3398813 : Blo 2265435 3398813 := bbase (se 3 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 3398813 = 1274555) (by norm_num)
theorem B2265875 : Blo 2265435 2265875 := bstep (se 1 (by rfl) ⟨1699406, by rfl⟩ : syracuseStep 2265875 = 3398813) B3398813
theorem B5098229 : Blo 2265435 5098229 := bbase (se 5 (by rfl) ⟨238979, by rfl⟩ : syracuseStep 5098229 = 477959) (by norm_num)
theorem B3398819 : Blo 2265435 3398819 := bstep (se 1 (by rfl) ⟨2549114, by rfl⟩ : syracuseStep 3398819 = 5098229) B5098229
theorem B2265879 : Blo 2265435 2265879 := bstep (se 1 (by rfl) ⟨1699409, by rfl⟩ : syracuseStep 2265879 = 3398819) B3398819
theorem B4419821 : Blo 2265435 4419821 := bbase (se 3 (by rfl) ⟨828716, by rfl⟩ : syracuseStep 4419821 = 1657433) (by norm_num)
theorem B2946547 : Blo 2265435 2946547 := bstep (se 1 (by rfl) ⟨2209910, by rfl⟩ : syracuseStep 2946547 = 4419821) B4419821
theorem B15714917 : Blo 2265435 15714917 := bstep (se 4 (by rfl) ⟨1473273, by rfl⟩ : syracuseStep 15714917 = 2946547) B2946547
theorem B10476611 : Blo 2265435 10476611 := bstep (se 1 (by rfl) ⟨7857458, by rfl⟩ : syracuseStep 10476611 = 15714917) B15714917
theorem B6984407 : Blo 2265435 6984407 := bstep (se 1 (by rfl) ⟨5238305, by rfl⟩ : syracuseStep 6984407 = 10476611) B10476611
theorem B18625085 : Blo 2265435 18625085 := bstep (se 3 (by rfl) ⟨3492203, by rfl⟩ : syracuseStep 18625085 = 6984407) B6984407
theorem B12416723 : Blo 2265435 12416723 := bstep (se 1 (by rfl) ⟨9312542, by rfl⟩ : syracuseStep 12416723 = 18625085) B18625085
theorem B8277815 : Blo 2265435 8277815 := bstep (se 1 (by rfl) ⟨6208361, by rfl⟩ : syracuseStep 8277815 = 12416723) B12416723
theorem B5518543 : Blo 2265435 5518543 := bstep (se 1 (by rfl) ⟨4138907, by rfl⟩ : syracuseStep 5518543 = 8277815) B8277815
theorem B7358057 : Blo 2265435 7358057 := bstep (se 2 (by rfl) ⟨2759271, by rfl⟩ : syracuseStep 7358057 = 5518543) B5518543
theorem B4905371 : Blo 2265435 4905371 := bstep (se 1 (by rfl) ⟨3679028, by rfl⟩ : syracuseStep 4905371 = 7358057) B7358057
theorem B13080989 : Blo 2265435 13080989 := bstep (se 3 (by rfl) ⟨2452685, by rfl⟩ : syracuseStep 13080989 = 4905371) B4905371
theorem B8720659 : Blo 2265435 8720659 := bstep (se 1 (by rfl) ⟨6540494, by rfl⟩ : syracuseStep 8720659 = 13080989) B13080989
theorem B11627545 : Blo 2265435 11627545 := bstep (se 2 (by rfl) ⟨4360329, by rfl⟩ : syracuseStep 11627545 = 8720659) B8720659
theorem B15503393 : Blo 2265435 15503393 := bstep (se 2 (by rfl) ⟨5813772, by rfl⟩ : syracuseStep 15503393 = 11627545) B11627545
theorem B10335595 : Blo 2265435 10335595 := bstep (se 1 (by rfl) ⟨7751696, by rfl⟩ : syracuseStep 10335595 = 15503393) B15503393
theorem B13780793 : Blo 2265435 13780793 := bstep (se 2 (by rfl) ⟨5167797, by rfl⟩ : syracuseStep 13780793 = 10335595) B10335595
theorem B9187195 : Blo 2265435 9187195 := bstep (se 1 (by rfl) ⟨6890396, by rfl⟩ : syracuseStep 9187195 = 13780793) B13780793
theorem B12249593 : Blo 2265435 12249593 := bstep (se 2 (by rfl) ⟨4593597, by rfl⟩ : syracuseStep 12249593 = 9187195) B9187195
theorem B8166395 : Blo 2265435 8166395 := bstep (se 1 (by rfl) ⟨6124796, by rfl⟩ : syracuseStep 8166395 = 12249593) B12249593
theorem B5444263 : Blo 2265435 5444263 := bstep (se 1 (by rfl) ⟨4083197, by rfl⟩ : syracuseStep 5444263 = 8166395) B8166395
theorem B29036069 : Blo 2265435 29036069 := bstep (se 4 (by rfl) ⟨2722131, by rfl⟩ : syracuseStep 29036069 = 5444263) B5444263
theorem B19357379 : Blo 2265435 19357379 := bstep (se 1 (by rfl) ⟨14518034, by rfl⟩ : syracuseStep 19357379 = 29036069) B29036069
theorem B12904919 : Blo 2265435 12904919 := bstep (se 1 (by rfl) ⟨9678689, by rfl⟩ : syracuseStep 12904919 = 19357379) B19357379
theorem B8603279 : Blo 2265435 8603279 := bstep (se 1 (by rfl) ⟨6452459, by rfl⟩ : syracuseStep 8603279 = 12904919) B12904919
theorem B5735519 : Blo 2265435 5735519 := bstep (se 1 (by rfl) ⟨4301639, by rfl⟩ : syracuseStep 5735519 = 8603279) B8603279
theorem B3823679 : Blo 2265435 3823679 := bstep (se 1 (by rfl) ⟨2867759, by rfl⟩ : syracuseStep 3823679 = 5735519) B5735519
theorem B2549119 : Blo 2265435 2549119 := bstep (se 1 (by rfl) ⟨1911839, by rfl⟩ : syracuseStep 2549119 = 3823679) B3823679
theorem B3398825 : Blo 2265435 3398825 := bstep (se 2 (by rfl) ⟨1274559, by rfl⟩ : syracuseStep 3398825 = 2549119) B2549119
theorem B2265883 : Blo 2265435 2265883 := bstep (se 1 (by rfl) ⟨1699412, by rfl⟩ : syracuseStep 2265883 = 3398825) B3398825
theorem B4083205 : Blo 2265435 4083205 := bbase (se 4 (by rfl) ⟨382800, by rfl⟩ : syracuseStep 4083205 = 765601) (by norm_num)
theorem B5444273 : Blo 2265435 5444273 := bstep (se 2 (by rfl) ⟨2041602, by rfl⟩ : syracuseStep 5444273 = 4083205) B4083205
theorem B3629515 : Blo 2265435 3629515 := bstep (se 1 (by rfl) ⟨2722136, by rfl⟩ : syracuseStep 3629515 = 5444273) B5444273
theorem B4839353 : Blo 2265435 4839353 := bstep (se 2 (by rfl) ⟨1814757, by rfl⟩ : syracuseStep 4839353 = 3629515) B3629515
theorem B3226235 : Blo 2265435 3226235 := bstep (se 1 (by rfl) ⟨2419676, by rfl⟩ : syracuseStep 3226235 = 4839353) B4839353
theorem B8603293 : Blo 2265435 8603293 := bstep (se 3 (by rfl) ⟨1613117, by rfl⟩ : syracuseStep 8603293 = 3226235) B3226235
theorem B11471057 : Blo 2265435 11471057 := bstep (se 2 (by rfl) ⟨4301646, by rfl⟩ : syracuseStep 11471057 = 8603293) B8603293
theorem B7647371 : Blo 2265435 7647371 := bstep (se 1 (by rfl) ⟨5735528, by rfl⟩ : syracuseStep 7647371 = 11471057) B11471057
theorem B5098247 : Blo 2265435 5098247 := bstep (se 1 (by rfl) ⟨3823685, by rfl⟩ : syracuseStep 5098247 = 7647371) B7647371
theorem B3398831 : Blo 2265435 3398831 := bstep (se 1 (by rfl) ⟨2549123, by rfl⟩ : syracuseStep 3398831 = 5098247) B5098247
theorem B2265887 : Blo 2265435 2265887 := bstep (se 1 (by rfl) ⟨1699415, by rfl⟩ : syracuseStep 2265887 = 3398831) B3398831
theorem B3398837 : Blo 2265435 3398837 := bbase (se 5 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 3398837 = 318641) (by norm_num)
theorem B2265891 : Blo 2265435 2265891 := bstep (se 1 (by rfl) ⟨1699418, by rfl⟩ : syracuseStep 2265891 = 3398837) B3398837
theorem B5735549 : Blo 2265435 5735549 := bbase (se 3 (by rfl) ⟨1075415, by rfl⟩ : syracuseStep 5735549 = 2150831) (by norm_num)
theorem B3823699 : Blo 2265435 3823699 := bstep (se 1 (by rfl) ⟨2867774, by rfl⟩ : syracuseStep 3823699 = 5735549) B5735549
theorem B5098265 : Blo 2265435 5098265 := bstep (se 2 (by rfl) ⟨1911849, by rfl⟩ : syracuseStep 5098265 = 3823699) B3823699
theorem B3398843 : Blo 2265435 3398843 := bstep (se 1 (by rfl) ⟨2549132, by rfl⟩ : syracuseStep 3398843 = 5098265) B5098265
theorem B2265895 : Blo 2265435 2265895 := bstep (se 1 (by rfl) ⟨1699421, by rfl⟩ : syracuseStep 2265895 = 3398843) B3398843
theorem B2549137 : Blo 2265435 2549137 := bbase (se 2 (by rfl) ⟨955926, by rfl⟩ : syracuseStep 2549137 = 1911853) (by norm_num)
theorem B3398849 : Blo 2265435 3398849 := bstep (se 2 (by rfl) ⟨1274568, by rfl⟩ : syracuseStep 3398849 = 2549137) B2549137
theorem B2265899 : Blo 2265435 2265899 := bstep (se 1 (by rfl) ⟨1699424, by rfl⟩ : syracuseStep 2265899 = 3398849) B3398849
theorem B4301677 : Blo 2265435 4301677 := bbase (se 3 (by rfl) ⟨806564, by rfl⟩ : syracuseStep 4301677 = 1613129) (by norm_num)
theorem B5735569 : Blo 2265435 5735569 := bstep (se 2 (by rfl) ⟨2150838, by rfl⟩ : syracuseStep 5735569 = 4301677) B4301677
theorem B7647425 : Blo 2265435 7647425 := bstep (se 2 (by rfl) ⟨2867784, by rfl⟩ : syracuseStep 7647425 = 5735569) B5735569
theorem B5098283 : Blo 2265435 5098283 := bstep (se 1 (by rfl) ⟨3823712, by rfl⟩ : syracuseStep 5098283 = 7647425) B7647425
theorem B3398855 : Blo 2265435 3398855 := bstep (se 1 (by rfl) ⟨2549141, by rfl⟩ : syracuseStep 3398855 = 5098283) B5098283
theorem B2265903 : Blo 2265435 2265903 := bstep (se 1 (by rfl) ⟨1699427, by rfl⟩ : syracuseStep 2265903 = 3398855) B3398855
theorem B3398861 : Blo 2265435 3398861 := bbase (se 3 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 3398861 = 1274573) (by norm_num)
theorem B2265907 : Blo 2265435 2265907 := bstep (se 1 (by rfl) ⟨1699430, by rfl⟩ : syracuseStep 2265907 = 3398861) B3398861
theorem B5098301 : Blo 2265435 5098301 := bbase (se 3 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 5098301 = 1911863) (by norm_num)
theorem B3398867 : Blo 2265435 3398867 := bstep (se 1 (by rfl) ⟨2549150, by rfl⟩ : syracuseStep 3398867 = 5098301) B5098301
theorem B2265911 : Blo 2265435 2265911 := bstep (se 1 (by rfl) ⟨1699433, by rfl⟩ : syracuseStep 2265911 = 3398867) B3398867
theorem B3823733 : Blo 2265435 3823733 := bbase (se 5 (by rfl) ⟨179237, by rfl⟩ : syracuseStep 3823733 = 358475) (by norm_num)
theorem B2549155 : Blo 2265435 2549155 := bstep (se 1 (by rfl) ⟨1911866, by rfl⟩ : syracuseStep 2549155 = 3823733) B3823733
theorem B3398873 : Blo 2265435 3398873 := bstep (se 2 (by rfl) ⟨1274577, by rfl⟩ : syracuseStep 3398873 = 2549155) B2549155
theorem B2265915 : Blo 2265435 2265915 := bstep (se 1 (by rfl) ⟨1699436, by rfl⟩ : syracuseStep 2265915 = 3398873) B3398873
theorem B4839421 : Blo 2265435 4839421 := bbase (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) (by norm_num)
theorem B6452561 : Blo 2265435 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B17206829 : Blo 2265435 17206829 := bstep (se 3 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 17206829 = 6452561) B6452561
theorem B11471219 : Blo 2265435 11471219 := bstep (se 1 (by rfl) ⟨8603414, by rfl⟩ : syracuseStep 11471219 = 17206829) B17206829
theorem B7647479 : Blo 2265435 7647479 := bstep (se 1 (by rfl) ⟨5735609, by rfl⟩ : syracuseStep 7647479 = 11471219) B11471219
theorem B5098319 : Blo 2265435 5098319 := bstep (se 1 (by rfl) ⟨3823739, by rfl⟩ : syracuseStep 5098319 = 7647479) B7647479
theorem B3398879 : Blo 2265435 3398879 := bstep (se 1 (by rfl) ⟨2549159, by rfl⟩ : syracuseStep 3398879 = 5098319) B5098319
theorem B2265919 : Blo 2265435 2265919 := bstep (se 1 (by rfl) ⟨1699439, by rfl⟩ : syracuseStep 2265919 = 3398879) B3398879
theorem B3398885 : Blo 2265435 3398885 := bbase (se 4 (by rfl) ⟨318645, by rfl⟩ : syracuseStep 3398885 = 637291) (by norm_num)
theorem B2265923 : Blo 2265435 2265923 := bstep (se 1 (by rfl) ⟨1699442, by rfl⟩ : syracuseStep 2265923 = 3398885) B3398885
theorem B16333109 : Blo 2265435 16333109 := bbase (se 5 (by rfl) ⟨765614, by rfl⟩ : syracuseStep 16333109 = 1531229) (by norm_num)
theorem B10888739 : Blo 2265435 10888739 := bstep (se 1 (by rfl) ⟨8166554, by rfl⟩ : syracuseStep 10888739 = 16333109) B16333109
theorem B7259159 : Blo 2265435 7259159 := bstep (se 1 (by rfl) ⟨5444369, by rfl⟩ : syracuseStep 7259159 = 10888739) B10888739
theorem B4839439 : Blo 2265435 4839439 := bstep (se 1 (by rfl) ⟨3629579, by rfl⟩ : syracuseStep 4839439 = 7259159) B7259159
theorem B6452585 : Blo 2265435 6452585 := bstep (se 2 (by rfl) ⟨2419719, by rfl⟩ : syracuseStep 6452585 = 4839439) B4839439
theorem B4301723 : Blo 2265435 4301723 := bstep (se 1 (by rfl) ⟨3226292, by rfl⟩ : syracuseStep 4301723 = 6452585) B6452585
theorem B2867815 : Blo 2265435 2867815 := bstep (se 1 (by rfl) ⟨2150861, by rfl⟩ : syracuseStep 2867815 = 4301723) B4301723
theorem B3823753 : Blo 2265435 3823753 := bstep (se 2 (by rfl) ⟨1433907, by rfl⟩ : syracuseStep 3823753 = 2867815) B2867815
theorem B5098337 : Blo 2265435 5098337 := bstep (se 2 (by rfl) ⟨1911876, by rfl⟩ : syracuseStep 5098337 = 3823753) B3823753
theorem B3398891 : Blo 2265435 3398891 := bstep (se 1 (by rfl) ⟨2549168, by rfl⟩ : syracuseStep 3398891 = 5098337) B5098337
theorem B2265927 : Blo 2265435 2265927 := bstep (se 1 (by rfl) ⟨1699445, by rfl⟩ : syracuseStep 2265927 = 3398891) B3398891
theorem B2549173 : Blo 2265435 2549173 := bbase (se 5 (by rfl) ⟨119492, by rfl⟩ : syracuseStep 2549173 = 238985) (by norm_num)
theorem B3398897 : Blo 2265435 3398897 := bstep (se 2 (by rfl) ⟨1274586, by rfl⟩ : syracuseStep 3398897 = 2549173) B2549173
theorem B2265931 : Blo 2265435 2265931 := bstep (se 1 (by rfl) ⟨1699448, by rfl⟩ : syracuseStep 2265931 = 3398897) B3398897
theorem B2867825 : Blo 2265435 2867825 := bbase (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) (by norm_num)
theorem B7647533 : Blo 2265435 7647533 := bstep (se 3 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 7647533 = 2867825) B2867825
theorem B5098355 : Blo 2265435 5098355 := bstep (se 1 (by rfl) ⟨3823766, by rfl⟩ : syracuseStep 5098355 = 7647533) B7647533
theorem B3398903 : Blo 2265435 3398903 := bstep (se 1 (by rfl) ⟨2549177, by rfl⟩ : syracuseStep 3398903 = 5098355) B5098355
theorem B2265935 : Blo 2265435 2265935 := bstep (se 1 (by rfl) ⟨1699451, by rfl⟩ : syracuseStep 2265935 = 3398903) B3398903
theorem B3398909 : Blo 2265435 3398909 := bbase (se 3 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 3398909 = 1274591) (by norm_num)
theorem B2265939 : Blo 2265435 2265939 := bstep (se 1 (by rfl) ⟨1699454, by rfl⟩ : syracuseStep 2265939 = 3398909) B3398909
theorem B5098373 : Blo 2265435 5098373 := bbase (se 4 (by rfl) ⟨477972, by rfl⟩ : syracuseStep 5098373 = 955945) (by norm_num)
theorem B3398915 : Blo 2265435 3398915 := bstep (se 1 (by rfl) ⟨2549186, by rfl⟩ : syracuseStep 3398915 = 5098373) B5098373
theorem B2265943 : Blo 2265435 2265943 := bstep (se 1 (by rfl) ⟨1699457, by rfl⟩ : syracuseStep 2265943 = 3398915) B3398915
theorem B2419741 : Blo 2265435 2419741 := bbase (se 3 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 2419741 = 907403) (by norm_num)
theorem B3226321 : Blo 2265435 3226321 := bstep (se 2 (by rfl) ⟨1209870, by rfl⟩ : syracuseStep 3226321 = 2419741) B2419741
theorem B4301761 : Blo 2265435 4301761 := bstep (se 2 (by rfl) ⟨1613160, by rfl⟩ : syracuseStep 4301761 = 3226321) B3226321
theorem B5735681 : Blo 2265435 5735681 := bstep (se 2 (by rfl) ⟨2150880, by rfl⟩ : syracuseStep 5735681 = 4301761) B4301761
theorem B3823787 : Blo 2265435 3823787 := bstep (se 1 (by rfl) ⟨2867840, by rfl⟩ : syracuseStep 3823787 = 5735681) B5735681
theorem B2549191 : Blo 2265435 2549191 := bstep (se 1 (by rfl) ⟨1911893, by rfl⟩ : syracuseStep 2549191 = 3823787) B3823787
theorem B3398921 : Blo 2265435 3398921 := bstep (se 2 (by rfl) ⟨1274595, by rfl⟩ : syracuseStep 3398921 = 2549191) B2549191
theorem B2265947 : Blo 2265435 2265947 := bstep (se 1 (by rfl) ⟨1699460, by rfl⟩ : syracuseStep 2265947 = 3398921) B3398921
theorem B11471381 : Blo 2265435 11471381 := bbase (se 6 (by rfl) ⟨268860, by rfl⟩ : syracuseStep 11471381 = 537721) (by norm_num)
theorem B7647587 : Blo 2265435 7647587 := bstep (se 1 (by rfl) ⟨5735690, by rfl⟩ : syracuseStep 7647587 = 11471381) B11471381
theorem B5098391 : Blo 2265435 5098391 := bstep (se 1 (by rfl) ⟨3823793, by rfl⟩ : syracuseStep 5098391 = 7647587) B7647587
theorem B3398927 : Blo 2265435 3398927 := bstep (se 1 (by rfl) ⟨2549195, by rfl⟩ : syracuseStep 3398927 = 5098391) B5098391
theorem B2265951 : Blo 2265435 2265951 := bstep (se 1 (by rfl) ⟨1699463, by rfl⟩ : syracuseStep 2265951 = 3398927) B3398927
theorem B3398933 : Blo 2265435 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B2265955 : Blo 2265435 2265955 := bstep (se 1 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 2265955 = 3398933) B3398933
theorem B21777781 : Blo 2265435 21777781 := bbase (se 5 (by rfl) ⟨1020833, by rfl⟩ : syracuseStep 21777781 = 2041667) (by norm_num)
theorem B29037041 : Blo 2265435 29037041 := bstep (se 2 (by rfl) ⟨10888890, by rfl⟩ : syracuseStep 29037041 = 21777781) B21777781
theorem B19358027 : Blo 2265435 19358027 := bstep (se 1 (by rfl) ⟨14518520, by rfl⟩ : syracuseStep 19358027 = 29037041) B29037041
theorem B12905351 : Blo 2265435 12905351 := bstep (se 1 (by rfl) ⟨9679013, by rfl⟩ : syracuseStep 12905351 = 19358027) B19358027
theorem B8603567 : Blo 2265435 8603567 := bstep (se 1 (by rfl) ⟨6452675, by rfl⟩ : syracuseStep 8603567 = 12905351) B12905351
theorem B5735711 : Blo 2265435 5735711 := bstep (se 1 (by rfl) ⟨4301783, by rfl⟩ : syracuseStep 5735711 = 8603567) B8603567
theorem B3823807 : Blo 2265435 3823807 := bstep (se 1 (by rfl) ⟨2867855, by rfl⟩ : syracuseStep 3823807 = 5735711) B5735711
theorem B5098409 : Blo 2265435 5098409 := bstep (se 2 (by rfl) ⟨1911903, by rfl⟩ : syracuseStep 5098409 = 3823807) B3823807
theorem B3398939 : Blo 2265435 3398939 := bstep (se 1 (by rfl) ⟨2549204, by rfl⟩ : syracuseStep 3398939 = 5098409) B5098409
theorem B2265959 : Blo 2265435 2265959 := bstep (se 1 (by rfl) ⟨1699469, by rfl⟩ : syracuseStep 2265959 = 3398939) B3398939
theorem B2549209 : Blo 2265435 2549209 := bbase (se 2 (by rfl) ⟨955953, by rfl⟩ : syracuseStep 2549209 = 1911907) (by norm_num)
theorem B3398945 : Blo 2265435 3398945 := bstep (se 2 (by rfl) ⟨1274604, by rfl⟩ : syracuseStep 3398945 = 2549209) B2549209
theorem B2265963 : Blo 2265435 2265963 := bstep (se 1 (by rfl) ⟨1699472, by rfl⟩ : syracuseStep 2265963 = 3398945) B3398945
theorem B3226349 : Blo 2265435 3226349 := bbase (se 3 (by rfl) ⟨604940, by rfl⟩ : syracuseStep 3226349 = 1209881) (by norm_num)
theorem B8603597 : Blo 2265435 8603597 := bstep (se 3 (by rfl) ⟨1613174, by rfl⟩ : syracuseStep 8603597 = 3226349) B3226349
theorem B5735731 : Blo 2265435 5735731 := bstep (se 1 (by rfl) ⟨4301798, by rfl⟩ : syracuseStep 5735731 = 8603597) B8603597
theorem B7647641 : Blo 2265435 7647641 := bstep (se 2 (by rfl) ⟨2867865, by rfl⟩ : syracuseStep 7647641 = 5735731) B5735731
theorem B5098427 : Blo 2265435 5098427 := bstep (se 1 (by rfl) ⟨3823820, by rfl⟩ : syracuseStep 5098427 = 7647641) B7647641
theorem B3398951 : Blo 2265435 3398951 := bstep (se 1 (by rfl) ⟨2549213, by rfl⟩ : syracuseStep 3398951 = 5098427) B5098427
theorem B2265967 : Blo 2265435 2265967 := bstep (se 1 (by rfl) ⟨1699475, by rfl⟩ : syracuseStep 2265967 = 3398951) B3398951
theorem B3398957 : Blo 2265435 3398957 := bbase (se 3 (by rfl) ⟨637304, by rfl⟩ : syracuseStep 3398957 = 1274609) (by norm_num)
theorem B2265971 : Blo 2265435 2265971 := bstep (se 1 (by rfl) ⟨1699478, by rfl⟩ : syracuseStep 2265971 = 3398957) B3398957
theorem B5098445 : Blo 2265435 5098445 := bbase (se 3 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 5098445 = 1911917) (by norm_num)
theorem B3398963 : Blo 2265435 3398963 := bstep (se 1 (by rfl) ⟨2549222, by rfl⟩ : syracuseStep 3398963 = 5098445) B5098445
theorem B2265975 : Blo 2265435 2265975 := bstep (se 1 (by rfl) ⟨1699481, by rfl⟩ : syracuseStep 2265975 = 3398963) B3398963
theorem B2867881 : Blo 2265435 2867881 := bbase (se 2 (by rfl) ⟨1075455, by rfl⟩ : syracuseStep 2867881 = 2150911) (by norm_num)
theorem B3823841 : Blo 2265435 3823841 := bstep (se 2 (by rfl) ⟨1433940, by rfl⟩ : syracuseStep 3823841 = 2867881) B2867881
theorem B2549227 : Blo 2265435 2549227 := bstep (se 1 (by rfl) ⟨1911920, by rfl⟩ : syracuseStep 2549227 = 3823841) B3823841
theorem B3398969 : Blo 2265435 3398969 := bstep (se 2 (by rfl) ⟨1274613, by rfl⟩ : syracuseStep 3398969 = 2549227) B2549227
theorem B2265979 : Blo 2265435 2265979 := bstep (se 1 (by rfl) ⟨1699484, by rfl⟩ : syracuseStep 2265979 = 3398969) B3398969
theorem B3062533 : Blo 2265435 3062533 := bbase (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) (by norm_num)
theorem B4083377 : Blo 2265435 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B10889005 : Blo 2265435 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B14518673 : Blo 2265435 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B9679115 : Blo 2265435 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B25810973 : Blo 2265435 25810973 := bstep (se 3 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 25810973 = 9679115) B9679115
theorem B17207315 : Blo 2265435 17207315 := bstep (se 1 (by rfl) ⟨12905486, by rfl⟩ : syracuseStep 17207315 = 25810973) B25810973
theorem B11471543 : Blo 2265435 11471543 := bstep (se 1 (by rfl) ⟨8603657, by rfl⟩ : syracuseStep 11471543 = 17207315) B17207315
theorem B7647695 : Blo 2265435 7647695 := bstep (se 1 (by rfl) ⟨5735771, by rfl⟩ : syracuseStep 7647695 = 11471543) B11471543
theorem B5098463 : Blo 2265435 5098463 := bstep (se 1 (by rfl) ⟨3823847, by rfl⟩ : syracuseStep 5098463 = 7647695) B7647695
theorem B3398975 : Blo 2265435 3398975 := bstep (se 1 (by rfl) ⟨2549231, by rfl⟩ : syracuseStep 3398975 = 5098463) B5098463
theorem B2265983 : Blo 2265435 2265983 := bstep (se 1 (by rfl) ⟨1699487, by rfl⟩ : syracuseStep 2265983 = 3398975) B3398975
theorem B3398981 : Blo 2265435 3398981 := bbase (se 4 (by rfl) ⟨318654, by rfl⟩ : syracuseStep 3398981 = 637309) (by norm_num)
theorem B2265987 : Blo 2265435 2265987 := bstep (se 1 (by rfl) ⟨1699490, by rfl⟩ : syracuseStep 2265987 = 3398981) B3398981
theorem B3823861 : Blo 2265435 3823861 := bbase (se 5 (by rfl) ⟨179243, by rfl⟩ : syracuseStep 3823861 = 358487) (by norm_num)
theorem B5098481 : Blo 2265435 5098481 := bstep (se 2 (by rfl) ⟨1911930, by rfl⟩ : syracuseStep 5098481 = 3823861) B3823861
theorem B3398987 : Blo 2265435 3398987 := bstep (se 1 (by rfl) ⟨2549240, by rfl⟩ : syracuseStep 3398987 = 5098481) B5098481
theorem B2265991 : Blo 2265435 2265991 := bstep (se 1 (by rfl) ⟨1699493, by rfl⟩ : syracuseStep 2265991 = 3398987) B3398987
theorem B2549245 : Blo 2265435 2549245 := bbase (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) (by norm_num)
theorem B3398993 : Blo 2265435 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B2265995 : Blo 2265435 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B7647749 : Blo 2265435 7647749 := bbase (se 4 (by rfl) ⟨716976, by rfl⟩ : syracuseStep 7647749 = 1433953) (by norm_num)
theorem B5098499 : Blo 2265435 5098499 := bstep (se 1 (by rfl) ⟨3823874, by rfl⟩ : syracuseStep 5098499 = 7647749) B7647749
theorem B3398999 : Blo 2265435 3398999 := bstep (se 1 (by rfl) ⟨2549249, by rfl⟩ : syracuseStep 3398999 = 5098499) B5098499
theorem B2265999 : Blo 2265435 2265999 := bstep (se 1 (by rfl) ⟨1699499, by rfl⟩ : syracuseStep 2265999 = 3398999) B3398999
theorem B3399005 : Blo 2265435 3399005 := bbase (se 3 (by rfl) ⟨637313, by rfl⟩ : syracuseStep 3399005 = 1274627) (by norm_num)
theorem B2266003 : Blo 2265435 2266003 := bstep (se 1 (by rfl) ⟨1699502, by rfl⟩ : syracuseStep 2266003 = 3399005) B3399005
theorem B5098517 : Blo 2265435 5098517 := bbase (se 6 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 5098517 = 238993) (by norm_num)
theorem B3399011 : Blo 2265435 3399011 := bstep (se 1 (by rfl) ⟨2549258, by rfl⟩ : syracuseStep 3399011 = 5098517) B5098517
theorem B2266007 : Blo 2265435 2266007 := bstep (se 1 (by rfl) ⟨1699505, by rfl⟩ : syracuseStep 2266007 = 3399011) B3399011
theorem B8603765 : Blo 2265435 8603765 := bbase (se 5 (by rfl) ⟨403301, by rfl⟩ : syracuseStep 8603765 = 806603) (by norm_num)
theorem B5735843 : Blo 2265435 5735843 := bstep (se 1 (by rfl) ⟨4301882, by rfl⟩ : syracuseStep 5735843 = 8603765) B8603765
theorem B3823895 : Blo 2265435 3823895 := bstep (se 1 (by rfl) ⟨2867921, by rfl⟩ : syracuseStep 3823895 = 5735843) B5735843
theorem B2549263 : Blo 2265435 2549263 := bstep (se 1 (by rfl) ⟨1911947, by rfl⟩ : syracuseStep 2549263 = 3823895) B3823895
theorem B3399017 : Blo 2265435 3399017 := bstep (se 2 (by rfl) ⟨1274631, by rfl⟩ : syracuseStep 3399017 = 2549263) B2549263
theorem B2266011 : Blo 2265435 2266011 := bstep (se 1 (by rfl) ⟨1699508, by rfl⟩ : syracuseStep 2266011 = 3399017) B3399017
theorem B2419813 : Blo 2265435 2419813 := bbase (se 4 (by rfl) ⟨226857, by rfl⟩ : syracuseStep 2419813 = 453715) (by norm_num)
theorem B12905669 : Blo 2265435 12905669 := bstep (se 4 (by rfl) ⟨1209906, by rfl⟩ : syracuseStep 12905669 = 2419813) B2419813
theorem B8603779 : Blo 2265435 8603779 := bstep (se 1 (by rfl) ⟨6452834, by rfl⟩ : syracuseStep 8603779 = 12905669) B12905669
theorem B11471705 : Blo 2265435 11471705 := bstep (se 2 (by rfl) ⟨4301889, by rfl⟩ : syracuseStep 11471705 = 8603779) B8603779
theorem B7647803 : Blo 2265435 7647803 := bstep (se 1 (by rfl) ⟨5735852, by rfl⟩ : syracuseStep 7647803 = 11471705) B11471705
theorem B5098535 : Blo 2265435 5098535 := bstep (se 1 (by rfl) ⟨3823901, by rfl⟩ : syracuseStep 5098535 = 7647803) B7647803
theorem B3399023 : Blo 2265435 3399023 := bstep (se 1 (by rfl) ⟨2549267, by rfl⟩ : syracuseStep 3399023 = 5098535) B5098535
theorem B2266015 : Blo 2265435 2266015 := bstep (se 1 (by rfl) ⟨1699511, by rfl⟩ : syracuseStep 2266015 = 3399023) B3399023
theorem B3399029 : Blo 2265435 3399029 := bbase (se 5 (by rfl) ⟨159329, by rfl⟩ : syracuseStep 3399029 = 318659) (by norm_num)
theorem B2266019 : Blo 2265435 2266019 := bstep (se 1 (by rfl) ⟨1699514, by rfl⟩ : syracuseStep 2266019 = 3399029) B3399029
theorem B3226429 : Blo 2265435 3226429 := bbase (se 3 (by rfl) ⟨604955, by rfl⟩ : syracuseStep 3226429 = 1209911) (by norm_num)
theorem B4301905 : Blo 2265435 4301905 := bstep (se 2 (by rfl) ⟨1613214, by rfl⟩ : syracuseStep 4301905 = 3226429) B3226429
theorem B5735873 : Blo 2265435 5735873 := bstep (se 2 (by rfl) ⟨2150952, by rfl⟩ : syracuseStep 5735873 = 4301905) B4301905
theorem B3823915 : Blo 2265435 3823915 := bstep (se 1 (by rfl) ⟨2867936, by rfl⟩ : syracuseStep 3823915 = 5735873) B5735873
theorem B5098553 : Blo 2265435 5098553 := bstep (se 2 (by rfl) ⟨1911957, by rfl⟩ : syracuseStep 5098553 = 3823915) B3823915
theorem B3399035 : Blo 2265435 3399035 := bstep (se 1 (by rfl) ⟨2549276, by rfl⟩ : syracuseStep 3399035 = 5098553) B5098553
theorem B2266023 : Blo 2265435 2266023 := bstep (se 1 (by rfl) ⟨1699517, by rfl⟩ : syracuseStep 2266023 = 3399035) B3399035
theorem B2549281 : Blo 2265435 2549281 := bbase (se 2 (by rfl) ⟨955980, by rfl⟩ : syracuseStep 2549281 = 1911961) (by norm_num)
theorem B3399041 : Blo 2265435 3399041 := bstep (se 2 (by rfl) ⟨1274640, by rfl⟩ : syracuseStep 3399041 = 2549281) B2549281
theorem B2266027 : Blo 2265435 2266027 := bstep (se 1 (by rfl) ⟨1699520, by rfl⟩ : syracuseStep 2266027 = 3399041) B3399041
theorem B5735893 : Blo 2265435 5735893 := bbase (se 7 (by rfl) ⟨67217, by rfl⟩ : syracuseStep 5735893 = 134435) (by norm_num)
theorem B7647857 : Blo 2265435 7647857 := bstep (se 2 (by rfl) ⟨2867946, by rfl⟩ : syracuseStep 7647857 = 5735893) B5735893
theorem B5098571 : Blo 2265435 5098571 := bstep (se 1 (by rfl) ⟨3823928, by rfl⟩ : syracuseStep 5098571 = 7647857) B7647857
theorem B3399047 : Blo 2265435 3399047 := bstep (se 1 (by rfl) ⟨2549285, by rfl⟩ : syracuseStep 3399047 = 5098571) B5098571
theorem B2266031 : Blo 2265435 2266031 := bstep (se 1 (by rfl) ⟨1699523, by rfl⟩ : syracuseStep 2266031 = 3399047) B3399047
theorem B3399053 : Blo 2265435 3399053 := bbase (se 3 (by rfl) ⟨637322, by rfl⟩ : syracuseStep 3399053 = 1274645) (by norm_num)
theorem B2266035 : Blo 2265435 2266035 := bstep (se 1 (by rfl) ⟨1699526, by rfl⟩ : syracuseStep 2266035 = 3399053) B3399053
theorem B5098589 : Blo 2265435 5098589 := bbase (se 3 (by rfl) ⟨955985, by rfl⟩ : syracuseStep 5098589 = 1911971) (by norm_num)
theorem B3399059 : Blo 2265435 3399059 := bstep (se 1 (by rfl) ⟨2549294, by rfl⟩ : syracuseStep 3399059 = 5098589) B5098589
theorem B2266039 : Blo 2265435 2266039 := bstep (se 1 (by rfl) ⟨1699529, by rfl⟩ : syracuseStep 2266039 = 3399059) B3399059
theorem B3823949 : Blo 2265435 3823949 := bbase (se 3 (by rfl) ⟨716990, by rfl⟩ : syracuseStep 3823949 = 1433981) (by norm_num)
theorem B2549299 : Blo 2265435 2549299 := bstep (se 1 (by rfl) ⟨1911974, by rfl⟩ : syracuseStep 2549299 = 3823949) B3823949
theorem B3399065 : Blo 2265435 3399065 := bstep (se 2 (by rfl) ⟨1274649, by rfl⟩ : syracuseStep 3399065 = 2549299) B2549299
theorem B2266043 : Blo 2265435 2266043 := bstep (se 1 (by rfl) ⟨1699532, by rfl⟩ : syracuseStep 2266043 = 3399065) B3399065
theorem B4360645 : Blo 2265435 4360645 := bbase (se 4 (by rfl) ⟨408810, by rfl⟩ : syracuseStep 4360645 = 817621) (by norm_num)
theorem B5814193 : Blo 2265435 5814193 := bstep (se 2 (by rfl) ⟨2180322, by rfl⟩ : syracuseStep 5814193 = 4360645) B4360645
theorem B7752257 : Blo 2265435 7752257 := bstep (se 2 (by rfl) ⟨2907096, by rfl⟩ : syracuseStep 7752257 = 5814193) B5814193
theorem B5168171 : Blo 2265435 5168171 := bstep (se 1 (by rfl) ⟨3876128, by rfl⟩ : syracuseStep 5168171 = 7752257) B7752257
theorem B3445447 : Blo 2265435 3445447 := bstep (se 1 (by rfl) ⟨2584085, by rfl⟩ : syracuseStep 3445447 = 5168171) B5168171
theorem B4593929 : Blo 2265435 4593929 := bstep (se 2 (by rfl) ⟨1722723, by rfl⟩ : syracuseStep 4593929 = 3445447) B3445447
theorem B12250477 : Blo 2265435 12250477 := bstep (se 3 (by rfl) ⟨2296964, by rfl⟩ : syracuseStep 12250477 = 4593929) B4593929
theorem B16333969 : Blo 2265435 16333969 := bstep (se 2 (by rfl) ⟨6125238, by rfl⟩ : syracuseStep 16333969 = 12250477) B12250477
theorem B21778625 : Blo 2265435 21778625 := bstep (se 2 (by rfl) ⟨8166984, by rfl⟩ : syracuseStep 21778625 = 16333969) B16333969
theorem B14519083 : Blo 2265435 14519083 := bstep (se 1 (by rfl) ⟨10889312, by rfl⟩ : syracuseStep 14519083 = 21778625) B21778625
theorem B19358777 : Blo 2265435 19358777 := bstep (se 2 (by rfl) ⟨7259541, by rfl⟩ : syracuseStep 19358777 = 14519083) B14519083
theorem B12905851 : Blo 2265435 12905851 := bstep (se 1 (by rfl) ⟨9679388, by rfl⟩ : syracuseStep 12905851 = 19358777) B19358777
theorem B17207801 : Blo 2265435 17207801 := bstep (se 2 (by rfl) ⟨6452925, by rfl⟩ : syracuseStep 17207801 = 12905851) B12905851
theorem B11471867 : Blo 2265435 11471867 := bstep (se 1 (by rfl) ⟨8603900, by rfl⟩ : syracuseStep 11471867 = 17207801) B17207801
theorem B7647911 : Blo 2265435 7647911 := bstep (se 1 (by rfl) ⟨5735933, by rfl⟩ : syracuseStep 7647911 = 11471867) B11471867
theorem B5098607 : Blo 2265435 5098607 := bstep (se 1 (by rfl) ⟨3823955, by rfl⟩ : syracuseStep 5098607 = 7647911) B7647911
theorem B3399071 : Blo 2265435 3399071 := bstep (se 1 (by rfl) ⟨2549303, by rfl⟩ : syracuseStep 3399071 = 5098607) B5098607
theorem B2266047 : Blo 2265435 2266047 := bstep (se 1 (by rfl) ⟨1699535, by rfl⟩ : syracuseStep 2266047 = 3399071) B3399071
theorem B3399077 : Blo 2265435 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B2266051 : Blo 2265435 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B2867977 : Blo 2265435 2867977 := bbase (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) (by norm_num)
theorem B3823969 : Blo 2265435 3823969 := bstep (se 2 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 3823969 = 2867977) B2867977
theorem B5098625 : Blo 2265435 5098625 := bstep (se 2 (by rfl) ⟨1911984, by rfl⟩ : syracuseStep 5098625 = 3823969) B3823969
theorem B3399083 : Blo 2265435 3399083 := bstep (se 1 (by rfl) ⟨2549312, by rfl⟩ : syracuseStep 3399083 = 5098625) B5098625
theorem B2266055 : Blo 2265435 2266055 := bstep (se 1 (by rfl) ⟨1699541, by rfl⟩ : syracuseStep 2266055 = 3399083) B3399083
theorem B2549317 : Blo 2265435 2549317 := bbase (se 4 (by rfl) ⟨238998, by rfl⟩ : syracuseStep 2549317 = 477997) (by norm_num)
theorem B3399089 : Blo 2265435 3399089 := bstep (se 2 (by rfl) ⟨1274658, by rfl⟩ : syracuseStep 3399089 = 2549317) B2549317
theorem B2266059 : Blo 2265435 2266059 := bstep (se 1 (by rfl) ⟨1699544, by rfl⟩ : syracuseStep 2266059 = 3399089) B3399089
theorem B4301981 : Blo 2265435 4301981 := bbase (se 3 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 4301981 = 1613243) (by norm_num)
theorem B2867987 : Blo 2265435 2867987 := bstep (se 1 (by rfl) ⟨2150990, by rfl⟩ : syracuseStep 2867987 = 4301981) B4301981
theorem B7647965 : Blo 2265435 7647965 := bstep (se 3 (by rfl) ⟨1433993, by rfl⟩ : syracuseStep 7647965 = 2867987) B2867987
theorem B5098643 : Blo 2265435 5098643 := bstep (se 1 (by rfl) ⟨3823982, by rfl⟩ : syracuseStep 5098643 = 7647965) B7647965
theorem B3399095 : Blo 2265435 3399095 := bstep (se 1 (by rfl) ⟨2549321, by rfl⟩ : syracuseStep 3399095 = 5098643) B5098643
theorem B2266063 : Blo 2265435 2266063 := bstep (se 1 (by rfl) ⟨1699547, by rfl⟩ : syracuseStep 2266063 = 3399095) B3399095
theorem B3399101 : Blo 2265435 3399101 := bbase (se 3 (by rfl) ⟨637331, by rfl⟩ : syracuseStep 3399101 = 1274663) (by norm_num)
theorem B2266067 : Blo 2265435 2266067 := bstep (se 1 (by rfl) ⟨1699550, by rfl⟩ : syracuseStep 2266067 = 3399101) B3399101
theorem B5098661 : Blo 2265435 5098661 := bbase (se 4 (by rfl) ⟨477999, by rfl⟩ : syracuseStep 5098661 = 955999) (by norm_num)
theorem B3399107 : Blo 2265435 3399107 := bstep (se 1 (by rfl) ⟨2549330, by rfl⟩ : syracuseStep 3399107 = 5098661) B5098661
theorem B2266071 : Blo 2265435 2266071 := bstep (se 1 (by rfl) ⟨1699553, by rfl⟩ : syracuseStep 2266071 = 3399107) B3399107
theorem B5736005 : Blo 2265435 5736005 := bbase (se 4 (by rfl) ⟨537750, by rfl⟩ : syracuseStep 5736005 = 1075501) (by norm_num)
theorem B3824003 : Blo 2265435 3824003 := bstep (se 1 (by rfl) ⟨2868002, by rfl⟩ : syracuseStep 3824003 = 5736005) B5736005
theorem B2549335 : Blo 2265435 2549335 := bstep (se 1 (by rfl) ⟨1912001, by rfl⟩ : syracuseStep 2549335 = 3824003) B3824003
theorem B3399113 : Blo 2265435 3399113 := bstep (se 2 (by rfl) ⟨1274667, by rfl⟩ : syracuseStep 3399113 = 2549335) B2549335
theorem B2266075 : Blo 2265435 2266075 := bstep (se 1 (by rfl) ⟨1699556, by rfl⟩ : syracuseStep 2266075 = 3399113) B3399113
theorem B20672981 : Blo 2265435 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B13781987 : Blo 2265435 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B9187991 : Blo 2265435 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B6125327 : Blo 2265435 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B4083551 : Blo 2265435 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B2722367 : Blo 2265435 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B7259645 : Blo 2265435 7259645 := bstep (se 3 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 7259645 = 2722367) B2722367
theorem B4839763 : Blo 2265435 4839763 := bstep (se 1 (by rfl) ⟨3629822, by rfl⟩ : syracuseStep 4839763 = 7259645) B7259645
theorem B6453017 : Blo 2265435 6453017 := bstep (se 2 (by rfl) ⟨2419881, by rfl⟩ : syracuseStep 6453017 = 4839763) B4839763
theorem B4302011 : Blo 2265435 4302011 := bstep (se 1 (by rfl) ⟨3226508, by rfl⟩ : syracuseStep 4302011 = 6453017) B6453017
theorem B11472029 : Blo 2265435 11472029 := bstep (se 3 (by rfl) ⟨2151005, by rfl⟩ : syracuseStep 11472029 = 4302011) B4302011
theorem B7648019 : Blo 2265435 7648019 := bstep (se 1 (by rfl) ⟨5736014, by rfl⟩ : syracuseStep 7648019 = 11472029) B11472029
theorem B5098679 : Blo 2265435 5098679 := bstep (se 1 (by rfl) ⟨3824009, by rfl⟩ : syracuseStep 5098679 = 7648019) B7648019
theorem B3399119 : Blo 2265435 3399119 := bstep (se 1 (by rfl) ⟨2549339, by rfl⟩ : syracuseStep 3399119 = 5098679) B5098679
theorem B2266079 : Blo 2265435 2266079 := bstep (se 1 (by rfl) ⟨1699559, by rfl⟩ : syracuseStep 2266079 = 3399119) B3399119
theorem B3399125 : Blo 2265435 3399125 := bbase (se 7 (by rfl) ⟨39833, by rfl⟩ : syracuseStep 3399125 = 79667) (by norm_num)
theorem B2266083 : Blo 2265435 2266083 := bstep (se 1 (by rfl) ⟨1699562, by rfl⟩ : syracuseStep 2266083 = 3399125) B3399125
theorem B8604053 : Blo 2265435 8604053 := bbase (se 6 (by rfl) ⟨201657, by rfl⟩ : syracuseStep 8604053 = 403315) (by norm_num)
theorem B5736035 : Blo 2265435 5736035 := bstep (se 1 (by rfl) ⟨4302026, by rfl⟩ : syracuseStep 5736035 = 8604053) B8604053
theorem B3824023 : Blo 2265435 3824023 := bstep (se 1 (by rfl) ⟨2868017, by rfl⟩ : syracuseStep 3824023 = 5736035) B5736035
theorem B5098697 : Blo 2265435 5098697 := bstep (se 2 (by rfl) ⟨1912011, by rfl⟩ : syracuseStep 5098697 = 3824023) B3824023
theorem B3399131 : Blo 2265435 3399131 := bstep (se 1 (by rfl) ⟨2549348, by rfl⟩ : syracuseStep 3399131 = 5098697) B5098697
theorem B2266087 : Blo 2265435 2266087 := bstep (se 1 (by rfl) ⟨1699565, by rfl⟩ : syracuseStep 2266087 = 3399131) B3399131
theorem B2549353 : Blo 2265435 2549353 := bbase (se 2 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 2549353 = 1912015) (by norm_num)
theorem B3399137 : Blo 2265435 3399137 := bstep (se 2 (by rfl) ⟨1274676, by rfl⟩ : syracuseStep 3399137 = 2549353) B2549353
theorem B2266091 : Blo 2265435 2266091 := bstep (se 1 (by rfl) ⟨1699568, by rfl⟩ : syracuseStep 2266091 = 3399137) B3399137
theorem B4839797 : Blo 2265435 4839797 := bbase (se 5 (by rfl) ⟨226865, by rfl⟩ : syracuseStep 4839797 = 453731) (by norm_num)
theorem B12906125 : Blo 2265435 12906125 := bstep (se 3 (by rfl) ⟨2419898, by rfl⟩ : syracuseStep 12906125 = 4839797) B4839797
theorem B8604083 : Blo 2265435 8604083 := bstep (se 1 (by rfl) ⟨6453062, by rfl⟩ : syracuseStep 8604083 = 12906125) B12906125
theorem B5736055 : Blo 2265435 5736055 := bstep (se 1 (by rfl) ⟨4302041, by rfl⟩ : syracuseStep 5736055 = 8604083) B8604083
theorem B7648073 : Blo 2265435 7648073 := bstep (se 2 (by rfl) ⟨2868027, by rfl⟩ : syracuseStep 7648073 = 5736055) B5736055
theorem B5098715 : Blo 2265435 5098715 := bstep (se 1 (by rfl) ⟨3824036, by rfl⟩ : syracuseStep 5098715 = 7648073) B7648073
theorem B3399143 : Blo 2265435 3399143 := bstep (se 1 (by rfl) ⟨2549357, by rfl⟩ : syracuseStep 3399143 = 5098715) B5098715
theorem B2266095 : Blo 2265435 2266095 := bstep (se 1 (by rfl) ⟨1699571, by rfl⟩ : syracuseStep 2266095 = 3399143) B3399143
theorem B3399149 : Blo 2265435 3399149 := bbase (se 3 (by rfl) ⟨637340, by rfl⟩ : syracuseStep 3399149 = 1274681) (by norm_num)
theorem B2266099 : Blo 2265435 2266099 := bstep (se 1 (by rfl) ⟨1699574, by rfl⟩ : syracuseStep 2266099 = 3399149) B3399149
theorem B5098733 : Blo 2265435 5098733 := bbase (se 3 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 5098733 = 1912025) (by norm_num)
theorem B3399155 : Blo 2265435 3399155 := bstep (se 1 (by rfl) ⟨2549366, by rfl⟩ : syracuseStep 3399155 = 5098733) B5098733
theorem B2266103 : Blo 2265435 2266103 := bstep (se 1 (by rfl) ⟨1699577, by rfl⟩ : syracuseStep 2266103 = 3399155) B3399155
theorem B3226549 : Blo 2265435 3226549 := bbase (se 5 (by rfl) ⟨151244, by rfl⟩ : syracuseStep 3226549 = 302489) (by norm_num)
theorem B4302065 : Blo 2265435 4302065 := bstep (se 2 (by rfl) ⟨1613274, by rfl⟩ : syracuseStep 4302065 = 3226549) B3226549
theorem B2868043 : Blo 2265435 2868043 := bstep (se 1 (by rfl) ⟨2151032, by rfl⟩ : syracuseStep 2868043 = 4302065) B4302065
theorem B3824057 : Blo 2265435 3824057 := bstep (se 2 (by rfl) ⟨1434021, by rfl⟩ : syracuseStep 3824057 = 2868043) B2868043
theorem B2549371 : Blo 2265435 2549371 := bstep (se 1 (by rfl) ⟨1912028, by rfl⟩ : syracuseStep 2549371 = 3824057) B3824057
theorem B3399161 : Blo 2265435 3399161 := bstep (se 2 (by rfl) ⟨1274685, by rfl⟩ : syracuseStep 3399161 = 2549371) B2549371
theorem B2266107 : Blo 2265435 2266107 := bstep (se 1 (by rfl) ⟨1699580, by rfl⟩ : syracuseStep 2266107 = 3399161) B3399161
theorem B39782357 : Blo 2265435 39782357 := bbase (se 7 (by rfl) ⟨466199, by rfl⟩ : syracuseStep 39782357 = 932399) (by norm_num)
theorem B26521571 : Blo 2265435 26521571 := bstep (se 1 (by rfl) ⟨19891178, by rfl⟩ : syracuseStep 26521571 = 39782357) B39782357
theorem B70724189 : Blo 2265435 70724189 := bstep (se 3 (by rfl) ⟨13260785, by rfl⟩ : syracuseStep 70724189 = 26521571) B26521571
theorem B47149459 : Blo 2265435 47149459 := bstep (se 1 (by rfl) ⟨35362094, by rfl⟩ : syracuseStep 47149459 = 70724189) B70724189
theorem B251463781 : Blo 2265435 251463781 := bstep (se 4 (by rfl) ⟨23574729, by rfl⟩ : syracuseStep 251463781 = 47149459) B47149459
theorem B335285041 : Blo 2265435 335285041 := bstep (se 2 (by rfl) ⟨125731890, by rfl⟩ : syracuseStep 335285041 = 251463781) B251463781
theorem B447046721 : Blo 2265435 447046721 := bstep (se 2 (by rfl) ⟨167642520, by rfl⟩ : syracuseStep 447046721 = 335285041) B335285041
theorem B298031147 : Blo 2265435 298031147 := bstep (se 1 (by rfl) ⟨223523360, by rfl⟩ : syracuseStep 298031147 = 447046721) B447046721
theorem B198687431 : Blo 2265435 198687431 := bstep (se 1 (by rfl) ⟨149015573, by rfl⟩ : syracuseStep 198687431 = 298031147) B298031147
theorem B132458287 : Blo 2265435 132458287 := bstep (se 1 (by rfl) ⟨99343715, by rfl⟩ : syracuseStep 132458287 = 198687431) B198687431
theorem B176611049 : Blo 2265435 176611049 := bstep (se 2 (by rfl) ⟨66229143, by rfl⟩ : syracuseStep 176611049 = 132458287) B132458287
theorem B117740699 : Blo 2265435 117740699 := bstep (se 1 (by rfl) ⟨88305524, by rfl⟩ : syracuseStep 117740699 = 176611049) B176611049
theorem B78493799 : Blo 2265435 78493799 := bstep (se 1 (by rfl) ⟨58870349, by rfl⟩ : syracuseStep 78493799 = 117740699) B117740699
theorem B52329199 : Blo 2265435 52329199 := bstep (se 1 (by rfl) ⟨39246899, by rfl⟩ : syracuseStep 52329199 = 78493799) B78493799
theorem B69772265 : Blo 2265435 69772265 := bstep (se 2 (by rfl) ⟨26164599, by rfl⟩ : syracuseStep 69772265 = 52329199) B52329199
theorem B46514843 : Blo 2265435 46514843 := bstep (se 1 (by rfl) ⟨34886132, by rfl⟩ : syracuseStep 46514843 = 69772265) B69772265
theorem B31009895 : Blo 2265435 31009895 := bstep (se 1 (by rfl) ⟨23257421, by rfl⟩ : syracuseStep 31009895 = 46514843) B46514843
theorem B20673263 : Blo 2265435 20673263 := bstep (se 1 (by rfl) ⟨15504947, by rfl⟩ : syracuseStep 20673263 = 31009895) B31009895
theorem B55128701 : Blo 2265435 55128701 := bstep (se 3 (by rfl) ⟨10336631, by rfl⟩ : syracuseStep 55128701 = 20673263) B20673263
theorem B36752467 : Blo 2265435 36752467 := bstep (se 1 (by rfl) ⟨27564350, by rfl⟩ : syracuseStep 36752467 = 55128701) B55128701
theorem B49003289 : Blo 2265435 49003289 := bstep (se 2 (by rfl) ⟨18376233, by rfl⟩ : syracuseStep 49003289 = 36752467) B36752467
theorem B32668859 : Blo 2265435 32668859 := bstep (se 1 (by rfl) ⟨24501644, by rfl⟩ : syracuseStep 32668859 = 49003289) B49003289
theorem B87116957 : Blo 2265435 87116957 := bstep (se 3 (by rfl) ⟨16334429, by rfl⟩ : syracuseStep 87116957 = 32668859) B32668859
theorem B58077971 : Blo 2265435 58077971 := bstep (se 1 (by rfl) ⟨43558478, by rfl⟩ : syracuseStep 58077971 = 87116957) B87116957
theorem B38718647 : Blo 2265435 38718647 := bstep (se 1 (by rfl) ⟨29038985, by rfl⟩ : syracuseStep 38718647 = 58077971) B58077971
theorem B25812431 : Blo 2265435 25812431 := bstep (se 1 (by rfl) ⟨19359323, by rfl⟩ : syracuseStep 25812431 = 38718647) B38718647
theorem B17208287 : Blo 2265435 17208287 := bstep (se 1 (by rfl) ⟨12906215, by rfl⟩ : syracuseStep 17208287 = 25812431) B25812431
theorem B11472191 : Blo 2265435 11472191 := bstep (se 1 (by rfl) ⟨8604143, by rfl⟩ : syracuseStep 11472191 = 17208287) B17208287
theorem B7648127 : Blo 2265435 7648127 := bstep (se 1 (by rfl) ⟨5736095, by rfl⟩ : syracuseStep 7648127 = 11472191) B11472191
theorem B5098751 : Blo 2265435 5098751 := bstep (se 1 (by rfl) ⟨3824063, by rfl⟩ : syracuseStep 5098751 = 7648127) B7648127
theorem B3399167 : Blo 2265435 3399167 := bstep (se 1 (by rfl) ⟨2549375, by rfl⟩ : syracuseStep 3399167 = 5098751) B5098751
theorem B2266111 : Blo 2265435 2266111 := bstep (se 1 (by rfl) ⟨1699583, by rfl⟩ : syracuseStep 2266111 = 3399167) B3399167
theorem B3399173 : Blo 2265435 3399173 := bbase (se 4 (by rfl) ⟨318672, by rfl⟩ : syracuseStep 3399173 = 637345) (by norm_num)
theorem B2266115 : Blo 2265435 2266115 := bstep (se 1 (by rfl) ⟨1699586, by rfl⟩ : syracuseStep 2266115 = 3399173) B3399173
theorem B3824077 : Blo 2265435 3824077 := bbase (se 3 (by rfl) ⟨717014, by rfl⟩ : syracuseStep 3824077 = 1434029) (by norm_num)
theorem B5098769 : Blo 2265435 5098769 := bstep (se 2 (by rfl) ⟨1912038, by rfl⟩ : syracuseStep 5098769 = 3824077) B3824077
theorem B3399179 : Blo 2265435 3399179 := bstep (se 1 (by rfl) ⟨2549384, by rfl⟩ : syracuseStep 3399179 = 5098769) B5098769
theorem B2266119 : Blo 2265435 2266119 := bstep (se 1 (by rfl) ⟨1699589, by rfl⟩ : syracuseStep 2266119 = 3399179) B3399179
theorem B2549389 : Blo 2265435 2549389 := bbase (se 3 (by rfl) ⟨478010, by rfl⟩ : syracuseStep 2549389 = 956021) (by norm_num)
theorem B3399185 : Blo 2265435 3399185 := bstep (se 2 (by rfl) ⟨1274694, by rfl⟩ : syracuseStep 3399185 = 2549389) B2549389
theorem B2266123 : Blo 2265435 2266123 := bstep (se 1 (by rfl) ⟨1699592, by rfl⟩ : syracuseStep 2266123 = 3399185) B3399185
theorem B7648181 : Blo 2265435 7648181 := bbase (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) (by norm_num)
theorem B5098787 : Blo 2265435 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B3399191 : Blo 2265435 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B2266127 : Blo 2265435 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B3399197 : Blo 2265435 3399197 := bbase (se 3 (by rfl) ⟨637349, by rfl⟩ : syracuseStep 3399197 = 1274699) (by norm_num)
theorem B2266131 : Blo 2265435 2266131 := bstep (se 1 (by rfl) ⟨1699598, by rfl⟩ : syracuseStep 2266131 = 3399197) B3399197
theorem B5098805 : Blo 2265435 5098805 := bbase (se 5 (by rfl) ⟨239006, by rfl⟩ : syracuseStep 5098805 = 478013) (by norm_num)
theorem B3399203 : Blo 2265435 3399203 := bstep (se 1 (by rfl) ⟨2549402, by rfl⟩ : syracuseStep 3399203 = 5098805) B5098805
theorem B2266135 : Blo 2265435 2266135 := bstep (se 1 (by rfl) ⟨1699601, by rfl⟩ : syracuseStep 2266135 = 3399203) B3399203
theorem B5168381 : Blo 2265435 5168381 := bbase (se 3 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 5168381 = 1938143) (by norm_num)
theorem B13782349 : Blo 2265435 13782349 := bstep (se 3 (by rfl) ⟨2584190, by rfl⟩ : syracuseStep 13782349 = 5168381) B5168381
theorem B18376465 : Blo 2265435 18376465 := bstep (se 2 (by rfl) ⟨6891174, by rfl⟩ : syracuseStep 18376465 = 13782349) B13782349
theorem B24501953 : Blo 2265435 24501953 := bstep (se 2 (by rfl) ⟨9188232, by rfl⟩ : syracuseStep 24501953 = 18376465) B18376465
theorem B16334635 : Blo 2265435 16334635 := bstep (se 1 (by rfl) ⟨12250976, by rfl⟩ : syracuseStep 16334635 = 24501953) B24501953
theorem B21779513 : Blo 2265435 21779513 := bstep (se 2 (by rfl) ⟨8167317, by rfl⟩ : syracuseStep 21779513 = 16334635) B16334635
theorem B14519675 : Blo 2265435 14519675 := bstep (se 1 (by rfl) ⟨10889756, by rfl⟩ : syracuseStep 14519675 = 21779513) B21779513
theorem B9679783 : Blo 2265435 9679783 := bstep (se 1 (by rfl) ⟨7259837, by rfl⟩ : syracuseStep 9679783 = 14519675) B14519675
theorem B12906377 : Blo 2265435 12906377 := bstep (se 2 (by rfl) ⟨4839891, by rfl⟩ : syracuseStep 12906377 = 9679783) B9679783
theorem B8604251 : Blo 2265435 8604251 := bstep (se 1 (by rfl) ⟨6453188, by rfl⟩ : syracuseStep 8604251 = 12906377) B12906377
theorem B5736167 : Blo 2265435 5736167 := bstep (se 1 (by rfl) ⟨4302125, by rfl⟩ : syracuseStep 5736167 = 8604251) B8604251
theorem B3824111 : Blo 2265435 3824111 := bstep (se 1 (by rfl) ⟨2868083, by rfl⟩ : syracuseStep 3824111 = 5736167) B5736167
theorem B2549407 : Blo 2265435 2549407 := bstep (se 1 (by rfl) ⟨1912055, by rfl⟩ : syracuseStep 2549407 = 3824111) B3824111
theorem B3399209 : Blo 2265435 3399209 := bstep (se 2 (by rfl) ⟨1274703, by rfl⟩ : syracuseStep 3399209 = 2549407) B2549407
theorem B2266139 : Blo 2265435 2266139 := bstep (se 1 (by rfl) ⟨1699604, by rfl⟩ : syracuseStep 2266139 = 3399209) B3399209
theorem B12250997 : Blo 2265435 12250997 := bbase (se 5 (by rfl) ⟨574265, by rfl⟩ : syracuseStep 12250997 = 1148531) (by norm_num)
theorem B8167331 : Blo 2265435 8167331 := bstep (se 1 (by rfl) ⟨6125498, by rfl⟩ : syracuseStep 8167331 = 12250997) B12250997
theorem B21779549 : Blo 2265435 21779549 := bstep (se 3 (by rfl) ⟨4083665, by rfl⟩ : syracuseStep 21779549 = 8167331) B8167331
theorem B14519699 : Blo 2265435 14519699 := bstep (se 1 (by rfl) ⟨10889774, by rfl⟩ : syracuseStep 14519699 = 21779549) B21779549
theorem B9679799 : Blo 2265435 9679799 := bstep (se 1 (by rfl) ⟨7259849, by rfl⟩ : syracuseStep 9679799 = 14519699) B14519699
theorem B6453199 : Blo 2265435 6453199 := bstep (se 1 (by rfl) ⟨4839899, by rfl⟩ : syracuseStep 6453199 = 9679799) B9679799
theorem B8604265 : Blo 2265435 8604265 := bstep (se 2 (by rfl) ⟨3226599, by rfl⟩ : syracuseStep 8604265 = 6453199) B6453199
theorem B11472353 : Blo 2265435 11472353 := bstep (se 2 (by rfl) ⟨4302132, by rfl⟩ : syracuseStep 11472353 = 8604265) B8604265
theorem B7648235 : Blo 2265435 7648235 := bstep (se 1 (by rfl) ⟨5736176, by rfl⟩ : syracuseStep 7648235 = 11472353) B11472353
theorem B5098823 : Blo 2265435 5098823 := bstep (se 1 (by rfl) ⟨3824117, by rfl⟩ : syracuseStep 5098823 = 7648235) B7648235
theorem B3399215 : Blo 2265435 3399215 := bstep (se 1 (by rfl) ⟨2549411, by rfl⟩ : syracuseStep 3399215 = 5098823) B5098823
theorem B2266143 : Blo 2265435 2266143 := bstep (se 1 (by rfl) ⟨1699607, by rfl⟩ : syracuseStep 2266143 = 3399215) B3399215
theorem B3399221 : Blo 2265435 3399221 := bbase (se 5 (by rfl) ⟨159338, by rfl⟩ : syracuseStep 3399221 = 318677) (by norm_num)
theorem B2266147 : Blo 2265435 2266147 := bstep (se 1 (by rfl) ⟨1699610, by rfl⟩ : syracuseStep 2266147 = 3399221) B3399221
theorem B5736197 : Blo 2265435 5736197 := bbase (se 4 (by rfl) ⟨537768, by rfl⟩ : syracuseStep 5736197 = 1075537) (by norm_num)
theorem B3824131 : Blo 2265435 3824131 := bstep (se 1 (by rfl) ⟨2868098, by rfl⟩ : syracuseStep 3824131 = 5736197) B5736197
theorem B5098841 : Blo 2265435 5098841 := bstep (se 2 (by rfl) ⟨1912065, by rfl⟩ : syracuseStep 5098841 = 3824131) B3824131
theorem B3399227 : Blo 2265435 3399227 := bstep (se 1 (by rfl) ⟨2549420, by rfl⟩ : syracuseStep 3399227 = 5098841) B5098841
theorem B2266151 : Blo 2265435 2266151 := bstep (se 1 (by rfl) ⟨1699613, by rfl⟩ : syracuseStep 2266151 = 3399227) B3399227
theorem B2549425 : Blo 2265435 2549425 := bbase (se 2 (by rfl) ⟨956034, by rfl⟩ : syracuseStep 2549425 = 1912069) (by norm_num)
theorem B3399233 : Blo 2265435 3399233 := bstep (se 2 (by rfl) ⟨1274712, by rfl⟩ : syracuseStep 3399233 = 2549425) B2549425
theorem B2266155 : Blo 2265435 2266155 := bstep (se 1 (by rfl) ⟨1699616, by rfl⟩ : syracuseStep 2266155 = 3399233) B3399233
theorem B4360861 : Blo 2265435 4360861 := bbase (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) (by norm_num)
theorem B23257925 : Blo 2265435 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B15505283 : Blo 2265435 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B41347421 : Blo 2265435 41347421 := bstep (se 3 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 41347421 = 15505283) B15505283
theorem B27564947 : Blo 2265435 27564947 := bstep (se 1 (by rfl) ⟨20673710, by rfl⟩ : syracuseStep 27564947 = 41347421) B41347421
theorem B18376631 : Blo 2265435 18376631 := bstep (se 1 (by rfl) ⟨13782473, by rfl⟩ : syracuseStep 18376631 = 27564947) B27564947
theorem B12251087 : Blo 2265435 12251087 := bstep (se 1 (by rfl) ⟨9188315, by rfl⟩ : syracuseStep 12251087 = 18376631) B18376631
theorem B8167391 : Blo 2265435 8167391 := bstep (se 1 (by rfl) ⟨6125543, by rfl⟩ : syracuseStep 8167391 = 12251087) B12251087
theorem B5444927 : Blo 2265435 5444927 := bstep (se 1 (by rfl) ⟨4083695, by rfl⟩ : syracuseStep 5444927 = 8167391) B8167391
theorem B3629951 : Blo 2265435 3629951 := bstep (se 1 (by rfl) ⟨2722463, by rfl⟩ : syracuseStep 3629951 = 5444927) B5444927
theorem B2419967 : Blo 2265435 2419967 := bstep (se 1 (by rfl) ⟨1814975, by rfl⟩ : syracuseStep 2419967 = 3629951) B3629951
theorem B6453245 : Blo 2265435 6453245 := bstep (se 3 (by rfl) ⟨1209983, by rfl⟩ : syracuseStep 6453245 = 2419967) B2419967
theorem B4302163 : Blo 2265435 4302163 := bstep (se 1 (by rfl) ⟨3226622, by rfl⟩ : syracuseStep 4302163 = 6453245) B6453245
theorem B5736217 : Blo 2265435 5736217 := bstep (se 2 (by rfl) ⟨2151081, by rfl⟩ : syracuseStep 5736217 = 4302163) B4302163
theorem B7648289 : Blo 2265435 7648289 := bstep (se 2 (by rfl) ⟨2868108, by rfl⟩ : syracuseStep 7648289 = 5736217) B5736217
theorem B5098859 : Blo 2265435 5098859 := bstep (se 1 (by rfl) ⟨3824144, by rfl⟩ : syracuseStep 5098859 = 7648289) B7648289
theorem B3399239 : Blo 2265435 3399239 := bstep (se 1 (by rfl) ⟨2549429, by rfl⟩ : syracuseStep 3399239 = 5098859) B5098859
theorem B2266159 : Blo 2265435 2266159 := bstep (se 1 (by rfl) ⟨1699619, by rfl⟩ : syracuseStep 2266159 = 3399239) B3399239
theorem B3399245 : Blo 2265435 3399245 := bbase (se 3 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 3399245 = 1274717) (by norm_num)
theorem B2266163 : Blo 2265435 2266163 := bstep (se 1 (by rfl) ⟨1699622, by rfl⟩ : syracuseStep 2266163 = 3399245) B3399245
theorem B5098877 : Blo 2265435 5098877 := bbase (se 3 (by rfl) ⟨956039, by rfl⟩ : syracuseStep 5098877 = 1912079) (by norm_num)
theorem B3399251 : Blo 2265435 3399251 := bstep (se 1 (by rfl) ⟨2549438, by rfl⟩ : syracuseStep 3399251 = 5098877) B5098877
theorem B2266167 : Blo 2265435 2266167 := bstep (se 1 (by rfl) ⟨1699625, by rfl⟩ : syracuseStep 2266167 = 3399251) B3399251
theorem B3824165 : Blo 2265435 3824165 := bbase (se 4 (by rfl) ⟨358515, by rfl⟩ : syracuseStep 3824165 = 717031) (by norm_num)
theorem B2549443 : Blo 2265435 2549443 := bstep (se 1 (by rfl) ⟨1912082, by rfl⟩ : syracuseStep 2549443 = 3824165) B3824165
theorem B3399257 : Blo 2265435 3399257 := bstep (se 2 (by rfl) ⟨1274721, by rfl⟩ : syracuseStep 3399257 = 2549443) B2549443
theorem B2266171 : Blo 2265435 2266171 := bstep (se 1 (by rfl) ⟨1699628, by rfl⟩ : syracuseStep 2266171 = 3399257) B3399257
theorem B3226645 : Blo 2265435 3226645 := bbase (se 6 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 3226645 = 151249) (by norm_num)
theorem B17208773 : Blo 2265435 17208773 := bstep (se 4 (by rfl) ⟨1613322, by rfl⟩ : syracuseStep 17208773 = 3226645) B3226645
theorem B11472515 : Blo 2265435 11472515 := bstep (se 1 (by rfl) ⟨8604386, by rfl⟩ : syracuseStep 11472515 = 17208773) B17208773
theorem B7648343 : Blo 2265435 7648343 := bstep (se 1 (by rfl) ⟨5736257, by rfl⟩ : syracuseStep 7648343 = 11472515) B11472515
theorem B5098895 : Blo 2265435 5098895 := bstep (se 1 (by rfl) ⟨3824171, by rfl⟩ : syracuseStep 5098895 = 7648343) B7648343
theorem B3399263 : Blo 2265435 3399263 := bstep (se 1 (by rfl) ⟨2549447, by rfl⟩ : syracuseStep 3399263 = 5098895) B5098895
theorem B2266175 : Blo 2265435 2266175 := bstep (se 1 (by rfl) ⟨1699631, by rfl⟩ : syracuseStep 2266175 = 3399263) B3399263
theorem B3399269 : Blo 2265435 3399269 := bbase (se 4 (by rfl) ⟨318681, by rfl⟩ : syracuseStep 3399269 = 637363) (by norm_num)
theorem B2266179 : Blo 2265435 2266179 := bstep (se 1 (by rfl) ⟨1699634, by rfl⟩ : syracuseStep 2266179 = 3399269) B3399269
theorem B2419993 : Blo 2265435 2419993 := bbase (se 2 (by rfl) ⟨907497, by rfl⟩ : syracuseStep 2419993 = 1814995) (by norm_num)
theorem B3226657 : Blo 2265435 3226657 := bstep (se 2 (by rfl) ⟨1209996, by rfl⟩ : syracuseStep 3226657 = 2419993) B2419993
theorem B4302209 : Blo 2265435 4302209 := bstep (se 2 (by rfl) ⟨1613328, by rfl⟩ : syracuseStep 4302209 = 3226657) B3226657
theorem B2868139 : Blo 2265435 2868139 := bstep (se 1 (by rfl) ⟨2151104, by rfl⟩ : syracuseStep 2868139 = 4302209) B4302209
theorem B3824185 : Blo 2265435 3824185 := bstep (se 2 (by rfl) ⟨1434069, by rfl⟩ : syracuseStep 3824185 = 2868139) B2868139
theorem B5098913 : Blo 2265435 5098913 := bstep (se 2 (by rfl) ⟨1912092, by rfl⟩ : syracuseStep 5098913 = 3824185) B3824185
theorem B3399275 : Blo 2265435 3399275 := bstep (se 1 (by rfl) ⟨2549456, by rfl⟩ : syracuseStep 3399275 = 5098913) B5098913
theorem B2266183 : Blo 2265435 2266183 := bstep (se 1 (by rfl) ⟨1699637, by rfl⟩ : syracuseStep 2266183 = 3399275) B3399275
theorem B2549461 : Blo 2265435 2549461 := bbase (se 7 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 2549461 = 59753) (by norm_num)
theorem B3399281 : Blo 2265435 3399281 := bstep (se 2 (by rfl) ⟨1274730, by rfl⟩ : syracuseStep 3399281 = 2549461) B2549461
theorem B2266187 : Blo 2265435 2266187 := bstep (se 1 (by rfl) ⟨1699640, by rfl⟩ : syracuseStep 2266187 = 3399281) B3399281
theorem B2868149 : Blo 2265435 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B7648397 : Blo 2265435 7648397 := bstep (se 3 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 7648397 = 2868149) B2868149
theorem B5098931 : Blo 2265435 5098931 := bstep (se 1 (by rfl) ⟨3824198, by rfl⟩ : syracuseStep 5098931 = 7648397) B7648397
theorem B3399287 : Blo 2265435 3399287 := bstep (se 1 (by rfl) ⟨2549465, by rfl⟩ : syracuseStep 3399287 = 5098931) B5098931
theorem B2266191 : Blo 2265435 2266191 := bstep (se 1 (by rfl) ⟨1699643, by rfl⟩ : syracuseStep 2266191 = 3399287) B3399287
theorem B3399293 : Blo 2265435 3399293 := bbase (se 3 (by rfl) ⟨637367, by rfl⟩ : syracuseStep 3399293 = 1274735) (by norm_num)
theorem B2266195 : Blo 2265435 2266195 := bstep (se 1 (by rfl) ⟨1699646, by rfl⟩ : syracuseStep 2266195 = 3399293) B3399293
theorem B5098949 : Blo 2265435 5098949 := bbase (se 4 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 5098949 = 956053) (by norm_num)
theorem B3399299 : Blo 2265435 3399299 := bstep (se 1 (by rfl) ⟨2549474, by rfl⟩ : syracuseStep 3399299 = 5098949) B5098949
theorem B2266199 : Blo 2265435 2266199 := bstep (se 1 (by rfl) ⟨1699649, by rfl⟩ : syracuseStep 2266199 = 3399299) B3399299
theorem B8721893 : Blo 2265435 8721893 := bbase (se 4 (by rfl) ⟨817677, by rfl⟩ : syracuseStep 8721893 = 1635355) (by norm_num)
theorem B5814595 : Blo 2265435 5814595 := bstep (se 1 (by rfl) ⟨4360946, by rfl⟩ : syracuseStep 5814595 = 8721893) B8721893
theorem B7752793 : Blo 2265435 7752793 := bstep (se 2 (by rfl) ⟨2907297, by rfl⟩ : syracuseStep 7752793 = 5814595) B5814595
theorem B10337057 : Blo 2265435 10337057 := bstep (se 2 (by rfl) ⟨3876396, by rfl⟩ : syracuseStep 10337057 = 7752793) B7752793
theorem B6891371 : Blo 2265435 6891371 := bstep (se 1 (by rfl) ⟨5168528, by rfl⟩ : syracuseStep 6891371 = 10337057) B10337057
theorem B4594247 : Blo 2265435 4594247 := bstep (se 1 (by rfl) ⟨3445685, by rfl⟩ : syracuseStep 4594247 = 6891371) B6891371
theorem B3062831 : Blo 2265435 3062831 := bstep (se 1 (by rfl) ⟨2297123, by rfl⟩ : syracuseStep 3062831 = 4594247) B4594247
theorem B8167549 : Blo 2265435 8167549 := bstep (se 3 (by rfl) ⟨1531415, by rfl⟩ : syracuseStep 8167549 = 3062831) B3062831
theorem B10890065 : Blo 2265435 10890065 := bstep (se 2 (by rfl) ⟨4083774, by rfl⟩ : syracuseStep 10890065 = 8167549) B8167549
theorem B7260043 : Blo 2265435 7260043 := bstep (se 1 (by rfl) ⟨5445032, by rfl⟩ : syracuseStep 7260043 = 10890065) B10890065
theorem B9680057 : Blo 2265435 9680057 := bstep (se 2 (by rfl) ⟨3630021, by rfl⟩ : syracuseStep 9680057 = 7260043) B7260043
theorem B6453371 : Blo 2265435 6453371 := bstep (se 1 (by rfl) ⟨4840028, by rfl⟩ : syracuseStep 6453371 = 9680057) B9680057
theorem B4302247 : Blo 2265435 4302247 := bstep (se 1 (by rfl) ⟨3226685, by rfl⟩ : syracuseStep 4302247 = 6453371) B6453371
theorem B5736329 : Blo 2265435 5736329 := bstep (se 2 (by rfl) ⟨2151123, by rfl⟩ : syracuseStep 5736329 = 4302247) B4302247
theorem B3824219 : Blo 2265435 3824219 := bstep (se 1 (by rfl) ⟨2868164, by rfl⟩ : syracuseStep 3824219 = 5736329) B5736329
theorem B2549479 : Blo 2265435 2549479 := bstep (se 1 (by rfl) ⟨1912109, by rfl⟩ : syracuseStep 2549479 = 3824219) B3824219
theorem B3399305 : Blo 2265435 3399305 := bstep (se 2 (by rfl) ⟨1274739, by rfl⟩ : syracuseStep 3399305 = 2549479) B2549479
theorem B2266203 : Blo 2265435 2266203 := bstep (se 1 (by rfl) ⟨1699652, by rfl⟩ : syracuseStep 2266203 = 3399305) B3399305
theorem B11472677 : Blo 2265435 11472677 := bbase (se 4 (by rfl) ⟨1075563, by rfl⟩ : syracuseStep 11472677 = 2151127) (by norm_num)
theorem B7648451 : Blo 2265435 7648451 := bstep (se 1 (by rfl) ⟨5736338, by rfl⟩ : syracuseStep 7648451 = 11472677) B11472677
theorem B5098967 : Blo 2265435 5098967 := bstep (se 1 (by rfl) ⟨3824225, by rfl⟩ : syracuseStep 5098967 = 7648451) B7648451
theorem B3399311 : Blo 2265435 3399311 := bstep (se 1 (by rfl) ⟨2549483, by rfl⟩ : syracuseStep 3399311 = 5098967) B5098967
theorem B2266207 : Blo 2265435 2266207 := bstep (se 1 (by rfl) ⟨1699655, by rfl⟩ : syracuseStep 2266207 = 3399311) B3399311
theorem B3399317 : Blo 2265435 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B2266211 : Blo 2265435 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B8622533 : Blo 2265435 8622533 := bbase (se 4 (by rfl) ⟨808362, by rfl⟩ : syracuseStep 8622533 = 1616725) (by norm_num)
theorem B5748355 : Blo 2265435 5748355 := bstep (se 1 (by rfl) ⟨4311266, by rfl⟩ : syracuseStep 5748355 = 8622533) B8622533
theorem B7664473 : Blo 2265435 7664473 := bstep (se 2 (by rfl) ⟨2874177, by rfl⟩ : syracuseStep 7664473 = 5748355) B5748355
theorem B10219297 : Blo 2265435 10219297 := bstep (se 2 (by rfl) ⟨3832236, by rfl⟩ : syracuseStep 10219297 = 7664473) B7664473
theorem B13625729 : Blo 2265435 13625729 := bstep (se 2 (by rfl) ⟨5109648, by rfl⟩ : syracuseStep 13625729 = 10219297) B10219297
theorem B9083819 : Blo 2265435 9083819 := bstep (se 1 (by rfl) ⟨6812864, by rfl⟩ : syracuseStep 9083819 = 13625729) B13625729
theorem B6055879 : Blo 2265435 6055879 := bstep (se 1 (by rfl) ⟨4541909, by rfl⟩ : syracuseStep 6055879 = 9083819) B9083819
theorem B8074505 : Blo 2265435 8074505 := bstep (se 2 (by rfl) ⟨3027939, by rfl⟩ : syracuseStep 8074505 = 6055879) B6055879
theorem B5383003 : Blo 2265435 5383003 := bstep (se 1 (by rfl) ⟨4037252, by rfl⟩ : syracuseStep 5383003 = 8074505) B8074505
theorem B7177337 : Blo 2265435 7177337 := bstep (se 2 (by rfl) ⟨2691501, by rfl⟩ : syracuseStep 7177337 = 5383003) B5383003
theorem B4784891 : Blo 2265435 4784891 := bstep (se 1 (by rfl) ⟨3588668, by rfl⟩ : syracuseStep 4784891 = 7177337) B7177337
theorem B51038837 : Blo 2265435 51038837 := bstep (se 5 (by rfl) ⟨2392445, by rfl⟩ : syracuseStep 51038837 = 4784891) B4784891
theorem B34025891 : Blo 2265435 34025891 := bstep (se 1 (by rfl) ⟨25519418, by rfl⟩ : syracuseStep 34025891 = 51038837) B51038837
theorem B90735709 : Blo 2265435 90735709 := bstep (se 3 (by rfl) ⟨17012945, by rfl⟩ : syracuseStep 90735709 = 34025891) B34025891
theorem B120980945 : Blo 2265435 120980945 := bstep (se 2 (by rfl) ⟨45367854, by rfl⟩ : syracuseStep 120980945 = 90735709) B90735709
theorem B80653963 : Blo 2265435 80653963 := bstep (se 1 (by rfl) ⟨60490472, by rfl⟩ : syracuseStep 80653963 = 120980945) B120980945
theorem B107538617 : Blo 2265435 107538617 := bstep (se 2 (by rfl) ⟨40326981, by rfl⟩ : syracuseStep 107538617 = 80653963) B80653963
theorem B286769645 : Blo 2265435 286769645 := bstep (se 3 (by rfl) ⟨53769308, by rfl⟩ : syracuseStep 286769645 = 107538617) B107538617
theorem B191179763 : Blo 2265435 191179763 := bstep (se 1 (by rfl) ⟨143384822, by rfl⟩ : syracuseStep 191179763 = 286769645) B286769645
theorem B127453175 : Blo 2265435 127453175 := bstep (se 1 (by rfl) ⟨95589881, by rfl⟩ : syracuseStep 127453175 = 191179763) B191179763
theorem B84968783 : Blo 2265435 84968783 := bstep (se 1 (by rfl) ⟨63726587, by rfl⟩ : syracuseStep 84968783 = 127453175) B127453175
theorem B56645855 : Blo 2265435 56645855 := bstep (se 1 (by rfl) ⟨42484391, by rfl⟩ : syracuseStep 56645855 = 84968783) B84968783
theorem B37763903 : Blo 2265435 37763903 := bstep (se 1 (by rfl) ⟨28322927, by rfl⟩ : syracuseStep 37763903 = 56645855) B56645855
theorem B100703741 : Blo 2265435 100703741 := bstep (se 3 (by rfl) ⟨18881951, by rfl⟩ : syracuseStep 100703741 = 37763903) B37763903
theorem B268543309 : Blo 2265435 268543309 := bstep (se 3 (by rfl) ⟨50351870, by rfl⟩ : syracuseStep 268543309 = 100703741) B100703741
theorem B358057745 : Blo 2265435 358057745 := bstep (se 2 (by rfl) ⟨134271654, by rfl⟩ : syracuseStep 358057745 = 268543309) B268543309
theorem B238705163 : Blo 2265435 238705163 := bstep (se 1 (by rfl) ⟨179028872, by rfl⟩ : syracuseStep 238705163 = 358057745) B358057745
theorem B159136775 : Blo 2265435 159136775 := bstep (se 1 (by rfl) ⟨119352581, by rfl⟩ : syracuseStep 159136775 = 238705163) B238705163
theorem B106091183 : Blo 2265435 106091183 := bstep (se 1 (by rfl) ⟨79568387, by rfl⟩ : syracuseStep 106091183 = 159136775) B159136775
theorem B70727455 : Blo 2265435 70727455 := bstep (se 1 (by rfl) ⟨53045591, by rfl⟩ : syracuseStep 70727455 = 106091183) B106091183
theorem B94303273 : Blo 2265435 94303273 := bstep (se 2 (by rfl) ⟨35363727, by rfl⟩ : syracuseStep 94303273 = 70727455) B70727455
theorem B125737697 : Blo 2265435 125737697 := bstep (se 2 (by rfl) ⟨47151636, by rfl⟩ : syracuseStep 125737697 = 94303273) B94303273
theorem B83825131 : Blo 2265435 83825131 := bstep (se 1 (by rfl) ⟨62868848, by rfl⟩ : syracuseStep 83825131 = 125737697) B125737697
theorem B111766841 : Blo 2265435 111766841 := bstep (se 2 (by rfl) ⟨41912565, by rfl⟩ : syracuseStep 111766841 = 83825131) B83825131
theorem B74511227 : Blo 2265435 74511227 := bstep (se 1 (by rfl) ⟨55883420, by rfl⟩ : syracuseStep 74511227 = 111766841) B111766841
theorem B49674151 : Blo 2265435 49674151 := bstep (se 1 (by rfl) ⟨37255613, by rfl⟩ : syracuseStep 49674151 = 74511227) B74511227
theorem B264928805 : Blo 2265435 264928805 := bstep (se 4 (by rfl) ⟨24837075, by rfl⟩ : syracuseStep 264928805 = 49674151) B49674151
theorem B176619203 : Blo 2265435 176619203 := bstep (se 1 (by rfl) ⟨132464402, by rfl⟩ : syracuseStep 176619203 = 264928805) B264928805
theorem B117746135 : Blo 2265435 117746135 := bstep (se 1 (by rfl) ⟨88309601, by rfl⟩ : syracuseStep 117746135 = 176619203) B176619203
theorem B78497423 : Blo 2265435 78497423 := bstep (se 1 (by rfl) ⟨58873067, by rfl⟩ : syracuseStep 78497423 = 117746135) B117746135
theorem B52331615 : Blo 2265435 52331615 := bstep (se 1 (by rfl) ⟨39248711, by rfl⟩ : syracuseStep 52331615 = 78497423) B78497423
theorem B34887743 : Blo 2265435 34887743 := bstep (se 1 (by rfl) ⟨26165807, by rfl⟩ : syracuseStep 34887743 = 52331615) B52331615
theorem B23258495 : Blo 2265435 23258495 := bstep (se 1 (by rfl) ⟨17443871, by rfl⟩ : syracuseStep 23258495 = 34887743) B34887743
theorem B15505663 : Blo 2265435 15505663 := bstep (se 1 (by rfl) ⟨11629247, by rfl⟩ : syracuseStep 15505663 = 23258495) B23258495
theorem B20674217 : Blo 2265435 20674217 := bstep (se 2 (by rfl) ⟨7752831, by rfl⟩ : syracuseStep 20674217 = 15505663) B15505663
theorem B13782811 : Blo 2265435 13782811 := bstep (se 1 (by rfl) ⟨10337108, by rfl⟩ : syracuseStep 13782811 = 20674217) B20674217
theorem B18377081 : Blo 2265435 18377081 := bstep (se 2 (by rfl) ⟨6891405, by rfl⟩ : syracuseStep 18377081 = 13782811) B13782811
theorem B12251387 : Blo 2265435 12251387 := bstep (se 1 (by rfl) ⟨9188540, by rfl⟩ : syracuseStep 12251387 = 18377081) B18377081
theorem B8167591 : Blo 2265435 8167591 := bstep (se 1 (by rfl) ⟨6125693, by rfl⟩ : syracuseStep 8167591 = 12251387) B12251387
theorem B10890121 : Blo 2265435 10890121 := bstep (se 2 (by rfl) ⟨4083795, by rfl⟩ : syracuseStep 10890121 = 8167591) B8167591
theorem B14520161 : Blo 2265435 14520161 := bstep (se 2 (by rfl) ⟨5445060, by rfl⟩ : syracuseStep 14520161 = 10890121) B10890121
theorem B9680107 : Blo 2265435 9680107 := bstep (se 1 (by rfl) ⟨7260080, by rfl⟩ : syracuseStep 9680107 = 14520161) B14520161
theorem B12906809 : Blo 2265435 12906809 := bstep (se 2 (by rfl) ⟨4840053, by rfl⟩ : syracuseStep 12906809 = 9680107) B9680107
theorem B8604539 : Blo 2265435 8604539 := bstep (se 1 (by rfl) ⟨6453404, by rfl⟩ : syracuseStep 8604539 = 12906809) B12906809
theorem B5736359 : Blo 2265435 5736359 := bstep (se 1 (by rfl) ⟨4302269, by rfl⟩ : syracuseStep 5736359 = 8604539) B8604539
theorem B3824239 : Blo 2265435 3824239 := bstep (se 1 (by rfl) ⟨2868179, by rfl⟩ : syracuseStep 3824239 = 5736359) B5736359
theorem B5098985 : Blo 2265435 5098985 := bstep (se 2 (by rfl) ⟨1912119, by rfl⟩ : syracuseStep 5098985 = 3824239) B3824239
theorem B3399323 : Blo 2265435 3399323 := bstep (se 1 (by rfl) ⟨2549492, by rfl⟩ : syracuseStep 3399323 = 5098985) B5098985
theorem B2266215 : Blo 2265435 2266215 := bstep (se 1 (by rfl) ⟨1699661, by rfl⟩ : syracuseStep 2266215 = 3399323) B3399323
theorem B2549497 : Blo 2265435 2549497 := bbase (se 2 (by rfl) ⟨956061, by rfl⟩ : syracuseStep 2549497 = 1912123) (by norm_num)
theorem B3399329 : Blo 2265435 3399329 := bstep (se 2 (by rfl) ⟨1274748, by rfl⟩ : syracuseStep 3399329 = 2549497) B2549497
theorem B2266219 : Blo 2265435 2266219 := bstep (se 1 (by rfl) ⟨1699664, by rfl⟩ : syracuseStep 2266219 = 3399329) B3399329
theorem B3630053 : Blo 2265435 3630053 := bbase (se 4 (by rfl) ⟨340317, by rfl⟩ : syracuseStep 3630053 = 680635) (by norm_num)
theorem B9680141 : Blo 2265435 9680141 := bstep (se 3 (by rfl) ⟨1815026, by rfl⟩ : syracuseStep 9680141 = 3630053) B3630053
theorem B6453427 : Blo 2265435 6453427 := bstep (se 1 (by rfl) ⟨4840070, by rfl⟩ : syracuseStep 6453427 = 9680141) B9680141
theorem B8604569 : Blo 2265435 8604569 := bstep (se 2 (by rfl) ⟨3226713, by rfl⟩ : syracuseStep 8604569 = 6453427) B6453427
theorem B5736379 : Blo 2265435 5736379 := bstep (se 1 (by rfl) ⟨4302284, by rfl⟩ : syracuseStep 5736379 = 8604569) B8604569
theorem B7648505 : Blo 2265435 7648505 := bstep (se 2 (by rfl) ⟨2868189, by rfl⟩ : syracuseStep 7648505 = 5736379) B5736379
theorem B5099003 : Blo 2265435 5099003 := bstep (se 1 (by rfl) ⟨3824252, by rfl⟩ : syracuseStep 5099003 = 7648505) B7648505
theorem B3399335 : Blo 2265435 3399335 := bstep (se 1 (by rfl) ⟨2549501, by rfl⟩ : syracuseStep 3399335 = 5099003) B5099003
theorem B2266223 : Blo 2265435 2266223 := bstep (se 1 (by rfl) ⟨1699667, by rfl⟩ : syracuseStep 2266223 = 3399335) B3399335
theorem B3399341 : Blo 2265435 3399341 := bbase (se 3 (by rfl) ⟨637376, by rfl⟩ : syracuseStep 3399341 = 1274753) (by norm_num)
theorem B2266227 : Blo 2265435 2266227 := bstep (se 1 (by rfl) ⟨1699670, by rfl⟩ : syracuseStep 2266227 = 3399341) B3399341
theorem B5099021 : Blo 2265435 5099021 := bbase (se 3 (by rfl) ⟨956066, by rfl⟩ : syracuseStep 5099021 = 1912133) (by norm_num)
theorem B3399347 : Blo 2265435 3399347 := bstep (se 1 (by rfl) ⟨2549510, by rfl⟩ : syracuseStep 3399347 = 5099021) B5099021
theorem B2266231 : Blo 2265435 2266231 := bstep (se 1 (by rfl) ⟨1699673, by rfl⟩ : syracuseStep 2266231 = 3399347) B3399347
theorem B2868205 : Blo 2265435 2868205 := bbase (se 3 (by rfl) ⟨537788, by rfl⟩ : syracuseStep 2868205 = 1075577) (by norm_num)
theorem B3824273 : Blo 2265435 3824273 := bstep (se 2 (by rfl) ⟨1434102, by rfl⟩ : syracuseStep 3824273 = 2868205) B2868205
theorem B2549515 : Blo 2265435 2549515 := bstep (se 1 (by rfl) ⟨1912136, by rfl⟩ : syracuseStep 2549515 = 3824273) B3824273
theorem B3399353 : Blo 2265435 3399353 := bstep (se 2 (by rfl) ⟨1274757, by rfl⟩ : syracuseStep 3399353 = 2549515) B2549515
theorem B2266235 : Blo 2265435 2266235 := bstep (se 1 (by rfl) ⟨1699676, by rfl⟩ : syracuseStep 2266235 = 3399353) B3399353
theorem B11788037 : Blo 2265435 11788037 := bbase (se 4 (by rfl) ⟨1105128, by rfl⟩ : syracuseStep 11788037 = 2210257) (by norm_num)
theorem B7858691 : Blo 2265435 7858691 := bstep (se 1 (by rfl) ⟨5894018, by rfl⟩ : syracuseStep 7858691 = 11788037) B11788037
theorem B5239127 : Blo 2265435 5239127 := bstep (se 1 (by rfl) ⟨3929345, by rfl⟩ : syracuseStep 5239127 = 7858691) B7858691
theorem B13971005 : Blo 2265435 13971005 := bstep (se 3 (by rfl) ⟨2619563, by rfl⟩ : syracuseStep 13971005 = 5239127) B5239127
theorem B9314003 : Blo 2265435 9314003 := bstep (se 1 (by rfl) ⟨6985502, by rfl⟩ : syracuseStep 9314003 = 13971005) B13971005
theorem B6209335 : Blo 2265435 6209335 := bstep (se 1 (by rfl) ⟨4657001, by rfl⟩ : syracuseStep 6209335 = 9314003) B9314003
theorem B8279113 : Blo 2265435 8279113 := bstep (se 2 (by rfl) ⟨3104667, by rfl⟩ : syracuseStep 8279113 = 6209335) B6209335
theorem B11038817 : Blo 2265435 11038817 := bstep (se 2 (by rfl) ⟨4139556, by rfl⟩ : syracuseStep 11038817 = 8279113) B8279113
theorem B7359211 : Blo 2265435 7359211 := bstep (se 1 (by rfl) ⟨5519408, by rfl⟩ : syracuseStep 7359211 = 11038817) B11038817
theorem B9812281 : Blo 2265435 9812281 := bstep (se 2 (by rfl) ⟨3679605, by rfl⟩ : syracuseStep 9812281 = 7359211) B7359211
theorem B13083041 : Blo 2265435 13083041 := bstep (se 2 (by rfl) ⟨4906140, by rfl⟩ : syracuseStep 13083041 = 9812281) B9812281
theorem B8722027 : Blo 2265435 8722027 := bstep (se 1 (by rfl) ⟨6541520, by rfl⟩ : syracuseStep 8722027 = 13083041) B13083041
theorem B11629369 : Blo 2265435 11629369 := bstep (se 2 (by rfl) ⟨4361013, by rfl⟩ : syracuseStep 11629369 = 8722027) B8722027
theorem B15505825 : Blo 2265435 15505825 := bstep (se 2 (by rfl) ⟨5814684, by rfl⟩ : syracuseStep 15505825 = 11629369) B11629369
theorem B20674433 : Blo 2265435 20674433 := bstep (se 2 (by rfl) ⟨7752912, by rfl⟩ : syracuseStep 20674433 = 15505825) B15505825
theorem B13782955 : Blo 2265435 13782955 := bstep (se 1 (by rfl) ⟨10337216, by rfl⟩ : syracuseStep 13782955 = 20674433) B20674433
theorem B18377273 : Blo 2265435 18377273 := bstep (se 2 (by rfl) ⟨6891477, by rfl⟩ : syracuseStep 18377273 = 13782955) B13782955
theorem B12251515 : Blo 2265435 12251515 := bstep (se 1 (by rfl) ⟨9188636, by rfl⟩ : syracuseStep 12251515 = 18377273) B18377273
theorem B16335353 : Blo 2265435 16335353 := bstep (se 2 (by rfl) ⟨6125757, by rfl⟩ : syracuseStep 16335353 = 12251515) B12251515
theorem B10890235 : Blo 2265435 10890235 := bstep (se 1 (by rfl) ⟨8167676, by rfl⟩ : syracuseStep 10890235 = 16335353) B16335353
theorem B14520313 : Blo 2265435 14520313 := bstep (se 2 (by rfl) ⟨5445117, by rfl⟩ : syracuseStep 14520313 = 10890235) B10890235
theorem B19360417 : Blo 2265435 19360417 := bstep (se 2 (by rfl) ⟨7260156, by rfl⟩ : syracuseStep 19360417 = 14520313) B14520313
theorem B25813889 : Blo 2265435 25813889 := bstep (se 2 (by rfl) ⟨9680208, by rfl⟩ : syracuseStep 25813889 = 19360417) B19360417
theorem B17209259 : Blo 2265435 17209259 := bstep (se 1 (by rfl) ⟨12906944, by rfl⟩ : syracuseStep 17209259 = 25813889) B25813889
theorem B11472839 : Blo 2265435 11472839 := bstep (se 1 (by rfl) ⟨8604629, by rfl⟩ : syracuseStep 11472839 = 17209259) B17209259
theorem B7648559 : Blo 2265435 7648559 := bstep (se 1 (by rfl) ⟨5736419, by rfl⟩ : syracuseStep 7648559 = 11472839) B11472839
theorem B5099039 : Blo 2265435 5099039 := bstep (se 1 (by rfl) ⟨3824279, by rfl⟩ : syracuseStep 5099039 = 7648559) B7648559
theorem B3399359 : Blo 2265435 3399359 := bstep (se 1 (by rfl) ⟨2549519, by rfl⟩ : syracuseStep 3399359 = 5099039) B5099039
theorem B2266239 : Blo 2265435 2266239 := bstep (se 1 (by rfl) ⟨1699679, by rfl⟩ : syracuseStep 2266239 = 3399359) B3399359
theorem B3399365 : Blo 2265435 3399365 := bbase (se 4 (by rfl) ⟨318690, by rfl⟩ : syracuseStep 3399365 = 637381) (by norm_num)
theorem B2266243 : Blo 2265435 2266243 := bstep (se 1 (by rfl) ⟨1699682, by rfl⟩ : syracuseStep 2266243 = 3399365) B3399365
theorem B3824293 : Blo 2265435 3824293 := bbase (se 4 (by rfl) ⟨358527, by rfl⟩ : syracuseStep 3824293 = 717055) (by norm_num)
theorem B5099057 : Blo 2265435 5099057 := bstep (se 2 (by rfl) ⟨1912146, by rfl⟩ : syracuseStep 5099057 = 3824293) B3824293
theorem B3399371 : Blo 2265435 3399371 := bstep (se 1 (by rfl) ⟨2549528, by rfl⟩ : syracuseStep 3399371 = 5099057) B5099057
theorem B2266247 : Blo 2265435 2266247 := bstep (se 1 (by rfl) ⟨1699685, by rfl⟩ : syracuseStep 2266247 = 3399371) B3399371
theorem B2549533 : Blo 2265435 2549533 := bbase (se 3 (by rfl) ⟨478037, by rfl⟩ : syracuseStep 2549533 = 956075) (by norm_num)
theorem B3399377 : Blo 2265435 3399377 := bstep (se 2 (by rfl) ⟨1274766, by rfl⟩ : syracuseStep 3399377 = 2549533) B2549533
theorem B2266251 : Blo 2265435 2266251 := bstep (se 1 (by rfl) ⟨1699688, by rfl⟩ : syracuseStep 2266251 = 3399377) B3399377
theorem B7648613 : Blo 2265435 7648613 := bbase (se 4 (by rfl) ⟨717057, by rfl⟩ : syracuseStep 7648613 = 1434115) (by norm_num)
theorem B5099075 : Blo 2265435 5099075 := bstep (se 1 (by rfl) ⟨3824306, by rfl⟩ : syracuseStep 5099075 = 7648613) B7648613
theorem B3399383 : Blo 2265435 3399383 := bstep (se 1 (by rfl) ⟨2549537, by rfl⟩ : syracuseStep 3399383 = 5099075) B5099075
theorem B2266255 : Blo 2265435 2266255 := bstep (se 1 (by rfl) ⟨1699691, by rfl⟩ : syracuseStep 2266255 = 3399383) B3399383
theorem B3399389 : Blo 2265435 3399389 := bbase (se 3 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 3399389 = 1274771) (by norm_num)
theorem B2266259 : Blo 2265435 2266259 := bstep (se 1 (by rfl) ⟨1699694, by rfl⟩ : syracuseStep 2266259 = 3399389) B3399389
theorem B5099093 : Blo 2265435 5099093 := bbase (se 8 (by rfl) ⟨29877, by rfl⟩ : syracuseStep 5099093 = 59755) (by norm_num)
theorem B3399395 : Blo 2265435 3399395 := bstep (se 1 (by rfl) ⟨2549546, by rfl⟩ : syracuseStep 3399395 = 5099093) B5099093
theorem B2266263 : Blo 2265435 2266263 := bstep (se 1 (by rfl) ⟨1699697, by rfl⟩ : syracuseStep 2266263 = 3399395) B3399395
theorem B4840165 : Blo 2265435 4840165 := bbase (se 4 (by rfl) ⟨453765, by rfl⟩ : syracuseStep 4840165 = 907531) (by norm_num)
theorem B6453553 : Blo 2265435 6453553 := bstep (se 2 (by rfl) ⟨2420082, by rfl⟩ : syracuseStep 6453553 = 4840165) B4840165
theorem B8604737 : Blo 2265435 8604737 := bstep (se 2 (by rfl) ⟨3226776, by rfl⟩ : syracuseStep 8604737 = 6453553) B6453553
theorem B5736491 : Blo 2265435 5736491 := bstep (se 1 (by rfl) ⟨4302368, by rfl⟩ : syracuseStep 5736491 = 8604737) B8604737
theorem B3824327 : Blo 2265435 3824327 := bstep (se 1 (by rfl) ⟨2868245, by rfl⟩ : syracuseStep 3824327 = 5736491) B5736491
theorem B2549551 : Blo 2265435 2549551 := bstep (se 1 (by rfl) ⟨1912163, by rfl⟩ : syracuseStep 2549551 = 3824327) B3824327
theorem B3399401 : Blo 2265435 3399401 := bstep (se 2 (by rfl) ⟨1274775, by rfl⟩ : syracuseStep 3399401 = 2549551) B2549551
theorem B2266267 : Blo 2265435 2266267 := bstep (se 1 (by rfl) ⟨1699700, by rfl⟩ : syracuseStep 2266267 = 3399401) B3399401
theorem B10890389 : Blo 2265435 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B29041037 : Blo 2265435 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B19360691 : Blo 2265435 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B12907127 : Blo 2265435 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B8604751 : Blo 2265435 8604751 := bstep (se 1 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 8604751 = 12907127) B12907127
theorem B11473001 : Blo 2265435 11473001 := bstep (se 2 (by rfl) ⟨4302375, by rfl⟩ : syracuseStep 11473001 = 8604751) B8604751
theorem B7648667 : Blo 2265435 7648667 := bstep (se 1 (by rfl) ⟨5736500, by rfl⟩ : syracuseStep 7648667 = 11473001) B11473001
theorem B5099111 : Blo 2265435 5099111 := bstep (se 1 (by rfl) ⟨3824333, by rfl⟩ : syracuseStep 5099111 = 7648667) B7648667
theorem B3399407 : Blo 2265435 3399407 := bstep (se 1 (by rfl) ⟨2549555, by rfl⟩ : syracuseStep 3399407 = 5099111) B5099111
theorem B2266271 : Blo 2265435 2266271 := bstep (se 1 (by rfl) ⟨1699703, by rfl⟩ : syracuseStep 2266271 = 3399407) B3399407
theorem B3399413 : Blo 2265435 3399413 := bbase (se 5 (by rfl) ⟨159347, by rfl⟩ : syracuseStep 3399413 = 318695) (by norm_num)
theorem B2266275 : Blo 2265435 2266275 := bstep (se 1 (by rfl) ⟨1699706, by rfl⟩ : syracuseStep 2266275 = 3399413) B3399413
theorem B5168701 : Blo 2265435 5168701 := bbase (se 3 (by rfl) ⟨969131, by rfl⟩ : syracuseStep 5168701 = 1938263) (by norm_num)
theorem B27566405 : Blo 2265435 27566405 := bstep (se 4 (by rfl) ⟨2584350, by rfl⟩ : syracuseStep 27566405 = 5168701) B5168701
theorem B18377603 : Blo 2265435 18377603 := bstep (se 1 (by rfl) ⟨13783202, by rfl⟩ : syracuseStep 18377603 = 27566405) B27566405
theorem B12251735 : Blo 2265435 12251735 := bstep (se 1 (by rfl) ⟨9188801, by rfl⟩ : syracuseStep 12251735 = 18377603) B18377603
theorem B8167823 : Blo 2265435 8167823 := bstep (se 1 (by rfl) ⟨6125867, by rfl⟩ : syracuseStep 8167823 = 12251735) B12251735
theorem B5445215 : Blo 2265435 5445215 := bstep (se 1 (by rfl) ⟨4083911, by rfl⟩ : syracuseStep 5445215 = 8167823) B8167823
theorem B3630143 : Blo 2265435 3630143 := bstep (se 1 (by rfl) ⟨2722607, by rfl⟩ : syracuseStep 3630143 = 5445215) B5445215
theorem B9680381 : Blo 2265435 9680381 := bstep (se 3 (by rfl) ⟨1815071, by rfl⟩ : syracuseStep 9680381 = 3630143) B3630143
theorem B6453587 : Blo 2265435 6453587 := bstep (se 1 (by rfl) ⟨4840190, by rfl⟩ : syracuseStep 6453587 = 9680381) B9680381
theorem B4302391 : Blo 2265435 4302391 := bstep (se 1 (by rfl) ⟨3226793, by rfl⟩ : syracuseStep 4302391 = 6453587) B6453587
theorem B5736521 : Blo 2265435 5736521 := bstep (se 2 (by rfl) ⟨2151195, by rfl⟩ : syracuseStep 5736521 = 4302391) B4302391
theorem B3824347 : Blo 2265435 3824347 := bstep (se 1 (by rfl) ⟨2868260, by rfl⟩ : syracuseStep 3824347 = 5736521) B5736521
theorem B5099129 : Blo 2265435 5099129 := bstep (se 2 (by rfl) ⟨1912173, by rfl⟩ : syracuseStep 5099129 = 3824347) B3824347
theorem B3399419 : Blo 2265435 3399419 := bstep (se 1 (by rfl) ⟨2549564, by rfl⟩ : syracuseStep 3399419 = 5099129) B5099129
theorem B2266279 : Blo 2265435 2266279 := bstep (se 1 (by rfl) ⟨1699709, by rfl⟩ : syracuseStep 2266279 = 3399419) B3399419
theorem B2549569 : Blo 2265435 2549569 := bbase (se 2 (by rfl) ⟨956088, by rfl⟩ : syracuseStep 2549569 = 1912177) (by norm_num)
theorem B3399425 : Blo 2265435 3399425 := bstep (se 2 (by rfl) ⟨1274784, by rfl⟩ : syracuseStep 3399425 = 2549569) B2549569
theorem B2266283 : Blo 2265435 2266283 := bstep (se 1 (by rfl) ⟨1699712, by rfl⟩ : syracuseStep 2266283 = 3399425) B3399425
theorem B5736541 : Blo 2265435 5736541 := bbase (se 3 (by rfl) ⟨1075601, by rfl⟩ : syracuseStep 5736541 = 2151203) (by norm_num)
theorem B7648721 : Blo 2265435 7648721 := bstep (se 2 (by rfl) ⟨2868270, by rfl⟩ : syracuseStep 7648721 = 5736541) B5736541
theorem B5099147 : Blo 2265435 5099147 := bstep (se 1 (by rfl) ⟨3824360, by rfl⟩ : syracuseStep 5099147 = 7648721) B7648721
theorem B3399431 : Blo 2265435 3399431 := bstep (se 1 (by rfl) ⟨2549573, by rfl⟩ : syracuseStep 3399431 = 5099147) B5099147
theorem B2266287 : Blo 2265435 2266287 := bstep (se 1 (by rfl) ⟨1699715, by rfl⟩ : syracuseStep 2266287 = 3399431) B3399431
theorem B3399437 : Blo 2265435 3399437 := bbase (se 3 (by rfl) ⟨637394, by rfl⟩ : syracuseStep 3399437 = 1274789) (by norm_num)
theorem B2266291 : Blo 2265435 2266291 := bstep (se 1 (by rfl) ⟨1699718, by rfl⟩ : syracuseStep 2266291 = 3399437) B3399437
theorem B5099165 : Blo 2265435 5099165 := bbase (se 3 (by rfl) ⟨956093, by rfl⟩ : syracuseStep 5099165 = 1912187) (by norm_num)
theorem B3399443 : Blo 2265435 3399443 := bstep (se 1 (by rfl) ⟨2549582, by rfl⟩ : syracuseStep 3399443 = 5099165) B5099165
theorem B2266295 : Blo 2265435 2266295 := bstep (se 1 (by rfl) ⟨1699721, by rfl⟩ : syracuseStep 2266295 = 3399443) B3399443
theorem B3824381 : Blo 2265435 3824381 := bbase (se 3 (by rfl) ⟨717071, by rfl⟩ : syracuseStep 3824381 = 1434143) (by norm_num)
theorem B2549587 : Blo 2265435 2549587 := bstep (se 1 (by rfl) ⟨1912190, by rfl⟩ : syracuseStep 2549587 = 3824381) B3824381
theorem B3399449 : Blo 2265435 3399449 := bstep (se 2 (by rfl) ⟨1274793, by rfl⟩ : syracuseStep 3399449 = 2549587) B2549587
theorem B2266299 : Blo 2265435 2266299 := bstep (se 1 (by rfl) ⟨1699724, by rfl⟩ : syracuseStep 2266299 = 3399449) B3399449
theorem B3630181 : Blo 2265435 3630181 := bbase (se 4 (by rfl) ⟨340329, by rfl⟩ : syracuseStep 3630181 = 680659) (by norm_num)
theorem B4840241 : Blo 2265435 4840241 := bstep (se 2 (by rfl) ⟨1815090, by rfl⟩ : syracuseStep 4840241 = 3630181) B3630181
theorem B12907309 : Blo 2265435 12907309 := bstep (se 3 (by rfl) ⟨2420120, by rfl⟩ : syracuseStep 12907309 = 4840241) B4840241
theorem B17209745 : Blo 2265435 17209745 := bstep (se 2 (by rfl) ⟨6453654, by rfl⟩ : syracuseStep 17209745 = 12907309) B12907309
theorem B11473163 : Blo 2265435 11473163 := bstep (se 1 (by rfl) ⟨8604872, by rfl⟩ : syracuseStep 11473163 = 17209745) B17209745
theorem B7648775 : Blo 2265435 7648775 := bstep (se 1 (by rfl) ⟨5736581, by rfl⟩ : syracuseStep 7648775 = 11473163) B11473163
theorem B5099183 : Blo 2265435 5099183 := bstep (se 1 (by rfl) ⟨3824387, by rfl⟩ : syracuseStep 5099183 = 7648775) B7648775
theorem B3399455 : Blo 2265435 3399455 := bstep (se 1 (by rfl) ⟨2549591, by rfl⟩ : syracuseStep 3399455 = 5099183) B5099183
theorem B2266303 : Blo 2265435 2266303 := bstep (se 1 (by rfl) ⟨1699727, by rfl⟩ : syracuseStep 2266303 = 3399455) B3399455
theorem B3399461 : Blo 2265435 3399461 := bbase (se 4 (by rfl) ⟨318699, by rfl⟩ : syracuseStep 3399461 = 637399) (by norm_num)
theorem B2266307 : Blo 2265435 2266307 := bstep (se 1 (by rfl) ⟨1699730, by rfl⟩ : syracuseStep 2266307 = 3399461) B3399461
theorem B2868301 : Blo 2265435 2868301 := bbase (se 3 (by rfl) ⟨537806, by rfl⟩ : syracuseStep 2868301 = 1075613) (by norm_num)
theorem B3824401 : Blo 2265435 3824401 := bstep (se 2 (by rfl) ⟨1434150, by rfl⟩ : syracuseStep 3824401 = 2868301) B2868301
theorem B5099201 : Blo 2265435 5099201 := bstep (se 2 (by rfl) ⟨1912200, by rfl⟩ : syracuseStep 5099201 = 3824401) B3824401
theorem B3399467 : Blo 2265435 3399467 := bstep (se 1 (by rfl) ⟨2549600, by rfl⟩ : syracuseStep 3399467 = 5099201) B5099201
theorem B2266311 : Blo 2265435 2266311 := bstep (se 1 (by rfl) ⟨1699733, by rfl⟩ : syracuseStep 2266311 = 3399467) B3399467
theorem B2549605 : Blo 2265435 2549605 := bbase (se 4 (by rfl) ⟨239025, by rfl⟩ : syracuseStep 2549605 = 478051) (by norm_num)
theorem B3399473 : Blo 2265435 3399473 := bstep (se 2 (by rfl) ⟨1274802, by rfl⟩ : syracuseStep 3399473 = 2549605) B2549605
theorem B2266315 : Blo 2265435 2266315 := bstep (se 1 (by rfl) ⟨1699736, by rfl⟩ : syracuseStep 2266315 = 3399473) B3399473
theorem B6453701 : Blo 2265435 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B4302467 : Blo 2265435 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B2868311 : Blo 2265435 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B7648829 : Blo 2265435 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B5099219 : Blo 2265435 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B3399479 : Blo 2265435 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B2266319 : Blo 2265435 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B3399485 : Blo 2265435 3399485 := bbase (se 3 (by rfl) ⟨637403, by rfl⟩ : syracuseStep 3399485 = 1274807) (by norm_num)
theorem B2266323 : Blo 2265435 2266323 := bstep (se 1 (by rfl) ⟨1699742, by rfl⟩ : syracuseStep 2266323 = 3399485) B3399485
theorem B5099237 : Blo 2265435 5099237 := bbase (se 4 (by rfl) ⟨478053, by rfl⟩ : syracuseStep 5099237 = 956107) (by norm_num)
theorem B3399491 : Blo 2265435 3399491 := bstep (se 1 (by rfl) ⟨2549618, by rfl⟩ : syracuseStep 3399491 = 5099237) B5099237
theorem B2266327 : Blo 2265435 2266327 := bstep (se 1 (by rfl) ⟨1699745, by rfl⟩ : syracuseStep 2266327 = 3399491) B3399491
theorem B5736653 : Blo 2265435 5736653 := bbase (se 3 (by rfl) ⟨1075622, by rfl⟩ : syracuseStep 5736653 = 2151245) (by norm_num)
theorem B3824435 : Blo 2265435 3824435 := bstep (se 1 (by rfl) ⟨2868326, by rfl⟩ : syracuseStep 3824435 = 5736653) B5736653
theorem B2549623 : Blo 2265435 2549623 := bstep (se 1 (by rfl) ⟨1912217, by rfl⟩ : syracuseStep 2549623 = 3824435) B3824435
theorem B3399497 : Blo 2265435 3399497 := bstep (se 2 (by rfl) ⟨1274811, by rfl⟩ : syracuseStep 3399497 = 2549623) B2549623
theorem B2266331 : Blo 2265435 2266331 := bstep (se 1 (by rfl) ⟨1699748, by rfl⟩ : syracuseStep 2266331 = 3399497) B3399497
theorem B4084013 : Blo 2265435 4084013 := bbase (se 3 (by rfl) ⟨765752, by rfl⟩ : syracuseStep 4084013 = 1531505) (by norm_num)
theorem B2722675 : Blo 2265435 2722675 := bstep (se 1 (by rfl) ⟨2042006, by rfl⟩ : syracuseStep 2722675 = 4084013) B4084013
theorem B3630233 : Blo 2265435 3630233 := bstep (se 2 (by rfl) ⟨1361337, by rfl⟩ : syracuseStep 3630233 = 2722675) B2722675
theorem B2420155 : Blo 2265435 2420155 := bstep (se 1 (by rfl) ⟨1815116, by rfl⟩ : syracuseStep 2420155 = 3630233) B3630233
theorem B3226873 : Blo 2265435 3226873 := bstep (se 2 (by rfl) ⟨1210077, by rfl⟩ : syracuseStep 3226873 = 2420155) B2420155
theorem B4302497 : Blo 2265435 4302497 := bstep (se 2 (by rfl) ⟨1613436, by rfl⟩ : syracuseStep 4302497 = 3226873) B3226873
theorem B11473325 : Blo 2265435 11473325 := bstep (se 3 (by rfl) ⟨2151248, by rfl⟩ : syracuseStep 11473325 = 4302497) B4302497
theorem B7648883 : Blo 2265435 7648883 := bstep (se 1 (by rfl) ⟨5736662, by rfl⟩ : syracuseStep 7648883 = 11473325) B11473325
theorem B5099255 : Blo 2265435 5099255 := bstep (se 1 (by rfl) ⟨3824441, by rfl⟩ : syracuseStep 5099255 = 7648883) B7648883
theorem B3399503 : Blo 2265435 3399503 := bstep (se 1 (by rfl) ⟨2549627, by rfl⟩ : syracuseStep 3399503 = 5099255) B5099255
theorem B2266335 : Blo 2265435 2266335 := bstep (se 1 (by rfl) ⟨1699751, by rfl⟩ : syracuseStep 2266335 = 3399503) B3399503
theorem B3399509 : Blo 2265435 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B2266339 : Blo 2265435 2266339 := bstep (se 1 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 2266339 = 3399509) B3399509
theorem B8168053 : Blo 2265435 8168053 := bbase (se 5 (by rfl) ⟨382877, by rfl⟩ : syracuseStep 8168053 = 765755) (by norm_num)
theorem B10890737 : Blo 2265435 10890737 := bstep (se 2 (by rfl) ⟨4084026, by rfl⟩ : syracuseStep 10890737 = 8168053) B8168053
theorem B7260491 : Blo 2265435 7260491 := bstep (se 1 (by rfl) ⟨5445368, by rfl⟩ : syracuseStep 7260491 = 10890737) B10890737
theorem B4840327 : Blo 2265435 4840327 := bstep (se 1 (by rfl) ⟨3630245, by rfl⟩ : syracuseStep 4840327 = 7260491) B7260491
theorem B6453769 : Blo 2265435 6453769 := bstep (se 2 (by rfl) ⟨2420163, by rfl⟩ : syracuseStep 6453769 = 4840327) B4840327
theorem B8605025 : Blo 2265435 8605025 := bstep (se 2 (by rfl) ⟨3226884, by rfl⟩ : syracuseStep 8605025 = 6453769) B6453769
theorem B5736683 : Blo 2265435 5736683 := bstep (se 1 (by rfl) ⟨4302512, by rfl⟩ : syracuseStep 5736683 = 8605025) B8605025
theorem B3824455 : Blo 2265435 3824455 := bstep (se 1 (by rfl) ⟨2868341, by rfl⟩ : syracuseStep 3824455 = 5736683) B5736683
theorem B5099273 : Blo 2265435 5099273 := bstep (se 2 (by rfl) ⟨1912227, by rfl⟩ : syracuseStep 5099273 = 3824455) B3824455
theorem B3399515 : Blo 2265435 3399515 := bstep (se 1 (by rfl) ⟨2549636, by rfl⟩ : syracuseStep 3399515 = 5099273) B5099273
theorem B2266343 : Blo 2265435 2266343 := bstep (se 1 (by rfl) ⟨1699757, by rfl⟩ : syracuseStep 2266343 = 3399515) B3399515
theorem B2549641 : Blo 2265435 2549641 := bbase (se 2 (by rfl) ⟨956115, by rfl⟩ : syracuseStep 2549641 = 1912231) (by norm_num)
theorem B3399521 : Blo 2265435 3399521 := bstep (se 2 (by rfl) ⟨1274820, by rfl⟩ : syracuseStep 3399521 = 2549641) B2549641
theorem B2266347 : Blo 2265435 2266347 := bstep (se 1 (by rfl) ⟨1699760, by rfl⟩ : syracuseStep 2266347 = 3399521) B3399521
theorem B3445909 : Blo 2265435 3445909 := bbase (se 6 (by rfl) ⟨80763, by rfl⟩ : syracuseStep 3445909 = 161527) (by norm_num)
theorem B18378181 : Blo 2265435 18378181 := bstep (se 4 (by rfl) ⟨1722954, by rfl⟩ : syracuseStep 18378181 = 3445909) B3445909
theorem B98016965 : Blo 2265435 98016965 := bstep (se 4 (by rfl) ⟨9189090, by rfl⟩ : syracuseStep 98016965 = 18378181) B18378181
theorem B65344643 : Blo 2265435 65344643 := bstep (se 1 (by rfl) ⟨49008482, by rfl⟩ : syracuseStep 65344643 = 98016965) B98016965
theorem B43563095 : Blo 2265435 43563095 := bstep (se 1 (by rfl) ⟨32672321, by rfl⟩ : syracuseStep 43563095 = 65344643) B65344643
theorem B29042063 : Blo 2265435 29042063 := bstep (se 1 (by rfl) ⟨21781547, by rfl⟩ : syracuseStep 29042063 = 43563095) B43563095
theorem B19361375 : Blo 2265435 19361375 := bstep (se 1 (by rfl) ⟨14521031, by rfl⟩ : syracuseStep 19361375 = 29042063) B29042063
theorem B12907583 : Blo 2265435 12907583 := bstep (se 1 (by rfl) ⟨9680687, by rfl⟩ : syracuseStep 12907583 = 19361375) B19361375
theorem B8605055 : Blo 2265435 8605055 := bstep (se 1 (by rfl) ⟨6453791, by rfl⟩ : syracuseStep 8605055 = 12907583) B12907583
theorem B5736703 : Blo 2265435 5736703 := bstep (se 1 (by rfl) ⟨4302527, by rfl⟩ : syracuseStep 5736703 = 8605055) B8605055
theorem B7648937 : Blo 2265435 7648937 := bstep (se 2 (by rfl) ⟨2868351, by rfl⟩ : syracuseStep 7648937 = 5736703) B5736703
theorem B5099291 : Blo 2265435 5099291 := bstep (se 1 (by rfl) ⟨3824468, by rfl⟩ : syracuseStep 5099291 = 7648937) B7648937
theorem B3399527 : Blo 2265435 3399527 := bstep (se 1 (by rfl) ⟨2549645, by rfl⟩ : syracuseStep 3399527 = 5099291) B5099291
theorem B2266351 : Blo 2265435 2266351 := bstep (se 1 (by rfl) ⟨1699763, by rfl⟩ : syracuseStep 2266351 = 3399527) B3399527
theorem B3399533 : Blo 2265435 3399533 := bbase (se 3 (by rfl) ⟨637412, by rfl⟩ : syracuseStep 3399533 = 1274825) (by norm_num)
theorem B2266355 : Blo 2265435 2266355 := bstep (se 1 (by rfl) ⟨1699766, by rfl⟩ : syracuseStep 2266355 = 3399533) B3399533
theorem B5099309 : Blo 2265435 5099309 := bbase (se 3 (by rfl) ⟨956120, by rfl⟩ : syracuseStep 5099309 = 1912241) (by norm_num)
theorem B3399539 : Blo 2265435 3399539 := bstep (se 1 (by rfl) ⟨2549654, by rfl⟩ : syracuseStep 3399539 = 5099309) B5099309
theorem B2266359 : Blo 2265435 2266359 := bstep (se 1 (by rfl) ⟨1699769, by rfl⟩ : syracuseStep 2266359 = 3399539) B3399539
theorem B9680741 : Blo 2265435 9680741 := bbase (se 4 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 9680741 = 1815139) (by norm_num)
theorem B6453827 : Blo 2265435 6453827 := bstep (se 1 (by rfl) ⟨4840370, by rfl⟩ : syracuseStep 6453827 = 9680741) B9680741
theorem B4302551 : Blo 2265435 4302551 := bstep (se 1 (by rfl) ⟨3226913, by rfl⟩ : syracuseStep 4302551 = 6453827) B6453827
theorem B2868367 : Blo 2265435 2868367 := bstep (se 1 (by rfl) ⟨2151275, by rfl⟩ : syracuseStep 2868367 = 4302551) B4302551
theorem B3824489 : Blo 2265435 3824489 := bstep (se 2 (by rfl) ⟨1434183, by rfl⟩ : syracuseStep 3824489 = 2868367) B2868367
theorem B2549659 : Blo 2265435 2549659 := bstep (se 1 (by rfl) ⟨1912244, by rfl⟩ : syracuseStep 2549659 = 3824489) B3824489
theorem B3399545 : Blo 2265435 3399545 := bstep (se 2 (by rfl) ⟨1274829, by rfl⟩ : syracuseStep 3399545 = 2549659) B2549659
theorem B2266363 : Blo 2265435 2266363 := bstep (se 1 (by rfl) ⟨1699772, by rfl⟩ : syracuseStep 2266363 = 3399545) B3399545
theorem B4084069 : Blo 2265435 4084069 := bbase (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) (by norm_num)
theorem B5445425 : Blo 2265435 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B14521133 : Blo 2265435 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B38723021 : Blo 2265435 38723021 := bstep (se 3 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 38723021 = 14521133) B14521133
theorem B25815347 : Blo 2265435 25815347 := bstep (se 1 (by rfl) ⟨19361510, by rfl⟩ : syracuseStep 25815347 = 38723021) B38723021
theorem B17210231 : Blo 2265435 17210231 := bstep (se 1 (by rfl) ⟨12907673, by rfl⟩ : syracuseStep 17210231 = 25815347) B25815347
theorem B11473487 : Blo 2265435 11473487 := bstep (se 1 (by rfl) ⟨8605115, by rfl⟩ : syracuseStep 11473487 = 17210231) B17210231
theorem B7648991 : Blo 2265435 7648991 := bstep (se 1 (by rfl) ⟨5736743, by rfl⟩ : syracuseStep 7648991 = 11473487) B11473487
theorem B5099327 : Blo 2265435 5099327 := bstep (se 1 (by rfl) ⟨3824495, by rfl⟩ : syracuseStep 5099327 = 7648991) B7648991
theorem B3399551 : Blo 2265435 3399551 := bstep (se 1 (by rfl) ⟨2549663, by rfl⟩ : syracuseStep 3399551 = 5099327) B5099327
theorem B2266367 : Blo 2265435 2266367 := bstep (se 1 (by rfl) ⟨1699775, by rfl⟩ : syracuseStep 2266367 = 3399551) B3399551
theorem B3399557 : Blo 2265435 3399557 := bbase (se 4 (by rfl) ⟨318708, by rfl⟩ : syracuseStep 3399557 = 637417) (by norm_num)
theorem B2266371 : Blo 2265435 2266371 := bstep (se 1 (by rfl) ⟨1699778, by rfl⟩ : syracuseStep 2266371 = 3399557) B3399557
theorem B3824509 : Blo 2265435 3824509 := bbase (se 3 (by rfl) ⟨717095, by rfl⟩ : syracuseStep 3824509 = 1434191) (by norm_num)
theorem B5099345 : Blo 2265435 5099345 := bstep (se 2 (by rfl) ⟨1912254, by rfl⟩ : syracuseStep 5099345 = 3824509) B3824509
theorem B3399563 : Blo 2265435 3399563 := bstep (se 1 (by rfl) ⟨2549672, by rfl⟩ : syracuseStep 3399563 = 5099345) B5099345
theorem B2266375 : Blo 2265435 2266375 := bstep (se 1 (by rfl) ⟨1699781, by rfl⟩ : syracuseStep 2266375 = 3399563) B3399563
theorem B2549677 : Blo 2265435 2549677 := bbase (se 3 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 2549677 = 956129) (by norm_num)
theorem B3399569 : Blo 2265435 3399569 := bstep (se 2 (by rfl) ⟨1274838, by rfl⟩ : syracuseStep 3399569 = 2549677) B2549677
theorem B2266379 : Blo 2265435 2266379 := bstep (se 1 (by rfl) ⟨1699784, by rfl⟩ : syracuseStep 2266379 = 3399569) B3399569
theorem B7649045 : Blo 2265435 7649045 := bbase (se 6 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 7649045 = 358549) (by norm_num)
theorem B5099363 : Blo 2265435 5099363 := bstep (se 1 (by rfl) ⟨3824522, by rfl⟩ : syracuseStep 5099363 = 7649045) B7649045
theorem B3399575 : Blo 2265435 3399575 := bstep (se 1 (by rfl) ⟨2549681, by rfl⟩ : syracuseStep 3399575 = 5099363) B5099363
theorem B2266383 : Blo 2265435 2266383 := bstep (se 1 (by rfl) ⟨1699787, by rfl⟩ : syracuseStep 2266383 = 3399575) B3399575
theorem B3399581 : Blo 2265435 3399581 := bbase (se 3 (by rfl) ⟨637421, by rfl⟩ : syracuseStep 3399581 = 1274843) (by norm_num)
theorem B2266387 : Blo 2265435 2266387 := bstep (se 1 (by rfl) ⟨1699790, by rfl⟩ : syracuseStep 2266387 = 3399581) B3399581
theorem B5099381 : Blo 2265435 5099381 := bbase (se 5 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 5099381 = 478067) (by norm_num)
theorem B3399587 : Blo 2265435 3399587 := bstep (se 1 (by rfl) ⟨2549690, by rfl⟩ : syracuseStep 3399587 = 5099381) B5099381
theorem B2266391 : Blo 2265435 2266391 := bstep (se 1 (by rfl) ⟨1699793, by rfl⟩ : syracuseStep 2266391 = 3399587) B3399587
theorem B21781973 : Blo 2265435 21781973 := bbase (se 7 (by rfl) ⟨255257, by rfl⟩ : syracuseStep 21781973 = 510515) (by norm_num)
theorem B14521315 : Blo 2265435 14521315 := bstep (se 1 (by rfl) ⟨10890986, by rfl⟩ : syracuseStep 14521315 = 21781973) B21781973
theorem B19361753 : Blo 2265435 19361753 := bstep (se 2 (by rfl) ⟨7260657, by rfl⟩ : syracuseStep 19361753 = 14521315) B14521315
theorem B12907835 : Blo 2265435 12907835 := bstep (se 1 (by rfl) ⟨9680876, by rfl⟩ : syracuseStep 12907835 = 19361753) B19361753
theorem B8605223 : Blo 2265435 8605223 := bstep (se 1 (by rfl) ⟨6453917, by rfl⟩ : syracuseStep 8605223 = 12907835) B12907835
theorem B5736815 : Blo 2265435 5736815 := bstep (se 1 (by rfl) ⟨4302611, by rfl⟩ : syracuseStep 5736815 = 8605223) B8605223
theorem B3824543 : Blo 2265435 3824543 := bstep (se 1 (by rfl) ⟨2868407, by rfl⟩ : syracuseStep 3824543 = 5736815) B5736815
theorem B2549695 : Blo 2265435 2549695 := bstep (se 1 (by rfl) ⟨1912271, by rfl⟩ : syracuseStep 2549695 = 3824543) B3824543
theorem B3399593 : Blo 2265435 3399593 := bstep (se 2 (by rfl) ⟨1274847, by rfl⟩ : syracuseStep 3399593 = 2549695) B2549695
theorem B2266395 : Blo 2265435 2266395 := bstep (se 1 (by rfl) ⟨1699796, by rfl⟩ : syracuseStep 2266395 = 3399593) B3399593
theorem B8605237 : Blo 2265435 8605237 := bbase (se 5 (by rfl) ⟨403370, by rfl⟩ : syracuseStep 8605237 = 806741) (by norm_num)
theorem B11473649 : Blo 2265435 11473649 := bstep (se 2 (by rfl) ⟨4302618, by rfl⟩ : syracuseStep 11473649 = 8605237) B8605237
theorem B7649099 : Blo 2265435 7649099 := bstep (se 1 (by rfl) ⟨5736824, by rfl⟩ : syracuseStep 7649099 = 11473649) B11473649
theorem B5099399 : Blo 2265435 5099399 := bstep (se 1 (by rfl) ⟨3824549, by rfl⟩ : syracuseStep 5099399 = 7649099) B7649099
theorem B3399599 : Blo 2265435 3399599 := bstep (se 1 (by rfl) ⟨2549699, by rfl⟩ : syracuseStep 3399599 = 5099399) B5099399
theorem B2266399 : Blo 2265435 2266399 := bstep (se 1 (by rfl) ⟨1699799, by rfl⟩ : syracuseStep 2266399 = 3399599) B3399599
theorem B3399605 : Blo 2265435 3399605 := bbase (se 5 (by rfl) ⟨159356, by rfl⟩ : syracuseStep 3399605 = 318713) (by norm_num)
theorem B2266403 : Blo 2265435 2266403 := bstep (se 1 (by rfl) ⟨1699802, by rfl⟩ : syracuseStep 2266403 = 3399605) B3399605
theorem B5736845 : Blo 2265435 5736845 := bbase (se 3 (by rfl) ⟨1075658, by rfl⟩ : syracuseStep 5736845 = 2151317) (by norm_num)
theorem B3824563 : Blo 2265435 3824563 := bstep (se 1 (by rfl) ⟨2868422, by rfl⟩ : syracuseStep 3824563 = 5736845) B5736845
theorem B5099417 : Blo 2265435 5099417 := bstep (se 2 (by rfl) ⟨1912281, by rfl⟩ : syracuseStep 5099417 = 3824563) B3824563
theorem B3399611 : Blo 2265435 3399611 := bstep (se 1 (by rfl) ⟨2549708, by rfl⟩ : syracuseStep 3399611 = 5099417) B5099417
theorem B2266407 : Blo 2265435 2266407 := bstep (se 1 (by rfl) ⟨1699805, by rfl⟩ : syracuseStep 2266407 = 3399611) B3399611
theorem B2549713 : Blo 2265435 2549713 := bbase (se 2 (by rfl) ⟨956142, by rfl⟩ : syracuseStep 2549713 = 1912285) (by norm_num)
theorem B3399617 : Blo 2265435 3399617 := bstep (se 2 (by rfl) ⟨1274856, by rfl⟩ : syracuseStep 3399617 = 2549713) B2549713
theorem B2266411 : Blo 2265435 2266411 := bstep (se 1 (by rfl) ⟨1699808, by rfl⟩ : syracuseStep 2266411 = 3399617) B3399617
theorem B4084157 : Blo 2265435 4084157 := bbase (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) (by norm_num)
theorem B2722771 : Blo 2265435 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B3630361 : Blo 2265435 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B4840481 : Blo 2265435 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B3226987 : Blo 2265435 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B4302649 : Blo 2265435 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B5736865 : Blo 2265435 5736865 := bstep (se 2 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 5736865 = 4302649) B4302649
theorem B7649153 : Blo 2265435 7649153 := bstep (se 2 (by rfl) ⟨2868432, by rfl⟩ : syracuseStep 7649153 = 5736865) B5736865
theorem B5099435 : Blo 2265435 5099435 := bstep (se 1 (by rfl) ⟨3824576, by rfl⟩ : syracuseStep 5099435 = 7649153) B7649153
theorem B3399623 : Blo 2265435 3399623 := bstep (se 1 (by rfl) ⟨2549717, by rfl⟩ : syracuseStep 3399623 = 5099435) B5099435
theorem B2266415 : Blo 2265435 2266415 := bstep (se 1 (by rfl) ⟨1699811, by rfl⟩ : syracuseStep 2266415 = 3399623) B3399623
theorem B3399629 : Blo 2265435 3399629 := bbase (se 3 (by rfl) ⟨637430, by rfl⟩ : syracuseStep 3399629 = 1274861) (by norm_num)
theorem B2266419 : Blo 2265435 2266419 := bstep (se 1 (by rfl) ⟨1699814, by rfl⟩ : syracuseStep 2266419 = 3399629) B3399629
theorem B5099453 : Blo 2265435 5099453 := bbase (se 3 (by rfl) ⟨956147, by rfl⟩ : syracuseStep 5099453 = 1912295) (by norm_num)
theorem B3399635 : Blo 2265435 3399635 := bstep (se 1 (by rfl) ⟨2549726, by rfl⟩ : syracuseStep 3399635 = 5099453) B5099453
theorem B2266423 : Blo 2265435 2266423 := bstep (se 1 (by rfl) ⟨1699817, by rfl⟩ : syracuseStep 2266423 = 3399635) B3399635
theorem B3824597 : Blo 2265435 3824597 := bbase (se 7 (by rfl) ⟨44819, by rfl⟩ : syracuseStep 3824597 = 89639) (by norm_num)
theorem B2549731 : Blo 2265435 2549731 := bstep (se 1 (by rfl) ⟨1912298, by rfl⟩ : syracuseStep 2549731 = 3824597) B3824597
theorem B3399641 : Blo 2265435 3399641 := bstep (se 2 (by rfl) ⟨1274865, by rfl⟩ : syracuseStep 3399641 = 2549731) B2549731
theorem B2266427 : Blo 2265435 2266427 := bstep (se 1 (by rfl) ⟨1699820, by rfl⟩ : syracuseStep 2266427 = 3399641) B3399641
theorem B9681029 : Blo 2265435 9681029 := bbase (se 4 (by rfl) ⟨907596, by rfl⟩ : syracuseStep 9681029 = 1815193) (by norm_num)
theorem B6454019 : Blo 2265435 6454019 := bstep (se 1 (by rfl) ⟨4840514, by rfl⟩ : syracuseStep 6454019 = 9681029) B9681029
theorem B17210717 : Blo 2265435 17210717 := bstep (se 3 (by rfl) ⟨3227009, by rfl⟩ : syracuseStep 17210717 = 6454019) B6454019
theorem B11473811 : Blo 2265435 11473811 := bstep (se 1 (by rfl) ⟨8605358, by rfl⟩ : syracuseStep 11473811 = 17210717) B17210717
theorem B7649207 : Blo 2265435 7649207 := bstep (se 1 (by rfl) ⟨5736905, by rfl⟩ : syracuseStep 7649207 = 11473811) B11473811
theorem B5099471 : Blo 2265435 5099471 := bstep (se 1 (by rfl) ⟨3824603, by rfl⟩ : syracuseStep 5099471 = 7649207) B7649207
theorem B3399647 : Blo 2265435 3399647 := bstep (se 1 (by rfl) ⟨2549735, by rfl⟩ : syracuseStep 3399647 = 5099471) B5099471
theorem B2266431 : Blo 2265435 2266431 := bstep (se 1 (by rfl) ⟨1699823, by rfl⟩ : syracuseStep 2266431 = 3399647) B3399647
theorem B3399653 : Blo 2265435 3399653 := bbase (se 4 (by rfl) ⟨318717, by rfl⟩ : syracuseStep 3399653 = 637435) (by norm_num)
theorem B2266435 : Blo 2265435 2266435 := bstep (se 1 (by rfl) ⟨1699826, by rfl⟩ : syracuseStep 2266435 = 3399653) B3399653
theorem B29439445 : Blo 2265435 29439445 := bbase (se 7 (by rfl) ⟨344993, by rfl⟩ : syracuseStep 29439445 = 689987) (by norm_num)
theorem B39252593 : Blo 2265435 39252593 := bstep (se 2 (by rfl) ⟨14719722, by rfl⟩ : syracuseStep 39252593 = 29439445) B29439445
theorem B26168395 : Blo 2265435 26168395 := bstep (se 1 (by rfl) ⟨19626296, by rfl⟩ : syracuseStep 26168395 = 39252593) B39252593
theorem B34891193 : Blo 2265435 34891193 := bstep (se 2 (by rfl) ⟨13084197, by rfl⟩ : syracuseStep 34891193 = 26168395) B26168395
theorem B93043181 : Blo 2265435 93043181 := bstep (se 3 (by rfl) ⟨17445596, by rfl⟩ : syracuseStep 93043181 = 34891193) B34891193
theorem B62028787 : Blo 2265435 62028787 := bstep (se 1 (by rfl) ⟨46521590, by rfl⟩ : syracuseStep 62028787 = 93043181) B93043181
theorem B82705049 : Blo 2265435 82705049 := bstep (se 2 (by rfl) ⟨31014393, by rfl⟩ : syracuseStep 82705049 = 62028787) B62028787
theorem B55136699 : Blo 2265435 55136699 := bstep (se 1 (by rfl) ⟨41352524, by rfl⟩ : syracuseStep 55136699 = 82705049) B82705049
theorem B36757799 : Blo 2265435 36757799 := bstep (se 1 (by rfl) ⟨27568349, by rfl⟩ : syracuseStep 36757799 = 55136699) B55136699
theorem B24505199 : Blo 2265435 24505199 := bstep (se 1 (by rfl) ⟨18378899, by rfl⟩ : syracuseStep 24505199 = 36757799) B36757799
theorem B16336799 : Blo 2265435 16336799 := bstep (se 1 (by rfl) ⟨12252599, by rfl⟩ : syracuseStep 16336799 = 24505199) B24505199
theorem B10891199 : Blo 2265435 10891199 := bstep (se 1 (by rfl) ⟨8168399, by rfl⟩ : syracuseStep 10891199 = 16336799) B16336799
theorem B7260799 : Blo 2265435 7260799 := bstep (se 1 (by rfl) ⟨5445599, by rfl⟩ : syracuseStep 7260799 = 10891199) B10891199
theorem B9681065 : Blo 2265435 9681065 := bstep (se 2 (by rfl) ⟨3630399, by rfl⟩ : syracuseStep 9681065 = 7260799) B7260799
theorem B6454043 : Blo 2265435 6454043 := bstep (se 1 (by rfl) ⟨4840532, by rfl⟩ : syracuseStep 6454043 = 9681065) B9681065
theorem B4302695 : Blo 2265435 4302695 := bstep (se 1 (by rfl) ⟨3227021, by rfl⟩ : syracuseStep 4302695 = 6454043) B6454043
theorem B2868463 : Blo 2265435 2868463 := bstep (se 1 (by rfl) ⟨2151347, by rfl⟩ : syracuseStep 2868463 = 4302695) B4302695
theorem B3824617 : Blo 2265435 3824617 := bstep (se 2 (by rfl) ⟨1434231, by rfl⟩ : syracuseStep 3824617 = 2868463) B2868463
theorem B5099489 : Blo 2265435 5099489 := bstep (se 2 (by rfl) ⟨1912308, by rfl⟩ : syracuseStep 5099489 = 3824617) B3824617
theorem B3399659 : Blo 2265435 3399659 := bstep (se 1 (by rfl) ⟨2549744, by rfl⟩ : syracuseStep 3399659 = 5099489) B5099489
theorem B2266439 : Blo 2265435 2266439 := bstep (se 1 (by rfl) ⟨1699829, by rfl⟩ : syracuseStep 2266439 = 3399659) B3399659
theorem B2549749 : Blo 2265435 2549749 := bbase (se 5 (by rfl) ⟨119519, by rfl⟩ : syracuseStep 2549749 = 239039) (by norm_num)
theorem B3399665 : Blo 2265435 3399665 := bstep (se 2 (by rfl) ⟨1274874, by rfl⟩ : syracuseStep 3399665 = 2549749) B2549749
theorem B2266443 : Blo 2265435 2266443 := bstep (se 1 (by rfl) ⟨1699832, by rfl⟩ : syracuseStep 2266443 = 3399665) B3399665
theorem B2868473 : Blo 2265435 2868473 := bbase (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) (by norm_num)
theorem B7649261 : Blo 2265435 7649261 := bstep (se 3 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 7649261 = 2868473) B2868473
theorem B5099507 : Blo 2265435 5099507 := bstep (se 1 (by rfl) ⟨3824630, by rfl⟩ : syracuseStep 5099507 = 7649261) B7649261
theorem B3399671 : Blo 2265435 3399671 := bstep (se 1 (by rfl) ⟨2549753, by rfl⟩ : syracuseStep 3399671 = 5099507) B5099507
theorem B2266447 : Blo 2265435 2266447 := bstep (se 1 (by rfl) ⟨1699835, by rfl⟩ : syracuseStep 2266447 = 3399671) B3399671
theorem B3399677 : Blo 2265435 3399677 := bbase (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) (by norm_num)
theorem B2266451 : Blo 2265435 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B5099525 : Blo 2265435 5099525 := bbase (se 4 (by rfl) ⟨478080, by rfl⟩ : syracuseStep 5099525 = 956161) (by norm_num)
theorem B3399683 : Blo 2265435 3399683 := bstep (se 1 (by rfl) ⟨2549762, by rfl⟩ : syracuseStep 3399683 = 5099525) B5099525
theorem B2266455 : Blo 2265435 2266455 := bstep (se 1 (by rfl) ⟨1699841, by rfl⟩ : syracuseStep 2266455 = 3399683) B3399683
theorem B4302733 : Blo 2265435 4302733 := bbase (se 3 (by rfl) ⟨806762, by rfl⟩ : syracuseStep 4302733 = 1613525) (by norm_num)
theorem B5736977 : Blo 2265435 5736977 := bstep (se 2 (by rfl) ⟨2151366, by rfl⟩ : syracuseStep 5736977 = 4302733) B4302733
theorem B3824651 : Blo 2265435 3824651 := bstep (se 1 (by rfl) ⟨2868488, by rfl⟩ : syracuseStep 3824651 = 5736977) B5736977
theorem B2549767 : Blo 2265435 2549767 := bstep (se 1 (by rfl) ⟨1912325, by rfl⟩ : syracuseStep 2549767 = 3824651) B3824651
theorem B3399689 : Blo 2265435 3399689 := bstep (se 2 (by rfl) ⟨1274883, by rfl⟩ : syracuseStep 3399689 = 2549767) B2549767
theorem B2266459 : Blo 2265435 2266459 := bstep (se 1 (by rfl) ⟨1699844, by rfl⟩ : syracuseStep 2266459 = 3399689) B3399689
theorem B11473973 : Blo 2265435 11473973 := bbase (se 5 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 11473973 = 1075685) (by norm_num)
theorem B7649315 : Blo 2265435 7649315 := bstep (se 1 (by rfl) ⟨5736986, by rfl⟩ : syracuseStep 7649315 = 11473973) B11473973
theorem B5099543 : Blo 2265435 5099543 := bstep (se 1 (by rfl) ⟨3824657, by rfl⟩ : syracuseStep 5099543 = 7649315) B7649315
theorem B3399695 : Blo 2265435 3399695 := bstep (se 1 (by rfl) ⟨2549771, by rfl⟩ : syracuseStep 3399695 = 5099543) B5099543
theorem B2266463 : Blo 2265435 2266463 := bstep (se 1 (by rfl) ⟨1699847, by rfl⟩ : syracuseStep 2266463 = 3399695) B3399695
theorem B3399701 : Blo 2265435 3399701 := bbase (se 6 (by rfl) ⟨79680, by rfl⟩ : syracuseStep 3399701 = 159361) (by norm_num)
theorem B2266467 : Blo 2265435 2266467 := bstep (se 1 (by rfl) ⟨1699850, by rfl⟩ : syracuseStep 2266467 = 3399701) B3399701
theorem B4594789 : Blo 2265435 4594789 := bbase (se 4 (by rfl) ⟨430761, by rfl⟩ : syracuseStep 4594789 = 861523) (by norm_num)
theorem B24505541 : Blo 2265435 24505541 := bstep (se 4 (by rfl) ⟨2297394, by rfl⟩ : syracuseStep 24505541 = 4594789) B4594789
theorem B16337027 : Blo 2265435 16337027 := bstep (se 1 (by rfl) ⟨12252770, by rfl⟩ : syracuseStep 16337027 = 24505541) B24505541
theorem B10891351 : Blo 2265435 10891351 := bstep (se 1 (by rfl) ⟨8168513, by rfl⟩ : syracuseStep 10891351 = 16337027) B16337027
theorem B14521801 : Blo 2265435 14521801 := bstep (se 2 (by rfl) ⟨5445675, by rfl⟩ : syracuseStep 14521801 = 10891351) B10891351
theorem B19362401 : Blo 2265435 19362401 := bstep (se 2 (by rfl) ⟨7260900, by rfl⟩ : syracuseStep 19362401 = 14521801) B14521801
theorem B12908267 : Blo 2265435 12908267 := bstep (se 1 (by rfl) ⟨9681200, by rfl⟩ : syracuseStep 12908267 = 19362401) B19362401
theorem B8605511 : Blo 2265435 8605511 := bstep (se 1 (by rfl) ⟨6454133, by rfl⟩ : syracuseStep 8605511 = 12908267) B12908267
theorem B5737007 : Blo 2265435 5737007 := bstep (se 1 (by rfl) ⟨4302755, by rfl⟩ : syracuseStep 5737007 = 8605511) B8605511
theorem B3824671 : Blo 2265435 3824671 := bstep (se 1 (by rfl) ⟨2868503, by rfl⟩ : syracuseStep 3824671 = 5737007) B5737007
theorem B5099561 : Blo 2265435 5099561 := bstep (se 2 (by rfl) ⟨1912335, by rfl⟩ : syracuseStep 5099561 = 3824671) B3824671
theorem B3399707 : Blo 2265435 3399707 := bstep (se 1 (by rfl) ⟨2549780, by rfl⟩ : syracuseStep 3399707 = 5099561) B5099561
theorem B2266471 : Blo 2265435 2266471 := bstep (se 1 (by rfl) ⟨1699853, by rfl⟩ : syracuseStep 2266471 = 3399707) B3399707
theorem B2549785 : Blo 2265435 2549785 := bbase (se 2 (by rfl) ⟨956169, by rfl⟩ : syracuseStep 2549785 = 1912339) (by norm_num)
theorem B3399713 : Blo 2265435 3399713 := bstep (se 2 (by rfl) ⟨1274892, by rfl⟩ : syracuseStep 3399713 = 2549785) B2549785
theorem B2266475 : Blo 2265435 2266475 := bstep (se 1 (by rfl) ⟨1699856, by rfl⟩ : syracuseStep 2266475 = 3399713) B3399713
theorem B8605541 : Blo 2265435 8605541 := bbase (se 4 (by rfl) ⟨806769, by rfl⟩ : syracuseStep 8605541 = 1613539) (by norm_num)
theorem B5737027 : Blo 2265435 5737027 := bstep (se 1 (by rfl) ⟨4302770, by rfl⟩ : syracuseStep 5737027 = 8605541) B8605541
theorem B7649369 : Blo 2265435 7649369 := bstep (se 2 (by rfl) ⟨2868513, by rfl⟩ : syracuseStep 7649369 = 5737027) B5737027
theorem B5099579 : Blo 2265435 5099579 := bstep (se 1 (by rfl) ⟨3824684, by rfl⟩ : syracuseStep 5099579 = 7649369) B7649369
theorem B3399719 : Blo 2265435 3399719 := bstep (se 1 (by rfl) ⟨2549789, by rfl⟩ : syracuseStep 3399719 = 5099579) B5099579
theorem B2266479 : Blo 2265435 2266479 := bstep (se 1 (by rfl) ⟨1699859, by rfl⟩ : syracuseStep 2266479 = 3399719) B3399719
theorem B3399725 : Blo 2265435 3399725 := bbase (se 3 (by rfl) ⟨637448, by rfl⟩ : syracuseStep 3399725 = 1274897) (by norm_num)
theorem B2266483 : Blo 2265435 2266483 := bstep (se 1 (by rfl) ⟨1699862, by rfl⟩ : syracuseStep 2266483 = 3399725) B3399725
theorem B5099597 : Blo 2265435 5099597 := bbase (se 3 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 5099597 = 1912349) (by norm_num)
theorem B3399731 : Blo 2265435 3399731 := bstep (se 1 (by rfl) ⟨2549798, by rfl⟩ : syracuseStep 3399731 = 5099597) B5099597
theorem B2266487 : Blo 2265435 2266487 := bstep (se 1 (by rfl) ⟨1699865, by rfl⟩ : syracuseStep 2266487 = 3399731) B3399731
theorem B2868529 : Blo 2265435 2868529 := bbase (se 2 (by rfl) ⟨1075698, by rfl⟩ : syracuseStep 2868529 = 2151397) (by norm_num)
theorem B3824705 : Blo 2265435 3824705 := bstep (se 2 (by rfl) ⟨1434264, by rfl⟩ : syracuseStep 3824705 = 2868529) B2868529
theorem B2549803 : Blo 2265435 2549803 := bstep (se 1 (by rfl) ⟨1912352, by rfl⟩ : syracuseStep 2549803 = 3824705) B3824705
theorem B3399737 : Blo 2265435 3399737 := bstep (se 2 (by rfl) ⟨1274901, by rfl⟩ : syracuseStep 3399737 = 2549803) B2549803
theorem B2266491 : Blo 2265435 2266491 := bstep (se 1 (by rfl) ⟨1699868, by rfl⟩ : syracuseStep 2266491 = 3399737) B3399737
theorem B5445733 : Blo 2265435 5445733 := bbase (se 4 (by rfl) ⟨510537, by rfl⟩ : syracuseStep 5445733 = 1021075) (by norm_num)
theorem B7260977 : Blo 2265435 7260977 := bstep (se 2 (by rfl) ⟨2722866, by rfl⟩ : syracuseStep 7260977 = 5445733) B5445733
theorem B4840651 : Blo 2265435 4840651 := bstep (se 1 (by rfl) ⟨3630488, by rfl⟩ : syracuseStep 4840651 = 7260977) B7260977
theorem B25816805 : Blo 2265435 25816805 := bstep (se 4 (by rfl) ⟨2420325, by rfl⟩ : syracuseStep 25816805 = 4840651) B4840651
theorem B17211203 : Blo 2265435 17211203 := bstep (se 1 (by rfl) ⟨12908402, by rfl⟩ : syracuseStep 17211203 = 25816805) B25816805
theorem B11474135 : Blo 2265435 11474135 := bstep (se 1 (by rfl) ⟨8605601, by rfl⟩ : syracuseStep 11474135 = 17211203) B17211203
theorem B7649423 : Blo 2265435 7649423 := bstep (se 1 (by rfl) ⟨5737067, by rfl⟩ : syracuseStep 7649423 = 11474135) B11474135
theorem B5099615 : Blo 2265435 5099615 := bstep (se 1 (by rfl) ⟨3824711, by rfl⟩ : syracuseStep 5099615 = 7649423) B7649423
theorem B3399743 : Blo 2265435 3399743 := bstep (se 1 (by rfl) ⟨2549807, by rfl⟩ : syracuseStep 3399743 = 5099615) B5099615
theorem B2266495 : Blo 2265435 2266495 := bstep (se 1 (by rfl) ⟨1699871, by rfl⟩ : syracuseStep 2266495 = 3399743) B3399743
theorem B3399749 : Blo 2265435 3399749 := bbase (se 4 (by rfl) ⟨318726, by rfl⟩ : syracuseStep 3399749 = 637453) (by norm_num)
theorem B2266499 : Blo 2265435 2266499 := bstep (se 1 (by rfl) ⟨1699874, by rfl⟩ : syracuseStep 2266499 = 3399749) B3399749
theorem B3824725 : Blo 2265435 3824725 := bbase (se 8 (by rfl) ⟨22410, by rfl⟩ : syracuseStep 3824725 = 44821) (by norm_num)
theorem B5099633 : Blo 2265435 5099633 := bstep (se 2 (by rfl) ⟨1912362, by rfl⟩ : syracuseStep 5099633 = 3824725) B3824725
theorem B3399755 : Blo 2265435 3399755 := bstep (se 1 (by rfl) ⟨2549816, by rfl⟩ : syracuseStep 3399755 = 5099633) B5099633
theorem B2266503 : Blo 2265435 2266503 := bstep (se 1 (by rfl) ⟨1699877, by rfl⟩ : syracuseStep 2266503 = 3399755) B3399755
theorem B2549821 : Blo 2265435 2549821 := bbase (se 3 (by rfl) ⟨478091, by rfl⟩ : syracuseStep 2549821 = 956183) (by norm_num)
theorem B3399761 : Blo 2265435 3399761 := bstep (se 2 (by rfl) ⟨1274910, by rfl⟩ : syracuseStep 3399761 = 2549821) B2549821
theorem B2266507 : Blo 2265435 2266507 := bstep (se 1 (by rfl) ⟨1699880, by rfl⟩ : syracuseStep 2266507 = 3399761) B3399761
theorem B7649477 : Blo 2265435 7649477 := bbase (se 4 (by rfl) ⟨717138, by rfl⟩ : syracuseStep 7649477 = 1434277) (by norm_num)
theorem B5099651 : Blo 2265435 5099651 := bstep (se 1 (by rfl) ⟨3824738, by rfl⟩ : syracuseStep 5099651 = 7649477) B7649477
theorem B3399767 : Blo 2265435 3399767 := bstep (se 1 (by rfl) ⟨2549825, by rfl⟩ : syracuseStep 3399767 = 5099651) B5099651
theorem B2266511 : Blo 2265435 2266511 := bstep (se 1 (by rfl) ⟨1699883, by rfl⟩ : syracuseStep 2266511 = 3399767) B3399767
theorem B3399773 : Blo 2265435 3399773 := bbase (se 3 (by rfl) ⟨637457, by rfl⟩ : syracuseStep 3399773 = 1274915) (by norm_num)
theorem B2266515 : Blo 2265435 2266515 := bstep (se 1 (by rfl) ⟨1699886, by rfl⟩ : syracuseStep 2266515 = 3399773) B3399773
theorem B5099669 : Blo 2265435 5099669 := bbase (se 6 (by rfl) ⟨119523, by rfl⟩ : syracuseStep 5099669 = 239047) (by norm_num)
theorem B3399779 : Blo 2265435 3399779 := bstep (se 1 (by rfl) ⟨2549834, by rfl⟩ : syracuseStep 3399779 = 5099669) B5099669
theorem B2266519 : Blo 2265435 2266519 := bstep (se 1 (by rfl) ⟨1699889, by rfl⟩ : syracuseStep 2266519 = 3399779) B3399779
theorem B3227141 : Blo 2265435 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B8605709 : Blo 2265435 8605709 := bstep (se 3 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 8605709 = 3227141) B3227141
theorem B5737139 : Blo 2265435 5737139 := bstep (se 1 (by rfl) ⟨4302854, by rfl⟩ : syracuseStep 5737139 = 8605709) B8605709
theorem B3824759 : Blo 2265435 3824759 := bstep (se 1 (by rfl) ⟨2868569, by rfl⟩ : syracuseStep 3824759 = 5737139) B5737139
theorem B2549839 : Blo 2265435 2549839 := bstep (se 1 (by rfl) ⟨1912379, by rfl⟩ : syracuseStep 2549839 = 3824759) B3824759
theorem B3399785 : Blo 2265435 3399785 := bstep (se 2 (by rfl) ⟨1274919, by rfl⟩ : syracuseStep 3399785 = 2549839) B2549839
theorem B2266523 : Blo 2265435 2266523 := bstep (se 1 (by rfl) ⟨1699892, by rfl⟩ : syracuseStep 2266523 = 3399785) B3399785
theorem B3876949 : Blo 2265435 3876949 := bbase (se 8 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 3876949 = 45433) (by norm_num)
theorem B5169265 : Blo 2265435 5169265 := bstep (se 2 (by rfl) ⟨1938474, by rfl⟩ : syracuseStep 5169265 = 3876949) B3876949
theorem B27569413 : Blo 2265435 27569413 := bstep (se 4 (by rfl) ⟨2584632, by rfl⟩ : syracuseStep 27569413 = 5169265) B5169265
theorem B36759217 : Blo 2265435 36759217 := bstep (se 2 (by rfl) ⟨13784706, by rfl⟩ : syracuseStep 36759217 = 27569413) B27569413
theorem B49012289 : Blo 2265435 49012289 := bstep (se 2 (by rfl) ⟨18379608, by rfl⟩ : syracuseStep 49012289 = 36759217) B36759217
theorem B32674859 : Blo 2265435 32674859 := bstep (se 1 (by rfl) ⟨24506144, by rfl⟩ : syracuseStep 32674859 = 49012289) B49012289
theorem B21783239 : Blo 2265435 21783239 := bstep (se 1 (by rfl) ⟨16337429, by rfl⟩ : syracuseStep 21783239 = 32674859) B32674859
theorem B14522159 : Blo 2265435 14522159 := bstep (se 1 (by rfl) ⟨10891619, by rfl⟩ : syracuseStep 14522159 = 21783239) B21783239
theorem B9681439 : Blo 2265435 9681439 := bstep (se 1 (by rfl) ⟨7261079, by rfl⟩ : syracuseStep 9681439 = 14522159) B14522159
theorem B12908585 : Blo 2265435 12908585 := bstep (se 2 (by rfl) ⟨4840719, by rfl⟩ : syracuseStep 12908585 = 9681439) B9681439
theorem B8605723 : Blo 2265435 8605723 := bstep (se 1 (by rfl) ⟨6454292, by rfl⟩ : syracuseStep 8605723 = 12908585) B12908585
theorem B11474297 : Blo 2265435 11474297 := bstep (se 2 (by rfl) ⟨4302861, by rfl⟩ : syracuseStep 11474297 = 8605723) B8605723
theorem B7649531 : Blo 2265435 7649531 := bstep (se 1 (by rfl) ⟨5737148, by rfl⟩ : syracuseStep 7649531 = 11474297) B11474297
theorem B5099687 : Blo 2265435 5099687 := bstep (se 1 (by rfl) ⟨3824765, by rfl⟩ : syracuseStep 5099687 = 7649531) B7649531
theorem B3399791 : Blo 2265435 3399791 := bstep (se 1 (by rfl) ⟨2549843, by rfl⟩ : syracuseStep 3399791 = 5099687) B5099687
theorem B2266527 : Blo 2265435 2266527 := bstep (se 1 (by rfl) ⟨1699895, by rfl⟩ : syracuseStep 2266527 = 3399791) B3399791
theorem B3399797 : Blo 2265435 3399797 := bbase (se 5 (by rfl) ⟨159365, by rfl⟩ : syracuseStep 3399797 = 318731) (by norm_num)
theorem B2266531 : Blo 2265435 2266531 := bstep (se 1 (by rfl) ⟨1699898, by rfl⟩ : syracuseStep 2266531 = 3399797) B3399797
theorem B4302877 : Blo 2265435 4302877 := bbase (se 3 (by rfl) ⟨806789, by rfl⟩ : syracuseStep 4302877 = 1613579) (by norm_num)
theorem B5737169 : Blo 2265435 5737169 := bstep (se 2 (by rfl) ⟨2151438, by rfl⟩ : syracuseStep 5737169 = 4302877) B4302877
theorem B3824779 : Blo 2265435 3824779 := bstep (se 1 (by rfl) ⟨2868584, by rfl⟩ : syracuseStep 3824779 = 5737169) B5737169
theorem B5099705 : Blo 2265435 5099705 := bstep (se 2 (by rfl) ⟨1912389, by rfl⟩ : syracuseStep 5099705 = 3824779) B3824779
theorem B3399803 : Blo 2265435 3399803 := bstep (se 1 (by rfl) ⟨2549852, by rfl⟩ : syracuseStep 3399803 = 5099705) B5099705
theorem B2266535 : Blo 2265435 2266535 := bstep (se 1 (by rfl) ⟨1699901, by rfl⟩ : syracuseStep 2266535 = 3399803) B3399803
theorem B2549857 : Blo 2265435 2549857 := bbase (se 2 (by rfl) ⟨956196, by rfl⟩ : syracuseStep 2549857 = 1912393) (by norm_num)
theorem B3399809 : Blo 2265435 3399809 := bstep (se 2 (by rfl) ⟨1274928, by rfl⟩ : syracuseStep 3399809 = 2549857) B2549857
theorem B2266539 : Blo 2265435 2266539 := bstep (se 1 (by rfl) ⟨1699904, by rfl⟩ : syracuseStep 2266539 = 3399809) B3399809
theorem B5737189 : Blo 2265435 5737189 := bbase (se 4 (by rfl) ⟨537861, by rfl⟩ : syracuseStep 5737189 = 1075723) (by norm_num)
theorem B7649585 : Blo 2265435 7649585 := bstep (se 2 (by rfl) ⟨2868594, by rfl⟩ : syracuseStep 7649585 = 5737189) B5737189
theorem B5099723 : Blo 2265435 5099723 := bstep (se 1 (by rfl) ⟨3824792, by rfl⟩ : syracuseStep 5099723 = 7649585) B7649585
theorem B3399815 : Blo 2265435 3399815 := bstep (se 1 (by rfl) ⟨2549861, by rfl⟩ : syracuseStep 3399815 = 5099723) B5099723
theorem B2266543 : Blo 2265435 2266543 := bstep (se 1 (by rfl) ⟨1699907, by rfl⟩ : syracuseStep 2266543 = 3399815) B3399815
theorem B3399821 : Blo 2265435 3399821 := bbase (se 3 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 3399821 = 1274933) (by norm_num)
theorem B2266547 : Blo 2265435 2266547 := bstep (se 1 (by rfl) ⟨1699910, by rfl⟩ : syracuseStep 2266547 = 3399821) B3399821
theorem B5099741 : Blo 2265435 5099741 := bbase (se 3 (by rfl) ⟨956201, by rfl⟩ : syracuseStep 5099741 = 1912403) (by norm_num)
theorem B3399827 : Blo 2265435 3399827 := bstep (se 1 (by rfl) ⟨2549870, by rfl⟩ : syracuseStep 3399827 = 5099741) B5099741
theorem B2266551 : Blo 2265435 2266551 := bstep (se 1 (by rfl) ⟨1699913, by rfl⟩ : syracuseStep 2266551 = 3399827) B3399827
theorem B3824813 : Blo 2265435 3824813 := bbase (se 3 (by rfl) ⟨717152, by rfl⟩ : syracuseStep 3824813 = 1434305) (by norm_num)
theorem B2549875 : Blo 2265435 2549875 := bstep (se 1 (by rfl) ⟨1912406, by rfl⟩ : syracuseStep 2549875 = 3824813) B3824813
theorem B3399833 : Blo 2265435 3399833 := bstep (se 2 (by rfl) ⟨1274937, by rfl⟩ : syracuseStep 3399833 = 2549875) B2549875
theorem B2266555 : Blo 2265435 2266555 := bstep (se 1 (by rfl) ⟨1699916, by rfl⟩ : syracuseStep 2266555 = 3399833) B3399833
theorem B31439189 : Blo 2265435 31439189 := bbase (se 10 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 31439189 = 92107) (by norm_num)
theorem B83837837 : Blo 2265435 83837837 := bstep (se 3 (by rfl) ⟨15719594, by rfl⟩ : syracuseStep 83837837 = 31439189) B31439189
theorem B55891891 : Blo 2265435 55891891 := bstep (se 1 (by rfl) ⟨41918918, by rfl⟩ : syracuseStep 55891891 = 83837837) B83837837
theorem B74522521 : Blo 2265435 74522521 := bstep (se 2 (by rfl) ⟨27945945, by rfl⟩ : syracuseStep 74522521 = 55891891) B55891891
theorem B99363361 : Blo 2265435 99363361 := bstep (se 2 (by rfl) ⟨37261260, by rfl⟩ : syracuseStep 99363361 = 74522521) B74522521
theorem B132484481 : Blo 2265435 132484481 := bstep (se 2 (by rfl) ⟨49681680, by rfl⟩ : syracuseStep 132484481 = 99363361) B99363361
theorem B88322987 : Blo 2265435 88322987 := bstep (se 1 (by rfl) ⟨66242240, by rfl⟩ : syracuseStep 88322987 = 132484481) B132484481
theorem B58881991 : Blo 2265435 58881991 := bstep (se 1 (by rfl) ⟨44161493, by rfl⟩ : syracuseStep 58881991 = 88322987) B88322987
theorem B78509321 : Blo 2265435 78509321 := bstep (se 2 (by rfl) ⟨29440995, by rfl⟩ : syracuseStep 78509321 = 58881991) B58881991
theorem B52339547 : Blo 2265435 52339547 := bstep (se 1 (by rfl) ⟨39254660, by rfl⟩ : syracuseStep 52339547 = 78509321) B78509321
theorem B34893031 : Blo 2265435 34893031 := bstep (se 1 (by rfl) ⟨26169773, by rfl⟩ : syracuseStep 34893031 = 52339547) B52339547
theorem B46524041 : Blo 2265435 46524041 := bstep (se 2 (by rfl) ⟨17446515, by rfl⟩ : syracuseStep 46524041 = 34893031) B34893031
theorem B31016027 : Blo 2265435 31016027 := bstep (se 1 (by rfl) ⟨23262020, by rfl⟩ : syracuseStep 31016027 = 46524041) B46524041
theorem B20677351 : Blo 2265435 20677351 := bstep (se 1 (by rfl) ⟨15508013, by rfl⟩ : syracuseStep 20677351 = 31016027) B31016027
theorem B27569801 : Blo 2265435 27569801 := bstep (se 2 (by rfl) ⟨10338675, by rfl⟩ : syracuseStep 27569801 = 20677351) B20677351
theorem B18379867 : Blo 2265435 18379867 := bstep (se 1 (by rfl) ⟨13784900, by rfl⟩ : syracuseStep 18379867 = 27569801) B27569801
theorem B24506489 : Blo 2265435 24506489 := bstep (se 2 (by rfl) ⟨9189933, by rfl⟩ : syracuseStep 24506489 = 18379867) B18379867
theorem B65350637 : Blo 2265435 65350637 := bstep (se 3 (by rfl) ⟨12253244, by rfl⟩ : syracuseStep 65350637 = 24506489) B24506489
theorem B43567091 : Blo 2265435 43567091 := bstep (se 1 (by rfl) ⟨32675318, by rfl⟩ : syracuseStep 43567091 = 65350637) B65350637
theorem B29044727 : Blo 2265435 29044727 := bstep (se 1 (by rfl) ⟨21783545, by rfl⟩ : syracuseStep 29044727 = 43567091) B43567091
theorem B19363151 : Blo 2265435 19363151 := bstep (se 1 (by rfl) ⟨14522363, by rfl⟩ : syracuseStep 19363151 = 29044727) B29044727
theorem B12908767 : Blo 2265435 12908767 := bstep (se 1 (by rfl) ⟨9681575, by rfl⟩ : syracuseStep 12908767 = 19363151) B19363151
theorem B17211689 : Blo 2265435 17211689 := bstep (se 2 (by rfl) ⟨6454383, by rfl⟩ : syracuseStep 17211689 = 12908767) B12908767
theorem B11474459 : Blo 2265435 11474459 := bstep (se 1 (by rfl) ⟨8605844, by rfl⟩ : syracuseStep 11474459 = 17211689) B17211689
theorem B7649639 : Blo 2265435 7649639 := bstep (se 1 (by rfl) ⟨5737229, by rfl⟩ : syracuseStep 7649639 = 11474459) B11474459
theorem B5099759 : Blo 2265435 5099759 := bstep (se 1 (by rfl) ⟨3824819, by rfl⟩ : syracuseStep 5099759 = 7649639) B7649639
theorem B3399839 : Blo 2265435 3399839 := bstep (se 1 (by rfl) ⟨2549879, by rfl⟩ : syracuseStep 3399839 = 5099759) B5099759
theorem B2266559 : Blo 2265435 2266559 := bstep (se 1 (by rfl) ⟨1699919, by rfl⟩ : syracuseStep 2266559 = 3399839) B3399839
theorem B3399845 : Blo 2265435 3399845 := bbase (se 4 (by rfl) ⟨318735, by rfl⟩ : syracuseStep 3399845 = 637471) (by norm_num)
theorem B2266563 : Blo 2265435 2266563 := bstep (se 1 (by rfl) ⟨1699922, by rfl⟩ : syracuseStep 2266563 = 3399845) B3399845
theorem B2868625 : Blo 2265435 2868625 := bbase (se 2 (by rfl) ⟨1075734, by rfl⟩ : syracuseStep 2868625 = 2151469) (by norm_num)
theorem B3824833 : Blo 2265435 3824833 := bstep (se 2 (by rfl) ⟨1434312, by rfl⟩ : syracuseStep 3824833 = 2868625) B2868625
theorem B5099777 : Blo 2265435 5099777 := bstep (se 2 (by rfl) ⟨1912416, by rfl⟩ : syracuseStep 5099777 = 3824833) B3824833
theorem B3399851 : Blo 2265435 3399851 := bstep (se 1 (by rfl) ⟨2549888, by rfl⟩ : syracuseStep 3399851 = 5099777) B5099777
theorem B2266567 : Blo 2265435 2266567 := bstep (se 1 (by rfl) ⟨1699925, by rfl⟩ : syracuseStep 2266567 = 3399851) B3399851
theorem B2549893 : Blo 2265435 2549893 := bbase (se 4 (by rfl) ⟨239052, by rfl⟩ : syracuseStep 2549893 = 478105) (by norm_num)
theorem B3399857 : Blo 2265435 3399857 := bstep (se 2 (by rfl) ⟨1274946, by rfl⟩ : syracuseStep 3399857 = 2549893) B2549893
theorem B2266571 : Blo 2265435 2266571 := bstep (se 1 (by rfl) ⟨1699928, by rfl⟩ : syracuseStep 2266571 = 3399857) B3399857
theorem B4084445 : Blo 2265435 4084445 := bbase (se 3 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 4084445 = 1531667) (by norm_num)
theorem B10891853 : Blo 2265435 10891853 := bstep (se 3 (by rfl) ⟨2042222, by rfl⟩ : syracuseStep 10891853 = 4084445) B4084445
theorem B7261235 : Blo 2265435 7261235 := bstep (se 1 (by rfl) ⟨5445926, by rfl⟩ : syracuseStep 7261235 = 10891853) B10891853
theorem B4840823 : Blo 2265435 4840823 := bstep (se 1 (by rfl) ⟨3630617, by rfl⟩ : syracuseStep 4840823 = 7261235) B7261235
theorem B3227215 : Blo 2265435 3227215 := bstep (se 1 (by rfl) ⟨2420411, by rfl⟩ : syracuseStep 3227215 = 4840823) B4840823
theorem B4302953 : Blo 2265435 4302953 := bstep (se 2 (by rfl) ⟨1613607, by rfl⟩ : syracuseStep 4302953 = 3227215) B3227215
theorem B2868635 : Blo 2265435 2868635 := bstep (se 1 (by rfl) ⟨2151476, by rfl⟩ : syracuseStep 2868635 = 4302953) B4302953
theorem B7649693 : Blo 2265435 7649693 := bstep (se 3 (by rfl) ⟨1434317, by rfl⟩ : syracuseStep 7649693 = 2868635) B2868635
theorem B5099795 : Blo 2265435 5099795 := bstep (se 1 (by rfl) ⟨3824846, by rfl⟩ : syracuseStep 5099795 = 7649693) B7649693
theorem B3399863 : Blo 2265435 3399863 := bstep (se 1 (by rfl) ⟨2549897, by rfl⟩ : syracuseStep 3399863 = 5099795) B5099795
theorem B2266575 : Blo 2265435 2266575 := bstep (se 1 (by rfl) ⟨1699931, by rfl⟩ : syracuseStep 2266575 = 3399863) B3399863
theorem B3399869 : Blo 2265435 3399869 := bbase (se 3 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 3399869 = 1274951) (by norm_num)
theorem B2266579 : Blo 2265435 2266579 := bstep (se 1 (by rfl) ⟨1699934, by rfl⟩ : syracuseStep 2266579 = 3399869) B3399869
theorem B5099813 : Blo 2265435 5099813 := bbase (se 4 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 5099813 = 956215) (by norm_num)
theorem B3399875 : Blo 2265435 3399875 := bstep (se 1 (by rfl) ⟨2549906, by rfl⟩ : syracuseStep 3399875 = 5099813) B5099813
theorem B2266583 : Blo 2265435 2266583 := bstep (se 1 (by rfl) ⟨1699937, by rfl⟩ : syracuseStep 2266583 = 3399875) B3399875
theorem B5737301 : Blo 2265435 5737301 := bbase (se 9 (by rfl) ⟨16808, by rfl⟩ : syracuseStep 5737301 = 33617) (by norm_num)
theorem B3824867 : Blo 2265435 3824867 := bstep (se 1 (by rfl) ⟨2868650, by rfl⟩ : syracuseStep 3824867 = 5737301) B5737301
theorem B2549911 : Blo 2265435 2549911 := bstep (se 1 (by rfl) ⟨1912433, by rfl⟩ : syracuseStep 2549911 = 3824867) B3824867
theorem B3399881 : Blo 2265435 3399881 := bstep (se 2 (by rfl) ⟨1274955, by rfl⟩ : syracuseStep 3399881 = 2549911) B2549911
theorem B2266587 : Blo 2265435 2266587 := bstep (se 1 (by rfl) ⟨1699940, by rfl⟩ : syracuseStep 2266587 = 3399881) B3399881
theorem B7261285 : Blo 2265435 7261285 := bbase (se 4 (by rfl) ⟨680745, by rfl⟩ : syracuseStep 7261285 = 1361491) (by norm_num)
theorem B9681713 : Blo 2265435 9681713 := bstep (se 2 (by rfl) ⟨3630642, by rfl⟩ : syracuseStep 9681713 = 7261285) B7261285
theorem B6454475 : Blo 2265435 6454475 := bstep (se 1 (by rfl) ⟨4840856, by rfl⟩ : syracuseStep 6454475 = 9681713) B9681713
theorem B4302983 : Blo 2265435 4302983 := bstep (se 1 (by rfl) ⟨3227237, by rfl⟩ : syracuseStep 4302983 = 6454475) B6454475
theorem B11474621 : Blo 2265435 11474621 := bstep (se 3 (by rfl) ⟨2151491, by rfl⟩ : syracuseStep 11474621 = 4302983) B4302983
theorem B7649747 : Blo 2265435 7649747 := bstep (se 1 (by rfl) ⟨5737310, by rfl⟩ : syracuseStep 7649747 = 11474621) B11474621
theorem B5099831 : Blo 2265435 5099831 := bstep (se 1 (by rfl) ⟨3824873, by rfl⟩ : syracuseStep 5099831 = 7649747) B7649747
theorem B3399887 : Blo 2265435 3399887 := bstep (se 1 (by rfl) ⟨2549915, by rfl⟩ : syracuseStep 3399887 = 5099831) B5099831
theorem B2266591 : Blo 2265435 2266591 := bstep (se 1 (by rfl) ⟨1699943, by rfl⟩ : syracuseStep 2266591 = 3399887) B3399887
theorem B3399893 : Blo 2265435 3399893 := bbase (se 7 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 3399893 = 79685) (by norm_num)
theorem B2266595 : Blo 2265435 2266595 := bstep (se 1 (by rfl) ⟨1699946, by rfl⟩ : syracuseStep 2266595 = 3399893) B3399893
theorem B2420437 : Blo 2265435 2420437 := bbase (se 7 (by rfl) ⟨28364, by rfl⟩ : syracuseStep 2420437 = 56729) (by norm_num)
theorem B3227249 : Blo 2265435 3227249 := bstep (se 2 (by rfl) ⟨1210218, by rfl⟩ : syracuseStep 3227249 = 2420437) B2420437
theorem B8605997 : Blo 2265435 8605997 := bstep (se 3 (by rfl) ⟨1613624, by rfl⟩ : syracuseStep 8605997 = 3227249) B3227249
theorem B5737331 : Blo 2265435 5737331 := bstep (se 1 (by rfl) ⟨4302998, by rfl⟩ : syracuseStep 5737331 = 8605997) B8605997
theorem B3824887 : Blo 2265435 3824887 := bstep (se 1 (by rfl) ⟨2868665, by rfl⟩ : syracuseStep 3824887 = 5737331) B5737331
theorem B5099849 : Blo 2265435 5099849 := bstep (se 2 (by rfl) ⟨1912443, by rfl⟩ : syracuseStep 5099849 = 3824887) B3824887
theorem B3399899 : Blo 2265435 3399899 := bstep (se 1 (by rfl) ⟨2549924, by rfl⟩ : syracuseStep 3399899 = 5099849) B5099849
theorem B2266599 : Blo 2265435 2266599 := bstep (se 1 (by rfl) ⟨1699949, by rfl⟩ : syracuseStep 2266599 = 3399899) B3399899
theorem B2549929 : Blo 2265435 2549929 := bbase (se 2 (by rfl) ⟨956223, by rfl⟩ : syracuseStep 2549929 = 1912447) (by norm_num)
theorem B3399905 : Blo 2265435 3399905 := bstep (se 2 (by rfl) ⟨1274964, by rfl⟩ : syracuseStep 3399905 = 2549929) B2549929
theorem B2266603 : Blo 2265435 2266603 := bstep (se 1 (by rfl) ⟨1699952, by rfl⟩ : syracuseStep 2266603 = 3399905) B3399905
theorem B9681781 : Blo 2265435 9681781 := bbase (se 5 (by rfl) ⟨453833, by rfl⟩ : syracuseStep 9681781 = 907667) (by norm_num)
theorem B12909041 : Blo 2265435 12909041 := bstep (se 2 (by rfl) ⟨4840890, by rfl⟩ : syracuseStep 12909041 = 9681781) B9681781
theorem B8606027 : Blo 2265435 8606027 := bstep (se 1 (by rfl) ⟨6454520, by rfl⟩ : syracuseStep 8606027 = 12909041) B12909041
theorem B5737351 : Blo 2265435 5737351 := bstep (se 1 (by rfl) ⟨4303013, by rfl⟩ : syracuseStep 5737351 = 8606027) B8606027
theorem B7649801 : Blo 2265435 7649801 := bstep (se 2 (by rfl) ⟨2868675, by rfl⟩ : syracuseStep 7649801 = 5737351) B5737351
theorem B5099867 : Blo 2265435 5099867 := bstep (se 1 (by rfl) ⟨3824900, by rfl⟩ : syracuseStep 5099867 = 7649801) B7649801
theorem B3399911 : Blo 2265435 3399911 := bstep (se 1 (by rfl) ⟨2549933, by rfl⟩ : syracuseStep 3399911 = 5099867) B5099867
theorem B2266607 : Blo 2265435 2266607 := bstep (se 1 (by rfl) ⟨1699955, by rfl⟩ : syracuseStep 2266607 = 3399911) B3399911
theorem B3399917 : Blo 2265435 3399917 := bbase (se 3 (by rfl) ⟨637484, by rfl⟩ : syracuseStep 3399917 = 1274969) (by norm_num)
theorem B2266611 : Blo 2265435 2266611 := bstep (se 1 (by rfl) ⟨1699958, by rfl⟩ : syracuseStep 2266611 = 3399917) B3399917
theorem B5099885 : Blo 2265435 5099885 := bbase (se 3 (by rfl) ⟨956228, by rfl⟩ : syracuseStep 5099885 = 1912457) (by norm_num)
theorem B3399923 : Blo 2265435 3399923 := bstep (se 1 (by rfl) ⟨2549942, by rfl⟩ : syracuseStep 3399923 = 5099885) B5099885
theorem B2266615 : Blo 2265435 2266615 := bstep (se 1 (by rfl) ⟨1699961, by rfl⟩ : syracuseStep 2266615 = 3399923) B3399923
theorem B4303037 : Blo 2265435 4303037 := bbase (se 3 (by rfl) ⟨806819, by rfl⟩ : syracuseStep 4303037 = 1613639) (by norm_num)
theorem B2868691 : Blo 2265435 2868691 := bstep (se 1 (by rfl) ⟨2151518, by rfl⟩ : syracuseStep 2868691 = 4303037) B4303037
theorem B3824921 : Blo 2265435 3824921 := bstep (se 2 (by rfl) ⟨1434345, by rfl⟩ : syracuseStep 3824921 = 2868691) B2868691
theorem B2549947 : Blo 2265435 2549947 := bstep (se 1 (by rfl) ⟨1912460, by rfl⟩ : syracuseStep 2549947 = 3824921) B3824921
theorem B3399929 : Blo 2265435 3399929 := bstep (se 2 (by rfl) ⟨1274973, by rfl⟩ : syracuseStep 3399929 = 2549947) B2549947
theorem B2266619 : Blo 2265435 2266619 := bstep (se 1 (by rfl) ⟨1699964, by rfl⟩ : syracuseStep 2266619 = 3399929) B3399929
theorem B58091093 : Blo 2265435 58091093 := bbase (se 8 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 58091093 = 680755) (by norm_num)
theorem B38727395 : Blo 2265435 38727395 := bstep (se 1 (by rfl) ⟨29045546, by rfl⟩ : syracuseStep 38727395 = 58091093) B58091093
theorem B25818263 : Blo 2265435 25818263 := bstep (se 1 (by rfl) ⟨19363697, by rfl⟩ : syracuseStep 25818263 = 38727395) B38727395
theorem B17212175 : Blo 2265435 17212175 := bstep (se 1 (by rfl) ⟨12909131, by rfl⟩ : syracuseStep 17212175 = 25818263) B25818263
theorem B11474783 : Blo 2265435 11474783 := bstep (se 1 (by rfl) ⟨8606087, by rfl⟩ : syracuseStep 11474783 = 17212175) B17212175
theorem B7649855 : Blo 2265435 7649855 := bstep (se 1 (by rfl) ⟨5737391, by rfl⟩ : syracuseStep 7649855 = 11474783) B11474783
theorem B5099903 : Blo 2265435 5099903 := bstep (se 1 (by rfl) ⟨3824927, by rfl⟩ : syracuseStep 5099903 = 7649855) B7649855
theorem B3399935 : Blo 2265435 3399935 := bstep (se 1 (by rfl) ⟨2549951, by rfl⟩ : syracuseStep 3399935 = 5099903) B5099903
theorem B2266623 : Blo 2265435 2266623 := bstep (se 1 (by rfl) ⟨1699967, by rfl⟩ : syracuseStep 2266623 = 3399935) B3399935
theorem B3399941 : Blo 2265435 3399941 := bbase (se 4 (by rfl) ⟨318744, by rfl⟩ : syracuseStep 3399941 = 637489) (by norm_num)
theorem B2266627 : Blo 2265435 2266627 := bstep (se 1 (by rfl) ⟨1699970, by rfl⟩ : syracuseStep 2266627 = 3399941) B3399941
theorem B3824941 : Blo 2265435 3824941 := bbase (se 3 (by rfl) ⟨717176, by rfl⟩ : syracuseStep 3824941 = 1434353) (by norm_num)
theorem B5099921 : Blo 2265435 5099921 := bstep (se 2 (by rfl) ⟨1912470, by rfl⟩ : syracuseStep 5099921 = 3824941) B3824941
theorem B3399947 : Blo 2265435 3399947 := bstep (se 1 (by rfl) ⟨2549960, by rfl⟩ : syracuseStep 3399947 = 5099921) B5099921
theorem B2266631 : Blo 2265435 2266631 := bstep (se 1 (by rfl) ⟨1699973, by rfl⟩ : syracuseStep 2266631 = 3399947) B3399947
theorem B2549965 : Blo 2265435 2549965 := bbase (se 3 (by rfl) ⟨478118, by rfl⟩ : syracuseStep 2549965 = 956237) (by norm_num)
theorem B3399953 : Blo 2265435 3399953 := bstep (se 2 (by rfl) ⟨1274982, by rfl⟩ : syracuseStep 3399953 = 2549965) B2549965
theorem B2266635 : Blo 2265435 2266635 := bstep (se 1 (by rfl) ⟨1699976, by rfl⟩ : syracuseStep 2266635 = 3399953) B3399953
theorem B7649909 : Blo 2265435 7649909 := bbase (se 5 (by rfl) ⟨358589, by rfl⟩ : syracuseStep 7649909 = 717179) (by norm_num)
theorem B5099939 : Blo 2265435 5099939 := bstep (se 1 (by rfl) ⟨3824954, by rfl⟩ : syracuseStep 5099939 = 7649909) B7649909
theorem B3399959 : Blo 2265435 3399959 := bstep (se 1 (by rfl) ⟨2549969, by rfl⟩ : syracuseStep 3399959 = 5099939) B5099939
theorem B2266639 : Blo 2265435 2266639 := bstep (se 1 (by rfl) ⟨1699979, by rfl⟩ : syracuseStep 2266639 = 3399959) B3399959
theorem B3399965 : Blo 2265435 3399965 := bbase (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) (by norm_num)
theorem B2266643 : Blo 2265435 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B5099957 : Blo 2265435 5099957 := bbase (se 5 (by rfl) ⟨239060, by rfl⟩ : syracuseStep 5099957 = 478121) (by norm_num)
theorem B3399971 : Blo 2265435 3399971 := bstep (se 1 (by rfl) ⟨2549978, by rfl⟩ : syracuseStep 3399971 = 5099957) B5099957
theorem B2266647 : Blo 2265435 2266647 := bstep (se 1 (by rfl) ⟨1699985, by rfl⟩ : syracuseStep 2266647 = 3399971) B3399971
theorem B5446109 : Blo 2265435 5446109 := bbase (se 3 (by rfl) ⟨1021145, by rfl⟩ : syracuseStep 5446109 = 2042291) (by norm_num)
theorem B3630739 : Blo 2265435 3630739 := bstep (se 1 (by rfl) ⟨2723054, by rfl⟩ : syracuseStep 3630739 = 5446109) B5446109
theorem B4840985 : Blo 2265435 4840985 := bstep (se 2 (by rfl) ⟨1815369, by rfl⟩ : syracuseStep 4840985 = 3630739) B3630739
theorem B12909293 : Blo 2265435 12909293 := bstep (se 3 (by rfl) ⟨2420492, by rfl⟩ : syracuseStep 12909293 = 4840985) B4840985
theorem B8606195 : Blo 2265435 8606195 := bstep (se 1 (by rfl) ⟨6454646, by rfl⟩ : syracuseStep 8606195 = 12909293) B12909293
theorem B5737463 : Blo 2265435 5737463 := bstep (se 1 (by rfl) ⟨4303097, by rfl⟩ : syracuseStep 5737463 = 8606195) B8606195
theorem B3824975 : Blo 2265435 3824975 := bstep (se 1 (by rfl) ⟨2868731, by rfl⟩ : syracuseStep 3824975 = 5737463) B5737463
theorem B2549983 : Blo 2265435 2549983 := bstep (se 1 (by rfl) ⟨1912487, by rfl⟩ : syracuseStep 2549983 = 3824975) B3824975
theorem B3399977 : Blo 2265435 3399977 := bstep (se 2 (by rfl) ⟨1274991, by rfl⟩ : syracuseStep 3399977 = 2549983) B2549983
theorem B2266651 : Blo 2265435 2266651 := bstep (se 1 (by rfl) ⟨1699988, by rfl⟩ : syracuseStep 2266651 = 3399977) B3399977
theorem B4084589 : Blo 2265435 4084589 := bbase (se 3 (by rfl) ⟨765860, by rfl⟩ : syracuseStep 4084589 = 1531721) (by norm_num)
theorem B2723059 : Blo 2265435 2723059 := bstep (se 1 (by rfl) ⟨2042294, by rfl⟩ : syracuseStep 2723059 = 4084589) B4084589
theorem B3630745 : Blo 2265435 3630745 := bstep (se 2 (by rfl) ⟨1361529, by rfl⟩ : syracuseStep 3630745 = 2723059) B2723059
theorem B4840993 : Blo 2265435 4840993 := bstep (se 2 (by rfl) ⟨1815372, by rfl⟩ : syracuseStep 4840993 = 3630745) B3630745
theorem B6454657 : Blo 2265435 6454657 := bstep (se 2 (by rfl) ⟨2420496, by rfl⟩ : syracuseStep 6454657 = 4840993) B4840993
theorem B8606209 : Blo 2265435 8606209 := bstep (se 2 (by rfl) ⟨3227328, by rfl⟩ : syracuseStep 8606209 = 6454657) B6454657
theorem B11474945 : Blo 2265435 11474945 := bstep (se 2 (by rfl) ⟨4303104, by rfl⟩ : syracuseStep 11474945 = 8606209) B8606209
theorem B7649963 : Blo 2265435 7649963 := bstep (se 1 (by rfl) ⟨5737472, by rfl⟩ : syracuseStep 7649963 = 11474945) B11474945
theorem B5099975 : Blo 2265435 5099975 := bstep (se 1 (by rfl) ⟨3824981, by rfl⟩ : syracuseStep 5099975 = 7649963) B7649963
theorem B3399983 : Blo 2265435 3399983 := bstep (se 1 (by rfl) ⟨2549987, by rfl⟩ : syracuseStep 3399983 = 5099975) B5099975
theorem B2266655 : Blo 2265435 2266655 := bstep (se 1 (by rfl) ⟨1699991, by rfl⟩ : syracuseStep 2266655 = 3399983) B3399983
theorem B3399989 : Blo 2265435 3399989 := bbase (se 5 (by rfl) ⟨159374, by rfl⟩ : syracuseStep 3399989 = 318749) (by norm_num)
theorem B2266659 : Blo 2265435 2266659 := bstep (se 1 (by rfl) ⟨1699994, by rfl⟩ : syracuseStep 2266659 = 3399989) B3399989
theorem B5737493 : Blo 2265435 5737493 := bbase (se 6 (by rfl) ⟨134472, by rfl⟩ : syracuseStep 5737493 = 268945) (by norm_num)
theorem B3824995 : Blo 2265435 3824995 := bstep (se 1 (by rfl) ⟨2868746, by rfl⟩ : syracuseStep 3824995 = 5737493) B5737493
theorem B5099993 : Blo 2265435 5099993 := bstep (se 2 (by rfl) ⟨1912497, by rfl⟩ : syracuseStep 5099993 = 3824995) B3824995
theorem B3399995 : Blo 2265435 3399995 := bstep (se 1 (by rfl) ⟨2549996, by rfl⟩ : syracuseStep 3399995 = 5099993) B5099993
theorem B2266663 : Blo 2265435 2266663 := bstep (se 1 (by rfl) ⟨1699997, by rfl⟩ : syracuseStep 2266663 = 3399995) B3399995
theorem B2550001 : Blo 2265435 2550001 := bbase (se 2 (by rfl) ⟨956250, by rfl⟩ : syracuseStep 2550001 = 1912501) (by norm_num)
theorem B3400001 : Blo 2265435 3400001 := bstep (se 2 (by rfl) ⟨1275000, by rfl⟩ : syracuseStep 3400001 = 2550001) B2550001
theorem B2266667 : Blo 2265435 2266667 := bstep (se 1 (by rfl) ⟨1700000, by rfl⟩ : syracuseStep 2266667 = 3400001) B3400001
theorem B3680309 : Blo 2265435 3680309 := bbase (se 5 (by rfl) ⟨172514, by rfl⟩ : syracuseStep 3680309 = 345029) (by norm_num)
theorem B2453539 : Blo 2265435 2453539 := bstep (se 1 (by rfl) ⟨1840154, by rfl⟩ : syracuseStep 2453539 = 3680309) B3680309
theorem B3271385 : Blo 2265435 3271385 := bstep (se 2 (by rfl) ⟨1226769, by rfl⟩ : syracuseStep 3271385 = 2453539) B2453539
theorem B8723693 : Blo 2265435 8723693 := bstep (se 3 (by rfl) ⟨1635692, by rfl⟩ : syracuseStep 8723693 = 3271385) B3271385
theorem B5815795 : Blo 2265435 5815795 := bstep (se 1 (by rfl) ⟨4361846, by rfl⟩ : syracuseStep 5815795 = 8723693) B8723693
theorem B7754393 : Blo 2265435 7754393 := bstep (se 2 (by rfl) ⟨2907897, by rfl⟩ : syracuseStep 7754393 = 5815795) B5815795
theorem B5169595 : Blo 2265435 5169595 := bstep (se 1 (by rfl) ⟨3877196, by rfl⟩ : syracuseStep 5169595 = 7754393) B7754393
theorem B6892793 : Blo 2265435 6892793 := bstep (se 2 (by rfl) ⟨2584797, by rfl⟩ : syracuseStep 6892793 = 5169595) B5169595
theorem B4595195 : Blo 2265435 4595195 := bstep (se 1 (by rfl) ⟨3446396, by rfl⟩ : syracuseStep 4595195 = 6892793) B6892793
theorem B3063463 : Blo 2265435 3063463 := bstep (se 1 (by rfl) ⟨2297597, by rfl⟩ : syracuseStep 3063463 = 4595195) B4595195
theorem B16338469 : Blo 2265435 16338469 := bstep (se 4 (by rfl) ⟨1531731, by rfl⟩ : syracuseStep 16338469 = 3063463) B3063463
theorem B21784625 : Blo 2265435 21784625 := bstep (se 2 (by rfl) ⟨8169234, by rfl⟩ : syracuseStep 21784625 = 16338469) B16338469
theorem B14523083 : Blo 2265435 14523083 := bstep (se 1 (by rfl) ⟨10892312, by rfl⟩ : syracuseStep 14523083 = 21784625) B21784625
theorem B9682055 : Blo 2265435 9682055 := bstep (se 1 (by rfl) ⟨7261541, by rfl⟩ : syracuseStep 9682055 = 14523083) B14523083
theorem B6454703 : Blo 2265435 6454703 := bstep (se 1 (by rfl) ⟨4841027, by rfl⟩ : syracuseStep 6454703 = 9682055) B9682055
theorem B4303135 : Blo 2265435 4303135 := bstep (se 1 (by rfl) ⟨3227351, by rfl⟩ : syracuseStep 4303135 = 6454703) B6454703
theorem B5737513 : Blo 2265435 5737513 := bstep (se 2 (by rfl) ⟨2151567, by rfl⟩ : syracuseStep 5737513 = 4303135) B4303135
theorem B7650017 : Blo 2265435 7650017 := bstep (se 2 (by rfl) ⟨2868756, by rfl⟩ : syracuseStep 7650017 = 5737513) B5737513
theorem B5100011 : Blo 2265435 5100011 := bstep (se 1 (by rfl) ⟨3825008, by rfl⟩ : syracuseStep 5100011 = 7650017) B7650017
theorem B3400007 : Blo 2265435 3400007 := bstep (se 1 (by rfl) ⟨2550005, by rfl⟩ : syracuseStep 3400007 = 5100011) B5100011
theorem B2266671 : Blo 2265435 2266671 := bstep (se 1 (by rfl) ⟨1700003, by rfl⟩ : syracuseStep 2266671 = 3400007) B3400007
theorem B3400013 : Blo 2265435 3400013 := bbase (se 3 (by rfl) ⟨637502, by rfl⟩ : syracuseStep 3400013 = 1275005) (by norm_num)
theorem B2266675 : Blo 2265435 2266675 := bstep (se 1 (by rfl) ⟨1700006, by rfl⟩ : syracuseStep 2266675 = 3400013) B3400013
theorem B5100029 : Blo 2265435 5100029 := bbase (se 3 (by rfl) ⟨956255, by rfl⟩ : syracuseStep 5100029 = 1912511) (by norm_num)
theorem B3400019 : Blo 2265435 3400019 := bstep (se 1 (by rfl) ⟨2550014, by rfl⟩ : syracuseStep 3400019 = 5100029) B5100029
theorem B2266679 : Blo 2265435 2266679 := bstep (se 1 (by rfl) ⟨1700009, by rfl⟩ : syracuseStep 2266679 = 3400019) B3400019
theorem B3825029 : Blo 2265435 3825029 := bbase (se 4 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 3825029 = 717193) (by norm_num)
theorem B2550019 : Blo 2265435 2550019 := bstep (se 1 (by rfl) ⟨1912514, by rfl⟩ : syracuseStep 2550019 = 3825029) B3825029
theorem B3400025 : Blo 2265435 3400025 := bstep (se 2 (by rfl) ⟨1275009, by rfl⟩ : syracuseStep 3400025 = 2550019) B2550019
theorem B2266683 : Blo 2265435 2266683 := bstep (se 1 (by rfl) ⟨1700012, by rfl⟩ : syracuseStep 2266683 = 3400025) B3400025
theorem B17212661 : Blo 2265435 17212661 := bbase (se 5 (by rfl) ⟨806843, by rfl⟩ : syracuseStep 17212661 = 1613687) (by norm_num)
theorem B11475107 : Blo 2265435 11475107 := bstep (se 1 (by rfl) ⟨8606330, by rfl⟩ : syracuseStep 11475107 = 17212661) B17212661
theorem B7650071 : Blo 2265435 7650071 := bstep (se 1 (by rfl) ⟨5737553, by rfl⟩ : syracuseStep 7650071 = 11475107) B11475107
theorem B5100047 : Blo 2265435 5100047 := bstep (se 1 (by rfl) ⟨3825035, by rfl⟩ : syracuseStep 5100047 = 7650071) B7650071
theorem B3400031 : Blo 2265435 3400031 := bstep (se 1 (by rfl) ⟨2550023, by rfl⟩ : syracuseStep 3400031 = 5100047) B5100047
theorem B2266687 : Blo 2265435 2266687 := bstep (se 1 (by rfl) ⟨1700015, by rfl⟩ : syracuseStep 2266687 = 3400031) B3400031
theorem B3400037 : Blo 2265435 3400037 := bbase (se 4 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 3400037 = 637507) (by norm_num)
theorem B2266691 : Blo 2265435 2266691 := bstep (se 1 (by rfl) ⟨1700018, by rfl⟩ : syracuseStep 2266691 = 3400037) B3400037
theorem B4303181 : Blo 2265435 4303181 := bbase (se 3 (by rfl) ⟨806846, by rfl⟩ : syracuseStep 4303181 = 1613693) (by norm_num)
theorem B2868787 : Blo 2265435 2868787 := bstep (se 1 (by rfl) ⟨2151590, by rfl⟩ : syracuseStep 2868787 = 4303181) B4303181
theorem B3825049 : Blo 2265435 3825049 := bstep (se 2 (by rfl) ⟨1434393, by rfl⟩ : syracuseStep 3825049 = 2868787) B2868787
theorem B5100065 : Blo 2265435 5100065 := bstep (se 2 (by rfl) ⟨1912524, by rfl⟩ : syracuseStep 5100065 = 3825049) B3825049
theorem B3400043 : Blo 2265435 3400043 := bstep (se 1 (by rfl) ⟨2550032, by rfl⟩ : syracuseStep 3400043 = 5100065) B5100065
theorem B2266695 : Blo 2265435 2266695 := bstep (se 1 (by rfl) ⟨1700021, by rfl⟩ : syracuseStep 2266695 = 3400043) B3400043
theorem B2550037 : Blo 2265435 2550037 := bbase (se 6 (by rfl) ⟨59766, by rfl⟩ : syracuseStep 2550037 = 119533) (by norm_num)
theorem B3400049 : Blo 2265435 3400049 := bstep (se 2 (by rfl) ⟨1275018, by rfl⟩ : syracuseStep 3400049 = 2550037) B2550037
theorem B2266699 : Blo 2265435 2266699 := bstep (se 1 (by rfl) ⟨1700024, by rfl⟩ : syracuseStep 2266699 = 3400049) B3400049
theorem B2868797 : Blo 2265435 2868797 := bbase (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) (by norm_num)
theorem B7650125 : Blo 2265435 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B5100083 : Blo 2265435 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B3400055 : Blo 2265435 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B2266703 : Blo 2265435 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B3400061 : Blo 2265435 3400061 := bbase (se 3 (by rfl) ⟨637511, by rfl⟩ : syracuseStep 3400061 = 1275023) (by norm_num)
theorem B2266707 : Blo 2265435 2266707 := bstep (se 1 (by rfl) ⟨1700030, by rfl⟩ : syracuseStep 2266707 = 3400061) B3400061
theorem B5100101 : Blo 2265435 5100101 := bbase (se 4 (by rfl) ⟨478134, by rfl⟩ : syracuseStep 5100101 = 956269) (by norm_num)
theorem B3400067 : Blo 2265435 3400067 := bstep (se 1 (by rfl) ⟨2550050, by rfl⟩ : syracuseStep 3400067 = 5100101) B5100101
theorem B2266711 : Blo 2265435 2266711 := bstep (se 1 (by rfl) ⟨1700033, by rfl⟩ : syracuseStep 2266711 = 3400067) B3400067
theorem B2420561 : Blo 2265435 2420561 := bbase (se 2 (by rfl) ⟨907710, by rfl⟩ : syracuseStep 2420561 = 1815421) (by norm_num)
theorem B6454829 : Blo 2265435 6454829 := bstep (se 3 (by rfl) ⟨1210280, by rfl⟩ : syracuseStep 6454829 = 2420561) B2420561
theorem B4303219 : Blo 2265435 4303219 := bstep (se 1 (by rfl) ⟨3227414, by rfl⟩ : syracuseStep 4303219 = 6454829) B6454829
theorem B5737625 : Blo 2265435 5737625 := bstep (se 2 (by rfl) ⟨2151609, by rfl⟩ : syracuseStep 5737625 = 4303219) B4303219
theorem B3825083 : Blo 2265435 3825083 := bstep (se 1 (by rfl) ⟨2868812, by rfl⟩ : syracuseStep 3825083 = 5737625) B5737625
theorem B2550055 : Blo 2265435 2550055 := bstep (se 1 (by rfl) ⟨1912541, by rfl⟩ : syracuseStep 2550055 = 3825083) B3825083
theorem B3400073 : Blo 2265435 3400073 := bstep (se 2 (by rfl) ⟨1275027, by rfl⟩ : syracuseStep 3400073 = 2550055) B2550055
theorem B2266715 : Blo 2265435 2266715 := bstep (se 1 (by rfl) ⟨1700036, by rfl⟩ : syracuseStep 2266715 = 3400073) B3400073
theorem B11475269 : Blo 2265435 11475269 := bbase (se 4 (by rfl) ⟨1075806, by rfl⟩ : syracuseStep 11475269 = 2151613) (by norm_num)
theorem B7650179 : Blo 2265435 7650179 := bstep (se 1 (by rfl) ⟨5737634, by rfl⟩ : syracuseStep 7650179 = 11475269) B11475269
theorem B5100119 : Blo 2265435 5100119 := bstep (se 1 (by rfl) ⟨3825089, by rfl⟩ : syracuseStep 5100119 = 7650179) B7650179
theorem B3400079 : Blo 2265435 3400079 := bstep (se 1 (by rfl) ⟨2550059, by rfl⟩ : syracuseStep 3400079 = 5100119) B5100119
theorem B2266719 : Blo 2265435 2266719 := bstep (se 1 (by rfl) ⟨1700039, by rfl⟩ : syracuseStep 2266719 = 3400079) B3400079
theorem B3400085 : Blo 2265435 3400085 := bbase (se 6 (by rfl) ⟨79689, by rfl⟩ : syracuseStep 3400085 = 159379) (by norm_num)
theorem B2266723 : Blo 2265435 2266723 := bstep (se 1 (by rfl) ⟨1700042, by rfl⟩ : syracuseStep 2266723 = 3400085) B3400085
theorem B4595309 : Blo 2265435 4595309 := bbase (se 3 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 4595309 = 1723241) (by norm_num)
theorem B3063539 : Blo 2265435 3063539 := bstep (se 1 (by rfl) ⟨2297654, by rfl⟩ : syracuseStep 3063539 = 4595309) B4595309
theorem B8169437 : Blo 2265435 8169437 := bstep (se 3 (by rfl) ⟨1531769, by rfl⟩ : syracuseStep 8169437 = 3063539) B3063539
theorem B5446291 : Blo 2265435 5446291 := bstep (se 1 (by rfl) ⟨4084718, by rfl⟩ : syracuseStep 5446291 = 8169437) B8169437
theorem B7261721 : Blo 2265435 7261721 := bstep (se 2 (by rfl) ⟨2723145, by rfl⟩ : syracuseStep 7261721 = 5446291) B5446291
theorem B4841147 : Blo 2265435 4841147 := bstep (se 1 (by rfl) ⟨3630860, by rfl⟩ : syracuseStep 4841147 = 7261721) B7261721
theorem B12909725 : Blo 2265435 12909725 := bstep (se 3 (by rfl) ⟨2420573, by rfl⟩ : syracuseStep 12909725 = 4841147) B4841147
theorem B8606483 : Blo 2265435 8606483 := bstep (se 1 (by rfl) ⟨6454862, by rfl⟩ : syracuseStep 8606483 = 12909725) B12909725
theorem B5737655 : Blo 2265435 5737655 := bstep (se 1 (by rfl) ⟨4303241, by rfl⟩ : syracuseStep 5737655 = 8606483) B8606483
theorem B3825103 : Blo 2265435 3825103 := bstep (se 1 (by rfl) ⟨2868827, by rfl⟩ : syracuseStep 3825103 = 5737655) B5737655
theorem B5100137 : Blo 2265435 5100137 := bstep (se 2 (by rfl) ⟨1912551, by rfl⟩ : syracuseStep 5100137 = 3825103) B3825103
theorem B3400091 : Blo 2265435 3400091 := bstep (se 1 (by rfl) ⟨2550068, by rfl⟩ : syracuseStep 3400091 = 5100137) B5100137
theorem B2266727 : Blo 2265435 2266727 := bstep (se 1 (by rfl) ⟨1700045, by rfl⟩ : syracuseStep 2266727 = 3400091) B3400091
theorem B2550073 : Blo 2265435 2550073 := bbase (se 2 (by rfl) ⟨956277, by rfl⟩ : syracuseStep 2550073 = 1912555) (by norm_num)
theorem B3400097 : Blo 2265435 3400097 := bstep (se 2 (by rfl) ⟨1275036, by rfl⟩ : syracuseStep 3400097 = 2550073) B2550073
theorem B2266731 : Blo 2265435 2266731 := bstep (se 1 (by rfl) ⟨1700048, by rfl⟩ : syracuseStep 2266731 = 3400097) B3400097
theorem B6454885 : Blo 2265435 6454885 := bbase (se 4 (by rfl) ⟨605145, by rfl⟩ : syracuseStep 6454885 = 1210291) (by norm_num)
theorem B8606513 : Blo 2265435 8606513 := bstep (se 2 (by rfl) ⟨3227442, by rfl⟩ : syracuseStep 8606513 = 6454885) B6454885
theorem B5737675 : Blo 2265435 5737675 := bstep (se 1 (by rfl) ⟨4303256, by rfl⟩ : syracuseStep 5737675 = 8606513) B8606513
theorem B7650233 : Blo 2265435 7650233 := bstep (se 2 (by rfl) ⟨2868837, by rfl⟩ : syracuseStep 7650233 = 5737675) B5737675
theorem B5100155 : Blo 2265435 5100155 := bstep (se 1 (by rfl) ⟨3825116, by rfl⟩ : syracuseStep 5100155 = 7650233) B7650233
theorem B3400103 : Blo 2265435 3400103 := bstep (se 1 (by rfl) ⟨2550077, by rfl⟩ : syracuseStep 3400103 = 5100155) B5100155
theorem B2266735 : Blo 2265435 2266735 := bstep (se 1 (by rfl) ⟨1700051, by rfl⟩ : syracuseStep 2266735 = 3400103) B3400103
theorem B3400109 : Blo 2265435 3400109 := bbase (se 3 (by rfl) ⟨637520, by rfl⟩ : syracuseStep 3400109 = 1275041) (by norm_num)
theorem B2266739 : Blo 2265435 2266739 := bstep (se 1 (by rfl) ⟨1700054, by rfl⟩ : syracuseStep 2266739 = 3400109) B3400109
theorem B5100173 : Blo 2265435 5100173 := bbase (se 3 (by rfl) ⟨956282, by rfl⟩ : syracuseStep 5100173 = 1912565) (by norm_num)
theorem B3400115 : Blo 2265435 3400115 := bstep (se 1 (by rfl) ⟨2550086, by rfl⟩ : syracuseStep 3400115 = 5100173) B5100173
theorem B2266743 : Blo 2265435 2266743 := bstep (se 1 (by rfl) ⟨1700057, by rfl⟩ : syracuseStep 2266743 = 3400115) B3400115
theorem B2868853 : Blo 2265435 2868853 := bbase (se 5 (by rfl) ⟨134477, by rfl⟩ : syracuseStep 2868853 = 268955) (by norm_num)
theorem B3825137 : Blo 2265435 3825137 := bstep (se 2 (by rfl) ⟨1434426, by rfl⟩ : syracuseStep 3825137 = 2868853) B2868853
theorem B2550091 : Blo 2265435 2550091 := bstep (se 1 (by rfl) ⟨1912568, by rfl⟩ : syracuseStep 2550091 = 3825137) B3825137
theorem B3400121 : Blo 2265435 3400121 := bstep (se 2 (by rfl) ⟨1275045, by rfl⟩ : syracuseStep 3400121 = 2550091) B2550091
theorem B2266747 : Blo 2265435 2266747 := bstep (se 1 (by rfl) ⟨1700060, by rfl⟩ : syracuseStep 2266747 = 3400121) B3400121
theorem B24508565 : Blo 2265435 24508565 := bbase (se 6 (by rfl) ⟨574419, by rfl⟩ : syracuseStep 24508565 = 1148839) (by norm_num)
theorem B16339043 : Blo 2265435 16339043 := bstep (se 1 (by rfl) ⟨12254282, by rfl⟩ : syracuseStep 16339043 = 24508565) B24508565
theorem B43570781 : Blo 2265435 43570781 := bstep (se 3 (by rfl) ⟨8169521, by rfl⟩ : syracuseStep 43570781 = 16339043) B16339043
theorem B29047187 : Blo 2265435 29047187 := bstep (se 1 (by rfl) ⟨21785390, by rfl⟩ : syracuseStep 29047187 = 43570781) B43570781
theorem B19364791 : Blo 2265435 19364791 := bstep (se 1 (by rfl) ⟨14523593, by rfl⟩ : syracuseStep 19364791 = 29047187) B29047187
theorem B25819721 : Blo 2265435 25819721 := bstep (se 2 (by rfl) ⟨9682395, by rfl⟩ : syracuseStep 25819721 = 19364791) B19364791
theorem B17213147 : Blo 2265435 17213147 := bstep (se 1 (by rfl) ⟨12909860, by rfl⟩ : syracuseStep 17213147 = 25819721) B25819721
theorem B11475431 : Blo 2265435 11475431 := bstep (se 1 (by rfl) ⟨8606573, by rfl⟩ : syracuseStep 11475431 = 17213147) B17213147
theorem B7650287 : Blo 2265435 7650287 := bstep (se 1 (by rfl) ⟨5737715, by rfl⟩ : syracuseStep 7650287 = 11475431) B11475431
theorem B5100191 : Blo 2265435 5100191 := bstep (se 1 (by rfl) ⟨3825143, by rfl⟩ : syracuseStep 5100191 = 7650287) B7650287
theorem B3400127 : Blo 2265435 3400127 := bstep (se 1 (by rfl) ⟨2550095, by rfl⟩ : syracuseStep 3400127 = 5100191) B5100191
theorem B2266751 : Blo 2265435 2266751 := bstep (se 1 (by rfl) ⟨1700063, by rfl⟩ : syracuseStep 2266751 = 3400127) B3400127
theorem B3400133 : Blo 2265435 3400133 := bbase (se 4 (by rfl) ⟨318762, by rfl⟩ : syracuseStep 3400133 = 637525) (by norm_num)
theorem B2266755 : Blo 2265435 2266755 := bstep (se 1 (by rfl) ⟨1700066, by rfl⟩ : syracuseStep 2266755 = 3400133) B3400133
theorem B3825157 : Blo 2265435 3825157 := bbase (se 4 (by rfl) ⟨358608, by rfl⟩ : syracuseStep 3825157 = 717217) (by norm_num)
theorem B5100209 : Blo 2265435 5100209 := bstep (se 2 (by rfl) ⟨1912578, by rfl⟩ : syracuseStep 5100209 = 3825157) B3825157
theorem B3400139 : Blo 2265435 3400139 := bstep (se 1 (by rfl) ⟨2550104, by rfl⟩ : syracuseStep 3400139 = 5100209) B5100209
theorem B2266759 : Blo 2265435 2266759 := bstep (se 1 (by rfl) ⟨1700069, by rfl⟩ : syracuseStep 2266759 = 3400139) B3400139
theorem B2550109 : Blo 2265435 2550109 := bbase (se 3 (by rfl) ⟨478145, by rfl⟩ : syracuseStep 2550109 = 956291) (by norm_num)
theorem B3400145 : Blo 2265435 3400145 := bstep (se 2 (by rfl) ⟨1275054, by rfl⟩ : syracuseStep 3400145 = 2550109) B2550109
theorem B2266763 : Blo 2265435 2266763 := bstep (se 1 (by rfl) ⟨1700072, by rfl⟩ : syracuseStep 2266763 = 3400145) B3400145
theorem B7650341 : Blo 2265435 7650341 := bbase (se 4 (by rfl) ⟨717219, by rfl⟩ : syracuseStep 7650341 = 1434439) (by norm_num)
theorem B5100227 : Blo 2265435 5100227 := bstep (se 1 (by rfl) ⟨3825170, by rfl⟩ : syracuseStep 5100227 = 7650341) B7650341
theorem B3400151 : Blo 2265435 3400151 := bstep (se 1 (by rfl) ⟨2550113, by rfl⟩ : syracuseStep 3400151 = 5100227) B5100227
theorem B2266767 : Blo 2265435 2266767 := bstep (se 1 (by rfl) ⟨1700075, by rfl⟩ : syracuseStep 2266767 = 3400151) B3400151
theorem B3400157 : Blo 2265435 3400157 := bbase (se 3 (by rfl) ⟨637529, by rfl⟩ : syracuseStep 3400157 = 1275059) (by norm_num)
theorem B2266771 : Blo 2265435 2266771 := bstep (se 1 (by rfl) ⟨1700078, by rfl⟩ : syracuseStep 2266771 = 3400157) B3400157
theorem B5100245 : Blo 2265435 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B3400163 : Blo 2265435 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B2266775 : Blo 2265435 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B9682517 : Blo 2265435 9682517 := bbase (se 8 (by rfl) ⟨56733, by rfl⟩ : syracuseStep 9682517 = 113467) (by norm_num)
theorem B6455011 : Blo 2265435 6455011 := bstep (se 1 (by rfl) ⟨4841258, by rfl⟩ : syracuseStep 6455011 = 9682517) B9682517
theorem B8606681 : Blo 2265435 8606681 := bstep (se 2 (by rfl) ⟨3227505, by rfl⟩ : syracuseStep 8606681 = 6455011) B6455011
theorem B5737787 : Blo 2265435 5737787 := bstep (se 1 (by rfl) ⟨4303340, by rfl⟩ : syracuseStep 5737787 = 8606681) B8606681
theorem B3825191 : Blo 2265435 3825191 := bstep (se 1 (by rfl) ⟨2868893, by rfl⟩ : syracuseStep 3825191 = 5737787) B5737787
theorem B2550127 : Blo 2265435 2550127 := bstep (se 1 (by rfl) ⟨1912595, by rfl⟩ : syracuseStep 2550127 = 3825191) B3825191
theorem B3400169 : Blo 2265435 3400169 := bstep (se 2 (by rfl) ⟨1275063, by rfl⟩ : syracuseStep 3400169 = 2550127) B2550127
theorem B2266779 : Blo 2265435 2266779 := bstep (se 1 (by rfl) ⟨1700084, by rfl⟩ : syracuseStep 2266779 = 3400169) B3400169
theorem B32678549 : Blo 2265435 32678549 := bbase (se 6 (by rfl) ⟨765903, by rfl⟩ : syracuseStep 32678549 = 1531807) (by norm_num)
theorem B21785699 : Blo 2265435 21785699 := bstep (se 1 (by rfl) ⟨16339274, by rfl⟩ : syracuseStep 21785699 = 32678549) B32678549
theorem B14523799 : Blo 2265435 14523799 := bstep (se 1 (by rfl) ⟨10892849, by rfl⟩ : syracuseStep 14523799 = 21785699) B21785699
theorem B19365065 : Blo 2265435 19365065 := bstep (se 2 (by rfl) ⟨7261899, by rfl⟩ : syracuseStep 19365065 = 14523799) B14523799
theorem B12910043 : Blo 2265435 12910043 := bstep (se 1 (by rfl) ⟨9682532, by rfl⟩ : syracuseStep 12910043 = 19365065) B19365065
theorem B8606695 : Blo 2265435 8606695 := bstep (se 1 (by rfl) ⟨6455021, by rfl⟩ : syracuseStep 8606695 = 12910043) B12910043
theorem B11475593 : Blo 2265435 11475593 := bstep (se 2 (by rfl) ⟨4303347, by rfl⟩ : syracuseStep 11475593 = 8606695) B8606695
theorem B7650395 : Blo 2265435 7650395 := bstep (se 1 (by rfl) ⟨5737796, by rfl⟩ : syracuseStep 7650395 = 11475593) B11475593
theorem B5100263 : Blo 2265435 5100263 := bstep (se 1 (by rfl) ⟨3825197, by rfl⟩ : syracuseStep 5100263 = 7650395) B7650395
theorem B3400175 : Blo 2265435 3400175 := bstep (se 1 (by rfl) ⟨2550131, by rfl⟩ : syracuseStep 3400175 = 5100263) B5100263
theorem B2266783 : Blo 2265435 2266783 := bstep (se 1 (by rfl) ⟨1700087, by rfl⟩ : syracuseStep 2266783 = 3400175) B3400175
theorem B3400181 : Blo 2265435 3400181 := bbase (se 5 (by rfl) ⟨159383, by rfl⟩ : syracuseStep 3400181 = 318767) (by norm_num)
theorem B2266787 : Blo 2265435 2266787 := bstep (se 1 (by rfl) ⟨1700090, by rfl⟩ : syracuseStep 2266787 = 3400181) B3400181
theorem B6455045 : Blo 2265435 6455045 := bbase (se 4 (by rfl) ⟨605160, by rfl⟩ : syracuseStep 6455045 = 1210321) (by norm_num)
theorem B4303363 : Blo 2265435 4303363 := bstep (se 1 (by rfl) ⟨3227522, by rfl⟩ : syracuseStep 4303363 = 6455045) B6455045
theorem B5737817 : Blo 2265435 5737817 := bstep (se 2 (by rfl) ⟨2151681, by rfl⟩ : syracuseStep 5737817 = 4303363) B4303363
theorem B3825211 : Blo 2265435 3825211 := bstep (se 1 (by rfl) ⟨2868908, by rfl⟩ : syracuseStep 3825211 = 5737817) B5737817
theorem B5100281 : Blo 2265435 5100281 := bstep (se 2 (by rfl) ⟨1912605, by rfl⟩ : syracuseStep 5100281 = 3825211) B3825211
theorem B3400187 : Blo 2265435 3400187 := bstep (se 1 (by rfl) ⟨2550140, by rfl⟩ : syracuseStep 3400187 = 5100281) B5100281
theorem B2266791 : Blo 2265435 2266791 := bstep (se 1 (by rfl) ⟨1700093, by rfl⟩ : syracuseStep 2266791 = 3400187) B3400187
theorem B2550145 : Blo 2265435 2550145 := bbase (se 2 (by rfl) ⟨956304, by rfl⟩ : syracuseStep 2550145 = 1912609) (by norm_num)
theorem B3400193 : Blo 2265435 3400193 := bstep (se 2 (by rfl) ⟨1275072, by rfl⟩ : syracuseStep 3400193 = 2550145) B2550145
theorem B2266795 : Blo 2265435 2266795 := bstep (se 1 (by rfl) ⟨1700096, by rfl⟩ : syracuseStep 2266795 = 3400193) B3400193
theorem B5737837 : Blo 2265435 5737837 := bbase (se 3 (by rfl) ⟨1075844, by rfl⟩ : syracuseStep 5737837 = 2151689) (by norm_num)
theorem B7650449 : Blo 2265435 7650449 := bstep (se 2 (by rfl) ⟨2868918, by rfl⟩ : syracuseStep 7650449 = 5737837) B5737837
theorem B5100299 : Blo 2265435 5100299 := bstep (se 1 (by rfl) ⟨3825224, by rfl⟩ : syracuseStep 5100299 = 7650449) B7650449
theorem B3400199 : Blo 2265435 3400199 := bstep (se 1 (by rfl) ⟨2550149, by rfl⟩ : syracuseStep 3400199 = 5100299) B5100299
theorem B2266799 : Blo 2265435 2266799 := bstep (se 1 (by rfl) ⟨1700099, by rfl⟩ : syracuseStep 2266799 = 3400199) B3400199
theorem B3400205 : Blo 2265435 3400205 := bbase (se 3 (by rfl) ⟨637538, by rfl⟩ : syracuseStep 3400205 = 1275077) (by norm_num)
theorem B2266803 : Blo 2265435 2266803 := bstep (se 1 (by rfl) ⟨1700102, by rfl⟩ : syracuseStep 2266803 = 3400205) B3400205
theorem B5100317 : Blo 2265435 5100317 := bbase (se 3 (by rfl) ⟨956309, by rfl⟩ : syracuseStep 5100317 = 1912619) (by norm_num)
theorem B3400211 : Blo 2265435 3400211 := bstep (se 1 (by rfl) ⟨2550158, by rfl⟩ : syracuseStep 3400211 = 5100317) B5100317
theorem B2266807 : Blo 2265435 2266807 := bstep (se 1 (by rfl) ⟨1700105, by rfl⟩ : syracuseStep 2266807 = 3400211) B3400211
theorem B3825245 : Blo 2265435 3825245 := bbase (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) (by norm_num)
theorem B2550163 : Blo 2265435 2550163 := bstep (se 1 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 2550163 = 3825245) B3825245
theorem B3400217 : Blo 2265435 3400217 := bstep (se 2 (by rfl) ⟨1275081, by rfl⟩ : syracuseStep 3400217 = 2550163) B2550163
theorem B2266811 : Blo 2265435 2266811 := bstep (se 1 (by rfl) ⟨1700108, by rfl⟩ : syracuseStep 2266811 = 3400217) B3400217
theorem B4084877 : Blo 2265435 4084877 := bbase (se 3 (by rfl) ⟨765914, by rfl⟩ : syracuseStep 4084877 = 1531829) (by norm_num)
theorem B2723251 : Blo 2265435 2723251 := bstep (se 1 (by rfl) ⟨2042438, by rfl⟩ : syracuseStep 2723251 = 4084877) B4084877
theorem B3631001 : Blo 2265435 3631001 := bstep (se 2 (by rfl) ⟨1361625, by rfl⟩ : syracuseStep 3631001 = 2723251) B2723251
theorem B9682669 : Blo 2265435 9682669 := bstep (se 3 (by rfl) ⟨1815500, by rfl⟩ : syracuseStep 9682669 = 3631001) B3631001
theorem B12910225 : Blo 2265435 12910225 := bstep (se 2 (by rfl) ⟨4841334, by rfl⟩ : syracuseStep 12910225 = 9682669) B9682669
theorem B17213633 : Blo 2265435 17213633 := bstep (se 2 (by rfl) ⟨6455112, by rfl⟩ : syracuseStep 17213633 = 12910225) B12910225
theorem B11475755 : Blo 2265435 11475755 := bstep (se 1 (by rfl) ⟨8606816, by rfl⟩ : syracuseStep 11475755 = 17213633) B17213633
theorem B7650503 : Blo 2265435 7650503 := bstep (se 1 (by rfl) ⟨5737877, by rfl⟩ : syracuseStep 7650503 = 11475755) B11475755
theorem B5100335 : Blo 2265435 5100335 := bstep (se 1 (by rfl) ⟨3825251, by rfl⟩ : syracuseStep 5100335 = 7650503) B7650503
theorem B3400223 : Blo 2265435 3400223 := bstep (se 1 (by rfl) ⟨2550167, by rfl⟩ : syracuseStep 3400223 = 5100335) B5100335
theorem B2266815 : Blo 2265435 2266815 := bstep (se 1 (by rfl) ⟨1700111, by rfl⟩ : syracuseStep 2266815 = 3400223) B3400223
theorem B3400229 : Blo 2265435 3400229 := bbase (se 4 (by rfl) ⟨318771, by rfl⟩ : syracuseStep 3400229 = 637543) (by norm_num)
theorem B2266819 : Blo 2265435 2266819 := bstep (se 1 (by rfl) ⟨1700114, by rfl⟩ : syracuseStep 2266819 = 3400229) B3400229
theorem B2868949 : Blo 2265435 2868949 := bbase (se 7 (by rfl) ⟨33620, by rfl⟩ : syracuseStep 2868949 = 67241) (by norm_num)
theorem B3825265 : Blo 2265435 3825265 := bstep (se 2 (by rfl) ⟨1434474, by rfl⟩ : syracuseStep 3825265 = 2868949) B2868949
theorem B5100353 : Blo 2265435 5100353 := bstep (se 2 (by rfl) ⟨1912632, by rfl⟩ : syracuseStep 5100353 = 3825265) B3825265
theorem B3400235 : Blo 2265435 3400235 := bstep (se 1 (by rfl) ⟨2550176, by rfl⟩ : syracuseStep 3400235 = 5100353) B5100353
theorem B2266823 : Blo 2265435 2266823 := bstep (se 1 (by rfl) ⟨1700117, by rfl⟩ : syracuseStep 2266823 = 3400235) B3400235
theorem B2550181 : Blo 2265435 2550181 := bbase (se 4 (by rfl) ⟨239079, by rfl⟩ : syracuseStep 2550181 = 478159) (by norm_num)
theorem B3400241 : Blo 2265435 3400241 := bstep (se 2 (by rfl) ⟨1275090, by rfl⟩ : syracuseStep 3400241 = 2550181) B2550181
theorem B2266827 : Blo 2265435 2266827 := bstep (se 1 (by rfl) ⟨1700120, by rfl⟩ : syracuseStep 2266827 = 3400241) B3400241
theorem B5446541 : Blo 2265435 5446541 := bbase (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) (by norm_num)
theorem B14524109 : Blo 2265435 14524109 := bstep (se 3 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 14524109 = 5446541) B5446541
theorem B9682739 : Blo 2265435 9682739 := bstep (se 1 (by rfl) ⟨7262054, by rfl⟩ : syracuseStep 9682739 = 14524109) B14524109
theorem B6455159 : Blo 2265435 6455159 := bstep (se 1 (by rfl) ⟨4841369, by rfl⟩ : syracuseStep 6455159 = 9682739) B9682739
theorem B4303439 : Blo 2265435 4303439 := bstep (se 1 (by rfl) ⟨3227579, by rfl⟩ : syracuseStep 4303439 = 6455159) B6455159
theorem B2868959 : Blo 2265435 2868959 := bstep (se 1 (by rfl) ⟨2151719, by rfl⟩ : syracuseStep 2868959 = 4303439) B4303439
theorem B7650557 : Blo 2265435 7650557 := bstep (se 3 (by rfl) ⟨1434479, by rfl⟩ : syracuseStep 7650557 = 2868959) B2868959
theorem B5100371 : Blo 2265435 5100371 := bstep (se 1 (by rfl) ⟨3825278, by rfl⟩ : syracuseStep 5100371 = 7650557) B7650557
theorem B3400247 : Blo 2265435 3400247 := bstep (se 1 (by rfl) ⟨2550185, by rfl⟩ : syracuseStep 3400247 = 5100371) B5100371
theorem B2266831 : Blo 2265435 2266831 := bstep (se 1 (by rfl) ⟨1700123, by rfl⟩ : syracuseStep 2266831 = 3400247) B3400247
theorem B3400253 : Blo 2265435 3400253 := bbase (se 3 (by rfl) ⟨637547, by rfl⟩ : syracuseStep 3400253 = 1275095) (by norm_num)
theorem B2266835 : Blo 2265435 2266835 := bstep (se 1 (by rfl) ⟨1700126, by rfl⟩ : syracuseStep 2266835 = 3400253) B3400253
theorem B5100389 : Blo 2265435 5100389 := bbase (se 4 (by rfl) ⟨478161, by rfl⟩ : syracuseStep 5100389 = 956323) (by norm_num)
theorem B3400259 : Blo 2265435 3400259 := bstep (se 1 (by rfl) ⟨2550194, by rfl⟩ : syracuseStep 3400259 = 5100389) B5100389
theorem B2266839 : Blo 2265435 2266839 := bstep (se 1 (by rfl) ⟨1700129, by rfl⟩ : syracuseStep 2266839 = 3400259) B3400259
theorem B5737949 : Blo 2265435 5737949 := bbase (se 3 (by rfl) ⟨1075865, by rfl⟩ : syracuseStep 5737949 = 2151731) (by norm_num)
theorem B3825299 : Blo 2265435 3825299 := bstep (se 1 (by rfl) ⟨2868974, by rfl⟩ : syracuseStep 3825299 = 5737949) B5737949
theorem B2550199 : Blo 2265435 2550199 := bstep (se 1 (by rfl) ⟨1912649, by rfl⟩ : syracuseStep 2550199 = 3825299) B3825299
theorem B3400265 : Blo 2265435 3400265 := bstep (se 2 (by rfl) ⟨1275099, by rfl⟩ : syracuseStep 3400265 = 2550199) B2550199
theorem B2266843 : Blo 2265435 2266843 := bstep (se 1 (by rfl) ⟨1700132, by rfl⟩ : syracuseStep 2266843 = 3400265) B3400265
theorem B4303469 : Blo 2265435 4303469 := bbase (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) (by norm_num)
theorem B11475917 : Blo 2265435 11475917 := bstep (se 3 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 11475917 = 4303469) B4303469
theorem B7650611 : Blo 2265435 7650611 := bstep (se 1 (by rfl) ⟨5737958, by rfl⟩ : syracuseStep 7650611 = 11475917) B11475917
theorem B5100407 : Blo 2265435 5100407 := bstep (se 1 (by rfl) ⟨3825305, by rfl⟩ : syracuseStep 5100407 = 7650611) B7650611
theorem B3400271 : Blo 2265435 3400271 := bstep (se 1 (by rfl) ⟨2550203, by rfl⟩ : syracuseStep 3400271 = 5100407) B5100407
theorem B2266847 : Blo 2265435 2266847 := bstep (se 1 (by rfl) ⟨1700135, by rfl⟩ : syracuseStep 2266847 = 3400271) B3400271
theorem B3400277 : Blo 2265435 3400277 := bbase (se 8 (by rfl) ⟨19923, by rfl⟩ : syracuseStep 3400277 = 39847) (by norm_num)
theorem B2266851 : Blo 2265435 2266851 := bstep (se 1 (by rfl) ⟨1700138, by rfl⟩ : syracuseStep 2266851 = 3400277) B3400277
theorem B4084949 : Blo 2265435 4084949 := bbase (se 7 (by rfl) ⟨47870, by rfl⟩ : syracuseStep 4084949 = 95741) (by norm_num)
theorem B10893197 : Blo 2265435 10893197 := bstep (se 3 (by rfl) ⟨2042474, by rfl⟩ : syracuseStep 10893197 = 4084949) B4084949
theorem B7262131 : Blo 2265435 7262131 := bstep (se 1 (by rfl) ⟨5446598, by rfl⟩ : syracuseStep 7262131 = 10893197) B10893197
theorem B9682841 : Blo 2265435 9682841 := bstep (se 2 (by rfl) ⟨3631065, by rfl⟩ : syracuseStep 9682841 = 7262131) B7262131
theorem B6455227 : Blo 2265435 6455227 := bstep (se 1 (by rfl) ⟨4841420, by rfl⟩ : syracuseStep 6455227 = 9682841) B9682841
theorem B8606969 : Blo 2265435 8606969 := bstep (se 2 (by rfl) ⟨3227613, by rfl⟩ : syracuseStep 8606969 = 6455227) B6455227
theorem B5737979 : Blo 2265435 5737979 := bstep (se 1 (by rfl) ⟨4303484, by rfl⟩ : syracuseStep 5737979 = 8606969) B8606969
theorem B3825319 : Blo 2265435 3825319 := bstep (se 1 (by rfl) ⟨2868989, by rfl⟩ : syracuseStep 3825319 = 5737979) B5737979
theorem B5100425 : Blo 2265435 5100425 := bstep (se 2 (by rfl) ⟨1912659, by rfl⟩ : syracuseStep 5100425 = 3825319) B3825319
theorem B3400283 : Blo 2265435 3400283 := bstep (se 1 (by rfl) ⟨2550212, by rfl⟩ : syracuseStep 3400283 = 5100425) B5100425
theorem B2266855 : Blo 2265435 2266855 := bstep (se 1 (by rfl) ⟨1700141, by rfl⟩ : syracuseStep 2266855 = 3400283) B3400283
theorem B2550217 : Blo 2265435 2550217 := bbase (se 2 (by rfl) ⟨956331, by rfl⟩ : syracuseStep 2550217 = 1912663) (by norm_num)
theorem B3400289 : Blo 2265435 3400289 := bstep (se 2 (by rfl) ⟨1275108, by rfl⟩ : syracuseStep 3400289 = 2550217) B2550217
theorem B2266859 : Blo 2265435 2266859 := bstep (se 1 (by rfl) ⟨1700144, by rfl⟩ : syracuseStep 2266859 = 3400289) B3400289
theorem B19365749 : Blo 2265435 19365749 := bbase (se 5 (by rfl) ⟨907769, by rfl⟩ : syracuseStep 19365749 = 1815539) (by norm_num)
theorem B12910499 : Blo 2265435 12910499 := bstep (se 1 (by rfl) ⟨9682874, by rfl⟩ : syracuseStep 12910499 = 19365749) B19365749
theorem B8606999 : Blo 2265435 8606999 := bstep (se 1 (by rfl) ⟨6455249, by rfl⟩ : syracuseStep 8606999 = 12910499) B12910499
theorem B5737999 : Blo 2265435 5737999 := bstep (se 1 (by rfl) ⟨4303499, by rfl⟩ : syracuseStep 5737999 = 8606999) B8606999
theorem B7650665 : Blo 2265435 7650665 := bstep (se 2 (by rfl) ⟨2868999, by rfl⟩ : syracuseStep 7650665 = 5737999) B5737999
theorem B5100443 : Blo 2265435 5100443 := bstep (se 1 (by rfl) ⟨3825332, by rfl⟩ : syracuseStep 5100443 = 7650665) B7650665
theorem B3400295 : Blo 2265435 3400295 := bstep (se 1 (by rfl) ⟨2550221, by rfl⟩ : syracuseStep 3400295 = 5100443) B5100443
theorem B2266863 : Blo 2265435 2266863 := bstep (se 1 (by rfl) ⟨1700147, by rfl⟩ : syracuseStep 2266863 = 3400295) B3400295
theorem B3400301 : Blo 2265435 3400301 := bbase (se 3 (by rfl) ⟨637556, by rfl⟩ : syracuseStep 3400301 = 1275113) (by norm_num)
theorem B2266867 : Blo 2265435 2266867 := bstep (se 1 (by rfl) ⟨1700150, by rfl⟩ : syracuseStep 2266867 = 3400301) B3400301
theorem B5100461 : Blo 2265435 5100461 := bbase (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) (by norm_num)
theorem B3400307 : Blo 2265435 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B2266871 : Blo 2265435 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B6455285 : Blo 2265435 6455285 := bbase (se 5 (by rfl) ⟨302591, by rfl⟩ : syracuseStep 6455285 = 605183) (by norm_num)
theorem B4303523 : Blo 2265435 4303523 := bstep (se 1 (by rfl) ⟨3227642, by rfl⟩ : syracuseStep 4303523 = 6455285) B6455285
theorem B2869015 : Blo 2265435 2869015 := bstep (se 1 (by rfl) ⟨2151761, by rfl⟩ : syracuseStep 2869015 = 4303523) B4303523
theorem B3825353 : Blo 2265435 3825353 := bstep (se 2 (by rfl) ⟨1434507, by rfl⟩ : syracuseStep 3825353 = 2869015) B2869015
theorem B2550235 : Blo 2265435 2550235 := bstep (se 1 (by rfl) ⟨1912676, by rfl⟩ : syracuseStep 2550235 = 3825353) B3825353
theorem B3400313 : Blo 2265435 3400313 := bstep (se 2 (by rfl) ⟨1275117, by rfl⟩ : syracuseStep 3400313 = 2550235) B2550235
theorem B2266875 : Blo 2265435 2266875 := bstep (se 1 (by rfl) ⟨1700156, by rfl⟩ : syracuseStep 2266875 = 3400313) B3400313
theorem B11345285 : Blo 2265435 11345285 := bbase (se 4 (by rfl) ⟨1063620, by rfl⟩ : syracuseStep 11345285 = 2127241) (by norm_num)
theorem B7563523 : Blo 2265435 7563523 := bstep (se 1 (by rfl) ⟨5672642, by rfl⟩ : syracuseStep 7563523 = 11345285) B11345285
theorem B10084697 : Blo 2265435 10084697 := bstep (se 2 (by rfl) ⟨3781761, by rfl⟩ : syracuseStep 10084697 = 7563523) B7563523
theorem B6723131 : Blo 2265435 6723131 := bstep (se 1 (by rfl) ⟨5042348, by rfl⟩ : syracuseStep 6723131 = 10084697) B10084697
theorem B17928349 : Blo 2265435 17928349 := bstep (se 3 (by rfl) ⟨3361565, by rfl⟩ : syracuseStep 17928349 = 6723131) B6723131
theorem B382471445 : Blo 2265435 382471445 := bstep (se 6 (by rfl) ⟨8964174, by rfl⟩ : syracuseStep 382471445 = 17928349) B17928349
theorem B254980963 : Blo 2265435 254980963 := bstep (se 1 (by rfl) ⟨191235722, by rfl⟩ : syracuseStep 254980963 = 382471445) B382471445
theorem B339974617 : Blo 2265435 339974617 := bstep (se 2 (by rfl) ⟨127490481, by rfl⟩ : syracuseStep 339974617 = 254980963) B254980963
theorem B453299489 : Blo 2265435 453299489 := bstep (se 2 (by rfl) ⟨169987308, by rfl⟩ : syracuseStep 453299489 = 339974617) B339974617
theorem B302199659 : Blo 2265435 302199659 := bstep (se 1 (by rfl) ⟨226649744, by rfl⟩ : syracuseStep 302199659 = 453299489) B453299489
theorem B201466439 : Blo 2265435 201466439 := bstep (se 1 (by rfl) ⟨151099829, by rfl⟩ : syracuseStep 201466439 = 302199659) B302199659
theorem B134310959 : Blo 2265435 134310959 := bstep (se 1 (by rfl) ⟨100733219, by rfl⟩ : syracuseStep 134310959 = 201466439) B201466439
theorem B89540639 : Blo 2265435 89540639 := bstep (se 1 (by rfl) ⟨67155479, by rfl⟩ : syracuseStep 89540639 = 134310959) B134310959
theorem B59693759 : Blo 2265435 59693759 := bstep (se 1 (by rfl) ⟨44770319, by rfl⟩ : syracuseStep 59693759 = 89540639) B89540639
theorem B39795839 : Blo 2265435 39795839 := bstep (se 1 (by rfl) ⟨29846879, by rfl⟩ : syracuseStep 39795839 = 59693759) B59693759
theorem B26530559 : Blo 2265435 26530559 := bstep (se 1 (by rfl) ⟨19897919, by rfl⟩ : syracuseStep 26530559 = 39795839) B39795839
theorem B282992629 : Blo 2265435 282992629 := bstep (se 5 (by rfl) ⟨13265279, by rfl⟩ : syracuseStep 282992629 = 26530559) B26530559
theorem B377323505 : Blo 2265435 377323505 := bstep (se 2 (by rfl) ⟨141496314, by rfl⟩ : syracuseStep 377323505 = 282992629) B282992629
theorem B251549003 : Blo 2265435 251549003 := bstep (se 1 (by rfl) ⟨188661752, by rfl⟩ : syracuseStep 251549003 = 377323505) B377323505
theorem B167699335 : Blo 2265435 167699335 := bstep (se 1 (by rfl) ⟨125774501, by rfl⟩ : syracuseStep 167699335 = 251549003) B251549003
theorem B223599113 : Blo 2265435 223599113 := bstep (se 2 (by rfl) ⟨83849667, by rfl⟩ : syracuseStep 223599113 = 167699335) B167699335
theorem B149066075 : Blo 2265435 149066075 := bstep (se 1 (by rfl) ⟨111799556, by rfl⟩ : syracuseStep 149066075 = 223599113) B223599113
theorem B99377383 : Blo 2265435 99377383 := bstep (se 1 (by rfl) ⟨74533037, by rfl⟩ : syracuseStep 99377383 = 149066075) B149066075
theorem B132503177 : Blo 2265435 132503177 := bstep (se 2 (by rfl) ⟨49688691, by rfl⟩ : syracuseStep 132503177 = 99377383) B99377383
theorem B88335451 : Blo 2265435 88335451 := bstep (se 1 (by rfl) ⟨66251588, by rfl⟩ : syracuseStep 88335451 = 132503177) B132503177
theorem B117780601 : Blo 2265435 117780601 := bstep (se 2 (by rfl) ⟨44167725, by rfl⟩ : syracuseStep 117780601 = 88335451) B88335451
theorem B157040801 : Blo 2265435 157040801 := bstep (se 2 (by rfl) ⟨58890300, by rfl⟩ : syracuseStep 157040801 = 117780601) B117780601
theorem B104693867 : Blo 2265435 104693867 := bstep (se 1 (by rfl) ⟨78520400, by rfl⟩ : syracuseStep 104693867 = 157040801) B157040801
theorem B69795911 : Blo 2265435 69795911 := bstep (se 1 (by rfl) ⟨52346933, by rfl⟩ : syracuseStep 69795911 = 104693867) B104693867
theorem B46530607 : Blo 2265435 46530607 := bstep (se 1 (by rfl) ⟨34897955, by rfl⟩ : syracuseStep 46530607 = 69795911) B69795911
theorem B62040809 : Blo 2265435 62040809 := bstep (se 2 (by rfl) ⟨23265303, by rfl⟩ : syracuseStep 62040809 = 46530607) B46530607
theorem B41360539 : Blo 2265435 41360539 := bstep (se 1 (by rfl) ⟨31020404, by rfl⟩ : syracuseStep 41360539 = 62040809) B62040809
theorem B55147385 : Blo 2265435 55147385 := bstep (se 2 (by rfl) ⟨20680269, by rfl⟩ : syracuseStep 55147385 = 41360539) B41360539
theorem B36764923 : Blo 2265435 36764923 := bstep (se 1 (by rfl) ⟨27573692, by rfl⟩ : syracuseStep 36764923 = 55147385) B55147385
theorem B49019897 : Blo 2265435 49019897 := bstep (se 2 (by rfl) ⟨18382461, by rfl⟩ : syracuseStep 49019897 = 36764923) B36764923
theorem B32679931 : Blo 2265435 32679931 := bstep (se 1 (by rfl) ⟨24509948, by rfl⟩ : syracuseStep 32679931 = 49019897) B49019897
theorem B43573241 : Blo 2265435 43573241 := bstep (se 2 (by rfl) ⟨16339965, by rfl⟩ : syracuseStep 43573241 = 32679931) B32679931
theorem B29048827 : Blo 2265435 29048827 := bstep (se 1 (by rfl) ⟨21786620, by rfl⟩ : syracuseStep 29048827 = 43573241) B43573241
theorem B38731769 : Blo 2265435 38731769 := bstep (se 2 (by rfl) ⟨14524413, by rfl⟩ : syracuseStep 38731769 = 29048827) B29048827
theorem B25821179 : Blo 2265435 25821179 := bstep (se 1 (by rfl) ⟨19365884, by rfl⟩ : syracuseStep 25821179 = 38731769) B38731769
theorem B17214119 : Blo 2265435 17214119 := bstep (se 1 (by rfl) ⟨12910589, by rfl⟩ : syracuseStep 17214119 = 25821179) B25821179
theorem B11476079 : Blo 2265435 11476079 := bstep (se 1 (by rfl) ⟨8607059, by rfl⟩ : syracuseStep 11476079 = 17214119) B17214119
theorem B7650719 : Blo 2265435 7650719 := bstep (se 1 (by rfl) ⟨5738039, by rfl⟩ : syracuseStep 7650719 = 11476079) B11476079
theorem B5100479 : Blo 2265435 5100479 := bstep (se 1 (by rfl) ⟨3825359, by rfl⟩ : syracuseStep 5100479 = 7650719) B7650719
theorem B3400319 : Blo 2265435 3400319 := bstep (se 1 (by rfl) ⟨2550239, by rfl⟩ : syracuseStep 3400319 = 5100479) B5100479
theorem B2266879 : Blo 2265435 2266879 := bstep (se 1 (by rfl) ⟨1700159, by rfl⟩ : syracuseStep 2266879 = 3400319) B3400319
theorem B3400325 : Blo 2265435 3400325 := bbase (se 4 (by rfl) ⟨318780, by rfl⟩ : syracuseStep 3400325 = 637561) (by norm_num)
theorem B2266883 : Blo 2265435 2266883 := bstep (se 1 (by rfl) ⟨1700162, by rfl⟩ : syracuseStep 2266883 = 3400325) B3400325
theorem B3825373 : Blo 2265435 3825373 := bbase (se 3 (by rfl) ⟨717257, by rfl⟩ : syracuseStep 3825373 = 1434515) (by norm_num)
theorem B5100497 : Blo 2265435 5100497 := bstep (se 2 (by rfl) ⟨1912686, by rfl⟩ : syracuseStep 5100497 = 3825373) B3825373
theorem B3400331 : Blo 2265435 3400331 := bstep (se 1 (by rfl) ⟨2550248, by rfl⟩ : syracuseStep 3400331 = 5100497) B5100497
theorem B2266887 : Blo 2265435 2266887 := bstep (se 1 (by rfl) ⟨1700165, by rfl⟩ : syracuseStep 2266887 = 3400331) B3400331
theorem B2550253 : Blo 2265435 2550253 := bbase (se 3 (by rfl) ⟨478172, by rfl⟩ : syracuseStep 2550253 = 956345) (by norm_num)
theorem B3400337 : Blo 2265435 3400337 := bstep (se 2 (by rfl) ⟨1275126, by rfl⟩ : syracuseStep 3400337 = 2550253) B2550253
theorem B2266891 : Blo 2265435 2266891 := bstep (se 1 (by rfl) ⟨1700168, by rfl⟩ : syracuseStep 2266891 = 3400337) B3400337
theorem B7650773 : Blo 2265435 7650773 := bbase (se 7 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 7650773 = 179315) (by norm_num)
theorem B5100515 : Blo 2265435 5100515 := bstep (se 1 (by rfl) ⟨3825386, by rfl⟩ : syracuseStep 5100515 = 7650773) B7650773
theorem B3400343 : Blo 2265435 3400343 := bstep (se 1 (by rfl) ⟨2550257, by rfl⟩ : syracuseStep 3400343 = 5100515) B5100515
theorem B2266895 : Blo 2265435 2266895 := bstep (se 1 (by rfl) ⟨1700171, by rfl⟩ : syracuseStep 2266895 = 3400343) B3400343
theorem B3400349 : Blo 2265435 3400349 := bbase (se 3 (by rfl) ⟨637565, by rfl⟩ : syracuseStep 3400349 = 1275131) (by norm_num)
theorem B2266899 : Blo 2265435 2266899 := bstep (se 1 (by rfl) ⟨1700174, by rfl⟩ : syracuseStep 2266899 = 3400349) B3400349
theorem B5100533 : Blo 2265435 5100533 := bbase (se 5 (by rfl) ⟨239087, by rfl⟩ : syracuseStep 5100533 = 478175) (by norm_num)
theorem B3400355 : Blo 2265435 3400355 := bstep (se 1 (by rfl) ⟨2550266, by rfl⟩ : syracuseStep 3400355 = 5100533) B5100533
theorem B2266903 : Blo 2265435 2266903 := bstep (se 1 (by rfl) ⟨1700177, by rfl⟩ : syracuseStep 2266903 = 3400355) B3400355
theorem B7361381 : Blo 2265435 7361381 := bbase (se 4 (by rfl) ⟨690129, by rfl⟩ : syracuseStep 7361381 = 1380259) (by norm_num)
theorem B4907587 : Blo 2265435 4907587 := bstep (se 1 (by rfl) ⟨3680690, by rfl⟩ : syracuseStep 4907587 = 7361381) B7361381
theorem B6543449 : Blo 2265435 6543449 := bstep (se 2 (by rfl) ⟨2453793, by rfl⟩ : syracuseStep 6543449 = 4907587) B4907587
theorem B4362299 : Blo 2265435 4362299 := bstep (se 1 (by rfl) ⟨3271724, by rfl⟩ : syracuseStep 4362299 = 6543449) B6543449
theorem B46531189 : Blo 2265435 46531189 := bstep (se 5 (by rfl) ⟨2181149, by rfl⟩ : syracuseStep 46531189 = 4362299) B4362299
theorem B248166341 : Blo 2265435 248166341 := bstep (se 4 (by rfl) ⟨23265594, by rfl⟩ : syracuseStep 248166341 = 46531189) B46531189
theorem B165444227 : Blo 2265435 165444227 := bstep (se 1 (by rfl) ⟨124083170, by rfl⟩ : syracuseStep 165444227 = 248166341) B248166341
theorem B110296151 : Blo 2265435 110296151 := bstep (se 1 (by rfl) ⟨82722113, by rfl⟩ : syracuseStep 110296151 = 165444227) B165444227
theorem B73530767 : Blo 2265435 73530767 := bstep (se 1 (by rfl) ⟨55148075, by rfl⟩ : syracuseStep 73530767 = 110296151) B110296151
theorem B49020511 : Blo 2265435 49020511 := bstep (se 1 (by rfl) ⟨36765383, by rfl⟩ : syracuseStep 49020511 = 73530767) B73530767
theorem B65360681 : Blo 2265435 65360681 := bstep (se 2 (by rfl) ⟨24510255, by rfl⟩ : syracuseStep 65360681 = 49020511) B49020511
theorem B43573787 : Blo 2265435 43573787 := bstep (se 1 (by rfl) ⟨32680340, by rfl⟩ : syracuseStep 43573787 = 65360681) B65360681
theorem B29049191 : Blo 2265435 29049191 := bstep (se 1 (by rfl) ⟨21786893, by rfl⟩ : syracuseStep 29049191 = 43573787) B43573787
theorem B19366127 : Blo 2265435 19366127 := bstep (se 1 (by rfl) ⟨14524595, by rfl⟩ : syracuseStep 19366127 = 29049191) B29049191
theorem B12910751 : Blo 2265435 12910751 := bstep (se 1 (by rfl) ⟨9683063, by rfl⟩ : syracuseStep 12910751 = 19366127) B19366127
theorem B8607167 : Blo 2265435 8607167 := bstep (se 1 (by rfl) ⟨6455375, by rfl⟩ : syracuseStep 8607167 = 12910751) B12910751
theorem B5738111 : Blo 2265435 5738111 := bstep (se 1 (by rfl) ⟨4303583, by rfl⟩ : syracuseStep 5738111 = 8607167) B8607167
theorem B3825407 : Blo 2265435 3825407 := bstep (se 1 (by rfl) ⟨2869055, by rfl⟩ : syracuseStep 3825407 = 5738111) B5738111
theorem B2550271 : Blo 2265435 2550271 := bstep (se 1 (by rfl) ⟨1912703, by rfl⟩ : syracuseStep 2550271 = 3825407) B3825407
theorem B3400361 : Blo 2265435 3400361 := bstep (se 2 (by rfl) ⟨1275135, by rfl⟩ : syracuseStep 3400361 = 2550271) B2550271
theorem B2266907 : Blo 2265435 2266907 := bstep (se 1 (by rfl) ⟨1700180, by rfl⟩ : syracuseStep 2266907 = 3400361) B3400361
theorem B3227693 : Blo 2265435 3227693 := bbase (se 3 (by rfl) ⟨605192, by rfl⟩ : syracuseStep 3227693 = 1210385) (by norm_num)
theorem B8607181 : Blo 2265435 8607181 := bstep (se 3 (by rfl) ⟨1613846, by rfl⟩ : syracuseStep 8607181 = 3227693) B3227693
theorem B11476241 : Blo 2265435 11476241 := bstep (se 2 (by rfl) ⟨4303590, by rfl⟩ : syracuseStep 11476241 = 8607181) B8607181
theorem B7650827 : Blo 2265435 7650827 := bstep (se 1 (by rfl) ⟨5738120, by rfl⟩ : syracuseStep 7650827 = 11476241) B11476241
theorem B5100551 : Blo 2265435 5100551 := bstep (se 1 (by rfl) ⟨3825413, by rfl⟩ : syracuseStep 5100551 = 7650827) B7650827
theorem B3400367 : Blo 2265435 3400367 := bstep (se 1 (by rfl) ⟨2550275, by rfl⟩ : syracuseStep 3400367 = 5100551) B5100551
theorem B2266911 : Blo 2265435 2266911 := bstep (se 1 (by rfl) ⟨1700183, by rfl⟩ : syracuseStep 2266911 = 3400367) B3400367
theorem B3400373 : Blo 2265435 3400373 := bbase (se 5 (by rfl) ⟨159392, by rfl⟩ : syracuseStep 3400373 = 318785) (by norm_num)
theorem B2266915 : Blo 2265435 2266915 := bstep (se 1 (by rfl) ⟨1700186, by rfl⟩ : syracuseStep 2266915 = 3400373) B3400373
theorem B5738141 : Blo 2265435 5738141 := bbase (se 3 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 5738141 = 2151803) (by norm_num)
theorem B3825427 : Blo 2265435 3825427 := bstep (se 1 (by rfl) ⟨2869070, by rfl⟩ : syracuseStep 3825427 = 5738141) B5738141
theorem B5100569 : Blo 2265435 5100569 := bstep (se 2 (by rfl) ⟨1912713, by rfl⟩ : syracuseStep 5100569 = 3825427) B3825427
theorem B3400379 : Blo 2265435 3400379 := bstep (se 1 (by rfl) ⟨2550284, by rfl⟩ : syracuseStep 3400379 = 5100569) B5100569
theorem B2266919 : Blo 2265435 2266919 := bstep (se 1 (by rfl) ⟨1700189, by rfl⟩ : syracuseStep 2266919 = 3400379) B3400379
theorem B2550289 : Blo 2265435 2550289 := bbase (se 2 (by rfl) ⟨956358, by rfl⟩ : syracuseStep 2550289 = 1912717) (by norm_num)
theorem B3400385 : Blo 2265435 3400385 := bstep (se 2 (by rfl) ⟨1275144, by rfl⟩ : syracuseStep 3400385 = 2550289) B2550289
theorem B2266923 : Blo 2265435 2266923 := bstep (se 1 (by rfl) ⟨1700192, by rfl⟩ : syracuseStep 2266923 = 3400385) B3400385
theorem B4303621 : Blo 2265435 4303621 := bbase (se 4 (by rfl) ⟨403464, by rfl⟩ : syracuseStep 4303621 = 806929) (by norm_num)
theorem B5738161 : Blo 2265435 5738161 := bstep (se 2 (by rfl) ⟨2151810, by rfl⟩ : syracuseStep 5738161 = 4303621) B4303621
theorem B7650881 : Blo 2265435 7650881 := bstep (se 2 (by rfl) ⟨2869080, by rfl⟩ : syracuseStep 7650881 = 5738161) B5738161
theorem B5100587 : Blo 2265435 5100587 := bstep (se 1 (by rfl) ⟨3825440, by rfl⟩ : syracuseStep 5100587 = 7650881) B7650881
theorem B3400391 : Blo 2265435 3400391 := bstep (se 1 (by rfl) ⟨2550293, by rfl⟩ : syracuseStep 3400391 = 5100587) B5100587
theorem B2266927 : Blo 2265435 2266927 := bstep (se 1 (by rfl) ⟨1700195, by rfl⟩ : syracuseStep 2266927 = 3400391) B3400391
theorem B3400397 : Blo 2265435 3400397 := bbase (se 3 (by rfl) ⟨637574, by rfl⟩ : syracuseStep 3400397 = 1275149) (by norm_num)
theorem B2266931 : Blo 2265435 2266931 := bstep (se 1 (by rfl) ⟨1700198, by rfl⟩ : syracuseStep 2266931 = 3400397) B3400397
theorem B5100605 : Blo 2265435 5100605 := bbase (se 3 (by rfl) ⟨956363, by rfl⟩ : syracuseStep 5100605 = 1912727) (by norm_num)
theorem B3400403 : Blo 2265435 3400403 := bstep (se 1 (by rfl) ⟨2550302, by rfl⟩ : syracuseStep 3400403 = 5100605) B5100605
theorem B2266935 : Blo 2265435 2266935 := bstep (se 1 (by rfl) ⟨1700201, by rfl⟩ : syracuseStep 2266935 = 3400403) B3400403
theorem B3825461 : Blo 2265435 3825461 := bbase (se 5 (by rfl) ⟨179318, by rfl⟩ : syracuseStep 3825461 = 358637) (by norm_num)
theorem B2550307 : Blo 2265435 2550307 := bstep (se 1 (by rfl) ⟨1912730, by rfl⟩ : syracuseStep 2550307 = 3825461) B3825461
theorem B3400409 : Blo 2265435 3400409 := bstep (se 2 (by rfl) ⟨1275153, by rfl⟩ : syracuseStep 3400409 = 2550307) B2550307
theorem B2266939 : Blo 2265435 2266939 := bstep (se 1 (by rfl) ⟨1700204, by rfl⟩ : syracuseStep 2266939 = 3400409) B3400409
theorem B6455477 : Blo 2265435 6455477 := bbase (se 5 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 6455477 = 605201) (by norm_num)
theorem B17214605 : Blo 2265435 17214605 := bstep (se 3 (by rfl) ⟨3227738, by rfl⟩ : syracuseStep 17214605 = 6455477) B6455477
theorem B11476403 : Blo 2265435 11476403 := bstep (se 1 (by rfl) ⟨8607302, by rfl⟩ : syracuseStep 11476403 = 17214605) B17214605
theorem B7650935 : Blo 2265435 7650935 := bstep (se 1 (by rfl) ⟨5738201, by rfl⟩ : syracuseStep 7650935 = 11476403) B11476403
theorem B5100623 : Blo 2265435 5100623 := bstep (se 1 (by rfl) ⟨3825467, by rfl⟩ : syracuseStep 5100623 = 7650935) B7650935
theorem B3400415 : Blo 2265435 3400415 := bstep (se 1 (by rfl) ⟨2550311, by rfl⟩ : syracuseStep 3400415 = 5100623) B5100623
theorem B2266943 : Blo 2265435 2266943 := bstep (se 1 (by rfl) ⟨1700207, by rfl⟩ : syracuseStep 2266943 = 3400415) B3400415
theorem B3400421 : Blo 2265435 3400421 := bbase (se 4 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 3400421 = 637579) (by norm_num)
theorem B2266947 : Blo 2265435 2266947 := bstep (se 1 (by rfl) ⟨1700210, by rfl⟩ : syracuseStep 2266947 = 3400421) B3400421
theorem B2420813 : Blo 2265435 2420813 := bbase (se 3 (by rfl) ⟨453902, by rfl⟩ : syracuseStep 2420813 = 907805) (by norm_num)
theorem B6455501 : Blo 2265435 6455501 := bstep (se 3 (by rfl) ⟨1210406, by rfl⟩ : syracuseStep 6455501 = 2420813) B2420813
theorem B4303667 : Blo 2265435 4303667 := bstep (se 1 (by rfl) ⟨3227750, by rfl⟩ : syracuseStep 4303667 = 6455501) B6455501
theorem B2869111 : Blo 2265435 2869111 := bstep (se 1 (by rfl) ⟨2151833, by rfl⟩ : syracuseStep 2869111 = 4303667) B4303667
theorem B3825481 : Blo 2265435 3825481 := bstep (se 2 (by rfl) ⟨1434555, by rfl⟩ : syracuseStep 3825481 = 2869111) B2869111
theorem B5100641 : Blo 2265435 5100641 := bstep (se 2 (by rfl) ⟨1912740, by rfl⟩ : syracuseStep 5100641 = 3825481) B3825481
theorem B3400427 : Blo 2265435 3400427 := bstep (se 1 (by rfl) ⟨2550320, by rfl⟩ : syracuseStep 3400427 = 5100641) B5100641
theorem B2266951 : Blo 2265435 2266951 := bstep (se 1 (by rfl) ⟨1700213, by rfl⟩ : syracuseStep 2266951 = 3400427) B3400427
theorem B2550325 : Blo 2265435 2550325 := bbase (se 5 (by rfl) ⟨119546, by rfl⟩ : syracuseStep 2550325 = 239093) (by norm_num)
theorem B3400433 : Blo 2265435 3400433 := bstep (se 2 (by rfl) ⟨1275162, by rfl⟩ : syracuseStep 3400433 = 2550325) B2550325
theorem B2266955 : Blo 2265435 2266955 := bstep (se 1 (by rfl) ⟨1700216, by rfl⟩ : syracuseStep 2266955 = 3400433) B3400433
theorem B2869121 : Blo 2265435 2869121 := bbase (se 2 (by rfl) ⟨1075920, by rfl⟩ : syracuseStep 2869121 = 2151841) (by norm_num)
theorem B7650989 : Blo 2265435 7650989 := bstep (se 3 (by rfl) ⟨1434560, by rfl⟩ : syracuseStep 7650989 = 2869121) B2869121
theorem B5100659 : Blo 2265435 5100659 := bstep (se 1 (by rfl) ⟨3825494, by rfl⟩ : syracuseStep 5100659 = 7650989) B7650989
theorem B3400439 : Blo 2265435 3400439 := bstep (se 1 (by rfl) ⟨2550329, by rfl⟩ : syracuseStep 3400439 = 5100659) B5100659
theorem B2266959 : Blo 2265435 2266959 := bstep (se 1 (by rfl) ⟨1700219, by rfl⟩ : syracuseStep 2266959 = 3400439) B3400439
theorem B3400445 : Blo 2265435 3400445 := bbase (se 3 (by rfl) ⟨637583, by rfl⟩ : syracuseStep 3400445 = 1275167) (by norm_num)
theorem B2266963 : Blo 2265435 2266963 := bstep (se 1 (by rfl) ⟨1700222, by rfl⟩ : syracuseStep 2266963 = 3400445) B3400445
theorem B5100677 : Blo 2265435 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B3400451 : Blo 2265435 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B2266967 : Blo 2265435 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B4841669 : Blo 2265435 4841669 := bbase (se 4 (by rfl) ⟨453906, by rfl⟩ : syracuseStep 4841669 = 907813) (by norm_num)
theorem B3227779 : Blo 2265435 3227779 := bstep (se 1 (by rfl) ⟨2420834, by rfl⟩ : syracuseStep 3227779 = 4841669) B4841669
theorem B4303705 : Blo 2265435 4303705 := bstep (se 2 (by rfl) ⟨1613889, by rfl⟩ : syracuseStep 4303705 = 3227779) B3227779
theorem B5738273 : Blo 2265435 5738273 := bstep (se 2 (by rfl) ⟨2151852, by rfl⟩ : syracuseStep 5738273 = 4303705) B4303705
theorem B3825515 : Blo 2265435 3825515 := bstep (se 1 (by rfl) ⟨2869136, by rfl⟩ : syracuseStep 3825515 = 5738273) B5738273
theorem B2550343 : Blo 2265435 2550343 := bstep (se 1 (by rfl) ⟨1912757, by rfl⟩ : syracuseStep 2550343 = 3825515) B3825515
theorem B3400457 : Blo 2265435 3400457 := bstep (se 2 (by rfl) ⟨1275171, by rfl⟩ : syracuseStep 3400457 = 2550343) B2550343
theorem B2266971 : Blo 2265435 2266971 := bstep (se 1 (by rfl) ⟨1700228, by rfl⟩ : syracuseStep 2266971 = 3400457) B3400457
theorem B11476565 : Blo 2265435 11476565 := bbase (se 8 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 11476565 = 134491) (by norm_num)
theorem B7651043 : Blo 2265435 7651043 := bstep (se 1 (by rfl) ⟨5738282, by rfl⟩ : syracuseStep 7651043 = 11476565) B11476565
theorem B5100695 : Blo 2265435 5100695 := bstep (se 1 (by rfl) ⟨3825521, by rfl⟩ : syracuseStep 5100695 = 7651043) B7651043
theorem B3400463 : Blo 2265435 3400463 := bstep (se 1 (by rfl) ⟨2550347, by rfl⟩ : syracuseStep 3400463 = 5100695) B5100695
theorem B2266975 : Blo 2265435 2266975 := bstep (se 1 (by rfl) ⟨1700231, by rfl⟩ : syracuseStep 2266975 = 3400463) B3400463
theorem B3400469 : Blo 2265435 3400469 := bbase (se 6 (by rfl) ⟨79698, by rfl⟩ : syracuseStep 3400469 = 159397) (by norm_num)
theorem B2266979 : Blo 2265435 2266979 := bstep (se 1 (by rfl) ⟨1700234, by rfl⟩ : syracuseStep 2266979 = 3400469) B3400469
theorem B2585153 : Blo 2265435 2585153 := bbase (se 2 (by rfl) ⟨969432, by rfl⟩ : syracuseStep 2585153 = 1938865) (by norm_num)
theorem B6893741 : Blo 2265435 6893741 := bstep (se 3 (by rfl) ⟨1292576, by rfl⟩ : syracuseStep 6893741 = 2585153) B2585153
theorem B4595827 : Blo 2265435 4595827 := bstep (se 1 (by rfl) ⟨3446870, by rfl⟩ : syracuseStep 4595827 = 6893741) B6893741
theorem B6127769 : Blo 2265435 6127769 := bstep (se 2 (by rfl) ⟨2297913, by rfl⟩ : syracuseStep 6127769 = 4595827) B4595827
theorem B16340717 : Blo 2265435 16340717 := bstep (se 3 (by rfl) ⟨3063884, by rfl⟩ : syracuseStep 16340717 = 6127769) B6127769
theorem B43575245 : Blo 2265435 43575245 := bstep (se 3 (by rfl) ⟨8170358, by rfl⟩ : syracuseStep 43575245 = 16340717) B16340717
theorem B29050163 : Blo 2265435 29050163 := bstep (se 1 (by rfl) ⟨21787622, by rfl⟩ : syracuseStep 29050163 = 43575245) B43575245
theorem B19366775 : Blo 2265435 19366775 := bstep (se 1 (by rfl) ⟨14525081, by rfl⟩ : syracuseStep 19366775 = 29050163) B29050163
theorem B12911183 : Blo 2265435 12911183 := bstep (se 1 (by rfl) ⟨9683387, by rfl⟩ : syracuseStep 12911183 = 19366775) B19366775
theorem B8607455 : Blo 2265435 8607455 := bstep (se 1 (by rfl) ⟨6455591, by rfl⟩ : syracuseStep 8607455 = 12911183) B12911183
theorem B5738303 : Blo 2265435 5738303 := bstep (se 1 (by rfl) ⟨4303727, by rfl⟩ : syracuseStep 5738303 = 8607455) B8607455
theorem B3825535 : Blo 2265435 3825535 := bstep (se 1 (by rfl) ⟨2869151, by rfl⟩ : syracuseStep 3825535 = 5738303) B5738303
theorem B5100713 : Blo 2265435 5100713 := bstep (se 2 (by rfl) ⟨1912767, by rfl⟩ : syracuseStep 5100713 = 3825535) B3825535
theorem B3400475 : Blo 2265435 3400475 := bstep (se 1 (by rfl) ⟨2550356, by rfl⟩ : syracuseStep 3400475 = 5100713) B5100713
theorem B2266983 : Blo 2265435 2266983 := bstep (se 1 (by rfl) ⟨1700237, by rfl⟩ : syracuseStep 2266983 = 3400475) B3400475
theorem B2550361 : Blo 2265435 2550361 := bbase (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) (by norm_num)
theorem B3400481 : Blo 2265435 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B2266987 : Blo 2265435 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B6211397 : Blo 2265435 6211397 := bbase (se 4 (by rfl) ⟨582318, by rfl⟩ : syracuseStep 6211397 = 1164637) (by norm_num)
theorem B4140931 : Blo 2265435 4140931 := bstep (se 1 (by rfl) ⟨3105698, by rfl⟩ : syracuseStep 4140931 = 6211397) B6211397
theorem B5521241 : Blo 2265435 5521241 := bstep (se 2 (by rfl) ⟨2070465, by rfl⟩ : syracuseStep 5521241 = 4140931) B4140931
theorem B14723309 : Blo 2265435 14723309 := bstep (se 3 (by rfl) ⟨2760620, by rfl⟩ : syracuseStep 14723309 = 5521241) B5521241
theorem B9815539 : Blo 2265435 9815539 := bstep (se 1 (by rfl) ⟨7361654, by rfl⟩ : syracuseStep 9815539 = 14723309) B14723309
theorem B13087385 : Blo 2265435 13087385 := bstep (se 2 (by rfl) ⟨4907769, by rfl⟩ : syracuseStep 13087385 = 9815539) B9815539
theorem B8724923 : Blo 2265435 8724923 := bstep (se 1 (by rfl) ⟨6543692, by rfl⟩ : syracuseStep 8724923 = 13087385) B13087385
theorem B5816615 : Blo 2265435 5816615 := bstep (se 1 (by rfl) ⟨4362461, by rfl⟩ : syracuseStep 5816615 = 8724923) B8724923
theorem B62043893 : Blo 2265435 62043893 := bstep (se 5 (by rfl) ⟨2908307, by rfl⟩ : syracuseStep 62043893 = 5816615) B5816615
theorem B41362595 : Blo 2265435 41362595 := bstep (se 1 (by rfl) ⟨31021946, by rfl⟩ : syracuseStep 41362595 = 62043893) B62043893
theorem B27575063 : Blo 2265435 27575063 := bstep (se 1 (by rfl) ⟨20681297, by rfl⟩ : syracuseStep 27575063 = 41362595) B41362595
theorem B18383375 : Blo 2265435 18383375 := bstep (se 1 (by rfl) ⟨13787531, by rfl⟩ : syracuseStep 18383375 = 27575063) B27575063
theorem B12255583 : Blo 2265435 12255583 := bstep (se 1 (by rfl) ⟨9191687, by rfl⟩ : syracuseStep 12255583 = 18383375) B18383375
theorem B16340777 : Blo 2265435 16340777 := bstep (se 2 (by rfl) ⟨6127791, by rfl⟩ : syracuseStep 16340777 = 12255583) B12255583
theorem B10893851 : Blo 2265435 10893851 := bstep (se 1 (by rfl) ⟨8170388, by rfl⟩ : syracuseStep 10893851 = 16340777) B16340777
theorem B7262567 : Blo 2265435 7262567 := bstep (se 1 (by rfl) ⟨5446925, by rfl⟩ : syracuseStep 7262567 = 10893851) B10893851
theorem B4841711 : Blo 2265435 4841711 := bstep (se 1 (by rfl) ⟨3631283, by rfl⟩ : syracuseStep 4841711 = 7262567) B7262567
theorem B3227807 : Blo 2265435 3227807 := bstep (se 1 (by rfl) ⟨2420855, by rfl⟩ : syracuseStep 3227807 = 4841711) B4841711
theorem B8607485 : Blo 2265435 8607485 := bstep (se 3 (by rfl) ⟨1613903, by rfl⟩ : syracuseStep 8607485 = 3227807) B3227807
theorem B5738323 : Blo 2265435 5738323 := bstep (se 1 (by rfl) ⟨4303742, by rfl⟩ : syracuseStep 5738323 = 8607485) B8607485
theorem B7651097 : Blo 2265435 7651097 := bstep (se 2 (by rfl) ⟨2869161, by rfl⟩ : syracuseStep 7651097 = 5738323) B5738323
theorem B5100731 : Blo 2265435 5100731 := bstep (se 1 (by rfl) ⟨3825548, by rfl⟩ : syracuseStep 5100731 = 7651097) B7651097
theorem B3400487 : Blo 2265435 3400487 := bstep (se 1 (by rfl) ⟨2550365, by rfl⟩ : syracuseStep 3400487 = 5100731) B5100731
theorem B2266991 : Blo 2265435 2266991 := bstep (se 1 (by rfl) ⟨1700243, by rfl⟩ : syracuseStep 2266991 = 3400487) B3400487
theorem B3400493 : Blo 2265435 3400493 := bbase (se 3 (by rfl) ⟨637592, by rfl⟩ : syracuseStep 3400493 = 1275185) (by norm_num)
theorem B2266995 : Blo 2265435 2266995 := bstep (se 1 (by rfl) ⟨1700246, by rfl⟩ : syracuseStep 2266995 = 3400493) B3400493
theorem B5100749 : Blo 2265435 5100749 := bbase (se 3 (by rfl) ⟨956390, by rfl⟩ : syracuseStep 5100749 = 1912781) (by norm_num)
theorem B3400499 : Blo 2265435 3400499 := bstep (se 1 (by rfl) ⟨2550374, by rfl⟩ : syracuseStep 3400499 = 5100749) B5100749
theorem B2266999 : Blo 2265435 2266999 := bstep (se 1 (by rfl) ⟨1700249, by rfl⟩ : syracuseStep 2266999 = 3400499) B3400499
theorem B2869177 : Blo 2265435 2869177 := bbase (se 2 (by rfl) ⟨1075941, by rfl⟩ : syracuseStep 2869177 = 2151883) (by norm_num)
theorem B3825569 : Blo 2265435 3825569 := bstep (se 2 (by rfl) ⟨1434588, by rfl⟩ : syracuseStep 3825569 = 2869177) B2869177
theorem B2550379 : Blo 2265435 2550379 := bstep (se 1 (by rfl) ⟨1912784, by rfl⟩ : syracuseStep 2550379 = 3825569) B3825569
theorem B3400505 : Blo 2265435 3400505 := bstep (se 2 (by rfl) ⟨1275189, by rfl⟩ : syracuseStep 3400505 = 2550379) B2550379
theorem B2267003 : Blo 2265435 2267003 := bstep (se 1 (by rfl) ⟨1700252, by rfl⟩ : syracuseStep 2267003 = 3400505) B3400505
theorem B3063917 : Blo 2265435 3063917 := bbase (se 3 (by rfl) ⟨574484, by rfl⟩ : syracuseStep 3063917 = 1148969) (by norm_num)
theorem B8170445 : Blo 2265435 8170445 := bstep (se 3 (by rfl) ⟨1531958, by rfl⟩ : syracuseStep 8170445 = 3063917) B3063917
theorem B5446963 : Blo 2265435 5446963 := bstep (se 1 (by rfl) ⟨4085222, by rfl⟩ : syracuseStep 5446963 = 8170445) B8170445
theorem B7262617 : Blo 2265435 7262617 := bstep (se 2 (by rfl) ⟨2723481, by rfl⟩ : syracuseStep 7262617 = 5446963) B5446963
theorem B9683489 : Blo 2265435 9683489 := bstep (se 2 (by rfl) ⟨3631308, by rfl⟩ : syracuseStep 9683489 = 7262617) B7262617
theorem B25822637 : Blo 2265435 25822637 := bstep (se 3 (by rfl) ⟨4841744, by rfl⟩ : syracuseStep 25822637 = 9683489) B9683489
theorem B17215091 : Blo 2265435 17215091 := bstep (se 1 (by rfl) ⟨12911318, by rfl⟩ : syracuseStep 17215091 = 25822637) B25822637
theorem B11476727 : Blo 2265435 11476727 := bstep (se 1 (by rfl) ⟨8607545, by rfl⟩ : syracuseStep 11476727 = 17215091) B17215091
theorem B7651151 : Blo 2265435 7651151 := bstep (se 1 (by rfl) ⟨5738363, by rfl⟩ : syracuseStep 7651151 = 11476727) B11476727
theorem B5100767 : Blo 2265435 5100767 := bstep (se 1 (by rfl) ⟨3825575, by rfl⟩ : syracuseStep 5100767 = 7651151) B7651151
theorem B3400511 : Blo 2265435 3400511 := bstep (se 1 (by rfl) ⟨2550383, by rfl⟩ : syracuseStep 3400511 = 5100767) B5100767
theorem B2267007 : Blo 2265435 2267007 := bstep (se 1 (by rfl) ⟨1700255, by rfl⟩ : syracuseStep 2267007 = 3400511) B3400511
theorem B3400517 : Blo 2265435 3400517 := bbase (se 4 (by rfl) ⟨318798, by rfl⟩ : syracuseStep 3400517 = 637597) (by norm_num)
theorem B2267011 : Blo 2265435 2267011 := bstep (se 1 (by rfl) ⟨1700258, by rfl⟩ : syracuseStep 2267011 = 3400517) B3400517
theorem B3825589 : Blo 2265435 3825589 := bbase (se 5 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 3825589 = 358649) (by norm_num)
theorem B5100785 : Blo 2265435 5100785 := bstep (se 2 (by rfl) ⟨1912794, by rfl⟩ : syracuseStep 5100785 = 3825589) B3825589
theorem B3400523 : Blo 2265435 3400523 := bstep (se 1 (by rfl) ⟨2550392, by rfl⟩ : syracuseStep 3400523 = 5100785) B5100785
theorem B2267015 : Blo 2265435 2267015 := bstep (se 1 (by rfl) ⟨1700261, by rfl⟩ : syracuseStep 2267015 = 3400523) B3400523
theorem B2550397 : Blo 2265435 2550397 := bbase (se 3 (by rfl) ⟨478199, by rfl⟩ : syracuseStep 2550397 = 956399) (by norm_num)
theorem B3400529 : Blo 2265435 3400529 := bstep (se 2 (by rfl) ⟨1275198, by rfl⟩ : syracuseStep 3400529 = 2550397) B2550397
theorem B2267019 : Blo 2265435 2267019 := bstep (se 1 (by rfl) ⟨1700264, by rfl⟩ : syracuseStep 2267019 = 3400529) B3400529
theorem B7651205 : Blo 2265435 7651205 := bbase (se 4 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 7651205 = 1434601) (by norm_num)
theorem B5100803 : Blo 2265435 5100803 := bstep (se 1 (by rfl) ⟨3825602, by rfl⟩ : syracuseStep 5100803 = 7651205) B7651205
theorem B3400535 : Blo 2265435 3400535 := bstep (se 1 (by rfl) ⟨2550401, by rfl⟩ : syracuseStep 3400535 = 5100803) B5100803
theorem B2267023 : Blo 2265435 2267023 := bstep (se 1 (by rfl) ⟨1700267, by rfl⟩ : syracuseStep 2267023 = 3400535) B3400535
theorem B3400541 : Blo 2265435 3400541 := bbase (se 3 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 3400541 = 1275203) (by norm_num)
theorem B2267027 : Blo 2265435 2267027 := bstep (se 1 (by rfl) ⟨1700270, by rfl⟩ : syracuseStep 2267027 = 3400541) B3400541
theorem B5100821 : Blo 2265435 5100821 := bbase (se 6 (by rfl) ⟨119550, by rfl⟩ : syracuseStep 5100821 = 239101) (by norm_num)
theorem B3400547 : Blo 2265435 3400547 := bstep (se 1 (by rfl) ⟨2550410, by rfl⟩ : syracuseStep 3400547 = 5100821) B5100821
theorem B2267031 : Blo 2265435 2267031 := bstep (se 1 (by rfl) ⟨1700273, by rfl⟩ : syracuseStep 2267031 = 3400547) B3400547
theorem B8607653 : Blo 2265435 8607653 := bbase (se 4 (by rfl) ⟨806967, by rfl⟩ : syracuseStep 8607653 = 1613935) (by norm_num)
theorem B5738435 : Blo 2265435 5738435 := bstep (se 1 (by rfl) ⟨4303826, by rfl⟩ : syracuseStep 5738435 = 8607653) B8607653
theorem B3825623 : Blo 2265435 3825623 := bstep (se 1 (by rfl) ⟨2869217, by rfl⟩ : syracuseStep 3825623 = 5738435) B5738435
theorem B2550415 : Blo 2265435 2550415 := bstep (se 1 (by rfl) ⟨1912811, by rfl⟩ : syracuseStep 2550415 = 3825623) B3825623
theorem B3400553 : Blo 2265435 3400553 := bstep (se 2 (by rfl) ⟨1275207, by rfl⟩ : syracuseStep 3400553 = 2550415) B2550415
theorem B2267035 : Blo 2265435 2267035 := bstep (se 1 (by rfl) ⟨1700276, by rfl⟩ : syracuseStep 2267035 = 3400553) B3400553
theorem B4841813 : Blo 2265435 4841813 := bbase (se 10 (by rfl) ⟨7092, by rfl⟩ : syracuseStep 4841813 = 14185) (by norm_num)
theorem B12911501 : Blo 2265435 12911501 := bstep (se 3 (by rfl) ⟨2420906, by rfl⟩ : syracuseStep 12911501 = 4841813) B4841813
theorem B8607667 : Blo 2265435 8607667 := bstep (se 1 (by rfl) ⟨6455750, by rfl⟩ : syracuseStep 8607667 = 12911501) B12911501
theorem B11476889 : Blo 2265435 11476889 := bstep (se 2 (by rfl) ⟨4303833, by rfl⟩ : syracuseStep 11476889 = 8607667) B8607667
theorem B7651259 : Blo 2265435 7651259 := bstep (se 1 (by rfl) ⟨5738444, by rfl⟩ : syracuseStep 7651259 = 11476889) B11476889
theorem B5100839 : Blo 2265435 5100839 := bstep (se 1 (by rfl) ⟨3825629, by rfl⟩ : syracuseStep 5100839 = 7651259) B7651259
theorem B3400559 : Blo 2265435 3400559 := bstep (se 1 (by rfl) ⟨2550419, by rfl⟩ : syracuseStep 3400559 = 5100839) B5100839
theorem B2267039 : Blo 2265435 2267039 := bstep (se 1 (by rfl) ⟨1700279, by rfl⟩ : syracuseStep 2267039 = 3400559) B3400559
theorem B3400565 : Blo 2265435 3400565 := bbase (se 5 (by rfl) ⟨159401, by rfl⟩ : syracuseStep 3400565 = 318803) (by norm_num)
theorem B2267043 : Blo 2265435 2267043 := bstep (se 1 (by rfl) ⟨1700282, by rfl⟩ : syracuseStep 2267043 = 3400565) B3400565
theorem B4974853 : Blo 2265435 4974853 := bbase (se 4 (by rfl) ⟨466392, by rfl⟩ : syracuseStep 4974853 = 932785) (by norm_num)
theorem B6633137 : Blo 2265435 6633137 := bstep (se 2 (by rfl) ⟨2487426, by rfl⟩ : syracuseStep 6633137 = 4974853) B4974853
theorem B17688365 : Blo 2265435 17688365 := bstep (se 3 (by rfl) ⟨3316568, by rfl⟩ : syracuseStep 17688365 = 6633137) B6633137
theorem B11792243 : Blo 2265435 11792243 := bstep (se 1 (by rfl) ⟨8844182, by rfl⟩ : syracuseStep 11792243 = 17688365) B17688365
theorem B7861495 : Blo 2265435 7861495 := bstep (se 1 (by rfl) ⟨5896121, by rfl⟩ : syracuseStep 7861495 = 11792243) B11792243
theorem B10481993 : Blo 2265435 10481993 := bstep (se 2 (by rfl) ⟨3930747, by rfl⟩ : syracuseStep 10481993 = 7861495) B7861495
theorem B6987995 : Blo 2265435 6987995 := bstep (se 1 (by rfl) ⟨5240996, by rfl⟩ : syracuseStep 6987995 = 10481993) B10481993
theorem B4658663 : Blo 2265435 4658663 := bstep (se 1 (by rfl) ⟨3493997, by rfl⟩ : syracuseStep 4658663 = 6987995) B6987995
theorem B3105775 : Blo 2265435 3105775 := bstep (se 1 (by rfl) ⟨2329331, by rfl⟩ : syracuseStep 3105775 = 4658663) B4658663
theorem B16564133 : Blo 2265435 16564133 := bstep (se 4 (by rfl) ⟨1552887, by rfl⟩ : syracuseStep 16564133 = 3105775) B3105775
theorem B44171021 : Blo 2265435 44171021 := bstep (se 3 (by rfl) ⟨8282066, by rfl⟩ : syracuseStep 44171021 = 16564133) B16564133
theorem B29447347 : Blo 2265435 29447347 := bstep (se 1 (by rfl) ⟨22085510, by rfl⟩ : syracuseStep 29447347 = 44171021) B44171021
theorem B39263129 : Blo 2265435 39263129 := bstep (se 2 (by rfl) ⟨14723673, by rfl⟩ : syracuseStep 39263129 = 29447347) B29447347
theorem B26175419 : Blo 2265435 26175419 := bstep (se 1 (by rfl) ⟨19631564, by rfl⟩ : syracuseStep 26175419 = 39263129) B39263129
theorem B17450279 : Blo 2265435 17450279 := bstep (se 1 (by rfl) ⟨13087709, by rfl⟩ : syracuseStep 17450279 = 26175419) B26175419
theorem B11633519 : Blo 2265435 11633519 := bstep (se 1 (by rfl) ⟨8725139, by rfl⟩ : syracuseStep 11633519 = 17450279) B17450279
theorem B7755679 : Blo 2265435 7755679 := bstep (se 1 (by rfl) ⟨5816759, by rfl⟩ : syracuseStep 7755679 = 11633519) B11633519
theorem B41363621 : Blo 2265435 41363621 := bstep (se 4 (by rfl) ⟨3877839, by rfl⟩ : syracuseStep 41363621 = 7755679) B7755679
theorem B27575747 : Blo 2265435 27575747 := bstep (se 1 (by rfl) ⟨20681810, by rfl⟩ : syracuseStep 27575747 = 41363621) B41363621
theorem B18383831 : Blo 2265435 18383831 := bstep (se 1 (by rfl) ⟨13787873, by rfl⟩ : syracuseStep 18383831 = 27575747) B27575747
theorem B12255887 : Blo 2265435 12255887 := bstep (se 1 (by rfl) ⟨9191915, by rfl⟩ : syracuseStep 12255887 = 18383831) B18383831
theorem B8170591 : Blo 2265435 8170591 := bstep (se 1 (by rfl) ⟨6127943, by rfl⟩ : syracuseStep 8170591 = 12255887) B12255887
theorem B10894121 : Blo 2265435 10894121 := bstep (se 2 (by rfl) ⟨4085295, by rfl⟩ : syracuseStep 10894121 = 8170591) B8170591
theorem B7262747 : Blo 2265435 7262747 := bstep (se 1 (by rfl) ⟨5447060, by rfl⟩ : syracuseStep 7262747 = 10894121) B10894121
theorem B4841831 : Blo 2265435 4841831 := bstep (se 1 (by rfl) ⟨3631373, by rfl⟩ : syracuseStep 4841831 = 7262747) B7262747
theorem B3227887 : Blo 2265435 3227887 := bstep (se 1 (by rfl) ⟨2420915, by rfl⟩ : syracuseStep 3227887 = 4841831) B4841831
theorem B4303849 : Blo 2265435 4303849 := bstep (se 2 (by rfl) ⟨1613943, by rfl⟩ : syracuseStep 4303849 = 3227887) B3227887
theorem B5738465 : Blo 2265435 5738465 := bstep (se 2 (by rfl) ⟨2151924, by rfl⟩ : syracuseStep 5738465 = 4303849) B4303849
theorem B3825643 : Blo 2265435 3825643 := bstep (se 1 (by rfl) ⟨2869232, by rfl⟩ : syracuseStep 3825643 = 5738465) B5738465
theorem B5100857 : Blo 2265435 5100857 := bstep (se 2 (by rfl) ⟨1912821, by rfl⟩ : syracuseStep 5100857 = 3825643) B3825643
theorem B3400571 : Blo 2265435 3400571 := bstep (se 1 (by rfl) ⟨2550428, by rfl⟩ : syracuseStep 3400571 = 5100857) B5100857
theorem B2267047 : Blo 2265435 2267047 := bstep (se 1 (by rfl) ⟨1700285, by rfl⟩ : syracuseStep 2267047 = 3400571) B3400571
theorem B2550433 : Blo 2265435 2550433 := bbase (se 2 (by rfl) ⟨956412, by rfl⟩ : syracuseStep 2550433 = 1912825) (by norm_num)
theorem B3400577 : Blo 2265435 3400577 := bstep (se 2 (by rfl) ⟨1275216, by rfl⟩ : syracuseStep 3400577 = 2550433) B2550433
theorem B2267051 : Blo 2265435 2267051 := bstep (se 1 (by rfl) ⟨1700288, by rfl⟩ : syracuseStep 2267051 = 3400577) B3400577
theorem B5738485 : Blo 2265435 5738485 := bbase (se 5 (by rfl) ⟨268991, by rfl⟩ : syracuseStep 5738485 = 537983) (by norm_num)
theorem B7651313 : Blo 2265435 7651313 := bstep (se 2 (by rfl) ⟨2869242, by rfl⟩ : syracuseStep 7651313 = 5738485) B5738485
theorem B5100875 : Blo 2265435 5100875 := bstep (se 1 (by rfl) ⟨3825656, by rfl⟩ : syracuseStep 5100875 = 7651313) B7651313
theorem B3400583 : Blo 2265435 3400583 := bstep (se 1 (by rfl) ⟨2550437, by rfl⟩ : syracuseStep 3400583 = 5100875) B5100875
theorem B2267055 : Blo 2265435 2267055 := bstep (se 1 (by rfl) ⟨1700291, by rfl⟩ : syracuseStep 2267055 = 3400583) B3400583
theorem B3400589 : Blo 2265435 3400589 := bbase (se 3 (by rfl) ⟨637610, by rfl⟩ : syracuseStep 3400589 = 1275221) (by norm_num)
theorem B2267059 : Blo 2265435 2267059 := bstep (se 1 (by rfl) ⟨1700294, by rfl⟩ : syracuseStep 2267059 = 3400589) B3400589
theorem B5100893 : Blo 2265435 5100893 := bbase (se 3 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 5100893 = 1912835) (by norm_num)
theorem B3400595 : Blo 2265435 3400595 := bstep (se 1 (by rfl) ⟨2550446, by rfl⟩ : syracuseStep 3400595 = 5100893) B5100893
theorem B2267063 : Blo 2265435 2267063 := bstep (se 1 (by rfl) ⟨1700297, by rfl⟩ : syracuseStep 2267063 = 3400595) B3400595
theorem B3825677 : Blo 2265435 3825677 := bbase (se 3 (by rfl) ⟨717314, by rfl⟩ : syracuseStep 3825677 = 1434629) (by norm_num)
theorem B2550451 : Blo 2265435 2550451 := bstep (se 1 (by rfl) ⟨1912838, by rfl⟩ : syracuseStep 2550451 = 3825677) B3825677
theorem B3400601 : Blo 2265435 3400601 := bstep (se 2 (by rfl) ⟨1275225, by rfl⟩ : syracuseStep 3400601 = 2550451) B2550451
theorem B2267067 : Blo 2265435 2267067 := bstep (se 1 (by rfl) ⟨1700300, by rfl⟩ : syracuseStep 2267067 = 3400601) B3400601
theorem B5447117 : Blo 2265435 5447117 := bbase (se 3 (by rfl) ⟨1021334, by rfl⟩ : syracuseStep 5447117 = 2042669) (by norm_num)
theorem B3631411 : Blo 2265435 3631411 := bstep (se 1 (by rfl) ⟨2723558, by rfl⟩ : syracuseStep 3631411 = 5447117) B5447117
theorem B19367525 : Blo 2265435 19367525 := bstep (se 4 (by rfl) ⟨1815705, by rfl⟩ : syracuseStep 19367525 = 3631411) B3631411
theorem B12911683 : Blo 2265435 12911683 := bstep (se 1 (by rfl) ⟨9683762, by rfl⟩ : syracuseStep 12911683 = 19367525) B19367525
theorem B17215577 : Blo 2265435 17215577 := bstep (se 2 (by rfl) ⟨6455841, by rfl⟩ : syracuseStep 17215577 = 12911683) B12911683
theorem B11477051 : Blo 2265435 11477051 := bstep (se 1 (by rfl) ⟨8607788, by rfl⟩ : syracuseStep 11477051 = 17215577) B17215577
theorem B7651367 : Blo 2265435 7651367 := bstep (se 1 (by rfl) ⟨5738525, by rfl⟩ : syracuseStep 7651367 = 11477051) B11477051
theorem B5100911 : Blo 2265435 5100911 := bstep (se 1 (by rfl) ⟨3825683, by rfl⟩ : syracuseStep 5100911 = 7651367) B7651367
theorem B3400607 : Blo 2265435 3400607 := bstep (se 1 (by rfl) ⟨2550455, by rfl⟩ : syracuseStep 3400607 = 5100911) B5100911
theorem B2267071 : Blo 2265435 2267071 := bstep (se 1 (by rfl) ⟨1700303, by rfl⟩ : syracuseStep 2267071 = 3400607) B3400607
theorem B3400613 : Blo 2265435 3400613 := bbase (se 4 (by rfl) ⟨318807, by rfl⟩ : syracuseStep 3400613 = 637615) (by norm_num)
theorem B2267075 : Blo 2265435 2267075 := bstep (se 1 (by rfl) ⟨1700306, by rfl⟩ : syracuseStep 2267075 = 3400613) B3400613
theorem B2869273 : Blo 2265435 2869273 := bbase (se 2 (by rfl) ⟨1075977, by rfl⟩ : syracuseStep 2869273 = 2151955) (by norm_num)
theorem B3825697 : Blo 2265435 3825697 := bstep (se 2 (by rfl) ⟨1434636, by rfl⟩ : syracuseStep 3825697 = 2869273) B2869273
theorem B5100929 : Blo 2265435 5100929 := bstep (se 2 (by rfl) ⟨1912848, by rfl⟩ : syracuseStep 5100929 = 3825697) B3825697
theorem B3400619 : Blo 2265435 3400619 := bstep (se 1 (by rfl) ⟨2550464, by rfl⟩ : syracuseStep 3400619 = 5100929) B5100929
theorem B2267079 : Blo 2265435 2267079 := bstep (se 1 (by rfl) ⟨1700309, by rfl⟩ : syracuseStep 2267079 = 3400619) B3400619
theorem B2550469 : Blo 2265435 2550469 := bbase (se 4 (by rfl) ⟨239106, by rfl⟩ : syracuseStep 2550469 = 478213) (by norm_num)
theorem B3400625 : Blo 2265435 3400625 := bstep (se 2 (by rfl) ⟨1275234, by rfl⟩ : syracuseStep 3400625 = 2550469) B2550469
theorem B2267083 : Blo 2265435 2267083 := bstep (se 1 (by rfl) ⟨1700312, by rfl⟩ : syracuseStep 2267083 = 3400625) B3400625
theorem B4303925 : Blo 2265435 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B2869283 : Blo 2265435 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B7651421 : Blo 2265435 7651421 := bstep (se 3 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 7651421 = 2869283) B2869283
theorem B5100947 : Blo 2265435 5100947 := bstep (se 1 (by rfl) ⟨3825710, by rfl⟩ : syracuseStep 5100947 = 7651421) B7651421
theorem B3400631 : Blo 2265435 3400631 := bstep (se 1 (by rfl) ⟨2550473, by rfl⟩ : syracuseStep 3400631 = 5100947) B5100947
theorem B2267087 : Blo 2265435 2267087 := bstep (se 1 (by rfl) ⟨1700315, by rfl⟩ : syracuseStep 2267087 = 3400631) B3400631
theorem B3400637 : Blo 2265435 3400637 := bbase (se 3 (by rfl) ⟨637619, by rfl⟩ : syracuseStep 3400637 = 1275239) (by norm_num)
theorem B2267091 : Blo 2265435 2267091 := bstep (se 1 (by rfl) ⟨1700318, by rfl⟩ : syracuseStep 2267091 = 3400637) B3400637
theorem B5100965 : Blo 2265435 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B3400643 : Blo 2265435 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B2267095 : Blo 2265435 2267095 := bstep (se 1 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 2267095 = 3400643) B3400643
theorem B5738597 : Blo 2265435 5738597 := bbase (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) (by norm_num)
theorem B3825731 : Blo 2265435 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B2550487 : Blo 2265435 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B3400649 : Blo 2265435 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B2267099 : Blo 2265435 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B11043029 : Blo 2265435 11043029 := bbase (se 7 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 11043029 = 258821) (by norm_num)
theorem B7362019 : Blo 2265435 7362019 := bstep (se 1 (by rfl) ⟨5521514, by rfl⟩ : syracuseStep 7362019 = 11043029) B11043029
theorem B39264101 : Blo 2265435 39264101 := bstep (se 4 (by rfl) ⟨3681009, by rfl⟩ : syracuseStep 39264101 = 7362019) B7362019
theorem B26176067 : Blo 2265435 26176067 := bstep (se 1 (by rfl) ⟨19632050, by rfl⟩ : syracuseStep 26176067 = 39264101) B39264101
theorem B17450711 : Blo 2265435 17450711 := bstep (se 1 (by rfl) ⟨13088033, by rfl⟩ : syracuseStep 17450711 = 26176067) B26176067
theorem B11633807 : Blo 2265435 11633807 := bstep (se 1 (by rfl) ⟨8725355, by rfl⟩ : syracuseStep 11633807 = 17450711) B17450711
theorem B31023485 : Blo 2265435 31023485 := bstep (se 3 (by rfl) ⟨5816903, by rfl⟩ : syracuseStep 31023485 = 11633807) B11633807
theorem B20682323 : Blo 2265435 20682323 := bstep (se 1 (by rfl) ⟨15511742, by rfl⟩ : syracuseStep 20682323 = 31023485) B31023485
theorem B13788215 : Blo 2265435 13788215 := bstep (se 1 (by rfl) ⟨10341161, by rfl⟩ : syracuseStep 13788215 = 20682323) B20682323
theorem B9192143 : Blo 2265435 9192143 := bstep (se 1 (by rfl) ⟨6894107, by rfl⟩ : syracuseStep 9192143 = 13788215) B13788215
theorem B6128095 : Blo 2265435 6128095 := bstep (se 1 (by rfl) ⟨4596071, by rfl⟩ : syracuseStep 6128095 = 9192143) B9192143
theorem B8170793 : Blo 2265435 8170793 := bstep (se 2 (by rfl) ⟨3064047, by rfl⟩ : syracuseStep 8170793 = 6128095) B6128095
theorem B5447195 : Blo 2265435 5447195 := bstep (se 1 (by rfl) ⟨4085396, by rfl⟩ : syracuseStep 5447195 = 8170793) B8170793
theorem B3631463 : Blo 2265435 3631463 := bstep (se 1 (by rfl) ⟨2723597, by rfl⟩ : syracuseStep 3631463 = 5447195) B5447195
theorem B2420975 : Blo 2265435 2420975 := bstep (se 1 (by rfl) ⟨1815731, by rfl⟩ : syracuseStep 2420975 = 3631463) B3631463
theorem B6455933 : Blo 2265435 6455933 := bstep (se 3 (by rfl) ⟨1210487, by rfl⟩ : syracuseStep 6455933 = 2420975) B2420975
theorem B4303955 : Blo 2265435 4303955 := bstep (se 1 (by rfl) ⟨3227966, by rfl⟩ : syracuseStep 4303955 = 6455933) B6455933
theorem B11477213 : Blo 2265435 11477213 := bstep (se 3 (by rfl) ⟨2151977, by rfl⟩ : syracuseStep 11477213 = 4303955) B4303955
theorem B7651475 : Blo 2265435 7651475 := bstep (se 1 (by rfl) ⟨5738606, by rfl⟩ : syracuseStep 7651475 = 11477213) B11477213
theorem B5100983 : Blo 2265435 5100983 := bstep (se 1 (by rfl) ⟨3825737, by rfl⟩ : syracuseStep 5100983 = 7651475) B7651475
theorem B3400655 : Blo 2265435 3400655 := bstep (se 1 (by rfl) ⟨2550491, by rfl⟩ : syracuseStep 3400655 = 5100983) B5100983
theorem B2267103 : Blo 2265435 2267103 := bstep (se 1 (by rfl) ⟨1700327, by rfl⟩ : syracuseStep 2267103 = 3400655) B3400655
theorem B3400661 : Blo 2265435 3400661 := bbase (se 7 (by rfl) ⟨39851, by rfl⟩ : syracuseStep 3400661 = 79703) (by norm_num)
theorem B2267107 : Blo 2265435 2267107 := bstep (se 1 (by rfl) ⟨1700330, by rfl⟩ : syracuseStep 2267107 = 3400661) B3400661
theorem B8607941 : Blo 2265435 8607941 := bbase (se 4 (by rfl) ⟨806994, by rfl⟩ : syracuseStep 8607941 = 1613989) (by norm_num)
theorem B5738627 : Blo 2265435 5738627 := bstep (se 1 (by rfl) ⟨4303970, by rfl⟩ : syracuseStep 5738627 = 8607941) B8607941
theorem B3825751 : Blo 2265435 3825751 := bstep (se 1 (by rfl) ⟨2869313, by rfl⟩ : syracuseStep 3825751 = 5738627) B5738627
theorem B5101001 : Blo 2265435 5101001 := bstep (se 2 (by rfl) ⟨1912875, by rfl⟩ : syracuseStep 5101001 = 3825751) B3825751
theorem B3400667 : Blo 2265435 3400667 := bstep (se 1 (by rfl) ⟨2550500, by rfl⟩ : syracuseStep 3400667 = 5101001) B5101001
theorem B2267111 : Blo 2265435 2267111 := bstep (se 1 (by rfl) ⟨1700333, by rfl⟩ : syracuseStep 2267111 = 3400667) B3400667
theorem B2550505 : Blo 2265435 2550505 := bbase (se 2 (by rfl) ⟨956439, by rfl⟩ : syracuseStep 2550505 = 1912879) (by norm_num)
theorem B3400673 : Blo 2265435 3400673 := bstep (se 2 (by rfl) ⟨1275252, by rfl⟩ : syracuseStep 3400673 = 2550505) B2550505
theorem B2267115 : Blo 2265435 2267115 := bstep (se 1 (by rfl) ⟨1700336, by rfl⟩ : syracuseStep 2267115 = 3400673) B3400673
theorem B12911957 : Blo 2265435 12911957 := bbase (se 12 (by rfl) ⟨4728, by rfl⟩ : syracuseStep 12911957 = 9457) (by norm_num)
theorem B8607971 : Blo 2265435 8607971 := bstep (se 1 (by rfl) ⟨6455978, by rfl⟩ : syracuseStep 8607971 = 12911957) B12911957
theorem B5738647 : Blo 2265435 5738647 := bstep (se 1 (by rfl) ⟨4303985, by rfl⟩ : syracuseStep 5738647 = 8607971) B8607971
theorem B7651529 : Blo 2265435 7651529 := bstep (se 2 (by rfl) ⟨2869323, by rfl⟩ : syracuseStep 7651529 = 5738647) B5738647
theorem B5101019 : Blo 2265435 5101019 := bstep (se 1 (by rfl) ⟨3825764, by rfl⟩ : syracuseStep 5101019 = 7651529) B7651529
theorem B3400679 : Blo 2265435 3400679 := bstep (se 1 (by rfl) ⟨2550509, by rfl⟩ : syracuseStep 3400679 = 5101019) B5101019
theorem B2267119 : Blo 2265435 2267119 := bstep (se 1 (by rfl) ⟨1700339, by rfl⟩ : syracuseStep 2267119 = 3400679) B3400679
theorem B3400685 : Blo 2265435 3400685 := bbase (se 3 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 3400685 = 1275257) (by norm_num)
theorem B2267123 : Blo 2265435 2267123 := bstep (se 1 (by rfl) ⟨1700342, by rfl⟩ : syracuseStep 2267123 = 3400685) B3400685
theorem B5101037 : Blo 2265435 5101037 := bbase (se 3 (by rfl) ⟨956444, by rfl⟩ : syracuseStep 5101037 = 1912889) (by norm_num)
theorem B3400691 : Blo 2265435 3400691 := bstep (se 1 (by rfl) ⟨2550518, by rfl⟩ : syracuseStep 3400691 = 5101037) B5101037
theorem B2267127 : Blo 2265435 2267127 := bstep (se 1 (by rfl) ⟨1700345, by rfl⟩ : syracuseStep 2267127 = 3400691) B3400691
theorem B5170645 : Blo 2265435 5170645 := bbase (se 7 (by rfl) ⟨60593, by rfl⟩ : syracuseStep 5170645 = 121187) (by norm_num)
theorem B27576773 : Blo 2265435 27576773 := bstep (se 4 (by rfl) ⟨2585322, by rfl⟩ : syracuseStep 27576773 = 5170645) B5170645
theorem B18384515 : Blo 2265435 18384515 := bstep (se 1 (by rfl) ⟨13788386, by rfl⟩ : syracuseStep 18384515 = 27576773) B27576773
theorem B12256343 : Blo 2265435 12256343 := bstep (se 1 (by rfl) ⟨9192257, by rfl⟩ : syracuseStep 12256343 = 18384515) B18384515
theorem B8170895 : Blo 2265435 8170895 := bstep (se 1 (by rfl) ⟨6128171, by rfl⟩ : syracuseStep 8170895 = 12256343) B12256343
theorem B5447263 : Blo 2265435 5447263 := bstep (se 1 (by rfl) ⟨4085447, by rfl⟩ : syracuseStep 5447263 = 8170895) B8170895
theorem B7263017 : Blo 2265435 7263017 := bstep (se 2 (by rfl) ⟨2723631, by rfl⟩ : syracuseStep 7263017 = 5447263) B5447263
theorem B4842011 : Blo 2265435 4842011 := bstep (se 1 (by rfl) ⟨3631508, by rfl⟩ : syracuseStep 4842011 = 7263017) B7263017
theorem B3228007 : Blo 2265435 3228007 := bstep (se 1 (by rfl) ⟨2421005, by rfl⟩ : syracuseStep 3228007 = 4842011) B4842011
theorem B4304009 : Blo 2265435 4304009 := bstep (se 2 (by rfl) ⟨1614003, by rfl⟩ : syracuseStep 4304009 = 3228007) B3228007
theorem B2869339 : Blo 2265435 2869339 := bstep (se 1 (by rfl) ⟨2152004, by rfl⟩ : syracuseStep 2869339 = 4304009) B4304009
theorem B3825785 : Blo 2265435 3825785 := bstep (se 2 (by rfl) ⟨1434669, by rfl⟩ : syracuseStep 3825785 = 2869339) B2869339
theorem B2550523 : Blo 2265435 2550523 := bstep (se 1 (by rfl) ⟨1912892, by rfl⟩ : syracuseStep 2550523 = 3825785) B3825785
theorem B3400697 : Blo 2265435 3400697 := bstep (se 2 (by rfl) ⟨1275261, by rfl⟩ : syracuseStep 3400697 = 2550523) B2550523
theorem B2267131 : Blo 2265435 2267131 := bstep (se 1 (by rfl) ⟨1700348, by rfl⟩ : syracuseStep 2267131 = 3400697) B3400697
theorem B3447101 : Blo 2265435 3447101 := bbase (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) (by norm_num)
theorem B9192269 : Blo 2265435 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B6128179 : Blo 2265435 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B130734485 : Blo 2265435 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B87156323 : Blo 2265435 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B58104215 : Blo 2265435 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B38736143 : Blo 2265435 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B25824095 : Blo 2265435 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B17216063 : Blo 2265435 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B11477375 : Blo 2265435 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B7651583 : Blo 2265435 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B5101055 : Blo 2265435 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B3400703 : Blo 2265435 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B2267135 : Blo 2265435 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B3400709 : Blo 2265435 3400709 := bbase (se 4 (by rfl) ⟨318816, by rfl⟩ : syracuseStep 3400709 = 637633) (by norm_num)
theorem B2267139 : Blo 2265435 2267139 := bstep (se 1 (by rfl) ⟨1700354, by rfl⟩ : syracuseStep 2267139 = 3400709) B3400709
theorem B3825805 : Blo 2265435 3825805 := bbase (se 3 (by rfl) ⟨717338, by rfl⟩ : syracuseStep 3825805 = 1434677) (by norm_num)
theorem B5101073 : Blo 2265435 5101073 := bstep (se 2 (by rfl) ⟨1912902, by rfl⟩ : syracuseStep 5101073 = 3825805) B3825805
theorem B3400715 : Blo 2265435 3400715 := bstep (se 1 (by rfl) ⟨2550536, by rfl⟩ : syracuseStep 3400715 = 5101073) B5101073
theorem B2267143 : Blo 2265435 2267143 := bstep (se 1 (by rfl) ⟨1700357, by rfl⟩ : syracuseStep 2267143 = 3400715) B3400715
theorem B2550541 : Blo 2265435 2550541 := bbase (se 3 (by rfl) ⟨478226, by rfl⟩ : syracuseStep 2550541 = 956453) (by norm_num)
theorem B3400721 : Blo 2265435 3400721 := bstep (se 2 (by rfl) ⟨1275270, by rfl⟩ : syracuseStep 3400721 = 2550541) B2550541
theorem B2267147 : Blo 2265435 2267147 := bstep (se 1 (by rfl) ⟨1700360, by rfl⟩ : syracuseStep 2267147 = 3400721) B3400721
theorem B7651637 : Blo 2265435 7651637 := bbase (se 5 (by rfl) ⟨358670, by rfl⟩ : syracuseStep 7651637 = 717341) (by norm_num)
theorem B5101091 : Blo 2265435 5101091 := bstep (se 1 (by rfl) ⟨3825818, by rfl⟩ : syracuseStep 5101091 = 7651637) B7651637
theorem B3400727 : Blo 2265435 3400727 := bstep (se 1 (by rfl) ⟨2550545, by rfl⟩ : syracuseStep 3400727 = 5101091) B5101091
theorem B2267151 : Blo 2265435 2267151 := bstep (se 1 (by rfl) ⟨1700363, by rfl⟩ : syracuseStep 2267151 = 3400727) B3400727
theorem B3400733 : Blo 2265435 3400733 := bbase (se 3 (by rfl) ⟨637637, by rfl⟩ : syracuseStep 3400733 = 1275275) (by norm_num)
theorem B2267155 : Blo 2265435 2267155 := bstep (se 1 (by rfl) ⟨1700366, by rfl⟩ : syracuseStep 2267155 = 3400733) B3400733
theorem B5101109 : Blo 2265435 5101109 := bbase (se 5 (by rfl) ⟨239114, by rfl⟩ : syracuseStep 5101109 = 478229) (by norm_num)
theorem B3400739 : Blo 2265435 3400739 := bstep (se 1 (by rfl) ⟨2550554, by rfl⟩ : syracuseStep 3400739 = 5101109) B5101109
theorem B2267159 : Blo 2265435 2267159 := bstep (se 1 (by rfl) ⟨1700369, by rfl⟩ : syracuseStep 2267159 = 3400739) B3400739
theorem B8725589 : Blo 2265435 8725589 := bbase (se 8 (by rfl) ⟨51126, by rfl⟩ : syracuseStep 8725589 = 102253) (by norm_num)
theorem B5817059 : Blo 2265435 5817059 := bstep (se 1 (by rfl) ⟨4362794, by rfl⟩ : syracuseStep 5817059 = 8725589) B8725589
theorem B3878039 : Blo 2265435 3878039 := bstep (se 1 (by rfl) ⟨2908529, by rfl⟩ : syracuseStep 3878039 = 5817059) B5817059
theorem B2585359 : Blo 2265435 2585359 := bstep (se 1 (by rfl) ⟨1939019, by rfl⟩ : syracuseStep 2585359 = 3878039) B3878039
theorem B3447145 : Blo 2265435 3447145 := bstep (se 2 (by rfl) ⟨1292679, by rfl⟩ : syracuseStep 3447145 = 2585359) B2585359
theorem B4596193 : Blo 2265435 4596193 := bstep (se 2 (by rfl) ⟨1723572, by rfl⟩ : syracuseStep 4596193 = 3447145) B3447145
theorem B6128257 : Blo 2265435 6128257 := bstep (se 2 (by rfl) ⟨2298096, by rfl⟩ : syracuseStep 6128257 = 4596193) B4596193
theorem B8171009 : Blo 2265435 8171009 := bstep (se 2 (by rfl) ⟨3064128, by rfl⟩ : syracuseStep 8171009 = 6128257) B6128257
theorem B5447339 : Blo 2265435 5447339 := bstep (se 1 (by rfl) ⟨4085504, by rfl⟩ : syracuseStep 5447339 = 8171009) B8171009
theorem B3631559 : Blo 2265435 3631559 := bstep (se 1 (by rfl) ⟨2723669, by rfl⟩ : syracuseStep 3631559 = 5447339) B5447339
theorem B9684157 : Blo 2265435 9684157 := bstep (se 3 (by rfl) ⟨1815779, by rfl⟩ : syracuseStep 9684157 = 3631559) B3631559
theorem B12912209 : Blo 2265435 12912209 := bstep (se 2 (by rfl) ⟨4842078, by rfl⟩ : syracuseStep 12912209 = 9684157) B9684157
theorem B8608139 : Blo 2265435 8608139 := bstep (se 1 (by rfl) ⟨6456104, by rfl⟩ : syracuseStep 8608139 = 12912209) B12912209
theorem B5738759 : Blo 2265435 5738759 := bstep (se 1 (by rfl) ⟨4304069, by rfl⟩ : syracuseStep 5738759 = 8608139) B8608139
theorem B3825839 : Blo 2265435 3825839 := bstep (se 1 (by rfl) ⟨2869379, by rfl⟩ : syracuseStep 3825839 = 5738759) B5738759
theorem B2550559 : Blo 2265435 2550559 := bstep (se 1 (by rfl) ⟨1912919, by rfl⟩ : syracuseStep 2550559 = 3825839) B3825839
theorem B3400745 : Blo 2265435 3400745 := bstep (se 2 (by rfl) ⟨1275279, by rfl⟩ : syracuseStep 3400745 = 2550559) B2550559
theorem B2267163 : Blo 2265435 2267163 := bstep (se 1 (by rfl) ⟨1700372, by rfl⟩ : syracuseStep 2267163 = 3400745) B3400745
theorem B3631565 : Blo 2265435 3631565 := bbase (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) (by norm_num)
theorem B9684173 : Blo 2265435 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B6456115 : Blo 2265435 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B8608153 : Blo 2265435 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B11477537 : Blo 2265435 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B7651691 : Blo 2265435 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B5101127 : Blo 2265435 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B3400751 : Blo 2265435 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B2267167 : Blo 2265435 2267167 := bstep (se 1 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 2267167 = 3400751) B3400751
theorem B3400757 : Blo 2265435 3400757 := bbase (se 5 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 3400757 = 318821) (by norm_num)
theorem B2267171 : Blo 2265435 2267171 := bstep (se 1 (by rfl) ⟨1700378, by rfl⟩ : syracuseStep 2267171 = 3400757) B3400757
theorem B5738789 : Blo 2265435 5738789 := bbase (se 4 (by rfl) ⟨538011, by rfl⟩ : syracuseStep 5738789 = 1076023) (by norm_num)
theorem B3825859 : Blo 2265435 3825859 := bstep (se 1 (by rfl) ⟨2869394, by rfl⟩ : syracuseStep 3825859 = 5738789) B5738789
theorem B5101145 : Blo 2265435 5101145 := bstep (se 2 (by rfl) ⟨1912929, by rfl⟩ : syracuseStep 5101145 = 3825859) B3825859
theorem B3400763 : Blo 2265435 3400763 := bstep (se 1 (by rfl) ⟨2550572, by rfl⟩ : syracuseStep 3400763 = 5101145) B5101145
theorem B2267175 : Blo 2265435 2267175 := bstep (se 1 (by rfl) ⟨1700381, by rfl⟩ : syracuseStep 2267175 = 3400763) B3400763
theorem B2550577 : Blo 2265435 2550577 := bbase (se 2 (by rfl) ⟨956466, by rfl⟩ : syracuseStep 2550577 = 1912933) (by norm_num)
theorem B3400769 : Blo 2265435 3400769 := bstep (se 2 (by rfl) ⟨1275288, by rfl⟩ : syracuseStep 3400769 = 2550577) B2550577
theorem B2267179 : Blo 2265435 2267179 := bstep (se 1 (by rfl) ⟨1700384, by rfl⟩ : syracuseStep 2267179 = 3400769) B3400769
theorem B5817109 : Blo 2265435 5817109 := bbase (se 6 (by rfl) ⟨136338, by rfl⟩ : syracuseStep 5817109 = 272677) (by norm_num)
theorem B7756145 : Blo 2265435 7756145 := bstep (se 2 (by rfl) ⟨2908554, by rfl⟩ : syracuseStep 7756145 = 5817109) B5817109
theorem B5170763 : Blo 2265435 5170763 := bstep (se 1 (by rfl) ⟨3878072, by rfl⟩ : syracuseStep 5170763 = 7756145) B7756145
theorem B13788701 : Blo 2265435 13788701 := bstep (se 3 (by rfl) ⟨2585381, by rfl⟩ : syracuseStep 13788701 = 5170763) B5170763
theorem B9192467 : Blo 2265435 9192467 := bstep (se 1 (by rfl) ⟨6894350, by rfl⟩ : syracuseStep 9192467 = 13788701) B13788701
theorem B6128311 : Blo 2265435 6128311 := bstep (se 1 (by rfl) ⟨4596233, by rfl⟩ : syracuseStep 6128311 = 9192467) B9192467
theorem B8171081 : Blo 2265435 8171081 := bstep (se 2 (by rfl) ⟨3064155, by rfl⟩ : syracuseStep 8171081 = 6128311) B6128311
theorem B5447387 : Blo 2265435 5447387 := bstep (se 1 (by rfl) ⟨4085540, by rfl⟩ : syracuseStep 5447387 = 8171081) B8171081
theorem B3631591 : Blo 2265435 3631591 := bstep (se 1 (by rfl) ⟨2723693, by rfl⟩ : syracuseStep 3631591 = 5447387) B5447387
theorem B4842121 : Blo 2265435 4842121 := bstep (se 2 (by rfl) ⟨1815795, by rfl⟩ : syracuseStep 4842121 = 3631591) B3631591
theorem B6456161 : Blo 2265435 6456161 := bstep (se 2 (by rfl) ⟨2421060, by rfl⟩ : syracuseStep 6456161 = 4842121) B4842121
theorem B4304107 : Blo 2265435 4304107 := bstep (se 1 (by rfl) ⟨3228080, by rfl⟩ : syracuseStep 4304107 = 6456161) B6456161
theorem B5738809 : Blo 2265435 5738809 := bstep (se 2 (by rfl) ⟨2152053, by rfl⟩ : syracuseStep 5738809 = 4304107) B4304107
theorem B7651745 : Blo 2265435 7651745 := bstep (se 2 (by rfl) ⟨2869404, by rfl⟩ : syracuseStep 7651745 = 5738809) B5738809
theorem B5101163 : Blo 2265435 5101163 := bstep (se 1 (by rfl) ⟨3825872, by rfl⟩ : syracuseStep 5101163 = 7651745) B7651745
theorem B3400775 : Blo 2265435 3400775 := bstep (se 1 (by rfl) ⟨2550581, by rfl⟩ : syracuseStep 3400775 = 5101163) B5101163
theorem B2267183 : Blo 2265435 2267183 := bstep (se 1 (by rfl) ⟨1700387, by rfl⟩ : syracuseStep 2267183 = 3400775) B3400775
theorem B3400781 : Blo 2265435 3400781 := bbase (se 3 (by rfl) ⟨637646, by rfl⟩ : syracuseStep 3400781 = 1275293) (by norm_num)
theorem B2267187 : Blo 2265435 2267187 := bstep (se 1 (by rfl) ⟨1700390, by rfl⟩ : syracuseStep 2267187 = 3400781) B3400781
theorem B5101181 : Blo 2265435 5101181 := bbase (se 3 (by rfl) ⟨956471, by rfl⟩ : syracuseStep 5101181 = 1912943) (by norm_num)
theorem B3400787 : Blo 2265435 3400787 := bstep (se 1 (by rfl) ⟨2550590, by rfl⟩ : syracuseStep 3400787 = 5101181) B5101181
theorem B2267191 : Blo 2265435 2267191 := bstep (se 1 (by rfl) ⟨1700393, by rfl⟩ : syracuseStep 2267191 = 3400787) B3400787
theorem B3825893 : Blo 2265435 3825893 := bbase (se 4 (by rfl) ⟨358677, by rfl⟩ : syracuseStep 3825893 = 717355) (by norm_num)
theorem B2550595 : Blo 2265435 2550595 := bstep (se 1 (by rfl) ⟨1912946, by rfl⟩ : syracuseStep 2550595 = 3825893) B3825893
theorem B3400793 : Blo 2265435 3400793 := bstep (se 2 (by rfl) ⟨1275297, by rfl⟩ : syracuseStep 3400793 = 2550595) B2550595
theorem B2267195 : Blo 2265435 2267195 := bstep (se 1 (by rfl) ⟨1700396, by rfl⟩ : syracuseStep 2267195 = 3400793) B3400793
theorem B2298133 : Blo 2265435 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B3064177 : Blo 2265435 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B4085569 : Blo 2265435 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B5447425 : Blo 2265435 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B7263233 : Blo 2265435 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B4842155 : Blo 2265435 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B3228103 : Blo 2265435 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B17216549 : Blo 2265435 17216549 := bstep (se 4 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 17216549 = 3228103) B3228103
theorem B11477699 : Blo 2265435 11477699 := bstep (se 1 (by rfl) ⟨8608274, by rfl⟩ : syracuseStep 11477699 = 17216549) B17216549
theorem B7651799 : Blo 2265435 7651799 := bstep (se 1 (by rfl) ⟨5738849, by rfl⟩ : syracuseStep 7651799 = 11477699) B11477699
theorem B5101199 : Blo 2265435 5101199 := bstep (se 1 (by rfl) ⟨3825899, by rfl⟩ : syracuseStep 5101199 = 7651799) B7651799
theorem B3400799 : Blo 2265435 3400799 := bstep (se 1 (by rfl) ⟨2550599, by rfl⟩ : syracuseStep 3400799 = 5101199) B5101199
theorem B2267199 : Blo 2265435 2267199 := bstep (se 1 (by rfl) ⟨1700399, by rfl⟩ : syracuseStep 2267199 = 3400799) B3400799
theorem B3400805 : Blo 2265435 3400805 := bbase (se 4 (by rfl) ⟨318825, by rfl⟩ : syracuseStep 3400805 = 637651) (by norm_num)
theorem B2267203 : Blo 2265435 2267203 := bstep (se 1 (by rfl) ⟨1700402, by rfl⟩ : syracuseStep 2267203 = 3400805) B3400805
theorem B4842173 : Blo 2265435 4842173 := bbase (se 3 (by rfl) ⟨907907, by rfl⟩ : syracuseStep 4842173 = 1815815) (by norm_num)
theorem B3228115 : Blo 2265435 3228115 := bstep (se 1 (by rfl) ⟨2421086, by rfl⟩ : syracuseStep 3228115 = 4842173) B4842173
theorem B4304153 : Blo 2265435 4304153 := bstep (se 2 (by rfl) ⟨1614057, by rfl⟩ : syracuseStep 4304153 = 3228115) B3228115
theorem B2869435 : Blo 2265435 2869435 := bstep (se 1 (by rfl) ⟨2152076, by rfl⟩ : syracuseStep 2869435 = 4304153) B4304153
theorem B3825913 : Blo 2265435 3825913 := bstep (se 2 (by rfl) ⟨1434717, by rfl⟩ : syracuseStep 3825913 = 2869435) B2869435
theorem B5101217 : Blo 2265435 5101217 := bstep (se 2 (by rfl) ⟨1912956, by rfl⟩ : syracuseStep 5101217 = 3825913) B3825913
theorem B3400811 : Blo 2265435 3400811 := bstep (se 1 (by rfl) ⟨2550608, by rfl⟩ : syracuseStep 3400811 = 5101217) B5101217
theorem B2267207 : Blo 2265435 2267207 := bstep (se 1 (by rfl) ⟨1700405, by rfl⟩ : syracuseStep 2267207 = 3400811) B3400811
theorem B2550613 : Blo 2265435 2550613 := bbase (se 9 (by rfl) ⟨7472, by rfl⟩ : syracuseStep 2550613 = 14945) (by norm_num)
theorem B3400817 : Blo 2265435 3400817 := bstep (se 2 (by rfl) ⟨1275306, by rfl⟩ : syracuseStep 3400817 = 2550613) B2550613
theorem B2267211 : Blo 2265435 2267211 := bstep (se 1 (by rfl) ⟨1700408, by rfl⟩ : syracuseStep 2267211 = 3400817) B3400817
theorem B2869445 : Blo 2265435 2869445 := bbase (se 4 (by rfl) ⟨269010, by rfl⟩ : syracuseStep 2869445 = 538021) (by norm_num)
theorem B7651853 : Blo 2265435 7651853 := bstep (se 3 (by rfl) ⟨1434722, by rfl⟩ : syracuseStep 7651853 = 2869445) B2869445
theorem B5101235 : Blo 2265435 5101235 := bstep (se 1 (by rfl) ⟨3825926, by rfl⟩ : syracuseStep 5101235 = 7651853) B7651853
theorem B3400823 : Blo 2265435 3400823 := bstep (se 1 (by rfl) ⟨2550617, by rfl⟩ : syracuseStep 3400823 = 5101235) B5101235
theorem B2267215 : Blo 2265435 2267215 := bstep (se 1 (by rfl) ⟨1700411, by rfl⟩ : syracuseStep 2267215 = 3400823) B3400823
theorem B3400829 : Blo 2265435 3400829 := bbase (se 3 (by rfl) ⟨637655, by rfl⟩ : syracuseStep 3400829 = 1275311) (by norm_num)
theorem B2267219 : Blo 2265435 2267219 := bstep (se 1 (by rfl) ⟨1700414, by rfl⟩ : syracuseStep 2267219 = 3400829) B3400829
theorem B5101253 : Blo 2265435 5101253 := bbase (se 4 (by rfl) ⟨478242, by rfl⟩ : syracuseStep 5101253 = 956485) (by norm_num)
theorem B3400835 : Blo 2265435 3400835 := bstep (se 1 (by rfl) ⟨2550626, by rfl⟩ : syracuseStep 3400835 = 5101253) B5101253
theorem B2267223 : Blo 2265435 2267223 := bstep (se 1 (by rfl) ⟨1700417, by rfl⟩ : syracuseStep 2267223 = 3400835) B3400835
theorem B7862117 : Blo 2265435 7862117 := bbase (se 4 (by rfl) ⟨737073, by rfl⟩ : syracuseStep 7862117 = 1474147) (by norm_num)
theorem B20965645 : Blo 2265435 20965645 := bstep (se 3 (by rfl) ⟨3931058, by rfl⟩ : syracuseStep 20965645 = 7862117) B7862117
theorem B27954193 : Blo 2265435 27954193 := bstep (se 2 (by rfl) ⟨10482822, by rfl⟩ : syracuseStep 27954193 = 20965645) B20965645
theorem B37272257 : Blo 2265435 37272257 := bstep (se 2 (by rfl) ⟨13977096, by rfl⟩ : syracuseStep 37272257 = 27954193) B27954193
theorem B24848171 : Blo 2265435 24848171 := bstep (se 1 (by rfl) ⟨18636128, by rfl⟩ : syracuseStep 24848171 = 37272257) B37272257
theorem B16565447 : Blo 2265435 16565447 := bstep (se 1 (by rfl) ⟨12424085, by rfl⟩ : syracuseStep 16565447 = 24848171) B24848171
theorem B11043631 : Blo 2265435 11043631 := bstep (se 1 (by rfl) ⟨8282723, by rfl⟩ : syracuseStep 11043631 = 16565447) B16565447
theorem B14724841 : Blo 2265435 14724841 := bstep (se 2 (by rfl) ⟨5521815, by rfl⟩ : syracuseStep 14724841 = 11043631) B11043631
theorem B19633121 : Blo 2265435 19633121 := bstep (se 2 (by rfl) ⟨7362420, by rfl⟩ : syracuseStep 19633121 = 14724841) B14724841
theorem B13088747 : Blo 2265435 13088747 := bstep (se 1 (by rfl) ⟨9816560, by rfl⟩ : syracuseStep 13088747 = 19633121) B19633121
theorem B34903325 : Blo 2265435 34903325 := bstep (se 3 (by rfl) ⟨6544373, by rfl⟩ : syracuseStep 34903325 = 13088747) B13088747
theorem B23268883 : Blo 2265435 23268883 := bstep (se 1 (by rfl) ⟨17451662, by rfl⟩ : syracuseStep 23268883 = 34903325) B34903325
theorem B31025177 : Blo 2265435 31025177 := bstep (se 2 (by rfl) ⟨11634441, by rfl⟩ : syracuseStep 31025177 = 23268883) B23268883
theorem B20683451 : Blo 2265435 20683451 := bstep (se 1 (by rfl) ⟨15512588, by rfl⟩ : syracuseStep 20683451 = 31025177) B31025177
theorem B13788967 : Blo 2265435 13788967 := bstep (se 1 (by rfl) ⟨10341725, by rfl⟩ : syracuseStep 13788967 = 20683451) B20683451
theorem B18385289 : Blo 2265435 18385289 := bstep (se 2 (by rfl) ⟨6894483, by rfl⟩ : syracuseStep 18385289 = 13788967) B13788967
theorem B12256859 : Blo 2265435 12256859 := bstep (se 1 (by rfl) ⟨9192644, by rfl⟩ : syracuseStep 12256859 = 18385289) B18385289
theorem B32684957 : Blo 2265435 32684957 := bstep (se 3 (by rfl) ⟨6128429, by rfl⟩ : syracuseStep 32684957 = 12256859) B12256859
theorem B21789971 : Blo 2265435 21789971 := bstep (se 1 (by rfl) ⟨16342478, by rfl⟩ : syracuseStep 21789971 = 32684957) B32684957
theorem B14526647 : Blo 2265435 14526647 := bstep (se 1 (by rfl) ⟨10894985, by rfl⟩ : syracuseStep 14526647 = 21789971) B21789971
theorem B9684431 : Blo 2265435 9684431 := bstep (se 1 (by rfl) ⟨7263323, by rfl⟩ : syracuseStep 9684431 = 14526647) B14526647
theorem B6456287 : Blo 2265435 6456287 := bstep (se 1 (by rfl) ⟨4842215, by rfl⟩ : syracuseStep 6456287 = 9684431) B9684431
theorem B4304191 : Blo 2265435 4304191 := bstep (se 1 (by rfl) ⟨3228143, by rfl⟩ : syracuseStep 4304191 = 6456287) B6456287
theorem B5738921 : Blo 2265435 5738921 := bstep (se 2 (by rfl) ⟨2152095, by rfl⟩ : syracuseStep 5738921 = 4304191) B4304191
theorem B3825947 : Blo 2265435 3825947 := bstep (se 1 (by rfl) ⟨2869460, by rfl⟩ : syracuseStep 3825947 = 5738921) B5738921
theorem B2550631 : Blo 2265435 2550631 := bstep (se 1 (by rfl) ⟨1912973, by rfl⟩ : syracuseStep 2550631 = 3825947) B3825947
theorem B3400841 : Blo 2265435 3400841 := bstep (se 2 (by rfl) ⟨1275315, by rfl⟩ : syracuseStep 3400841 = 2550631) B2550631
theorem B2267227 : Blo 2265435 2267227 := bstep (se 1 (by rfl) ⟨1700420, by rfl⟩ : syracuseStep 2267227 = 3400841) B3400841
theorem B11477861 : Blo 2265435 11477861 := bbase (se 4 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 11477861 = 2152099) (by norm_num)
theorem B7651907 : Blo 2265435 7651907 := bstep (se 1 (by rfl) ⟨5738930, by rfl⟩ : syracuseStep 7651907 = 11477861) B11477861
theorem B5101271 : Blo 2265435 5101271 := bstep (se 1 (by rfl) ⟨3825953, by rfl⟩ : syracuseStep 5101271 = 7651907) B7651907
theorem B3400847 : Blo 2265435 3400847 := bstep (se 1 (by rfl) ⟨2550635, by rfl⟩ : syracuseStep 3400847 = 5101271) B5101271
theorem B2267231 : Blo 2265435 2267231 := bstep (se 1 (by rfl) ⟨1700423, by rfl⟩ : syracuseStep 2267231 = 3400847) B3400847
theorem B3400853 : Blo 2265435 3400853 := bbase (se 6 (by rfl) ⟨79707, by rfl⟩ : syracuseStep 3400853 = 159415) (by norm_num)
theorem B2267235 : Blo 2265435 2267235 := bstep (se 1 (by rfl) ⟨1700426, by rfl⟩ : syracuseStep 2267235 = 3400853) B3400853
theorem B5817253 : Blo 2265435 5817253 := bbase (se 4 (by rfl) ⟨545367, by rfl⟩ : syracuseStep 5817253 = 1090735) (by norm_num)
theorem B7756337 : Blo 2265435 7756337 := bstep (se 2 (by rfl) ⟨2908626, by rfl⟩ : syracuseStep 7756337 = 5817253) B5817253
theorem B5170891 : Blo 2265435 5170891 := bstep (se 1 (by rfl) ⟨3878168, by rfl⟩ : syracuseStep 5170891 = 7756337) B7756337
theorem B6894521 : Blo 2265435 6894521 := bstep (se 2 (by rfl) ⟨2585445, by rfl⟩ : syracuseStep 6894521 = 5170891) B5170891
theorem B4596347 : Blo 2265435 4596347 := bstep (se 1 (by rfl) ⟨3447260, by rfl⟩ : syracuseStep 4596347 = 6894521) B6894521
theorem B3064231 : Blo 2265435 3064231 := bstep (se 1 (by rfl) ⟨2298173, by rfl⟩ : syracuseStep 3064231 = 4596347) B4596347
theorem B4085641 : Blo 2265435 4085641 := bstep (se 2 (by rfl) ⟨1532115, by rfl⟩ : syracuseStep 4085641 = 3064231) B3064231
theorem B5447521 : Blo 2265435 5447521 := bstep (se 2 (by rfl) ⟨2042820, by rfl⟩ : syracuseStep 5447521 = 4085641) B4085641
theorem B7263361 : Blo 2265435 7263361 := bstep (se 2 (by rfl) ⟨2723760, by rfl⟩ : syracuseStep 7263361 = 5447521) B5447521
theorem B9684481 : Blo 2265435 9684481 := bstep (se 2 (by rfl) ⟨3631680, by rfl⟩ : syracuseStep 9684481 = 7263361) B7263361
theorem B12912641 : Blo 2265435 12912641 := bstep (se 2 (by rfl) ⟨4842240, by rfl⟩ : syracuseStep 12912641 = 9684481) B9684481
theorem B8608427 : Blo 2265435 8608427 := bstep (se 1 (by rfl) ⟨6456320, by rfl⟩ : syracuseStep 8608427 = 12912641) B12912641
theorem B5738951 : Blo 2265435 5738951 := bstep (se 1 (by rfl) ⟨4304213, by rfl⟩ : syracuseStep 5738951 = 8608427) B8608427
theorem B3825967 : Blo 2265435 3825967 := bstep (se 1 (by rfl) ⟨2869475, by rfl⟩ : syracuseStep 3825967 = 5738951) B5738951
theorem B5101289 : Blo 2265435 5101289 := bstep (se 2 (by rfl) ⟨1912983, by rfl⟩ : syracuseStep 5101289 = 3825967) B3825967
theorem B3400859 : Blo 2265435 3400859 := bstep (se 1 (by rfl) ⟨2550644, by rfl⟩ : syracuseStep 3400859 = 5101289) B5101289
theorem B2267239 : Blo 2265435 2267239 := bstep (se 1 (by rfl) ⟨1700429, by rfl⟩ : syracuseStep 2267239 = 3400859) B3400859
theorem B2550649 : Blo 2265435 2550649 := bbase (se 2 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 2550649 = 1912987) (by norm_num)
theorem B3400865 : Blo 2265435 3400865 := bstep (se 2 (by rfl) ⟨1275324, by rfl⟩ : syracuseStep 3400865 = 2550649) B2550649
theorem B2267243 : Blo 2265435 2267243 := bstep (se 1 (by rfl) ⟨1700432, by rfl⟩ : syracuseStep 2267243 = 3400865) B3400865
theorem B14526773 : Blo 2265435 14526773 := bbase (se 5 (by rfl) ⟨680942, by rfl⟩ : syracuseStep 14526773 = 1361885) (by norm_num)
theorem B9684515 : Blo 2265435 9684515 := bstep (se 1 (by rfl) ⟨7263386, by rfl⟩ : syracuseStep 9684515 = 14526773) B14526773
theorem B6456343 : Blo 2265435 6456343 := bstep (se 1 (by rfl) ⟨4842257, by rfl⟩ : syracuseStep 6456343 = 9684515) B9684515
theorem B8608457 : Blo 2265435 8608457 := bstep (se 2 (by rfl) ⟨3228171, by rfl⟩ : syracuseStep 8608457 = 6456343) B6456343
theorem B5738971 : Blo 2265435 5738971 := bstep (se 1 (by rfl) ⟨4304228, by rfl⟩ : syracuseStep 5738971 = 8608457) B8608457
theorem B7651961 : Blo 2265435 7651961 := bstep (se 2 (by rfl) ⟨2869485, by rfl⟩ : syracuseStep 7651961 = 5738971) B5738971
theorem B5101307 : Blo 2265435 5101307 := bstep (se 1 (by rfl) ⟨3825980, by rfl⟩ : syracuseStep 5101307 = 7651961) B7651961
theorem B3400871 : Blo 2265435 3400871 := bstep (se 1 (by rfl) ⟨2550653, by rfl⟩ : syracuseStep 3400871 = 5101307) B5101307
theorem B2267247 : Blo 2265435 2267247 := bstep (se 1 (by rfl) ⟨1700435, by rfl⟩ : syracuseStep 2267247 = 3400871) B3400871
theorem B3400877 : Blo 2265435 3400877 := bbase (se 3 (by rfl) ⟨637664, by rfl⟩ : syracuseStep 3400877 = 1275329) (by norm_num)
theorem B2267251 : Blo 2265435 2267251 := bstep (se 1 (by rfl) ⟨1700438, by rfl⟩ : syracuseStep 2267251 = 3400877) B3400877
theorem B5101325 : Blo 2265435 5101325 := bbase (se 3 (by rfl) ⟨956498, by rfl⟩ : syracuseStep 5101325 = 1912997) (by norm_num)
theorem B3400883 : Blo 2265435 3400883 := bstep (se 1 (by rfl) ⟨2550662, by rfl⟩ : syracuseStep 3400883 = 5101325) B5101325
theorem B2267255 : Blo 2265435 2267255 := bstep (se 1 (by rfl) ⟨1700441, by rfl⟩ : syracuseStep 2267255 = 3400883) B3400883
theorem B2869501 : Blo 2265435 2869501 := bbase (se 3 (by rfl) ⟨538031, by rfl⟩ : syracuseStep 2869501 = 1076063) (by norm_num)
theorem B3826001 : Blo 2265435 3826001 := bstep (se 2 (by rfl) ⟨1434750, by rfl⟩ : syracuseStep 3826001 = 2869501) B2869501
theorem B2550667 : Blo 2265435 2550667 := bstep (se 1 (by rfl) ⟨1913000, by rfl⟩ : syracuseStep 2550667 = 3826001) B3826001
theorem B3400889 : Blo 2265435 3400889 := bstep (se 2 (by rfl) ⟨1275333, by rfl⟩ : syracuseStep 3400889 = 2550667) B2550667
theorem B2267259 : Blo 2265435 2267259 := bstep (se 1 (by rfl) ⟨1700444, by rfl⟩ : syracuseStep 2267259 = 3400889) B3400889
theorem B2723789 : Blo 2265435 2723789 := bbase (se 3 (by rfl) ⟨510710, by rfl⟩ : syracuseStep 2723789 = 1021421) (by norm_num)
theorem B7263437 : Blo 2265435 7263437 := bstep (se 3 (by rfl) ⟨1361894, by rfl⟩ : syracuseStep 7263437 = 2723789) B2723789
theorem B19369165 : Blo 2265435 19369165 := bstep (se 3 (by rfl) ⟨3631718, by rfl⟩ : syracuseStep 19369165 = 7263437) B7263437
theorem B25825553 : Blo 2265435 25825553 := bstep (se 2 (by rfl) ⟨9684582, by rfl⟩ : syracuseStep 25825553 = 19369165) B19369165
theorem B17217035 : Blo 2265435 17217035 := bstep (se 1 (by rfl) ⟨12912776, by rfl⟩ : syracuseStep 17217035 = 25825553) B25825553
theorem B11478023 : Blo 2265435 11478023 := bstep (se 1 (by rfl) ⟨8608517, by rfl⟩ : syracuseStep 11478023 = 17217035) B17217035
theorem B7652015 : Blo 2265435 7652015 := bstep (se 1 (by rfl) ⟨5739011, by rfl⟩ : syracuseStep 7652015 = 11478023) B11478023
theorem B5101343 : Blo 2265435 5101343 := bstep (se 1 (by rfl) ⟨3826007, by rfl⟩ : syracuseStep 5101343 = 7652015) B7652015
theorem B3400895 : Blo 2265435 3400895 := bstep (se 1 (by rfl) ⟨2550671, by rfl⟩ : syracuseStep 3400895 = 5101343) B5101343
theorem B2267263 : Blo 2265435 2267263 := bstep (se 1 (by rfl) ⟨1700447, by rfl⟩ : syracuseStep 2267263 = 3400895) B3400895
theorem B3400901 : Blo 2265435 3400901 := bbase (se 4 (by rfl) ⟨318834, by rfl⟩ : syracuseStep 3400901 = 637669) (by norm_num)
theorem B2267267 : Blo 2265435 2267267 := bstep (se 1 (by rfl) ⟨1700450, by rfl⟩ : syracuseStep 2267267 = 3400901) B3400901
theorem B3826021 : Blo 2265435 3826021 := bbase (se 4 (by rfl) ⟨358689, by rfl⟩ : syracuseStep 3826021 = 717379) (by norm_num)
theorem B5101361 : Blo 2265435 5101361 := bstep (se 2 (by rfl) ⟨1913010, by rfl⟩ : syracuseStep 5101361 = 3826021) B3826021
theorem B3400907 : Blo 2265435 3400907 := bstep (se 1 (by rfl) ⟨2550680, by rfl⟩ : syracuseStep 3400907 = 5101361) B5101361
theorem B2267271 : Blo 2265435 2267271 := bstep (se 1 (by rfl) ⟨1700453, by rfl⟩ : syracuseStep 2267271 = 3400907) B3400907
theorem B2550685 : Blo 2265435 2550685 := bbase (se 3 (by rfl) ⟨478253, by rfl⟩ : syracuseStep 2550685 = 956507) (by norm_num)
theorem B3400913 : Blo 2265435 3400913 := bstep (se 2 (by rfl) ⟨1275342, by rfl⟩ : syracuseStep 3400913 = 2550685) B2550685
theorem B2267275 : Blo 2265435 2267275 := bstep (se 1 (by rfl) ⟨1700456, by rfl⟩ : syracuseStep 2267275 = 3400913) B3400913
theorem B7652069 : Blo 2265435 7652069 := bbase (se 4 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 7652069 = 1434763) (by norm_num)
theorem B5101379 : Blo 2265435 5101379 := bstep (se 1 (by rfl) ⟨3826034, by rfl⟩ : syracuseStep 5101379 = 7652069) B7652069
theorem B3400919 : Blo 2265435 3400919 := bstep (se 1 (by rfl) ⟨2550689, by rfl⟩ : syracuseStep 3400919 = 5101379) B5101379
theorem B2267279 : Blo 2265435 2267279 := bstep (se 1 (by rfl) ⟨1700459, by rfl⟩ : syracuseStep 2267279 = 3400919) B3400919
theorem B3400925 : Blo 2265435 3400925 := bbase (se 3 (by rfl) ⟨637673, by rfl⟩ : syracuseStep 3400925 = 1275347) (by norm_num)
theorem B2267283 : Blo 2265435 2267283 := bstep (se 1 (by rfl) ⟨1700462, by rfl⟩ : syracuseStep 2267283 = 3400925) B3400925
theorem B5101397 : Blo 2265435 5101397 := bbase (se 9 (by rfl) ⟨14945, by rfl⟩ : syracuseStep 5101397 = 29891) (by norm_num)
theorem B3400931 : Blo 2265435 3400931 := bstep (se 1 (by rfl) ⟨2550698, by rfl⟩ : syracuseStep 3400931 = 5101397) B5101397
theorem B2267287 : Blo 2265435 2267287 := bstep (se 1 (by rfl) ⟨1700465, by rfl⟩ : syracuseStep 2267287 = 3400931) B3400931
theorem B6456469 : Blo 2265435 6456469 := bbase (se 6 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 6456469 = 302647) (by norm_num)
theorem B8608625 : Blo 2265435 8608625 := bstep (se 2 (by rfl) ⟨3228234, by rfl⟩ : syracuseStep 8608625 = 6456469) B6456469
theorem B5739083 : Blo 2265435 5739083 := bstep (se 1 (by rfl) ⟨4304312, by rfl⟩ : syracuseStep 5739083 = 8608625) B8608625
theorem B3826055 : Blo 2265435 3826055 := bstep (se 1 (by rfl) ⟨2869541, by rfl⟩ : syracuseStep 3826055 = 5739083) B5739083
theorem B2550703 : Blo 2265435 2550703 := bstep (se 1 (by rfl) ⟨1913027, by rfl⟩ : syracuseStep 2550703 = 3826055) B3826055
theorem B3400937 : Blo 2265435 3400937 := bstep (se 2 (by rfl) ⟨1275351, by rfl⟩ : syracuseStep 3400937 = 2550703) B2550703
theorem B2267291 : Blo 2265435 2267291 := bstep (se 1 (by rfl) ⟨1700468, by rfl⟩ : syracuseStep 2267291 = 3400937) B3400937
theorem B17452181 : Blo 2265435 17452181 := bbase (se 6 (by rfl) ⟨409035, by rfl⟩ : syracuseStep 17452181 = 818071) (by norm_num)
theorem B11634787 : Blo 2265435 11634787 := bstep (se 1 (by rfl) ⟨8726090, by rfl⟩ : syracuseStep 11634787 = 17452181) B17452181
theorem B15513049 : Blo 2265435 15513049 := bstep (se 2 (by rfl) ⟨5817393, by rfl⟩ : syracuseStep 15513049 = 11634787) B11634787
theorem B82736261 : Blo 2265435 82736261 := bstep (se 4 (by rfl) ⟨7756524, by rfl⟩ : syracuseStep 82736261 = 15513049) B15513049
theorem B55157507 : Blo 2265435 55157507 := bstep (se 1 (by rfl) ⟨41368130, by rfl⟩ : syracuseStep 55157507 = 82736261) B82736261
theorem B36771671 : Blo 2265435 36771671 := bstep (se 1 (by rfl) ⟨27578753, by rfl⟩ : syracuseStep 36771671 = 55157507) B55157507
theorem B98057789 : Blo 2265435 98057789 := bstep (se 3 (by rfl) ⟨18385835, by rfl⟩ : syracuseStep 98057789 = 36771671) B36771671
theorem B65371859 : Blo 2265435 65371859 := bstep (se 1 (by rfl) ⟨49028894, by rfl⟩ : syracuseStep 65371859 = 98057789) B98057789
theorem B43581239 : Blo 2265435 43581239 := bstep (se 1 (by rfl) ⟨32685929, by rfl⟩ : syracuseStep 43581239 = 65371859) B65371859
theorem B29054159 : Blo 2265435 29054159 := bstep (se 1 (by rfl) ⟨21790619, by rfl⟩ : syracuseStep 29054159 = 43581239) B43581239
theorem B19369439 : Blo 2265435 19369439 := bstep (se 1 (by rfl) ⟨14527079, by rfl⟩ : syracuseStep 19369439 = 29054159) B29054159
theorem B12912959 : Blo 2265435 12912959 := bstep (se 1 (by rfl) ⟨9684719, by rfl⟩ : syracuseStep 12912959 = 19369439) B19369439
theorem B8608639 : Blo 2265435 8608639 := bstep (se 1 (by rfl) ⟨6456479, by rfl⟩ : syracuseStep 8608639 = 12912959) B12912959
theorem B11478185 : Blo 2265435 11478185 := bstep (se 2 (by rfl) ⟨4304319, by rfl⟩ : syracuseStep 11478185 = 8608639) B8608639
theorem B7652123 : Blo 2265435 7652123 := bstep (se 1 (by rfl) ⟨5739092, by rfl⟩ : syracuseStep 7652123 = 11478185) B11478185
theorem B5101415 : Blo 2265435 5101415 := bstep (se 1 (by rfl) ⟨3826061, by rfl⟩ : syracuseStep 5101415 = 7652123) B7652123
theorem B3400943 : Blo 2265435 3400943 := bstep (se 1 (by rfl) ⟨2550707, by rfl⟩ : syracuseStep 3400943 = 5101415) B5101415
theorem B2267295 : Blo 2265435 2267295 := bstep (se 1 (by rfl) ⟨1700471, by rfl⟩ : syracuseStep 2267295 = 3400943) B3400943
theorem B3400949 : Blo 2265435 3400949 := bbase (se 5 (by rfl) ⟨159419, by rfl⟩ : syracuseStep 3400949 = 318839) (by norm_num)
theorem B2267299 : Blo 2265435 2267299 := bstep (se 1 (by rfl) ⟨1700474, by rfl⟩ : syracuseStep 2267299 = 3400949) B3400949
theorem B2487709 : Blo 2265435 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3316945 : Blo 2265435 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4422593 : Blo 2265435 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2948395 : Blo 2265435 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B3931193 : Blo 2265435 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B10483181 : Blo 2265435 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B6988787 : Blo 2265435 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B4659191 : Blo 2265435 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B3106127 : Blo 2265435 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B8283005 : Blo 2265435 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B5522003 : Blo 2265435 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B3681335 : Blo 2265435 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B2454223 : Blo 2265435 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B3272297 : Blo 2265435 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B8726125 : Blo 2265435 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B11634833 : Blo 2265435 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B7756555 : Blo 2265435 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B10342073 : Blo 2265435 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B6894715 : Blo 2265435 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B9192953 : Blo 2265435 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B6128635 : Blo 2265435 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B8171513 : Blo 2265435 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B5447675 : Blo 2265435 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B14527133 : Blo 2265435 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B9684755 : Blo 2265435 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B6456503 : Blo 2265435 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B4304335 : Blo 2265435 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B5739113 : Blo 2265435 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B3826075 : Blo 2265435 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B5101433 : Blo 2265435 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B3400955 : Blo 2265435 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B2267303 : Blo 2265435 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B2550721 : Blo 2265435 2550721 := bbase (se 2 (by rfl) ⟨956520, by rfl⟩ : syracuseStep 2550721 = 1913041) (by norm_num)
theorem B3400961 : Blo 2265435 3400961 := bstep (se 2 (by rfl) ⟨1275360, by rfl⟩ : syracuseStep 3400961 = 2550721) B2550721
theorem B2267307 : Blo 2265435 2267307 := bstep (se 1 (by rfl) ⟨1700480, by rfl⟩ : syracuseStep 2267307 = 3400961) B3400961
theorem B5739133 : Blo 2265435 5739133 := bbase (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) (by norm_num)
theorem B7652177 : Blo 2265435 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B5101451 : Blo 2265435 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B3400967 : Blo 2265435 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B2267311 : Blo 2265435 2267311 := bstep (se 1 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 2267311 = 3400967) B3400967
theorem B3400973 : Blo 2265435 3400973 := bbase (se 3 (by rfl) ⟨637682, by rfl⟩ : syracuseStep 3400973 = 1275365) (by norm_num)
theorem B2267315 : Blo 2265435 2267315 := bstep (se 1 (by rfl) ⟨1700486, by rfl⟩ : syracuseStep 2267315 = 3400973) B3400973
theorem B5101469 : Blo 2265435 5101469 := bbase (se 3 (by rfl) ⟨956525, by rfl⟩ : syracuseStep 5101469 = 1913051) (by norm_num)
theorem B3400979 : Blo 2265435 3400979 := bstep (se 1 (by rfl) ⟨2550734, by rfl⟩ : syracuseStep 3400979 = 5101469) B5101469
theorem B2267319 : Blo 2265435 2267319 := bstep (se 1 (by rfl) ⟨1700489, by rfl⟩ : syracuseStep 2267319 = 3400979) B3400979
theorem B3826109 : Blo 2265435 3826109 := bbase (se 3 (by rfl) ⟨717395, by rfl⟩ : syracuseStep 3826109 = 1434791) (by norm_num)
theorem B2550739 : Blo 2265435 2550739 := bstep (se 1 (by rfl) ⟨1913054, by rfl⟩ : syracuseStep 2550739 = 3826109) B3826109
theorem B3400985 : Blo 2265435 3400985 := bstep (se 2 (by rfl) ⟨1275369, by rfl⟩ : syracuseStep 3400985 = 2550739) B2550739
theorem B2267323 : Blo 2265435 2267323 := bstep (se 1 (by rfl) ⟨1700492, by rfl⟩ : syracuseStep 2267323 = 3400985) B3400985
theorem B12913141 : Blo 2265435 12913141 := bbase (se 5 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 12913141 = 1210607) (by norm_num)
theorem B17217521 : Blo 2265435 17217521 := bstep (se 2 (by rfl) ⟨6456570, by rfl⟩ : syracuseStep 17217521 = 12913141) B12913141
theorem B11478347 : Blo 2265435 11478347 := bstep (se 1 (by rfl) ⟨8608760, by rfl⟩ : syracuseStep 11478347 = 17217521) B17217521
theorem B7652231 : Blo 2265435 7652231 := bstep (se 1 (by rfl) ⟨5739173, by rfl⟩ : syracuseStep 7652231 = 11478347) B11478347
theorem B5101487 : Blo 2265435 5101487 := bstep (se 1 (by rfl) ⟨3826115, by rfl⟩ : syracuseStep 5101487 = 7652231) B7652231
theorem B3400991 : Blo 2265435 3400991 := bstep (se 1 (by rfl) ⟨2550743, by rfl⟩ : syracuseStep 3400991 = 5101487) B5101487
theorem B2267327 : Blo 2265435 2267327 := bstep (se 1 (by rfl) ⟨1700495, by rfl⟩ : syracuseStep 2267327 = 3400991) B3400991
theorem B3400997 : Blo 2265435 3400997 := bbase (se 4 (by rfl) ⟨318843, by rfl⟩ : syracuseStep 3400997 = 637687) (by norm_num)
theorem B2267331 : Blo 2265435 2267331 := bstep (se 1 (by rfl) ⟨1700498, by rfl⟩ : syracuseStep 2267331 = 3400997) B3400997
theorem B2869597 : Blo 2265435 2869597 := bbase (se 3 (by rfl) ⟨538049, by rfl⟩ : syracuseStep 2869597 = 1076099) (by norm_num)
theorem B3826129 : Blo 2265435 3826129 := bstep (se 2 (by rfl) ⟨1434798, by rfl⟩ : syracuseStep 3826129 = 2869597) B2869597
theorem B5101505 : Blo 2265435 5101505 := bstep (se 2 (by rfl) ⟨1913064, by rfl⟩ : syracuseStep 5101505 = 3826129) B3826129
theorem B3401003 : Blo 2265435 3401003 := bstep (se 1 (by rfl) ⟨2550752, by rfl⟩ : syracuseStep 3401003 = 5101505) B5101505
theorem B2267335 : Blo 2265435 2267335 := bstep (se 1 (by rfl) ⟨1700501, by rfl⟩ : syracuseStep 2267335 = 3401003) B3401003
theorem B2550757 : Blo 2265435 2550757 := bbase (se 4 (by rfl) ⟨239133, by rfl⟩ : syracuseStep 2550757 = 478267) (by norm_num)
theorem B3401009 : Blo 2265435 3401009 := bstep (se 2 (by rfl) ⟨1275378, by rfl⟩ : syracuseStep 3401009 = 2550757) B2550757
theorem B2267339 : Blo 2265435 2267339 := bstep (se 1 (by rfl) ⟨1700504, by rfl⟩ : syracuseStep 2267339 = 3401009) B3401009
theorem B3494453 : Blo 2265435 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B37274165 : Blo 2265435 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B24849443 : Blo 2265435 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B16566295 : Blo 2265435 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B22088393 : Blo 2265435 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B14725595 : Blo 2265435 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B39268253 : Blo 2265435 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B26178835 : Blo 2265435 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B34905113 : Blo 2265435 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B23270075 : Blo 2265435 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B15513383 : Blo 2265435 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B10342255 : Blo 2265435 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B13789673 : Blo 2265435 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B9193115 : Blo 2265435 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B24514973 : Blo 2265435 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B16343315 : Blo 2265435 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B10895543 : Blo 2265435 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B7263695 : Blo 2265435 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B4842463 : Blo 2265435 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B6456617 : Blo 2265435 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B4304411 : Blo 2265435 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B2869607 : Blo 2265435 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B7652285 : Blo 2265435 7652285 := bstep (se 3 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 7652285 = 2869607) B2869607
theorem B5101523 : Blo 2265435 5101523 := bstep (se 1 (by rfl) ⟨3826142, by rfl⟩ : syracuseStep 5101523 = 7652285) B7652285
theorem B3401015 : Blo 2265435 3401015 := bstep (se 1 (by rfl) ⟨2550761, by rfl⟩ : syracuseStep 3401015 = 5101523) B5101523
theorem B2267343 : Blo 2265435 2267343 := bstep (se 1 (by rfl) ⟨1700507, by rfl⟩ : syracuseStep 2267343 = 3401015) B3401015
theorem B3401021 : Blo 2265435 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B2267347 : Blo 2265435 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B5101541 : Blo 2265435 5101541 := bbase (se 4 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 5101541 = 956539) (by norm_num)
theorem B3401027 : Blo 2265435 3401027 := bstep (se 1 (by rfl) ⟨2550770, by rfl⟩ : syracuseStep 3401027 = 5101541) B5101541
theorem B2267351 : Blo 2265435 2267351 := bstep (se 1 (by rfl) ⟨1700513, by rfl⟩ : syracuseStep 2267351 = 3401027) B3401027
theorem B5739245 : Blo 2265435 5739245 := bbase (se 3 (by rfl) ⟨1076108, by rfl⟩ : syracuseStep 5739245 = 2152217) (by norm_num)
theorem B3826163 : Blo 2265435 3826163 := bstep (se 1 (by rfl) ⟨2869622, by rfl⟩ : syracuseStep 3826163 = 5739245) B5739245
theorem B2550775 : Blo 2265435 2550775 := bstep (se 1 (by rfl) ⟨1913081, by rfl⟩ : syracuseStep 2550775 = 3826163) B3826163
theorem B3401033 : Blo 2265435 3401033 := bstep (se 2 (by rfl) ⟨1275387, by rfl⟩ : syracuseStep 3401033 = 2550775) B2550775
theorem B2267355 : Blo 2265435 2267355 := bstep (se 1 (by rfl) ⟨1700516, by rfl⟩ : syracuseStep 2267355 = 3401033) B3401033
theorem B2723905 : Blo 2265435 2723905 := bbase (se 2 (by rfl) ⟨1021464, by rfl⟩ : syracuseStep 2723905 = 2042929) (by norm_num)
theorem B3631873 : Blo 2265435 3631873 := bstep (se 2 (by rfl) ⟨1361952, by rfl⟩ : syracuseStep 3631873 = 2723905) B2723905
theorem B4842497 : Blo 2265435 4842497 := bstep (se 2 (by rfl) ⟨1815936, by rfl⟩ : syracuseStep 4842497 = 3631873) B3631873
theorem B3228331 : Blo 2265435 3228331 := bstep (se 1 (by rfl) ⟨2421248, by rfl⟩ : syracuseStep 3228331 = 4842497) B4842497
theorem B4304441 : Blo 2265435 4304441 := bstep (se 2 (by rfl) ⟨1614165, by rfl⟩ : syracuseStep 4304441 = 3228331) B3228331
theorem B11478509 : Blo 2265435 11478509 := bstep (se 3 (by rfl) ⟨2152220, by rfl⟩ : syracuseStep 11478509 = 4304441) B4304441
theorem B7652339 : Blo 2265435 7652339 := bstep (se 1 (by rfl) ⟨5739254, by rfl⟩ : syracuseStep 7652339 = 11478509) B11478509
theorem B5101559 : Blo 2265435 5101559 := bstep (se 1 (by rfl) ⟨3826169, by rfl⟩ : syracuseStep 5101559 = 7652339) B7652339
theorem B3401039 : Blo 2265435 3401039 := bstep (se 1 (by rfl) ⟨2550779, by rfl⟩ : syracuseStep 3401039 = 5101559) B5101559
theorem B2267359 : Blo 2265435 2267359 := bstep (se 1 (by rfl) ⟨1700519, by rfl⟩ : syracuseStep 2267359 = 3401039) B3401039
theorem B3401045 : Blo 2265435 3401045 := bbase (se 12 (by rfl) ⟨1245, by rfl⟩ : syracuseStep 3401045 = 2491) (by norm_num)
theorem B2267363 : Blo 2265435 2267363 := bstep (se 1 (by rfl) ⟨1700522, by rfl⟩ : syracuseStep 2267363 = 3401045) B3401045
theorem B2421257 : Blo 2265435 2421257 := bbase (se 2 (by rfl) ⟨907971, by rfl⟩ : syracuseStep 2421257 = 1815943) (by norm_num)
theorem B6456685 : Blo 2265435 6456685 := bstep (se 3 (by rfl) ⟨1210628, by rfl⟩ : syracuseStep 6456685 = 2421257) B2421257
theorem B8608913 : Blo 2265435 8608913 := bstep (se 2 (by rfl) ⟨3228342, by rfl⟩ : syracuseStep 8608913 = 6456685) B6456685
theorem B5739275 : Blo 2265435 5739275 := bstep (se 1 (by rfl) ⟨4304456, by rfl⟩ : syracuseStep 5739275 = 8608913) B8608913
theorem B3826183 : Blo 2265435 3826183 := bstep (se 1 (by rfl) ⟨2869637, by rfl⟩ : syracuseStep 3826183 = 5739275) B5739275
theorem B5101577 : Blo 2265435 5101577 := bstep (se 2 (by rfl) ⟨1913091, by rfl⟩ : syracuseStep 5101577 = 3826183) B3826183
theorem B3401051 : Blo 2265435 3401051 := bstep (se 1 (by rfl) ⟨2550788, by rfl⟩ : syracuseStep 3401051 = 5101577) B5101577
theorem B2267367 : Blo 2265435 2267367 := bstep (se 1 (by rfl) ⟨1700525, by rfl⟩ : syracuseStep 2267367 = 3401051) B3401051
theorem B2550793 : Blo 2265435 2550793 := bbase (se 2 (by rfl) ⟨956547, by rfl⟩ : syracuseStep 2550793 = 1913095) (by norm_num)
theorem B3401057 : Blo 2265435 3401057 := bstep (se 2 (by rfl) ⟨1275396, by rfl⟩ : syracuseStep 3401057 = 2550793) B2550793
theorem B2267371 : Blo 2265435 2267371 := bstep (se 1 (by rfl) ⟨1700528, by rfl⟩ : syracuseStep 2267371 = 3401057) B3401057
theorem B14926709 : Blo 2265435 14926709 := bbase (se 5 (by rfl) ⟨699689, by rfl⟩ : syracuseStep 14926709 = 1399379) (by norm_num)
theorem B9951139 : Blo 2265435 9951139 := bstep (se 1 (by rfl) ⟨7463354, by rfl⟩ : syracuseStep 9951139 = 14926709) B14926709
theorem B13268185 : Blo 2265435 13268185 := bstep (se 2 (by rfl) ⟨4975569, by rfl⟩ : syracuseStep 13268185 = 9951139) B9951139
theorem B70763653 : Blo 2265435 70763653 := bstep (se 4 (by rfl) ⟨6634092, by rfl⟩ : syracuseStep 70763653 = 13268185) B13268185
theorem B94351537 : Blo 2265435 94351537 := bstep (se 2 (by rfl) ⟨35381826, by rfl⟩ : syracuseStep 94351537 = 70763653) B70763653
theorem B503208197 : Blo 2265435 503208197 := bstep (se 4 (by rfl) ⟨47175768, by rfl⟩ : syracuseStep 503208197 = 94351537) B94351537
theorem B335472131 : Blo 2265435 335472131 := bstep (se 1 (by rfl) ⟨251604098, by rfl⟩ : syracuseStep 335472131 = 503208197) B503208197
theorem B894592349 : Blo 2265435 894592349 := bstep (se 3 (by rfl) ⟨167736065, by rfl⟩ : syracuseStep 894592349 = 335472131) B335472131
theorem B596394899 : Blo 2265435 596394899 := bstep (se 1 (by rfl) ⟨447296174, by rfl⟩ : syracuseStep 596394899 = 894592349) B894592349
theorem B397596599 : Blo 2265435 397596599 := bstep (se 1 (by rfl) ⟨298197449, by rfl⟩ : syracuseStep 397596599 = 596394899) B596394899
theorem B265064399 : Blo 2265435 265064399 := bstep (se 1 (by rfl) ⟨198798299, by rfl⟩ : syracuseStep 265064399 = 397596599) B397596599
theorem B176709599 : Blo 2265435 176709599 := bstep (se 1 (by rfl) ⟨132532199, by rfl⟩ : syracuseStep 176709599 = 265064399) B265064399
theorem B117806399 : Blo 2265435 117806399 := bstep (se 1 (by rfl) ⟨88354799, by rfl⟩ : syracuseStep 117806399 = 176709599) B176709599
theorem B78537599 : Blo 2265435 78537599 := bstep (se 1 (by rfl) ⟨58903199, by rfl⟩ : syracuseStep 78537599 = 117806399) B117806399
theorem B52358399 : Blo 2265435 52358399 := bstep (se 1 (by rfl) ⟨39268799, by rfl⟩ : syracuseStep 52358399 = 78537599) B78537599
theorem B34905599 : Blo 2265435 34905599 := bstep (se 1 (by rfl) ⟨26179199, by rfl⟩ : syracuseStep 34905599 = 52358399) B52358399
theorem B23270399 : Blo 2265435 23270399 := bstep (se 1 (by rfl) ⟨17452799, by rfl⟩ : syracuseStep 23270399 = 34905599) B34905599
theorem B15513599 : Blo 2265435 15513599 := bstep (se 1 (by rfl) ⟨11635199, by rfl⟩ : syracuseStep 15513599 = 23270399) B23270399
theorem B10342399 : Blo 2265435 10342399 := bstep (se 1 (by rfl) ⟨7756799, by rfl⟩ : syracuseStep 10342399 = 15513599) B15513599
theorem B13789865 : Blo 2265435 13789865 := bstep (se 2 (by rfl) ⟨5171199, by rfl⟩ : syracuseStep 13789865 = 10342399) B10342399
theorem B9193243 : Blo 2265435 9193243 := bstep (se 1 (by rfl) ⟨6894932, by rfl⟩ : syracuseStep 9193243 = 13789865) B13789865
theorem B12257657 : Blo 2265435 12257657 := bstep (se 2 (by rfl) ⟨4596621, by rfl⟩ : syracuseStep 12257657 = 9193243) B9193243
theorem B8171771 : Blo 2265435 8171771 := bstep (se 1 (by rfl) ⟨6128828, by rfl⟩ : syracuseStep 8171771 = 12257657) B12257657
theorem B21791389 : Blo 2265435 21791389 := bstep (se 3 (by rfl) ⟨4085885, by rfl⟩ : syracuseStep 21791389 = 8171771) B8171771
theorem B29055185 : Blo 2265435 29055185 := bstep (se 2 (by rfl) ⟨10895694, by rfl⟩ : syracuseStep 29055185 = 21791389) B21791389
theorem B19370123 : Blo 2265435 19370123 := bstep (se 1 (by rfl) ⟨14527592, by rfl⟩ : syracuseStep 19370123 = 29055185) B29055185
theorem B12913415 : Blo 2265435 12913415 := bstep (se 1 (by rfl) ⟨9685061, by rfl⟩ : syracuseStep 12913415 = 19370123) B19370123
theorem B8608943 : Blo 2265435 8608943 := bstep (se 1 (by rfl) ⟨6456707, by rfl⟩ : syracuseStep 8608943 = 12913415) B12913415
theorem B5739295 : Blo 2265435 5739295 := bstep (se 1 (by rfl) ⟨4304471, by rfl⟩ : syracuseStep 5739295 = 8608943) B8608943
theorem B7652393 : Blo 2265435 7652393 := bstep (se 2 (by rfl) ⟨2869647, by rfl⟩ : syracuseStep 7652393 = 5739295) B5739295
theorem B5101595 : Blo 2265435 5101595 := bstep (se 1 (by rfl) ⟨3826196, by rfl⟩ : syracuseStep 5101595 = 7652393) B7652393
theorem B3401063 : Blo 2265435 3401063 := bstep (se 1 (by rfl) ⟨2550797, by rfl⟩ : syracuseStep 3401063 = 5101595) B5101595
theorem B2267375 : Blo 2265435 2267375 := bstep (se 1 (by rfl) ⟨1700531, by rfl⟩ : syracuseStep 2267375 = 3401063) B3401063
theorem B3401069 : Blo 2265435 3401069 := bbase (se 3 (by rfl) ⟨637700, by rfl⟩ : syracuseStep 3401069 = 1275401) (by norm_num)
theorem B2267379 : Blo 2265435 2267379 := bstep (se 1 (by rfl) ⟨1700534, by rfl⟩ : syracuseStep 2267379 = 3401069) B3401069
theorem B5101613 : Blo 2265435 5101613 := bbase (se 3 (by rfl) ⟨956552, by rfl⟩ : syracuseStep 5101613 = 1913105) (by norm_num)
theorem B3401075 : Blo 2265435 3401075 := bstep (se 1 (by rfl) ⟨2550806, by rfl⟩ : syracuseStep 3401075 = 5101613) B5101613
theorem B2267383 : Blo 2265435 2267383 := bstep (se 1 (by rfl) ⟨1700537, by rfl⟩ : syracuseStep 2267383 = 3401075) B3401075
theorem B6544837 : Blo 2265435 6544837 := bbase (se 4 (by rfl) ⟨613578, by rfl⟩ : syracuseStep 6544837 = 1227157) (by norm_num)
theorem B8726449 : Blo 2265435 8726449 := bstep (se 2 (by rfl) ⟨3272418, by rfl⟩ : syracuseStep 8726449 = 6544837) B6544837
theorem B11635265 : Blo 2265435 11635265 := bstep (se 2 (by rfl) ⟨4363224, by rfl⟩ : syracuseStep 11635265 = 8726449) B8726449
theorem B7756843 : Blo 2265435 7756843 := bstep (se 1 (by rfl) ⟨5817632, by rfl⟩ : syracuseStep 7756843 = 11635265) B11635265
theorem B10342457 : Blo 2265435 10342457 := bstep (se 2 (by rfl) ⟨3878421, by rfl⟩ : syracuseStep 10342457 = 7756843) B7756843
theorem B6894971 : Blo 2265435 6894971 := bstep (se 1 (by rfl) ⟨5171228, by rfl⟩ : syracuseStep 6894971 = 10342457) B10342457
theorem B4596647 : Blo 2265435 4596647 := bstep (se 1 (by rfl) ⟨3447485, by rfl⟩ : syracuseStep 4596647 = 6894971) B6894971
theorem B12257725 : Blo 2265435 12257725 := bstep (se 3 (by rfl) ⟨2298323, by rfl⟩ : syracuseStep 12257725 = 4596647) B4596647
theorem B16343633 : Blo 2265435 16343633 := bstep (se 2 (by rfl) ⟨6128862, by rfl⟩ : syracuseStep 16343633 = 12257725) B12257725
theorem B10895755 : Blo 2265435 10895755 := bstep (se 1 (by rfl) ⟨8171816, by rfl⟩ : syracuseStep 10895755 = 16343633) B16343633
theorem B14527673 : Blo 2265435 14527673 := bstep (se 2 (by rfl) ⟨5447877, by rfl⟩ : syracuseStep 14527673 = 10895755) B10895755
theorem B9685115 : Blo 2265435 9685115 := bstep (se 1 (by rfl) ⟨7263836, by rfl⟩ : syracuseStep 9685115 = 14527673) B14527673
theorem B6456743 : Blo 2265435 6456743 := bstep (se 1 (by rfl) ⟨4842557, by rfl⟩ : syracuseStep 6456743 = 9685115) B9685115
theorem B4304495 : Blo 2265435 4304495 := bstep (se 1 (by rfl) ⟨3228371, by rfl⟩ : syracuseStep 4304495 = 6456743) B6456743
theorem B2869663 : Blo 2265435 2869663 := bstep (se 1 (by rfl) ⟨2152247, by rfl⟩ : syracuseStep 2869663 = 4304495) B4304495
theorem B3826217 : Blo 2265435 3826217 := bstep (se 2 (by rfl) ⟨1434831, by rfl⟩ : syracuseStep 3826217 = 2869663) B2869663
theorem B2550811 : Blo 2265435 2550811 := bstep (se 1 (by rfl) ⟨1913108, by rfl⟩ : syracuseStep 2550811 = 3826217) B3826217
theorem B3401081 : Blo 2265435 3401081 := bstep (se 2 (by rfl) ⟨1275405, by rfl⟩ : syracuseStep 3401081 = 2550811) B2550811
theorem B2267387 : Blo 2265435 2267387 := bstep (se 1 (by rfl) ⟨1700540, by rfl⟩ : syracuseStep 2267387 = 3401081) B3401081
theorem B49699925 : Blo 2265435 49699925 := bbase (se 8 (by rfl) ⟨291210, by rfl⟩ : syracuseStep 49699925 = 582421) (by norm_num)
theorem B33133283 : Blo 2265435 33133283 := bstep (se 1 (by rfl) ⟨24849962, by rfl⟩ : syracuseStep 33133283 = 49699925) B49699925
theorem B22088855 : Blo 2265435 22088855 := bstep (se 1 (by rfl) ⟨16566641, by rfl⟩ : syracuseStep 22088855 = 33133283) B33133283
theorem B14725903 : Blo 2265435 14725903 := bstep (se 1 (by rfl) ⟨11044427, by rfl⟩ : syracuseStep 14725903 = 22088855) B22088855
theorem B19634537 : Blo 2265435 19634537 := bstep (se 2 (by rfl) ⟨7362951, by rfl⟩ : syracuseStep 19634537 = 14725903) B14725903
theorem B13089691 : Blo 2265435 13089691 := bstep (se 1 (by rfl) ⟨9817268, by rfl⟩ : syracuseStep 13089691 = 19634537) B19634537
theorem B17452921 : Blo 2265435 17452921 := bstep (se 2 (by rfl) ⟨6544845, by rfl⟩ : syracuseStep 17452921 = 13089691) B13089691
theorem B23270561 : Blo 2265435 23270561 := bstep (se 2 (by rfl) ⟨8726460, by rfl⟩ : syracuseStep 23270561 = 17452921) B17452921
theorem B15513707 : Blo 2265435 15513707 := bstep (se 1 (by rfl) ⟨11635280, by rfl⟩ : syracuseStep 15513707 = 23270561) B23270561
theorem B41369885 : Blo 2265435 41369885 := bstep (se 3 (by rfl) ⟨7756853, by rfl⟩ : syracuseStep 41369885 = 15513707) B15513707
theorem B27579923 : Blo 2265435 27579923 := bstep (se 1 (by rfl) ⟨20684942, by rfl⟩ : syracuseStep 27579923 = 41369885) B41369885
theorem B18386615 : Blo 2265435 18386615 := bstep (se 1 (by rfl) ⟨13789961, by rfl⟩ : syracuseStep 18386615 = 27579923) B27579923
theorem B12257743 : Blo 2265435 12257743 := bstep (se 1 (by rfl) ⟨9193307, by rfl⟩ : syracuseStep 12257743 = 18386615) B18386615
theorem B16343657 : Blo 2265435 16343657 := bstep (se 2 (by rfl) ⟨6128871, by rfl⟩ : syracuseStep 16343657 = 12257743) B12257743
theorem B10895771 : Blo 2265435 10895771 := bstep (se 1 (by rfl) ⟨8171828, by rfl⟩ : syracuseStep 10895771 = 16343657) B16343657
theorem B7263847 : Blo 2265435 7263847 := bstep (se 1 (by rfl) ⟨5447885, by rfl⟩ : syracuseStep 7263847 = 10895771) B10895771
theorem B38740517 : Blo 2265435 38740517 := bstep (se 4 (by rfl) ⟨3631923, by rfl⟩ : syracuseStep 38740517 = 7263847) B7263847
theorem B25827011 : Blo 2265435 25827011 := bstep (se 1 (by rfl) ⟨19370258, by rfl⟩ : syracuseStep 25827011 = 38740517) B38740517
theorem B17218007 : Blo 2265435 17218007 := bstep (se 1 (by rfl) ⟨12913505, by rfl⟩ : syracuseStep 17218007 = 25827011) B25827011
theorem B11478671 : Blo 2265435 11478671 := bstep (se 1 (by rfl) ⟨8609003, by rfl⟩ : syracuseStep 11478671 = 17218007) B17218007
theorem B7652447 : Blo 2265435 7652447 := bstep (se 1 (by rfl) ⟨5739335, by rfl⟩ : syracuseStep 7652447 = 11478671) B11478671
theorem B5101631 : Blo 2265435 5101631 := bstep (se 1 (by rfl) ⟨3826223, by rfl⟩ : syracuseStep 5101631 = 7652447) B7652447
theorem B3401087 : Blo 2265435 3401087 := bstep (se 1 (by rfl) ⟨2550815, by rfl⟩ : syracuseStep 3401087 = 5101631) B5101631
theorem B2267391 : Blo 2265435 2267391 := bstep (se 1 (by rfl) ⟨1700543, by rfl⟩ : syracuseStep 2267391 = 3401087) B3401087
theorem B3401093 : Blo 2265435 3401093 := bbase (se 4 (by rfl) ⟨318852, by rfl⟩ : syracuseStep 3401093 = 637705) (by norm_num)
theorem B2267395 : Blo 2265435 2267395 := bstep (se 1 (by rfl) ⟨1700546, by rfl⟩ : syracuseStep 2267395 = 3401093) B3401093
theorem B3826237 : Blo 2265435 3826237 := bbase (se 3 (by rfl) ⟨717419, by rfl⟩ : syracuseStep 3826237 = 1434839) (by norm_num)
theorem B5101649 : Blo 2265435 5101649 := bstep (se 2 (by rfl) ⟨1913118, by rfl⟩ : syracuseStep 5101649 = 3826237) B3826237
theorem B3401099 : Blo 2265435 3401099 := bstep (se 1 (by rfl) ⟨2550824, by rfl⟩ : syracuseStep 3401099 = 5101649) B5101649
theorem B2267399 : Blo 2265435 2267399 := bstep (se 1 (by rfl) ⟨1700549, by rfl⟩ : syracuseStep 2267399 = 3401099) B3401099
theorem B2550829 : Blo 2265435 2550829 := bbase (se 3 (by rfl) ⟨478280, by rfl⟩ : syracuseStep 2550829 = 956561) (by norm_num)
theorem B3401105 : Blo 2265435 3401105 := bstep (se 2 (by rfl) ⟨1275414, by rfl⟩ : syracuseStep 3401105 = 2550829) B2550829
theorem B2267403 : Blo 2265435 2267403 := bstep (se 1 (by rfl) ⟨1700552, by rfl⟩ : syracuseStep 2267403 = 3401105) B3401105
theorem B7652501 : Blo 2265435 7652501 := bbase (se 6 (by rfl) ⟨179355, by rfl⟩ : syracuseStep 7652501 = 358711) (by norm_num)
theorem B5101667 : Blo 2265435 5101667 := bstep (se 1 (by rfl) ⟨3826250, by rfl⟩ : syracuseStep 5101667 = 7652501) B7652501
theorem B3401111 : Blo 2265435 3401111 := bstep (se 1 (by rfl) ⟨2550833, by rfl⟩ : syracuseStep 3401111 = 5101667) B5101667
theorem B2267407 : Blo 2265435 2267407 := bstep (se 1 (by rfl) ⟨1700555, by rfl⟩ : syracuseStep 2267407 = 3401111) B3401111
theorem B3401117 : Blo 2265435 3401117 := bbase (se 3 (by rfl) ⟨637709, by rfl⟩ : syracuseStep 3401117 = 1275419) (by norm_num)
theorem B2267411 : Blo 2265435 2267411 := bstep (se 1 (by rfl) ⟨1700558, by rfl⟩ : syracuseStep 2267411 = 3401117) B3401117
theorem B5101685 : Blo 2265435 5101685 := bbase (se 5 (by rfl) ⟨239141, by rfl⟩ : syracuseStep 5101685 = 478283) (by norm_num)
theorem B3401123 : Blo 2265435 3401123 := bstep (se 1 (by rfl) ⟨2550842, by rfl⟩ : syracuseStep 3401123 = 5101685) B5101685
theorem B2267415 : Blo 2265435 2267415 := bstep (se 1 (by rfl) ⟨1700561, by rfl⟩ : syracuseStep 2267415 = 3401123) B3401123
theorem B2723977 : Blo 2265435 2723977 := bbase (se 2 (by rfl) ⟨1021491, by rfl⟩ : syracuseStep 2723977 = 2042983) (by norm_num)
theorem B3631969 : Blo 2265435 3631969 := bstep (se 2 (by rfl) ⟨1361988, by rfl⟩ : syracuseStep 3631969 = 2723977) B2723977
theorem B19370501 : Blo 2265435 19370501 := bstep (se 4 (by rfl) ⟨1815984, by rfl⟩ : syracuseStep 19370501 = 3631969) B3631969
theorem B12913667 : Blo 2265435 12913667 := bstep (se 1 (by rfl) ⟨9685250, by rfl⟩ : syracuseStep 12913667 = 19370501) B19370501
theorem B8609111 : Blo 2265435 8609111 := bstep (se 1 (by rfl) ⟨6456833, by rfl⟩ : syracuseStep 8609111 = 12913667) B12913667
theorem B5739407 : Blo 2265435 5739407 := bstep (se 1 (by rfl) ⟨4304555, by rfl⟩ : syracuseStep 5739407 = 8609111) B8609111
theorem B3826271 : Blo 2265435 3826271 := bstep (se 1 (by rfl) ⟨2869703, by rfl⟩ : syracuseStep 3826271 = 5739407) B5739407
theorem B2550847 : Blo 2265435 2550847 := bstep (se 1 (by rfl) ⟨1913135, by rfl⟩ : syracuseStep 2550847 = 3826271) B3826271
theorem B3401129 : Blo 2265435 3401129 := bstep (se 2 (by rfl) ⟨1275423, by rfl⟩ : syracuseStep 3401129 = 2550847) B2550847
theorem B2267419 : Blo 2265435 2267419 := bstep (se 1 (by rfl) ⟨1700564, by rfl⟩ : syracuseStep 2267419 = 3401129) B3401129
theorem B8609125 : Blo 2265435 8609125 := bbase (se 4 (by rfl) ⟨807105, by rfl⟩ : syracuseStep 8609125 = 1614211) (by norm_num)
theorem B11478833 : Blo 2265435 11478833 := bstep (se 2 (by rfl) ⟨4304562, by rfl⟩ : syracuseStep 11478833 = 8609125) B8609125
theorem B7652555 : Blo 2265435 7652555 := bstep (se 1 (by rfl) ⟨5739416, by rfl⟩ : syracuseStep 7652555 = 11478833) B11478833
theorem B5101703 : Blo 2265435 5101703 := bstep (se 1 (by rfl) ⟨3826277, by rfl⟩ : syracuseStep 5101703 = 7652555) B7652555
theorem B3401135 : Blo 2265435 3401135 := bstep (se 1 (by rfl) ⟨2550851, by rfl⟩ : syracuseStep 3401135 = 5101703) B5101703
theorem B2267423 : Blo 2265435 2267423 := bstep (se 1 (by rfl) ⟨1700567, by rfl⟩ : syracuseStep 2267423 = 3401135) B3401135
theorem B3401141 : Blo 2265435 3401141 := bbase (se 5 (by rfl) ⟨159428, by rfl⟩ : syracuseStep 3401141 = 318857) (by norm_num)
theorem B2267427 : Blo 2265435 2267427 := bstep (se 1 (by rfl) ⟨1700570, by rfl⟩ : syracuseStep 2267427 = 3401141) B3401141
theorem B5739437 : Blo 2265435 5739437 := bbase (se 3 (by rfl) ⟨1076144, by rfl⟩ : syracuseStep 5739437 = 2152289) (by norm_num)
theorem B3826291 : Blo 2265435 3826291 := bstep (se 1 (by rfl) ⟨2869718, by rfl⟩ : syracuseStep 3826291 = 5739437) B5739437
theorem B5101721 : Blo 2265435 5101721 := bstep (se 2 (by rfl) ⟨1913145, by rfl⟩ : syracuseStep 5101721 = 3826291) B3826291
theorem B3401147 : Blo 2265435 3401147 := bstep (se 1 (by rfl) ⟨2550860, by rfl⟩ : syracuseStep 3401147 = 5101721) B5101721
theorem B2267431 : Blo 2265435 2267431 := bstep (se 1 (by rfl) ⟨1700573, by rfl⟩ : syracuseStep 2267431 = 3401147) B3401147
theorem B2550865 : Blo 2265435 2550865 := bbase (se 2 (by rfl) ⟨956574, by rfl⟩ : syracuseStep 2550865 = 1913149) (by norm_num)
theorem B3401153 : Blo 2265435 3401153 := bstep (se 2 (by rfl) ⟨1275432, by rfl⟩ : syracuseStep 3401153 = 2550865) B2550865
theorem B2267435 : Blo 2265435 2267435 := bstep (se 1 (by rfl) ⟨1700576, by rfl⟩ : syracuseStep 2267435 = 3401153) B3401153
theorem C0 (j : ℕ) (h1 : 566358 ≤ j) (h2 : j ≤ 566858) : Blo 2265435 (4 * j + 3) := by
  interval_cases j
  · exact B2265435
  · exact B2265439
  · exact B2265443
  · exact B2265447
  · exact B2265451
  · exact B2265455
  · exact B2265459
  · exact B2265463
  · exact B2265467
  · exact B2265471
  · exact B2265475
  · exact B2265479
  · exact B2265483
  · exact B2265487
  · exact B2265491
  · exact B2265495
  · exact B2265499
  · exact B2265503
  · exact B2265507
  · exact B2265511
  · exact B2265515
  · exact B2265519
  · exact B2265523
  · exact B2265527
  · exact B2265531
  · exact B2265535
  · exact B2265539
  · exact B2265543
  · exact B2265547
  · exact B2265551
  · exact B2265555
  · exact B2265559
  · exact B2265563
  · exact B2265567
  · exact B2265571
  · exact B2265575
  · exact B2265579
  · exact B2265583
  · exact B2265587
  · exact B2265591
  · exact B2265595
  · exact B2265599
  · exact B2265603
  · exact B2265607
  · exact B2265611
  · exact B2265615
  · exact B2265619
  · exact B2265623
  · exact B2265627
  · exact B2265631
  · exact B2265635
  · exact B2265639
  · exact B2265643
  · exact B2265647
  · exact B2265651
  · exact B2265655
  · exact B2265659
  · exact B2265663
  · exact B2265667
  · exact B2265671
  · exact B2265675
  · exact B2265679
  · exact B2265683
  · exact B2265687
  · exact B2265691
  · exact B2265695
  · exact B2265699
  · exact B2265703
  · exact B2265707
  · exact B2265711
  · exact B2265715
  · exact B2265719
  · exact B2265723
  · exact B2265727
  · exact B2265731
  · exact B2265735
  · exact B2265739
  · exact B2265743
  · exact B2265747
  · exact B2265751
  · exact B2265755
  · exact B2265759
  · exact B2265763
  · exact B2265767
  · exact B2265771
  · exact B2265775
  · exact B2265779
  · exact B2265783
  · exact B2265787
  · exact B2265791
  · exact B2265795
  · exact B2265799
  · exact B2265803
  · exact B2265807
  · exact B2265811
  · exact B2265815
  · exact B2265819
  · exact B2265823
  · exact B2265827
  · exact B2265831
  · exact B2265835
  · exact B2265839
  · exact B2265843
  · exact B2265847
  · exact B2265851
  · exact B2265855
  · exact B2265859
  · exact B2265863
  · exact B2265867
  · exact B2265871
  · exact B2265875
  · exact B2265879
  · exact B2265883
  · exact B2265887
  · exact B2265891
  · exact B2265895
  · exact B2265899
  · exact B2265903
  · exact B2265907
  · exact B2265911
  · exact B2265915
  · exact B2265919
  · exact B2265923
  · exact B2265927
  · exact B2265931
  · exact B2265935
  · exact B2265939
  · exact B2265943
  · exact B2265947
  · exact B2265951
  · exact B2265955
  · exact B2265959
  · exact B2265963
  · exact B2265967
  · exact B2265971
  · exact B2265975
  · exact B2265979
  · exact B2265983
  · exact B2265987
  · exact B2265991
  · exact B2265995
  · exact B2265999
  · exact B2266003
  · exact B2266007
  · exact B2266011
  · exact B2266015
  · exact B2266019
  · exact B2266023
  · exact B2266027
  · exact B2266031
  · exact B2266035
  · exact B2266039
  · exact B2266043
  · exact B2266047
  · exact B2266051
  · exact B2266055
  · exact B2266059
  · exact B2266063
  · exact B2266067
  · exact B2266071
  · exact B2266075
  · exact B2266079
  · exact B2266083
  · exact B2266087
  · exact B2266091
  · exact B2266095
  · exact B2266099
  · exact B2266103
  · exact B2266107
  · exact B2266111
  · exact B2266115
  · exact B2266119
  · exact B2266123
  · exact B2266127
  · exact B2266131
  · exact B2266135
  · exact B2266139
  · exact B2266143
  · exact B2266147
  · exact B2266151
  · exact B2266155
  · exact B2266159
  · exact B2266163
  · exact B2266167
  · exact B2266171
  · exact B2266175
  · exact B2266179
  · exact B2266183
  · exact B2266187
  · exact B2266191
  · exact B2266195
  · exact B2266199
  · exact B2266203
  · exact B2266207
  · exact B2266211
  · exact B2266215
  · exact B2266219
  · exact B2266223
  · exact B2266227
  · exact B2266231
  · exact B2266235
  · exact B2266239
  · exact B2266243
  · exact B2266247
  · exact B2266251
  · exact B2266255
  · exact B2266259
  · exact B2266263
  · exact B2266267
  · exact B2266271
  · exact B2266275
  · exact B2266279
  · exact B2266283
  · exact B2266287
  · exact B2266291
  · exact B2266295
  · exact B2266299
  · exact B2266303
  · exact B2266307
  · exact B2266311
  · exact B2266315
  · exact B2266319
  · exact B2266323
  · exact B2266327
  · exact B2266331
  · exact B2266335
  · exact B2266339
  · exact B2266343
  · exact B2266347
  · exact B2266351
  · exact B2266355
  · exact B2266359
  · exact B2266363
  · exact B2266367
  · exact B2266371
  · exact B2266375
  · exact B2266379
  · exact B2266383
  · exact B2266387
  · exact B2266391
  · exact B2266395
  · exact B2266399
  · exact B2266403
  · exact B2266407
  · exact B2266411
  · exact B2266415
  · exact B2266419
  · exact B2266423
  · exact B2266427
  · exact B2266431
  · exact B2266435
  · exact B2266439
  · exact B2266443
  · exact B2266447
  · exact B2266451
  · exact B2266455
  · exact B2266459
  · exact B2266463
  · exact B2266467
  · exact B2266471
  · exact B2266475
  · exact B2266479
  · exact B2266483
  · exact B2266487
  · exact B2266491
  · exact B2266495
  · exact B2266499
  · exact B2266503
  · exact B2266507
  · exact B2266511
  · exact B2266515
  · exact B2266519
  · exact B2266523
  · exact B2266527
  · exact B2266531
  · exact B2266535
  · exact B2266539
  · exact B2266543
  · exact B2266547
  · exact B2266551
  · exact B2266555
  · exact B2266559
  · exact B2266563
  · exact B2266567
  · exact B2266571
  · exact B2266575
  · exact B2266579
  · exact B2266583
  · exact B2266587
  · exact B2266591
  · exact B2266595
  · exact B2266599
  · exact B2266603
  · exact B2266607
  · exact B2266611
  · exact B2266615
  · exact B2266619
  · exact B2266623
  · exact B2266627
  · exact B2266631
  · exact B2266635
  · exact B2266639
  · exact B2266643
  · exact B2266647
  · exact B2266651
  · exact B2266655
  · exact B2266659
  · exact B2266663
  · exact B2266667
  · exact B2266671
  · exact B2266675
  · exact B2266679
  · exact B2266683
  · exact B2266687
  · exact B2266691
  · exact B2266695
  · exact B2266699
  · exact B2266703
  · exact B2266707
  · exact B2266711
  · exact B2266715
  · exact B2266719
  · exact B2266723
  · exact B2266727
  · exact B2266731
  · exact B2266735
  · exact B2266739
  · exact B2266743
  · exact B2266747
  · exact B2266751
  · exact B2266755
  · exact B2266759
  · exact B2266763
  · exact B2266767
  · exact B2266771
  · exact B2266775
  · exact B2266779
  · exact B2266783
  · exact B2266787
  · exact B2266791
  · exact B2266795
  · exact B2266799
  · exact B2266803
  · exact B2266807
  · exact B2266811
  · exact B2266815
  · exact B2266819
  · exact B2266823
  · exact B2266827
  · exact B2266831
  · exact B2266835
  · exact B2266839
  · exact B2266843
  · exact B2266847
  · exact B2266851
  · exact B2266855
  · exact B2266859
  · exact B2266863
  · exact B2266867
  · exact B2266871
  · exact B2266875
  · exact B2266879
  · exact B2266883
  · exact B2266887
  · exact B2266891
  · exact B2266895
  · exact B2266899
  · exact B2266903
  · exact B2266907
  · exact B2266911
  · exact B2266915
  · exact B2266919
  · exact B2266923
  · exact B2266927
  · exact B2266931
  · exact B2266935
  · exact B2266939
  · exact B2266943
  · exact B2266947
  · exact B2266951
  · exact B2266955
  · exact B2266959
  · exact B2266963
  · exact B2266967
  · exact B2266971
  · exact B2266975
  · exact B2266979
  · exact B2266983
  · exact B2266987
  · exact B2266991
  · exact B2266995
  · exact B2266999
  · exact B2267003
  · exact B2267007
  · exact B2267011
  · exact B2267015
  · exact B2267019
  · exact B2267023
  · exact B2267027
  · exact B2267031
  · exact B2267035
  · exact B2267039
  · exact B2267043
  · exact B2267047
  · exact B2267051
  · exact B2267055
  · exact B2267059
  · exact B2267063
  · exact B2267067
  · exact B2267071
  · exact B2267075
  · exact B2267079
  · exact B2267083
  · exact B2267087
  · exact B2267091
  · exact B2267095
  · exact B2267099
  · exact B2267103
  · exact B2267107
  · exact B2267111
  · exact B2267115
  · exact B2267119
  · exact B2267123
  · exact B2267127
  · exact B2267131
  · exact B2267135
  · exact B2267139
  · exact B2267143
  · exact B2267147
  · exact B2267151
  · exact B2267155
  · exact B2267159
  · exact B2267163
  · exact B2267167
  · exact B2267171
  · exact B2267175
  · exact B2267179
  · exact B2267183
  · exact B2267187
  · exact B2267191
  · exact B2267195
  · exact B2267199
  · exact B2267203
  · exact B2267207
  · exact B2267211
  · exact B2267215
  · exact B2267219
  · exact B2267223
  · exact B2267227
  · exact B2267231
  · exact B2267235
  · exact B2267239
  · exact B2267243
  · exact B2267247
  · exact B2267251
  · exact B2267255
  · exact B2267259
  · exact B2267263
  · exact B2267267
  · exact B2267271
  · exact B2267275
  · exact B2267279
  · exact B2267283
  · exact B2267287
  · exact B2267291
  · exact B2267295
  · exact B2267299
  · exact B2267303
  · exact B2267307
  · exact B2267311
  · exact B2267315
  · exact B2267319
  · exact B2267323
  · exact B2267327
  · exact B2267331
  · exact B2267335
  · exact B2267339
  · exact B2267343
  · exact B2267347
  · exact B2267351
  · exact B2267355
  · exact B2267359
  · exact B2267363
  · exact B2267367
  · exact B2267371
  · exact B2267375
  · exact B2267379
  · exact B2267383
  · exact B2267387
  · exact B2267391
  · exact B2267395
  · exact B2267399
  · exact B2267403
  · exact B2267407
  · exact B2267411
  · exact B2267415
  · exact B2267419
  · exact B2267423
  · exact B2267427
  · exact B2267431
  · exact B2267435
theorem solution (m : ℕ) (hlo : 2265435 ≤ m) (hhi : m ≤ 2267435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 566358 ≤ j := by omega
    have hj2 : j ≤ 566858 := by omega
    have hb : Blo 2265435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
