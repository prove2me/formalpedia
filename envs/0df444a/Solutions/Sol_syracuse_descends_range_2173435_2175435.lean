-- Prove2me | solution 1 for syracuse_descends_range_2173435_2175435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:49.82253+00:00
-- url     : https://prove2.me/submissions/b2991ddc-58a1-433a-b1eb-4b7822e88125

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

theorem B4126133 : Blo 2173435 4126133 := bbase (se 5 (by rfl) ⟨193412, by rfl⟩ : syracuseStep 4126133 = 386825) (by norm_num)
theorem B2750755 : Blo 2173435 2750755 := bstep (se 1 (by rfl) ⟨2063066, by rfl⟩ : syracuseStep 2750755 = 4126133) B4126133
theorem B3667673 : Blo 2173435 3667673 := bstep (se 2 (by rfl) ⟨1375377, by rfl⟩ : syracuseStep 3667673 = 2750755) B2750755
theorem B2445115 : Blo 2173435 2445115 := bstep (se 1 (by rfl) ⟨1833836, by rfl⟩ : syracuseStep 2445115 = 3667673) B3667673
theorem B3260153 : Blo 2173435 3260153 := bstep (se 2 (by rfl) ⟨1222557, by rfl⟩ : syracuseStep 3260153 = 2445115) B2445115
theorem B2173435 : Blo 2173435 2173435 := bstep (se 1 (by rfl) ⟨1630076, by rfl⟩ : syracuseStep 2173435 = 3260153) B3260153
theorem B10586789 : Blo 2173435 10586789 := bbase (se 4 (by rfl) ⟨992511, by rfl⟩ : syracuseStep 10586789 = 1985023) (by norm_num)
theorem B7057859 : Blo 2173435 7057859 := bstep (se 1 (by rfl) ⟨5293394, by rfl⟩ : syracuseStep 7057859 = 10586789) B10586789
theorem B18820957 : Blo 2173435 18820957 := bstep (se 3 (by rfl) ⟨3528929, by rfl⟩ : syracuseStep 18820957 = 7057859) B7057859
theorem B25094609 : Blo 2173435 25094609 := bstep (se 2 (by rfl) ⟨9410478, by rfl⟩ : syracuseStep 25094609 = 18820957) B18820957
theorem B16729739 : Blo 2173435 16729739 := bstep (se 1 (by rfl) ⟨12547304, by rfl⟩ : syracuseStep 16729739 = 25094609) B25094609
theorem B11153159 : Blo 2173435 11153159 := bstep (se 1 (by rfl) ⟨8364869, by rfl⟩ : syracuseStep 11153159 = 16729739) B16729739
theorem B7435439 : Blo 2173435 7435439 := bstep (se 1 (by rfl) ⟨5576579, by rfl⟩ : syracuseStep 7435439 = 11153159) B11153159
theorem B4956959 : Blo 2173435 4956959 := bstep (se 1 (by rfl) ⟨3717719, by rfl⟩ : syracuseStep 4956959 = 7435439) B7435439
theorem B13218557 : Blo 2173435 13218557 := bstep (se 3 (by rfl) ⟨2478479, by rfl⟩ : syracuseStep 13218557 = 4956959) B4956959
theorem B140997941 : Blo 2173435 140997941 := bstep (se 5 (by rfl) ⟨6609278, by rfl⟩ : syracuseStep 140997941 = 13218557) B13218557
theorem B93998627 : Blo 2173435 93998627 := bstep (se 1 (by rfl) ⟨70498970, by rfl⟩ : syracuseStep 93998627 = 140997941) B140997941
theorem B62665751 : Blo 2173435 62665751 := bstep (se 1 (by rfl) ⟨46999313, by rfl⟩ : syracuseStep 62665751 = 93998627) B93998627
theorem B41777167 : Blo 2173435 41777167 := bstep (se 1 (by rfl) ⟨31332875, by rfl⟩ : syracuseStep 41777167 = 62665751) B62665751
theorem B55702889 : Blo 2173435 55702889 := bstep (se 2 (by rfl) ⟨20888583, by rfl⟩ : syracuseStep 55702889 = 41777167) B41777167
theorem B37135259 : Blo 2173435 37135259 := bstep (se 1 (by rfl) ⟨27851444, by rfl⟩ : syracuseStep 37135259 = 55702889) B55702889
theorem B24756839 : Blo 2173435 24756839 := bstep (se 1 (by rfl) ⟨18567629, by rfl⟩ : syracuseStep 24756839 = 37135259) B37135259
theorem B16504559 : Blo 2173435 16504559 := bstep (se 1 (by rfl) ⟨12378419, by rfl⟩ : syracuseStep 16504559 = 24756839) B24756839
theorem B11003039 : Blo 2173435 11003039 := bstep (se 1 (by rfl) ⟨8252279, by rfl⟩ : syracuseStep 11003039 = 16504559) B16504559
theorem B7335359 : Blo 2173435 7335359 := bstep (se 1 (by rfl) ⟨5501519, by rfl⟩ : syracuseStep 7335359 = 11003039) B11003039
theorem B4890239 : Blo 2173435 4890239 := bstep (se 1 (by rfl) ⟨3667679, by rfl⟩ : syracuseStep 4890239 = 7335359) B7335359
theorem B3260159 : Blo 2173435 3260159 := bstep (se 1 (by rfl) ⟨2445119, by rfl⟩ : syracuseStep 3260159 = 4890239) B4890239
theorem B2173439 : Blo 2173435 2173439 := bstep (se 1 (by rfl) ⟨1630079, by rfl⟩ : syracuseStep 2173439 = 3260159) B3260159
theorem B3260165 : Blo 2173435 3260165 := bbase (se 4 (by rfl) ⟨305640, by rfl⟩ : syracuseStep 3260165 = 611281) (by norm_num)
theorem B2173443 : Blo 2173435 2173443 := bstep (se 1 (by rfl) ⟨1630082, by rfl⟩ : syracuseStep 2173443 = 3260165) B3260165
theorem B3667693 : Blo 2173435 3667693 := bbase (se 3 (by rfl) ⟨687692, by rfl⟩ : syracuseStep 3667693 = 1375385) (by norm_num)
theorem B4890257 : Blo 2173435 4890257 := bstep (se 2 (by rfl) ⟨1833846, by rfl⟩ : syracuseStep 4890257 = 3667693) B3667693
theorem B3260171 : Blo 2173435 3260171 := bstep (se 1 (by rfl) ⟨2445128, by rfl⟩ : syracuseStep 3260171 = 4890257) B4890257
theorem B2173447 : Blo 2173435 2173447 := bstep (se 1 (by rfl) ⟨1630085, by rfl⟩ : syracuseStep 2173447 = 3260171) B3260171
theorem B2445133 : Blo 2173435 2445133 := bbase (se 3 (by rfl) ⟨458462, by rfl⟩ : syracuseStep 2445133 = 916925) (by norm_num)
theorem B3260177 : Blo 2173435 3260177 := bstep (se 2 (by rfl) ⟨1222566, by rfl⟩ : syracuseStep 3260177 = 2445133) B2445133
theorem B2173451 : Blo 2173435 2173451 := bstep (se 1 (by rfl) ⟨1630088, by rfl⟩ : syracuseStep 2173451 = 3260177) B3260177
theorem B7335413 : Blo 2173435 7335413 := bbase (se 5 (by rfl) ⟨343847, by rfl⟩ : syracuseStep 7335413 = 687695) (by norm_num)
theorem B4890275 : Blo 2173435 4890275 := bstep (se 1 (by rfl) ⟨3667706, by rfl⟩ : syracuseStep 4890275 = 7335413) B7335413
theorem B3260183 : Blo 2173435 3260183 := bstep (se 1 (by rfl) ⟨2445137, by rfl⟩ : syracuseStep 3260183 = 4890275) B4890275
theorem B2173455 : Blo 2173435 2173455 := bstep (se 1 (by rfl) ⟨1630091, by rfl⟩ : syracuseStep 2173455 = 3260183) B3260183
theorem B3260189 : Blo 2173435 3260189 := bbase (se 3 (by rfl) ⟨611285, by rfl⟩ : syracuseStep 3260189 = 1222571) (by norm_num)
theorem B2173459 : Blo 2173435 2173459 := bstep (se 1 (by rfl) ⟨1630094, by rfl⟩ : syracuseStep 2173459 = 3260189) B3260189
theorem B4890293 : Blo 2173435 4890293 := bbase (se 5 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 4890293 = 458465) (by norm_num)
theorem B3260195 : Blo 2173435 3260195 := bstep (se 1 (by rfl) ⟨2445146, by rfl⟩ : syracuseStep 3260195 = 4890293) B4890293
theorem B2173463 : Blo 2173435 2173463 := bstep (se 1 (by rfl) ⟨1630097, by rfl⟩ : syracuseStep 2173463 = 3260195) B3260195
theorem B12378581 : Blo 2173435 12378581 := bbase (se 7 (by rfl) ⟨145061, by rfl⟩ : syracuseStep 12378581 = 290123) (by norm_num)
theorem B8252387 : Blo 2173435 8252387 := bstep (se 1 (by rfl) ⟨6189290, by rfl⟩ : syracuseStep 8252387 = 12378581) B12378581
theorem B5501591 : Blo 2173435 5501591 := bstep (se 1 (by rfl) ⟨4126193, by rfl⟩ : syracuseStep 5501591 = 8252387) B8252387
theorem B3667727 : Blo 2173435 3667727 := bstep (se 1 (by rfl) ⟨2750795, by rfl⟩ : syracuseStep 3667727 = 5501591) B5501591
theorem B2445151 : Blo 2173435 2445151 := bstep (se 1 (by rfl) ⟨1833863, by rfl⟩ : syracuseStep 2445151 = 3667727) B3667727
theorem B3260201 : Blo 2173435 3260201 := bstep (se 2 (by rfl) ⟨1222575, by rfl⟩ : syracuseStep 3260201 = 2445151) B2445151
theorem B2173467 : Blo 2173435 2173467 := bstep (se 1 (by rfl) ⟨1630100, by rfl⟩ : syracuseStep 2173467 = 3260201) B3260201
theorem B6189301 : Blo 2173435 6189301 := bbase (se 5 (by rfl) ⟨290123, by rfl⟩ : syracuseStep 6189301 = 580247) (by norm_num)
theorem B8252401 : Blo 2173435 8252401 := bstep (se 2 (by rfl) ⟨3094650, by rfl⟩ : syracuseStep 8252401 = 6189301) B6189301
theorem B11003201 : Blo 2173435 11003201 := bstep (se 2 (by rfl) ⟨4126200, by rfl⟩ : syracuseStep 11003201 = 8252401) B8252401
theorem B7335467 : Blo 2173435 7335467 := bstep (se 1 (by rfl) ⟨5501600, by rfl⟩ : syracuseStep 7335467 = 11003201) B11003201
theorem B4890311 : Blo 2173435 4890311 := bstep (se 1 (by rfl) ⟨3667733, by rfl⟩ : syracuseStep 4890311 = 7335467) B7335467
theorem B3260207 : Blo 2173435 3260207 := bstep (se 1 (by rfl) ⟨2445155, by rfl⟩ : syracuseStep 3260207 = 4890311) B4890311
theorem B2173471 : Blo 2173435 2173471 := bstep (se 1 (by rfl) ⟨1630103, by rfl⟩ : syracuseStep 2173471 = 3260207) B3260207
theorem B3260213 : Blo 2173435 3260213 := bbase (se 5 (by rfl) ⟨152822, by rfl⟩ : syracuseStep 3260213 = 305645) (by norm_num)
theorem B2173475 : Blo 2173435 2173475 := bstep (se 1 (by rfl) ⟨1630106, by rfl⟩ : syracuseStep 2173475 = 3260213) B3260213
theorem B5501621 : Blo 2173435 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B3667747 : Blo 2173435 3667747 := bstep (se 1 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 3667747 = 5501621) B5501621
theorem B4890329 : Blo 2173435 4890329 := bstep (se 2 (by rfl) ⟨1833873, by rfl⟩ : syracuseStep 4890329 = 3667747) B3667747
theorem B3260219 : Blo 2173435 3260219 := bstep (se 1 (by rfl) ⟨2445164, by rfl⟩ : syracuseStep 3260219 = 4890329) B4890329
theorem B2173479 : Blo 2173435 2173479 := bstep (se 1 (by rfl) ⟨1630109, by rfl⟩ : syracuseStep 2173479 = 3260219) B3260219
theorem B2445169 : Blo 2173435 2445169 := bbase (se 2 (by rfl) ⟨916938, by rfl⟩ : syracuseStep 2445169 = 1833877) (by norm_num)
theorem B3260225 : Blo 2173435 3260225 := bstep (se 2 (by rfl) ⟨1222584, by rfl⟩ : syracuseStep 3260225 = 2445169) B2445169
theorem B2173483 : Blo 2173435 2173483 := bstep (se 1 (by rfl) ⟨1630112, by rfl⟩ : syracuseStep 2173483 = 3260225) B3260225
theorem B9284021 : Blo 2173435 9284021 := bbase (se 5 (by rfl) ⟨435188, by rfl⟩ : syracuseStep 9284021 = 870377) (by norm_num)
theorem B6189347 : Blo 2173435 6189347 := bstep (se 1 (by rfl) ⟨4642010, by rfl⟩ : syracuseStep 6189347 = 9284021) B9284021
theorem B4126231 : Blo 2173435 4126231 := bstep (se 1 (by rfl) ⟨3094673, by rfl⟩ : syracuseStep 4126231 = 6189347) B6189347
theorem B5501641 : Blo 2173435 5501641 := bstep (se 2 (by rfl) ⟨2063115, by rfl⟩ : syracuseStep 5501641 = 4126231) B4126231
theorem B7335521 : Blo 2173435 7335521 := bstep (se 2 (by rfl) ⟨2750820, by rfl⟩ : syracuseStep 7335521 = 5501641) B5501641
theorem B4890347 : Blo 2173435 4890347 := bstep (se 1 (by rfl) ⟨3667760, by rfl⟩ : syracuseStep 4890347 = 7335521) B7335521
theorem B3260231 : Blo 2173435 3260231 := bstep (se 1 (by rfl) ⟨2445173, by rfl⟩ : syracuseStep 3260231 = 4890347) B4890347
theorem B2173487 : Blo 2173435 2173487 := bstep (se 1 (by rfl) ⟨1630115, by rfl⟩ : syracuseStep 2173487 = 3260231) B3260231
theorem B3260237 : Blo 2173435 3260237 := bbase (se 3 (by rfl) ⟨611294, by rfl⟩ : syracuseStep 3260237 = 1222589) (by norm_num)
theorem B2173491 : Blo 2173435 2173491 := bstep (se 1 (by rfl) ⟨1630118, by rfl⟩ : syracuseStep 2173491 = 3260237) B3260237
theorem B4890365 : Blo 2173435 4890365 := bbase (se 3 (by rfl) ⟨916943, by rfl⟩ : syracuseStep 4890365 = 1833887) (by norm_num)
theorem B3260243 : Blo 2173435 3260243 := bstep (se 1 (by rfl) ⟨2445182, by rfl⟩ : syracuseStep 3260243 = 4890365) B4890365
theorem B2173495 : Blo 2173435 2173495 := bstep (se 1 (by rfl) ⟨1630121, by rfl⟩ : syracuseStep 2173495 = 3260243) B3260243
theorem B3667781 : Blo 2173435 3667781 := bbase (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) (by norm_num)
theorem B2445187 : Blo 2173435 2445187 := bstep (se 1 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 2445187 = 3667781) B3667781
theorem B3260249 : Blo 2173435 3260249 := bstep (se 2 (by rfl) ⟨1222593, by rfl⟩ : syracuseStep 3260249 = 2445187) B2445187
theorem B2173499 : Blo 2173435 2173499 := bstep (se 1 (by rfl) ⟨1630124, by rfl⟩ : syracuseStep 2173499 = 3260249) B3260249
theorem B16505045 : Blo 2173435 16505045 := bbase (se 7 (by rfl) ⟨193418, by rfl⟩ : syracuseStep 16505045 = 386837) (by norm_num)
theorem B11003363 : Blo 2173435 11003363 := bstep (se 1 (by rfl) ⟨8252522, by rfl⟩ : syracuseStep 11003363 = 16505045) B16505045
theorem B7335575 : Blo 2173435 7335575 := bstep (se 1 (by rfl) ⟨5501681, by rfl⟩ : syracuseStep 7335575 = 11003363) B11003363
theorem B4890383 : Blo 2173435 4890383 := bstep (se 1 (by rfl) ⟨3667787, by rfl⟩ : syracuseStep 4890383 = 7335575) B7335575
theorem B3260255 : Blo 2173435 3260255 := bstep (se 1 (by rfl) ⟨2445191, by rfl⟩ : syracuseStep 3260255 = 4890383) B4890383
theorem B2173503 : Blo 2173435 2173503 := bstep (se 1 (by rfl) ⟨1630127, by rfl⟩ : syracuseStep 2173503 = 3260255) B3260255
theorem B3260261 : Blo 2173435 3260261 := bbase (se 4 (by rfl) ⟨305649, by rfl⟩ : syracuseStep 3260261 = 611299) (by norm_num)
theorem B2173507 : Blo 2173435 2173507 := bstep (se 1 (by rfl) ⟨1630130, by rfl⟩ : syracuseStep 2173507 = 3260261) B3260261
theorem B4126277 : Blo 2173435 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B2750851 : Blo 2173435 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B3667801 : Blo 2173435 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B4890401 : Blo 2173435 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B3260267 : Blo 2173435 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B2173511 : Blo 2173435 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B2445205 : Blo 2173435 2445205 := bbase (se 6 (by rfl) ⟨57309, by rfl⟩ : syracuseStep 2445205 = 114619) (by norm_num)
theorem B3260273 : Blo 2173435 3260273 := bstep (se 2 (by rfl) ⟨1222602, by rfl⟩ : syracuseStep 3260273 = 2445205) B2445205
theorem B2173515 : Blo 2173435 2173515 := bstep (se 1 (by rfl) ⟨1630136, by rfl⟩ : syracuseStep 2173515 = 3260273) B3260273
theorem B2750861 : Blo 2173435 2750861 := bbase (se 3 (by rfl) ⟨515786, by rfl⟩ : syracuseStep 2750861 = 1031573) (by norm_num)
theorem B7335629 : Blo 2173435 7335629 := bstep (se 3 (by rfl) ⟨1375430, by rfl⟩ : syracuseStep 7335629 = 2750861) B2750861
theorem B4890419 : Blo 2173435 4890419 := bstep (se 1 (by rfl) ⟨3667814, by rfl⟩ : syracuseStep 4890419 = 7335629) B7335629
theorem B3260279 : Blo 2173435 3260279 := bstep (se 1 (by rfl) ⟨2445209, by rfl⟩ : syracuseStep 3260279 = 4890419) B4890419
theorem B2173519 : Blo 2173435 2173519 := bstep (se 1 (by rfl) ⟨1630139, by rfl⟩ : syracuseStep 2173519 = 3260279) B3260279
theorem B3260285 : Blo 2173435 3260285 := bbase (se 3 (by rfl) ⟨611303, by rfl⟩ : syracuseStep 3260285 = 1222607) (by norm_num)
theorem B2173523 : Blo 2173435 2173523 := bstep (se 1 (by rfl) ⟨1630142, by rfl⟩ : syracuseStep 2173523 = 3260285) B3260285
theorem B4890437 : Blo 2173435 4890437 := bbase (se 4 (by rfl) ⟨458478, by rfl⟩ : syracuseStep 4890437 = 916957) (by norm_num)
theorem B3260291 : Blo 2173435 3260291 := bstep (se 1 (by rfl) ⟨2445218, by rfl⟩ : syracuseStep 3260291 = 4890437) B4890437
theorem B2173527 : Blo 2173435 2173527 := bstep (se 1 (by rfl) ⟨1630145, by rfl⟩ : syracuseStep 2173527 = 3260291) B3260291
theorem B2384821 : Blo 2173435 2384821 := bbase (se 5 (by rfl) ⟨111788, by rfl⟩ : syracuseStep 2384821 = 223577) (by norm_num)
theorem B12719045 : Blo 2173435 12719045 := bstep (se 4 (by rfl) ⟨1192410, by rfl⟩ : syracuseStep 12719045 = 2384821) B2384821
theorem B8479363 : Blo 2173435 8479363 := bstep (se 1 (by rfl) ⟨6359522, by rfl⟩ : syracuseStep 8479363 = 12719045) B12719045
theorem B11305817 : Blo 2173435 11305817 := bstep (se 2 (by rfl) ⟨4239681, by rfl⟩ : syracuseStep 11305817 = 8479363) B8479363
theorem B7537211 : Blo 2173435 7537211 := bstep (se 1 (by rfl) ⟨5652908, by rfl⟩ : syracuseStep 7537211 = 11305817) B11305817
theorem B5024807 : Blo 2173435 5024807 := bstep (se 1 (by rfl) ⟨3768605, by rfl⟩ : syracuseStep 5024807 = 7537211) B7537211
theorem B3349871 : Blo 2173435 3349871 := bstep (se 1 (by rfl) ⟨2512403, by rfl⟩ : syracuseStep 3349871 = 5024807) B5024807
theorem B2233247 : Blo 2173435 2233247 := bstep (se 1 (by rfl) ⟨1674935, by rfl⟩ : syracuseStep 2233247 = 3349871) B3349871
theorem B5955325 : Blo 2173435 5955325 := bstep (se 3 (by rfl) ⟨1116623, by rfl⟩ : syracuseStep 5955325 = 2233247) B2233247
theorem B31761733 : Blo 2173435 31761733 := bstep (se 4 (by rfl) ⟨2977662, by rfl⟩ : syracuseStep 31761733 = 5955325) B5955325
theorem B42348977 : Blo 2173435 42348977 := bstep (se 2 (by rfl) ⟨15880866, by rfl⟩ : syracuseStep 42348977 = 31761733) B31761733
theorem B28232651 : Blo 2173435 28232651 := bstep (se 1 (by rfl) ⟨21174488, by rfl⟩ : syracuseStep 28232651 = 42348977) B42348977
theorem B18821767 : Blo 2173435 18821767 := bstep (se 1 (by rfl) ⟨14116325, by rfl⟩ : syracuseStep 18821767 = 28232651) B28232651
theorem B25095689 : Blo 2173435 25095689 := bstep (se 2 (by rfl) ⟨9410883, by rfl⟩ : syracuseStep 25095689 = 18821767) B18821767
theorem B16730459 : Blo 2173435 16730459 := bstep (se 1 (by rfl) ⟨12547844, by rfl⟩ : syracuseStep 16730459 = 25095689) B25095689
theorem B11153639 : Blo 2173435 11153639 := bstep (se 1 (by rfl) ⟨8365229, by rfl⟩ : syracuseStep 11153639 = 16730459) B16730459
theorem B7435759 : Blo 2173435 7435759 := bstep (se 1 (by rfl) ⟨5576819, by rfl⟩ : syracuseStep 7435759 = 11153639) B11153639
theorem B9914345 : Blo 2173435 9914345 := bstep (se 2 (by rfl) ⟨3717879, by rfl⟩ : syracuseStep 9914345 = 7435759) B7435759
theorem B6609563 : Blo 2173435 6609563 := bstep (se 1 (by rfl) ⟨4957172, by rfl⟩ : syracuseStep 6609563 = 9914345) B9914345
theorem B4406375 : Blo 2173435 4406375 := bstep (se 1 (by rfl) ⟨3304781, by rfl⟩ : syracuseStep 4406375 = 6609563) B6609563
theorem B2937583 : Blo 2173435 2937583 := bstep (se 1 (by rfl) ⟨2203187, by rfl⟩ : syracuseStep 2937583 = 4406375) B4406375
theorem B3916777 : Blo 2173435 3916777 := bstep (se 2 (by rfl) ⟨1468791, by rfl⟩ : syracuseStep 3916777 = 2937583) B2937583
theorem B5222369 : Blo 2173435 5222369 := bstep (se 2 (by rfl) ⟨1958388, by rfl⟩ : syracuseStep 5222369 = 3916777) B3916777
theorem B3481579 : Blo 2173435 3481579 := bstep (se 1 (by rfl) ⟨2611184, by rfl⟩ : syracuseStep 3481579 = 5222369) B5222369
theorem B4642105 : Blo 2173435 4642105 := bstep (se 2 (by rfl) ⟨1740789, by rfl⟩ : syracuseStep 4642105 = 3481579) B3481579
theorem B6189473 : Blo 2173435 6189473 := bstep (se 2 (by rfl) ⟨2321052, by rfl⟩ : syracuseStep 6189473 = 4642105) B4642105
theorem B4126315 : Blo 2173435 4126315 := bstep (se 1 (by rfl) ⟨3094736, by rfl⟩ : syracuseStep 4126315 = 6189473) B6189473
theorem B5501753 : Blo 2173435 5501753 := bstep (se 2 (by rfl) ⟨2063157, by rfl⟩ : syracuseStep 5501753 = 4126315) B4126315
theorem B3667835 : Blo 2173435 3667835 := bstep (se 1 (by rfl) ⟨2750876, by rfl⟩ : syracuseStep 3667835 = 5501753) B5501753
theorem B2445223 : Blo 2173435 2445223 := bstep (se 1 (by rfl) ⟨1833917, by rfl⟩ : syracuseStep 2445223 = 3667835) B3667835
theorem B3260297 : Blo 2173435 3260297 := bstep (se 2 (by rfl) ⟨1222611, by rfl⟩ : syracuseStep 3260297 = 2445223) B2445223
theorem B2173531 : Blo 2173435 2173531 := bstep (se 1 (by rfl) ⟨1630148, by rfl⟩ : syracuseStep 2173531 = 3260297) B3260297
theorem B11003525 : Blo 2173435 11003525 := bbase (se 4 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 11003525 = 2063161) (by norm_num)
theorem B7335683 : Blo 2173435 7335683 := bstep (se 1 (by rfl) ⟨5501762, by rfl⟩ : syracuseStep 7335683 = 11003525) B11003525
theorem B4890455 : Blo 2173435 4890455 := bstep (se 1 (by rfl) ⟨3667841, by rfl⟩ : syracuseStep 4890455 = 7335683) B7335683
theorem B3260303 : Blo 2173435 3260303 := bstep (se 1 (by rfl) ⟨2445227, by rfl⟩ : syracuseStep 3260303 = 4890455) B4890455
theorem B2173535 : Blo 2173435 2173535 := bstep (se 1 (by rfl) ⟨1630151, by rfl⟩ : syracuseStep 2173535 = 3260303) B3260303
theorem B3260309 : Blo 2173435 3260309 := bbase (se 6 (by rfl) ⟨76413, by rfl⟩ : syracuseStep 3260309 = 152827) (by norm_num)
theorem B2173539 : Blo 2173435 2173539 := bstep (se 1 (by rfl) ⟨1630154, by rfl⟩ : syracuseStep 2173539 = 3260309) B3260309
theorem B2321065 : Blo 2173435 2321065 := bbase (se 2 (by rfl) ⟨870399, by rfl⟩ : syracuseStep 2321065 = 1740799) (by norm_num)
theorem B12379013 : Blo 2173435 12379013 := bstep (se 4 (by rfl) ⟨1160532, by rfl⟩ : syracuseStep 12379013 = 2321065) B2321065
theorem B8252675 : Blo 2173435 8252675 := bstep (se 1 (by rfl) ⟨6189506, by rfl⟩ : syracuseStep 8252675 = 12379013) B12379013
theorem B5501783 : Blo 2173435 5501783 := bstep (se 1 (by rfl) ⟨4126337, by rfl⟩ : syracuseStep 5501783 = 8252675) B8252675
theorem B3667855 : Blo 2173435 3667855 := bstep (se 1 (by rfl) ⟨2750891, by rfl⟩ : syracuseStep 3667855 = 5501783) B5501783
theorem B4890473 : Blo 2173435 4890473 := bstep (se 2 (by rfl) ⟨1833927, by rfl⟩ : syracuseStep 4890473 = 3667855) B3667855
theorem B3260315 : Blo 2173435 3260315 := bstep (se 1 (by rfl) ⟨2445236, by rfl⟩ : syracuseStep 3260315 = 4890473) B4890473
theorem B2173543 : Blo 2173435 2173543 := bstep (se 1 (by rfl) ⟨1630157, by rfl⟩ : syracuseStep 2173543 = 3260315) B3260315
theorem B2445241 : Blo 2173435 2445241 := bbase (se 2 (by rfl) ⟨916965, by rfl⟩ : syracuseStep 2445241 = 1833931) (by norm_num)
theorem B3260321 : Blo 2173435 3260321 := bstep (se 2 (by rfl) ⟨1222620, by rfl⟩ : syracuseStep 3260321 = 2445241) B2445241
theorem B2173547 : Blo 2173435 2173547 := bstep (se 1 (by rfl) ⟨1630160, by rfl⟩ : syracuseStep 2173547 = 3260321) B3260321
theorem B6963221 : Blo 2173435 6963221 := bbase (se 6 (by rfl) ⟨163200, by rfl⟩ : syracuseStep 6963221 = 326401) (by norm_num)
theorem B4642147 : Blo 2173435 4642147 := bstep (se 1 (by rfl) ⟨3481610, by rfl⟩ : syracuseStep 4642147 = 6963221) B6963221
theorem B6189529 : Blo 2173435 6189529 := bstep (se 2 (by rfl) ⟨2321073, by rfl⟩ : syracuseStep 6189529 = 4642147) B4642147
theorem B8252705 : Blo 2173435 8252705 := bstep (se 2 (by rfl) ⟨3094764, by rfl⟩ : syracuseStep 8252705 = 6189529) B6189529
theorem B5501803 : Blo 2173435 5501803 := bstep (se 1 (by rfl) ⟨4126352, by rfl⟩ : syracuseStep 5501803 = 8252705) B8252705
theorem B7335737 : Blo 2173435 7335737 := bstep (se 2 (by rfl) ⟨2750901, by rfl⟩ : syracuseStep 7335737 = 5501803) B5501803
theorem B4890491 : Blo 2173435 4890491 := bstep (se 1 (by rfl) ⟨3667868, by rfl⟩ : syracuseStep 4890491 = 7335737) B7335737
theorem B3260327 : Blo 2173435 3260327 := bstep (se 1 (by rfl) ⟨2445245, by rfl⟩ : syracuseStep 3260327 = 4890491) B4890491
theorem B2173551 : Blo 2173435 2173551 := bstep (se 1 (by rfl) ⟨1630163, by rfl⟩ : syracuseStep 2173551 = 3260327) B3260327
theorem B3260333 : Blo 2173435 3260333 := bbase (se 3 (by rfl) ⟨611312, by rfl⟩ : syracuseStep 3260333 = 1222625) (by norm_num)
theorem B2173555 : Blo 2173435 2173555 := bstep (se 1 (by rfl) ⟨1630166, by rfl⟩ : syracuseStep 2173555 = 3260333) B3260333
theorem B4890509 : Blo 2173435 4890509 := bbase (se 3 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 4890509 = 1833941) (by norm_num)
theorem B3260339 : Blo 2173435 3260339 := bstep (se 1 (by rfl) ⟨2445254, by rfl⟩ : syracuseStep 3260339 = 4890509) B4890509
theorem B2173559 : Blo 2173435 2173559 := bstep (se 1 (by rfl) ⟨1630169, by rfl⟩ : syracuseStep 2173559 = 3260339) B3260339
theorem B2750917 : Blo 2173435 2750917 := bbase (se 4 (by rfl) ⟨257898, by rfl⟩ : syracuseStep 2750917 = 515797) (by norm_num)
theorem B3667889 : Blo 2173435 3667889 := bstep (se 2 (by rfl) ⟨1375458, by rfl⟩ : syracuseStep 3667889 = 2750917) B2750917
theorem B2445259 : Blo 2173435 2445259 := bstep (se 1 (by rfl) ⟨1833944, by rfl⟩ : syracuseStep 2445259 = 3667889) B3667889
theorem B3260345 : Blo 2173435 3260345 := bstep (se 2 (by rfl) ⟨1222629, by rfl⟩ : syracuseStep 3260345 = 2445259) B2445259
theorem B2173563 : Blo 2173435 2173563 := bstep (se 1 (by rfl) ⟨1630172, by rfl⟩ : syracuseStep 2173563 = 3260345) B3260345
theorem B4705517 : Blo 2173435 4705517 := bbase (se 3 (by rfl) ⟨882284, by rfl⟩ : syracuseStep 4705517 = 1764569) (by norm_num)
theorem B3137011 : Blo 2173435 3137011 := bstep (se 1 (by rfl) ⟨2352758, by rfl⟩ : syracuseStep 3137011 = 4705517) B4705517
theorem B16730725 : Blo 2173435 16730725 := bstep (se 4 (by rfl) ⟨1568505, by rfl⟩ : syracuseStep 16730725 = 3137011) B3137011
theorem B22307633 : Blo 2173435 22307633 := bstep (se 2 (by rfl) ⟨8365362, by rfl⟩ : syracuseStep 22307633 = 16730725) B16730725
theorem B14871755 : Blo 2173435 14871755 := bstep (se 1 (by rfl) ⟨11153816, by rfl⟩ : syracuseStep 14871755 = 22307633) B22307633
theorem B9914503 : Blo 2173435 9914503 := bstep (se 1 (by rfl) ⟨7435877, by rfl⟩ : syracuseStep 9914503 = 14871755) B14871755
theorem B13219337 : Blo 2173435 13219337 := bstep (se 2 (by rfl) ⟨4957251, by rfl⟩ : syracuseStep 13219337 = 9914503) B9914503
theorem B8812891 : Blo 2173435 8812891 := bstep (se 1 (by rfl) ⟨6609668, by rfl⟩ : syracuseStep 8812891 = 13219337) B13219337
theorem B11750521 : Blo 2173435 11750521 := bstep (se 2 (by rfl) ⟨4406445, by rfl⟩ : syracuseStep 11750521 = 8812891) B8812891
theorem B15667361 : Blo 2173435 15667361 := bstep (se 2 (by rfl) ⟨5875260, by rfl⟩ : syracuseStep 15667361 = 11750521) B11750521
theorem B10444907 : Blo 2173435 10444907 := bstep (se 1 (by rfl) ⟨7833680, by rfl⟩ : syracuseStep 10444907 = 15667361) B15667361
theorem B27853085 : Blo 2173435 27853085 := bstep (se 3 (by rfl) ⟨5222453, by rfl⟩ : syracuseStep 27853085 = 10444907) B10444907
theorem B18568723 : Blo 2173435 18568723 := bstep (se 1 (by rfl) ⟨13926542, by rfl⟩ : syracuseStep 18568723 = 27853085) B27853085
theorem B24758297 : Blo 2173435 24758297 := bstep (se 2 (by rfl) ⟨9284361, by rfl⟩ : syracuseStep 24758297 = 18568723) B18568723
theorem B16505531 : Blo 2173435 16505531 := bstep (se 1 (by rfl) ⟨12379148, by rfl⟩ : syracuseStep 16505531 = 24758297) B24758297
theorem B11003687 : Blo 2173435 11003687 := bstep (se 1 (by rfl) ⟨8252765, by rfl⟩ : syracuseStep 11003687 = 16505531) B16505531
theorem B7335791 : Blo 2173435 7335791 := bstep (se 1 (by rfl) ⟨5501843, by rfl⟩ : syracuseStep 7335791 = 11003687) B11003687
theorem B4890527 : Blo 2173435 4890527 := bstep (se 1 (by rfl) ⟨3667895, by rfl⟩ : syracuseStep 4890527 = 7335791) B7335791
theorem B3260351 : Blo 2173435 3260351 := bstep (se 1 (by rfl) ⟨2445263, by rfl⟩ : syracuseStep 3260351 = 4890527) B4890527
theorem B2173567 : Blo 2173435 2173567 := bstep (se 1 (by rfl) ⟨1630175, by rfl⟩ : syracuseStep 2173567 = 3260351) B3260351
theorem B3260357 : Blo 2173435 3260357 := bbase (se 4 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 3260357 = 611317) (by norm_num)
theorem B2173571 : Blo 2173435 2173571 := bstep (se 1 (by rfl) ⟨1630178, by rfl⟩ : syracuseStep 2173571 = 3260357) B3260357
theorem B3667909 : Blo 2173435 3667909 := bbase (se 4 (by rfl) ⟨343866, by rfl⟩ : syracuseStep 3667909 = 687733) (by norm_num)
theorem B4890545 : Blo 2173435 4890545 := bstep (se 2 (by rfl) ⟨1833954, by rfl⟩ : syracuseStep 4890545 = 3667909) B3667909
theorem B3260363 : Blo 2173435 3260363 := bstep (se 1 (by rfl) ⟨2445272, by rfl⟩ : syracuseStep 3260363 = 4890545) B4890545
theorem B2173575 : Blo 2173435 2173575 := bstep (se 1 (by rfl) ⟨1630181, by rfl⟩ : syracuseStep 2173575 = 3260363) B3260363
theorem B2445277 : Blo 2173435 2445277 := bbase (se 3 (by rfl) ⟨458489, by rfl⟩ : syracuseStep 2445277 = 916979) (by norm_num)
theorem B3260369 : Blo 2173435 3260369 := bstep (se 2 (by rfl) ⟨1222638, by rfl⟩ : syracuseStep 3260369 = 2445277) B2445277
theorem B2173579 : Blo 2173435 2173579 := bstep (se 1 (by rfl) ⟨1630184, by rfl⟩ : syracuseStep 2173579 = 3260369) B3260369
theorem B7335845 : Blo 2173435 7335845 := bbase (se 4 (by rfl) ⟨687735, by rfl⟩ : syracuseStep 7335845 = 1375471) (by norm_num)
theorem B4890563 : Blo 2173435 4890563 := bstep (se 1 (by rfl) ⟨3667922, by rfl⟩ : syracuseStep 4890563 = 7335845) B7335845
theorem B3260375 : Blo 2173435 3260375 := bstep (se 1 (by rfl) ⟨2445281, by rfl⟩ : syracuseStep 3260375 = 4890563) B4890563
theorem B2173583 : Blo 2173435 2173583 := bstep (se 1 (by rfl) ⟨1630187, by rfl⟩ : syracuseStep 2173583 = 3260375) B3260375
theorem B3260381 : Blo 2173435 3260381 := bbase (se 3 (by rfl) ⟨611321, by rfl⟩ : syracuseStep 3260381 = 1222643) (by norm_num)
theorem B2173587 : Blo 2173435 2173587 := bstep (se 1 (by rfl) ⟨1630190, by rfl⟩ : syracuseStep 2173587 = 3260381) B3260381
theorem B4890581 : Blo 2173435 4890581 := bbase (se 7 (by rfl) ⟨57311, by rfl⟩ : syracuseStep 4890581 = 114623) (by norm_num)
theorem B3260387 : Blo 2173435 3260387 := bstep (se 1 (by rfl) ⟨2445290, by rfl⟩ : syracuseStep 3260387 = 4890581) B4890581
theorem B2173591 : Blo 2173435 2173591 := bstep (se 1 (by rfl) ⟨1630193, by rfl⟩ : syracuseStep 2173591 = 3260387) B3260387
theorem B2611261 : Blo 2173435 2611261 := bbase (se 3 (by rfl) ⟨489611, by rfl⟩ : syracuseStep 2611261 = 979223) (by norm_num)
theorem B13926725 : Blo 2173435 13926725 := bstep (se 4 (by rfl) ⟨1305630, by rfl⟩ : syracuseStep 13926725 = 2611261) B2611261
theorem B9284483 : Blo 2173435 9284483 := bstep (se 1 (by rfl) ⟨6963362, by rfl⟩ : syracuseStep 9284483 = 13926725) B13926725
theorem B6189655 : Blo 2173435 6189655 := bstep (se 1 (by rfl) ⟨4642241, by rfl⟩ : syracuseStep 6189655 = 9284483) B9284483
theorem B8252873 : Blo 2173435 8252873 := bstep (se 2 (by rfl) ⟨3094827, by rfl⟩ : syracuseStep 8252873 = 6189655) B6189655
theorem B5501915 : Blo 2173435 5501915 := bstep (se 1 (by rfl) ⟨4126436, by rfl⟩ : syracuseStep 5501915 = 8252873) B8252873
theorem B3667943 : Blo 2173435 3667943 := bstep (se 1 (by rfl) ⟨2750957, by rfl⟩ : syracuseStep 3667943 = 5501915) B5501915
theorem B2445295 : Blo 2173435 2445295 := bstep (se 1 (by rfl) ⟨1833971, by rfl⟩ : syracuseStep 2445295 = 3667943) B3667943
theorem B3260393 : Blo 2173435 3260393 := bstep (se 2 (by rfl) ⟨1222647, by rfl⟩ : syracuseStep 3260393 = 2445295) B2445295
theorem B2173595 : Blo 2173435 2173595 := bstep (se 1 (by rfl) ⟨1630196, by rfl⟩ : syracuseStep 2173595 = 3260393) B3260393
theorem B7833797 : Blo 2173435 7833797 := bbase (se 4 (by rfl) ⟨734418, by rfl⟩ : syracuseStep 7833797 = 1468837) (by norm_num)
theorem B5222531 : Blo 2173435 5222531 := bstep (se 1 (by rfl) ⟨3916898, by rfl⟩ : syracuseStep 5222531 = 7833797) B7833797
theorem B3481687 : Blo 2173435 3481687 := bstep (se 1 (by rfl) ⟨2611265, by rfl⟩ : syracuseStep 3481687 = 5222531) B5222531
theorem B18568997 : Blo 2173435 18568997 := bstep (se 4 (by rfl) ⟨1740843, by rfl⟩ : syracuseStep 18568997 = 3481687) B3481687
theorem B12379331 : Blo 2173435 12379331 := bstep (se 1 (by rfl) ⟨9284498, by rfl⟩ : syracuseStep 12379331 = 18568997) B18568997
theorem B8252887 : Blo 2173435 8252887 := bstep (se 1 (by rfl) ⟨6189665, by rfl⟩ : syracuseStep 8252887 = 12379331) B12379331
theorem B11003849 : Blo 2173435 11003849 := bstep (se 2 (by rfl) ⟨4126443, by rfl⟩ : syracuseStep 11003849 = 8252887) B8252887
theorem B7335899 : Blo 2173435 7335899 := bstep (se 1 (by rfl) ⟨5501924, by rfl⟩ : syracuseStep 7335899 = 11003849) B11003849
theorem B4890599 : Blo 2173435 4890599 := bstep (se 1 (by rfl) ⟨3667949, by rfl⟩ : syracuseStep 4890599 = 7335899) B7335899
theorem B3260399 : Blo 2173435 3260399 := bstep (se 1 (by rfl) ⟨2445299, by rfl⟩ : syracuseStep 3260399 = 4890599) B4890599
theorem B2173599 : Blo 2173435 2173599 := bstep (se 1 (by rfl) ⟨1630199, by rfl⟩ : syracuseStep 2173599 = 3260399) B3260399
theorem B3260405 : Blo 2173435 3260405 := bbase (se 5 (by rfl) ⟨152831, by rfl⟩ : syracuseStep 3260405 = 305663) (by norm_num)
theorem B2173603 : Blo 2173435 2173603 := bstep (se 1 (by rfl) ⟨1630202, by rfl⟩ : syracuseStep 2173603 = 3260405) B3260405
theorem B11750741 : Blo 2173435 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B7833827 : Blo 2173435 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B5222551 : Blo 2173435 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B6963401 : Blo 2173435 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B4642267 : Blo 2173435 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B6189689 : Blo 2173435 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B4126459 : Blo 2173435 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B5501945 : Blo 2173435 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B3667963 : Blo 2173435 3667963 := bstep (se 1 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 3667963 = 5501945) B5501945
theorem B4890617 : Blo 2173435 4890617 := bstep (se 2 (by rfl) ⟨1833981, by rfl⟩ : syracuseStep 4890617 = 3667963) B3667963
theorem B3260411 : Blo 2173435 3260411 := bstep (se 1 (by rfl) ⟨2445308, by rfl⟩ : syracuseStep 3260411 = 4890617) B4890617
theorem B2173607 : Blo 2173435 2173607 := bstep (se 1 (by rfl) ⟨1630205, by rfl⟩ : syracuseStep 2173607 = 3260411) B3260411
theorem B2445313 : Blo 2173435 2445313 := bbase (se 2 (by rfl) ⟨916992, by rfl⟩ : syracuseStep 2445313 = 1833985) (by norm_num)
theorem B3260417 : Blo 2173435 3260417 := bstep (se 2 (by rfl) ⟨1222656, by rfl⟩ : syracuseStep 3260417 = 2445313) B2445313
theorem B2173611 : Blo 2173435 2173611 := bstep (se 1 (by rfl) ⟨1630208, by rfl⟩ : syracuseStep 2173611 = 3260417) B3260417
theorem B5501965 : Blo 2173435 5501965 := bbase (se 3 (by rfl) ⟨1031618, by rfl⟩ : syracuseStep 5501965 = 2063237) (by norm_num)
theorem B7335953 : Blo 2173435 7335953 := bstep (se 2 (by rfl) ⟨2750982, by rfl⟩ : syracuseStep 7335953 = 5501965) B5501965
theorem B4890635 : Blo 2173435 4890635 := bstep (se 1 (by rfl) ⟨3667976, by rfl⟩ : syracuseStep 4890635 = 7335953) B7335953
theorem B3260423 : Blo 2173435 3260423 := bstep (se 1 (by rfl) ⟨2445317, by rfl⟩ : syracuseStep 3260423 = 4890635) B4890635
theorem B2173615 : Blo 2173435 2173615 := bstep (se 1 (by rfl) ⟨1630211, by rfl⟩ : syracuseStep 2173615 = 3260423) B3260423
theorem B3260429 : Blo 2173435 3260429 := bbase (se 3 (by rfl) ⟨611330, by rfl⟩ : syracuseStep 3260429 = 1222661) (by norm_num)
theorem B2173619 : Blo 2173435 2173619 := bstep (se 1 (by rfl) ⟨1630214, by rfl⟩ : syracuseStep 2173619 = 3260429) B3260429
theorem B4890653 : Blo 2173435 4890653 := bbase (se 3 (by rfl) ⟨916997, by rfl⟩ : syracuseStep 4890653 = 1833995) (by norm_num)
theorem B3260435 : Blo 2173435 3260435 := bstep (se 1 (by rfl) ⟨2445326, by rfl⟩ : syracuseStep 3260435 = 4890653) B4890653
theorem B2173623 : Blo 2173435 2173623 := bstep (se 1 (by rfl) ⟨1630217, by rfl⟩ : syracuseStep 2173623 = 3260435) B3260435
theorem B3667997 : Blo 2173435 3667997 := bbase (se 3 (by rfl) ⟨687749, by rfl⟩ : syracuseStep 3667997 = 1375499) (by norm_num)
theorem B2445331 : Blo 2173435 2445331 := bstep (se 1 (by rfl) ⟨1833998, by rfl⟩ : syracuseStep 2445331 = 3667997) B3667997
theorem B3260441 : Blo 2173435 3260441 := bstep (se 2 (by rfl) ⟨1222665, by rfl⟩ : syracuseStep 3260441 = 2445331) B2445331
theorem B2173627 : Blo 2173435 2173627 := bstep (se 1 (by rfl) ⟨1630220, by rfl⟩ : syracuseStep 2173627 = 3260441) B3260441
theorem B47644757 : Blo 2173435 47644757 := bbase (se 8 (by rfl) ⟨279168, by rfl⟩ : syracuseStep 47644757 = 558337) (by norm_num)
theorem B31763171 : Blo 2173435 31763171 := bstep (se 1 (by rfl) ⟨23822378, by rfl⟩ : syracuseStep 31763171 = 47644757) B47644757
theorem B21175447 : Blo 2173435 21175447 := bstep (se 1 (by rfl) ⟨15881585, by rfl⟩ : syracuseStep 21175447 = 31763171) B31763171
theorem B28233929 : Blo 2173435 28233929 := bstep (se 2 (by rfl) ⟨10587723, by rfl⟩ : syracuseStep 28233929 = 21175447) B21175447
theorem B18822619 : Blo 2173435 18822619 := bstep (se 1 (by rfl) ⟨14116964, by rfl⟩ : syracuseStep 18822619 = 28233929) B28233929
theorem B25096825 : Blo 2173435 25096825 := bstep (se 2 (by rfl) ⟨9411309, by rfl⟩ : syracuseStep 25096825 = 18822619) B18822619
theorem B33462433 : Blo 2173435 33462433 := bstep (se 2 (by rfl) ⟨12548412, by rfl⟩ : syracuseStep 33462433 = 25096825) B25096825
theorem B44616577 : Blo 2173435 44616577 := bstep (se 2 (by rfl) ⟨16731216, by rfl⟩ : syracuseStep 44616577 = 33462433) B33462433
theorem B59488769 : Blo 2173435 59488769 := bstep (se 2 (by rfl) ⟨22308288, by rfl⟩ : syracuseStep 59488769 = 44616577) B44616577
theorem B39659179 : Blo 2173435 39659179 := bstep (se 1 (by rfl) ⟨29744384, by rfl⟩ : syracuseStep 39659179 = 59488769) B59488769
theorem B52878905 : Blo 2173435 52878905 := bstep (se 2 (by rfl) ⟨19829589, by rfl⟩ : syracuseStep 52878905 = 39659179) B39659179
theorem B35252603 : Blo 2173435 35252603 := bstep (se 1 (by rfl) ⟨26439452, by rfl⟩ : syracuseStep 35252603 = 52878905) B52878905
theorem B23501735 : Blo 2173435 23501735 := bstep (se 1 (by rfl) ⟨17626301, by rfl⟩ : syracuseStep 23501735 = 35252603) B35252603
theorem B15667823 : Blo 2173435 15667823 := bstep (se 1 (by rfl) ⟨11750867, by rfl⟩ : syracuseStep 15667823 = 23501735) B23501735
theorem B10445215 : Blo 2173435 10445215 := bstep (se 1 (by rfl) ⟨7833911, by rfl⟩ : syracuseStep 10445215 = 15667823) B15667823
theorem B13926953 : Blo 2173435 13926953 := bstep (se 2 (by rfl) ⟨5222607, by rfl⟩ : syracuseStep 13926953 = 10445215) B10445215
theorem B9284635 : Blo 2173435 9284635 := bstep (se 1 (by rfl) ⟨6963476, by rfl⟩ : syracuseStep 9284635 = 13926953) B13926953
theorem B12379513 : Blo 2173435 12379513 := bstep (se 2 (by rfl) ⟨4642317, by rfl⟩ : syracuseStep 12379513 = 9284635) B9284635
theorem B16506017 : Blo 2173435 16506017 := bstep (se 2 (by rfl) ⟨6189756, by rfl⟩ : syracuseStep 16506017 = 12379513) B12379513
theorem B11004011 : Blo 2173435 11004011 := bstep (se 1 (by rfl) ⟨8253008, by rfl⟩ : syracuseStep 11004011 = 16506017) B16506017
theorem B7336007 : Blo 2173435 7336007 := bstep (se 1 (by rfl) ⟨5502005, by rfl⟩ : syracuseStep 7336007 = 11004011) B11004011
theorem B4890671 : Blo 2173435 4890671 := bstep (se 1 (by rfl) ⟨3668003, by rfl⟩ : syracuseStep 4890671 = 7336007) B7336007
theorem B3260447 : Blo 2173435 3260447 := bstep (se 1 (by rfl) ⟨2445335, by rfl⟩ : syracuseStep 3260447 = 4890671) B4890671
theorem B2173631 : Blo 2173435 2173631 := bstep (se 1 (by rfl) ⟨1630223, by rfl⟩ : syracuseStep 2173631 = 3260447) B3260447
theorem B3260453 : Blo 2173435 3260453 := bbase (se 4 (by rfl) ⟨305667, by rfl⟩ : syracuseStep 3260453 = 611335) (by norm_num)
theorem B2173635 : Blo 2173435 2173635 := bstep (se 1 (by rfl) ⟨1630226, by rfl⟩ : syracuseStep 2173635 = 3260453) B3260453
theorem B2751013 : Blo 2173435 2751013 := bbase (se 4 (by rfl) ⟨257907, by rfl⟩ : syracuseStep 2751013 = 515815) (by norm_num)
theorem B3668017 : Blo 2173435 3668017 := bstep (se 2 (by rfl) ⟨1375506, by rfl⟩ : syracuseStep 3668017 = 2751013) B2751013
theorem B4890689 : Blo 2173435 4890689 := bstep (se 2 (by rfl) ⟨1834008, by rfl⟩ : syracuseStep 4890689 = 3668017) B3668017
theorem B3260459 : Blo 2173435 3260459 := bstep (se 1 (by rfl) ⟨2445344, by rfl⟩ : syracuseStep 3260459 = 4890689) B4890689
theorem B2173639 : Blo 2173435 2173639 := bstep (se 1 (by rfl) ⟨1630229, by rfl⟩ : syracuseStep 2173639 = 3260459) B3260459
theorem B2445349 : Blo 2173435 2445349 := bbase (se 4 (by rfl) ⟨229251, by rfl⟩ : syracuseStep 2445349 = 458503) (by norm_num)
theorem B3260465 : Blo 2173435 3260465 := bstep (se 2 (by rfl) ⟨1222674, by rfl⟩ : syracuseStep 3260465 = 2445349) B2445349
theorem B2173643 : Blo 2173435 2173643 := bstep (se 1 (by rfl) ⟨1630232, by rfl⟩ : syracuseStep 2173643 = 3260465) B3260465
theorem B3304957 : Blo 2173435 3304957 := bbase (se 3 (by rfl) ⟨619679, by rfl⟩ : syracuseStep 3304957 = 1239359) (by norm_num)
theorem B4406609 : Blo 2173435 4406609 := bstep (se 2 (by rfl) ⟨1652478, by rfl⟩ : syracuseStep 4406609 = 3304957) B3304957
theorem B11750957 : Blo 2173435 11750957 := bstep (se 3 (by rfl) ⟨2203304, by rfl⟩ : syracuseStep 11750957 = 4406609) B4406609
theorem B7833971 : Blo 2173435 7833971 := bstep (se 1 (by rfl) ⟨5875478, by rfl⟩ : syracuseStep 7833971 = 11750957) B11750957
theorem B5222647 : Blo 2173435 5222647 := bstep (se 1 (by rfl) ⟨3916985, by rfl⟩ : syracuseStep 5222647 = 7833971) B7833971
theorem B6963529 : Blo 2173435 6963529 := bstep (se 2 (by rfl) ⟨2611323, by rfl⟩ : syracuseStep 6963529 = 5222647) B5222647
theorem B9284705 : Blo 2173435 9284705 := bstep (se 2 (by rfl) ⟨3481764, by rfl⟩ : syracuseStep 9284705 = 6963529) B6963529
theorem B6189803 : Blo 2173435 6189803 := bstep (se 1 (by rfl) ⟨4642352, by rfl⟩ : syracuseStep 6189803 = 9284705) B9284705
theorem B4126535 : Blo 2173435 4126535 := bstep (se 1 (by rfl) ⟨3094901, by rfl⟩ : syracuseStep 4126535 = 6189803) B6189803
theorem B2751023 : Blo 2173435 2751023 := bstep (se 1 (by rfl) ⟨2063267, by rfl⟩ : syracuseStep 2751023 = 4126535) B4126535
theorem B7336061 : Blo 2173435 7336061 := bstep (se 3 (by rfl) ⟨1375511, by rfl⟩ : syracuseStep 7336061 = 2751023) B2751023
theorem B4890707 : Blo 2173435 4890707 := bstep (se 1 (by rfl) ⟨3668030, by rfl⟩ : syracuseStep 4890707 = 7336061) B7336061
theorem B3260471 : Blo 2173435 3260471 := bstep (se 1 (by rfl) ⟨2445353, by rfl⟩ : syracuseStep 3260471 = 4890707) B4890707
theorem B2173647 : Blo 2173435 2173647 := bstep (se 1 (by rfl) ⟨1630235, by rfl⟩ : syracuseStep 2173647 = 3260471) B3260471
theorem B3260477 : Blo 2173435 3260477 := bbase (se 3 (by rfl) ⟨611339, by rfl⟩ : syracuseStep 3260477 = 1222679) (by norm_num)
theorem B2173651 : Blo 2173435 2173651 := bstep (se 1 (by rfl) ⟨1630238, by rfl⟩ : syracuseStep 2173651 = 3260477) B3260477
theorem B4890725 : Blo 2173435 4890725 := bbase (se 4 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 4890725 = 917011) (by norm_num)
theorem B3260483 : Blo 2173435 3260483 := bstep (se 1 (by rfl) ⟨2445362, by rfl⟩ : syracuseStep 3260483 = 4890725) B4890725
theorem B2173655 : Blo 2173435 2173655 := bstep (se 1 (by rfl) ⟨1630241, by rfl⟩ : syracuseStep 2173655 = 3260483) B3260483
theorem B5502077 : Blo 2173435 5502077 := bbase (se 3 (by rfl) ⟨1031639, by rfl⟩ : syracuseStep 5502077 = 2063279) (by norm_num)
theorem B3668051 : Blo 2173435 3668051 := bstep (se 1 (by rfl) ⟨2751038, by rfl⟩ : syracuseStep 3668051 = 5502077) B5502077
theorem B2445367 : Blo 2173435 2445367 := bstep (se 1 (by rfl) ⟨1834025, by rfl⟩ : syracuseStep 2445367 = 3668051) B3668051
theorem B3260489 : Blo 2173435 3260489 := bstep (se 2 (by rfl) ⟨1222683, by rfl⟩ : syracuseStep 3260489 = 2445367) B2445367
theorem B2173659 : Blo 2173435 2173659 := bstep (se 1 (by rfl) ⟨1630244, by rfl⟩ : syracuseStep 2173659 = 3260489) B3260489
theorem B4126565 : Blo 2173435 4126565 := bbase (se 4 (by rfl) ⟨386865, by rfl⟩ : syracuseStep 4126565 = 773731) (by norm_num)
theorem B11004173 : Blo 2173435 11004173 := bstep (se 3 (by rfl) ⟨2063282, by rfl⟩ : syracuseStep 11004173 = 4126565) B4126565
theorem B7336115 : Blo 2173435 7336115 := bstep (se 1 (by rfl) ⟨5502086, by rfl⟩ : syracuseStep 7336115 = 11004173) B11004173
theorem B4890743 : Blo 2173435 4890743 := bstep (se 1 (by rfl) ⟨3668057, by rfl⟩ : syracuseStep 4890743 = 7336115) B7336115
theorem B3260495 : Blo 2173435 3260495 := bstep (se 1 (by rfl) ⟨2445371, by rfl⟩ : syracuseStep 3260495 = 4890743) B4890743
theorem B2173663 : Blo 2173435 2173663 := bstep (se 1 (by rfl) ⟨1630247, by rfl⟩ : syracuseStep 2173663 = 3260495) B3260495
theorem B3260501 : Blo 2173435 3260501 := bbase (se 8 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 3260501 = 38209) (by norm_num)
theorem B2173667 : Blo 2173435 2173667 := bstep (se 1 (by rfl) ⟨1630250, by rfl⟩ : syracuseStep 2173667 = 3260501) B3260501
theorem B2478745 : Blo 2173435 2478745 := bbase (se 2 (by rfl) ⟨929529, by rfl⟩ : syracuseStep 2478745 = 1859059) (by norm_num)
theorem B3304993 : Blo 2173435 3304993 := bstep (se 2 (by rfl) ⟨1239372, by rfl⟩ : syracuseStep 3304993 = 2478745) B2478745
theorem B4406657 : Blo 2173435 4406657 := bstep (se 2 (by rfl) ⟨1652496, by rfl⟩ : syracuseStep 4406657 = 3304993) B3304993
theorem B11751085 : Blo 2173435 11751085 := bstep (se 3 (by rfl) ⟨2203328, by rfl⟩ : syracuseStep 11751085 = 4406657) B4406657
theorem B15668113 : Blo 2173435 15668113 := bstep (se 2 (by rfl) ⟨5875542, by rfl⟩ : syracuseStep 15668113 = 11751085) B11751085
theorem B20890817 : Blo 2173435 20890817 := bstep (se 2 (by rfl) ⟨7834056, by rfl⟩ : syracuseStep 20890817 = 15668113) B15668113
theorem B13927211 : Blo 2173435 13927211 := bstep (se 1 (by rfl) ⟨10445408, by rfl⟩ : syracuseStep 13927211 = 20890817) B20890817
theorem B9284807 : Blo 2173435 9284807 := bstep (se 1 (by rfl) ⟨6963605, by rfl⟩ : syracuseStep 9284807 = 13927211) B13927211
theorem B6189871 : Blo 2173435 6189871 := bstep (se 1 (by rfl) ⟨4642403, by rfl⟩ : syracuseStep 6189871 = 9284807) B9284807
theorem B8253161 : Blo 2173435 8253161 := bstep (se 2 (by rfl) ⟨3094935, by rfl⟩ : syracuseStep 8253161 = 6189871) B6189871
theorem B5502107 : Blo 2173435 5502107 := bstep (se 1 (by rfl) ⟨4126580, by rfl⟩ : syracuseStep 5502107 = 8253161) B8253161
theorem B3668071 : Blo 2173435 3668071 := bstep (se 1 (by rfl) ⟨2751053, by rfl⟩ : syracuseStep 3668071 = 5502107) B5502107
theorem B4890761 : Blo 2173435 4890761 := bstep (se 2 (by rfl) ⟨1834035, by rfl⟩ : syracuseStep 4890761 = 3668071) B3668071
theorem B3260507 : Blo 2173435 3260507 := bstep (se 1 (by rfl) ⟨2445380, by rfl⟩ : syracuseStep 3260507 = 4890761) B4890761
theorem B2173671 : Blo 2173435 2173671 := bstep (se 1 (by rfl) ⟨1630253, by rfl⟩ : syracuseStep 2173671 = 3260507) B3260507
theorem B2445385 : Blo 2173435 2445385 := bbase (se 2 (by rfl) ⟨917019, by rfl⟩ : syracuseStep 2445385 = 1834039) (by norm_num)
theorem B3260513 : Blo 2173435 3260513 := bstep (se 2 (by rfl) ⟨1222692, by rfl⟩ : syracuseStep 3260513 = 2445385) B2445385
theorem B2173675 : Blo 2173435 2173675 := bstep (se 1 (by rfl) ⟨1630256, by rfl⟩ : syracuseStep 2173675 = 3260513) B3260513
theorem B7834085 : Blo 2173435 7834085 := bbase (se 4 (by rfl) ⟨734445, by rfl⟩ : syracuseStep 7834085 = 1468891) (by norm_num)
theorem B5222723 : Blo 2173435 5222723 := bstep (se 1 (by rfl) ⟨3917042, by rfl⟩ : syracuseStep 5222723 = 7834085) B7834085
theorem B13927261 : Blo 2173435 13927261 := bstep (se 3 (by rfl) ⟨2611361, by rfl⟩ : syracuseStep 13927261 = 5222723) B5222723
theorem B18569681 : Blo 2173435 18569681 := bstep (se 2 (by rfl) ⟨6963630, by rfl⟩ : syracuseStep 18569681 = 13927261) B13927261
theorem B12379787 : Blo 2173435 12379787 := bstep (se 1 (by rfl) ⟨9284840, by rfl⟩ : syracuseStep 12379787 = 18569681) B18569681
theorem B8253191 : Blo 2173435 8253191 := bstep (se 1 (by rfl) ⟨6189893, by rfl⟩ : syracuseStep 8253191 = 12379787) B12379787
theorem B5502127 : Blo 2173435 5502127 := bstep (se 1 (by rfl) ⟨4126595, by rfl⟩ : syracuseStep 5502127 = 8253191) B8253191
theorem B7336169 : Blo 2173435 7336169 := bstep (se 2 (by rfl) ⟨2751063, by rfl⟩ : syracuseStep 7336169 = 5502127) B5502127
theorem B4890779 : Blo 2173435 4890779 := bstep (se 1 (by rfl) ⟨3668084, by rfl⟩ : syracuseStep 4890779 = 7336169) B7336169
theorem B3260519 : Blo 2173435 3260519 := bstep (se 1 (by rfl) ⟨2445389, by rfl⟩ : syracuseStep 3260519 = 4890779) B4890779
theorem B2173679 : Blo 2173435 2173679 := bstep (se 1 (by rfl) ⟨1630259, by rfl⟩ : syracuseStep 2173679 = 3260519) B3260519
theorem B3260525 : Blo 2173435 3260525 := bbase (se 3 (by rfl) ⟨611348, by rfl⟩ : syracuseStep 3260525 = 1222697) (by norm_num)
theorem B2173683 : Blo 2173435 2173683 := bstep (se 1 (by rfl) ⟨1630262, by rfl⟩ : syracuseStep 2173683 = 3260525) B3260525
theorem B4890797 : Blo 2173435 4890797 := bbase (se 3 (by rfl) ⟨917024, by rfl⟩ : syracuseStep 4890797 = 1834049) (by norm_num)
theorem B3260531 : Blo 2173435 3260531 := bstep (se 1 (by rfl) ⟨2445398, by rfl⟩ : syracuseStep 3260531 = 4890797) B4890797
theorem B2173687 : Blo 2173435 2173687 := bstep (se 1 (by rfl) ⟨1630265, by rfl⟩ : syracuseStep 2173687 = 3260531) B3260531
theorem B4705789 : Blo 2173435 4705789 := bbase (se 3 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 4705789 = 1764671) (by norm_num)
theorem B6274385 : Blo 2173435 6274385 := bstep (se 2 (by rfl) ⟨2352894, by rfl⟩ : syracuseStep 6274385 = 4705789) B4705789
theorem B4182923 : Blo 2173435 4182923 := bstep (se 1 (by rfl) ⟨3137192, by rfl⟩ : syracuseStep 4182923 = 6274385) B6274385
theorem B2788615 : Blo 2173435 2788615 := bstep (se 1 (by rfl) ⟨2091461, by rfl⟩ : syracuseStep 2788615 = 4182923) B4182923
theorem B3718153 : Blo 2173435 3718153 := bstep (se 2 (by rfl) ⟨1394307, by rfl⟩ : syracuseStep 3718153 = 2788615) B2788615
theorem B4957537 : Blo 2173435 4957537 := bstep (se 2 (by rfl) ⟨1859076, by rfl⟩ : syracuseStep 4957537 = 3718153) B3718153
theorem B6610049 : Blo 2173435 6610049 := bstep (se 2 (by rfl) ⟨2478768, by rfl⟩ : syracuseStep 6610049 = 4957537) B4957537
theorem B4406699 : Blo 2173435 4406699 := bstep (se 1 (by rfl) ⟨3305024, by rfl⟩ : syracuseStep 4406699 = 6610049) B6610049
theorem B2937799 : Blo 2173435 2937799 := bstep (se 1 (by rfl) ⟨2203349, by rfl⟩ : syracuseStep 2937799 = 4406699) B4406699
theorem B15668261 : Blo 2173435 15668261 := bstep (se 4 (by rfl) ⟨1468899, by rfl⟩ : syracuseStep 15668261 = 2937799) B2937799
theorem B10445507 : Blo 2173435 10445507 := bstep (se 1 (by rfl) ⟨7834130, by rfl⟩ : syracuseStep 10445507 = 15668261) B15668261
theorem B6963671 : Blo 2173435 6963671 := bstep (se 1 (by rfl) ⟨5222753, by rfl⟩ : syracuseStep 6963671 = 10445507) B10445507
theorem B4642447 : Blo 2173435 4642447 := bstep (se 1 (by rfl) ⟨3481835, by rfl⟩ : syracuseStep 4642447 = 6963671) B6963671
theorem B6189929 : Blo 2173435 6189929 := bstep (se 2 (by rfl) ⟨2321223, by rfl⟩ : syracuseStep 6189929 = 4642447) B4642447
theorem B4126619 : Blo 2173435 4126619 := bstep (se 1 (by rfl) ⟨3094964, by rfl⟩ : syracuseStep 4126619 = 6189929) B6189929
theorem B2751079 : Blo 2173435 2751079 := bstep (se 1 (by rfl) ⟨2063309, by rfl⟩ : syracuseStep 2751079 = 4126619) B4126619
theorem B3668105 : Blo 2173435 3668105 := bstep (se 2 (by rfl) ⟨1375539, by rfl⟩ : syracuseStep 3668105 = 2751079) B2751079
theorem B2445403 : Blo 2173435 2445403 := bstep (se 1 (by rfl) ⟨1834052, by rfl⟩ : syracuseStep 2445403 = 3668105) B3668105
theorem B3260537 : Blo 2173435 3260537 := bstep (se 2 (by rfl) ⟨1222701, by rfl⟩ : syracuseStep 3260537 = 2445403) B2445403
theorem B2173691 : Blo 2173435 2173691 := bstep (se 1 (by rfl) ⟨1630268, by rfl⟩ : syracuseStep 2173691 = 3260537) B3260537
theorem B13220117 : Blo 2173435 13220117 := bbase (se 6 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 13220117 = 619693) (by norm_num)
theorem B8813411 : Blo 2173435 8813411 := bstep (se 1 (by rfl) ⟨6610058, by rfl⟩ : syracuseStep 8813411 = 13220117) B13220117
theorem B5875607 : Blo 2173435 5875607 := bstep (se 1 (by rfl) ⟨4406705, by rfl⟩ : syracuseStep 5875607 = 8813411) B8813411
theorem B3917071 : Blo 2173435 3917071 := bstep (se 1 (by rfl) ⟨2937803, by rfl⟩ : syracuseStep 3917071 = 5875607) B5875607
theorem B5222761 : Blo 2173435 5222761 := bstep (se 2 (by rfl) ⟨1958535, by rfl⟩ : syracuseStep 5222761 = 3917071) B3917071
theorem B27854725 : Blo 2173435 27854725 := bstep (se 4 (by rfl) ⟨2611380, by rfl⟩ : syracuseStep 27854725 = 5222761) B5222761
theorem B37139633 : Blo 2173435 37139633 := bstep (se 2 (by rfl) ⟨13927362, by rfl⟩ : syracuseStep 37139633 = 27854725) B27854725
theorem B24759755 : Blo 2173435 24759755 := bstep (se 1 (by rfl) ⟨18569816, by rfl⟩ : syracuseStep 24759755 = 37139633) B37139633
theorem B16506503 : Blo 2173435 16506503 := bstep (se 1 (by rfl) ⟨12379877, by rfl⟩ : syracuseStep 16506503 = 24759755) B24759755
theorem B11004335 : Blo 2173435 11004335 := bstep (se 1 (by rfl) ⟨8253251, by rfl⟩ : syracuseStep 11004335 = 16506503) B16506503
theorem B7336223 : Blo 2173435 7336223 := bstep (se 1 (by rfl) ⟨5502167, by rfl⟩ : syracuseStep 7336223 = 11004335) B11004335
theorem B4890815 : Blo 2173435 4890815 := bstep (se 1 (by rfl) ⟨3668111, by rfl⟩ : syracuseStep 4890815 = 7336223) B7336223
theorem B3260543 : Blo 2173435 3260543 := bstep (se 1 (by rfl) ⟨2445407, by rfl⟩ : syracuseStep 3260543 = 4890815) B4890815
theorem B2173695 : Blo 2173435 2173695 := bstep (se 1 (by rfl) ⟨1630271, by rfl⟩ : syracuseStep 2173695 = 3260543) B3260543
theorem B3260549 : Blo 2173435 3260549 := bbase (se 4 (by rfl) ⟨305676, by rfl⟩ : syracuseStep 3260549 = 611353) (by norm_num)
theorem B2173699 : Blo 2173435 2173699 := bstep (se 1 (by rfl) ⟨1630274, by rfl⟩ : syracuseStep 2173699 = 3260549) B3260549
theorem B3668125 : Blo 2173435 3668125 := bbase (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) (by norm_num)
theorem B4890833 : Blo 2173435 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B3260555 : Blo 2173435 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B2173703 : Blo 2173435 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B2445421 : Blo 2173435 2445421 := bbase (se 3 (by rfl) ⟨458516, by rfl⟩ : syracuseStep 2445421 = 917033) (by norm_num)
theorem B3260561 : Blo 2173435 3260561 := bstep (se 2 (by rfl) ⟨1222710, by rfl⟩ : syracuseStep 3260561 = 2445421) B2445421
theorem B2173707 : Blo 2173435 2173707 := bstep (se 1 (by rfl) ⟨1630280, by rfl⟩ : syracuseStep 2173707 = 3260561) B3260561
theorem B7336277 : Blo 2173435 7336277 := bbase (se 10 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 7336277 = 21493) (by norm_num)
theorem B4890851 : Blo 2173435 4890851 := bstep (se 1 (by rfl) ⟨3668138, by rfl⟩ : syracuseStep 4890851 = 7336277) B7336277
theorem B3260567 : Blo 2173435 3260567 := bstep (se 1 (by rfl) ⟨2445425, by rfl⟩ : syracuseStep 3260567 = 4890851) B4890851
theorem B2173711 : Blo 2173435 2173711 := bstep (se 1 (by rfl) ⟨1630283, by rfl⟩ : syracuseStep 2173711 = 3260567) B3260567
theorem B3260573 : Blo 2173435 3260573 := bbase (se 3 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 3260573 = 1222715) (by norm_num)
theorem B2173715 : Blo 2173435 2173715 := bstep (se 1 (by rfl) ⟨1630286, by rfl⟩ : syracuseStep 2173715 = 3260573) B3260573
theorem B4890869 : Blo 2173435 4890869 := bbase (se 5 (by rfl) ⟨229259, by rfl⟩ : syracuseStep 4890869 = 458519) (by norm_num)
theorem B3260579 : Blo 2173435 3260579 := bstep (se 1 (by rfl) ⟨2445434, by rfl⟩ : syracuseStep 3260579 = 4890869) B4890869
theorem B2173719 : Blo 2173435 2173719 := bstep (se 1 (by rfl) ⟨1630289, by rfl⟩ : syracuseStep 2173719 = 3260579) B3260579
theorem B20891317 : Blo 2173435 20891317 := bbase (se 5 (by rfl) ⟨979280, by rfl⟩ : syracuseStep 20891317 = 1958561) (by norm_num)
theorem B27855089 : Blo 2173435 27855089 := bstep (se 2 (by rfl) ⟨10445658, by rfl⟩ : syracuseStep 27855089 = 20891317) B20891317
theorem B18570059 : Blo 2173435 18570059 := bstep (se 1 (by rfl) ⟨13927544, by rfl⟩ : syracuseStep 18570059 = 27855089) B27855089
theorem B12380039 : Blo 2173435 12380039 := bstep (se 1 (by rfl) ⟨9285029, by rfl⟩ : syracuseStep 12380039 = 18570059) B18570059
theorem B8253359 : Blo 2173435 8253359 := bstep (se 1 (by rfl) ⟨6190019, by rfl⟩ : syracuseStep 8253359 = 12380039) B12380039
theorem B5502239 : Blo 2173435 5502239 := bstep (se 1 (by rfl) ⟨4126679, by rfl⟩ : syracuseStep 5502239 = 8253359) B8253359
theorem B3668159 : Blo 2173435 3668159 := bstep (se 1 (by rfl) ⟨2751119, by rfl⟩ : syracuseStep 3668159 = 5502239) B5502239
theorem B2445439 : Blo 2173435 2445439 := bstep (se 1 (by rfl) ⟨1834079, by rfl⟩ : syracuseStep 2445439 = 3668159) B3668159
theorem B3260585 : Blo 2173435 3260585 := bstep (se 2 (by rfl) ⟨1222719, by rfl⟩ : syracuseStep 3260585 = 2445439) B2445439
theorem B2173723 : Blo 2173435 2173723 := bstep (se 1 (by rfl) ⟨1630292, by rfl⟩ : syracuseStep 2173723 = 3260585) B3260585
theorem B2478809 : Blo 2173435 2478809 := bbase (se 2 (by rfl) ⟨929553, by rfl⟩ : syracuseStep 2478809 = 1859107) (by norm_num)
theorem B6610157 : Blo 2173435 6610157 := bstep (se 3 (by rfl) ⟨1239404, by rfl⟩ : syracuseStep 6610157 = 2478809) B2478809
theorem B4406771 : Blo 2173435 4406771 := bstep (se 1 (by rfl) ⟨3305078, by rfl⟩ : syracuseStep 4406771 = 6610157) B6610157
theorem B11751389 : Blo 2173435 11751389 := bstep (se 3 (by rfl) ⟨2203385, by rfl⟩ : syracuseStep 11751389 = 4406771) B4406771
theorem B7834259 : Blo 2173435 7834259 := bstep (se 1 (by rfl) ⟨5875694, by rfl⟩ : syracuseStep 7834259 = 11751389) B11751389
theorem B5222839 : Blo 2173435 5222839 := bstep (se 1 (by rfl) ⟨3917129, by rfl⟩ : syracuseStep 5222839 = 7834259) B7834259
theorem B6963785 : Blo 2173435 6963785 := bstep (se 2 (by rfl) ⟨2611419, by rfl⟩ : syracuseStep 6963785 = 5222839) B5222839
theorem B4642523 : Blo 2173435 4642523 := bstep (se 1 (by rfl) ⟨3481892, by rfl⟩ : syracuseStep 4642523 = 6963785) B6963785
theorem B3095015 : Blo 2173435 3095015 := bstep (se 1 (by rfl) ⟨2321261, by rfl⟩ : syracuseStep 3095015 = 4642523) B4642523
theorem B8253373 : Blo 2173435 8253373 := bstep (se 3 (by rfl) ⟨1547507, by rfl⟩ : syracuseStep 8253373 = 3095015) B3095015
theorem B11004497 : Blo 2173435 11004497 := bstep (se 2 (by rfl) ⟨4126686, by rfl⟩ : syracuseStep 11004497 = 8253373) B8253373
theorem B7336331 : Blo 2173435 7336331 := bstep (se 1 (by rfl) ⟨5502248, by rfl⟩ : syracuseStep 7336331 = 11004497) B11004497
theorem B4890887 : Blo 2173435 4890887 := bstep (se 1 (by rfl) ⟨3668165, by rfl⟩ : syracuseStep 4890887 = 7336331) B7336331
theorem B3260591 : Blo 2173435 3260591 := bstep (se 1 (by rfl) ⟨2445443, by rfl⟩ : syracuseStep 3260591 = 4890887) B4890887
theorem B2173727 : Blo 2173435 2173727 := bstep (se 1 (by rfl) ⟨1630295, by rfl⟩ : syracuseStep 2173727 = 3260591) B3260591
theorem B3260597 : Blo 2173435 3260597 := bbase (se 5 (by rfl) ⟨152840, by rfl⟩ : syracuseStep 3260597 = 305681) (by norm_num)
theorem B2173731 : Blo 2173435 2173731 := bstep (se 1 (by rfl) ⟨1630298, by rfl⟩ : syracuseStep 2173731 = 3260597) B3260597
theorem B5502269 : Blo 2173435 5502269 := bbase (se 3 (by rfl) ⟨1031675, by rfl⟩ : syracuseStep 5502269 = 2063351) (by norm_num)
theorem B3668179 : Blo 2173435 3668179 := bstep (se 1 (by rfl) ⟨2751134, by rfl⟩ : syracuseStep 3668179 = 5502269) B5502269
theorem B4890905 : Blo 2173435 4890905 := bstep (se 2 (by rfl) ⟨1834089, by rfl⟩ : syracuseStep 4890905 = 3668179) B3668179
theorem B3260603 : Blo 2173435 3260603 := bstep (se 1 (by rfl) ⟨2445452, by rfl⟩ : syracuseStep 3260603 = 4890905) B4890905
theorem B2173735 : Blo 2173435 2173735 := bstep (se 1 (by rfl) ⟨1630301, by rfl⟩ : syracuseStep 2173735 = 3260603) B3260603
theorem B2445457 : Blo 2173435 2445457 := bbase (se 2 (by rfl) ⟨917046, by rfl⟩ : syracuseStep 2445457 = 1834093) (by norm_num)
theorem B3260609 : Blo 2173435 3260609 := bstep (se 2 (by rfl) ⟨1222728, by rfl⟩ : syracuseStep 3260609 = 2445457) B2445457
theorem B2173739 : Blo 2173435 2173739 := bstep (se 1 (by rfl) ⟨1630304, by rfl⟩ : syracuseStep 2173739 = 3260609) B3260609
theorem B4126717 : Blo 2173435 4126717 := bbase (se 3 (by rfl) ⟨773759, by rfl⟩ : syracuseStep 4126717 = 1547519) (by norm_num)
theorem B5502289 : Blo 2173435 5502289 := bstep (se 2 (by rfl) ⟨2063358, by rfl⟩ : syracuseStep 5502289 = 4126717) B4126717
theorem B7336385 : Blo 2173435 7336385 := bstep (se 2 (by rfl) ⟨2751144, by rfl⟩ : syracuseStep 7336385 = 5502289) B5502289
theorem B4890923 : Blo 2173435 4890923 := bstep (se 1 (by rfl) ⟨3668192, by rfl⟩ : syracuseStep 4890923 = 7336385) B7336385
theorem B3260615 : Blo 2173435 3260615 := bstep (se 1 (by rfl) ⟨2445461, by rfl⟩ : syracuseStep 3260615 = 4890923) B4890923
theorem B2173743 : Blo 2173435 2173743 := bstep (se 1 (by rfl) ⟨1630307, by rfl⟩ : syracuseStep 2173743 = 3260615) B3260615
theorem B3260621 : Blo 2173435 3260621 := bbase (se 3 (by rfl) ⟨611366, by rfl⟩ : syracuseStep 3260621 = 1222733) (by norm_num)
theorem B2173747 : Blo 2173435 2173747 := bstep (se 1 (by rfl) ⟨1630310, by rfl⟩ : syracuseStep 2173747 = 3260621) B3260621
theorem B4890941 : Blo 2173435 4890941 := bbase (se 3 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 4890941 = 1834103) (by norm_num)
theorem B3260627 : Blo 2173435 3260627 := bstep (se 1 (by rfl) ⟨2445470, by rfl⟩ : syracuseStep 3260627 = 4890941) B4890941
theorem B2173751 : Blo 2173435 2173751 := bstep (se 1 (by rfl) ⟨1630313, by rfl⟩ : syracuseStep 2173751 = 3260627) B3260627
theorem B3668213 : Blo 2173435 3668213 := bbase (se 5 (by rfl) ⟨171947, by rfl⟩ : syracuseStep 3668213 = 343895) (by norm_num)
theorem B2445475 : Blo 2173435 2445475 := bstep (se 1 (by rfl) ⟨1834106, by rfl⟩ : syracuseStep 2445475 = 3668213) B3668213
theorem B3260633 : Blo 2173435 3260633 := bstep (se 2 (by rfl) ⟨1222737, by rfl⟩ : syracuseStep 3260633 = 2445475) B2445475
theorem B2173755 : Blo 2173435 2173755 := bstep (se 1 (by rfl) ⟨1630316, by rfl⟩ : syracuseStep 2173755 = 3260633) B3260633
theorem B2478845 : Blo 2173435 2478845 := bbase (se 3 (by rfl) ⟨464783, by rfl⟩ : syracuseStep 2478845 = 929567) (by norm_num)
theorem B6610253 : Blo 2173435 6610253 := bstep (se 3 (by rfl) ⟨1239422, by rfl⟩ : syracuseStep 6610253 = 2478845) B2478845
theorem B17627341 : Blo 2173435 17627341 := bstep (se 3 (by rfl) ⟨3305126, by rfl⟩ : syracuseStep 17627341 = 6610253) B6610253
theorem B23503121 : Blo 2173435 23503121 := bstep (se 2 (by rfl) ⟨8813670, by rfl⟩ : syracuseStep 23503121 = 17627341) B17627341
theorem B15668747 : Blo 2173435 15668747 := bstep (se 1 (by rfl) ⟨11751560, by rfl⟩ : syracuseStep 15668747 = 23503121) B23503121
theorem B10445831 : Blo 2173435 10445831 := bstep (se 1 (by rfl) ⟨7834373, by rfl⟩ : syracuseStep 10445831 = 15668747) B15668747
theorem B6963887 : Blo 2173435 6963887 := bstep (se 1 (by rfl) ⟨5222915, by rfl⟩ : syracuseStep 6963887 = 10445831) B10445831
theorem B4642591 : Blo 2173435 4642591 := bstep (se 1 (by rfl) ⟨3481943, by rfl⟩ : syracuseStep 4642591 = 6963887) B6963887
theorem B6190121 : Blo 2173435 6190121 := bstep (se 2 (by rfl) ⟨2321295, by rfl⟩ : syracuseStep 6190121 = 4642591) B4642591
theorem B16506989 : Blo 2173435 16506989 := bstep (se 3 (by rfl) ⟨3095060, by rfl⟩ : syracuseStep 16506989 = 6190121) B6190121
theorem B11004659 : Blo 2173435 11004659 := bstep (se 1 (by rfl) ⟨8253494, by rfl⟩ : syracuseStep 11004659 = 16506989) B16506989
theorem B7336439 : Blo 2173435 7336439 := bstep (se 1 (by rfl) ⟨5502329, by rfl⟩ : syracuseStep 7336439 = 11004659) B11004659
theorem B4890959 : Blo 2173435 4890959 := bstep (se 1 (by rfl) ⟨3668219, by rfl⟩ : syracuseStep 4890959 = 7336439) B7336439
theorem B3260639 : Blo 2173435 3260639 := bstep (se 1 (by rfl) ⟨2445479, by rfl⟩ : syracuseStep 3260639 = 4890959) B4890959
theorem B2173759 : Blo 2173435 2173759 := bstep (se 1 (by rfl) ⟨1630319, by rfl⟩ : syracuseStep 2173759 = 3260639) B3260639
theorem B3260645 : Blo 2173435 3260645 := bbase (se 4 (by rfl) ⟨305685, by rfl⟩ : syracuseStep 3260645 = 611371) (by norm_num)
theorem B2173763 : Blo 2173435 2173763 := bstep (se 1 (by rfl) ⟨1630322, by rfl⟩ : syracuseStep 2173763 = 3260645) B3260645
theorem B3481957 : Blo 2173435 3481957 := bbase (se 4 (by rfl) ⟨326433, by rfl⟩ : syracuseStep 3481957 = 652867) (by norm_num)
theorem B4642609 : Blo 2173435 4642609 := bstep (se 2 (by rfl) ⟨1740978, by rfl⟩ : syracuseStep 4642609 = 3481957) B3481957
theorem B6190145 : Blo 2173435 6190145 := bstep (se 2 (by rfl) ⟨2321304, by rfl⟩ : syracuseStep 6190145 = 4642609) B4642609
theorem B4126763 : Blo 2173435 4126763 := bstep (se 1 (by rfl) ⟨3095072, by rfl⟩ : syracuseStep 4126763 = 6190145) B6190145
theorem B2751175 : Blo 2173435 2751175 := bstep (se 1 (by rfl) ⟨2063381, by rfl⟩ : syracuseStep 2751175 = 4126763) B4126763
theorem B3668233 : Blo 2173435 3668233 := bstep (se 2 (by rfl) ⟨1375587, by rfl⟩ : syracuseStep 3668233 = 2751175) B2751175
theorem B4890977 : Blo 2173435 4890977 := bstep (se 2 (by rfl) ⟨1834116, by rfl⟩ : syracuseStep 4890977 = 3668233) B3668233
theorem B3260651 : Blo 2173435 3260651 := bstep (se 1 (by rfl) ⟨2445488, by rfl⟩ : syracuseStep 3260651 = 4890977) B4890977
theorem B2173767 : Blo 2173435 2173767 := bstep (se 1 (by rfl) ⟨1630325, by rfl⟩ : syracuseStep 2173767 = 3260651) B3260651
theorem B2445493 : Blo 2173435 2445493 := bbase (se 5 (by rfl) ⟨114632, by rfl⟩ : syracuseStep 2445493 = 229265) (by norm_num)
theorem B3260657 : Blo 2173435 3260657 := bstep (se 2 (by rfl) ⟨1222746, by rfl⟩ : syracuseStep 3260657 = 2445493) B2445493
theorem B2173771 : Blo 2173435 2173771 := bstep (se 1 (by rfl) ⟨1630328, by rfl⟩ : syracuseStep 2173771 = 3260657) B3260657
theorem B2751185 : Blo 2173435 2751185 := bbase (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) (by norm_num)
theorem B7336493 : Blo 2173435 7336493 := bstep (se 3 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 7336493 = 2751185) B2751185
theorem B4890995 : Blo 2173435 4890995 := bstep (se 1 (by rfl) ⟨3668246, by rfl⟩ : syracuseStep 4890995 = 7336493) B7336493
theorem B3260663 : Blo 2173435 3260663 := bstep (se 1 (by rfl) ⟨2445497, by rfl⟩ : syracuseStep 3260663 = 4890995) B4890995
theorem B2173775 : Blo 2173435 2173775 := bstep (se 1 (by rfl) ⟨1630331, by rfl⟩ : syracuseStep 2173775 = 3260663) B3260663
theorem B3260669 : Blo 2173435 3260669 := bbase (se 3 (by rfl) ⟨611375, by rfl⟩ : syracuseStep 3260669 = 1222751) (by norm_num)
theorem B2173779 : Blo 2173435 2173779 := bstep (se 1 (by rfl) ⟨1630334, by rfl⟩ : syracuseStep 2173779 = 3260669) B3260669
theorem B4891013 : Blo 2173435 4891013 := bbase (se 4 (by rfl) ⟨458532, by rfl⟩ : syracuseStep 4891013 = 917065) (by norm_num)
theorem B3260675 : Blo 2173435 3260675 := bstep (se 1 (by rfl) ⟨2445506, by rfl⟩ : syracuseStep 3260675 = 4891013) B4891013
theorem B2173783 : Blo 2173435 2173783 := bstep (se 1 (by rfl) ⟨1630337, by rfl⟩ : syracuseStep 2173783 = 3260675) B3260675
theorem B3095101 : Blo 2173435 3095101 := bbase (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) (by norm_num)
theorem B4126801 : Blo 2173435 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B5502401 : Blo 2173435 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B3668267 : Blo 2173435 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B2445511 : Blo 2173435 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B3260681 : Blo 2173435 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B2173787 : Blo 2173435 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B11004821 : Blo 2173435 11004821 := bbase (se 6 (by rfl) ⟨257925, by rfl⟩ : syracuseStep 11004821 = 515851) (by norm_num)
theorem B7336547 : Blo 2173435 7336547 := bstep (se 1 (by rfl) ⟨5502410, by rfl⟩ : syracuseStep 7336547 = 11004821) B11004821
theorem B4891031 : Blo 2173435 4891031 := bstep (se 1 (by rfl) ⟨3668273, by rfl⟩ : syracuseStep 4891031 = 7336547) B7336547
theorem B3260687 : Blo 2173435 3260687 := bstep (se 1 (by rfl) ⟨2445515, by rfl⟩ : syracuseStep 3260687 = 4891031) B4891031
theorem B2173791 : Blo 2173435 2173791 := bstep (se 1 (by rfl) ⟨1630343, by rfl⟩ : syracuseStep 2173791 = 3260687) B3260687
theorem B3260693 : Blo 2173435 3260693 := bbase (se 6 (by rfl) ⟨76422, by rfl⟩ : syracuseStep 3260693 = 152845) (by norm_num)
theorem B2173795 : Blo 2173435 2173795 := bstep (se 1 (by rfl) ⟨1630346, by rfl⟩ : syracuseStep 2173795 = 3260693) B3260693
theorem B4957781 : Blo 2173435 4957781 := bbase (se 8 (by rfl) ⟨29049, by rfl⟩ : syracuseStep 4957781 = 58099) (by norm_num)
theorem B13220749 : Blo 2173435 13220749 := bstep (se 3 (by rfl) ⟨2478890, by rfl⟩ : syracuseStep 13220749 = 4957781) B4957781
theorem B17627665 : Blo 2173435 17627665 := bstep (se 2 (by rfl) ⟨6610374, by rfl⟩ : syracuseStep 17627665 = 13220749) B13220749
theorem B23503553 : Blo 2173435 23503553 := bstep (se 2 (by rfl) ⟨8813832, by rfl⟩ : syracuseStep 23503553 = 17627665) B17627665
theorem B15669035 : Blo 2173435 15669035 := bstep (se 1 (by rfl) ⟨11751776, by rfl⟩ : syracuseStep 15669035 = 23503553) B23503553
theorem B10446023 : Blo 2173435 10446023 := bstep (se 1 (by rfl) ⟨7834517, by rfl⟩ : syracuseStep 10446023 = 15669035) B15669035
theorem B27856061 : Blo 2173435 27856061 := bstep (se 3 (by rfl) ⟨5223011, by rfl⟩ : syracuseStep 27856061 = 10446023) B10446023
theorem B18570707 : Blo 2173435 18570707 := bstep (se 1 (by rfl) ⟨13928030, by rfl⟩ : syracuseStep 18570707 = 27856061) B27856061
theorem B12380471 : Blo 2173435 12380471 := bstep (se 1 (by rfl) ⟨9285353, by rfl⟩ : syracuseStep 12380471 = 18570707) B18570707
theorem B8253647 : Blo 2173435 8253647 := bstep (se 1 (by rfl) ⟨6190235, by rfl⟩ : syracuseStep 8253647 = 12380471) B12380471
theorem B5502431 : Blo 2173435 5502431 := bstep (se 1 (by rfl) ⟨4126823, by rfl⟩ : syracuseStep 5502431 = 8253647) B8253647
theorem B3668287 : Blo 2173435 3668287 := bstep (se 1 (by rfl) ⟨2751215, by rfl⟩ : syracuseStep 3668287 = 5502431) B5502431
theorem B4891049 : Blo 2173435 4891049 := bstep (se 2 (by rfl) ⟨1834143, by rfl⟩ : syracuseStep 4891049 = 3668287) B3668287
theorem B3260699 : Blo 2173435 3260699 := bstep (se 1 (by rfl) ⟨2445524, by rfl⟩ : syracuseStep 3260699 = 4891049) B4891049
theorem B2173799 : Blo 2173435 2173799 := bstep (se 1 (by rfl) ⟨1630349, by rfl⟩ : syracuseStep 2173799 = 3260699) B3260699
theorem B2445529 : Blo 2173435 2445529 := bbase (se 2 (by rfl) ⟨917073, by rfl⟩ : syracuseStep 2445529 = 1834147) (by norm_num)
theorem B3260705 : Blo 2173435 3260705 := bstep (se 2 (by rfl) ⟨1222764, by rfl⟩ : syracuseStep 3260705 = 2445529) B2445529
theorem B2173803 : Blo 2173435 2173803 := bstep (se 1 (by rfl) ⟨1630352, by rfl⟩ : syracuseStep 2173803 = 3260705) B3260705
theorem B3482021 : Blo 2173435 3482021 := bbase (se 4 (by rfl) ⟨326439, by rfl⟩ : syracuseStep 3482021 = 652879) (by norm_num)
theorem B2321347 : Blo 2173435 2321347 := bstep (se 1 (by rfl) ⟨1741010, by rfl⟩ : syracuseStep 2321347 = 3482021) B3482021
theorem B3095129 : Blo 2173435 3095129 := bstep (se 2 (by rfl) ⟨1160673, by rfl⟩ : syracuseStep 3095129 = 2321347) B2321347
theorem B8253677 : Blo 2173435 8253677 := bstep (se 3 (by rfl) ⟨1547564, by rfl⟩ : syracuseStep 8253677 = 3095129) B3095129
theorem B5502451 : Blo 2173435 5502451 := bstep (se 1 (by rfl) ⟨4126838, by rfl⟩ : syracuseStep 5502451 = 8253677) B8253677
theorem B7336601 : Blo 2173435 7336601 := bstep (se 2 (by rfl) ⟨2751225, by rfl⟩ : syracuseStep 7336601 = 5502451) B5502451
theorem B4891067 : Blo 2173435 4891067 := bstep (se 1 (by rfl) ⟨3668300, by rfl⟩ : syracuseStep 4891067 = 7336601) B7336601
theorem B3260711 : Blo 2173435 3260711 := bstep (se 1 (by rfl) ⟨2445533, by rfl⟩ : syracuseStep 3260711 = 4891067) B4891067
theorem B2173807 : Blo 2173435 2173807 := bstep (se 1 (by rfl) ⟨1630355, by rfl⟩ : syracuseStep 2173807 = 3260711) B3260711
theorem B3260717 : Blo 2173435 3260717 := bbase (se 3 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 3260717 = 1222769) (by norm_num)
theorem B2173811 : Blo 2173435 2173811 := bstep (se 1 (by rfl) ⟨1630358, by rfl⟩ : syracuseStep 2173811 = 3260717) B3260717
theorem B4891085 : Blo 2173435 4891085 := bbase (se 3 (by rfl) ⟨917078, by rfl⟩ : syracuseStep 4891085 = 1834157) (by norm_num)
theorem B3260723 : Blo 2173435 3260723 := bstep (se 1 (by rfl) ⟨2445542, by rfl⟩ : syracuseStep 3260723 = 4891085) B4891085
theorem B2173815 : Blo 2173435 2173815 := bstep (se 1 (by rfl) ⟨1630361, by rfl⟩ : syracuseStep 2173815 = 3260723) B3260723
theorem B2751241 : Blo 2173435 2751241 := bbase (se 2 (by rfl) ⟨1031715, by rfl⟩ : syracuseStep 2751241 = 2063431) (by norm_num)
theorem B3668321 : Blo 2173435 3668321 := bstep (se 2 (by rfl) ⟨1375620, by rfl⟩ : syracuseStep 3668321 = 2751241) B2751241
theorem B2445547 : Blo 2173435 2445547 := bstep (se 1 (by rfl) ⟨1834160, by rfl⟩ : syracuseStep 2445547 = 3668321) B3668321
theorem B3260729 : Blo 2173435 3260729 := bstep (se 2 (by rfl) ⟨1222773, by rfl⟩ : syracuseStep 3260729 = 2445547) B2445547
theorem B2173819 : Blo 2173435 2173819 := bstep (se 1 (by rfl) ⟨1630364, by rfl⟩ : syracuseStep 2173819 = 3260729) B3260729
theorem B22310261 : Blo 2173435 22310261 := bbase (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) (by norm_num)
theorem B14873507 : Blo 2173435 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B9915671 : Blo 2173435 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B6610447 : Blo 2173435 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B8813929 : Blo 2173435 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B11751905 : Blo 2173435 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B31338413 : Blo 2173435 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B20892275 : Blo 2173435 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B13928183 : Blo 2173435 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B9285455 : Blo 2173435 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B24761213 : Blo 2173435 24761213 := bstep (se 3 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 24761213 = 9285455) B9285455
theorem B16507475 : Blo 2173435 16507475 := bstep (se 1 (by rfl) ⟨12380606, by rfl⟩ : syracuseStep 16507475 = 24761213) B24761213
theorem B11004983 : Blo 2173435 11004983 := bstep (se 1 (by rfl) ⟨8253737, by rfl⟩ : syracuseStep 11004983 = 16507475) B16507475
theorem B7336655 : Blo 2173435 7336655 := bstep (se 1 (by rfl) ⟨5502491, by rfl⟩ : syracuseStep 7336655 = 11004983) B11004983
theorem B4891103 : Blo 2173435 4891103 := bstep (se 1 (by rfl) ⟨3668327, by rfl⟩ : syracuseStep 4891103 = 7336655) B7336655
theorem B3260735 : Blo 2173435 3260735 := bstep (se 1 (by rfl) ⟨2445551, by rfl⟩ : syracuseStep 3260735 = 4891103) B4891103
theorem B2173823 : Blo 2173435 2173823 := bstep (se 1 (by rfl) ⟨1630367, by rfl⟩ : syracuseStep 2173823 = 3260735) B3260735
theorem B3260741 : Blo 2173435 3260741 := bbase (se 4 (by rfl) ⟨305694, by rfl⟩ : syracuseStep 3260741 = 611389) (by norm_num)
theorem B2173827 : Blo 2173435 2173827 := bstep (se 1 (by rfl) ⟨1630370, by rfl⟩ : syracuseStep 2173827 = 3260741) B3260741
theorem B3668341 : Blo 2173435 3668341 := bbase (se 5 (by rfl) ⟨171953, by rfl⟩ : syracuseStep 3668341 = 343907) (by norm_num)
theorem B4891121 : Blo 2173435 4891121 := bstep (se 2 (by rfl) ⟨1834170, by rfl⟩ : syracuseStep 4891121 = 3668341) B3668341
theorem B3260747 : Blo 2173435 3260747 := bstep (se 1 (by rfl) ⟨2445560, by rfl⟩ : syracuseStep 3260747 = 4891121) B4891121
theorem B2173831 : Blo 2173435 2173831 := bstep (se 1 (by rfl) ⟨1630373, by rfl⟩ : syracuseStep 2173831 = 3260747) B3260747
theorem B2445565 : Blo 2173435 2445565 := bbase (se 3 (by rfl) ⟨458543, by rfl⟩ : syracuseStep 2445565 = 917087) (by norm_num)
theorem B3260753 : Blo 2173435 3260753 := bstep (se 2 (by rfl) ⟨1222782, by rfl⟩ : syracuseStep 3260753 = 2445565) B2445565
theorem B2173835 : Blo 2173435 2173835 := bstep (se 1 (by rfl) ⟨1630376, by rfl⟩ : syracuseStep 2173835 = 3260753) B3260753
theorem B7336709 : Blo 2173435 7336709 := bbase (se 4 (by rfl) ⟨687816, by rfl⟩ : syracuseStep 7336709 = 1375633) (by norm_num)
theorem B4891139 : Blo 2173435 4891139 := bstep (se 1 (by rfl) ⟨3668354, by rfl⟩ : syracuseStep 4891139 = 7336709) B7336709
theorem B3260759 : Blo 2173435 3260759 := bstep (se 1 (by rfl) ⟨2445569, by rfl⟩ : syracuseStep 3260759 = 4891139) B4891139
theorem B2173839 : Blo 2173435 2173839 := bstep (se 1 (by rfl) ⟨1630379, by rfl⟩ : syracuseStep 2173839 = 3260759) B3260759
theorem B3260765 : Blo 2173435 3260765 := bbase (se 3 (by rfl) ⟨611393, by rfl⟩ : syracuseStep 3260765 = 1222787) (by norm_num)
theorem B2173843 : Blo 2173435 2173843 := bstep (se 1 (by rfl) ⟨1630382, by rfl⟩ : syracuseStep 2173843 = 3260765) B3260765
theorem B4891157 : Blo 2173435 4891157 := bbase (se 6 (by rfl) ⟨114636, by rfl⟩ : syracuseStep 4891157 = 229273) (by norm_num)
theorem B3260771 : Blo 2173435 3260771 := bstep (se 1 (by rfl) ⟨2445578, by rfl⟩ : syracuseStep 3260771 = 4891157) B4891157
theorem B2173847 : Blo 2173435 2173847 := bstep (se 1 (by rfl) ⟨1630385, by rfl⟩ : syracuseStep 2173847 = 3260771) B3260771
theorem B8253845 : Blo 2173435 8253845 := bbase (se 6 (by rfl) ⟨193449, by rfl⟩ : syracuseStep 8253845 = 386899) (by norm_num)
theorem B5502563 : Blo 2173435 5502563 := bstep (se 1 (by rfl) ⟨4126922, by rfl⟩ : syracuseStep 5502563 = 8253845) B8253845
theorem B3668375 : Blo 2173435 3668375 := bstep (se 1 (by rfl) ⟨2751281, by rfl⟩ : syracuseStep 3668375 = 5502563) B5502563
theorem B2445583 : Blo 2173435 2445583 := bstep (se 1 (by rfl) ⟨1834187, by rfl⟩ : syracuseStep 2445583 = 3668375) B3668375
theorem B3260777 : Blo 2173435 3260777 := bstep (se 2 (by rfl) ⟨1222791, by rfl⟩ : syracuseStep 3260777 = 2445583) B2445583
theorem B2173851 : Blo 2173435 2173851 := bstep (se 1 (by rfl) ⟨1630388, by rfl⟩ : syracuseStep 2173851 = 3260777) B3260777
theorem B12380789 : Blo 2173435 12380789 := bbase (se 5 (by rfl) ⟨580349, by rfl⟩ : syracuseStep 12380789 = 1160699) (by norm_num)
theorem B8253859 : Blo 2173435 8253859 := bstep (se 1 (by rfl) ⟨6190394, by rfl⟩ : syracuseStep 8253859 = 12380789) B12380789
theorem B11005145 : Blo 2173435 11005145 := bstep (se 2 (by rfl) ⟨4126929, by rfl⟩ : syracuseStep 11005145 = 8253859) B8253859
theorem B7336763 : Blo 2173435 7336763 := bstep (se 1 (by rfl) ⟨5502572, by rfl⟩ : syracuseStep 7336763 = 11005145) B11005145
theorem B4891175 : Blo 2173435 4891175 := bstep (se 1 (by rfl) ⟨3668381, by rfl⟩ : syracuseStep 4891175 = 7336763) B7336763
theorem B3260783 : Blo 2173435 3260783 := bstep (se 1 (by rfl) ⟨2445587, by rfl⟩ : syracuseStep 3260783 = 4891175) B4891175
theorem B2173855 : Blo 2173435 2173855 := bstep (se 1 (by rfl) ⟨1630391, by rfl⟩ : syracuseStep 2173855 = 3260783) B3260783
theorem B3260789 : Blo 2173435 3260789 := bbase (se 5 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 3260789 = 305699) (by norm_num)
theorem B2173859 : Blo 2173435 2173859 := bstep (se 1 (by rfl) ⟨1630394, by rfl⟩ : syracuseStep 2173859 = 3260789) B3260789
theorem B5514101 : Blo 2173435 5514101 := bbase (se 5 (by rfl) ⟨258473, by rfl⟩ : syracuseStep 5514101 = 516947) (by norm_num)
theorem B3676067 : Blo 2173435 3676067 := bstep (se 1 (by rfl) ⟨2757050, by rfl⟩ : syracuseStep 3676067 = 5514101) B5514101
theorem B39211381 : Blo 2173435 39211381 := bstep (se 5 (by rfl) ⟨1838033, by rfl⟩ : syracuseStep 39211381 = 3676067) B3676067
theorem B209127365 : Blo 2173435 209127365 := bstep (se 4 (by rfl) ⟨19605690, by rfl⟩ : syracuseStep 209127365 = 39211381) B39211381
theorem B139418243 : Blo 2173435 139418243 := bstep (se 1 (by rfl) ⟨104563682, by rfl⟩ : syracuseStep 139418243 = 209127365) B209127365
theorem B92945495 : Blo 2173435 92945495 := bstep (se 1 (by rfl) ⟨69709121, by rfl⟩ : syracuseStep 92945495 = 139418243) B139418243
theorem B61963663 : Blo 2173435 61963663 := bstep (se 1 (by rfl) ⟨46472747, by rfl⟩ : syracuseStep 61963663 = 92945495) B92945495
theorem B82618217 : Blo 2173435 82618217 := bstep (se 2 (by rfl) ⟨30981831, by rfl⟩ : syracuseStep 82618217 = 61963663) B61963663
theorem B55078811 : Blo 2173435 55078811 := bstep (se 1 (by rfl) ⟨41309108, by rfl⟩ : syracuseStep 55078811 = 82618217) B82618217
theorem B36719207 : Blo 2173435 36719207 := bstep (se 1 (by rfl) ⟨27539405, by rfl⟩ : syracuseStep 36719207 = 55078811) B55078811
theorem B24479471 : Blo 2173435 24479471 := bstep (se 1 (by rfl) ⟨18359603, by rfl⟩ : syracuseStep 24479471 = 36719207) B36719207
theorem B16319647 : Blo 2173435 16319647 := bstep (se 1 (by rfl) ⟨12239735, by rfl⟩ : syracuseStep 16319647 = 24479471) B24479471
theorem B21759529 : Blo 2173435 21759529 := bstep (se 2 (by rfl) ⟨8159823, by rfl⟩ : syracuseStep 21759529 = 16319647) B16319647
theorem B29012705 : Blo 2173435 29012705 := bstep (se 2 (by rfl) ⟨10879764, by rfl⟩ : syracuseStep 29012705 = 21759529) B21759529
theorem B19341803 : Blo 2173435 19341803 := bstep (se 1 (by rfl) ⟨14506352, by rfl⟩ : syracuseStep 19341803 = 29012705) B29012705
theorem B12894535 : Blo 2173435 12894535 := bstep (se 1 (by rfl) ⟨9670901, by rfl⟩ : syracuseStep 12894535 = 19341803) B19341803
theorem B68770853 : Blo 2173435 68770853 := bstep (se 4 (by rfl) ⟨6447267, by rfl⟩ : syracuseStep 68770853 = 12894535) B12894535
theorem B45847235 : Blo 2173435 45847235 := bstep (se 1 (by rfl) ⟨34385426, by rfl⟩ : syracuseStep 45847235 = 68770853) B68770853
theorem B122259293 : Blo 2173435 122259293 := bstep (se 3 (by rfl) ⟨22923617, by rfl⟩ : syracuseStep 122259293 = 45847235) B45847235
theorem B81506195 : Blo 2173435 81506195 := bstep (se 1 (by rfl) ⟨61129646, by rfl⟩ : syracuseStep 81506195 = 122259293) B122259293
theorem B54337463 : Blo 2173435 54337463 := bstep (se 1 (by rfl) ⟨40753097, by rfl⟩ : syracuseStep 54337463 = 81506195) B81506195
theorem B36224975 : Blo 2173435 36224975 := bstep (se 1 (by rfl) ⟨27168731, by rfl⟩ : syracuseStep 36224975 = 54337463) B54337463
theorem B24149983 : Blo 2173435 24149983 := bstep (se 1 (by rfl) ⟨18112487, by rfl⟩ : syracuseStep 24149983 = 36224975) B36224975
theorem B32199977 : Blo 2173435 32199977 := bstep (se 2 (by rfl) ⟨12074991, by rfl⟩ : syracuseStep 32199977 = 24149983) B24149983
theorem B85866605 : Blo 2173435 85866605 := bstep (se 3 (by rfl) ⟨16099988, by rfl⟩ : syracuseStep 85866605 = 32199977) B32199977
theorem B57244403 : Blo 2173435 57244403 := bstep (se 1 (by rfl) ⟨42933302, by rfl⟩ : syracuseStep 57244403 = 85866605) B85866605
theorem B38162935 : Blo 2173435 38162935 := bstep (se 1 (by rfl) ⟨28622201, by rfl⟩ : syracuseStep 38162935 = 57244403) B57244403
theorem B50883913 : Blo 2173435 50883913 := bstep (se 2 (by rfl) ⟨19081467, by rfl⟩ : syracuseStep 50883913 = 38162935) B38162935
theorem B67845217 : Blo 2173435 67845217 := bstep (se 2 (by rfl) ⟨25441956, by rfl⟩ : syracuseStep 67845217 = 50883913) B50883913
theorem B90460289 : Blo 2173435 90460289 := bstep (se 2 (by rfl) ⟨33922608, by rfl⟩ : syracuseStep 90460289 = 67845217) B67845217
theorem B60306859 : Blo 2173435 60306859 := bstep (se 1 (by rfl) ⟨45230144, by rfl⟩ : syracuseStep 60306859 = 90460289) B90460289
theorem B80409145 : Blo 2173435 80409145 := bstep (se 2 (by rfl) ⟨30153429, by rfl⟩ : syracuseStep 80409145 = 60306859) B60306859
theorem B107212193 : Blo 2173435 107212193 := bstep (se 2 (by rfl) ⟨40204572, by rfl⟩ : syracuseStep 107212193 = 80409145) B80409145
theorem B71474795 : Blo 2173435 71474795 := bstep (se 1 (by rfl) ⟨53606096, by rfl⟩ : syracuseStep 71474795 = 107212193) B107212193
theorem B47649863 : Blo 2173435 47649863 := bstep (se 1 (by rfl) ⟨35737397, by rfl⟩ : syracuseStep 47649863 = 71474795) B71474795
theorem B31766575 : Blo 2173435 31766575 := bstep (se 1 (by rfl) ⟨23824931, by rfl⟩ : syracuseStep 31766575 = 47649863) B47649863
theorem B42355433 : Blo 2173435 42355433 := bstep (se 2 (by rfl) ⟨15883287, by rfl⟩ : syracuseStep 42355433 = 31766575) B31766575
theorem B112947821 : Blo 2173435 112947821 := bstep (se 3 (by rfl) ⟨21177716, by rfl⟩ : syracuseStep 112947821 = 42355433) B42355433
theorem B75298547 : Blo 2173435 75298547 := bstep (se 1 (by rfl) ⟨56473910, by rfl⟩ : syracuseStep 75298547 = 112947821) B112947821
theorem B50199031 : Blo 2173435 50199031 := bstep (se 1 (by rfl) ⟨37649273, by rfl⟩ : syracuseStep 50199031 = 75298547) B75298547
theorem B66932041 : Blo 2173435 66932041 := bstep (se 2 (by rfl) ⟨25099515, by rfl⟩ : syracuseStep 66932041 = 50199031) B50199031
theorem B89242721 : Blo 2173435 89242721 := bstep (se 2 (by rfl) ⟨33466020, by rfl⟩ : syracuseStep 89242721 = 66932041) B66932041
theorem B59495147 : Blo 2173435 59495147 := bstep (se 1 (by rfl) ⟨44621360, by rfl⟩ : syracuseStep 59495147 = 89242721) B89242721
theorem B39663431 : Blo 2173435 39663431 := bstep (se 1 (by rfl) ⟨29747573, by rfl⟩ : syracuseStep 39663431 = 59495147) B59495147
theorem B26442287 : Blo 2173435 26442287 := bstep (se 1 (by rfl) ⟨19831715, by rfl⟩ : syracuseStep 26442287 = 39663431) B39663431
theorem B17628191 : Blo 2173435 17628191 := bstep (se 1 (by rfl) ⟨13221143, by rfl⟩ : syracuseStep 17628191 = 26442287) B26442287
theorem B11752127 : Blo 2173435 11752127 := bstep (se 1 (by rfl) ⟨8814095, by rfl⟩ : syracuseStep 11752127 = 17628191) B17628191
theorem B7834751 : Blo 2173435 7834751 := bstep (se 1 (by rfl) ⟨5876063, by rfl⟩ : syracuseStep 7834751 = 11752127) B11752127
theorem B5223167 : Blo 2173435 5223167 := bstep (se 1 (by rfl) ⟨3917375, by rfl⟩ : syracuseStep 5223167 = 7834751) B7834751
theorem B3482111 : Blo 2173435 3482111 := bstep (se 1 (by rfl) ⟨2611583, by rfl⟩ : syracuseStep 3482111 = 5223167) B5223167
theorem B2321407 : Blo 2173435 2321407 := bstep (se 1 (by rfl) ⟨1741055, by rfl⟩ : syracuseStep 2321407 = 3482111) B3482111
theorem B3095209 : Blo 2173435 3095209 := bstep (se 2 (by rfl) ⟨1160703, by rfl⟩ : syracuseStep 3095209 = 2321407) B2321407
theorem B4126945 : Blo 2173435 4126945 := bstep (se 2 (by rfl) ⟨1547604, by rfl⟩ : syracuseStep 4126945 = 3095209) B3095209
theorem B5502593 : Blo 2173435 5502593 := bstep (se 2 (by rfl) ⟨2063472, by rfl⟩ : syracuseStep 5502593 = 4126945) B4126945
theorem B3668395 : Blo 2173435 3668395 := bstep (se 1 (by rfl) ⟨2751296, by rfl⟩ : syracuseStep 3668395 = 5502593) B5502593
theorem B4891193 : Blo 2173435 4891193 := bstep (se 2 (by rfl) ⟨1834197, by rfl⟩ : syracuseStep 4891193 = 3668395) B3668395
theorem B3260795 : Blo 2173435 3260795 := bstep (se 1 (by rfl) ⟨2445596, by rfl⟩ : syracuseStep 3260795 = 4891193) B4891193
theorem B2173863 : Blo 2173435 2173863 := bstep (se 1 (by rfl) ⟨1630397, by rfl⟩ : syracuseStep 2173863 = 3260795) B3260795
theorem B2445601 : Blo 2173435 2445601 := bbase (se 2 (by rfl) ⟨917100, by rfl⟩ : syracuseStep 2445601 = 1834201) (by norm_num)
theorem B3260801 : Blo 2173435 3260801 := bstep (se 2 (by rfl) ⟨1222800, by rfl⟩ : syracuseStep 3260801 = 2445601) B2445601
theorem B2173867 : Blo 2173435 2173867 := bstep (se 1 (by rfl) ⟨1630400, by rfl⟩ : syracuseStep 2173867 = 3260801) B3260801
theorem B5502613 : Blo 2173435 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B7336817 : Blo 2173435 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B4891211 : Blo 2173435 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B3260807 : Blo 2173435 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B2173871 : Blo 2173435 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B3260813 : Blo 2173435 3260813 := bbase (se 3 (by rfl) ⟨611402, by rfl⟩ : syracuseStep 3260813 = 1222805) (by norm_num)
theorem B2173875 : Blo 2173435 2173875 := bstep (se 1 (by rfl) ⟨1630406, by rfl⟩ : syracuseStep 2173875 = 3260813) B3260813
theorem B4891229 : Blo 2173435 4891229 := bbase (se 3 (by rfl) ⟨917105, by rfl⟩ : syracuseStep 4891229 = 1834211) (by norm_num)
theorem B3260819 : Blo 2173435 3260819 := bstep (se 1 (by rfl) ⟨2445614, by rfl⟩ : syracuseStep 3260819 = 4891229) B4891229
theorem B2173879 : Blo 2173435 2173879 := bstep (se 1 (by rfl) ⟨1630409, by rfl⟩ : syracuseStep 2173879 = 3260819) B3260819
theorem B3668429 : Blo 2173435 3668429 := bbase (se 3 (by rfl) ⟨687830, by rfl⟩ : syracuseStep 3668429 = 1375661) (by norm_num)
theorem B2445619 : Blo 2173435 2445619 := bstep (se 1 (by rfl) ⟨1834214, by rfl⟩ : syracuseStep 2445619 = 3668429) B3668429
theorem B3260825 : Blo 2173435 3260825 := bstep (se 2 (by rfl) ⟨1222809, by rfl⟩ : syracuseStep 3260825 = 2445619) B2445619
theorem B2173883 : Blo 2173435 2173883 := bstep (se 1 (by rfl) ⟨1630412, by rfl⟩ : syracuseStep 2173883 = 3260825) B3260825
theorem B8366597 : Blo 2173435 8366597 := bbase (se 4 (by rfl) ⟨784368, by rfl⟩ : syracuseStep 8366597 = 1568737) (by norm_num)
theorem B5577731 : Blo 2173435 5577731 := bstep (se 1 (by rfl) ⟨4183298, by rfl⟩ : syracuseStep 5577731 = 8366597) B8366597
theorem B3718487 : Blo 2173435 3718487 := bstep (se 1 (by rfl) ⟨2788865, by rfl⟩ : syracuseStep 3718487 = 5577731) B5577731
theorem B9915965 : Blo 2173435 9915965 := bstep (se 3 (by rfl) ⟨1859243, by rfl⟩ : syracuseStep 9915965 = 3718487) B3718487
theorem B6610643 : Blo 2173435 6610643 := bstep (se 1 (by rfl) ⟨4957982, by rfl⟩ : syracuseStep 6610643 = 9915965) B9915965
theorem B4407095 : Blo 2173435 4407095 := bstep (se 1 (by rfl) ⟨3305321, by rfl⟩ : syracuseStep 4407095 = 6610643) B6610643
theorem B2938063 : Blo 2173435 2938063 := bstep (se 1 (by rfl) ⟨2203547, by rfl⟩ : syracuseStep 2938063 = 4407095) B4407095
theorem B3917417 : Blo 2173435 3917417 := bstep (se 2 (by rfl) ⟨1469031, by rfl⟩ : syracuseStep 3917417 = 2938063) B2938063
theorem B10446445 : Blo 2173435 10446445 := bstep (se 3 (by rfl) ⟨1958708, by rfl⟩ : syracuseStep 10446445 = 3917417) B3917417
theorem B13928593 : Blo 2173435 13928593 := bstep (se 2 (by rfl) ⟨5223222, by rfl⟩ : syracuseStep 13928593 = 10446445) B10446445
theorem B18571457 : Blo 2173435 18571457 := bstep (se 2 (by rfl) ⟨6964296, by rfl⟩ : syracuseStep 18571457 = 13928593) B13928593
theorem B12380971 : Blo 2173435 12380971 := bstep (se 1 (by rfl) ⟨9285728, by rfl⟩ : syracuseStep 12380971 = 18571457) B18571457
theorem B16507961 : Blo 2173435 16507961 := bstep (se 2 (by rfl) ⟨6190485, by rfl⟩ : syracuseStep 16507961 = 12380971) B12380971
theorem B11005307 : Blo 2173435 11005307 := bstep (se 1 (by rfl) ⟨8253980, by rfl⟩ : syracuseStep 11005307 = 16507961) B16507961
theorem B7336871 : Blo 2173435 7336871 := bstep (se 1 (by rfl) ⟨5502653, by rfl⟩ : syracuseStep 7336871 = 11005307) B11005307
theorem B4891247 : Blo 2173435 4891247 := bstep (se 1 (by rfl) ⟨3668435, by rfl⟩ : syracuseStep 4891247 = 7336871) B7336871
theorem B3260831 : Blo 2173435 3260831 := bstep (se 1 (by rfl) ⟨2445623, by rfl⟩ : syracuseStep 3260831 = 4891247) B4891247
theorem B2173887 : Blo 2173435 2173887 := bstep (se 1 (by rfl) ⟨1630415, by rfl⟩ : syracuseStep 2173887 = 3260831) B3260831
theorem B3260837 : Blo 2173435 3260837 := bbase (se 4 (by rfl) ⟨305703, by rfl⟩ : syracuseStep 3260837 = 611407) (by norm_num)
theorem B2173891 : Blo 2173435 2173891 := bstep (se 1 (by rfl) ⟨1630418, by rfl⟩ : syracuseStep 2173891 = 3260837) B3260837
theorem B2751337 : Blo 2173435 2751337 := bbase (se 2 (by rfl) ⟨1031751, by rfl⟩ : syracuseStep 2751337 = 2063503) (by norm_num)
theorem B3668449 : Blo 2173435 3668449 := bstep (se 2 (by rfl) ⟨1375668, by rfl⟩ : syracuseStep 3668449 = 2751337) B2751337
theorem B4891265 : Blo 2173435 4891265 := bstep (se 2 (by rfl) ⟨1834224, by rfl⟩ : syracuseStep 4891265 = 3668449) B3668449
theorem B3260843 : Blo 2173435 3260843 := bstep (se 1 (by rfl) ⟨2445632, by rfl⟩ : syracuseStep 3260843 = 4891265) B4891265
theorem B2173895 : Blo 2173435 2173895 := bstep (se 1 (by rfl) ⟨1630421, by rfl⟩ : syracuseStep 2173895 = 3260843) B3260843
theorem B2445637 : Blo 2173435 2445637 := bbase (se 4 (by rfl) ⟨229278, by rfl⟩ : syracuseStep 2445637 = 458557) (by norm_num)
theorem B3260849 : Blo 2173435 3260849 := bstep (se 2 (by rfl) ⟨1222818, by rfl⟩ : syracuseStep 3260849 = 2445637) B2445637
theorem B2173899 : Blo 2173435 2173899 := bstep (se 1 (by rfl) ⟨1630424, by rfl⟩ : syracuseStep 2173899 = 3260849) B3260849
theorem B4127021 : Blo 2173435 4127021 := bbase (se 3 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 4127021 = 1547633) (by norm_num)
theorem B2751347 : Blo 2173435 2751347 := bstep (se 1 (by rfl) ⟨2063510, by rfl⟩ : syracuseStep 2751347 = 4127021) B4127021
theorem B7336925 : Blo 2173435 7336925 := bstep (se 3 (by rfl) ⟨1375673, by rfl⟩ : syracuseStep 7336925 = 2751347) B2751347
theorem B4891283 : Blo 2173435 4891283 := bstep (se 1 (by rfl) ⟨3668462, by rfl⟩ : syracuseStep 4891283 = 7336925) B7336925
theorem B3260855 : Blo 2173435 3260855 := bstep (se 1 (by rfl) ⟨2445641, by rfl⟩ : syracuseStep 3260855 = 4891283) B4891283
theorem B2173903 : Blo 2173435 2173903 := bstep (se 1 (by rfl) ⟨1630427, by rfl⟩ : syracuseStep 2173903 = 3260855) B3260855
theorem B3260861 : Blo 2173435 3260861 := bbase (se 3 (by rfl) ⟨611411, by rfl⟩ : syracuseStep 3260861 = 1222823) (by norm_num)
theorem B2173907 : Blo 2173435 2173907 := bstep (se 1 (by rfl) ⟨1630430, by rfl⟩ : syracuseStep 2173907 = 3260861) B3260861
theorem B4891301 : Blo 2173435 4891301 := bbase (se 4 (by rfl) ⟨458559, by rfl⟩ : syracuseStep 4891301 = 917119) (by norm_num)
theorem B3260867 : Blo 2173435 3260867 := bstep (se 1 (by rfl) ⟨2445650, by rfl⟩ : syracuseStep 3260867 = 4891301) B4891301
theorem B2173911 : Blo 2173435 2173911 := bstep (se 1 (by rfl) ⟨1630433, by rfl⟩ : syracuseStep 2173911 = 3260867) B3260867
theorem B5502725 : Blo 2173435 5502725 := bbase (se 4 (by rfl) ⟨515880, by rfl⟩ : syracuseStep 5502725 = 1031761) (by norm_num)
theorem B3668483 : Blo 2173435 3668483 := bstep (se 1 (by rfl) ⟨2751362, by rfl⟩ : syracuseStep 3668483 = 5502725) B5502725
theorem B2445655 : Blo 2173435 2445655 := bstep (se 1 (by rfl) ⟨1834241, by rfl⟩ : syracuseStep 2445655 = 3668483) B3668483
theorem B3260873 : Blo 2173435 3260873 := bstep (se 2 (by rfl) ⟨1222827, by rfl⟩ : syracuseStep 3260873 = 2445655) B2445655
theorem B2173915 : Blo 2173435 2173915 := bstep (se 1 (by rfl) ⟨1630436, by rfl⟩ : syracuseStep 2173915 = 3260873) B3260873
theorem B4642933 : Blo 2173435 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B6190577 : Blo 2173435 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B4127051 : Blo 2173435 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B11005469 : Blo 2173435 11005469 := bstep (se 3 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 11005469 = 4127051) B4127051
theorem B7336979 : Blo 2173435 7336979 := bstep (se 1 (by rfl) ⟨5502734, by rfl⟩ : syracuseStep 7336979 = 11005469) B11005469
theorem B4891319 : Blo 2173435 4891319 := bstep (se 1 (by rfl) ⟨3668489, by rfl⟩ : syracuseStep 4891319 = 7336979) B7336979
theorem B3260879 : Blo 2173435 3260879 := bstep (se 1 (by rfl) ⟨2445659, by rfl⟩ : syracuseStep 3260879 = 4891319) B4891319
theorem B2173919 : Blo 2173435 2173919 := bstep (se 1 (by rfl) ⟨1630439, by rfl⟩ : syracuseStep 2173919 = 3260879) B3260879
theorem B3260885 : Blo 2173435 3260885 := bbase (se 7 (by rfl) ⟨38213, by rfl⟩ : syracuseStep 3260885 = 76427) (by norm_num)
theorem B2173923 : Blo 2173435 2173923 := bstep (se 1 (by rfl) ⟨1630442, by rfl⟩ : syracuseStep 2173923 = 3260885) B3260885
theorem B8254133 : Blo 2173435 8254133 := bbase (se 5 (by rfl) ⟨386912, by rfl⟩ : syracuseStep 8254133 = 773825) (by norm_num)
theorem B5502755 : Blo 2173435 5502755 := bstep (se 1 (by rfl) ⟨4127066, by rfl⟩ : syracuseStep 5502755 = 8254133) B8254133
theorem B3668503 : Blo 2173435 3668503 := bstep (se 1 (by rfl) ⟨2751377, by rfl⟩ : syracuseStep 3668503 = 5502755) B5502755
theorem B4891337 : Blo 2173435 4891337 := bstep (se 2 (by rfl) ⟨1834251, by rfl⟩ : syracuseStep 4891337 = 3668503) B3668503
theorem B3260891 : Blo 2173435 3260891 := bstep (se 1 (by rfl) ⟨2445668, by rfl⟩ : syracuseStep 3260891 = 4891337) B4891337
theorem B2173927 : Blo 2173435 2173927 := bstep (se 1 (by rfl) ⟨1630445, by rfl⟩ : syracuseStep 2173927 = 3260891) B3260891
theorem B2445673 : Blo 2173435 2445673 := bbase (se 2 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 2445673 = 1834255) (by norm_num)
theorem B3260897 : Blo 2173435 3260897 := bstep (se 2 (by rfl) ⟨1222836, by rfl⟩ : syracuseStep 3260897 = 2445673) B2445673
theorem B2173931 : Blo 2173435 2173931 := bstep (se 1 (by rfl) ⟨1630448, by rfl⟩ : syracuseStep 2173931 = 3260897) B3260897
theorem B10446677 : Blo 2173435 10446677 := bbase (se 9 (by rfl) ⟨30605, by rfl⟩ : syracuseStep 10446677 = 61211) (by norm_num)
theorem B6964451 : Blo 2173435 6964451 := bstep (se 1 (by rfl) ⟨5223338, by rfl⟩ : syracuseStep 6964451 = 10446677) B10446677
theorem B4642967 : Blo 2173435 4642967 := bstep (se 1 (by rfl) ⟨3482225, by rfl⟩ : syracuseStep 4642967 = 6964451) B6964451
theorem B12381245 : Blo 2173435 12381245 := bstep (se 3 (by rfl) ⟨2321483, by rfl⟩ : syracuseStep 12381245 = 4642967) B4642967
theorem B8254163 : Blo 2173435 8254163 := bstep (se 1 (by rfl) ⟨6190622, by rfl⟩ : syracuseStep 8254163 = 12381245) B12381245
theorem B5502775 : Blo 2173435 5502775 := bstep (se 1 (by rfl) ⟨4127081, by rfl⟩ : syracuseStep 5502775 = 8254163) B8254163
theorem B7337033 : Blo 2173435 7337033 := bstep (se 2 (by rfl) ⟨2751387, by rfl⟩ : syracuseStep 7337033 = 5502775) B5502775
theorem B4891355 : Blo 2173435 4891355 := bstep (se 1 (by rfl) ⟨3668516, by rfl⟩ : syracuseStep 4891355 = 7337033) B7337033
theorem B3260903 : Blo 2173435 3260903 := bstep (se 1 (by rfl) ⟨2445677, by rfl⟩ : syracuseStep 3260903 = 4891355) B4891355
theorem B2173935 : Blo 2173435 2173935 := bstep (se 1 (by rfl) ⟨1630451, by rfl⟩ : syracuseStep 2173935 = 3260903) B3260903
theorem B3260909 : Blo 2173435 3260909 := bbase (se 3 (by rfl) ⟨611420, by rfl⟩ : syracuseStep 3260909 = 1222841) (by norm_num)
theorem B2173939 : Blo 2173435 2173939 := bstep (se 1 (by rfl) ⟨1630454, by rfl⟩ : syracuseStep 2173939 = 3260909) B3260909
theorem B4891373 : Blo 2173435 4891373 := bbase (se 3 (by rfl) ⟨917132, by rfl⟩ : syracuseStep 4891373 = 1834265) (by norm_num)
theorem B3260915 : Blo 2173435 3260915 := bstep (se 1 (by rfl) ⟨2445686, by rfl⟩ : syracuseStep 3260915 = 4891373) B4891373
theorem B2173943 : Blo 2173435 2173943 := bstep (se 1 (by rfl) ⟨1630457, by rfl⟩ : syracuseStep 2173943 = 3260915) B3260915
theorem B2321497 : Blo 2173435 2321497 := bbase (se 2 (by rfl) ⟨870561, by rfl⟩ : syracuseStep 2321497 = 1741123) (by norm_num)
theorem B3095329 : Blo 2173435 3095329 := bstep (se 2 (by rfl) ⟨1160748, by rfl⟩ : syracuseStep 3095329 = 2321497) B2321497
theorem B4127105 : Blo 2173435 4127105 := bstep (se 2 (by rfl) ⟨1547664, by rfl⟩ : syracuseStep 4127105 = 3095329) B3095329
theorem B2751403 : Blo 2173435 2751403 := bstep (se 1 (by rfl) ⟨2063552, by rfl⟩ : syracuseStep 2751403 = 4127105) B4127105
theorem B3668537 : Blo 2173435 3668537 := bstep (se 2 (by rfl) ⟨1375701, by rfl⟩ : syracuseStep 3668537 = 2751403) B2751403
theorem B2445691 : Blo 2173435 2445691 := bstep (se 1 (by rfl) ⟨1834268, by rfl⟩ : syracuseStep 2445691 = 3668537) B3668537
theorem B3260921 : Blo 2173435 3260921 := bstep (se 2 (by rfl) ⟨1222845, by rfl⟩ : syracuseStep 3260921 = 2445691) B2445691
theorem B2173947 : Blo 2173435 2173947 := bstep (se 1 (by rfl) ⟨1630460, by rfl⟩ : syracuseStep 2173947 = 3260921) B3260921
theorem B3970981 : Blo 2173435 3970981 := bbase (se 4 (by rfl) ⟨372279, by rfl⟩ : syracuseStep 3970981 = 744559) (by norm_num)
theorem B5294641 : Blo 2173435 5294641 := bstep (se 2 (by rfl) ⟨1985490, by rfl⟩ : syracuseStep 5294641 = 3970981) B3970981
theorem B7059521 : Blo 2173435 7059521 := bstep (se 2 (by rfl) ⟨2647320, by rfl⟩ : syracuseStep 7059521 = 5294641) B5294641
theorem B18825389 : Blo 2173435 18825389 := bstep (se 3 (by rfl) ⟨3529760, by rfl⟩ : syracuseStep 18825389 = 7059521) B7059521
theorem B12550259 : Blo 2173435 12550259 := bstep (se 1 (by rfl) ⟨9412694, by rfl⟩ : syracuseStep 12550259 = 18825389) B18825389
theorem B33467357 : Blo 2173435 33467357 := bstep (se 3 (by rfl) ⟨6275129, by rfl⟩ : syracuseStep 33467357 = 12550259) B12550259
theorem B22311571 : Blo 2173435 22311571 := bstep (se 1 (by rfl) ⟨16733678, by rfl⟩ : syracuseStep 22311571 = 33467357) B33467357
theorem B29748761 : Blo 2173435 29748761 := bstep (se 2 (by rfl) ⟨11155785, by rfl⟩ : syracuseStep 29748761 = 22311571) B22311571
theorem B19832507 : Blo 2173435 19832507 := bstep (se 1 (by rfl) ⟨14874380, by rfl⟩ : syracuseStep 19832507 = 29748761) B29748761
theorem B13221671 : Blo 2173435 13221671 := bstep (se 1 (by rfl) ⟨9916253, by rfl⟩ : syracuseStep 13221671 = 19832507) B19832507
theorem B35257789 : Blo 2173435 35257789 := bstep (se 3 (by rfl) ⟨6610835, by rfl⟩ : syracuseStep 35257789 = 13221671) B13221671
theorem B47010385 : Blo 2173435 47010385 := bstep (se 2 (by rfl) ⟨17628894, by rfl⟩ : syracuseStep 47010385 = 35257789) B35257789
theorem B62680513 : Blo 2173435 62680513 := bstep (se 2 (by rfl) ⟨23505192, by rfl⟩ : syracuseStep 62680513 = 47010385) B47010385
theorem B83574017 : Blo 2173435 83574017 := bstep (se 2 (by rfl) ⟨31340256, by rfl⟩ : syracuseStep 83574017 = 62680513) B62680513
theorem B55716011 : Blo 2173435 55716011 := bstep (se 1 (by rfl) ⟨41787008, by rfl⟩ : syracuseStep 55716011 = 83574017) B83574017
theorem B37144007 : Blo 2173435 37144007 := bstep (se 1 (by rfl) ⟨27858005, by rfl⟩ : syracuseStep 37144007 = 55716011) B55716011
theorem B24762671 : Blo 2173435 24762671 := bstep (se 1 (by rfl) ⟨18572003, by rfl⟩ : syracuseStep 24762671 = 37144007) B37144007
theorem B16508447 : Blo 2173435 16508447 := bstep (se 1 (by rfl) ⟨12381335, by rfl⟩ : syracuseStep 16508447 = 24762671) B24762671
theorem B11005631 : Blo 2173435 11005631 := bstep (se 1 (by rfl) ⟨8254223, by rfl⟩ : syracuseStep 11005631 = 16508447) B16508447
theorem B7337087 : Blo 2173435 7337087 := bstep (se 1 (by rfl) ⟨5502815, by rfl⟩ : syracuseStep 7337087 = 11005631) B11005631
theorem B4891391 : Blo 2173435 4891391 := bstep (se 1 (by rfl) ⟨3668543, by rfl⟩ : syracuseStep 4891391 = 7337087) B7337087
theorem B3260927 : Blo 2173435 3260927 := bstep (se 1 (by rfl) ⟨2445695, by rfl⟩ : syracuseStep 3260927 = 4891391) B4891391
theorem B2173951 : Blo 2173435 2173951 := bstep (se 1 (by rfl) ⟨1630463, by rfl⟩ : syracuseStep 2173951 = 3260927) B3260927
theorem B3260933 : Blo 2173435 3260933 := bbase (se 4 (by rfl) ⟨305712, by rfl⟩ : syracuseStep 3260933 = 611425) (by norm_num)
theorem B2173955 : Blo 2173435 2173955 := bstep (se 1 (by rfl) ⟨1630466, by rfl⟩ : syracuseStep 2173955 = 3260933) B3260933
theorem B3668557 : Blo 2173435 3668557 := bbase (se 3 (by rfl) ⟨687854, by rfl⟩ : syracuseStep 3668557 = 1375709) (by norm_num)
theorem B4891409 : Blo 2173435 4891409 := bstep (se 2 (by rfl) ⟨1834278, by rfl⟩ : syracuseStep 4891409 = 3668557) B3668557
theorem B3260939 : Blo 2173435 3260939 := bstep (se 1 (by rfl) ⟨2445704, by rfl⟩ : syracuseStep 3260939 = 4891409) B4891409
theorem B2173959 : Blo 2173435 2173959 := bstep (se 1 (by rfl) ⟨1630469, by rfl⟩ : syracuseStep 2173959 = 3260939) B3260939
theorem B2445709 : Blo 2173435 2445709 := bbase (se 3 (by rfl) ⟨458570, by rfl⟩ : syracuseStep 2445709 = 917141) (by norm_num)
theorem B3260945 : Blo 2173435 3260945 := bstep (se 2 (by rfl) ⟨1222854, by rfl⟩ : syracuseStep 3260945 = 2445709) B2445709
theorem B2173963 : Blo 2173435 2173963 := bstep (se 1 (by rfl) ⟨1630472, by rfl⟩ : syracuseStep 2173963 = 3260945) B3260945
theorem B7337141 : Blo 2173435 7337141 := bbase (se 5 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 7337141 = 687857) (by norm_num)
theorem B4891427 : Blo 2173435 4891427 := bstep (se 1 (by rfl) ⟨3668570, by rfl⟩ : syracuseStep 4891427 = 7337141) B7337141
theorem B3260951 : Blo 2173435 3260951 := bstep (se 1 (by rfl) ⟨2445713, by rfl⟩ : syracuseStep 3260951 = 4891427) B4891427
theorem B2173967 : Blo 2173435 2173967 := bstep (se 1 (by rfl) ⟨1630475, by rfl⟩ : syracuseStep 2173967 = 3260951) B3260951
theorem B3260957 : Blo 2173435 3260957 := bbase (se 3 (by rfl) ⟨611429, by rfl⟩ : syracuseStep 3260957 = 1222859) (by norm_num)
theorem B2173971 : Blo 2173435 2173971 := bstep (se 1 (by rfl) ⟨1630478, by rfl⟩ : syracuseStep 2173971 = 3260957) B3260957
theorem B4891445 : Blo 2173435 4891445 := bbase (se 5 (by rfl) ⟨229286, by rfl⟩ : syracuseStep 4891445 = 458573) (by norm_num)
theorem B3260963 : Blo 2173435 3260963 := bstep (se 1 (by rfl) ⟨2445722, by rfl⟩ : syracuseStep 3260963 = 4891445) B4891445
theorem B2173975 : Blo 2173435 2173975 := bstep (se 1 (by rfl) ⟨1630481, by rfl⟩ : syracuseStep 2173975 = 3260963) B3260963
theorem B4467413 : Blo 2173435 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B11913101 : Blo 2173435 11913101 := bstep (se 3 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 11913101 = 4467413) B4467413
theorem B7942067 : Blo 2173435 7942067 := bstep (se 1 (by rfl) ⟨5956550, by rfl⟩ : syracuseStep 7942067 = 11913101) B11913101
theorem B5294711 : Blo 2173435 5294711 := bstep (se 1 (by rfl) ⟨3971033, by rfl⟩ : syracuseStep 5294711 = 7942067) B7942067
theorem B3529807 : Blo 2173435 3529807 := bstep (se 1 (by rfl) ⟨2647355, by rfl⟩ : syracuseStep 3529807 = 5294711) B5294711
theorem B18825637 : Blo 2173435 18825637 := bstep (se 4 (by rfl) ⟨1764903, by rfl⟩ : syracuseStep 18825637 = 3529807) B3529807
theorem B25100849 : Blo 2173435 25100849 := bstep (se 2 (by rfl) ⟨9412818, by rfl⟩ : syracuseStep 25100849 = 18825637) B18825637
theorem B16733899 : Blo 2173435 16733899 := bstep (se 1 (by rfl) ⟨12550424, by rfl⟩ : syracuseStep 16733899 = 25100849) B25100849
theorem B22311865 : Blo 2173435 22311865 := bstep (se 2 (by rfl) ⟨8366949, by rfl⟩ : syracuseStep 22311865 = 16733899) B16733899
theorem B29749153 : Blo 2173435 29749153 := bstep (se 2 (by rfl) ⟨11155932, by rfl⟩ : syracuseStep 29749153 = 22311865) B22311865
theorem B39665537 : Blo 2173435 39665537 := bstep (se 2 (by rfl) ⟨14874576, by rfl⟩ : syracuseStep 39665537 = 29749153) B29749153
theorem B26443691 : Blo 2173435 26443691 := bstep (se 1 (by rfl) ⟨19832768, by rfl⟩ : syracuseStep 26443691 = 39665537) B39665537
theorem B17629127 : Blo 2173435 17629127 := bstep (se 1 (by rfl) ⟨13221845, by rfl⟩ : syracuseStep 17629127 = 26443691) B26443691
theorem B11752751 : Blo 2173435 11752751 := bstep (se 1 (by rfl) ⟨8814563, by rfl⟩ : syracuseStep 11752751 = 17629127) B17629127
theorem B7835167 : Blo 2173435 7835167 := bstep (se 1 (by rfl) ⟨5876375, by rfl⟩ : syracuseStep 7835167 = 11752751) B11752751
theorem B10446889 : Blo 2173435 10446889 := bstep (se 2 (by rfl) ⟨3917583, by rfl⟩ : syracuseStep 10446889 = 7835167) B7835167
theorem B13929185 : Blo 2173435 13929185 := bstep (se 2 (by rfl) ⟨5223444, by rfl⟩ : syracuseStep 13929185 = 10446889) B10446889
theorem B9286123 : Blo 2173435 9286123 := bstep (se 1 (by rfl) ⟨6964592, by rfl⟩ : syracuseStep 9286123 = 13929185) B13929185
theorem B12381497 : Blo 2173435 12381497 := bstep (se 2 (by rfl) ⟨4643061, by rfl⟩ : syracuseStep 12381497 = 9286123) B9286123
theorem B8254331 : Blo 2173435 8254331 := bstep (se 1 (by rfl) ⟨6190748, by rfl⟩ : syracuseStep 8254331 = 12381497) B12381497
theorem B5502887 : Blo 2173435 5502887 := bstep (se 1 (by rfl) ⟨4127165, by rfl⟩ : syracuseStep 5502887 = 8254331) B8254331
theorem B3668591 : Blo 2173435 3668591 := bstep (se 1 (by rfl) ⟨2751443, by rfl⟩ : syracuseStep 3668591 = 5502887) B5502887
theorem B2445727 : Blo 2173435 2445727 := bstep (se 1 (by rfl) ⟨1834295, by rfl⟩ : syracuseStep 2445727 = 3668591) B3668591
theorem B3260969 : Blo 2173435 3260969 := bstep (se 2 (by rfl) ⟨1222863, by rfl⟩ : syracuseStep 3260969 = 2445727) B2445727
theorem B2173979 : Blo 2173435 2173979 := bstep (se 1 (by rfl) ⟨1630484, by rfl⟩ : syracuseStep 2173979 = 3260969) B3260969
theorem B2647361 : Blo 2173435 2647361 := bbase (se 2 (by rfl) ⟨992760, by rfl⟩ : syracuseStep 2647361 = 1985521) (by norm_num)
theorem B7059629 : Blo 2173435 7059629 := bstep (se 3 (by rfl) ⟨1323680, by rfl⟩ : syracuseStep 7059629 = 2647361) B2647361
theorem B4706419 : Blo 2173435 4706419 := bstep (se 1 (by rfl) ⟨3529814, by rfl⟩ : syracuseStep 4706419 = 7059629) B7059629
theorem B6275225 : Blo 2173435 6275225 := bstep (se 2 (by rfl) ⟨2353209, by rfl⟩ : syracuseStep 6275225 = 4706419) B4706419
theorem B4183483 : Blo 2173435 4183483 := bstep (se 1 (by rfl) ⟨3137612, by rfl⟩ : syracuseStep 4183483 = 6275225) B6275225
theorem B5577977 : Blo 2173435 5577977 := bstep (se 2 (by rfl) ⟨2091741, by rfl⟩ : syracuseStep 5577977 = 4183483) B4183483
theorem B3718651 : Blo 2173435 3718651 := bstep (se 1 (by rfl) ⟨2788988, by rfl⟩ : syracuseStep 3718651 = 5577977) B5577977
theorem B4958201 : Blo 2173435 4958201 := bstep (se 2 (by rfl) ⟨1859325, by rfl⟩ : syracuseStep 4958201 = 3718651) B3718651
theorem B3305467 : Blo 2173435 3305467 := bstep (se 1 (by rfl) ⟨2479100, by rfl⟩ : syracuseStep 3305467 = 4958201) B4958201
theorem B17629157 : Blo 2173435 17629157 := bstep (se 4 (by rfl) ⟨1652733, by rfl⟩ : syracuseStep 17629157 = 3305467) B3305467
theorem B11752771 : Blo 2173435 11752771 := bstep (se 1 (by rfl) ⟨8814578, by rfl⟩ : syracuseStep 11752771 = 17629157) B17629157
theorem B15670361 : Blo 2173435 15670361 := bstep (se 2 (by rfl) ⟨5876385, by rfl⟩ : syracuseStep 15670361 = 11752771) B11752771
theorem B10446907 : Blo 2173435 10446907 := bstep (se 1 (by rfl) ⟨7835180, by rfl⟩ : syracuseStep 10446907 = 15670361) B15670361
theorem B13929209 : Blo 2173435 13929209 := bstep (se 2 (by rfl) ⟨5223453, by rfl⟩ : syracuseStep 13929209 = 10446907) B10446907
theorem B9286139 : Blo 2173435 9286139 := bstep (se 1 (by rfl) ⟨6964604, by rfl⟩ : syracuseStep 9286139 = 13929209) B13929209
theorem B6190759 : Blo 2173435 6190759 := bstep (se 1 (by rfl) ⟨4643069, by rfl⟩ : syracuseStep 6190759 = 9286139) B9286139
theorem B8254345 : Blo 2173435 8254345 := bstep (se 2 (by rfl) ⟨3095379, by rfl⟩ : syracuseStep 8254345 = 6190759) B6190759
theorem B11005793 : Blo 2173435 11005793 := bstep (se 2 (by rfl) ⟨4127172, by rfl⟩ : syracuseStep 11005793 = 8254345) B8254345
theorem B7337195 : Blo 2173435 7337195 := bstep (se 1 (by rfl) ⟨5502896, by rfl⟩ : syracuseStep 7337195 = 11005793) B11005793
theorem B4891463 : Blo 2173435 4891463 := bstep (se 1 (by rfl) ⟨3668597, by rfl⟩ : syracuseStep 4891463 = 7337195) B7337195
theorem B3260975 : Blo 2173435 3260975 := bstep (se 1 (by rfl) ⟨2445731, by rfl⟩ : syracuseStep 3260975 = 4891463) B4891463
theorem B2173983 : Blo 2173435 2173983 := bstep (se 1 (by rfl) ⟨1630487, by rfl⟩ : syracuseStep 2173983 = 3260975) B3260975
theorem B3260981 : Blo 2173435 3260981 := bbase (se 5 (by rfl) ⟨152858, by rfl⟩ : syracuseStep 3260981 = 305717) (by norm_num)
theorem B2173987 : Blo 2173435 2173987 := bstep (se 1 (by rfl) ⟨1630490, by rfl⟩ : syracuseStep 2173987 = 3260981) B3260981
theorem B5502917 : Blo 2173435 5502917 := bbase (se 4 (by rfl) ⟨515898, by rfl⟩ : syracuseStep 5502917 = 1031797) (by norm_num)
theorem B3668611 : Blo 2173435 3668611 := bstep (se 1 (by rfl) ⟨2751458, by rfl⟩ : syracuseStep 3668611 = 5502917) B5502917
theorem B4891481 : Blo 2173435 4891481 := bstep (se 2 (by rfl) ⟨1834305, by rfl⟩ : syracuseStep 4891481 = 3668611) B3668611
theorem B3260987 : Blo 2173435 3260987 := bstep (se 1 (by rfl) ⟨2445740, by rfl⟩ : syracuseStep 3260987 = 4891481) B4891481
theorem B2173991 : Blo 2173435 2173991 := bstep (se 1 (by rfl) ⟨1630493, by rfl⟩ : syracuseStep 2173991 = 3260987) B3260987
theorem B2445745 : Blo 2173435 2445745 := bbase (se 2 (by rfl) ⟨917154, by rfl⟩ : syracuseStep 2445745 = 1834309) (by norm_num)
theorem B3260993 : Blo 2173435 3260993 := bstep (se 2 (by rfl) ⟨1222872, by rfl⟩ : syracuseStep 3260993 = 2445745) B2445745
theorem B2173995 : Blo 2173435 2173995 := bstep (se 1 (by rfl) ⟨1630496, by rfl⟩ : syracuseStep 2173995 = 3260993) B3260993
theorem B6190805 : Blo 2173435 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B4127203 : Blo 2173435 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B5502937 : Blo 2173435 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B7337249 : Blo 2173435 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B4891499 : Blo 2173435 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B3260999 : Blo 2173435 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B2173999 : Blo 2173435 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B3261005 : Blo 2173435 3261005 := bbase (se 3 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 3261005 = 1222877) (by norm_num)
theorem B2174003 : Blo 2173435 2174003 := bstep (se 1 (by rfl) ⟨1630502, by rfl⟩ : syracuseStep 2174003 = 3261005) B3261005
theorem B4891517 : Blo 2173435 4891517 := bbase (se 3 (by rfl) ⟨917159, by rfl⟩ : syracuseStep 4891517 = 1834319) (by norm_num)
theorem B3261011 : Blo 2173435 3261011 := bstep (se 1 (by rfl) ⟨2445758, by rfl⟩ : syracuseStep 3261011 = 4891517) B4891517
theorem B2174007 : Blo 2173435 2174007 := bstep (se 1 (by rfl) ⟨1630505, by rfl⟩ : syracuseStep 2174007 = 3261011) B3261011
theorem B3668645 : Blo 2173435 3668645 := bbase (se 4 (by rfl) ⟨343935, by rfl⟩ : syracuseStep 3668645 = 687871) (by norm_num)
theorem B2445763 : Blo 2173435 2445763 := bstep (se 1 (by rfl) ⟨1834322, by rfl⟩ : syracuseStep 2445763 = 3668645) B3668645
theorem B3261017 : Blo 2173435 3261017 := bstep (se 2 (by rfl) ⟨1222881, by rfl⟩ : syracuseStep 3261017 = 2445763) B2445763
theorem B2174011 : Blo 2173435 2174011 := bstep (se 1 (by rfl) ⟨1630508, by rfl⟩ : syracuseStep 2174011 = 3261017) B3261017
theorem B2321569 : Blo 2173435 2321569 := bbase (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) (by norm_num)
theorem B3095425 : Blo 2173435 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B16508933 : Blo 2173435 16508933 := bstep (se 4 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 16508933 = 3095425) B3095425
theorem B11005955 : Blo 2173435 11005955 := bstep (se 1 (by rfl) ⟨8254466, by rfl⟩ : syracuseStep 11005955 = 16508933) B16508933
theorem B7337303 : Blo 2173435 7337303 := bstep (se 1 (by rfl) ⟨5502977, by rfl⟩ : syracuseStep 7337303 = 11005955) B11005955
theorem B4891535 : Blo 2173435 4891535 := bstep (se 1 (by rfl) ⟨3668651, by rfl⟩ : syracuseStep 4891535 = 7337303) B7337303
theorem B3261023 : Blo 2173435 3261023 := bstep (se 1 (by rfl) ⟨2445767, by rfl⟩ : syracuseStep 3261023 = 4891535) B4891535
theorem B2174015 : Blo 2173435 2174015 := bstep (se 1 (by rfl) ⟨1630511, by rfl⟩ : syracuseStep 2174015 = 3261023) B3261023
theorem B3261029 : Blo 2173435 3261029 := bbase (se 4 (by rfl) ⟨305721, by rfl⟩ : syracuseStep 3261029 = 611443) (by norm_num)
theorem B2174019 : Blo 2173435 2174019 := bstep (se 1 (by rfl) ⟨1630514, by rfl⟩ : syracuseStep 2174019 = 3261029) B3261029
theorem B3095437 : Blo 2173435 3095437 := bbase (se 3 (by rfl) ⟨580394, by rfl⟩ : syracuseStep 3095437 = 1160789) (by norm_num)
theorem B4127249 : Blo 2173435 4127249 := bstep (se 2 (by rfl) ⟨1547718, by rfl⟩ : syracuseStep 4127249 = 3095437) B3095437
theorem B2751499 : Blo 2173435 2751499 := bstep (se 1 (by rfl) ⟨2063624, by rfl⟩ : syracuseStep 2751499 = 4127249) B4127249
theorem B3668665 : Blo 2173435 3668665 := bstep (se 2 (by rfl) ⟨1375749, by rfl⟩ : syracuseStep 3668665 = 2751499) B2751499
theorem B4891553 : Blo 2173435 4891553 := bstep (se 2 (by rfl) ⟨1834332, by rfl⟩ : syracuseStep 4891553 = 3668665) B3668665
theorem B3261035 : Blo 2173435 3261035 := bstep (se 1 (by rfl) ⟨2445776, by rfl⟩ : syracuseStep 3261035 = 4891553) B4891553
theorem B2174023 : Blo 2173435 2174023 := bstep (se 1 (by rfl) ⟨1630517, by rfl⟩ : syracuseStep 2174023 = 3261035) B3261035
theorem B2445781 : Blo 2173435 2445781 := bbase (se 7 (by rfl) ⟨28661, by rfl⟩ : syracuseStep 2445781 = 57323) (by norm_num)
theorem B3261041 : Blo 2173435 3261041 := bstep (se 2 (by rfl) ⟨1222890, by rfl⟩ : syracuseStep 3261041 = 2445781) B2445781
theorem B2174027 : Blo 2173435 2174027 := bstep (se 1 (by rfl) ⟨1630520, by rfl⟩ : syracuseStep 2174027 = 3261041) B3261041
theorem B2751509 : Blo 2173435 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B7337357 : Blo 2173435 7337357 := bstep (se 3 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 7337357 = 2751509) B2751509
theorem B4891571 : Blo 2173435 4891571 := bstep (se 1 (by rfl) ⟨3668678, by rfl⟩ : syracuseStep 4891571 = 7337357) B7337357
theorem B3261047 : Blo 2173435 3261047 := bstep (se 1 (by rfl) ⟨2445785, by rfl⟩ : syracuseStep 3261047 = 4891571) B4891571
theorem B2174031 : Blo 2173435 2174031 := bstep (se 1 (by rfl) ⟨1630523, by rfl⟩ : syracuseStep 2174031 = 3261047) B3261047
theorem B3261053 : Blo 2173435 3261053 := bbase (se 3 (by rfl) ⟨611447, by rfl⟩ : syracuseStep 3261053 = 1222895) (by norm_num)
theorem B2174035 : Blo 2173435 2174035 := bstep (se 1 (by rfl) ⟨1630526, by rfl⟩ : syracuseStep 2174035 = 3261053) B3261053
theorem B4891589 : Blo 2173435 4891589 := bbase (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) (by norm_num)
theorem B3261059 : Blo 2173435 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B2174039 : Blo 2173435 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B7437509 : Blo 2173435 7437509 := bbase (se 4 (by rfl) ⟨697266, by rfl⟩ : syracuseStep 7437509 = 1394533) (by norm_num)
theorem B4958339 : Blo 2173435 4958339 := bstep (se 1 (by rfl) ⟨3718754, by rfl⟩ : syracuseStep 4958339 = 7437509) B7437509
theorem B13222237 : Blo 2173435 13222237 := bstep (se 3 (by rfl) ⟨2479169, by rfl⟩ : syracuseStep 13222237 = 4958339) B4958339
theorem B17629649 : Blo 2173435 17629649 := bstep (se 2 (by rfl) ⟨6611118, by rfl⟩ : syracuseStep 17629649 = 13222237) B13222237
theorem B11753099 : Blo 2173435 11753099 := bstep (se 1 (by rfl) ⟨8814824, by rfl⟩ : syracuseStep 11753099 = 17629649) B17629649
theorem B7835399 : Blo 2173435 7835399 := bstep (se 1 (by rfl) ⟨5876549, by rfl⟩ : syracuseStep 7835399 = 11753099) B11753099
theorem B5223599 : Blo 2173435 5223599 := bstep (se 1 (by rfl) ⟨3917699, by rfl⟩ : syracuseStep 5223599 = 7835399) B7835399
theorem B3482399 : Blo 2173435 3482399 := bstep (se 1 (by rfl) ⟨2611799, by rfl⟩ : syracuseStep 3482399 = 5223599) B5223599
theorem B9286397 : Blo 2173435 9286397 := bstep (se 3 (by rfl) ⟨1741199, by rfl⟩ : syracuseStep 9286397 = 3482399) B3482399
theorem B6190931 : Blo 2173435 6190931 := bstep (se 1 (by rfl) ⟨4643198, by rfl⟩ : syracuseStep 6190931 = 9286397) B9286397
theorem B4127287 : Blo 2173435 4127287 := bstep (se 1 (by rfl) ⟨3095465, by rfl⟩ : syracuseStep 4127287 = 6190931) B6190931
theorem B5503049 : Blo 2173435 5503049 := bstep (se 2 (by rfl) ⟨2063643, by rfl⟩ : syracuseStep 5503049 = 4127287) B4127287
theorem B3668699 : Blo 2173435 3668699 := bstep (se 1 (by rfl) ⟨2751524, by rfl⟩ : syracuseStep 3668699 = 5503049) B5503049
theorem B2445799 : Blo 2173435 2445799 := bstep (se 1 (by rfl) ⟨1834349, by rfl⟩ : syracuseStep 2445799 = 3668699) B3668699
theorem B3261065 : Blo 2173435 3261065 := bstep (se 2 (by rfl) ⟨1222899, by rfl⟩ : syracuseStep 3261065 = 2445799) B2445799
theorem B2174043 : Blo 2173435 2174043 := bstep (se 1 (by rfl) ⟨1630532, by rfl⟩ : syracuseStep 2174043 = 3261065) B3261065
theorem B11006117 : Blo 2173435 11006117 := bbase (se 4 (by rfl) ⟨1031823, by rfl⟩ : syracuseStep 11006117 = 2063647) (by norm_num)
theorem B7337411 : Blo 2173435 7337411 := bstep (se 1 (by rfl) ⟨5503058, by rfl⟩ : syracuseStep 7337411 = 11006117) B11006117
theorem B4891607 : Blo 2173435 4891607 := bstep (se 1 (by rfl) ⟨3668705, by rfl⟩ : syracuseStep 4891607 = 7337411) B7337411
theorem B3261071 : Blo 2173435 3261071 := bstep (se 1 (by rfl) ⟨2445803, by rfl⟩ : syracuseStep 3261071 = 4891607) B4891607
theorem B2174047 : Blo 2173435 2174047 := bstep (se 1 (by rfl) ⟨1630535, by rfl⟩ : syracuseStep 2174047 = 3261071) B3261071
theorem B3261077 : Blo 2173435 3261077 := bbase (se 6 (by rfl) ⟨76431, by rfl⟩ : syracuseStep 3261077 = 152863) (by norm_num)
theorem B2174051 : Blo 2173435 2174051 := bstep (se 1 (by rfl) ⟨1630538, by rfl⟩ : syracuseStep 2174051 = 3261077) B3261077
theorem B4958365 : Blo 2173435 4958365 := bbase (se 3 (by rfl) ⟨929693, by rfl⟩ : syracuseStep 4958365 = 1859387) (by norm_num)
theorem B6611153 : Blo 2173435 6611153 := bstep (se 2 (by rfl) ⟨2479182, by rfl⟩ : syracuseStep 6611153 = 4958365) B4958365
theorem B17629741 : Blo 2173435 17629741 := bstep (se 3 (by rfl) ⟨3305576, by rfl⟩ : syracuseStep 17629741 = 6611153) B6611153
theorem B23506321 : Blo 2173435 23506321 := bstep (se 2 (by rfl) ⟨8814870, by rfl⟩ : syracuseStep 23506321 = 17629741) B17629741
theorem B31341761 : Blo 2173435 31341761 := bstep (se 2 (by rfl) ⟨11753160, by rfl⟩ : syracuseStep 31341761 = 23506321) B23506321
theorem B20894507 : Blo 2173435 20894507 := bstep (se 1 (by rfl) ⟨15670880, by rfl⟩ : syracuseStep 20894507 = 31341761) B31341761
theorem B13929671 : Blo 2173435 13929671 := bstep (se 1 (by rfl) ⟨10447253, by rfl⟩ : syracuseStep 13929671 = 20894507) B20894507
theorem B9286447 : Blo 2173435 9286447 := bstep (se 1 (by rfl) ⟨6964835, by rfl⟩ : syracuseStep 9286447 = 13929671) B13929671
theorem B12381929 : Blo 2173435 12381929 := bstep (se 2 (by rfl) ⟨4643223, by rfl⟩ : syracuseStep 12381929 = 9286447) B9286447
theorem B8254619 : Blo 2173435 8254619 := bstep (se 1 (by rfl) ⟨6190964, by rfl⟩ : syracuseStep 8254619 = 12381929) B12381929
theorem B5503079 : Blo 2173435 5503079 := bstep (se 1 (by rfl) ⟨4127309, by rfl⟩ : syracuseStep 5503079 = 8254619) B8254619
theorem B3668719 : Blo 2173435 3668719 := bstep (se 1 (by rfl) ⟨2751539, by rfl⟩ : syracuseStep 3668719 = 5503079) B5503079
theorem B4891625 : Blo 2173435 4891625 := bstep (se 2 (by rfl) ⟨1834359, by rfl⟩ : syracuseStep 4891625 = 3668719) B3668719
theorem B3261083 : Blo 2173435 3261083 := bstep (se 1 (by rfl) ⟨2445812, by rfl⟩ : syracuseStep 3261083 = 4891625) B4891625
theorem B2174055 : Blo 2173435 2174055 := bstep (se 1 (by rfl) ⟨1630541, by rfl⟩ : syracuseStep 2174055 = 3261083) B3261083
theorem B2445817 : Blo 2173435 2445817 := bbase (se 2 (by rfl) ⟨917181, by rfl⟩ : syracuseStep 2445817 = 1834363) (by norm_num)
theorem B3261089 : Blo 2173435 3261089 := bstep (se 2 (by rfl) ⟨1222908, by rfl⟩ : syracuseStep 3261089 = 2445817) B2445817
theorem B2174059 : Blo 2173435 2174059 := bstep (se 1 (by rfl) ⟨1630544, by rfl⟩ : syracuseStep 2174059 = 3261089) B3261089
theorem B5294917 : Blo 2173435 5294917 := bbase (se 4 (by rfl) ⟨496398, by rfl⟩ : syracuseStep 5294917 = 992797) (by norm_num)
theorem B7059889 : Blo 2173435 7059889 := bstep (se 2 (by rfl) ⟨2647458, by rfl⟩ : syracuseStep 7059889 = 5294917) B5294917
theorem B9413185 : Blo 2173435 9413185 := bstep (se 2 (by rfl) ⟨3529944, by rfl⟩ : syracuseStep 9413185 = 7059889) B7059889
theorem B12550913 : Blo 2173435 12550913 := bstep (se 2 (by rfl) ⟨4706592, by rfl⟩ : syracuseStep 12550913 = 9413185) B9413185
theorem B8367275 : Blo 2173435 8367275 := bstep (se 1 (by rfl) ⟨6275456, by rfl⟩ : syracuseStep 8367275 = 12550913) B12550913
theorem B5578183 : Blo 2173435 5578183 := bstep (se 1 (by rfl) ⟨4183637, by rfl⟩ : syracuseStep 5578183 = 8367275) B8367275
theorem B7437577 : Blo 2173435 7437577 := bstep (se 2 (by rfl) ⟨2789091, by rfl⟩ : syracuseStep 7437577 = 5578183) B5578183
theorem B9916769 : Blo 2173435 9916769 := bstep (se 2 (by rfl) ⟨3718788, by rfl⟩ : syracuseStep 9916769 = 7437577) B7437577
theorem B6611179 : Blo 2173435 6611179 := bstep (se 1 (by rfl) ⟨4958384, by rfl⟩ : syracuseStep 6611179 = 9916769) B9916769
theorem B8814905 : Blo 2173435 8814905 := bstep (se 2 (by rfl) ⟨3305589, by rfl⟩ : syracuseStep 8814905 = 6611179) B6611179
theorem B5876603 : Blo 2173435 5876603 := bstep (se 1 (by rfl) ⟨4407452, by rfl⟩ : syracuseStep 5876603 = 8814905) B8814905
theorem B3917735 : Blo 2173435 3917735 := bstep (se 1 (by rfl) ⟨2938301, by rfl⟩ : syracuseStep 3917735 = 5876603) B5876603
theorem B2611823 : Blo 2173435 2611823 := bstep (se 1 (by rfl) ⟨1958867, by rfl⟩ : syracuseStep 2611823 = 3917735) B3917735
theorem B6964861 : Blo 2173435 6964861 := bstep (se 3 (by rfl) ⟨1305911, by rfl⟩ : syracuseStep 6964861 = 2611823) B2611823
theorem B9286481 : Blo 2173435 9286481 := bstep (se 2 (by rfl) ⟨3482430, by rfl⟩ : syracuseStep 9286481 = 6964861) B6964861
theorem B6190987 : Blo 2173435 6190987 := bstep (se 1 (by rfl) ⟨4643240, by rfl⟩ : syracuseStep 6190987 = 9286481) B9286481
theorem B8254649 : Blo 2173435 8254649 := bstep (se 2 (by rfl) ⟨3095493, by rfl⟩ : syracuseStep 8254649 = 6190987) B6190987
theorem B5503099 : Blo 2173435 5503099 := bstep (se 1 (by rfl) ⟨4127324, by rfl⟩ : syracuseStep 5503099 = 8254649) B8254649
theorem B7337465 : Blo 2173435 7337465 := bstep (se 2 (by rfl) ⟨2751549, by rfl⟩ : syracuseStep 7337465 = 5503099) B5503099
theorem B4891643 : Blo 2173435 4891643 := bstep (se 1 (by rfl) ⟨3668732, by rfl⟩ : syracuseStep 4891643 = 7337465) B7337465
theorem B3261095 : Blo 2173435 3261095 := bstep (se 1 (by rfl) ⟨2445821, by rfl⟩ : syracuseStep 3261095 = 4891643) B4891643
theorem B2174063 : Blo 2173435 2174063 := bstep (se 1 (by rfl) ⟨1630547, by rfl⟩ : syracuseStep 2174063 = 3261095) B3261095
theorem B3261101 : Blo 2173435 3261101 := bbase (se 3 (by rfl) ⟨611456, by rfl⟩ : syracuseStep 3261101 = 1222913) (by norm_num)
theorem B2174067 : Blo 2173435 2174067 := bstep (se 1 (by rfl) ⟨1630550, by rfl⟩ : syracuseStep 2174067 = 3261101) B3261101
theorem B4891661 : Blo 2173435 4891661 := bbase (se 3 (by rfl) ⟨917186, by rfl⟩ : syracuseStep 4891661 = 1834373) (by norm_num)
theorem B3261107 : Blo 2173435 3261107 := bstep (se 1 (by rfl) ⟨2445830, by rfl⟩ : syracuseStep 3261107 = 4891661) B4891661
theorem B2174071 : Blo 2173435 2174071 := bstep (se 1 (by rfl) ⟨1630553, by rfl⟩ : syracuseStep 2174071 = 3261107) B3261107
theorem B2751565 : Blo 2173435 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B3668753 : Blo 2173435 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B2445835 : Blo 2173435 2445835 := bstep (se 1 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 2445835 = 3668753) B3668753
theorem B3261113 : Blo 2173435 3261113 := bstep (se 2 (by rfl) ⟨1222917, by rfl⟩ : syracuseStep 3261113 = 2445835) B2445835
theorem B2174075 : Blo 2173435 2174075 := bstep (se 1 (by rfl) ⟨1630556, by rfl⟩ : syracuseStep 2174075 = 3261113) B3261113
theorem B2353313 : Blo 2173435 2353313 := bbase (se 2 (by rfl) ⟨882492, by rfl⟩ : syracuseStep 2353313 = 1764985) (by norm_num)
theorem B6275501 : Blo 2173435 6275501 := bstep (se 3 (by rfl) ⟨1176656, by rfl⟩ : syracuseStep 6275501 = 2353313) B2353313
theorem B4183667 : Blo 2173435 4183667 := bstep (se 1 (by rfl) ⟨3137750, by rfl⟩ : syracuseStep 4183667 = 6275501) B6275501
theorem B2789111 : Blo 2173435 2789111 := bstep (se 1 (by rfl) ⟨2091833, by rfl⟩ : syracuseStep 2789111 = 4183667) B4183667
theorem B7437629 : Blo 2173435 7437629 := bstep (se 3 (by rfl) ⟨1394555, by rfl⟩ : syracuseStep 7437629 = 2789111) B2789111
theorem B4958419 : Blo 2173435 4958419 := bstep (se 1 (by rfl) ⟨3718814, by rfl⟩ : syracuseStep 4958419 = 7437629) B7437629
theorem B6611225 : Blo 2173435 6611225 := bstep (se 2 (by rfl) ⟨2479209, by rfl⟩ : syracuseStep 6611225 = 4958419) B4958419
theorem B70519733 : Blo 2173435 70519733 := bstep (se 5 (by rfl) ⟨3305612, by rfl⟩ : syracuseStep 70519733 = 6611225) B6611225
theorem B47013155 : Blo 2173435 47013155 := bstep (se 1 (by rfl) ⟨35259866, by rfl⟩ : syracuseStep 47013155 = 70519733) B70519733
theorem B31342103 : Blo 2173435 31342103 := bstep (se 1 (by rfl) ⟨23506577, by rfl⟩ : syracuseStep 31342103 = 47013155) B47013155
theorem B20894735 : Blo 2173435 20894735 := bstep (se 1 (by rfl) ⟨15671051, by rfl⟩ : syracuseStep 20894735 = 31342103) B31342103
theorem B13929823 : Blo 2173435 13929823 := bstep (se 1 (by rfl) ⟨10447367, by rfl⟩ : syracuseStep 13929823 = 20894735) B20894735
theorem B18573097 : Blo 2173435 18573097 := bstep (se 2 (by rfl) ⟨6964911, by rfl⟩ : syracuseStep 18573097 = 13929823) B13929823
theorem B24764129 : Blo 2173435 24764129 := bstep (se 2 (by rfl) ⟨9286548, by rfl⟩ : syracuseStep 24764129 = 18573097) B18573097
theorem B16509419 : Blo 2173435 16509419 := bstep (se 1 (by rfl) ⟨12382064, by rfl⟩ : syracuseStep 16509419 = 24764129) B24764129
theorem B11006279 : Blo 2173435 11006279 := bstep (se 1 (by rfl) ⟨8254709, by rfl⟩ : syracuseStep 11006279 = 16509419) B16509419
theorem B7337519 : Blo 2173435 7337519 := bstep (se 1 (by rfl) ⟨5503139, by rfl⟩ : syracuseStep 7337519 = 11006279) B11006279
theorem B4891679 : Blo 2173435 4891679 := bstep (se 1 (by rfl) ⟨3668759, by rfl⟩ : syracuseStep 4891679 = 7337519) B7337519
theorem B3261119 : Blo 2173435 3261119 := bstep (se 1 (by rfl) ⟨2445839, by rfl⟩ : syracuseStep 3261119 = 4891679) B4891679
theorem B2174079 : Blo 2173435 2174079 := bstep (se 1 (by rfl) ⟨1630559, by rfl⟩ : syracuseStep 2174079 = 3261119) B3261119
theorem B3261125 : Blo 2173435 3261125 := bbase (se 4 (by rfl) ⟨305730, by rfl⟩ : syracuseStep 3261125 = 611461) (by norm_num)
theorem B2174083 : Blo 2173435 2174083 := bstep (se 1 (by rfl) ⟨1630562, by rfl⟩ : syracuseStep 2174083 = 3261125) B3261125
theorem B3668773 : Blo 2173435 3668773 := bbase (se 4 (by rfl) ⟨343947, by rfl⟩ : syracuseStep 3668773 = 687895) (by norm_num)
theorem B4891697 : Blo 2173435 4891697 := bstep (se 2 (by rfl) ⟨1834386, by rfl⟩ : syracuseStep 4891697 = 3668773) B3668773
theorem B3261131 : Blo 2173435 3261131 := bstep (se 1 (by rfl) ⟨2445848, by rfl⟩ : syracuseStep 3261131 = 4891697) B4891697
theorem B2174087 : Blo 2173435 2174087 := bstep (se 1 (by rfl) ⟨1630565, by rfl⟩ : syracuseStep 2174087 = 3261131) B3261131
theorem B2445853 : Blo 2173435 2445853 := bbase (se 3 (by rfl) ⟨458597, by rfl⟩ : syracuseStep 2445853 = 917195) (by norm_num)
theorem B3261137 : Blo 2173435 3261137 := bstep (se 2 (by rfl) ⟨1222926, by rfl⟩ : syracuseStep 3261137 = 2445853) B2445853
theorem B2174091 : Blo 2173435 2174091 := bstep (se 1 (by rfl) ⟨1630568, by rfl⟩ : syracuseStep 2174091 = 3261137) B3261137
theorem B7337573 : Blo 2173435 7337573 := bbase (se 4 (by rfl) ⟨687897, by rfl⟩ : syracuseStep 7337573 = 1375795) (by norm_num)
theorem B4891715 : Blo 2173435 4891715 := bstep (se 1 (by rfl) ⟨3668786, by rfl⟩ : syracuseStep 4891715 = 7337573) B7337573
theorem B3261143 : Blo 2173435 3261143 := bstep (se 1 (by rfl) ⟨2445857, by rfl⟩ : syracuseStep 3261143 = 4891715) B4891715
theorem B2174095 : Blo 2173435 2174095 := bstep (se 1 (by rfl) ⟨1630571, by rfl⟩ : syracuseStep 2174095 = 3261143) B3261143
theorem B3261149 : Blo 2173435 3261149 := bbase (se 3 (by rfl) ⟨611465, by rfl⟩ : syracuseStep 3261149 = 1222931) (by norm_num)
theorem B2174099 : Blo 2173435 2174099 := bstep (se 1 (by rfl) ⟨1630574, by rfl⟩ : syracuseStep 2174099 = 3261149) B3261149
theorem B4891733 : Blo 2173435 4891733 := bbase (se 8 (by rfl) ⟨28662, by rfl⟩ : syracuseStep 4891733 = 57325) (by norm_num)
theorem B3261155 : Blo 2173435 3261155 := bstep (se 1 (by rfl) ⟨2445866, by rfl⟩ : syracuseStep 3261155 = 4891733) B4891733
theorem B2174103 : Blo 2173435 2174103 := bstep (se 1 (by rfl) ⟨1630577, by rfl⟩ : syracuseStep 2174103 = 3261155) B3261155
theorem B2789149 : Blo 2173435 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B3718865 : Blo 2173435 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B2479243 : Blo 2173435 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B3305657 : Blo 2173435 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2203771 : Blo 2173435 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B2938361 : Blo 2173435 2938361 := bstep (se 2 (by rfl) ⟨1101885, by rfl⟩ : syracuseStep 2938361 = 2203771) B2203771
theorem B7835629 : Blo 2173435 7835629 := bstep (se 3 (by rfl) ⟨1469180, by rfl⟩ : syracuseStep 7835629 = 2938361) B2938361
theorem B10447505 : Blo 2173435 10447505 := bstep (se 2 (by rfl) ⟨3917814, by rfl⟩ : syracuseStep 10447505 = 7835629) B7835629
theorem B6965003 : Blo 2173435 6965003 := bstep (se 1 (by rfl) ⟨5223752, by rfl⟩ : syracuseStep 6965003 = 10447505) B10447505
theorem B4643335 : Blo 2173435 4643335 := bstep (se 1 (by rfl) ⟨3482501, by rfl⟩ : syracuseStep 4643335 = 6965003) B6965003
theorem B6191113 : Blo 2173435 6191113 := bstep (se 2 (by rfl) ⟨2321667, by rfl⟩ : syracuseStep 6191113 = 4643335) B4643335
theorem B8254817 : Blo 2173435 8254817 := bstep (se 2 (by rfl) ⟨3095556, by rfl⟩ : syracuseStep 8254817 = 6191113) B6191113
theorem B5503211 : Blo 2173435 5503211 := bstep (se 1 (by rfl) ⟨4127408, by rfl⟩ : syracuseStep 5503211 = 8254817) B8254817
theorem B3668807 : Blo 2173435 3668807 := bstep (se 1 (by rfl) ⟨2751605, by rfl⟩ : syracuseStep 3668807 = 5503211) B5503211
theorem B2445871 : Blo 2173435 2445871 := bstep (se 1 (by rfl) ⟨1834403, by rfl⟩ : syracuseStep 2445871 = 3668807) B3668807
theorem B3261161 : Blo 2173435 3261161 := bstep (se 2 (by rfl) ⟨1222935, by rfl⟩ : syracuseStep 3261161 = 2445871) B2445871
theorem B2174107 : Blo 2173435 2174107 := bstep (se 1 (by rfl) ⟨1630580, by rfl⟩ : syracuseStep 2174107 = 3261161) B3261161
theorem B7942549 : Blo 2173435 7942549 := bbase (se 6 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 7942549 = 372307) (by norm_num)
theorem B10590065 : Blo 2173435 10590065 := bstep (se 2 (by rfl) ⟨3971274, by rfl⟩ : syracuseStep 10590065 = 7942549) B7942549
theorem B7060043 : Blo 2173435 7060043 := bstep (se 1 (by rfl) ⟨5295032, by rfl⟩ : syracuseStep 7060043 = 10590065) B10590065
theorem B4706695 : Blo 2173435 4706695 := bstep (se 1 (by rfl) ⟨3530021, by rfl⟩ : syracuseStep 4706695 = 7060043) B7060043
theorem B6275593 : Blo 2173435 6275593 := bstep (se 2 (by rfl) ⟨2353347, by rfl⟩ : syracuseStep 6275593 = 4706695) B4706695
theorem B8367457 : Blo 2173435 8367457 := bstep (se 2 (by rfl) ⟨3137796, by rfl⟩ : syracuseStep 8367457 = 6275593) B6275593
theorem B11156609 : Blo 2173435 11156609 := bstep (se 2 (by rfl) ⟨4183728, by rfl⟩ : syracuseStep 11156609 = 8367457) B8367457
theorem B7437739 : Blo 2173435 7437739 := bstep (se 1 (by rfl) ⟨5578304, by rfl⟩ : syracuseStep 7437739 = 11156609) B11156609
theorem B9916985 : Blo 2173435 9916985 := bstep (se 2 (by rfl) ⟨3718869, by rfl⟩ : syracuseStep 9916985 = 7437739) B7437739
theorem B6611323 : Blo 2173435 6611323 := bstep (se 1 (by rfl) ⟨4958492, by rfl⟩ : syracuseStep 6611323 = 9916985) B9916985
theorem B8815097 : Blo 2173435 8815097 := bstep (se 2 (by rfl) ⟨3305661, by rfl⟩ : syracuseStep 8815097 = 6611323) B6611323
theorem B5876731 : Blo 2173435 5876731 := bstep (se 1 (by rfl) ⟨4407548, by rfl⟩ : syracuseStep 5876731 = 8815097) B8815097
theorem B31342565 : Blo 2173435 31342565 := bstep (se 4 (by rfl) ⟨2938365, by rfl⟩ : syracuseStep 31342565 = 5876731) B5876731
theorem B20895043 : Blo 2173435 20895043 := bstep (se 1 (by rfl) ⟨15671282, by rfl⟩ : syracuseStep 20895043 = 31342565) B31342565
theorem B27860057 : Blo 2173435 27860057 := bstep (se 2 (by rfl) ⟨10447521, by rfl⟩ : syracuseStep 27860057 = 20895043) B20895043
theorem B18573371 : Blo 2173435 18573371 := bstep (se 1 (by rfl) ⟨13930028, by rfl⟩ : syracuseStep 18573371 = 27860057) B27860057
theorem B12382247 : Blo 2173435 12382247 := bstep (se 1 (by rfl) ⟨9286685, by rfl⟩ : syracuseStep 12382247 = 18573371) B18573371
theorem B8254831 : Blo 2173435 8254831 := bstep (se 1 (by rfl) ⟨6191123, by rfl⟩ : syracuseStep 8254831 = 12382247) B12382247
theorem B11006441 : Blo 2173435 11006441 := bstep (se 2 (by rfl) ⟨4127415, by rfl⟩ : syracuseStep 11006441 = 8254831) B8254831
theorem B7337627 : Blo 2173435 7337627 := bstep (se 1 (by rfl) ⟨5503220, by rfl⟩ : syracuseStep 7337627 = 11006441) B11006441
theorem B4891751 : Blo 2173435 4891751 := bstep (se 1 (by rfl) ⟨3668813, by rfl⟩ : syracuseStep 4891751 = 7337627) B7337627
theorem B3261167 : Blo 2173435 3261167 := bstep (se 1 (by rfl) ⟨2445875, by rfl⟩ : syracuseStep 3261167 = 4891751) B4891751
theorem B2174111 : Blo 2173435 2174111 := bstep (se 1 (by rfl) ⟨1630583, by rfl⟩ : syracuseStep 2174111 = 3261167) B3261167
theorem B3261173 : Blo 2173435 3261173 := bbase (se 5 (by rfl) ⟨152867, by rfl⟩ : syracuseStep 3261173 = 305735) (by norm_num)
theorem B2174115 : Blo 2173435 2174115 := bstep (se 1 (by rfl) ⟨1630586, by rfl⟩ : syracuseStep 2174115 = 3261173) B3261173
theorem B5223781 : Blo 2173435 5223781 := bbase (se 4 (by rfl) ⟨489729, by rfl⟩ : syracuseStep 5223781 = 979459) (by norm_num)
theorem B6965041 : Blo 2173435 6965041 := bstep (se 2 (by rfl) ⟨2611890, by rfl⟩ : syracuseStep 6965041 = 5223781) B5223781
theorem B9286721 : Blo 2173435 9286721 := bstep (se 2 (by rfl) ⟨3482520, by rfl⟩ : syracuseStep 9286721 = 6965041) B6965041
theorem B6191147 : Blo 2173435 6191147 := bstep (se 1 (by rfl) ⟨4643360, by rfl⟩ : syracuseStep 6191147 = 9286721) B9286721
theorem B4127431 : Blo 2173435 4127431 := bstep (se 1 (by rfl) ⟨3095573, by rfl⟩ : syracuseStep 4127431 = 6191147) B6191147
theorem B5503241 : Blo 2173435 5503241 := bstep (se 2 (by rfl) ⟨2063715, by rfl⟩ : syracuseStep 5503241 = 4127431) B4127431
theorem B3668827 : Blo 2173435 3668827 := bstep (se 1 (by rfl) ⟨2751620, by rfl⟩ : syracuseStep 3668827 = 5503241) B5503241
theorem B4891769 : Blo 2173435 4891769 := bstep (se 2 (by rfl) ⟨1834413, by rfl⟩ : syracuseStep 4891769 = 3668827) B3668827
theorem B3261179 : Blo 2173435 3261179 := bstep (se 1 (by rfl) ⟨2445884, by rfl⟩ : syracuseStep 3261179 = 4891769) B4891769
theorem B2174119 : Blo 2173435 2174119 := bstep (se 1 (by rfl) ⟨1630589, by rfl⟩ : syracuseStep 2174119 = 3261179) B3261179
theorem B2445889 : Blo 2173435 2445889 := bbase (se 2 (by rfl) ⟨917208, by rfl⟩ : syracuseStep 2445889 = 1834417) (by norm_num)
theorem B3261185 : Blo 2173435 3261185 := bstep (se 2 (by rfl) ⟨1222944, by rfl⟩ : syracuseStep 3261185 = 2445889) B2445889
theorem B2174123 : Blo 2173435 2174123 := bstep (se 1 (by rfl) ⟨1630592, by rfl⟩ : syracuseStep 2174123 = 3261185) B3261185
theorem B5503261 : Blo 2173435 5503261 := bbase (se 3 (by rfl) ⟨1031861, by rfl⟩ : syracuseStep 5503261 = 2063723) (by norm_num)
theorem B7337681 : Blo 2173435 7337681 := bstep (se 2 (by rfl) ⟨2751630, by rfl⟩ : syracuseStep 7337681 = 5503261) B5503261
theorem B4891787 : Blo 2173435 4891787 := bstep (se 1 (by rfl) ⟨3668840, by rfl⟩ : syracuseStep 4891787 = 7337681) B7337681
theorem B3261191 : Blo 2173435 3261191 := bstep (se 1 (by rfl) ⟨2445893, by rfl⟩ : syracuseStep 3261191 = 4891787) B4891787
theorem B2174127 : Blo 2173435 2174127 := bstep (se 1 (by rfl) ⟨1630595, by rfl⟩ : syracuseStep 2174127 = 3261191) B3261191
theorem B3261197 : Blo 2173435 3261197 := bbase (se 3 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 3261197 = 1222949) (by norm_num)
theorem B2174131 : Blo 2173435 2174131 := bstep (se 1 (by rfl) ⟨1630598, by rfl⟩ : syracuseStep 2174131 = 3261197) B3261197
theorem B4891805 : Blo 2173435 4891805 := bbase (se 3 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 4891805 = 1834427) (by norm_num)
theorem B3261203 : Blo 2173435 3261203 := bstep (se 1 (by rfl) ⟨2445902, by rfl⟩ : syracuseStep 3261203 = 4891805) B4891805
theorem B2174135 : Blo 2173435 2174135 := bstep (se 1 (by rfl) ⟨1630601, by rfl⟩ : syracuseStep 2174135 = 3261203) B3261203
theorem B3668861 : Blo 2173435 3668861 := bbase (se 3 (by rfl) ⟨687911, by rfl⟩ : syracuseStep 3668861 = 1375823) (by norm_num)
theorem B2445907 : Blo 2173435 2445907 := bstep (se 1 (by rfl) ⟨1834430, by rfl⟩ : syracuseStep 2445907 = 3668861) B3668861
theorem B3261209 : Blo 2173435 3261209 := bstep (se 2 (by rfl) ⟨1222953, by rfl⟩ : syracuseStep 3261209 = 2445907) B2445907
theorem B2174139 : Blo 2173435 2174139 := bstep (se 1 (by rfl) ⟨1630604, by rfl⟩ : syracuseStep 2174139 = 3261209) B3261209
theorem B3350813 : Blo 2173435 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B35742005 : Blo 2173435 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B23828003 : Blo 2173435 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B15885335 : Blo 2173435 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B42360893 : Blo 2173435 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B28240595 : Blo 2173435 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B18827063 : Blo 2173435 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B12551375 : Blo 2173435 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B8367583 : Blo 2173435 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B11156777 : Blo 2173435 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B7437851 : Blo 2173435 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B4958567 : Blo 2173435 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B3305711 : Blo 2173435 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B8815229 : Blo 2173435 8815229 := bstep (se 3 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 8815229 = 3305711) B3305711
theorem B5876819 : Blo 2173435 5876819 := bstep (se 1 (by rfl) ⟨4407614, by rfl⟩ : syracuseStep 5876819 = 8815229) B8815229
theorem B3917879 : Blo 2173435 3917879 := bstep (se 1 (by rfl) ⟨2938409, by rfl⟩ : syracuseStep 3917879 = 5876819) B5876819
theorem B2611919 : Blo 2173435 2611919 := bstep (se 1 (by rfl) ⟨1958939, by rfl⟩ : syracuseStep 2611919 = 3917879) B3917879
theorem B6965117 : Blo 2173435 6965117 := bstep (se 3 (by rfl) ⟨1305959, by rfl⟩ : syracuseStep 6965117 = 2611919) B2611919
theorem B4643411 : Blo 2173435 4643411 := bstep (se 1 (by rfl) ⟨3482558, by rfl⟩ : syracuseStep 4643411 = 6965117) B6965117
theorem B12382429 : Blo 2173435 12382429 := bstep (se 3 (by rfl) ⟨2321705, by rfl⟩ : syracuseStep 12382429 = 4643411) B4643411
theorem B16509905 : Blo 2173435 16509905 := bstep (se 2 (by rfl) ⟨6191214, by rfl⟩ : syracuseStep 16509905 = 12382429) B12382429
theorem B11006603 : Blo 2173435 11006603 := bstep (se 1 (by rfl) ⟨8254952, by rfl⟩ : syracuseStep 11006603 = 16509905) B16509905
theorem B7337735 : Blo 2173435 7337735 := bstep (se 1 (by rfl) ⟨5503301, by rfl⟩ : syracuseStep 7337735 = 11006603) B11006603
theorem B4891823 : Blo 2173435 4891823 := bstep (se 1 (by rfl) ⟨3668867, by rfl⟩ : syracuseStep 4891823 = 7337735) B7337735
theorem B3261215 : Blo 2173435 3261215 := bstep (se 1 (by rfl) ⟨2445911, by rfl⟩ : syracuseStep 3261215 = 4891823) B4891823
theorem B2174143 : Blo 2173435 2174143 := bstep (se 1 (by rfl) ⟨1630607, by rfl⟩ : syracuseStep 2174143 = 3261215) B3261215
theorem B3261221 : Blo 2173435 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B2174147 : Blo 2173435 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B2751661 : Blo 2173435 2751661 := bbase (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) (by norm_num)
theorem B3668881 : Blo 2173435 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B4891841 : Blo 2173435 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B3261227 : Blo 2173435 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B2174151 : Blo 2173435 2174151 := bstep (se 1 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 2174151 = 3261227) B3261227
theorem B2445925 : Blo 2173435 2445925 := bbase (se 4 (by rfl) ⟨229305, by rfl⟩ : syracuseStep 2445925 = 458611) (by norm_num)
theorem B3261233 : Blo 2173435 3261233 := bstep (se 2 (by rfl) ⟨1222962, by rfl⟩ : syracuseStep 3261233 = 2445925) B2445925
theorem B2174155 : Blo 2173435 2174155 := bstep (se 1 (by rfl) ⟨1630616, by rfl⟩ : syracuseStep 2174155 = 3261233) B3261233
theorem B3917909 : Blo 2173435 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B2611939 : Blo 2173435 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B3482585 : Blo 2173435 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B2321723 : Blo 2173435 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B6191261 : Blo 2173435 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B4127507 : Blo 2173435 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B2751671 : Blo 2173435 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B7337789 : Blo 2173435 7337789 := bstep (se 3 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 7337789 = 2751671) B2751671
theorem B4891859 : Blo 2173435 4891859 := bstep (se 1 (by rfl) ⟨3668894, by rfl⟩ : syracuseStep 4891859 = 7337789) B7337789
theorem B3261239 : Blo 2173435 3261239 := bstep (se 1 (by rfl) ⟨2445929, by rfl⟩ : syracuseStep 3261239 = 4891859) B4891859
theorem B2174159 : Blo 2173435 2174159 := bstep (se 1 (by rfl) ⟨1630619, by rfl⟩ : syracuseStep 2174159 = 3261239) B3261239
theorem B3261245 : Blo 2173435 3261245 := bbase (se 3 (by rfl) ⟨611483, by rfl⟩ : syracuseStep 3261245 = 1222967) (by norm_num)
theorem B2174163 : Blo 2173435 2174163 := bstep (se 1 (by rfl) ⟨1630622, by rfl⟩ : syracuseStep 2174163 = 3261245) B3261245
theorem B4891877 : Blo 2173435 4891877 := bbase (se 4 (by rfl) ⟨458613, by rfl⟩ : syracuseStep 4891877 = 917227) (by norm_num)
theorem B3261251 : Blo 2173435 3261251 := bstep (se 1 (by rfl) ⟨2445938, by rfl⟩ : syracuseStep 3261251 = 4891877) B4891877
theorem B2174167 : Blo 2173435 2174167 := bstep (se 1 (by rfl) ⟨1630625, by rfl⟩ : syracuseStep 2174167 = 3261251) B3261251
theorem B5503373 : Blo 2173435 5503373 := bbase (se 3 (by rfl) ⟨1031882, by rfl⟩ : syracuseStep 5503373 = 2063765) (by norm_num)
theorem B3668915 : Blo 2173435 3668915 := bstep (se 1 (by rfl) ⟨2751686, by rfl⟩ : syracuseStep 3668915 = 5503373) B5503373
theorem B2445943 : Blo 2173435 2445943 := bstep (se 1 (by rfl) ⟨1834457, by rfl⟩ : syracuseStep 2445943 = 3668915) B3668915
theorem B3261257 : Blo 2173435 3261257 := bstep (se 2 (by rfl) ⟨1222971, by rfl⟩ : syracuseStep 3261257 = 2445943) B2445943
theorem B2174171 : Blo 2173435 2174171 := bstep (se 1 (by rfl) ⟨1630628, by rfl⟩ : syracuseStep 2174171 = 3261257) B3261257
theorem B3095653 : Blo 2173435 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B4127537 : Blo 2173435 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B11006765 : Blo 2173435 11006765 := bstep (se 3 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 11006765 = 4127537) B4127537
theorem B7337843 : Blo 2173435 7337843 := bstep (se 1 (by rfl) ⟨5503382, by rfl⟩ : syracuseStep 7337843 = 11006765) B11006765
theorem B4891895 : Blo 2173435 4891895 := bstep (se 1 (by rfl) ⟨3668921, by rfl⟩ : syracuseStep 4891895 = 7337843) B7337843
theorem B3261263 : Blo 2173435 3261263 := bstep (se 1 (by rfl) ⟨2445947, by rfl⟩ : syracuseStep 3261263 = 4891895) B4891895
theorem B2174175 : Blo 2173435 2174175 := bstep (se 1 (by rfl) ⟨1630631, by rfl⟩ : syracuseStep 2174175 = 3261263) B3261263
theorem B3261269 : Blo 2173435 3261269 := bbase (se 9 (by rfl) ⟨9554, by rfl⟩ : syracuseStep 3261269 = 19109) (by norm_num)
theorem B2174179 : Blo 2173435 2174179 := bstep (se 1 (by rfl) ⟨1630634, by rfl⟩ : syracuseStep 2174179 = 3261269) B3261269
theorem B7060277 : Blo 2173435 7060277 := bbase (se 5 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 7060277 = 661901) (by norm_num)
theorem B18827405 : Blo 2173435 18827405 := bstep (se 3 (by rfl) ⟨3530138, by rfl⟩ : syracuseStep 18827405 = 7060277) B7060277
theorem B12551603 : Blo 2173435 12551603 := bstep (se 1 (by rfl) ⟨9413702, by rfl⟩ : syracuseStep 12551603 = 18827405) B18827405
theorem B133883765 : Blo 2173435 133883765 := bstep (se 5 (by rfl) ⟨6275801, by rfl⟩ : syracuseStep 133883765 = 12551603) B12551603
theorem B89255843 : Blo 2173435 89255843 := bstep (se 1 (by rfl) ⟨66941882, by rfl⟩ : syracuseStep 89255843 = 133883765) B133883765
theorem B59503895 : Blo 2173435 59503895 := bstep (se 1 (by rfl) ⟨44627921, by rfl⟩ : syracuseStep 59503895 = 89255843) B89255843
theorem B39669263 : Blo 2173435 39669263 := bstep (se 1 (by rfl) ⟨29751947, by rfl⟩ : syracuseStep 39669263 = 59503895) B59503895
theorem B26446175 : Blo 2173435 26446175 := bstep (se 1 (by rfl) ⟨19834631, by rfl⟩ : syracuseStep 26446175 = 39669263) B39669263
theorem B17630783 : Blo 2173435 17630783 := bstep (se 1 (by rfl) ⟨13223087, by rfl⟩ : syracuseStep 17630783 = 26446175) B26446175
theorem B11753855 : Blo 2173435 11753855 := bstep (se 1 (by rfl) ⟨8815391, by rfl⟩ : syracuseStep 11753855 = 17630783) B17630783
theorem B7835903 : Blo 2173435 7835903 := bstep (se 1 (by rfl) ⟨5876927, by rfl⟩ : syracuseStep 7835903 = 11753855) B11753855
theorem B5223935 : Blo 2173435 5223935 := bstep (se 1 (by rfl) ⟨3917951, by rfl⟩ : syracuseStep 5223935 = 7835903) B7835903
theorem B3482623 : Blo 2173435 3482623 := bstep (se 1 (by rfl) ⟨2611967, by rfl⟩ : syracuseStep 3482623 = 5223935) B5223935
theorem B4643497 : Blo 2173435 4643497 := bstep (se 2 (by rfl) ⟨1741311, by rfl⟩ : syracuseStep 4643497 = 3482623) B3482623
theorem B6191329 : Blo 2173435 6191329 := bstep (se 2 (by rfl) ⟨2321748, by rfl⟩ : syracuseStep 6191329 = 4643497) B4643497
theorem B8255105 : Blo 2173435 8255105 := bstep (se 2 (by rfl) ⟨3095664, by rfl⟩ : syracuseStep 8255105 = 6191329) B6191329
theorem B5503403 : Blo 2173435 5503403 := bstep (se 1 (by rfl) ⟨4127552, by rfl⟩ : syracuseStep 5503403 = 8255105) B8255105
theorem B3668935 : Blo 2173435 3668935 := bstep (se 1 (by rfl) ⟨2751701, by rfl⟩ : syracuseStep 3668935 = 5503403) B5503403
theorem B4891913 : Blo 2173435 4891913 := bstep (se 2 (by rfl) ⟨1834467, by rfl⟩ : syracuseStep 4891913 = 3668935) B3668935
theorem B3261275 : Blo 2173435 3261275 := bstep (se 1 (by rfl) ⟨2445956, by rfl⟩ : syracuseStep 3261275 = 4891913) B4891913
theorem B2174183 : Blo 2173435 2174183 := bstep (se 1 (by rfl) ⟨1630637, by rfl⟩ : syracuseStep 2174183 = 3261275) B3261275
theorem B2445961 : Blo 2173435 2445961 := bbase (se 2 (by rfl) ⟨917235, by rfl⟩ : syracuseStep 2445961 = 1834471) (by norm_num)
theorem B3261281 : Blo 2173435 3261281 := bstep (se 2 (by rfl) ⟨1222980, by rfl⟩ : syracuseStep 3261281 = 2445961) B2445961
theorem B2174187 : Blo 2173435 2174187 := bstep (se 1 (by rfl) ⟨1630640, by rfl⟩ : syracuseStep 2174187 = 3261281) B3261281
theorem B7539493 : Blo 2173435 7539493 := bbase (se 4 (by rfl) ⟨706827, by rfl⟩ : syracuseStep 7539493 = 1413655) (by norm_num)
theorem B10052657 : Blo 2173435 10052657 := bstep (se 2 (by rfl) ⟨3769746, by rfl⟩ : syracuseStep 10052657 = 7539493) B7539493
theorem B6701771 : Blo 2173435 6701771 := bstep (se 1 (by rfl) ⟨5026328, by rfl⟩ : syracuseStep 6701771 = 10052657) B10052657
theorem B4467847 : Blo 2173435 4467847 := bstep (se 1 (by rfl) ⟨3350885, by rfl⟩ : syracuseStep 4467847 = 6701771) B6701771
theorem B5957129 : Blo 2173435 5957129 := bstep (se 2 (by rfl) ⟨2233923, by rfl⟩ : syracuseStep 5957129 = 4467847) B4467847
theorem B3971419 : Blo 2173435 3971419 := bstep (se 1 (by rfl) ⟨2978564, by rfl⟩ : syracuseStep 3971419 = 5957129) B5957129
theorem B21180901 : Blo 2173435 21180901 := bstep (se 4 (by rfl) ⟨1985709, by rfl⟩ : syracuseStep 21180901 = 3971419) B3971419
theorem B28241201 : Blo 2173435 28241201 := bstep (se 2 (by rfl) ⟨10590450, by rfl⟩ : syracuseStep 28241201 = 21180901) B21180901
theorem B75309869 : Blo 2173435 75309869 := bstep (se 3 (by rfl) ⟨14120600, by rfl⟩ : syracuseStep 75309869 = 28241201) B28241201
theorem B200826317 : Blo 2173435 200826317 := bstep (se 3 (by rfl) ⟨37654934, by rfl⟩ : syracuseStep 200826317 = 75309869) B75309869
theorem B133884211 : Blo 2173435 133884211 := bstep (se 1 (by rfl) ⟨100413158, by rfl⟩ : syracuseStep 133884211 = 200826317) B200826317
theorem B178512281 : Blo 2173435 178512281 := bstep (se 2 (by rfl) ⟨66942105, by rfl⟩ : syracuseStep 178512281 = 133884211) B133884211
theorem B119008187 : Blo 2173435 119008187 := bstep (se 1 (by rfl) ⟨89256140, by rfl⟩ : syracuseStep 119008187 = 178512281) B178512281
theorem B79338791 : Blo 2173435 79338791 := bstep (se 1 (by rfl) ⟨59504093, by rfl⟩ : syracuseStep 79338791 = 119008187) B119008187
theorem B52892527 : Blo 2173435 52892527 := bstep (se 1 (by rfl) ⟨39669395, by rfl⟩ : syracuseStep 52892527 = 79338791) B79338791
theorem B70523369 : Blo 2173435 70523369 := bstep (se 2 (by rfl) ⟨26446263, by rfl⟩ : syracuseStep 70523369 = 52892527) B52892527
theorem B47015579 : Blo 2173435 47015579 := bstep (se 1 (by rfl) ⟨35261684, by rfl⟩ : syracuseStep 47015579 = 70523369) B70523369
theorem B31343719 : Blo 2173435 31343719 := bstep (se 1 (by rfl) ⟨23507789, by rfl⟩ : syracuseStep 31343719 = 47015579) B47015579
theorem B41791625 : Blo 2173435 41791625 := bstep (se 2 (by rfl) ⟨15671859, by rfl⟩ : syracuseStep 41791625 = 31343719) B31343719
theorem B27861083 : Blo 2173435 27861083 := bstep (se 1 (by rfl) ⟨20895812, by rfl⟩ : syracuseStep 27861083 = 41791625) B41791625
theorem B18574055 : Blo 2173435 18574055 := bstep (se 1 (by rfl) ⟨13930541, by rfl⟩ : syracuseStep 18574055 = 27861083) B27861083
theorem B12382703 : Blo 2173435 12382703 := bstep (se 1 (by rfl) ⟨9287027, by rfl⟩ : syracuseStep 12382703 = 18574055) B18574055
theorem B8255135 : Blo 2173435 8255135 := bstep (se 1 (by rfl) ⟨6191351, by rfl⟩ : syracuseStep 8255135 = 12382703) B12382703
theorem B5503423 : Blo 2173435 5503423 := bstep (se 1 (by rfl) ⟨4127567, by rfl⟩ : syracuseStep 5503423 = 8255135) B8255135
theorem B7337897 : Blo 2173435 7337897 := bstep (se 2 (by rfl) ⟨2751711, by rfl⟩ : syracuseStep 7337897 = 5503423) B5503423
theorem B4891931 : Blo 2173435 4891931 := bstep (se 1 (by rfl) ⟨3668948, by rfl⟩ : syracuseStep 4891931 = 7337897) B7337897
theorem B3261287 : Blo 2173435 3261287 := bstep (se 1 (by rfl) ⟨2445965, by rfl⟩ : syracuseStep 3261287 = 4891931) B4891931
theorem B2174191 : Blo 2173435 2174191 := bstep (se 1 (by rfl) ⟨1630643, by rfl⟩ : syracuseStep 2174191 = 3261287) B3261287
theorem B3261293 : Blo 2173435 3261293 := bbase (se 3 (by rfl) ⟨611492, by rfl⟩ : syracuseStep 3261293 = 1222985) (by norm_num)
theorem B2174195 : Blo 2173435 2174195 := bstep (se 1 (by rfl) ⟨1630646, by rfl⟩ : syracuseStep 2174195 = 3261293) B3261293
theorem B4891949 : Blo 2173435 4891949 := bbase (se 3 (by rfl) ⟨917240, by rfl⟩ : syracuseStep 4891949 = 1834481) (by norm_num)
theorem B3261299 : Blo 2173435 3261299 := bstep (se 1 (by rfl) ⟨2445974, by rfl⟩ : syracuseStep 3261299 = 4891949) B4891949
theorem B2174199 : Blo 2173435 2174199 := bstep (se 1 (by rfl) ⟨1630649, by rfl⟩ : syracuseStep 2174199 = 3261299) B3261299
theorem B31771541 : Blo 2173435 31771541 := bbase (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) (by norm_num)
theorem B21181027 : Blo 2173435 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B28241369 : Blo 2173435 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B18827579 : Blo 2173435 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B50206877 : Blo 2173435 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B33471251 : Blo 2173435 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B22314167 : Blo 2173435 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B14876111 : Blo 2173435 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B9917407 : Blo 2173435 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B52892837 : Blo 2173435 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B35261891 : Blo 2173435 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B23507927 : Blo 2173435 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B15671951 : Blo 2173435 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B10447967 : Blo 2173435 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B6965311 : Blo 2173435 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B9287081 : Blo 2173435 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B6191387 : Blo 2173435 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B4127591 : Blo 2173435 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B2751727 : Blo 2173435 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B3668969 : Blo 2173435 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B2445979 : Blo 2173435 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B3261305 : Blo 2173435 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B2174203 : Blo 2173435 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B38168981 : Blo 2173435 38168981 := bbase (se 6 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 38168981 = 1789171) (by norm_num)
theorem B25445987 : Blo 2173435 25445987 := bstep (se 1 (by rfl) ⟨19084490, by rfl⟩ : syracuseStep 25445987 = 38168981) B38168981
theorem B16963991 : Blo 2173435 16963991 := bstep (se 1 (by rfl) ⟨12722993, by rfl⟩ : syracuseStep 16963991 = 25445987) B25445987
theorem B11309327 : Blo 2173435 11309327 := bstep (se 1 (by rfl) ⟨8481995, by rfl⟩ : syracuseStep 11309327 = 16963991) B16963991
theorem B7539551 : Blo 2173435 7539551 := bstep (se 1 (by rfl) ⟨5654663, by rfl⟩ : syracuseStep 7539551 = 11309327) B11309327
theorem B5026367 : Blo 2173435 5026367 := bstep (se 1 (by rfl) ⟨3769775, by rfl⟩ : syracuseStep 5026367 = 7539551) B7539551
theorem B3350911 : Blo 2173435 3350911 := bstep (se 1 (by rfl) ⟨2513183, by rfl⟩ : syracuseStep 3350911 = 5026367) B5026367
theorem B4467881 : Blo 2173435 4467881 := bstep (se 2 (by rfl) ⟨1675455, by rfl⟩ : syracuseStep 4467881 = 3350911) B3350911
theorem B2978587 : Blo 2173435 2978587 := bstep (se 1 (by rfl) ⟨2233940, by rfl⟩ : syracuseStep 2978587 = 4467881) B4467881
theorem B3971449 : Blo 2173435 3971449 := bstep (se 2 (by rfl) ⟨1489293, by rfl⟩ : syracuseStep 3971449 = 2978587) B2978587
theorem B21181061 : Blo 2173435 21181061 := bstep (se 4 (by rfl) ⟨1985724, by rfl⟩ : syracuseStep 21181061 = 3971449) B3971449
theorem B56482829 : Blo 2173435 56482829 := bstep (se 3 (by rfl) ⟨10590530, by rfl⟩ : syracuseStep 56482829 = 21181061) B21181061
theorem B37655219 : Blo 2173435 37655219 := bstep (se 1 (by rfl) ⟨28241414, by rfl⟩ : syracuseStep 37655219 = 56482829) B56482829
theorem B25103479 : Blo 2173435 25103479 := bstep (se 1 (by rfl) ⟨18827609, by rfl⟩ : syracuseStep 25103479 = 37655219) B37655219
theorem B33471305 : Blo 2173435 33471305 := bstep (se 2 (by rfl) ⟨12551739, by rfl⟩ : syracuseStep 33471305 = 25103479) B25103479
theorem B22314203 : Blo 2173435 22314203 := bstep (se 1 (by rfl) ⟨16735652, by rfl⟩ : syracuseStep 22314203 = 33471305) B33471305
theorem B14876135 : Blo 2173435 14876135 := bstep (se 1 (by rfl) ⟨11157101, by rfl⟩ : syracuseStep 14876135 = 22314203) B22314203
theorem B9917423 : Blo 2173435 9917423 := bstep (se 1 (by rfl) ⟨7438067, by rfl⟩ : syracuseStep 9917423 = 14876135) B14876135
theorem B6611615 : Blo 2173435 6611615 := bstep (se 1 (by rfl) ⟨4958711, by rfl⟩ : syracuseStep 6611615 = 9917423) B9917423
theorem B4407743 : Blo 2173435 4407743 := bstep (se 1 (by rfl) ⟨3305807, by rfl⟩ : syracuseStep 4407743 = 6611615) B6611615
theorem B11753981 : Blo 2173435 11753981 := bstep (se 3 (by rfl) ⟨2203871, by rfl⟩ : syracuseStep 11753981 = 4407743) B4407743
theorem B7835987 : Blo 2173435 7835987 := bstep (se 1 (by rfl) ⟨5876990, by rfl⟩ : syracuseStep 7835987 = 11753981) B11753981
theorem B20895965 : Blo 2173435 20895965 := bstep (se 3 (by rfl) ⟨3917993, by rfl⟩ : syracuseStep 20895965 = 7835987) B7835987
theorem B13930643 : Blo 2173435 13930643 := bstep (se 1 (by rfl) ⟨10447982, by rfl⟩ : syracuseStep 13930643 = 20895965) B20895965
theorem B37148381 : Blo 2173435 37148381 := bstep (se 3 (by rfl) ⟨6965321, by rfl⟩ : syracuseStep 37148381 = 13930643) B13930643
theorem B24765587 : Blo 2173435 24765587 := bstep (se 1 (by rfl) ⟨18574190, by rfl⟩ : syracuseStep 24765587 = 37148381) B37148381
theorem B16510391 : Blo 2173435 16510391 := bstep (se 1 (by rfl) ⟨12382793, by rfl⟩ : syracuseStep 16510391 = 24765587) B24765587
theorem B11006927 : Blo 2173435 11006927 := bstep (se 1 (by rfl) ⟨8255195, by rfl⟩ : syracuseStep 11006927 = 16510391) B16510391
theorem B7337951 : Blo 2173435 7337951 := bstep (se 1 (by rfl) ⟨5503463, by rfl⟩ : syracuseStep 7337951 = 11006927) B11006927
theorem B4891967 : Blo 2173435 4891967 := bstep (se 1 (by rfl) ⟨3668975, by rfl⟩ : syracuseStep 4891967 = 7337951) B7337951
theorem B3261311 : Blo 2173435 3261311 := bstep (se 1 (by rfl) ⟨2445983, by rfl⟩ : syracuseStep 3261311 = 4891967) B4891967
theorem B2174207 : Blo 2173435 2174207 := bstep (se 1 (by rfl) ⟨1630655, by rfl⟩ : syracuseStep 2174207 = 3261311) B3261311
theorem B3261317 : Blo 2173435 3261317 := bbase (se 4 (by rfl) ⟨305748, by rfl⟩ : syracuseStep 3261317 = 611497) (by norm_num)
theorem B2174211 : Blo 2173435 2174211 := bstep (se 1 (by rfl) ⟨1630658, by rfl⟩ : syracuseStep 2174211 = 3261317) B3261317
theorem B3668989 : Blo 2173435 3668989 := bbase (se 3 (by rfl) ⟨687935, by rfl⟩ : syracuseStep 3668989 = 1375871) (by norm_num)
theorem B4891985 : Blo 2173435 4891985 := bstep (se 2 (by rfl) ⟨1834494, by rfl⟩ : syracuseStep 4891985 = 3668989) B3668989
theorem B3261323 : Blo 2173435 3261323 := bstep (se 1 (by rfl) ⟨2445992, by rfl⟩ : syracuseStep 3261323 = 4891985) B4891985
theorem B2174215 : Blo 2173435 2174215 := bstep (se 1 (by rfl) ⟨1630661, by rfl⟩ : syracuseStep 2174215 = 3261323) B3261323
theorem B2445997 : Blo 2173435 2445997 := bbase (se 3 (by rfl) ⟨458624, by rfl⟩ : syracuseStep 2445997 = 917249) (by norm_num)
theorem B3261329 : Blo 2173435 3261329 := bstep (se 2 (by rfl) ⟨1222998, by rfl⟩ : syracuseStep 3261329 = 2445997) B2445997
theorem B2174219 : Blo 2173435 2174219 := bstep (se 1 (by rfl) ⟨1630664, by rfl⟩ : syracuseStep 2174219 = 3261329) B3261329
theorem B7338005 : Blo 2173435 7338005 := bbase (se 6 (by rfl) ⟨171984, by rfl⟩ : syracuseStep 7338005 = 343969) (by norm_num)
theorem B4892003 : Blo 2173435 4892003 := bstep (se 1 (by rfl) ⟨3669002, by rfl⟩ : syracuseStep 4892003 = 7338005) B7338005
theorem B3261335 : Blo 2173435 3261335 := bstep (se 1 (by rfl) ⟨2446001, by rfl⟩ : syracuseStep 3261335 = 4892003) B4892003
theorem B2174223 : Blo 2173435 2174223 := bstep (se 1 (by rfl) ⟨1630667, by rfl⟩ : syracuseStep 2174223 = 3261335) B3261335
theorem B3261341 : Blo 2173435 3261341 := bbase (se 3 (by rfl) ⟨611501, by rfl⟩ : syracuseStep 3261341 = 1223003) (by norm_num)
theorem B2174227 : Blo 2173435 2174227 := bstep (se 1 (by rfl) ⟨1630670, by rfl⟩ : syracuseStep 2174227 = 3261341) B3261341
theorem B4892021 : Blo 2173435 4892021 := bbase (se 5 (by rfl) ⟨229313, by rfl⟩ : syracuseStep 4892021 = 458627) (by norm_num)
theorem B3261347 : Blo 2173435 3261347 := bstep (se 1 (by rfl) ⟨2446010, by rfl⟩ : syracuseStep 3261347 = 4892021) B4892021
theorem B2174231 : Blo 2173435 2174231 := bstep (se 1 (by rfl) ⟨1630673, by rfl⟩ : syracuseStep 2174231 = 3261347) B3261347
theorem B6611701 : Blo 2173435 6611701 := bbase (se 5 (by rfl) ⟨309923, by rfl⟩ : syracuseStep 6611701 = 619847) (by norm_num)
theorem B8815601 : Blo 2173435 8815601 := bstep (se 2 (by rfl) ⟨3305850, by rfl⟩ : syracuseStep 8815601 = 6611701) B6611701
theorem B23508269 : Blo 2173435 23508269 := bstep (se 3 (by rfl) ⟨4407800, by rfl⟩ : syracuseStep 23508269 = 8815601) B8815601
theorem B15672179 : Blo 2173435 15672179 := bstep (se 1 (by rfl) ⟨11754134, by rfl⟩ : syracuseStep 15672179 = 23508269) B23508269
theorem B10448119 : Blo 2173435 10448119 := bstep (se 1 (by rfl) ⟨7836089, by rfl⟩ : syracuseStep 10448119 = 15672179) B15672179
theorem B13930825 : Blo 2173435 13930825 := bstep (se 2 (by rfl) ⟨5224059, by rfl⟩ : syracuseStep 13930825 = 10448119) B10448119
theorem B18574433 : Blo 2173435 18574433 := bstep (se 2 (by rfl) ⟨6965412, by rfl⟩ : syracuseStep 18574433 = 13930825) B13930825
theorem B12382955 : Blo 2173435 12382955 := bstep (se 1 (by rfl) ⟨9287216, by rfl⟩ : syracuseStep 12382955 = 18574433) B18574433
theorem B8255303 : Blo 2173435 8255303 := bstep (se 1 (by rfl) ⟨6191477, by rfl⟩ : syracuseStep 8255303 = 12382955) B12382955
theorem B5503535 : Blo 2173435 5503535 := bstep (se 1 (by rfl) ⟨4127651, by rfl⟩ : syracuseStep 5503535 = 8255303) B8255303
theorem B3669023 : Blo 2173435 3669023 := bstep (se 1 (by rfl) ⟨2751767, by rfl⟩ : syracuseStep 3669023 = 5503535) B5503535
theorem B2446015 : Blo 2173435 2446015 := bstep (se 1 (by rfl) ⟨1834511, by rfl⟩ : syracuseStep 2446015 = 3669023) B3669023
theorem B3261353 : Blo 2173435 3261353 := bstep (se 2 (by rfl) ⟨1223007, by rfl⟩ : syracuseStep 3261353 = 2446015) B2446015
theorem B2174235 : Blo 2173435 2174235 := bstep (se 1 (by rfl) ⟨1630676, by rfl⟩ : syracuseStep 2174235 = 3261353) B3261353
theorem B8255317 : Blo 2173435 8255317 := bbase (se 9 (by rfl) ⟨24185, by rfl⟩ : syracuseStep 8255317 = 48371) (by norm_num)
theorem B11007089 : Blo 2173435 11007089 := bstep (se 2 (by rfl) ⟨4127658, by rfl⟩ : syracuseStep 11007089 = 8255317) B8255317
theorem B7338059 : Blo 2173435 7338059 := bstep (se 1 (by rfl) ⟨5503544, by rfl⟩ : syracuseStep 7338059 = 11007089) B11007089
theorem B4892039 : Blo 2173435 4892039 := bstep (se 1 (by rfl) ⟨3669029, by rfl⟩ : syracuseStep 4892039 = 7338059) B7338059
theorem B3261359 : Blo 2173435 3261359 := bstep (se 1 (by rfl) ⟨2446019, by rfl⟩ : syracuseStep 3261359 = 4892039) B4892039
theorem B2174239 : Blo 2173435 2174239 := bstep (se 1 (by rfl) ⟨1630679, by rfl⟩ : syracuseStep 2174239 = 3261359) B3261359
theorem B3261365 : Blo 2173435 3261365 := bbase (se 5 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 3261365 = 305753) (by norm_num)
theorem B2174243 : Blo 2173435 2174243 := bstep (se 1 (by rfl) ⟨1630682, by rfl⟩ : syracuseStep 2174243 = 3261365) B3261365
theorem B5503565 : Blo 2173435 5503565 := bbase (se 3 (by rfl) ⟨1031918, by rfl⟩ : syracuseStep 5503565 = 2063837) (by norm_num)
theorem B3669043 : Blo 2173435 3669043 := bstep (se 1 (by rfl) ⟨2751782, by rfl⟩ : syracuseStep 3669043 = 5503565) B5503565
theorem B4892057 : Blo 2173435 4892057 := bstep (se 2 (by rfl) ⟨1834521, by rfl⟩ : syracuseStep 4892057 = 3669043) B3669043
theorem B3261371 : Blo 2173435 3261371 := bstep (se 1 (by rfl) ⟨2446028, by rfl⟩ : syracuseStep 3261371 = 4892057) B4892057
theorem B2174247 : Blo 2173435 2174247 := bstep (se 1 (by rfl) ⟨1630685, by rfl⟩ : syracuseStep 2174247 = 3261371) B3261371
theorem B2446033 : Blo 2173435 2446033 := bbase (se 2 (by rfl) ⟨917262, by rfl⟩ : syracuseStep 2446033 = 1834525) (by norm_num)
theorem B3261377 : Blo 2173435 3261377 := bstep (se 2 (by rfl) ⟨1223016, by rfl⟩ : syracuseStep 3261377 = 2446033) B2446033
theorem B2174251 : Blo 2173435 2174251 := bstep (se 1 (by rfl) ⟨1630688, by rfl⟩ : syracuseStep 2174251 = 3261377) B3261377
theorem B6965477 : Blo 2173435 6965477 := bbase (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) (by norm_num)
theorem B4643651 : Blo 2173435 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B3095767 : Blo 2173435 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B4127689 : Blo 2173435 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B5503585 : Blo 2173435 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B7338113 : Blo 2173435 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B4892075 : Blo 2173435 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B3261383 : Blo 2173435 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B2174255 : Blo 2173435 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B3261389 : Blo 2173435 3261389 := bbase (se 3 (by rfl) ⟨611510, by rfl⟩ : syracuseStep 3261389 = 1223021) (by norm_num)
theorem B2174259 : Blo 2173435 2174259 := bstep (se 1 (by rfl) ⟨1630694, by rfl⟩ : syracuseStep 2174259 = 3261389) B3261389
theorem B4892093 : Blo 2173435 4892093 := bbase (se 3 (by rfl) ⟨917267, by rfl⟩ : syracuseStep 4892093 = 1834535) (by norm_num)
theorem B3261395 : Blo 2173435 3261395 := bstep (se 1 (by rfl) ⟨2446046, by rfl⟩ : syracuseStep 3261395 = 4892093) B4892093
theorem B2174263 : Blo 2173435 2174263 := bstep (se 1 (by rfl) ⟨1630697, by rfl⟩ : syracuseStep 2174263 = 3261395) B3261395
theorem B3669077 : Blo 2173435 3669077 := bbase (se 8 (by rfl) ⟨21498, by rfl⟩ : syracuseStep 3669077 = 42997) (by norm_num)
theorem B2446051 : Blo 2173435 2446051 := bstep (se 1 (by rfl) ⟨1834538, by rfl⟩ : syracuseStep 2446051 = 3669077) B3669077
theorem B3261401 : Blo 2173435 3261401 := bstep (se 2 (by rfl) ⟨1223025, by rfl⟩ : syracuseStep 3261401 = 2446051) B2446051
theorem B2174267 : Blo 2173435 2174267 := bstep (se 1 (by rfl) ⟨1630700, by rfl⟩ : syracuseStep 2174267 = 3261401) B3261401
theorem B15672437 : Blo 2173435 15672437 := bbase (se 5 (by rfl) ⟨734645, by rfl⟩ : syracuseStep 15672437 = 1469291) (by norm_num)
theorem B10448291 : Blo 2173435 10448291 := bstep (se 1 (by rfl) ⟨7836218, by rfl⟩ : syracuseStep 10448291 = 15672437) B15672437
theorem B6965527 : Blo 2173435 6965527 := bstep (se 1 (by rfl) ⟨5224145, by rfl⟩ : syracuseStep 6965527 = 10448291) B10448291
theorem B9287369 : Blo 2173435 9287369 := bstep (se 2 (by rfl) ⟨3482763, by rfl⟩ : syracuseStep 9287369 = 6965527) B6965527
theorem B6191579 : Blo 2173435 6191579 := bstep (se 1 (by rfl) ⟨4643684, by rfl⟩ : syracuseStep 6191579 = 9287369) B9287369
theorem B16510877 : Blo 2173435 16510877 := bstep (se 3 (by rfl) ⟨3095789, by rfl⟩ : syracuseStep 16510877 = 6191579) B6191579
theorem B11007251 : Blo 2173435 11007251 := bstep (se 1 (by rfl) ⟨8255438, by rfl⟩ : syracuseStep 11007251 = 16510877) B16510877
theorem B7338167 : Blo 2173435 7338167 := bstep (se 1 (by rfl) ⟨5503625, by rfl⟩ : syracuseStep 7338167 = 11007251) B11007251
theorem B4892111 : Blo 2173435 4892111 := bstep (se 1 (by rfl) ⟨3669083, by rfl⟩ : syracuseStep 4892111 = 7338167) B7338167
theorem B3261407 : Blo 2173435 3261407 := bstep (se 1 (by rfl) ⟨2446055, by rfl⟩ : syracuseStep 3261407 = 4892111) B4892111
theorem B2174271 : Blo 2173435 2174271 := bstep (se 1 (by rfl) ⟨1630703, by rfl⟩ : syracuseStep 2174271 = 3261407) B3261407
theorem B3261413 : Blo 2173435 3261413 := bbase (se 4 (by rfl) ⟨305757, by rfl⟩ : syracuseStep 3261413 = 611515) (by norm_num)
theorem B2174275 : Blo 2173435 2174275 := bstep (se 1 (by rfl) ⟨1630706, by rfl⟩ : syracuseStep 2174275 = 3261413) B3261413
theorem B3918125 : Blo 2173435 3918125 := bbase (se 3 (by rfl) ⟨734648, by rfl⟩ : syracuseStep 3918125 = 1469297) (by norm_num)
theorem B2612083 : Blo 2173435 2612083 := bstep (se 1 (by rfl) ⟨1959062, by rfl⟩ : syracuseStep 2612083 = 3918125) B3918125
theorem B3482777 : Blo 2173435 3482777 := bstep (se 2 (by rfl) ⟨1306041, by rfl⟩ : syracuseStep 3482777 = 2612083) B2612083
theorem B9287405 : Blo 2173435 9287405 := bstep (se 3 (by rfl) ⟨1741388, by rfl⟩ : syracuseStep 9287405 = 3482777) B3482777
theorem B6191603 : Blo 2173435 6191603 := bstep (se 1 (by rfl) ⟨4643702, by rfl⟩ : syracuseStep 6191603 = 9287405) B9287405
theorem B4127735 : Blo 2173435 4127735 := bstep (se 1 (by rfl) ⟨3095801, by rfl⟩ : syracuseStep 4127735 = 6191603) B6191603
theorem B2751823 : Blo 2173435 2751823 := bstep (se 1 (by rfl) ⟨2063867, by rfl⟩ : syracuseStep 2751823 = 4127735) B4127735
theorem B3669097 : Blo 2173435 3669097 := bstep (se 2 (by rfl) ⟨1375911, by rfl⟩ : syracuseStep 3669097 = 2751823) B2751823
theorem B4892129 : Blo 2173435 4892129 := bstep (se 2 (by rfl) ⟨1834548, by rfl⟩ : syracuseStep 4892129 = 3669097) B3669097
theorem B3261419 : Blo 2173435 3261419 := bstep (se 1 (by rfl) ⟨2446064, by rfl⟩ : syracuseStep 3261419 = 4892129) B4892129
theorem B2174279 : Blo 2173435 2174279 := bstep (se 1 (by rfl) ⟨1630709, by rfl⟩ : syracuseStep 2174279 = 3261419) B3261419
theorem B2446069 : Blo 2173435 2446069 := bbase (se 5 (by rfl) ⟨114659, by rfl⟩ : syracuseStep 2446069 = 229319) (by norm_num)
theorem B3261425 : Blo 2173435 3261425 := bstep (se 2 (by rfl) ⟨1223034, by rfl⟩ : syracuseStep 3261425 = 2446069) B2446069
theorem B2174283 : Blo 2173435 2174283 := bstep (se 1 (by rfl) ⟨1630712, by rfl⟩ : syracuseStep 2174283 = 3261425) B3261425
theorem B2751833 : Blo 2173435 2751833 := bbase (se 2 (by rfl) ⟨1031937, by rfl⟩ : syracuseStep 2751833 = 2063875) (by norm_num)
theorem B7338221 : Blo 2173435 7338221 := bstep (se 3 (by rfl) ⟨1375916, by rfl⟩ : syracuseStep 7338221 = 2751833) B2751833
theorem B4892147 : Blo 2173435 4892147 := bstep (se 1 (by rfl) ⟨3669110, by rfl⟩ : syracuseStep 4892147 = 7338221) B7338221
theorem B3261431 : Blo 2173435 3261431 := bstep (se 1 (by rfl) ⟨2446073, by rfl⟩ : syracuseStep 3261431 = 4892147) B4892147
theorem B2174287 : Blo 2173435 2174287 := bstep (se 1 (by rfl) ⟨1630715, by rfl⟩ : syracuseStep 2174287 = 3261431) B3261431
theorem B3261437 : Blo 2173435 3261437 := bbase (se 3 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 3261437 = 1223039) (by norm_num)
theorem B2174291 : Blo 2173435 2174291 := bstep (se 1 (by rfl) ⟨1630718, by rfl⟩ : syracuseStep 2174291 = 3261437) B3261437
theorem B4892165 : Blo 2173435 4892165 := bbase (se 4 (by rfl) ⟨458640, by rfl⟩ : syracuseStep 4892165 = 917281) (by norm_num)
theorem B3261443 : Blo 2173435 3261443 := bstep (se 1 (by rfl) ⟨2446082, by rfl⟩ : syracuseStep 3261443 = 4892165) B4892165
theorem B2174295 : Blo 2173435 2174295 := bstep (se 1 (by rfl) ⟨1630721, by rfl⟩ : syracuseStep 2174295 = 3261443) B3261443
theorem B4127773 : Blo 2173435 4127773 := bbase (se 3 (by rfl) ⟨773957, by rfl⟩ : syracuseStep 4127773 = 1547915) (by norm_num)
theorem B5503697 : Blo 2173435 5503697 := bstep (se 2 (by rfl) ⟨2063886, by rfl⟩ : syracuseStep 5503697 = 4127773) B4127773
theorem B3669131 : Blo 2173435 3669131 := bstep (se 1 (by rfl) ⟨2751848, by rfl⟩ : syracuseStep 3669131 = 5503697) B5503697
theorem B2446087 : Blo 2173435 2446087 := bstep (se 1 (by rfl) ⟨1834565, by rfl⟩ : syracuseStep 2446087 = 3669131) B3669131
theorem B3261449 : Blo 2173435 3261449 := bstep (se 2 (by rfl) ⟨1223043, by rfl⟩ : syracuseStep 3261449 = 2446087) B2446087
theorem B2174299 : Blo 2173435 2174299 := bstep (se 1 (by rfl) ⟨1630724, by rfl⟩ : syracuseStep 2174299 = 3261449) B3261449
theorem B11007413 : Blo 2173435 11007413 := bbase (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) (by norm_num)
theorem B7338275 : Blo 2173435 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B4892183 : Blo 2173435 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B3261455 : Blo 2173435 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B2174303 : Blo 2173435 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B3261461 : Blo 2173435 3261461 := bbase (se 6 (by rfl) ⟨76440, by rfl⟩ : syracuseStep 3261461 = 152881) (by norm_num)
theorem B2174307 : Blo 2173435 2174307 := bstep (se 1 (by rfl) ⟨1630730, by rfl⟩ : syracuseStep 2174307 = 3261461) B3261461
theorem B3138085 : Blo 2173435 3138085 := bbase (se 4 (by rfl) ⟨294195, by rfl⟩ : syracuseStep 3138085 = 588391) (by norm_num)
theorem B16736453 : Blo 2173435 16736453 := bstep (se 4 (by rfl) ⟨1569042, by rfl⟩ : syracuseStep 16736453 = 3138085) B3138085
theorem B11157635 : Blo 2173435 11157635 := bstep (se 1 (by rfl) ⟨8368226, by rfl⟩ : syracuseStep 11157635 = 16736453) B16736453
theorem B7438423 : Blo 2173435 7438423 := bstep (se 1 (by rfl) ⟨5578817, by rfl⟩ : syracuseStep 7438423 = 11157635) B11157635
theorem B9917897 : Blo 2173435 9917897 := bstep (se 2 (by rfl) ⟨3719211, by rfl⟩ : syracuseStep 9917897 = 7438423) B7438423
theorem B26447725 : Blo 2173435 26447725 := bstep (se 3 (by rfl) ⟨4958948, by rfl⟩ : syracuseStep 26447725 = 9917897) B9917897
theorem B35263633 : Blo 2173435 35263633 := bstep (se 2 (by rfl) ⟨13223862, by rfl⟩ : syracuseStep 35263633 = 26447725) B26447725
theorem B47018177 : Blo 2173435 47018177 := bstep (se 2 (by rfl) ⟨17631816, by rfl⟩ : syracuseStep 47018177 = 35263633) B35263633
theorem B31345451 : Blo 2173435 31345451 := bstep (se 1 (by rfl) ⟨23509088, by rfl⟩ : syracuseStep 31345451 = 47018177) B47018177
theorem B20896967 : Blo 2173435 20896967 := bstep (se 1 (by rfl) ⟨15672725, by rfl⟩ : syracuseStep 20896967 = 31345451) B31345451
theorem B13931311 : Blo 2173435 13931311 := bstep (se 1 (by rfl) ⟨10448483, by rfl⟩ : syracuseStep 13931311 = 20896967) B20896967
theorem B18575081 : Blo 2173435 18575081 := bstep (se 2 (by rfl) ⟨6965655, by rfl⟩ : syracuseStep 18575081 = 13931311) B13931311
theorem B12383387 : Blo 2173435 12383387 := bstep (se 1 (by rfl) ⟨9287540, by rfl⟩ : syracuseStep 12383387 = 18575081) B18575081
theorem B8255591 : Blo 2173435 8255591 := bstep (se 1 (by rfl) ⟨6191693, by rfl⟩ : syracuseStep 8255591 = 12383387) B12383387
theorem B5503727 : Blo 2173435 5503727 := bstep (se 1 (by rfl) ⟨4127795, by rfl⟩ : syracuseStep 5503727 = 8255591) B8255591
theorem B3669151 : Blo 2173435 3669151 := bstep (se 1 (by rfl) ⟨2751863, by rfl⟩ : syracuseStep 3669151 = 5503727) B5503727
theorem B4892201 : Blo 2173435 4892201 := bstep (se 2 (by rfl) ⟨1834575, by rfl⟩ : syracuseStep 4892201 = 3669151) B3669151
theorem B3261467 : Blo 2173435 3261467 := bstep (se 1 (by rfl) ⟨2446100, by rfl⟩ : syracuseStep 3261467 = 4892201) B4892201
theorem B2174311 : Blo 2173435 2174311 := bstep (se 1 (by rfl) ⟨1630733, by rfl⟩ : syracuseStep 2174311 = 3261467) B3261467
theorem B2446105 : Blo 2173435 2446105 := bbase (se 2 (by rfl) ⟨917289, by rfl⟩ : syracuseStep 2446105 = 1834579) (by norm_num)
theorem B3261473 : Blo 2173435 3261473 := bstep (se 2 (by rfl) ⟨1223052, by rfl⟩ : syracuseStep 3261473 = 2446105) B2446105
theorem B2174315 : Blo 2173435 2174315 := bstep (se 1 (by rfl) ⟨1630736, by rfl⟩ : syracuseStep 2174315 = 3261473) B3261473
theorem B8255621 : Blo 2173435 8255621 := bbase (se 4 (by rfl) ⟨773964, by rfl⟩ : syracuseStep 8255621 = 1547929) (by norm_num)
theorem B5503747 : Blo 2173435 5503747 := bstep (se 1 (by rfl) ⟨4127810, by rfl⟩ : syracuseStep 5503747 = 8255621) B8255621
theorem B7338329 : Blo 2173435 7338329 := bstep (se 2 (by rfl) ⟨2751873, by rfl⟩ : syracuseStep 7338329 = 5503747) B5503747
theorem B4892219 : Blo 2173435 4892219 := bstep (se 1 (by rfl) ⟨3669164, by rfl⟩ : syracuseStep 4892219 = 7338329) B7338329
theorem B3261479 : Blo 2173435 3261479 := bstep (se 1 (by rfl) ⟨2446109, by rfl⟩ : syracuseStep 3261479 = 4892219) B4892219
theorem B2174319 : Blo 2173435 2174319 := bstep (se 1 (by rfl) ⟨1630739, by rfl⟩ : syracuseStep 2174319 = 3261479) B3261479
theorem B3261485 : Blo 2173435 3261485 := bbase (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) (by norm_num)
theorem B2174323 : Blo 2173435 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B4892237 : Blo 2173435 4892237 := bbase (se 3 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 4892237 = 1834589) (by norm_num)
theorem B3261491 : Blo 2173435 3261491 := bstep (se 1 (by rfl) ⟨2446118, by rfl⟩ : syracuseStep 3261491 = 4892237) B4892237
theorem B2174327 : Blo 2173435 2174327 := bstep (se 1 (by rfl) ⟨1630745, by rfl⟩ : syracuseStep 2174327 = 3261491) B3261491
theorem B2751889 : Blo 2173435 2751889 := bbase (se 2 (by rfl) ⟨1031958, by rfl⟩ : syracuseStep 2751889 = 2063917) (by norm_num)
theorem B3669185 : Blo 2173435 3669185 := bstep (se 2 (by rfl) ⟨1375944, by rfl⟩ : syracuseStep 3669185 = 2751889) B2751889
theorem B2446123 : Blo 2173435 2446123 := bstep (se 1 (by rfl) ⟨1834592, by rfl⟩ : syracuseStep 2446123 = 3669185) B3669185
theorem B3261497 : Blo 2173435 3261497 := bstep (se 2 (by rfl) ⟨1223061, by rfl⟩ : syracuseStep 3261497 = 2446123) B2446123
theorem B2174331 : Blo 2173435 2174331 := bstep (se 1 (by rfl) ⟨1630748, by rfl⟩ : syracuseStep 2174331 = 3261497) B3261497
theorem B4643821 : Blo 2173435 4643821 := bbase (se 3 (by rfl) ⟨870716, by rfl⟩ : syracuseStep 4643821 = 1741433) (by norm_num)
theorem B24767045 : Blo 2173435 24767045 := bstep (se 4 (by rfl) ⟨2321910, by rfl⟩ : syracuseStep 24767045 = 4643821) B4643821
theorem B16511363 : Blo 2173435 16511363 := bstep (se 1 (by rfl) ⟨12383522, by rfl⟩ : syracuseStep 16511363 = 24767045) B24767045
theorem B11007575 : Blo 2173435 11007575 := bstep (se 1 (by rfl) ⟨8255681, by rfl⟩ : syracuseStep 11007575 = 16511363) B16511363
theorem B7338383 : Blo 2173435 7338383 := bstep (se 1 (by rfl) ⟨5503787, by rfl⟩ : syracuseStep 7338383 = 11007575) B11007575
theorem B4892255 : Blo 2173435 4892255 := bstep (se 1 (by rfl) ⟨3669191, by rfl⟩ : syracuseStep 4892255 = 7338383) B7338383
theorem B3261503 : Blo 2173435 3261503 := bstep (se 1 (by rfl) ⟨2446127, by rfl⟩ : syracuseStep 3261503 = 4892255) B4892255
theorem B2174335 : Blo 2173435 2174335 := bstep (se 1 (by rfl) ⟨1630751, by rfl⟩ : syracuseStep 2174335 = 3261503) B3261503
theorem B3261509 : Blo 2173435 3261509 := bbase (se 4 (by rfl) ⟨305766, by rfl⟩ : syracuseStep 3261509 = 611533) (by norm_num)
theorem B2174339 : Blo 2173435 2174339 := bstep (se 1 (by rfl) ⟨1630754, by rfl⟩ : syracuseStep 2174339 = 3261509) B3261509
theorem B3669205 : Blo 2173435 3669205 := bbase (se 7 (by rfl) ⟨42998, by rfl⟩ : syracuseStep 3669205 = 85997) (by norm_num)
theorem B4892273 : Blo 2173435 4892273 := bstep (se 2 (by rfl) ⟨1834602, by rfl⟩ : syracuseStep 4892273 = 3669205) B3669205
theorem B3261515 : Blo 2173435 3261515 := bstep (se 1 (by rfl) ⟨2446136, by rfl⟩ : syracuseStep 3261515 = 4892273) B4892273
theorem B2174343 : Blo 2173435 2174343 := bstep (se 1 (by rfl) ⟨1630757, by rfl⟩ : syracuseStep 2174343 = 3261515) B3261515
theorem B2446141 : Blo 2173435 2446141 := bbase (se 3 (by rfl) ⟨458651, by rfl⟩ : syracuseStep 2446141 = 917303) (by norm_num)
theorem B3261521 : Blo 2173435 3261521 := bstep (se 2 (by rfl) ⟨1223070, by rfl⟩ : syracuseStep 3261521 = 2446141) B2446141
theorem B2174347 : Blo 2173435 2174347 := bstep (se 1 (by rfl) ⟨1630760, by rfl⟩ : syracuseStep 2174347 = 3261521) B3261521
theorem B7338437 : Blo 2173435 7338437 := bbase (se 4 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 7338437 = 1375957) (by norm_num)
theorem B4892291 : Blo 2173435 4892291 := bstep (se 1 (by rfl) ⟨3669218, by rfl⟩ : syracuseStep 4892291 = 7338437) B7338437
theorem B3261527 : Blo 2173435 3261527 := bstep (se 1 (by rfl) ⟨2446145, by rfl⟩ : syracuseStep 3261527 = 4892291) B4892291
theorem B2174351 : Blo 2173435 2174351 := bstep (se 1 (by rfl) ⟨1630763, by rfl⟩ : syracuseStep 2174351 = 3261527) B3261527
theorem B3261533 : Blo 2173435 3261533 := bbase (se 3 (by rfl) ⟨611537, by rfl⟩ : syracuseStep 3261533 = 1223075) (by norm_num)
theorem B2174355 : Blo 2173435 2174355 := bstep (se 1 (by rfl) ⟨1630766, by rfl⟩ : syracuseStep 2174355 = 3261533) B3261533
theorem B4892309 : Blo 2173435 4892309 := bbase (se 6 (by rfl) ⟨114663, by rfl⟩ : syracuseStep 4892309 = 229327) (by norm_num)
theorem B3261539 : Blo 2173435 3261539 := bstep (se 1 (by rfl) ⟨2446154, by rfl⟩ : syracuseStep 3261539 = 4892309) B4892309
theorem B2174359 : Blo 2173435 2174359 := bstep (se 1 (by rfl) ⟨1630769, by rfl⟩ : syracuseStep 2174359 = 3261539) B3261539
theorem B2321941 : Blo 2173435 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B3095921 : Blo 2173435 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B8255789 : Blo 2173435 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B5503859 : Blo 2173435 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B3669239 : Blo 2173435 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B2446159 : Blo 2173435 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B3261545 : Blo 2173435 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B2174363 : Blo 2173435 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B13931669 : Blo 2173435 13931669 := bbase (se 6 (by rfl) ⟨326523, by rfl⟩ : syracuseStep 13931669 = 653047) (by norm_num)
theorem B9287779 : Blo 2173435 9287779 := bstep (se 1 (by rfl) ⟨6965834, by rfl⟩ : syracuseStep 9287779 = 13931669) B13931669
theorem B12383705 : Blo 2173435 12383705 := bstep (se 2 (by rfl) ⟨4643889, by rfl⟩ : syracuseStep 12383705 = 9287779) B9287779
theorem B8255803 : Blo 2173435 8255803 := bstep (se 1 (by rfl) ⟨6191852, by rfl⟩ : syracuseStep 8255803 = 12383705) B12383705
theorem B11007737 : Blo 2173435 11007737 := bstep (se 2 (by rfl) ⟨4127901, by rfl⟩ : syracuseStep 11007737 = 8255803) B8255803
theorem B7338491 : Blo 2173435 7338491 := bstep (se 1 (by rfl) ⟨5503868, by rfl⟩ : syracuseStep 7338491 = 11007737) B11007737
theorem B4892327 : Blo 2173435 4892327 := bstep (se 1 (by rfl) ⟨3669245, by rfl⟩ : syracuseStep 4892327 = 7338491) B7338491
theorem B3261551 : Blo 2173435 3261551 := bstep (se 1 (by rfl) ⟨2446163, by rfl⟩ : syracuseStep 3261551 = 4892327) B4892327
theorem B2174367 : Blo 2173435 2174367 := bstep (se 1 (by rfl) ⟨1630775, by rfl⟩ : syracuseStep 2174367 = 3261551) B3261551
theorem B3261557 : Blo 2173435 3261557 := bbase (se 5 (by rfl) ⟨152885, by rfl⟩ : syracuseStep 3261557 = 305771) (by norm_num)
theorem B2174371 : Blo 2173435 2174371 := bstep (se 1 (by rfl) ⟨1630778, by rfl⟩ : syracuseStep 2174371 = 3261557) B3261557
theorem B4127917 : Blo 2173435 4127917 := bbase (se 3 (by rfl) ⟨773984, by rfl⟩ : syracuseStep 4127917 = 1547969) (by norm_num)
theorem B5503889 : Blo 2173435 5503889 := bstep (se 2 (by rfl) ⟨2063958, by rfl⟩ : syracuseStep 5503889 = 4127917) B4127917
theorem B3669259 : Blo 2173435 3669259 := bstep (se 1 (by rfl) ⟨2751944, by rfl⟩ : syracuseStep 3669259 = 5503889) B5503889
theorem B4892345 : Blo 2173435 4892345 := bstep (se 2 (by rfl) ⟨1834629, by rfl⟩ : syracuseStep 4892345 = 3669259) B3669259
theorem B3261563 : Blo 2173435 3261563 := bstep (se 1 (by rfl) ⟨2446172, by rfl⟩ : syracuseStep 3261563 = 4892345) B4892345
theorem B2174375 : Blo 2173435 2174375 := bstep (se 1 (by rfl) ⟨1630781, by rfl⟩ : syracuseStep 2174375 = 3261563) B3261563
theorem B2446177 : Blo 2173435 2446177 := bbase (se 2 (by rfl) ⟨917316, by rfl⟩ : syracuseStep 2446177 = 1834633) (by norm_num)
theorem B3261569 : Blo 2173435 3261569 := bstep (se 2 (by rfl) ⟨1223088, by rfl⟩ : syracuseStep 3261569 = 2446177) B2446177
theorem B2174379 : Blo 2173435 2174379 := bstep (se 1 (by rfl) ⟨1630784, by rfl⟩ : syracuseStep 2174379 = 3261569) B3261569
theorem B5503909 : Blo 2173435 5503909 := bbase (se 4 (by rfl) ⟨515991, by rfl⟩ : syracuseStep 5503909 = 1031983) (by norm_num)
theorem B7338545 : Blo 2173435 7338545 := bstep (se 2 (by rfl) ⟨2751954, by rfl⟩ : syracuseStep 7338545 = 5503909) B5503909
theorem B4892363 : Blo 2173435 4892363 := bstep (se 1 (by rfl) ⟨3669272, by rfl⟩ : syracuseStep 4892363 = 7338545) B7338545
theorem B3261575 : Blo 2173435 3261575 := bstep (se 1 (by rfl) ⟨2446181, by rfl⟩ : syracuseStep 3261575 = 4892363) B4892363
theorem B2174383 : Blo 2173435 2174383 := bstep (se 1 (by rfl) ⟨1630787, by rfl⟩ : syracuseStep 2174383 = 3261575) B3261575
theorem B3261581 : Blo 2173435 3261581 := bbase (se 3 (by rfl) ⟨611546, by rfl⟩ : syracuseStep 3261581 = 1223093) (by norm_num)
theorem B2174387 : Blo 2173435 2174387 := bstep (se 1 (by rfl) ⟨1630790, by rfl⟩ : syracuseStep 2174387 = 3261581) B3261581
theorem B4892381 : Blo 2173435 4892381 := bbase (se 3 (by rfl) ⟨917321, by rfl⟩ : syracuseStep 4892381 = 1834643) (by norm_num)
theorem B3261587 : Blo 2173435 3261587 := bstep (se 1 (by rfl) ⟨2446190, by rfl⟩ : syracuseStep 3261587 = 4892381) B4892381
theorem B2174391 : Blo 2173435 2174391 := bstep (se 1 (by rfl) ⟨1630793, by rfl⟩ : syracuseStep 2174391 = 3261587) B3261587
theorem B3669293 : Blo 2173435 3669293 := bbase (se 3 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 3669293 = 1375985) (by norm_num)
theorem B2446195 : Blo 2173435 2446195 := bstep (se 1 (by rfl) ⟨1834646, by rfl⟩ : syracuseStep 2446195 = 3669293) B3669293
theorem B3261593 : Blo 2173435 3261593 := bstep (se 2 (by rfl) ⟨1223097, by rfl⟩ : syracuseStep 3261593 = 2446195) B2446195
theorem B2174395 : Blo 2173435 2174395 := bstep (se 1 (by rfl) ⟨1630796, by rfl⟩ : syracuseStep 2174395 = 3261593) B3261593
theorem B4959149 : Blo 2173435 4959149 := bbase (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) (by norm_num)
theorem B13224397 : Blo 2173435 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B17632529 : Blo 2173435 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B11755019 : Blo 2173435 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B7836679 : Blo 2173435 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B41795621 : Blo 2173435 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B27863747 : Blo 2173435 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B18575831 : Blo 2173435 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B12383887 : Blo 2173435 12383887 := bstep (se 1 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 12383887 = 18575831) B18575831
theorem B16511849 : Blo 2173435 16511849 := bstep (se 2 (by rfl) ⟨6191943, by rfl⟩ : syracuseStep 16511849 = 12383887) B12383887
theorem B11007899 : Blo 2173435 11007899 := bstep (se 1 (by rfl) ⟨8255924, by rfl⟩ : syracuseStep 11007899 = 16511849) B16511849
theorem B7338599 : Blo 2173435 7338599 := bstep (se 1 (by rfl) ⟨5503949, by rfl⟩ : syracuseStep 7338599 = 11007899) B11007899
theorem B4892399 : Blo 2173435 4892399 := bstep (se 1 (by rfl) ⟨3669299, by rfl⟩ : syracuseStep 4892399 = 7338599) B7338599
theorem B3261599 : Blo 2173435 3261599 := bstep (se 1 (by rfl) ⟨2446199, by rfl⟩ : syracuseStep 3261599 = 4892399) B4892399
theorem B2174399 : Blo 2173435 2174399 := bstep (se 1 (by rfl) ⟨1630799, by rfl⟩ : syracuseStep 2174399 = 3261599) B3261599
theorem B3261605 : Blo 2173435 3261605 := bbase (se 4 (by rfl) ⟨305775, by rfl⟩ : syracuseStep 3261605 = 611551) (by norm_num)
theorem B2174403 : Blo 2173435 2174403 := bstep (se 1 (by rfl) ⟨1630802, by rfl⟩ : syracuseStep 2174403 = 3261605) B3261605
theorem B2751985 : Blo 2173435 2751985 := bbase (se 2 (by rfl) ⟨1031994, by rfl⟩ : syracuseStep 2751985 = 2063989) (by norm_num)
theorem B3669313 : Blo 2173435 3669313 := bstep (se 2 (by rfl) ⟨1375992, by rfl⟩ : syracuseStep 3669313 = 2751985) B2751985
theorem B4892417 : Blo 2173435 4892417 := bstep (se 2 (by rfl) ⟨1834656, by rfl⟩ : syracuseStep 4892417 = 3669313) B3669313
theorem B3261611 : Blo 2173435 3261611 := bstep (se 1 (by rfl) ⟨2446208, by rfl⟩ : syracuseStep 3261611 = 4892417) B4892417
theorem B2174407 : Blo 2173435 2174407 := bstep (se 1 (by rfl) ⟨1630805, by rfl⟩ : syracuseStep 2174407 = 3261611) B3261611
theorem B2446213 : Blo 2173435 2446213 := bbase (se 4 (by rfl) ⟨229332, by rfl⟩ : syracuseStep 2446213 = 458665) (by norm_num)
theorem B3261617 : Blo 2173435 3261617 := bstep (se 2 (by rfl) ⟨1223106, by rfl⟩ : syracuseStep 3261617 = 2446213) B2446213
theorem B2174411 : Blo 2173435 2174411 := bstep (se 1 (by rfl) ⟨1630808, by rfl⟩ : syracuseStep 2174411 = 3261617) B3261617
theorem B5224493 : Blo 2173435 5224493 := bbase (se 3 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 5224493 = 1959185) (by norm_num)
theorem B3482995 : Blo 2173435 3482995 := bstep (se 1 (by rfl) ⟨2612246, by rfl⟩ : syracuseStep 3482995 = 5224493) B5224493
theorem B4643993 : Blo 2173435 4643993 := bstep (se 2 (by rfl) ⟨1741497, by rfl⟩ : syracuseStep 4643993 = 3482995) B3482995
theorem B3095995 : Blo 2173435 3095995 := bstep (se 1 (by rfl) ⟨2321996, by rfl⟩ : syracuseStep 3095995 = 4643993) B4643993
theorem B4127993 : Blo 2173435 4127993 := bstep (se 2 (by rfl) ⟨1547997, by rfl⟩ : syracuseStep 4127993 = 3095995) B3095995
theorem B2751995 : Blo 2173435 2751995 := bstep (se 1 (by rfl) ⟨2063996, by rfl⟩ : syracuseStep 2751995 = 4127993) B4127993
theorem B7338653 : Blo 2173435 7338653 := bstep (se 3 (by rfl) ⟨1375997, by rfl⟩ : syracuseStep 7338653 = 2751995) B2751995
theorem B4892435 : Blo 2173435 4892435 := bstep (se 1 (by rfl) ⟨3669326, by rfl⟩ : syracuseStep 4892435 = 7338653) B7338653
theorem B3261623 : Blo 2173435 3261623 := bstep (se 1 (by rfl) ⟨2446217, by rfl⟩ : syracuseStep 3261623 = 4892435) B4892435
theorem B2174415 : Blo 2173435 2174415 := bstep (se 1 (by rfl) ⟨1630811, by rfl⟩ : syracuseStep 2174415 = 3261623) B3261623
theorem B3261629 : Blo 2173435 3261629 := bbase (se 3 (by rfl) ⟨611555, by rfl⟩ : syracuseStep 3261629 = 1223111) (by norm_num)
theorem B2174419 : Blo 2173435 2174419 := bstep (se 1 (by rfl) ⟨1630814, by rfl⟩ : syracuseStep 2174419 = 3261629) B3261629
theorem B4892453 : Blo 2173435 4892453 := bbase (se 4 (by rfl) ⟨458667, by rfl⟩ : syracuseStep 4892453 = 917335) (by norm_num)
theorem B3261635 : Blo 2173435 3261635 := bstep (se 1 (by rfl) ⟨2446226, by rfl⟩ : syracuseStep 3261635 = 4892453) B4892453
theorem B2174423 : Blo 2173435 2174423 := bstep (se 1 (by rfl) ⟨1630817, by rfl⟩ : syracuseStep 2174423 = 3261635) B3261635
theorem B5504021 : Blo 2173435 5504021 := bbase (se 6 (by rfl) ⟨129000, by rfl⟩ : syracuseStep 5504021 = 258001) (by norm_num)
theorem B3669347 : Blo 2173435 3669347 := bstep (se 1 (by rfl) ⟨2752010, by rfl⟩ : syracuseStep 3669347 = 5504021) B5504021
theorem B2446231 : Blo 2173435 2446231 := bstep (se 1 (by rfl) ⟨1834673, by rfl⟩ : syracuseStep 2446231 = 3669347) B3669347
theorem B3261641 : Blo 2173435 3261641 := bstep (se 2 (by rfl) ⟨1223115, by rfl⟩ : syracuseStep 3261641 = 2446231) B2446231
theorem B2174427 : Blo 2173435 2174427 := bstep (se 1 (by rfl) ⟨1630820, by rfl⟩ : syracuseStep 2174427 = 3261641) B3261641
theorem B9288053 : Blo 2173435 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B6192035 : Blo 2173435 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B4128023 : Blo 2173435 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B11008061 : Blo 2173435 11008061 := bstep (se 3 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 11008061 = 4128023) B4128023
theorem B7338707 : Blo 2173435 7338707 := bstep (se 1 (by rfl) ⟨5504030, by rfl⟩ : syracuseStep 7338707 = 11008061) B11008061
theorem B4892471 : Blo 2173435 4892471 := bstep (se 1 (by rfl) ⟨3669353, by rfl⟩ : syracuseStep 4892471 = 7338707) B7338707
theorem B3261647 : Blo 2173435 3261647 := bstep (se 1 (by rfl) ⟨2446235, by rfl⟩ : syracuseStep 3261647 = 4892471) B4892471
theorem B2174431 : Blo 2173435 2174431 := bstep (se 1 (by rfl) ⟨1630823, by rfl⟩ : syracuseStep 2174431 = 3261647) B3261647
theorem B3261653 : Blo 2173435 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B2174435 : Blo 2173435 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B3096029 : Blo 2173435 3096029 := bbase (se 3 (by rfl) ⟨580505, by rfl⟩ : syracuseStep 3096029 = 1161011) (by norm_num)
theorem B8256077 : Blo 2173435 8256077 := bstep (se 3 (by rfl) ⟨1548014, by rfl⟩ : syracuseStep 8256077 = 3096029) B3096029
theorem B5504051 : Blo 2173435 5504051 := bstep (se 1 (by rfl) ⟨4128038, by rfl⟩ : syracuseStep 5504051 = 8256077) B8256077
theorem B3669367 : Blo 2173435 3669367 := bstep (se 1 (by rfl) ⟨2752025, by rfl⟩ : syracuseStep 3669367 = 5504051) B5504051
theorem B4892489 : Blo 2173435 4892489 := bstep (se 2 (by rfl) ⟨1834683, by rfl⟩ : syracuseStep 4892489 = 3669367) B3669367
theorem B3261659 : Blo 2173435 3261659 := bstep (se 1 (by rfl) ⟨2446244, by rfl⟩ : syracuseStep 3261659 = 4892489) B4892489
theorem B2174439 : Blo 2173435 2174439 := bstep (se 1 (by rfl) ⟨1630829, by rfl⟩ : syracuseStep 2174439 = 3261659) B3261659
theorem B2446249 : Blo 2173435 2446249 := bbase (se 2 (by rfl) ⟨917343, by rfl⟩ : syracuseStep 2446249 = 1834687) (by norm_num)
theorem B3261665 : Blo 2173435 3261665 := bstep (se 2 (by rfl) ⟨1223124, by rfl⟩ : syracuseStep 3261665 = 2446249) B2446249
theorem B2174443 : Blo 2173435 2174443 := bstep (se 1 (by rfl) ⟨1630832, by rfl⟩ : syracuseStep 2174443 = 3261665) B3261665
theorem B7836853 : Blo 2173435 7836853 := bbase (se 5 (by rfl) ⟨367352, by rfl⟩ : syracuseStep 7836853 = 734705) (by norm_num)
theorem B10449137 : Blo 2173435 10449137 := bstep (se 2 (by rfl) ⟨3918426, by rfl⟩ : syracuseStep 10449137 = 7836853) B7836853
theorem B6966091 : Blo 2173435 6966091 := bstep (se 1 (by rfl) ⟨5224568, by rfl⟩ : syracuseStep 6966091 = 10449137) B10449137
theorem B9288121 : Blo 2173435 9288121 := bstep (se 2 (by rfl) ⟨3483045, by rfl⟩ : syracuseStep 9288121 = 6966091) B6966091
theorem B12384161 : Blo 2173435 12384161 := bstep (se 2 (by rfl) ⟨4644060, by rfl⟩ : syracuseStep 12384161 = 9288121) B9288121
theorem B8256107 : Blo 2173435 8256107 := bstep (se 1 (by rfl) ⟨6192080, by rfl⟩ : syracuseStep 8256107 = 12384161) B12384161
theorem B5504071 : Blo 2173435 5504071 := bstep (se 1 (by rfl) ⟨4128053, by rfl⟩ : syracuseStep 5504071 = 8256107) B8256107
theorem B7338761 : Blo 2173435 7338761 := bstep (se 2 (by rfl) ⟨2752035, by rfl⟩ : syracuseStep 7338761 = 5504071) B5504071
theorem B4892507 : Blo 2173435 4892507 := bstep (se 1 (by rfl) ⟨3669380, by rfl⟩ : syracuseStep 4892507 = 7338761) B7338761
theorem B3261671 : Blo 2173435 3261671 := bstep (se 1 (by rfl) ⟨2446253, by rfl⟩ : syracuseStep 3261671 = 4892507) B4892507
theorem B2174447 : Blo 2173435 2174447 := bstep (se 1 (by rfl) ⟨1630835, by rfl⟩ : syracuseStep 2174447 = 3261671) B3261671
theorem B3261677 : Blo 2173435 3261677 := bbase (se 3 (by rfl) ⟨611564, by rfl⟩ : syracuseStep 3261677 = 1223129) (by norm_num)
theorem B2174451 : Blo 2173435 2174451 := bstep (se 1 (by rfl) ⟨1630838, by rfl⟩ : syracuseStep 2174451 = 3261677) B3261677
theorem B4892525 : Blo 2173435 4892525 := bbase (se 3 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 4892525 = 1834697) (by norm_num)
theorem B3261683 : Blo 2173435 3261683 := bstep (se 1 (by rfl) ⟨2446262, by rfl⟩ : syracuseStep 3261683 = 4892525) B4892525
theorem B2174455 : Blo 2173435 2174455 := bstep (se 1 (by rfl) ⟨1630841, by rfl⟩ : syracuseStep 2174455 = 3261683) B3261683
theorem B4128077 : Blo 2173435 4128077 := bbase (se 3 (by rfl) ⟨774014, by rfl⟩ : syracuseStep 4128077 = 1548029) (by norm_num)
theorem B2752051 : Blo 2173435 2752051 := bstep (se 1 (by rfl) ⟨2064038, by rfl⟩ : syracuseStep 2752051 = 4128077) B4128077
theorem B3669401 : Blo 2173435 3669401 := bstep (se 2 (by rfl) ⟨1376025, by rfl⟩ : syracuseStep 3669401 = 2752051) B2752051
theorem B2446267 : Blo 2173435 2446267 := bstep (se 1 (by rfl) ⟨1834700, by rfl⟩ : syracuseStep 2446267 = 3669401) B3669401
theorem B3261689 : Blo 2173435 3261689 := bstep (se 2 (by rfl) ⟨1223133, by rfl⟩ : syracuseStep 3261689 = 2446267) B2446267
theorem B2174459 : Blo 2173435 2174459 := bstep (se 1 (by rfl) ⟨1630844, by rfl⟩ : syracuseStep 2174459 = 3261689) B3261689
theorem B3971917 : Blo 2173435 3971917 := bbase (se 3 (by rfl) ⟨744734, by rfl⟩ : syracuseStep 3971917 = 1489469) (by norm_num)
theorem B5295889 : Blo 2173435 5295889 := bstep (se 2 (by rfl) ⟨1985958, by rfl⟩ : syracuseStep 5295889 = 3971917) B3971917
theorem B7061185 : Blo 2173435 7061185 := bstep (se 2 (by rfl) ⟨2647944, by rfl⟩ : syracuseStep 7061185 = 5295889) B5295889
theorem B9414913 : Blo 2173435 9414913 := bstep (se 2 (by rfl) ⟨3530592, by rfl⟩ : syracuseStep 9414913 = 7061185) B7061185
theorem B12553217 : Blo 2173435 12553217 := bstep (se 2 (by rfl) ⟨4707456, by rfl⟩ : syracuseStep 12553217 = 9414913) B9414913
theorem B8368811 : Blo 2173435 8368811 := bstep (se 1 (by rfl) ⟨6276608, by rfl⟩ : syracuseStep 8368811 = 12553217) B12553217
theorem B5579207 : Blo 2173435 5579207 := bstep (se 1 (by rfl) ⟨4184405, by rfl⟩ : syracuseStep 5579207 = 8368811) B8368811
theorem B3719471 : Blo 2173435 3719471 := bstep (se 1 (by rfl) ⟨2789603, by rfl⟩ : syracuseStep 3719471 = 5579207) B5579207
theorem B39674357 : Blo 2173435 39674357 := bstep (se 5 (by rfl) ⟨1859735, by rfl⟩ : syracuseStep 39674357 = 3719471) B3719471
theorem B26449571 : Blo 2173435 26449571 := bstep (se 1 (by rfl) ⟨19837178, by rfl⟩ : syracuseStep 26449571 = 39674357) B39674357
theorem B17633047 : Blo 2173435 17633047 := bstep (se 1 (by rfl) ⟨13224785, by rfl⟩ : syracuseStep 17633047 = 26449571) B26449571
theorem B23510729 : Blo 2173435 23510729 := bstep (se 2 (by rfl) ⟨8816523, by rfl⟩ : syracuseStep 23510729 = 17633047) B17633047
theorem B15673819 : Blo 2173435 15673819 := bstep (se 1 (by rfl) ⟨11755364, by rfl⟩ : syracuseStep 15673819 = 23510729) B23510729
theorem B20898425 : Blo 2173435 20898425 := bstep (se 2 (by rfl) ⟨7836909, by rfl⟩ : syracuseStep 20898425 = 15673819) B15673819
theorem B55729133 : Blo 2173435 55729133 := bstep (se 3 (by rfl) ⟨10449212, by rfl⟩ : syracuseStep 55729133 = 20898425) B20898425
theorem B37152755 : Blo 2173435 37152755 := bstep (se 1 (by rfl) ⟨27864566, by rfl⟩ : syracuseStep 37152755 = 55729133) B55729133
theorem B24768503 : Blo 2173435 24768503 := bstep (se 1 (by rfl) ⟨18576377, by rfl⟩ : syracuseStep 24768503 = 37152755) B37152755
theorem B16512335 : Blo 2173435 16512335 := bstep (se 1 (by rfl) ⟨12384251, by rfl⟩ : syracuseStep 16512335 = 24768503) B24768503
theorem B11008223 : Blo 2173435 11008223 := bstep (se 1 (by rfl) ⟨8256167, by rfl⟩ : syracuseStep 11008223 = 16512335) B16512335
theorem B7338815 : Blo 2173435 7338815 := bstep (se 1 (by rfl) ⟨5504111, by rfl⟩ : syracuseStep 7338815 = 11008223) B11008223
theorem B4892543 : Blo 2173435 4892543 := bstep (se 1 (by rfl) ⟨3669407, by rfl⟩ : syracuseStep 4892543 = 7338815) B7338815
theorem B3261695 : Blo 2173435 3261695 := bstep (se 1 (by rfl) ⟨2446271, by rfl⟩ : syracuseStep 3261695 = 4892543) B4892543
theorem B2174463 : Blo 2173435 2174463 := bstep (se 1 (by rfl) ⟨1630847, by rfl⟩ : syracuseStep 2174463 = 3261695) B3261695
theorem B3261701 : Blo 2173435 3261701 := bbase (se 4 (by rfl) ⟨305784, by rfl⟩ : syracuseStep 3261701 = 611569) (by norm_num)
theorem B2174467 : Blo 2173435 2174467 := bstep (se 1 (by rfl) ⟨1630850, by rfl⟩ : syracuseStep 2174467 = 3261701) B3261701
theorem B3669421 : Blo 2173435 3669421 := bbase (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) (by norm_num)
theorem B4892561 : Blo 2173435 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B3261707 : Blo 2173435 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B2174471 : Blo 2173435 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B2446285 : Blo 2173435 2446285 := bbase (se 3 (by rfl) ⟨458678, by rfl⟩ : syracuseStep 2446285 = 917357) (by norm_num)
theorem B3261713 : Blo 2173435 3261713 := bstep (se 2 (by rfl) ⟨1223142, by rfl⟩ : syracuseStep 3261713 = 2446285) B2446285
theorem B2174475 : Blo 2173435 2174475 := bstep (se 1 (by rfl) ⟨1630856, by rfl⟩ : syracuseStep 2174475 = 3261713) B3261713
theorem B7338869 : Blo 2173435 7338869 := bbase (se 5 (by rfl) ⟨344009, by rfl⟩ : syracuseStep 7338869 = 688019) (by norm_num)
theorem B4892579 : Blo 2173435 4892579 := bstep (se 1 (by rfl) ⟨3669434, by rfl⟩ : syracuseStep 4892579 = 7338869) B7338869
theorem B3261719 : Blo 2173435 3261719 := bstep (se 1 (by rfl) ⟨2446289, by rfl⟩ : syracuseStep 3261719 = 4892579) B4892579
theorem B2174479 : Blo 2173435 2174479 := bstep (se 1 (by rfl) ⟨1630859, by rfl⟩ : syracuseStep 2174479 = 3261719) B3261719
theorem B3261725 : Blo 2173435 3261725 := bbase (se 3 (by rfl) ⟨611573, by rfl⟩ : syracuseStep 3261725 = 1223147) (by norm_num)
theorem B2174483 : Blo 2173435 2174483 := bstep (se 1 (by rfl) ⟨1630862, by rfl⟩ : syracuseStep 2174483 = 3261725) B3261725
theorem B4892597 : Blo 2173435 4892597 := bbase (se 5 (by rfl) ⟨229340, by rfl⟩ : syracuseStep 4892597 = 458681) (by norm_num)
theorem B3261731 : Blo 2173435 3261731 := bstep (se 1 (by rfl) ⟨2446298, by rfl⟩ : syracuseStep 3261731 = 4892597) B4892597
theorem B2174487 : Blo 2173435 2174487 := bstep (se 1 (by rfl) ⟨1630865, by rfl⟩ : syracuseStep 2174487 = 3261731) B3261731
theorem B7837013 : Blo 2173435 7837013 := bbase (se 14 (by rfl) ⟨717, by rfl⟩ : syracuseStep 7837013 = 1435) (by norm_num)
theorem B5224675 : Blo 2173435 5224675 := bstep (se 1 (by rfl) ⟨3918506, by rfl⟩ : syracuseStep 5224675 = 7837013) B7837013
theorem B6966233 : Blo 2173435 6966233 := bstep (se 2 (by rfl) ⟨2612337, by rfl⟩ : syracuseStep 6966233 = 5224675) B5224675
theorem B4644155 : Blo 2173435 4644155 := bstep (se 1 (by rfl) ⟨3483116, by rfl⟩ : syracuseStep 4644155 = 6966233) B6966233
theorem B12384413 : Blo 2173435 12384413 := bstep (se 3 (by rfl) ⟨2322077, by rfl⟩ : syracuseStep 12384413 = 4644155) B4644155
theorem B8256275 : Blo 2173435 8256275 := bstep (se 1 (by rfl) ⟨6192206, by rfl⟩ : syracuseStep 8256275 = 12384413) B12384413
theorem B5504183 : Blo 2173435 5504183 := bstep (se 1 (by rfl) ⟨4128137, by rfl⟩ : syracuseStep 5504183 = 8256275) B8256275
theorem B3669455 : Blo 2173435 3669455 := bstep (se 1 (by rfl) ⟨2752091, by rfl⟩ : syracuseStep 3669455 = 5504183) B5504183
theorem B2446303 : Blo 2173435 2446303 := bstep (se 1 (by rfl) ⟨1834727, by rfl⟩ : syracuseStep 2446303 = 3669455) B3669455
theorem B3261737 : Blo 2173435 3261737 := bstep (se 2 (by rfl) ⟨1223151, by rfl⟩ : syracuseStep 3261737 = 2446303) B2446303
theorem B2174491 : Blo 2173435 2174491 := bstep (se 1 (by rfl) ⟨1630868, by rfl⟩ : syracuseStep 2174491 = 3261737) B3261737
theorem B6966245 : Blo 2173435 6966245 := bbase (se 4 (by rfl) ⟨653085, by rfl⟩ : syracuseStep 6966245 = 1306171) (by norm_num)
theorem B4644163 : Blo 2173435 4644163 := bstep (se 1 (by rfl) ⟨3483122, by rfl⟩ : syracuseStep 4644163 = 6966245) B6966245
theorem B6192217 : Blo 2173435 6192217 := bstep (se 2 (by rfl) ⟨2322081, by rfl⟩ : syracuseStep 6192217 = 4644163) B4644163
theorem B8256289 : Blo 2173435 8256289 := bstep (se 2 (by rfl) ⟨3096108, by rfl⟩ : syracuseStep 8256289 = 6192217) B6192217
theorem B11008385 : Blo 2173435 11008385 := bstep (se 2 (by rfl) ⟨4128144, by rfl⟩ : syracuseStep 11008385 = 8256289) B8256289
theorem B7338923 : Blo 2173435 7338923 := bstep (se 1 (by rfl) ⟨5504192, by rfl⟩ : syracuseStep 7338923 = 11008385) B11008385
theorem B4892615 : Blo 2173435 4892615 := bstep (se 1 (by rfl) ⟨3669461, by rfl⟩ : syracuseStep 4892615 = 7338923) B7338923
theorem B3261743 : Blo 2173435 3261743 := bstep (se 1 (by rfl) ⟨2446307, by rfl⟩ : syracuseStep 3261743 = 4892615) B4892615
theorem B2174495 : Blo 2173435 2174495 := bstep (se 1 (by rfl) ⟨1630871, by rfl⟩ : syracuseStep 2174495 = 3261743) B3261743
theorem B3261749 : Blo 2173435 3261749 := bbase (se 5 (by rfl) ⟨152894, by rfl⟩ : syracuseStep 3261749 = 305789) (by norm_num)
theorem B2174499 : Blo 2173435 2174499 := bstep (se 1 (by rfl) ⟨1630874, by rfl⟩ : syracuseStep 2174499 = 3261749) B3261749
theorem B5504213 : Blo 2173435 5504213 := bbase (se 7 (by rfl) ⟨64502, by rfl⟩ : syracuseStep 5504213 = 129005) (by norm_num)
theorem B3669475 : Blo 2173435 3669475 := bstep (se 1 (by rfl) ⟨2752106, by rfl⟩ : syracuseStep 3669475 = 5504213) B5504213
theorem B4892633 : Blo 2173435 4892633 := bstep (se 2 (by rfl) ⟨1834737, by rfl⟩ : syracuseStep 4892633 = 3669475) B3669475
theorem B3261755 : Blo 2173435 3261755 := bstep (se 1 (by rfl) ⟨2446316, by rfl⟩ : syracuseStep 3261755 = 4892633) B4892633
theorem B2174503 : Blo 2173435 2174503 := bstep (se 1 (by rfl) ⟨1630877, by rfl⟩ : syracuseStep 2174503 = 3261755) B3261755
theorem B2446321 : Blo 2173435 2446321 := bbase (se 2 (by rfl) ⟨917370, by rfl⟩ : syracuseStep 2446321 = 1834741) (by norm_num)
theorem B3261761 : Blo 2173435 3261761 := bstep (se 2 (by rfl) ⟨1223160, by rfl⟩ : syracuseStep 3261761 = 2446321) B2446321
theorem B2174507 : Blo 2173435 2174507 := bstep (se 1 (by rfl) ⟨1630880, by rfl⟩ : syracuseStep 2174507 = 3261761) B3261761
theorem B10449445 : Blo 2173435 10449445 := bbase (se 4 (by rfl) ⟨979635, by rfl⟩ : syracuseStep 10449445 = 1959271) (by norm_num)
theorem B13932593 : Blo 2173435 13932593 := bstep (se 2 (by rfl) ⟨5224722, by rfl⟩ : syracuseStep 13932593 = 10449445) B10449445
theorem B9288395 : Blo 2173435 9288395 := bstep (se 1 (by rfl) ⟨6966296, by rfl⟩ : syracuseStep 9288395 = 13932593) B13932593
theorem B6192263 : Blo 2173435 6192263 := bstep (se 1 (by rfl) ⟨4644197, by rfl⟩ : syracuseStep 6192263 = 9288395) B9288395
theorem B4128175 : Blo 2173435 4128175 := bstep (se 1 (by rfl) ⟨3096131, by rfl⟩ : syracuseStep 4128175 = 6192263) B6192263
theorem B5504233 : Blo 2173435 5504233 := bstep (se 2 (by rfl) ⟨2064087, by rfl⟩ : syracuseStep 5504233 = 4128175) B4128175
theorem B7338977 : Blo 2173435 7338977 := bstep (se 2 (by rfl) ⟨2752116, by rfl⟩ : syracuseStep 7338977 = 5504233) B5504233
theorem B4892651 : Blo 2173435 4892651 := bstep (se 1 (by rfl) ⟨3669488, by rfl⟩ : syracuseStep 4892651 = 7338977) B7338977
theorem B3261767 : Blo 2173435 3261767 := bstep (se 1 (by rfl) ⟨2446325, by rfl⟩ : syracuseStep 3261767 = 4892651) B4892651
theorem B2174511 : Blo 2173435 2174511 := bstep (se 1 (by rfl) ⟨1630883, by rfl⟩ : syracuseStep 2174511 = 3261767) B3261767
theorem B3261773 : Blo 2173435 3261773 := bbase (se 3 (by rfl) ⟨611582, by rfl⟩ : syracuseStep 3261773 = 1223165) (by norm_num)
theorem B2174515 : Blo 2173435 2174515 := bstep (se 1 (by rfl) ⟨1630886, by rfl⟩ : syracuseStep 2174515 = 3261773) B3261773
theorem B4892669 : Blo 2173435 4892669 := bbase (se 3 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 4892669 = 1834751) (by norm_num)
theorem B3261779 : Blo 2173435 3261779 := bstep (se 1 (by rfl) ⟨2446334, by rfl⟩ : syracuseStep 3261779 = 4892669) B4892669
theorem B2174519 : Blo 2173435 2174519 := bstep (se 1 (by rfl) ⟨1630889, by rfl⟩ : syracuseStep 2174519 = 3261779) B3261779
theorem B3669509 : Blo 2173435 3669509 := bbase (se 4 (by rfl) ⟨344016, by rfl⟩ : syracuseStep 3669509 = 688033) (by norm_num)
theorem B2446339 : Blo 2173435 2446339 := bstep (se 1 (by rfl) ⟨1834754, by rfl⟩ : syracuseStep 2446339 = 3669509) B3669509
theorem B3261785 : Blo 2173435 3261785 := bstep (se 2 (by rfl) ⟨1223169, by rfl⟩ : syracuseStep 3261785 = 2446339) B2446339
theorem B2174523 : Blo 2173435 2174523 := bstep (se 1 (by rfl) ⟨1630892, by rfl⟩ : syracuseStep 2174523 = 3261785) B3261785
theorem B16512821 : Blo 2173435 16512821 := bbase (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) (by norm_num)
theorem B11008547 : Blo 2173435 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B7339031 : Blo 2173435 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B4892687 : Blo 2173435 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B3261791 : Blo 2173435 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B2174527 : Blo 2173435 2174527 := bstep (se 1 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 2174527 = 3261791) B3261791
theorem B3261797 : Blo 2173435 3261797 := bbase (se 4 (by rfl) ⟨305793, by rfl⟩ : syracuseStep 3261797 = 611587) (by norm_num)
theorem B2174531 : Blo 2173435 2174531 := bstep (se 1 (by rfl) ⟨1630898, by rfl⟩ : syracuseStep 2174531 = 3261797) B3261797
theorem B4128221 : Blo 2173435 4128221 := bbase (se 3 (by rfl) ⟨774041, by rfl⟩ : syracuseStep 4128221 = 1548083) (by norm_num)
theorem B2752147 : Blo 2173435 2752147 := bstep (se 1 (by rfl) ⟨2064110, by rfl⟩ : syracuseStep 2752147 = 4128221) B4128221
theorem B3669529 : Blo 2173435 3669529 := bstep (se 2 (by rfl) ⟨1376073, by rfl⟩ : syracuseStep 3669529 = 2752147) B2752147
theorem B4892705 : Blo 2173435 4892705 := bstep (se 2 (by rfl) ⟨1834764, by rfl⟩ : syracuseStep 4892705 = 3669529) B3669529
theorem B3261803 : Blo 2173435 3261803 := bstep (se 1 (by rfl) ⟨2446352, by rfl⟩ : syracuseStep 3261803 = 4892705) B4892705
theorem B2174535 : Blo 2173435 2174535 := bstep (se 1 (by rfl) ⟨1630901, by rfl⟩ : syracuseStep 2174535 = 3261803) B3261803
theorem B2446357 : Blo 2173435 2446357 := bbase (se 6 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 2446357 = 114673) (by norm_num)
theorem B3261809 : Blo 2173435 3261809 := bstep (se 2 (by rfl) ⟨1223178, by rfl⟩ : syracuseStep 3261809 = 2446357) B2446357
theorem B2174539 : Blo 2173435 2174539 := bstep (se 1 (by rfl) ⟨1630904, by rfl⟩ : syracuseStep 2174539 = 3261809) B3261809
theorem B2752157 : Blo 2173435 2752157 := bbase (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) (by norm_num)
theorem B7339085 : Blo 2173435 7339085 := bstep (se 3 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 7339085 = 2752157) B2752157
theorem B4892723 : Blo 2173435 4892723 := bstep (se 1 (by rfl) ⟨3669542, by rfl⟩ : syracuseStep 4892723 = 7339085) B7339085
theorem B3261815 : Blo 2173435 3261815 := bstep (se 1 (by rfl) ⟨2446361, by rfl⟩ : syracuseStep 3261815 = 4892723) B4892723
theorem B2174543 : Blo 2173435 2174543 := bstep (se 1 (by rfl) ⟨1630907, by rfl⟩ : syracuseStep 2174543 = 3261815) B3261815
theorem B3261821 : Blo 2173435 3261821 := bbase (se 3 (by rfl) ⟨611591, by rfl⟩ : syracuseStep 3261821 = 1223183) (by norm_num)
theorem B2174547 : Blo 2173435 2174547 := bstep (se 1 (by rfl) ⟨1630910, by rfl⟩ : syracuseStep 2174547 = 3261821) B3261821
theorem B4892741 : Blo 2173435 4892741 := bbase (se 4 (by rfl) ⟨458694, by rfl⟩ : syracuseStep 4892741 = 917389) (by norm_num)
theorem B3261827 : Blo 2173435 3261827 := bstep (se 1 (by rfl) ⟨2446370, by rfl⟩ : syracuseStep 3261827 = 4892741) B4892741
theorem B2174551 : Blo 2173435 2174551 := bstep (se 1 (by rfl) ⟨1630913, by rfl⟩ : syracuseStep 2174551 = 3261827) B3261827
theorem B6192389 : Blo 2173435 6192389 := bbase (se 4 (by rfl) ⟨580536, by rfl⟩ : syracuseStep 6192389 = 1161073) (by norm_num)
theorem B4128259 : Blo 2173435 4128259 := bstep (se 1 (by rfl) ⟨3096194, by rfl⟩ : syracuseStep 4128259 = 6192389) B6192389
theorem B5504345 : Blo 2173435 5504345 := bstep (se 2 (by rfl) ⟨2064129, by rfl⟩ : syracuseStep 5504345 = 4128259) B4128259
theorem B3669563 : Blo 2173435 3669563 := bstep (se 1 (by rfl) ⟨2752172, by rfl⟩ : syracuseStep 3669563 = 5504345) B5504345
theorem B2446375 : Blo 2173435 2446375 := bstep (se 1 (by rfl) ⟨1834781, by rfl⟩ : syracuseStep 2446375 = 3669563) B3669563
theorem B3261833 : Blo 2173435 3261833 := bstep (se 2 (by rfl) ⟨1223187, by rfl⟩ : syracuseStep 3261833 = 2446375) B2446375
theorem B2174555 : Blo 2173435 2174555 := bstep (se 1 (by rfl) ⟨1630916, by rfl⟩ : syracuseStep 2174555 = 3261833) B3261833
theorem B11008709 : Blo 2173435 11008709 := bbase (se 4 (by rfl) ⟨1032066, by rfl⟩ : syracuseStep 11008709 = 2064133) (by norm_num)
theorem B7339139 : Blo 2173435 7339139 := bstep (se 1 (by rfl) ⟨5504354, by rfl⟩ : syracuseStep 7339139 = 11008709) B11008709
theorem B4892759 : Blo 2173435 4892759 := bstep (se 1 (by rfl) ⟨3669569, by rfl⟩ : syracuseStep 4892759 = 7339139) B7339139
theorem B3261839 : Blo 2173435 3261839 := bstep (se 1 (by rfl) ⟨2446379, by rfl⟩ : syracuseStep 3261839 = 4892759) B4892759
theorem B2174559 : Blo 2173435 2174559 := bstep (se 1 (by rfl) ⟨1630919, by rfl⟩ : syracuseStep 2174559 = 3261839) B3261839
theorem B3261845 : Blo 2173435 3261845 := bbase (se 6 (by rfl) ⟨76449, by rfl⟩ : syracuseStep 3261845 = 152899) (by norm_num)
theorem B2174563 : Blo 2173435 2174563 := bstep (se 1 (by rfl) ⟨1630922, by rfl⟩ : syracuseStep 2174563 = 3261845) B3261845
theorem B4644317 : Blo 2173435 4644317 := bbase (se 3 (by rfl) ⟨870809, by rfl⟩ : syracuseStep 4644317 = 1741619) (by norm_num)
theorem B12384845 : Blo 2173435 12384845 := bstep (se 3 (by rfl) ⟨2322158, by rfl⟩ : syracuseStep 12384845 = 4644317) B4644317
theorem B8256563 : Blo 2173435 8256563 := bstep (se 1 (by rfl) ⟨6192422, by rfl⟩ : syracuseStep 8256563 = 12384845) B12384845
theorem B5504375 : Blo 2173435 5504375 := bstep (se 1 (by rfl) ⟨4128281, by rfl⟩ : syracuseStep 5504375 = 8256563) B8256563
theorem B3669583 : Blo 2173435 3669583 := bstep (se 1 (by rfl) ⟨2752187, by rfl⟩ : syracuseStep 3669583 = 5504375) B5504375
theorem B4892777 : Blo 2173435 4892777 := bstep (se 2 (by rfl) ⟨1834791, by rfl⟩ : syracuseStep 4892777 = 3669583) B3669583
theorem B3261851 : Blo 2173435 3261851 := bstep (se 1 (by rfl) ⟨2446388, by rfl⟩ : syracuseStep 3261851 = 4892777) B4892777
theorem B2174567 : Blo 2173435 2174567 := bstep (se 1 (by rfl) ⟨1630925, by rfl⟩ : syracuseStep 2174567 = 3261851) B3261851
theorem B2446393 : Blo 2173435 2446393 := bbase (se 2 (by rfl) ⟨917397, by rfl⟩ : syracuseStep 2446393 = 1834795) (by norm_num)
theorem B3261857 : Blo 2173435 3261857 := bstep (se 2 (by rfl) ⟨1223196, by rfl⟩ : syracuseStep 3261857 = 2446393) B2446393
theorem B2174571 : Blo 2173435 2174571 := bstep (se 1 (by rfl) ⟨1630928, by rfl⟩ : syracuseStep 2174571 = 3261857) B3261857
theorem B5224877 : Blo 2173435 5224877 := bbase (se 3 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 5224877 = 1959329) (by norm_num)
theorem B3483251 : Blo 2173435 3483251 := bstep (se 1 (by rfl) ⟨2612438, by rfl⟩ : syracuseStep 3483251 = 5224877) B5224877
theorem B2322167 : Blo 2173435 2322167 := bstep (se 1 (by rfl) ⟨1741625, by rfl⟩ : syracuseStep 2322167 = 3483251) B3483251
theorem B6192445 : Blo 2173435 6192445 := bstep (se 3 (by rfl) ⟨1161083, by rfl⟩ : syracuseStep 6192445 = 2322167) B2322167
theorem B8256593 : Blo 2173435 8256593 := bstep (se 2 (by rfl) ⟨3096222, by rfl⟩ : syracuseStep 8256593 = 6192445) B6192445
theorem B5504395 : Blo 2173435 5504395 := bstep (se 1 (by rfl) ⟨4128296, by rfl⟩ : syracuseStep 5504395 = 8256593) B8256593
theorem B7339193 : Blo 2173435 7339193 := bstep (se 2 (by rfl) ⟨2752197, by rfl⟩ : syracuseStep 7339193 = 5504395) B5504395
theorem B4892795 : Blo 2173435 4892795 := bstep (se 1 (by rfl) ⟨3669596, by rfl⟩ : syracuseStep 4892795 = 7339193) B7339193
theorem B3261863 : Blo 2173435 3261863 := bstep (se 1 (by rfl) ⟨2446397, by rfl⟩ : syracuseStep 3261863 = 4892795) B4892795
theorem B2174575 : Blo 2173435 2174575 := bstep (se 1 (by rfl) ⟨1630931, by rfl⟩ : syracuseStep 2174575 = 3261863) B3261863
theorem B3261869 : Blo 2173435 3261869 := bbase (se 3 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 3261869 = 1223201) (by norm_num)
theorem B2174579 : Blo 2173435 2174579 := bstep (se 1 (by rfl) ⟨1630934, by rfl⟩ : syracuseStep 2174579 = 3261869) B3261869
theorem B4892813 : Blo 2173435 4892813 := bbase (se 3 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 4892813 = 1834805) (by norm_num)
theorem B3261875 : Blo 2173435 3261875 := bstep (se 1 (by rfl) ⟨2446406, by rfl⟩ : syracuseStep 3261875 = 4892813) B4892813
theorem B2174583 : Blo 2173435 2174583 := bstep (se 1 (by rfl) ⟨1630937, by rfl⟩ : syracuseStep 2174583 = 3261875) B3261875
theorem B2752213 : Blo 2173435 2752213 := bbase (se 7 (by rfl) ⟨32252, by rfl⟩ : syracuseStep 2752213 = 64505) (by norm_num)
theorem B3669617 : Blo 2173435 3669617 := bstep (se 2 (by rfl) ⟨1376106, by rfl⟩ : syracuseStep 3669617 = 2752213) B2752213
theorem B2446411 : Blo 2173435 2446411 := bstep (se 1 (by rfl) ⟨1834808, by rfl⟩ : syracuseStep 2446411 = 3669617) B3669617
theorem B3261881 : Blo 2173435 3261881 := bstep (se 2 (by rfl) ⟨1223205, by rfl⟩ : syracuseStep 3261881 = 2446411) B2446411
theorem B2174587 : Blo 2173435 2174587 := bstep (se 1 (by rfl) ⟨1630940, by rfl⟩ : syracuseStep 2174587 = 3261881) B3261881
theorem B3397229 : Blo 2173435 3397229 := bbase (se 3 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 3397229 = 1273961) (by norm_num)
theorem B2264819 : Blo 2173435 2264819 := bstep (se 1 (by rfl) ⟨1698614, by rfl⟩ : syracuseStep 2264819 = 3397229) B3397229
theorem B6039517 : Blo 2173435 6039517 := bstep (se 3 (by rfl) ⟨1132409, by rfl⟩ : syracuseStep 6039517 = 2264819) B2264819
theorem B8052689 : Blo 2173435 8052689 := bstep (se 2 (by rfl) ⟨3019758, by rfl⟩ : syracuseStep 8052689 = 6039517) B6039517
theorem B5368459 : Blo 2173435 5368459 := bstep (se 1 (by rfl) ⟨4026344, by rfl⟩ : syracuseStep 5368459 = 8052689) B8052689
theorem B7157945 : Blo 2173435 7157945 := bstep (se 2 (by rfl) ⟨2684229, by rfl⟩ : syracuseStep 7157945 = 5368459) B5368459
theorem B4771963 : Blo 2173435 4771963 := bstep (se 1 (by rfl) ⟨3578972, by rfl⟩ : syracuseStep 4771963 = 7157945) B7157945
theorem B25450469 : Blo 2173435 25450469 := bstep (se 4 (by rfl) ⟨2385981, by rfl⟩ : syracuseStep 25450469 = 4771963) B4771963
theorem B16966979 : Blo 2173435 16966979 := bstep (se 1 (by rfl) ⟨12725234, by rfl⟩ : syracuseStep 16966979 = 25450469) B25450469
theorem B11311319 : Blo 2173435 11311319 := bstep (se 1 (by rfl) ⟨8483489, by rfl⟩ : syracuseStep 11311319 = 16966979) B16966979
theorem B7540879 : Blo 2173435 7540879 := bstep (se 1 (by rfl) ⟨5655659, by rfl⟩ : syracuseStep 7540879 = 11311319) B11311319
theorem B10054505 : Blo 2173435 10054505 := bstep (se 2 (by rfl) ⟨3770439, by rfl⟩ : syracuseStep 10054505 = 7540879) B7540879
theorem B6703003 : Blo 2173435 6703003 := bstep (se 1 (by rfl) ⟨5027252, by rfl⟩ : syracuseStep 6703003 = 10054505) B10054505
theorem B35749349 : Blo 2173435 35749349 := bstep (se 4 (by rfl) ⟨3351501, by rfl⟩ : syracuseStep 35749349 = 6703003) B6703003
theorem B23832899 : Blo 2173435 23832899 := bstep (se 1 (by rfl) ⟨17874674, by rfl⟩ : syracuseStep 23832899 = 35749349) B35749349
theorem B15888599 : Blo 2173435 15888599 := bstep (se 1 (by rfl) ⟨11916449, by rfl⟩ : syracuseStep 15888599 = 23832899) B23832899
theorem B10592399 : Blo 2173435 10592399 := bstep (se 1 (by rfl) ⟨7944299, by rfl⟩ : syracuseStep 10592399 = 15888599) B15888599
theorem B7061599 : Blo 2173435 7061599 := bstep (se 1 (by rfl) ⟨5296199, by rfl⟩ : syracuseStep 7061599 = 10592399) B10592399
theorem B37661861 : Blo 2173435 37661861 := bstep (se 4 (by rfl) ⟨3530799, by rfl⟩ : syracuseStep 37661861 = 7061599) B7061599
theorem B25107907 : Blo 2173435 25107907 := bstep (se 1 (by rfl) ⟨18830930, by rfl⟩ : syracuseStep 25107907 = 37661861) B37661861
theorem B33477209 : Blo 2173435 33477209 := bstep (se 2 (by rfl) ⟨12553953, by rfl⟩ : syracuseStep 33477209 = 25107907) B25107907
theorem B22318139 : Blo 2173435 22318139 := bstep (se 1 (by rfl) ⟨16738604, by rfl⟩ : syracuseStep 22318139 = 33477209) B33477209
theorem B59515037 : Blo 2173435 59515037 := bstep (se 3 (by rfl) ⟨11159069, by rfl⟩ : syracuseStep 59515037 = 22318139) B22318139
theorem B39676691 : Blo 2173435 39676691 := bstep (se 1 (by rfl) ⟨29757518, by rfl⟩ : syracuseStep 39676691 = 59515037) B59515037
theorem B26451127 : Blo 2173435 26451127 := bstep (se 1 (by rfl) ⟨19838345, by rfl⟩ : syracuseStep 26451127 = 39676691) B39676691
theorem B141072677 : Blo 2173435 141072677 := bstep (se 4 (by rfl) ⟨13225563, by rfl⟩ : syracuseStep 141072677 = 26451127) B26451127
theorem B94048451 : Blo 2173435 94048451 := bstep (se 1 (by rfl) ⟨70536338, by rfl⟩ : syracuseStep 94048451 = 141072677) B141072677
theorem B62698967 : Blo 2173435 62698967 := bstep (se 1 (by rfl) ⟨47024225, by rfl⟩ : syracuseStep 62698967 = 94048451) B94048451
theorem B41799311 : Blo 2173435 41799311 := bstep (se 1 (by rfl) ⟨31349483, by rfl⟩ : syracuseStep 41799311 = 62698967) B62698967
theorem B27866207 : Blo 2173435 27866207 := bstep (se 1 (by rfl) ⟨20899655, by rfl⟩ : syracuseStep 27866207 = 41799311) B41799311
theorem B18577471 : Blo 2173435 18577471 := bstep (se 1 (by rfl) ⟨13933103, by rfl⟩ : syracuseStep 18577471 = 27866207) B27866207
theorem B24769961 : Blo 2173435 24769961 := bstep (se 2 (by rfl) ⟨9288735, by rfl⟩ : syracuseStep 24769961 = 18577471) B18577471
theorem B16513307 : Blo 2173435 16513307 := bstep (se 1 (by rfl) ⟨12384980, by rfl⟩ : syracuseStep 16513307 = 24769961) B24769961
theorem B11008871 : Blo 2173435 11008871 := bstep (se 1 (by rfl) ⟨8256653, by rfl⟩ : syracuseStep 11008871 = 16513307) B16513307
theorem B7339247 : Blo 2173435 7339247 := bstep (se 1 (by rfl) ⟨5504435, by rfl⟩ : syracuseStep 7339247 = 11008871) B11008871
theorem B4892831 : Blo 2173435 4892831 := bstep (se 1 (by rfl) ⟨3669623, by rfl⟩ : syracuseStep 4892831 = 7339247) B7339247
theorem B3261887 : Blo 2173435 3261887 := bstep (se 1 (by rfl) ⟨2446415, by rfl⟩ : syracuseStep 3261887 = 4892831) B4892831
theorem B2174591 : Blo 2173435 2174591 := bstep (se 1 (by rfl) ⟨1630943, by rfl⟩ : syracuseStep 2174591 = 3261887) B3261887
theorem B3261893 : Blo 2173435 3261893 := bbase (se 4 (by rfl) ⟨305802, by rfl⟩ : syracuseStep 3261893 = 611605) (by norm_num)
theorem B2174595 : Blo 2173435 2174595 := bstep (se 1 (by rfl) ⟨1630946, by rfl⟩ : syracuseStep 2174595 = 3261893) B3261893
theorem B3669637 : Blo 2173435 3669637 := bbase (se 4 (by rfl) ⟨344028, by rfl⟩ : syracuseStep 3669637 = 688057) (by norm_num)
theorem B4892849 : Blo 2173435 4892849 := bstep (se 2 (by rfl) ⟨1834818, by rfl⟩ : syracuseStep 4892849 = 3669637) B3669637
theorem B3261899 : Blo 2173435 3261899 := bstep (se 1 (by rfl) ⟨2446424, by rfl⟩ : syracuseStep 3261899 = 4892849) B4892849
theorem B2174599 : Blo 2173435 2174599 := bstep (se 1 (by rfl) ⟨1630949, by rfl⟩ : syracuseStep 2174599 = 3261899) B3261899
theorem B2446429 : Blo 2173435 2446429 := bbase (se 3 (by rfl) ⟨458705, by rfl⟩ : syracuseStep 2446429 = 917411) (by norm_num)
theorem B3261905 : Blo 2173435 3261905 := bstep (se 2 (by rfl) ⟨1223214, by rfl⟩ : syracuseStep 3261905 = 2446429) B2446429
theorem B2174603 : Blo 2173435 2174603 := bstep (se 1 (by rfl) ⟨1630952, by rfl⟩ : syracuseStep 2174603 = 3261905) B3261905
theorem B7339301 : Blo 2173435 7339301 := bbase (se 4 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 7339301 = 1376119) (by norm_num)
theorem B4892867 : Blo 2173435 4892867 := bstep (se 1 (by rfl) ⟨3669650, by rfl⟩ : syracuseStep 4892867 = 7339301) B7339301
theorem B3261911 : Blo 2173435 3261911 := bstep (se 1 (by rfl) ⟨2446433, by rfl⟩ : syracuseStep 3261911 = 4892867) B4892867
theorem B2174607 : Blo 2173435 2174607 := bstep (se 1 (by rfl) ⟨1630955, by rfl⟩ : syracuseStep 2174607 = 3261911) B3261911
theorem B3261917 : Blo 2173435 3261917 := bbase (se 3 (by rfl) ⟨611609, by rfl⟩ : syracuseStep 3261917 = 1223219) (by norm_num)
theorem B2174611 : Blo 2173435 2174611 := bstep (se 1 (by rfl) ⟨1630958, by rfl⟩ : syracuseStep 2174611 = 3261917) B3261917
theorem B4892885 : Blo 2173435 4892885 := bbase (se 7 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 4892885 = 114677) (by norm_num)
theorem B3261923 : Blo 2173435 3261923 := bstep (se 1 (by rfl) ⟨2446442, by rfl⟩ : syracuseStep 3261923 = 4892885) B4892885
theorem B2174615 : Blo 2173435 2174615 := bstep (se 1 (by rfl) ⟨1630961, by rfl⟩ : syracuseStep 2174615 = 3261923) B3261923
theorem B2939053 : Blo 2173435 2939053 := bbase (se 3 (by rfl) ⟨551072, by rfl⟩ : syracuseStep 2939053 = 1102145) (by norm_num)
theorem B3918737 : Blo 2173435 3918737 := bstep (se 2 (by rfl) ⟨1469526, by rfl⟩ : syracuseStep 3918737 = 2939053) B2939053
theorem B10449965 : Blo 2173435 10449965 := bstep (se 3 (by rfl) ⟨1959368, by rfl⟩ : syracuseStep 10449965 = 3918737) B3918737
theorem B6966643 : Blo 2173435 6966643 := bstep (se 1 (by rfl) ⟨5224982, by rfl⟩ : syracuseStep 6966643 = 10449965) B10449965
theorem B9288857 : Blo 2173435 9288857 := bstep (se 2 (by rfl) ⟨3483321, by rfl⟩ : syracuseStep 9288857 = 6966643) B6966643
theorem B6192571 : Blo 2173435 6192571 := bstep (se 1 (by rfl) ⟨4644428, by rfl⟩ : syracuseStep 6192571 = 9288857) B9288857
theorem B8256761 : Blo 2173435 8256761 := bstep (se 2 (by rfl) ⟨3096285, by rfl⟩ : syracuseStep 8256761 = 6192571) B6192571
theorem B5504507 : Blo 2173435 5504507 := bstep (se 1 (by rfl) ⟨4128380, by rfl⟩ : syracuseStep 5504507 = 8256761) B8256761
theorem B3669671 : Blo 2173435 3669671 := bstep (se 1 (by rfl) ⟨2752253, by rfl⟩ : syracuseStep 3669671 = 5504507) B5504507
theorem B2446447 : Blo 2173435 2446447 := bstep (se 1 (by rfl) ⟨1834835, by rfl⟩ : syracuseStep 2446447 = 3669671) B3669671
theorem B3261929 : Blo 2173435 3261929 := bstep (se 2 (by rfl) ⟨1223223, by rfl⟩ : syracuseStep 3261929 = 2446447) B2446447
theorem B2174619 : Blo 2173435 2174619 := bstep (se 1 (by rfl) ⟨1630964, by rfl⟩ : syracuseStep 2174619 = 3261929) B3261929
theorem B2789809 : Blo 2173435 2789809 := bbase (se 2 (by rfl) ⟨1046178, by rfl⟩ : syracuseStep 2789809 = 2092357) (by norm_num)
theorem B14878981 : Blo 2173435 14878981 := bstep (se 4 (by rfl) ⟨1394904, by rfl⟩ : syracuseStep 14878981 = 2789809) B2789809
theorem B19838641 : Blo 2173435 19838641 := bstep (se 2 (by rfl) ⟨7439490, by rfl⟩ : syracuseStep 19838641 = 14878981) B14878981
theorem B26451521 : Blo 2173435 26451521 := bstep (se 2 (by rfl) ⟨9919320, by rfl⟩ : syracuseStep 26451521 = 19838641) B19838641
theorem B17634347 : Blo 2173435 17634347 := bstep (se 1 (by rfl) ⟨13225760, by rfl⟩ : syracuseStep 17634347 = 26451521) B26451521
theorem B11756231 : Blo 2173435 11756231 := bstep (se 1 (by rfl) ⟨8817173, by rfl⟩ : syracuseStep 11756231 = 17634347) B17634347
theorem B7837487 : Blo 2173435 7837487 := bstep (se 1 (by rfl) ⟨5878115, by rfl⟩ : syracuseStep 7837487 = 11756231) B11756231
theorem B5224991 : Blo 2173435 5224991 := bstep (se 1 (by rfl) ⟨3918743, by rfl⟩ : syracuseStep 5224991 = 7837487) B7837487
theorem B13933309 : Blo 2173435 13933309 := bstep (se 3 (by rfl) ⟨2612495, by rfl⟩ : syracuseStep 13933309 = 5224991) B5224991
theorem B18577745 : Blo 2173435 18577745 := bstep (se 2 (by rfl) ⟨6966654, by rfl⟩ : syracuseStep 18577745 = 13933309) B13933309
theorem B12385163 : Blo 2173435 12385163 := bstep (se 1 (by rfl) ⟨9288872, by rfl⟩ : syracuseStep 12385163 = 18577745) B18577745
theorem B8256775 : Blo 2173435 8256775 := bstep (se 1 (by rfl) ⟨6192581, by rfl⟩ : syracuseStep 8256775 = 12385163) B12385163
theorem B11009033 : Blo 2173435 11009033 := bstep (se 2 (by rfl) ⟨4128387, by rfl⟩ : syracuseStep 11009033 = 8256775) B8256775
theorem B7339355 : Blo 2173435 7339355 := bstep (se 1 (by rfl) ⟨5504516, by rfl⟩ : syracuseStep 7339355 = 11009033) B11009033
theorem B4892903 : Blo 2173435 4892903 := bstep (se 1 (by rfl) ⟨3669677, by rfl⟩ : syracuseStep 4892903 = 7339355) B7339355
theorem B3261935 : Blo 2173435 3261935 := bstep (se 1 (by rfl) ⟨2446451, by rfl⟩ : syracuseStep 3261935 = 4892903) B4892903
theorem B2174623 : Blo 2173435 2174623 := bstep (se 1 (by rfl) ⟨1630967, by rfl⟩ : syracuseStep 2174623 = 3261935) B3261935
theorem B3261941 : Blo 2173435 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B2174627 : Blo 2173435 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B3483341 : Blo 2173435 3483341 := bbase (se 3 (by rfl) ⟨653126, by rfl⟩ : syracuseStep 3483341 = 1306253) (by norm_num)
theorem B2322227 : Blo 2173435 2322227 := bstep (se 1 (by rfl) ⟨1741670, by rfl⟩ : syracuseStep 2322227 = 3483341) B3483341
theorem B6192605 : Blo 2173435 6192605 := bstep (se 3 (by rfl) ⟨1161113, by rfl⟩ : syracuseStep 6192605 = 2322227) B2322227
theorem B4128403 : Blo 2173435 4128403 := bstep (se 1 (by rfl) ⟨3096302, by rfl⟩ : syracuseStep 4128403 = 6192605) B6192605
theorem B5504537 : Blo 2173435 5504537 := bstep (se 2 (by rfl) ⟨2064201, by rfl⟩ : syracuseStep 5504537 = 4128403) B4128403
theorem B3669691 : Blo 2173435 3669691 := bstep (se 1 (by rfl) ⟨2752268, by rfl⟩ : syracuseStep 3669691 = 5504537) B5504537
theorem B4892921 : Blo 2173435 4892921 := bstep (se 2 (by rfl) ⟨1834845, by rfl⟩ : syracuseStep 4892921 = 3669691) B3669691
theorem B3261947 : Blo 2173435 3261947 := bstep (se 1 (by rfl) ⟨2446460, by rfl⟩ : syracuseStep 3261947 = 4892921) B4892921
theorem B2174631 : Blo 2173435 2174631 := bstep (se 1 (by rfl) ⟨1630973, by rfl⟩ : syracuseStep 2174631 = 3261947) B3261947
theorem B2446465 : Blo 2173435 2446465 := bbase (se 2 (by rfl) ⟨917424, by rfl⟩ : syracuseStep 2446465 = 1834849) (by norm_num)
theorem B3261953 : Blo 2173435 3261953 := bstep (se 2 (by rfl) ⟨1223232, by rfl⟩ : syracuseStep 3261953 = 2446465) B2446465
theorem B2174635 : Blo 2173435 2174635 := bstep (se 1 (by rfl) ⟨1630976, by rfl⟩ : syracuseStep 2174635 = 3261953) B3261953
theorem B5504557 : Blo 2173435 5504557 := bbase (se 3 (by rfl) ⟨1032104, by rfl⟩ : syracuseStep 5504557 = 2064209) (by norm_num)
theorem B7339409 : Blo 2173435 7339409 := bstep (se 2 (by rfl) ⟨2752278, by rfl⟩ : syracuseStep 7339409 = 5504557) B5504557
theorem B4892939 : Blo 2173435 4892939 := bstep (se 1 (by rfl) ⟨3669704, by rfl⟩ : syracuseStep 4892939 = 7339409) B7339409
theorem B3261959 : Blo 2173435 3261959 := bstep (se 1 (by rfl) ⟨2446469, by rfl⟩ : syracuseStep 3261959 = 4892939) B4892939
theorem B2174639 : Blo 2173435 2174639 := bstep (se 1 (by rfl) ⟨1630979, by rfl⟩ : syracuseStep 2174639 = 3261959) B3261959
theorem B3261965 : Blo 2173435 3261965 := bbase (se 3 (by rfl) ⟨611618, by rfl⟩ : syracuseStep 3261965 = 1223237) (by norm_num)
theorem B2174643 : Blo 2173435 2174643 := bstep (se 1 (by rfl) ⟨1630982, by rfl⟩ : syracuseStep 2174643 = 3261965) B3261965
theorem B4892957 : Blo 2173435 4892957 := bbase (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) (by norm_num)
theorem B3261971 : Blo 2173435 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B2174647 : Blo 2173435 2174647 := bstep (se 1 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 2174647 = 3261971) B3261971
theorem B3669725 : Blo 2173435 3669725 := bbase (se 3 (by rfl) ⟨688073, by rfl⟩ : syracuseStep 3669725 = 1376147) (by norm_num)
theorem B2446483 : Blo 2173435 2446483 := bstep (se 1 (by rfl) ⟨1834862, by rfl⟩ : syracuseStep 2446483 = 3669725) B3669725
theorem B3261977 : Blo 2173435 3261977 := bstep (se 2 (by rfl) ⟨1223241, by rfl⟩ : syracuseStep 3261977 = 2446483) B2446483
theorem B2174651 : Blo 2173435 2174651 := bstep (se 1 (by rfl) ⟨1630988, by rfl⟩ : syracuseStep 2174651 = 3261977) B3261977
theorem B6966757 : Blo 2173435 6966757 := bbase (se 4 (by rfl) ⟨653133, by rfl⟩ : syracuseStep 6966757 = 1306267) (by norm_num)
theorem B9289009 : Blo 2173435 9289009 := bstep (se 2 (by rfl) ⟨3483378, by rfl⟩ : syracuseStep 9289009 = 6966757) B6966757
theorem B12385345 : Blo 2173435 12385345 := bstep (se 2 (by rfl) ⟨4644504, by rfl⟩ : syracuseStep 12385345 = 9289009) B9289009
theorem B16513793 : Blo 2173435 16513793 := bstep (se 2 (by rfl) ⟨6192672, by rfl⟩ : syracuseStep 16513793 = 12385345) B12385345
theorem B11009195 : Blo 2173435 11009195 := bstep (se 1 (by rfl) ⟨8256896, by rfl⟩ : syracuseStep 11009195 = 16513793) B16513793
theorem B7339463 : Blo 2173435 7339463 := bstep (se 1 (by rfl) ⟨5504597, by rfl⟩ : syracuseStep 7339463 = 11009195) B11009195
theorem B4892975 : Blo 2173435 4892975 := bstep (se 1 (by rfl) ⟨3669731, by rfl⟩ : syracuseStep 4892975 = 7339463) B7339463
theorem B3261983 : Blo 2173435 3261983 := bstep (se 1 (by rfl) ⟨2446487, by rfl⟩ : syracuseStep 3261983 = 4892975) B4892975
theorem B2174655 : Blo 2173435 2174655 := bstep (se 1 (by rfl) ⟨1630991, by rfl⟩ : syracuseStep 2174655 = 3261983) B3261983
theorem B3261989 : Blo 2173435 3261989 := bbase (se 4 (by rfl) ⟨305811, by rfl⟩ : syracuseStep 3261989 = 611623) (by norm_num)
theorem B2174659 : Blo 2173435 2174659 := bstep (se 1 (by rfl) ⟨1630994, by rfl⟩ : syracuseStep 2174659 = 3261989) B3261989
theorem B2752309 : Blo 2173435 2752309 := bbase (se 5 (by rfl) ⟨129014, by rfl⟩ : syracuseStep 2752309 = 258029) (by norm_num)
theorem B3669745 : Blo 2173435 3669745 := bstep (se 2 (by rfl) ⟨1376154, by rfl⟩ : syracuseStep 3669745 = 2752309) B2752309
theorem B4892993 : Blo 2173435 4892993 := bstep (se 2 (by rfl) ⟨1834872, by rfl⟩ : syracuseStep 4892993 = 3669745) B3669745
theorem B3261995 : Blo 2173435 3261995 := bstep (se 1 (by rfl) ⟨2446496, by rfl⟩ : syracuseStep 3261995 = 4892993) B4892993
theorem B2174663 : Blo 2173435 2174663 := bstep (se 1 (by rfl) ⟨1630997, by rfl⟩ : syracuseStep 2174663 = 3261995) B3261995
theorem B2446501 : Blo 2173435 2446501 := bbase (se 4 (by rfl) ⟨229359, by rfl⟩ : syracuseStep 2446501 = 458719) (by norm_num)
theorem B3262001 : Blo 2173435 3262001 := bstep (se 2 (by rfl) ⟨1223250, by rfl⟩ : syracuseStep 3262001 = 2446501) B2446501
theorem B2174667 : Blo 2173435 2174667 := bstep (se 1 (by rfl) ⟨1631000, by rfl⟩ : syracuseStep 2174667 = 3262001) B3262001
theorem B4408685 : Blo 2173435 4408685 := bbase (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) (by norm_num)
theorem B2939123 : Blo 2173435 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B7837661 : Blo 2173435 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B20900429 : Blo 2173435 20900429 := bstep (se 3 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 20900429 = 7837661) B7837661
theorem B13933619 : Blo 2173435 13933619 := bstep (se 1 (by rfl) ⟨10450214, by rfl⟩ : syracuseStep 13933619 = 20900429) B20900429
theorem B9289079 : Blo 2173435 9289079 := bstep (se 1 (by rfl) ⟨6966809, by rfl⟩ : syracuseStep 9289079 = 13933619) B13933619
theorem B6192719 : Blo 2173435 6192719 := bstep (se 1 (by rfl) ⟨4644539, by rfl⟩ : syracuseStep 6192719 = 9289079) B9289079
theorem B4128479 : Blo 2173435 4128479 := bstep (se 1 (by rfl) ⟨3096359, by rfl⟩ : syracuseStep 4128479 = 6192719) B6192719
theorem B2752319 : Blo 2173435 2752319 := bstep (se 1 (by rfl) ⟨2064239, by rfl⟩ : syracuseStep 2752319 = 4128479) B4128479
theorem B7339517 : Blo 2173435 7339517 := bstep (se 3 (by rfl) ⟨1376159, by rfl⟩ : syracuseStep 7339517 = 2752319) B2752319
theorem B4893011 : Blo 2173435 4893011 := bstep (se 1 (by rfl) ⟨3669758, by rfl⟩ : syracuseStep 4893011 = 7339517) B7339517
theorem B3262007 : Blo 2173435 3262007 := bstep (se 1 (by rfl) ⟨2446505, by rfl⟩ : syracuseStep 3262007 = 4893011) B4893011
theorem B2174671 : Blo 2173435 2174671 := bstep (se 1 (by rfl) ⟨1631003, by rfl⟩ : syracuseStep 2174671 = 3262007) B3262007
theorem B3262013 : Blo 2173435 3262013 := bbase (se 3 (by rfl) ⟨611627, by rfl⟩ : syracuseStep 3262013 = 1223255) (by norm_num)
theorem B2174675 : Blo 2173435 2174675 := bstep (se 1 (by rfl) ⟨1631006, by rfl⟩ : syracuseStep 2174675 = 3262013) B3262013
theorem B4893029 : Blo 2173435 4893029 := bbase (se 4 (by rfl) ⟨458721, by rfl⟩ : syracuseStep 4893029 = 917443) (by norm_num)
theorem B3262019 : Blo 2173435 3262019 := bstep (se 1 (by rfl) ⟨2446514, by rfl⟩ : syracuseStep 3262019 = 4893029) B4893029
theorem B2174679 : Blo 2173435 2174679 := bstep (se 1 (by rfl) ⟨1631009, by rfl⟩ : syracuseStep 2174679 = 3262019) B3262019
theorem B5504669 : Blo 2173435 5504669 := bbase (se 3 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 5504669 = 2064251) (by norm_num)
theorem B3669779 : Blo 2173435 3669779 := bstep (se 1 (by rfl) ⟨2752334, by rfl⟩ : syracuseStep 3669779 = 5504669) B5504669
theorem B2446519 : Blo 2173435 2446519 := bstep (se 1 (by rfl) ⟨1834889, by rfl⟩ : syracuseStep 2446519 = 3669779) B3669779
theorem B3262025 : Blo 2173435 3262025 := bstep (se 2 (by rfl) ⟨1223259, by rfl⟩ : syracuseStep 3262025 = 2446519) B2446519
theorem B2174683 : Blo 2173435 2174683 := bstep (se 1 (by rfl) ⟨1631012, by rfl⟩ : syracuseStep 2174683 = 3262025) B3262025
theorem B4128509 : Blo 2173435 4128509 := bbase (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) (by norm_num)
theorem B11009357 : Blo 2173435 11009357 := bstep (se 3 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 11009357 = 4128509) B4128509
theorem B7339571 : Blo 2173435 7339571 := bstep (se 1 (by rfl) ⟨5504678, by rfl⟩ : syracuseStep 7339571 = 11009357) B11009357
theorem B4893047 : Blo 2173435 4893047 := bstep (se 1 (by rfl) ⟨3669785, by rfl⟩ : syracuseStep 4893047 = 7339571) B7339571
theorem B3262031 : Blo 2173435 3262031 := bstep (se 1 (by rfl) ⟨2446523, by rfl⟩ : syracuseStep 3262031 = 4893047) B4893047
theorem B2174687 : Blo 2173435 2174687 := bstep (se 1 (by rfl) ⟨1631015, by rfl⟩ : syracuseStep 2174687 = 3262031) B3262031
theorem B3262037 : Blo 2173435 3262037 := bbase (se 8 (by rfl) ⟨19113, by rfl⟩ : syracuseStep 3262037 = 38227) (by norm_num)
theorem B2174691 : Blo 2173435 2174691 := bstep (se 1 (by rfl) ⟨1631018, by rfl⟩ : syracuseStep 2174691 = 3262037) B3262037
theorem B5225165 : Blo 2173435 5225165 := bbase (se 3 (by rfl) ⟨979718, by rfl⟩ : syracuseStep 5225165 = 1959437) (by norm_num)
theorem B3483443 : Blo 2173435 3483443 := bstep (se 1 (by rfl) ⟨2612582, by rfl⟩ : syracuseStep 3483443 = 5225165) B5225165
theorem B9289181 : Blo 2173435 9289181 := bstep (se 3 (by rfl) ⟨1741721, by rfl⟩ : syracuseStep 9289181 = 3483443) B3483443
theorem B6192787 : Blo 2173435 6192787 := bstep (se 1 (by rfl) ⟨4644590, by rfl⟩ : syracuseStep 6192787 = 9289181) B9289181
theorem B8257049 : Blo 2173435 8257049 := bstep (se 2 (by rfl) ⟨3096393, by rfl⟩ : syracuseStep 8257049 = 6192787) B6192787
theorem B5504699 : Blo 2173435 5504699 := bstep (se 1 (by rfl) ⟨4128524, by rfl⟩ : syracuseStep 5504699 = 8257049) B8257049
theorem B3669799 : Blo 2173435 3669799 := bstep (se 1 (by rfl) ⟨2752349, by rfl⟩ : syracuseStep 3669799 = 5504699) B5504699
theorem B4893065 : Blo 2173435 4893065 := bstep (se 2 (by rfl) ⟨1834899, by rfl⟩ : syracuseStep 4893065 = 3669799) B3669799
theorem B3262043 : Blo 2173435 3262043 := bstep (se 1 (by rfl) ⟨2446532, by rfl⟩ : syracuseStep 3262043 = 4893065) B4893065
theorem B2174695 : Blo 2173435 2174695 := bstep (se 1 (by rfl) ⟨1631021, by rfl⟩ : syracuseStep 2174695 = 3262043) B3262043
theorem B2446537 : Blo 2173435 2446537 := bbase (se 2 (by rfl) ⟨917451, by rfl⟩ : syracuseStep 2446537 = 1834903) (by norm_num)
theorem B3262049 : Blo 2173435 3262049 := bstep (se 2 (by rfl) ⟨1223268, by rfl⟩ : syracuseStep 3262049 = 2446537) B2446537
theorem B2174699 : Blo 2173435 2174699 := bstep (se 1 (by rfl) ⟨1631024, by rfl⟩ : syracuseStep 2174699 = 3262049) B3262049
theorem B33935701 : Blo 2173435 33935701 := bbase (se 10 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 33935701 = 99421) (by norm_num)
theorem B45247601 : Blo 2173435 45247601 := bstep (se 2 (by rfl) ⟨16967850, by rfl⟩ : syracuseStep 45247601 = 33935701) B33935701
theorem B30165067 : Blo 2173435 30165067 := bstep (se 1 (by rfl) ⟨22623800, by rfl⟩ : syracuseStep 30165067 = 45247601) B45247601
theorem B40220089 : Blo 2173435 40220089 := bstep (se 2 (by rfl) ⟨15082533, by rfl⟩ : syracuseStep 40220089 = 30165067) B30165067
theorem B858028565 : Blo 2173435 858028565 := bstep (se 6 (by rfl) ⟨20110044, by rfl⟩ : syracuseStep 858028565 = 40220089) B40220089
theorem B572019043 : Blo 2173435 572019043 := bstep (se 1 (by rfl) ⟨429014282, by rfl⟩ : syracuseStep 572019043 = 858028565) B858028565
theorem B762692057 : Blo 2173435 762692057 := bstep (se 2 (by rfl) ⟨286009521, by rfl⟩ : syracuseStep 762692057 = 572019043) B572019043
theorem B508461371 : Blo 2173435 508461371 := bstep (se 1 (by rfl) ⟨381346028, by rfl⟩ : syracuseStep 508461371 = 762692057) B762692057
theorem B338974247 : Blo 2173435 338974247 := bstep (se 1 (by rfl) ⟨254230685, by rfl⟩ : syracuseStep 338974247 = 508461371) B508461371
theorem B225982831 : Blo 2173435 225982831 := bstep (se 1 (by rfl) ⟨169487123, by rfl⟩ : syracuseStep 225982831 = 338974247) B338974247
theorem B301310441 : Blo 2173435 301310441 := bstep (se 2 (by rfl) ⟨112991415, by rfl⟩ : syracuseStep 301310441 = 225982831) B225982831
theorem B200873627 : Blo 2173435 200873627 := bstep (se 1 (by rfl) ⟨150655220, by rfl⟩ : syracuseStep 200873627 = 301310441) B301310441
theorem B133915751 : Blo 2173435 133915751 := bstep (se 1 (by rfl) ⟨100436813, by rfl⟩ : syracuseStep 133915751 = 200873627) B200873627
theorem B89277167 : Blo 2173435 89277167 := bstep (se 1 (by rfl) ⟨66957875, by rfl⟩ : syracuseStep 89277167 = 133915751) B133915751
theorem B59518111 : Blo 2173435 59518111 := bstep (se 1 (by rfl) ⟨44638583, by rfl⟩ : syracuseStep 59518111 = 89277167) B89277167
theorem B79357481 : Blo 2173435 79357481 := bstep (se 2 (by rfl) ⟨29759055, by rfl⟩ : syracuseStep 79357481 = 59518111) B59518111
theorem B52904987 : Blo 2173435 52904987 := bstep (se 1 (by rfl) ⟨39678740, by rfl⟩ : syracuseStep 52904987 = 79357481) B79357481
theorem B35269991 : Blo 2173435 35269991 := bstep (se 1 (by rfl) ⟨26452493, by rfl⟩ : syracuseStep 35269991 = 52904987) B52904987
theorem B23513327 : Blo 2173435 23513327 := bstep (se 1 (by rfl) ⟨17634995, by rfl⟩ : syracuseStep 23513327 = 35269991) B35269991
theorem B15675551 : Blo 2173435 15675551 := bstep (se 1 (by rfl) ⟨11756663, by rfl⟩ : syracuseStep 15675551 = 23513327) B23513327
theorem B10450367 : Blo 2173435 10450367 := bstep (se 1 (by rfl) ⟨7837775, by rfl⟩ : syracuseStep 10450367 = 15675551) B15675551
theorem B6966911 : Blo 2173435 6966911 := bstep (se 1 (by rfl) ⟨5225183, by rfl⟩ : syracuseStep 6966911 = 10450367) B10450367
theorem B18578429 : Blo 2173435 18578429 := bstep (se 3 (by rfl) ⟨3483455, by rfl⟩ : syracuseStep 18578429 = 6966911) B6966911
theorem B12385619 : Blo 2173435 12385619 := bstep (se 1 (by rfl) ⟨9289214, by rfl⟩ : syracuseStep 12385619 = 18578429) B18578429
theorem B8257079 : Blo 2173435 8257079 := bstep (se 1 (by rfl) ⟨6192809, by rfl⟩ : syracuseStep 8257079 = 12385619) B12385619
theorem B5504719 : Blo 2173435 5504719 := bstep (se 1 (by rfl) ⟨4128539, by rfl⟩ : syracuseStep 5504719 = 8257079) B8257079
theorem B7339625 : Blo 2173435 7339625 := bstep (se 2 (by rfl) ⟨2752359, by rfl⟩ : syracuseStep 7339625 = 5504719) B5504719
theorem B4893083 : Blo 2173435 4893083 := bstep (se 1 (by rfl) ⟨3669812, by rfl⟩ : syracuseStep 4893083 = 7339625) B7339625
theorem B3262055 : Blo 2173435 3262055 := bstep (se 1 (by rfl) ⟨2446541, by rfl⟩ : syracuseStep 3262055 = 4893083) B4893083
theorem B2174703 : Blo 2173435 2174703 := bstep (se 1 (by rfl) ⟨1631027, by rfl⟩ : syracuseStep 2174703 = 3262055) B3262055
theorem B3262061 : Blo 2173435 3262061 := bbase (se 3 (by rfl) ⟨611636, by rfl⟩ : syracuseStep 3262061 = 1223273) (by norm_num)
theorem B2174707 : Blo 2173435 2174707 := bstep (se 1 (by rfl) ⟨1631030, by rfl⟩ : syracuseStep 2174707 = 3262061) B3262061
theorem B4893101 : Blo 2173435 4893101 := bbase (se 3 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 4893101 = 1834913) (by norm_num)
theorem B3262067 : Blo 2173435 3262067 := bstep (se 1 (by rfl) ⟨2446550, by rfl⟩ : syracuseStep 3262067 = 4893101) B4893101
theorem B2174711 : Blo 2173435 2174711 := bstep (se 1 (by rfl) ⟨1631033, by rfl⟩ : syracuseStep 2174711 = 3262067) B3262067
theorem B2322317 : Blo 2173435 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B6192845 : Blo 2173435 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B4128563 : Blo 2173435 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B2752375 : Blo 2173435 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B3669833 : Blo 2173435 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B2446555 : Blo 2173435 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B3262073 : Blo 2173435 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B2174715 : Blo 2173435 2174715 := bstep (se 1 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 2174715 = 3262073) B3262073
theorem B3719909 : Blo 2173435 3719909 := bbase (se 4 (by rfl) ⟨348741, by rfl⟩ : syracuseStep 3719909 = 697483) (by norm_num)
theorem B9919757 : Blo 2173435 9919757 := bstep (se 3 (by rfl) ⟨1859954, by rfl⟩ : syracuseStep 9919757 = 3719909) B3719909
theorem B6613171 : Blo 2173435 6613171 := bstep (se 1 (by rfl) ⟨4959878, by rfl⟩ : syracuseStep 6613171 = 9919757) B9919757
theorem B35270245 : Blo 2173435 35270245 := bstep (se 4 (by rfl) ⟨3306585, by rfl⟩ : syracuseStep 35270245 = 6613171) B6613171
theorem B47026993 : Blo 2173435 47026993 := bstep (se 2 (by rfl) ⟨17635122, by rfl⟩ : syracuseStep 47026993 = 35270245) B35270245
theorem B62702657 : Blo 2173435 62702657 := bstep (se 2 (by rfl) ⟨23513496, by rfl⟩ : syracuseStep 62702657 = 47026993) B47026993
theorem B41801771 : Blo 2173435 41801771 := bstep (se 1 (by rfl) ⟨31351328, by rfl⟩ : syracuseStep 41801771 = 62702657) B62702657
theorem B27867847 : Blo 2173435 27867847 := bstep (se 1 (by rfl) ⟨20900885, by rfl⟩ : syracuseStep 27867847 = 41801771) B41801771
theorem B37157129 : Blo 2173435 37157129 := bstep (se 2 (by rfl) ⟨13933923, by rfl⟩ : syracuseStep 37157129 = 27867847) B27867847
theorem B24771419 : Blo 2173435 24771419 := bstep (se 1 (by rfl) ⟨18578564, by rfl⟩ : syracuseStep 24771419 = 37157129) B37157129
theorem B16514279 : Blo 2173435 16514279 := bstep (se 1 (by rfl) ⟨12385709, by rfl⟩ : syracuseStep 16514279 = 24771419) B24771419
theorem B11009519 : Blo 2173435 11009519 := bstep (se 1 (by rfl) ⟨8257139, by rfl⟩ : syracuseStep 11009519 = 16514279) B16514279
theorem B7339679 : Blo 2173435 7339679 := bstep (se 1 (by rfl) ⟨5504759, by rfl⟩ : syracuseStep 7339679 = 11009519) B11009519
theorem B4893119 : Blo 2173435 4893119 := bstep (se 1 (by rfl) ⟨3669839, by rfl⟩ : syracuseStep 4893119 = 7339679) B7339679
theorem B3262079 : Blo 2173435 3262079 := bstep (se 1 (by rfl) ⟨2446559, by rfl⟩ : syracuseStep 3262079 = 4893119) B4893119
theorem B2174719 : Blo 2173435 2174719 := bstep (se 1 (by rfl) ⟨1631039, by rfl⟩ : syracuseStep 2174719 = 3262079) B3262079
theorem B3262085 : Blo 2173435 3262085 := bbase (se 4 (by rfl) ⟨305820, by rfl⟩ : syracuseStep 3262085 = 611641) (by norm_num)
theorem B2174723 : Blo 2173435 2174723 := bstep (se 1 (by rfl) ⟨1631042, by rfl⟩ : syracuseStep 2174723 = 3262085) B3262085
theorem B3669853 : Blo 2173435 3669853 := bbase (se 3 (by rfl) ⟨688097, by rfl⟩ : syracuseStep 3669853 = 1376195) (by norm_num)
theorem B4893137 : Blo 2173435 4893137 := bstep (se 2 (by rfl) ⟨1834926, by rfl⟩ : syracuseStep 4893137 = 3669853) B3669853
theorem B3262091 : Blo 2173435 3262091 := bstep (se 1 (by rfl) ⟨2446568, by rfl⟩ : syracuseStep 3262091 = 4893137) B4893137
theorem B2174727 : Blo 2173435 2174727 := bstep (se 1 (by rfl) ⟨1631045, by rfl⟩ : syracuseStep 2174727 = 3262091) B3262091
theorem B2446573 : Blo 2173435 2446573 := bbase (se 3 (by rfl) ⟨458732, by rfl⟩ : syracuseStep 2446573 = 917465) (by norm_num)
theorem B3262097 : Blo 2173435 3262097 := bstep (se 2 (by rfl) ⟨1223286, by rfl⟩ : syracuseStep 3262097 = 2446573) B2446573
theorem B2174731 : Blo 2173435 2174731 := bstep (se 1 (by rfl) ⟨1631048, by rfl⟩ : syracuseStep 2174731 = 3262097) B3262097
theorem B7339733 : Blo 2173435 7339733 := bbase (se 7 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 7339733 = 172025) (by norm_num)
theorem B4893155 : Blo 2173435 4893155 := bstep (se 1 (by rfl) ⟨3669866, by rfl⟩ : syracuseStep 4893155 = 7339733) B7339733
theorem B3262103 : Blo 2173435 3262103 := bstep (se 1 (by rfl) ⟨2446577, by rfl⟩ : syracuseStep 3262103 = 4893155) B4893155
theorem B2174735 : Blo 2173435 2174735 := bstep (se 1 (by rfl) ⟨1631051, by rfl⟩ : syracuseStep 2174735 = 3262103) B3262103
theorem B3262109 : Blo 2173435 3262109 := bbase (se 3 (by rfl) ⟨611645, by rfl⟩ : syracuseStep 3262109 = 1223291) (by norm_num)
theorem B2174739 : Blo 2173435 2174739 := bstep (se 1 (by rfl) ⟨1631054, by rfl⟩ : syracuseStep 2174739 = 3262109) B3262109
theorem B4893173 : Blo 2173435 4893173 := bbase (se 5 (by rfl) ⟨229367, by rfl⟩ : syracuseStep 4893173 = 458735) (by norm_num)
theorem B3262115 : Blo 2173435 3262115 := bstep (se 1 (by rfl) ⟨2446586, by rfl⟩ : syracuseStep 3262115 = 4893173) B4893173
theorem B2174743 : Blo 2173435 2174743 := bstep (se 1 (by rfl) ⟨1631057, by rfl⟩ : syracuseStep 2174743 = 3262115) B3262115
theorem B3306629 : Blo 2173435 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B8817677 : Blo 2173435 8817677 := bstep (se 3 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 8817677 = 3306629) B3306629
theorem B5878451 : Blo 2173435 5878451 := bstep (se 1 (by rfl) ⟨4408838, by rfl⟩ : syracuseStep 5878451 = 8817677) B8817677
theorem B15675869 : Blo 2173435 15675869 := bstep (se 3 (by rfl) ⟨2939225, by rfl⟩ : syracuseStep 15675869 = 5878451) B5878451
theorem B41802317 : Blo 2173435 41802317 := bstep (se 3 (by rfl) ⟨7837934, by rfl⟩ : syracuseStep 41802317 = 15675869) B15675869
theorem B27868211 : Blo 2173435 27868211 := bstep (se 1 (by rfl) ⟨20901158, by rfl⟩ : syracuseStep 27868211 = 41802317) B41802317
theorem B18578807 : Blo 2173435 18578807 := bstep (se 1 (by rfl) ⟨13934105, by rfl⟩ : syracuseStep 18578807 = 27868211) B27868211
theorem B12385871 : Blo 2173435 12385871 := bstep (se 1 (by rfl) ⟨9289403, by rfl⟩ : syracuseStep 12385871 = 18578807) B18578807
theorem B8257247 : Blo 2173435 8257247 := bstep (se 1 (by rfl) ⟨6192935, by rfl⟩ : syracuseStep 8257247 = 12385871) B12385871
theorem B5504831 : Blo 2173435 5504831 := bstep (se 1 (by rfl) ⟨4128623, by rfl⟩ : syracuseStep 5504831 = 8257247) B8257247
theorem B3669887 : Blo 2173435 3669887 := bstep (se 1 (by rfl) ⟨2752415, by rfl⟩ : syracuseStep 3669887 = 5504831) B5504831
theorem B2446591 : Blo 2173435 2446591 := bstep (se 1 (by rfl) ⟨1834943, by rfl⟩ : syracuseStep 2446591 = 3669887) B3669887
theorem B3262121 : Blo 2173435 3262121 := bstep (se 2 (by rfl) ⟨1223295, by rfl⟩ : syracuseStep 3262121 = 2446591) B2446591
theorem B2174747 : Blo 2173435 2174747 := bstep (se 1 (by rfl) ⟨1631060, by rfl⟩ : syracuseStep 2174747 = 3262121) B3262121
theorem B3483533 : Blo 2173435 3483533 := bbase (se 3 (by rfl) ⟨653162, by rfl⟩ : syracuseStep 3483533 = 1306325) (by norm_num)
theorem B2322355 : Blo 2173435 2322355 := bstep (se 1 (by rfl) ⟨1741766, by rfl⟩ : syracuseStep 2322355 = 3483533) B3483533
theorem B3096473 : Blo 2173435 3096473 := bstep (se 2 (by rfl) ⟨1161177, by rfl⟩ : syracuseStep 3096473 = 2322355) B2322355
theorem B8257261 : Blo 2173435 8257261 := bstep (se 3 (by rfl) ⟨1548236, by rfl⟩ : syracuseStep 8257261 = 3096473) B3096473
theorem B11009681 : Blo 2173435 11009681 := bstep (se 2 (by rfl) ⟨4128630, by rfl⟩ : syracuseStep 11009681 = 8257261) B8257261
theorem B7339787 : Blo 2173435 7339787 := bstep (se 1 (by rfl) ⟨5504840, by rfl⟩ : syracuseStep 7339787 = 11009681) B11009681
theorem B4893191 : Blo 2173435 4893191 := bstep (se 1 (by rfl) ⟨3669893, by rfl⟩ : syracuseStep 4893191 = 7339787) B7339787
theorem B3262127 : Blo 2173435 3262127 := bstep (se 1 (by rfl) ⟨2446595, by rfl⟩ : syracuseStep 3262127 = 4893191) B4893191
theorem B2174751 : Blo 2173435 2174751 := bstep (se 1 (by rfl) ⟨1631063, by rfl⟩ : syracuseStep 2174751 = 3262127) B3262127
theorem B3262133 : Blo 2173435 3262133 := bbase (se 5 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 3262133 = 305825) (by norm_num)
theorem B2174755 : Blo 2173435 2174755 := bstep (se 1 (by rfl) ⟨1631066, by rfl⟩ : syracuseStep 2174755 = 3262133) B3262133
theorem B5504861 : Blo 2173435 5504861 := bbase (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) (by norm_num)
theorem B3669907 : Blo 2173435 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B4893209 : Blo 2173435 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B3262139 : Blo 2173435 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B2174759 : Blo 2173435 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B2446609 : Blo 2173435 2446609 := bbase (se 2 (by rfl) ⟨917478, by rfl⟩ : syracuseStep 2446609 = 1834957) (by norm_num)
theorem B3262145 : Blo 2173435 3262145 := bstep (se 2 (by rfl) ⟨1223304, by rfl⟩ : syracuseStep 3262145 = 2446609) B2446609
theorem B2174763 : Blo 2173435 2174763 := bstep (se 1 (by rfl) ⟨1631072, by rfl⟩ : syracuseStep 2174763 = 3262145) B3262145
theorem B4128661 : Blo 2173435 4128661 := bbase (se 6 (by rfl) ⟨96765, by rfl⟩ : syracuseStep 4128661 = 193531) (by norm_num)
theorem B5504881 : Blo 2173435 5504881 := bstep (se 2 (by rfl) ⟨2064330, by rfl⟩ : syracuseStep 5504881 = 4128661) B4128661
theorem B7339841 : Blo 2173435 7339841 := bstep (se 2 (by rfl) ⟨2752440, by rfl⟩ : syracuseStep 7339841 = 5504881) B5504881
theorem B4893227 : Blo 2173435 4893227 := bstep (se 1 (by rfl) ⟨3669920, by rfl⟩ : syracuseStep 4893227 = 7339841) B7339841
theorem B3262151 : Blo 2173435 3262151 := bstep (se 1 (by rfl) ⟨2446613, by rfl⟩ : syracuseStep 3262151 = 4893227) B4893227
theorem B2174767 : Blo 2173435 2174767 := bstep (se 1 (by rfl) ⟨1631075, by rfl⟩ : syracuseStep 2174767 = 3262151) B3262151
theorem B3262157 : Blo 2173435 3262157 := bbase (se 3 (by rfl) ⟨611654, by rfl⟩ : syracuseStep 3262157 = 1223309) (by norm_num)
theorem B2174771 : Blo 2173435 2174771 := bstep (se 1 (by rfl) ⟨1631078, by rfl⟩ : syracuseStep 2174771 = 3262157) B3262157
theorem B4893245 : Blo 2173435 4893245 := bbase (se 3 (by rfl) ⟨917483, by rfl⟩ : syracuseStep 4893245 = 1834967) (by norm_num)
theorem B3262163 : Blo 2173435 3262163 := bstep (se 1 (by rfl) ⟨2446622, by rfl⟩ : syracuseStep 3262163 = 4893245) B4893245
theorem B2174775 : Blo 2173435 2174775 := bstep (se 1 (by rfl) ⟨1631081, by rfl⟩ : syracuseStep 2174775 = 3262163) B3262163
theorem B3669941 : Blo 2173435 3669941 := bbase (se 5 (by rfl) ⟨172028, by rfl⟩ : syracuseStep 3669941 = 344057) (by norm_num)
theorem B2446627 : Blo 2173435 2446627 := bstep (se 1 (by rfl) ⟨1834970, by rfl⟩ : syracuseStep 2446627 = 3669941) B3669941
theorem B3262169 : Blo 2173435 3262169 := bstep (se 2 (by rfl) ⟨1223313, by rfl⟩ : syracuseStep 3262169 = 2446627) B2446627
theorem B2174779 : Blo 2173435 2174779 := bstep (se 1 (by rfl) ⟨1631084, by rfl⟩ : syracuseStep 2174779 = 3262169) B3262169
theorem B2322389 : Blo 2173435 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B6193037 : Blo 2173435 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B16514765 : Blo 2173435 16514765 := bstep (se 3 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 16514765 = 6193037) B6193037
theorem B11009843 : Blo 2173435 11009843 := bstep (se 1 (by rfl) ⟨8257382, by rfl⟩ : syracuseStep 11009843 = 16514765) B16514765
theorem B7339895 : Blo 2173435 7339895 := bstep (se 1 (by rfl) ⟨5504921, by rfl⟩ : syracuseStep 7339895 = 11009843) B11009843
theorem B4893263 : Blo 2173435 4893263 := bstep (se 1 (by rfl) ⟨3669947, by rfl⟩ : syracuseStep 4893263 = 7339895) B7339895
theorem B3262175 : Blo 2173435 3262175 := bstep (se 1 (by rfl) ⟨2446631, by rfl⟩ : syracuseStep 3262175 = 4893263) B4893263
theorem B2174783 : Blo 2173435 2174783 := bstep (se 1 (by rfl) ⟨1631087, by rfl⟩ : syracuseStep 2174783 = 3262175) B3262175
theorem B3262181 : Blo 2173435 3262181 := bbase (se 4 (by rfl) ⟨305829, by rfl⟩ : syracuseStep 3262181 = 611659) (by norm_num)
theorem B2174787 : Blo 2173435 2174787 := bstep (se 1 (by rfl) ⟨1631090, by rfl⟩ : syracuseStep 2174787 = 3262181) B3262181
theorem B6193061 : Blo 2173435 6193061 := bbase (se 4 (by rfl) ⟨580599, by rfl⟩ : syracuseStep 6193061 = 1161199) (by norm_num)
theorem B4128707 : Blo 2173435 4128707 := bstep (se 1 (by rfl) ⟨3096530, by rfl⟩ : syracuseStep 4128707 = 6193061) B6193061
theorem B2752471 : Blo 2173435 2752471 := bstep (se 1 (by rfl) ⟨2064353, by rfl⟩ : syracuseStep 2752471 = 4128707) B4128707
theorem B3669961 : Blo 2173435 3669961 := bstep (se 2 (by rfl) ⟨1376235, by rfl⟩ : syracuseStep 3669961 = 2752471) B2752471
theorem B4893281 : Blo 2173435 4893281 := bstep (se 2 (by rfl) ⟨1834980, by rfl⟩ : syracuseStep 4893281 = 3669961) B3669961
theorem B3262187 : Blo 2173435 3262187 := bstep (se 1 (by rfl) ⟨2446640, by rfl⟩ : syracuseStep 3262187 = 4893281) B4893281
theorem B2174791 : Blo 2173435 2174791 := bstep (se 1 (by rfl) ⟨1631093, by rfl⟩ : syracuseStep 2174791 = 3262187) B3262187
theorem B2446645 : Blo 2173435 2446645 := bbase (se 5 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 2446645 = 229373) (by norm_num)
theorem B3262193 : Blo 2173435 3262193 := bstep (se 2 (by rfl) ⟨1223322, by rfl⟩ : syracuseStep 3262193 = 2446645) B2446645
theorem B2174795 : Blo 2173435 2174795 := bstep (se 1 (by rfl) ⟨1631096, by rfl⟩ : syracuseStep 2174795 = 3262193) B3262193
theorem B2752481 : Blo 2173435 2752481 := bbase (se 2 (by rfl) ⟨1032180, by rfl⟩ : syracuseStep 2752481 = 2064361) (by norm_num)
theorem B7339949 : Blo 2173435 7339949 := bstep (se 3 (by rfl) ⟨1376240, by rfl⟩ : syracuseStep 7339949 = 2752481) B2752481
theorem B4893299 : Blo 2173435 4893299 := bstep (se 1 (by rfl) ⟨3669974, by rfl⟩ : syracuseStep 4893299 = 7339949) B7339949
theorem B3262199 : Blo 2173435 3262199 := bstep (se 1 (by rfl) ⟨2446649, by rfl⟩ : syracuseStep 3262199 = 4893299) B4893299
theorem B2174799 : Blo 2173435 2174799 := bstep (se 1 (by rfl) ⟨1631099, by rfl⟩ : syracuseStep 2174799 = 3262199) B3262199
theorem B3262205 : Blo 2173435 3262205 := bbase (se 3 (by rfl) ⟨611663, by rfl⟩ : syracuseStep 3262205 = 1223327) (by norm_num)
theorem B2174803 : Blo 2173435 2174803 := bstep (se 1 (by rfl) ⟨1631102, by rfl⟩ : syracuseStep 2174803 = 3262205) B3262205
theorem B4893317 : Blo 2173435 4893317 := bbase (se 4 (by rfl) ⟨458748, by rfl⟩ : syracuseStep 4893317 = 917497) (by norm_num)
theorem B3262211 : Blo 2173435 3262211 := bstep (se 1 (by rfl) ⟨2446658, by rfl⟩ : syracuseStep 3262211 = 4893317) B4893317
theorem B2174807 : Blo 2173435 2174807 := bstep (se 1 (by rfl) ⟨1631105, by rfl⟩ : syracuseStep 2174807 = 3262211) B3262211
theorem B5027765 : Blo 2173435 5027765 := bbase (se 5 (by rfl) ⟨235676, by rfl⟩ : syracuseStep 5027765 = 471353) (by norm_num)
theorem B13407373 : Blo 2173435 13407373 := bstep (se 3 (by rfl) ⟨2513882, by rfl⟩ : syracuseStep 13407373 = 5027765) B5027765
theorem B17876497 : Blo 2173435 17876497 := bstep (se 2 (by rfl) ⟨6703686, by rfl⟩ : syracuseStep 17876497 = 13407373) B13407373
theorem B23835329 : Blo 2173435 23835329 := bstep (se 2 (by rfl) ⟨8938248, by rfl⟩ : syracuseStep 23835329 = 17876497) B17876497
theorem B15890219 : Blo 2173435 15890219 := bstep (se 1 (by rfl) ⟨11917664, by rfl⟩ : syracuseStep 15890219 = 23835329) B23835329
theorem B10593479 : Blo 2173435 10593479 := bstep (se 1 (by rfl) ⟨7945109, by rfl⟩ : syracuseStep 10593479 = 15890219) B15890219
theorem B7062319 : Blo 2173435 7062319 := bstep (se 1 (by rfl) ⟨5296739, by rfl⟩ : syracuseStep 7062319 = 10593479) B10593479
theorem B9416425 : Blo 2173435 9416425 := bstep (se 2 (by rfl) ⟨3531159, by rfl⟩ : syracuseStep 9416425 = 7062319) B7062319
theorem B12555233 : Blo 2173435 12555233 := bstep (se 2 (by rfl) ⟨4708212, by rfl⟩ : syracuseStep 12555233 = 9416425) B9416425
theorem B8370155 : Blo 2173435 8370155 := bstep (se 1 (by rfl) ⟨6277616, by rfl⟩ : syracuseStep 8370155 = 12555233) B12555233
theorem B5580103 : Blo 2173435 5580103 := bstep (se 1 (by rfl) ⟨4185077, by rfl⟩ : syracuseStep 5580103 = 8370155) B8370155
theorem B7440137 : Blo 2173435 7440137 := bstep (se 2 (by rfl) ⟨2790051, by rfl⟩ : syracuseStep 7440137 = 5580103) B5580103
theorem B4960091 : Blo 2173435 4960091 := bstep (se 1 (by rfl) ⟨3720068, by rfl⟩ : syracuseStep 4960091 = 7440137) B7440137
theorem B3306727 : Blo 2173435 3306727 := bstep (se 1 (by rfl) ⟨2480045, by rfl⟩ : syracuseStep 3306727 = 4960091) B4960091
theorem B17635877 : Blo 2173435 17635877 := bstep (se 4 (by rfl) ⟨1653363, by rfl⟩ : syracuseStep 17635877 = 3306727) B3306727
theorem B11757251 : Blo 2173435 11757251 := bstep (se 1 (by rfl) ⟨8817938, by rfl⟩ : syracuseStep 11757251 = 17635877) B17635877
theorem B7838167 : Blo 2173435 7838167 := bstep (se 1 (by rfl) ⟨5878625, by rfl⟩ : syracuseStep 7838167 = 11757251) B11757251
theorem B10450889 : Blo 2173435 10450889 := bstep (se 2 (by rfl) ⟨3919083, by rfl⟩ : syracuseStep 10450889 = 7838167) B7838167
theorem B6967259 : Blo 2173435 6967259 := bstep (se 1 (by rfl) ⟨5225444, by rfl⟩ : syracuseStep 6967259 = 10450889) B10450889
theorem B4644839 : Blo 2173435 4644839 := bstep (se 1 (by rfl) ⟨3483629, by rfl⟩ : syracuseStep 4644839 = 6967259) B6967259
theorem B3096559 : Blo 2173435 3096559 := bstep (se 1 (by rfl) ⟨2322419, by rfl⟩ : syracuseStep 3096559 = 4644839) B4644839
theorem B4128745 : Blo 2173435 4128745 := bstep (se 2 (by rfl) ⟨1548279, by rfl⟩ : syracuseStep 4128745 = 3096559) B3096559
theorem B5504993 : Blo 2173435 5504993 := bstep (se 2 (by rfl) ⟨2064372, by rfl⟩ : syracuseStep 5504993 = 4128745) B4128745
theorem B3669995 : Blo 2173435 3669995 := bstep (se 1 (by rfl) ⟨2752496, by rfl⟩ : syracuseStep 3669995 = 5504993) B5504993
theorem B2446663 : Blo 2173435 2446663 := bstep (se 1 (by rfl) ⟨1834997, by rfl⟩ : syracuseStep 2446663 = 3669995) B3669995
theorem B3262217 : Blo 2173435 3262217 := bstep (se 2 (by rfl) ⟨1223331, by rfl⟩ : syracuseStep 3262217 = 2446663) B2446663
theorem B2174811 : Blo 2173435 2174811 := bstep (se 1 (by rfl) ⟨1631108, by rfl⟩ : syracuseStep 2174811 = 3262217) B3262217
theorem B11010005 : Blo 2173435 11010005 := bbase (se 7 (by rfl) ⟨129023, by rfl⟩ : syracuseStep 11010005 = 258047) (by norm_num)
theorem B7340003 : Blo 2173435 7340003 := bstep (se 1 (by rfl) ⟨5505002, by rfl⟩ : syracuseStep 7340003 = 11010005) B11010005
theorem B4893335 : Blo 2173435 4893335 := bstep (se 1 (by rfl) ⟨3670001, by rfl⟩ : syracuseStep 4893335 = 7340003) B7340003
theorem B3262223 : Blo 2173435 3262223 := bstep (se 1 (by rfl) ⟨2446667, by rfl⟩ : syracuseStep 3262223 = 4893335) B4893335
theorem B2174815 : Blo 2173435 2174815 := bstep (se 1 (by rfl) ⟨1631111, by rfl⟩ : syracuseStep 2174815 = 3262223) B3262223
theorem B3262229 : Blo 2173435 3262229 := bbase (se 6 (by rfl) ⟨76458, by rfl⟩ : syracuseStep 3262229 = 152917) (by norm_num)
theorem B2174819 : Blo 2173435 2174819 := bstep (se 1 (by rfl) ⟨1631114, by rfl⟩ : syracuseStep 2174819 = 3262229) B3262229
theorem B2653921 : Blo 2173435 2653921 := bbase (se 2 (by rfl) ⟨995220, by rfl⟩ : syracuseStep 2653921 = 1990441) (by norm_num)
theorem B3538561 : Blo 2173435 3538561 := bstep (se 2 (by rfl) ⟨1326960, by rfl⟩ : syracuseStep 3538561 = 2653921) B2653921
theorem B4718081 : Blo 2173435 4718081 := bstep (se 2 (by rfl) ⟨1769280, by rfl⟩ : syracuseStep 4718081 = 3538561) B3538561
theorem B3145387 : Blo 2173435 3145387 := bstep (se 1 (by rfl) ⟨2359040, by rfl⟩ : syracuseStep 3145387 = 4718081) B4718081
theorem B4193849 : Blo 2173435 4193849 := bstep (se 2 (by rfl) ⟨1572693, by rfl⟩ : syracuseStep 4193849 = 3145387) B3145387
theorem B2795899 : Blo 2173435 2795899 := bstep (se 1 (by rfl) ⟨2096924, by rfl⟩ : syracuseStep 2795899 = 4193849) B4193849
theorem B3727865 : Blo 2173435 3727865 := bstep (se 2 (by rfl) ⟨1397949, by rfl⟩ : syracuseStep 3727865 = 2795899) B2795899
theorem B2485243 : Blo 2173435 2485243 := bstep (se 1 (by rfl) ⟨1863932, by rfl⟩ : syracuseStep 2485243 = 3727865) B3727865
theorem B3313657 : Blo 2173435 3313657 := bstep (se 2 (by rfl) ⟨1242621, by rfl⟩ : syracuseStep 3313657 = 2485243) B2485243
theorem B4418209 : Blo 2173435 4418209 := bstep (se 2 (by rfl) ⟨1656828, by rfl⟩ : syracuseStep 4418209 = 3313657) B3313657
theorem B23563781 : Blo 2173435 23563781 := bstep (se 4 (by rfl) ⟨2209104, by rfl⟩ : syracuseStep 23563781 = 4418209) B4418209
theorem B15709187 : Blo 2173435 15709187 := bstep (se 1 (by rfl) ⟨11781890, by rfl⟩ : syracuseStep 15709187 = 23563781) B23563781
theorem B41891165 : Blo 2173435 41891165 := bstep (se 3 (by rfl) ⟨7854593, by rfl⟩ : syracuseStep 41891165 = 15709187) B15709187
theorem B27927443 : Blo 2173435 27927443 := bstep (se 1 (by rfl) ⟨20945582, by rfl⟩ : syracuseStep 27927443 = 41891165) B41891165
theorem B74473181 : Blo 2173435 74473181 := bstep (se 3 (by rfl) ⟨13963721, by rfl⟩ : syracuseStep 74473181 = 27927443) B27927443
theorem B49648787 : Blo 2173435 49648787 := bstep (se 1 (by rfl) ⟨37236590, by rfl⟩ : syracuseStep 49648787 = 74473181) B74473181
theorem B33099191 : Blo 2173435 33099191 := bstep (se 1 (by rfl) ⟨24824393, by rfl⟩ : syracuseStep 33099191 = 49648787) B49648787
theorem B22066127 : Blo 2173435 22066127 := bstep (se 1 (by rfl) ⟨16549595, by rfl⟩ : syracuseStep 22066127 = 33099191) B33099191
theorem B14710751 : Blo 2173435 14710751 := bstep (se 1 (by rfl) ⟨11033063, by rfl⟩ : syracuseStep 14710751 = 22066127) B22066127
theorem B9807167 : Blo 2173435 9807167 := bstep (se 1 (by rfl) ⟨7355375, by rfl⟩ : syracuseStep 9807167 = 14710751) B14710751
theorem B26152445 : Blo 2173435 26152445 := bstep (se 3 (by rfl) ⟨4903583, by rfl⟩ : syracuseStep 26152445 = 9807167) B9807167
theorem B1115837653 : Blo 2173435 1115837653 := bstep (se 7 (by rfl) ⟨13076222, by rfl⟩ : syracuseStep 1115837653 = 26152445) B26152445
theorem B1487783537 : Blo 2173435 1487783537 := bstep (se 2 (by rfl) ⟨557918826, by rfl⟩ : syracuseStep 1487783537 = 1115837653) B1115837653
theorem B991855691 : Blo 2173435 991855691 := bstep (se 1 (by rfl) ⟨743891768, by rfl⟩ : syracuseStep 991855691 = 1487783537) B1487783537
theorem B661237127 : Blo 2173435 661237127 := bstep (se 1 (by rfl) ⟨495927845, by rfl⟩ : syracuseStep 661237127 = 991855691) B991855691
theorem B440824751 : Blo 2173435 440824751 := bstep (se 1 (by rfl) ⟨330618563, by rfl⟩ : syracuseStep 440824751 = 661237127) B661237127
theorem B293883167 : Blo 2173435 293883167 := bstep (se 1 (by rfl) ⟨220412375, by rfl⟩ : syracuseStep 293883167 = 440824751) B440824751
theorem B195922111 : Blo 2173435 195922111 := bstep (se 1 (by rfl) ⟨146941583, by rfl⟩ : syracuseStep 195922111 = 293883167) B293883167
theorem B261229481 : Blo 2173435 261229481 := bstep (se 2 (by rfl) ⟨97961055, by rfl⟩ : syracuseStep 261229481 = 195922111) B195922111
theorem B174152987 : Blo 2173435 174152987 := bstep (se 1 (by rfl) ⟨130614740, by rfl⟩ : syracuseStep 174152987 = 261229481) B261229481
theorem B116101991 : Blo 2173435 116101991 := bstep (se 1 (by rfl) ⟨87076493, by rfl⟩ : syracuseStep 116101991 = 174152987) B174152987
theorem B77401327 : Blo 2173435 77401327 := bstep (se 1 (by rfl) ⟨58050995, by rfl⟩ : syracuseStep 77401327 = 116101991) B116101991
theorem B103201769 : Blo 2173435 103201769 := bstep (se 2 (by rfl) ⟨38700663, by rfl⟩ : syracuseStep 103201769 = 77401327) B77401327
theorem B68801179 : Blo 2173435 68801179 := bstep (se 1 (by rfl) ⟨51600884, by rfl⟩ : syracuseStep 68801179 = 103201769) B103201769
theorem B1467758485 : Blo 2173435 1467758485 := bstep (se 6 (by rfl) ⟨34400589, by rfl⟩ : syracuseStep 1467758485 = 68801179) B68801179
theorem B7828045253 : Blo 2173435 7828045253 := bstep (se 4 (by rfl) ⟨733879242, by rfl⟩ : syracuseStep 7828045253 = 1467758485) B1467758485
theorem B5218696835 : Blo 2173435 5218696835 := bstep (se 1 (by rfl) ⟨3914022626, by rfl⟩ : syracuseStep 5218696835 = 7828045253) B7828045253
theorem B3479131223 : Blo 2173435 3479131223 := bstep (se 1 (by rfl) ⟨2609348417, by rfl⟩ : syracuseStep 3479131223 = 5218696835) B5218696835
theorem B2319420815 : Blo 2173435 2319420815 := bstep (se 1 (by rfl) ⟨1739565611, by rfl⟩ : syracuseStep 2319420815 = 3479131223) B3479131223
theorem B1546280543 : Blo 2173435 1546280543 := bstep (se 1 (by rfl) ⟨1159710407, by rfl⟩ : syracuseStep 1546280543 = 2319420815) B2319420815
theorem B4123414781 : Blo 2173435 4123414781 := bstep (se 3 (by rfl) ⟨773140271, by rfl⟩ : syracuseStep 4123414781 = 1546280543) B1546280543
theorem B2748943187 : Blo 2173435 2748943187 := bstep (se 1 (by rfl) ⟨2061707390, by rfl⟩ : syracuseStep 2748943187 = 4123414781) B4123414781
theorem B1832628791 : Blo 2173435 1832628791 := bstep (se 1 (by rfl) ⟨1374471593, by rfl⟩ : syracuseStep 1832628791 = 2748943187) B2748943187
theorem B4887010109 : Blo 2173435 4887010109 := bstep (se 3 (by rfl) ⟨916314395, by rfl⟩ : syracuseStep 4887010109 = 1832628791) B1832628791
theorem B13032026957 : Blo 2173435 13032026957 := bstep (se 3 (by rfl) ⟨2443505054, by rfl⟩ : syracuseStep 13032026957 = 4887010109) B4887010109
theorem B8688017971 : Blo 2173435 8688017971 := bstep (se 1 (by rfl) ⟨6516013478, by rfl⟩ : syracuseStep 8688017971 = 13032026957) B13032026957
theorem B11584023961 : Blo 2173435 11584023961 := bstep (se 2 (by rfl) ⟨4344008985, by rfl⟩ : syracuseStep 11584023961 = 8688017971) B8688017971
theorem B15445365281 : Blo 2173435 15445365281 := bstep (se 2 (by rfl) ⟨5792011980, by rfl⟩ : syracuseStep 15445365281 = 11584023961) B11584023961
theorem B10296910187 : Blo 2173435 10296910187 := bstep (se 1 (by rfl) ⟨7722682640, by rfl⟩ : syracuseStep 10296910187 = 15445365281) B15445365281
theorem B6864606791 : Blo 2173435 6864606791 := bstep (se 1 (by rfl) ⟨5148455093, by rfl⟩ : syracuseStep 6864606791 = 10296910187) B10296910187
theorem B4576404527 : Blo 2173435 4576404527 := bstep (se 1 (by rfl) ⟨3432303395, by rfl⟩ : syracuseStep 4576404527 = 6864606791) B6864606791
theorem B3050936351 : Blo 2173435 3050936351 := bstep (se 1 (by rfl) ⟨2288202263, by rfl⟩ : syracuseStep 3050936351 = 4576404527) B4576404527
theorem B2033957567 : Blo 2173435 2033957567 := bstep (se 1 (by rfl) ⟨1525468175, by rfl⟩ : syracuseStep 2033957567 = 3050936351) B3050936351
theorem B5423886845 : Blo 2173435 5423886845 := bstep (se 3 (by rfl) ⟨1016978783, by rfl⟩ : syracuseStep 5423886845 = 2033957567) B2033957567
theorem B3615924563 : Blo 2173435 3615924563 := bstep (se 1 (by rfl) ⟨2711943422, by rfl⟩ : syracuseStep 3615924563 = 5423886845) B5423886845
theorem B2410616375 : Blo 2173435 2410616375 := bstep (se 1 (by rfl) ⟨1807962281, by rfl⟩ : syracuseStep 2410616375 = 3615924563) B3615924563
theorem B1607077583 : Blo 2173435 1607077583 := bstep (se 1 (by rfl) ⟨1205308187, by rfl⟩ : syracuseStep 1607077583 = 2410616375) B2410616375
theorem B1071385055 : Blo 2173435 1071385055 := bstep (se 1 (by rfl) ⟨803538791, by rfl⟩ : syracuseStep 1071385055 = 1607077583) B1607077583
theorem B714256703 : Blo 2173435 714256703 := bstep (se 1 (by rfl) ⟨535692527, by rfl⟩ : syracuseStep 714256703 = 1071385055) B1071385055
theorem B476171135 : Blo 2173435 476171135 := bstep (se 1 (by rfl) ⟨357128351, by rfl⟩ : syracuseStep 476171135 = 714256703) B714256703
theorem B317447423 : Blo 2173435 317447423 := bstep (se 1 (by rfl) ⟨238085567, by rfl⟩ : syracuseStep 317447423 = 476171135) B476171135
theorem B211631615 : Blo 2173435 211631615 := bstep (se 1 (by rfl) ⟨158723711, by rfl⟩ : syracuseStep 211631615 = 317447423) B317447423
theorem B141087743 : Blo 2173435 141087743 := bstep (se 1 (by rfl) ⟨105815807, by rfl⟩ : syracuseStep 141087743 = 211631615) B211631615
theorem B94058495 : Blo 2173435 94058495 := bstep (se 1 (by rfl) ⟨70543871, by rfl⟩ : syracuseStep 94058495 = 141087743) B141087743
theorem B62705663 : Blo 2173435 62705663 := bstep (se 1 (by rfl) ⟨47029247, by rfl⟩ : syracuseStep 62705663 = 94058495) B94058495
theorem B41803775 : Blo 2173435 41803775 := bstep (se 1 (by rfl) ⟨31352831, by rfl⟩ : syracuseStep 41803775 = 62705663) B62705663
theorem B27869183 : Blo 2173435 27869183 := bstep (se 1 (by rfl) ⟨20901887, by rfl⟩ : syracuseStep 27869183 = 41803775) B41803775
theorem B18579455 : Blo 2173435 18579455 := bstep (se 1 (by rfl) ⟨13934591, by rfl⟩ : syracuseStep 18579455 = 27869183) B27869183
theorem B12386303 : Blo 2173435 12386303 := bstep (se 1 (by rfl) ⟨9289727, by rfl⟩ : syracuseStep 12386303 = 18579455) B18579455
theorem B8257535 : Blo 2173435 8257535 := bstep (se 1 (by rfl) ⟨6193151, by rfl⟩ : syracuseStep 8257535 = 12386303) B12386303
theorem B5505023 : Blo 2173435 5505023 := bstep (se 1 (by rfl) ⟨4128767, by rfl⟩ : syracuseStep 5505023 = 8257535) B8257535
theorem B3670015 : Blo 2173435 3670015 := bstep (se 1 (by rfl) ⟨2752511, by rfl⟩ : syracuseStep 3670015 = 5505023) B5505023
theorem B4893353 : Blo 2173435 4893353 := bstep (se 2 (by rfl) ⟨1835007, by rfl⟩ : syracuseStep 4893353 = 3670015) B3670015
theorem B3262235 : Blo 2173435 3262235 := bstep (se 1 (by rfl) ⟨2446676, by rfl⟩ : syracuseStep 3262235 = 4893353) B4893353
theorem B2174823 : Blo 2173435 2174823 := bstep (se 1 (by rfl) ⟨1631117, by rfl⟩ : syracuseStep 2174823 = 3262235) B3262235
theorem B2446681 : Blo 2173435 2446681 := bbase (se 2 (by rfl) ⟨917505, by rfl⟩ : syracuseStep 2446681 = 1835011) (by norm_num)
theorem B3262241 : Blo 2173435 3262241 := bstep (se 2 (by rfl) ⟨1223340, by rfl⟩ : syracuseStep 3262241 = 2446681) B2446681
theorem B2174827 : Blo 2173435 2174827 := bstep (se 1 (by rfl) ⟨1631120, by rfl⟩ : syracuseStep 2174827 = 3262241) B3262241
theorem B3483661 : Blo 2173435 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B4644881 : Blo 2173435 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B3096587 : Blo 2173435 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B8257565 : Blo 2173435 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B5505043 : Blo 2173435 5505043 := bstep (se 1 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 5505043 = 8257565) B8257565
theorem B7340057 : Blo 2173435 7340057 := bstep (se 2 (by rfl) ⟨2752521, by rfl⟩ : syracuseStep 7340057 = 5505043) B5505043
theorem B4893371 : Blo 2173435 4893371 := bstep (se 1 (by rfl) ⟨3670028, by rfl⟩ : syracuseStep 4893371 = 7340057) B7340057
theorem B3262247 : Blo 2173435 3262247 := bstep (se 1 (by rfl) ⟨2446685, by rfl⟩ : syracuseStep 3262247 = 4893371) B4893371
theorem B2174831 : Blo 2173435 2174831 := bstep (se 1 (by rfl) ⟨1631123, by rfl⟩ : syracuseStep 2174831 = 3262247) B3262247
theorem B3262253 : Blo 2173435 3262253 := bbase (se 3 (by rfl) ⟨611672, by rfl⟩ : syracuseStep 3262253 = 1223345) (by norm_num)
theorem B2174835 : Blo 2173435 2174835 := bstep (se 1 (by rfl) ⟨1631126, by rfl⟩ : syracuseStep 2174835 = 3262253) B3262253
theorem B4893389 : Blo 2173435 4893389 := bbase (se 3 (by rfl) ⟨917510, by rfl⟩ : syracuseStep 4893389 = 1835021) (by norm_num)
theorem B3262259 : Blo 2173435 3262259 := bstep (se 1 (by rfl) ⟨2446694, by rfl⟩ : syracuseStep 3262259 = 4893389) B4893389
theorem B2174839 : Blo 2173435 2174839 := bstep (se 1 (by rfl) ⟨1631129, by rfl⟩ : syracuseStep 2174839 = 3262259) B3262259
theorem B2752537 : Blo 2173435 2752537 := bbase (se 2 (by rfl) ⟨1032201, by rfl⟩ : syracuseStep 2752537 = 2064403) (by norm_num)
theorem B3670049 : Blo 2173435 3670049 := bstep (se 2 (by rfl) ⟨1376268, by rfl⟩ : syracuseStep 3670049 = 2752537) B2752537
theorem B2446699 : Blo 2173435 2446699 := bstep (se 1 (by rfl) ⟨1835024, by rfl⟩ : syracuseStep 2446699 = 3670049) B3670049
theorem B3262265 : Blo 2173435 3262265 := bstep (se 2 (by rfl) ⟨1223349, by rfl⟩ : syracuseStep 3262265 = 2446699) B2446699
theorem B2174843 : Blo 2173435 2174843 := bstep (se 1 (by rfl) ⟨1631132, by rfl⟩ : syracuseStep 2174843 = 3262265) B3262265
theorem B9289829 : Blo 2173435 9289829 := bbase (se 4 (by rfl) ⟨870921, by rfl⟩ : syracuseStep 9289829 = 1741843) (by norm_num)
theorem B24772877 : Blo 2173435 24772877 := bstep (se 3 (by rfl) ⟨4644914, by rfl⟩ : syracuseStep 24772877 = 9289829) B9289829
theorem B16515251 : Blo 2173435 16515251 := bstep (se 1 (by rfl) ⟨12386438, by rfl⟩ : syracuseStep 16515251 = 24772877) B24772877
theorem B11010167 : Blo 2173435 11010167 := bstep (se 1 (by rfl) ⟨8257625, by rfl⟩ : syracuseStep 11010167 = 16515251) B16515251
theorem B7340111 : Blo 2173435 7340111 := bstep (se 1 (by rfl) ⟨5505083, by rfl⟩ : syracuseStep 7340111 = 11010167) B11010167
theorem B4893407 : Blo 2173435 4893407 := bstep (se 1 (by rfl) ⟨3670055, by rfl⟩ : syracuseStep 4893407 = 7340111) B7340111
theorem B3262271 : Blo 2173435 3262271 := bstep (se 1 (by rfl) ⟨2446703, by rfl⟩ : syracuseStep 3262271 = 4893407) B4893407
theorem B2174847 : Blo 2173435 2174847 := bstep (se 1 (by rfl) ⟨1631135, by rfl⟩ : syracuseStep 2174847 = 3262271) B3262271
theorem B3262277 : Blo 2173435 3262277 := bbase (se 4 (by rfl) ⟨305838, by rfl⟩ : syracuseStep 3262277 = 611677) (by norm_num)
theorem B2174851 : Blo 2173435 2174851 := bstep (se 1 (by rfl) ⟨1631138, by rfl⟩ : syracuseStep 2174851 = 3262277) B3262277
theorem B3670069 : Blo 2173435 3670069 := bbase (se 5 (by rfl) ⟨172034, by rfl⟩ : syracuseStep 3670069 = 344069) (by norm_num)
theorem B4893425 : Blo 2173435 4893425 := bstep (se 2 (by rfl) ⟨1835034, by rfl⟩ : syracuseStep 4893425 = 3670069) B3670069
theorem B3262283 : Blo 2173435 3262283 := bstep (se 1 (by rfl) ⟨2446712, by rfl⟩ : syracuseStep 3262283 = 4893425) B4893425
theorem B2174855 : Blo 2173435 2174855 := bstep (se 1 (by rfl) ⟨1631141, by rfl⟩ : syracuseStep 2174855 = 3262283) B3262283
theorem B2446717 : Blo 2173435 2446717 := bbase (se 3 (by rfl) ⟨458759, by rfl⟩ : syracuseStep 2446717 = 917519) (by norm_num)
theorem B3262289 : Blo 2173435 3262289 := bstep (se 2 (by rfl) ⟨1223358, by rfl⟩ : syracuseStep 3262289 = 2446717) B2446717
theorem B2174859 : Blo 2173435 2174859 := bstep (se 1 (by rfl) ⟨1631144, by rfl⟩ : syracuseStep 2174859 = 3262289) B3262289
theorem B7340165 : Blo 2173435 7340165 := bbase (se 4 (by rfl) ⟨688140, by rfl⟩ : syracuseStep 7340165 = 1376281) (by norm_num)
theorem B4893443 : Blo 2173435 4893443 := bstep (se 1 (by rfl) ⟨3670082, by rfl⟩ : syracuseStep 4893443 = 7340165) B7340165
theorem B3262295 : Blo 2173435 3262295 := bstep (se 1 (by rfl) ⟨2446721, by rfl⟩ : syracuseStep 3262295 = 4893443) B4893443
theorem B2174863 : Blo 2173435 2174863 := bstep (se 1 (by rfl) ⟨1631147, by rfl⟩ : syracuseStep 2174863 = 3262295) B3262295
theorem B3262301 : Blo 2173435 3262301 := bbase (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) (by norm_num)
theorem B2174867 : Blo 2173435 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B4893461 : Blo 2173435 4893461 := bbase (se 6 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 4893461 = 229381) (by norm_num)
theorem B3262307 : Blo 2173435 3262307 := bstep (se 1 (by rfl) ⟨2446730, by rfl⟩ : syracuseStep 3262307 = 4893461) B4893461
theorem B2174871 : Blo 2173435 2174871 := bstep (se 1 (by rfl) ⟨1631153, by rfl⟩ : syracuseStep 2174871 = 3262307) B3262307
theorem B8257733 : Blo 2173435 8257733 := bbase (se 4 (by rfl) ⟨774162, by rfl⟩ : syracuseStep 8257733 = 1548325) (by norm_num)
theorem B5505155 : Blo 2173435 5505155 := bstep (se 1 (by rfl) ⟨4128866, by rfl⟩ : syracuseStep 5505155 = 8257733) B8257733
theorem B3670103 : Blo 2173435 3670103 := bstep (se 1 (by rfl) ⟨2752577, by rfl⟩ : syracuseStep 3670103 = 5505155) B5505155
theorem B2446735 : Blo 2173435 2446735 := bstep (se 1 (by rfl) ⟨1835051, by rfl⟩ : syracuseStep 2446735 = 3670103) B3670103
theorem B3262313 : Blo 2173435 3262313 := bstep (se 2 (by rfl) ⟨1223367, by rfl⟩ : syracuseStep 3262313 = 2446735) B2446735
theorem B2174875 : Blo 2173435 2174875 := bstep (se 1 (by rfl) ⟨1631156, by rfl⟩ : syracuseStep 2174875 = 3262313) B3262313
theorem B3919205 : Blo 2173435 3919205 := bbase (se 4 (by rfl) ⟨367425, by rfl⟩ : syracuseStep 3919205 = 734851) (by norm_num)
theorem B10451213 : Blo 2173435 10451213 := bstep (se 3 (by rfl) ⟨1959602, by rfl⟩ : syracuseStep 10451213 = 3919205) B3919205
theorem B6967475 : Blo 2173435 6967475 := bstep (se 1 (by rfl) ⟨5225606, by rfl⟩ : syracuseStep 6967475 = 10451213) B10451213
theorem B4644983 : Blo 2173435 4644983 := bstep (se 1 (by rfl) ⟨3483737, by rfl⟩ : syracuseStep 4644983 = 6967475) B6967475
theorem B12386621 : Blo 2173435 12386621 := bstep (se 3 (by rfl) ⟨2322491, by rfl⟩ : syracuseStep 12386621 = 4644983) B4644983
theorem B8257747 : Blo 2173435 8257747 := bstep (se 1 (by rfl) ⟨6193310, by rfl⟩ : syracuseStep 8257747 = 12386621) B12386621
theorem B11010329 : Blo 2173435 11010329 := bstep (se 2 (by rfl) ⟨4128873, by rfl⟩ : syracuseStep 11010329 = 8257747) B8257747
theorem B7340219 : Blo 2173435 7340219 := bstep (se 1 (by rfl) ⟨5505164, by rfl⟩ : syracuseStep 7340219 = 11010329) B11010329
theorem B4893479 : Blo 2173435 4893479 := bstep (se 1 (by rfl) ⟨3670109, by rfl⟩ : syracuseStep 4893479 = 7340219) B7340219
theorem B3262319 : Blo 2173435 3262319 := bstep (se 1 (by rfl) ⟨2446739, by rfl⟩ : syracuseStep 3262319 = 4893479) B4893479
theorem B2174879 : Blo 2173435 2174879 := bstep (se 1 (by rfl) ⟨1631159, by rfl⟩ : syracuseStep 2174879 = 3262319) B3262319
theorem B3262325 : Blo 2173435 3262325 := bbase (se 5 (by rfl) ⟨152921, by rfl⟩ : syracuseStep 3262325 = 305843) (by norm_num)
theorem B2174883 : Blo 2173435 2174883 := bstep (se 1 (by rfl) ⟨1631162, by rfl⟩ : syracuseStep 2174883 = 3262325) B3262325
theorem B7062565 : Blo 2173435 7062565 := bbase (se 4 (by rfl) ⟨662115, by rfl⟩ : syracuseStep 7062565 = 1324231) (by norm_num)
theorem B9416753 : Blo 2173435 9416753 := bstep (se 2 (by rfl) ⟨3531282, by rfl⟩ : syracuseStep 9416753 = 7062565) B7062565
theorem B6277835 : Blo 2173435 6277835 := bstep (se 1 (by rfl) ⟨4708376, by rfl⟩ : syracuseStep 6277835 = 9416753) B9416753
theorem B16740893 : Blo 2173435 16740893 := bstep (se 3 (by rfl) ⟨3138917, by rfl⟩ : syracuseStep 16740893 = 6277835) B6277835
theorem B11160595 : Blo 2173435 11160595 := bstep (se 1 (by rfl) ⟨8370446, by rfl⟩ : syracuseStep 11160595 = 16740893) B16740893
theorem B14880793 : Blo 2173435 14880793 := bstep (se 2 (by rfl) ⟨5580297, by rfl⟩ : syracuseStep 14880793 = 11160595) B11160595
theorem B19841057 : Blo 2173435 19841057 := bstep (se 2 (by rfl) ⟨7440396, by rfl⟩ : syracuseStep 19841057 = 14880793) B14880793
theorem B13227371 : Blo 2173435 13227371 := bstep (se 1 (by rfl) ⟨9920528, by rfl⟩ : syracuseStep 13227371 = 19841057) B19841057
theorem B8818247 : Blo 2173435 8818247 := bstep (se 1 (by rfl) ⟨6613685, by rfl⟩ : syracuseStep 8818247 = 13227371) B13227371
theorem B5878831 : Blo 2173435 5878831 := bstep (se 1 (by rfl) ⟨4409123, by rfl⟩ : syracuseStep 5878831 = 8818247) B8818247
theorem B7838441 : Blo 2173435 7838441 := bstep (se 2 (by rfl) ⟨2939415, by rfl⟩ : syracuseStep 7838441 = 5878831) B5878831
theorem B5225627 : Blo 2173435 5225627 := bstep (se 1 (by rfl) ⟨3919220, by rfl⟩ : syracuseStep 5225627 = 7838441) B7838441
theorem B3483751 : Blo 2173435 3483751 := bstep (se 1 (by rfl) ⟨2612813, by rfl⟩ : syracuseStep 3483751 = 5225627) B5225627
theorem B4645001 : Blo 2173435 4645001 := bstep (se 2 (by rfl) ⟨1741875, by rfl⟩ : syracuseStep 4645001 = 3483751) B3483751
theorem B3096667 : Blo 2173435 3096667 := bstep (se 1 (by rfl) ⟨2322500, by rfl⟩ : syracuseStep 3096667 = 4645001) B4645001
theorem B4128889 : Blo 2173435 4128889 := bstep (se 2 (by rfl) ⟨1548333, by rfl⟩ : syracuseStep 4128889 = 3096667) B3096667
theorem B5505185 : Blo 2173435 5505185 := bstep (se 2 (by rfl) ⟨2064444, by rfl⟩ : syracuseStep 5505185 = 4128889) B4128889
theorem B3670123 : Blo 2173435 3670123 := bstep (se 1 (by rfl) ⟨2752592, by rfl⟩ : syracuseStep 3670123 = 5505185) B5505185
theorem B4893497 : Blo 2173435 4893497 := bstep (se 2 (by rfl) ⟨1835061, by rfl⟩ : syracuseStep 4893497 = 3670123) B3670123
theorem B3262331 : Blo 2173435 3262331 := bstep (se 1 (by rfl) ⟨2446748, by rfl⟩ : syracuseStep 3262331 = 4893497) B4893497
theorem B2174887 : Blo 2173435 2174887 := bstep (se 1 (by rfl) ⟨1631165, by rfl⟩ : syracuseStep 2174887 = 3262331) B3262331
theorem B2446753 : Blo 2173435 2446753 := bbase (se 2 (by rfl) ⟨917532, by rfl⟩ : syracuseStep 2446753 = 1835065) (by norm_num)
theorem B3262337 : Blo 2173435 3262337 := bstep (se 2 (by rfl) ⟨1223376, by rfl⟩ : syracuseStep 3262337 = 2446753) B2446753
theorem B2174891 : Blo 2173435 2174891 := bstep (se 1 (by rfl) ⟨1631168, by rfl⟩ : syracuseStep 2174891 = 3262337) B3262337
theorem B5505205 : Blo 2173435 5505205 := bbase (se 5 (by rfl) ⟨258056, by rfl⟩ : syracuseStep 5505205 = 516113) (by norm_num)
theorem B7340273 : Blo 2173435 7340273 := bstep (se 2 (by rfl) ⟨2752602, by rfl⟩ : syracuseStep 7340273 = 5505205) B5505205
theorem B4893515 : Blo 2173435 4893515 := bstep (se 1 (by rfl) ⟨3670136, by rfl⟩ : syracuseStep 4893515 = 7340273) B7340273
theorem B3262343 : Blo 2173435 3262343 := bstep (se 1 (by rfl) ⟨2446757, by rfl⟩ : syracuseStep 3262343 = 4893515) B4893515
theorem B2174895 : Blo 2173435 2174895 := bstep (se 1 (by rfl) ⟨1631171, by rfl⟩ : syracuseStep 2174895 = 3262343) B3262343
theorem B3262349 : Blo 2173435 3262349 := bbase (se 3 (by rfl) ⟨611690, by rfl⟩ : syracuseStep 3262349 = 1223381) (by norm_num)
theorem B2174899 : Blo 2173435 2174899 := bstep (se 1 (by rfl) ⟨1631174, by rfl⟩ : syracuseStep 2174899 = 3262349) B3262349
theorem B4893533 : Blo 2173435 4893533 := bbase (se 3 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 4893533 = 1835075) (by norm_num)
theorem B3262355 : Blo 2173435 3262355 := bstep (se 1 (by rfl) ⟨2446766, by rfl⟩ : syracuseStep 3262355 = 4893533) B4893533
theorem B2174903 : Blo 2173435 2174903 := bstep (se 1 (by rfl) ⟨1631177, by rfl⟩ : syracuseStep 2174903 = 3262355) B3262355
theorem B3670157 : Blo 2173435 3670157 := bbase (se 3 (by rfl) ⟨688154, by rfl⟩ : syracuseStep 3670157 = 1376309) (by norm_num)
theorem B2446771 : Blo 2173435 2446771 := bstep (se 1 (by rfl) ⟨1835078, by rfl⟩ : syracuseStep 2446771 = 3670157) B3670157
theorem B3262361 : Blo 2173435 3262361 := bstep (se 2 (by rfl) ⟨1223385, by rfl⟩ : syracuseStep 3262361 = 2446771) B2446771
theorem B2174907 : Blo 2173435 2174907 := bstep (se 1 (by rfl) ⟨1631180, by rfl⟩ : syracuseStep 2174907 = 3262361) B3262361
theorem B2234665 : Blo 2173435 2234665 := bbase (se 2 (by rfl) ⟨837999, by rfl⟩ : syracuseStep 2234665 = 1675999) (by norm_num)
theorem B2979553 : Blo 2173435 2979553 := bstep (se 2 (by rfl) ⟨1117332, by rfl⟩ : syracuseStep 2979553 = 2234665) B2234665
theorem B3972737 : Blo 2173435 3972737 := bstep (se 2 (by rfl) ⟨1489776, by rfl⟩ : syracuseStep 3972737 = 2979553) B2979553
theorem B10593965 : Blo 2173435 10593965 := bstep (se 3 (by rfl) ⟨1986368, by rfl⟩ : syracuseStep 10593965 = 3972737) B3972737
theorem B7062643 : Blo 2173435 7062643 := bstep (se 1 (by rfl) ⟨5296982, by rfl⟩ : syracuseStep 7062643 = 10593965) B10593965
theorem B9416857 : Blo 2173435 9416857 := bstep (se 2 (by rfl) ⟨3531321, by rfl⟩ : syracuseStep 9416857 = 7062643) B7062643
theorem B12555809 : Blo 2173435 12555809 := bstep (se 2 (by rfl) ⟨4708428, by rfl⟩ : syracuseStep 12555809 = 9416857) B9416857
theorem B8370539 : Blo 2173435 8370539 := bstep (se 1 (by rfl) ⟨6277904, by rfl⟩ : syracuseStep 8370539 = 12555809) B12555809
theorem B5580359 : Blo 2173435 5580359 := bstep (se 1 (by rfl) ⟨4185269, by rfl⟩ : syracuseStep 5580359 = 8370539) B8370539
theorem B3720239 : Blo 2173435 3720239 := bstep (se 1 (by rfl) ⟨2790179, by rfl⟩ : syracuseStep 3720239 = 5580359) B5580359
theorem B2480159 : Blo 2173435 2480159 := bstep (se 1 (by rfl) ⟨1860119, by rfl⟩ : syracuseStep 2480159 = 3720239) B3720239
theorem B6613757 : Blo 2173435 6613757 := bstep (se 3 (by rfl) ⟨1240079, by rfl⟩ : syracuseStep 6613757 = 2480159) B2480159
theorem B4409171 : Blo 2173435 4409171 := bstep (se 1 (by rfl) ⟨3306878, by rfl⟩ : syracuseStep 4409171 = 6613757) B6613757
theorem B2939447 : Blo 2173435 2939447 := bstep (se 1 (by rfl) ⟨2204585, by rfl⟩ : syracuseStep 2939447 = 4409171) B4409171
theorem B7838525 : Blo 2173435 7838525 := bstep (se 3 (by rfl) ⟨1469723, by rfl⟩ : syracuseStep 7838525 = 2939447) B2939447
theorem B5225683 : Blo 2173435 5225683 := bstep (se 1 (by rfl) ⟨3919262, by rfl⟩ : syracuseStep 5225683 = 7838525) B7838525
theorem B6967577 : Blo 2173435 6967577 := bstep (se 2 (by rfl) ⟨2612841, by rfl⟩ : syracuseStep 6967577 = 5225683) B5225683
theorem B18580205 : Blo 2173435 18580205 := bstep (se 3 (by rfl) ⟨3483788, by rfl⟩ : syracuseStep 18580205 = 6967577) B6967577
theorem B12386803 : Blo 2173435 12386803 := bstep (se 1 (by rfl) ⟨9290102, by rfl⟩ : syracuseStep 12386803 = 18580205) B18580205
theorem B16515737 : Blo 2173435 16515737 := bstep (se 2 (by rfl) ⟨6193401, by rfl⟩ : syracuseStep 16515737 = 12386803) B12386803
theorem B11010491 : Blo 2173435 11010491 := bstep (se 1 (by rfl) ⟨8257868, by rfl⟩ : syracuseStep 11010491 = 16515737) B16515737
theorem B7340327 : Blo 2173435 7340327 := bstep (se 1 (by rfl) ⟨5505245, by rfl⟩ : syracuseStep 7340327 = 11010491) B11010491
theorem B4893551 : Blo 2173435 4893551 := bstep (se 1 (by rfl) ⟨3670163, by rfl⟩ : syracuseStep 4893551 = 7340327) B7340327
theorem B3262367 : Blo 2173435 3262367 := bstep (se 1 (by rfl) ⟨2446775, by rfl⟩ : syracuseStep 3262367 = 4893551) B4893551
theorem B2174911 : Blo 2173435 2174911 := bstep (se 1 (by rfl) ⟨1631183, by rfl⟩ : syracuseStep 2174911 = 3262367) B3262367
theorem B3262373 : Blo 2173435 3262373 := bbase (se 4 (by rfl) ⟨305847, by rfl⟩ : syracuseStep 3262373 = 611695) (by norm_num)
theorem B2174915 : Blo 2173435 2174915 := bstep (se 1 (by rfl) ⟨1631186, by rfl⟩ : syracuseStep 2174915 = 3262373) B3262373
theorem B2752633 : Blo 2173435 2752633 := bbase (se 2 (by rfl) ⟨1032237, by rfl⟩ : syracuseStep 2752633 = 2064475) (by norm_num)
theorem B3670177 : Blo 2173435 3670177 := bstep (se 2 (by rfl) ⟨1376316, by rfl⟩ : syracuseStep 3670177 = 2752633) B2752633
theorem B4893569 : Blo 2173435 4893569 := bstep (se 2 (by rfl) ⟨1835088, by rfl⟩ : syracuseStep 4893569 = 3670177) B3670177
theorem B3262379 : Blo 2173435 3262379 := bstep (se 1 (by rfl) ⟨2446784, by rfl⟩ : syracuseStep 3262379 = 4893569) B4893569
theorem B2174919 : Blo 2173435 2174919 := bstep (se 1 (by rfl) ⟨1631189, by rfl⟩ : syracuseStep 2174919 = 3262379) B3262379
theorem B2446789 : Blo 2173435 2446789 := bbase (se 4 (by rfl) ⟨229386, by rfl⟩ : syracuseStep 2446789 = 458773) (by norm_num)
theorem B3262385 : Blo 2173435 3262385 := bstep (se 2 (by rfl) ⟨1223394, by rfl⟩ : syracuseStep 3262385 = 2446789) B2446789
theorem B2174923 : Blo 2173435 2174923 := bstep (se 1 (by rfl) ⟨1631192, by rfl⟩ : syracuseStep 2174923 = 3262385) B3262385
theorem B4128965 : Blo 2173435 4128965 := bbase (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) (by norm_num)
theorem B2752643 : Blo 2173435 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B7340381 : Blo 2173435 7340381 := bstep (se 3 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 7340381 = 2752643) B2752643
theorem B4893587 : Blo 2173435 4893587 := bstep (se 1 (by rfl) ⟨3670190, by rfl⟩ : syracuseStep 4893587 = 7340381) B7340381
theorem B3262391 : Blo 2173435 3262391 := bstep (se 1 (by rfl) ⟨2446793, by rfl⟩ : syracuseStep 3262391 = 4893587) B4893587
theorem B2174927 : Blo 2173435 2174927 := bstep (se 1 (by rfl) ⟨1631195, by rfl⟩ : syracuseStep 2174927 = 3262391) B3262391
theorem B3262397 : Blo 2173435 3262397 := bbase (se 3 (by rfl) ⟨611699, by rfl⟩ : syracuseStep 3262397 = 1223399) (by norm_num)
theorem B2174931 : Blo 2173435 2174931 := bstep (se 1 (by rfl) ⟨1631198, by rfl⟩ : syracuseStep 2174931 = 3262397) B3262397
theorem B4893605 : Blo 2173435 4893605 := bbase (se 4 (by rfl) ⟨458775, by rfl⟩ : syracuseStep 4893605 = 917551) (by norm_num)
theorem B3262403 : Blo 2173435 3262403 := bstep (se 1 (by rfl) ⟨2446802, by rfl⟩ : syracuseStep 3262403 = 4893605) B4893605
theorem B2174935 : Blo 2173435 2174935 := bstep (se 1 (by rfl) ⟨1631201, by rfl⟩ : syracuseStep 2174935 = 3262403) B3262403
theorem B5505317 : Blo 2173435 5505317 := bbase (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) (by norm_num)
theorem B3670211 : Blo 2173435 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B2446807 : Blo 2173435 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B3262409 : Blo 2173435 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B2174939 : Blo 2173435 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B6193493 : Blo 2173435 6193493 := bbase (se 10 (by rfl) ⟨9072, by rfl⟩ : syracuseStep 6193493 = 18145) (by norm_num)
theorem B4128995 : Blo 2173435 4128995 := bstep (se 1 (by rfl) ⟨3096746, by rfl⟩ : syracuseStep 4128995 = 6193493) B6193493
theorem B11010653 : Blo 2173435 11010653 := bstep (se 3 (by rfl) ⟨2064497, by rfl⟩ : syracuseStep 11010653 = 4128995) B4128995
theorem B7340435 : Blo 2173435 7340435 := bstep (se 1 (by rfl) ⟨5505326, by rfl⟩ : syracuseStep 7340435 = 11010653) B11010653
theorem B4893623 : Blo 2173435 4893623 := bstep (se 1 (by rfl) ⟨3670217, by rfl⟩ : syracuseStep 4893623 = 7340435) B7340435
theorem B3262415 : Blo 2173435 3262415 := bstep (se 1 (by rfl) ⟨2446811, by rfl⟩ : syracuseStep 3262415 = 4893623) B4893623
theorem B2174943 : Blo 2173435 2174943 := bstep (se 1 (by rfl) ⟨1631207, by rfl⟩ : syracuseStep 2174943 = 3262415) B3262415
theorem B3262421 : Blo 2173435 3262421 := bbase (se 7 (by rfl) ⟨38231, by rfl⟩ : syracuseStep 3262421 = 76463) (by norm_num)
theorem B2174947 : Blo 2173435 2174947 := bstep (se 1 (by rfl) ⟨1631210, by rfl⟩ : syracuseStep 2174947 = 3262421) B3262421
theorem B8258021 : Blo 2173435 8258021 := bbase (se 4 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 8258021 = 1548379) (by norm_num)
theorem B5505347 : Blo 2173435 5505347 := bstep (se 1 (by rfl) ⟨4129010, by rfl⟩ : syracuseStep 5505347 = 8258021) B8258021
theorem B3670231 : Blo 2173435 3670231 := bstep (se 1 (by rfl) ⟨2752673, by rfl⟩ : syracuseStep 3670231 = 5505347) B5505347
theorem B4893641 : Blo 2173435 4893641 := bstep (se 2 (by rfl) ⟨1835115, by rfl⟩ : syracuseStep 4893641 = 3670231) B3670231
theorem B3262427 : Blo 2173435 3262427 := bstep (se 1 (by rfl) ⟨2446820, by rfl⟩ : syracuseStep 3262427 = 4893641) B4893641
theorem B2174951 : Blo 2173435 2174951 := bstep (se 1 (by rfl) ⟨1631213, by rfl⟩ : syracuseStep 2174951 = 3262427) B3262427
theorem B2446825 : Blo 2173435 2446825 := bbase (se 2 (by rfl) ⟨917559, by rfl⟩ : syracuseStep 2446825 = 1835119) (by norm_num)
theorem B3262433 : Blo 2173435 3262433 := bstep (se 2 (by rfl) ⟨1223412, by rfl⟩ : syracuseStep 3262433 = 2446825) B2446825
theorem B2174955 : Blo 2173435 2174955 := bstep (se 1 (by rfl) ⟨1631216, by rfl⟩ : syracuseStep 2174955 = 3262433) B3262433
theorem B2322577 : Blo 2173435 2322577 := bbase (se 2 (by rfl) ⟨870966, by rfl⟩ : syracuseStep 2322577 = 1741933) (by norm_num)
theorem B12387077 : Blo 2173435 12387077 := bstep (se 4 (by rfl) ⟨1161288, by rfl⟩ : syracuseStep 12387077 = 2322577) B2322577
theorem B8258051 : Blo 2173435 8258051 := bstep (se 1 (by rfl) ⟨6193538, by rfl⟩ : syracuseStep 8258051 = 12387077) B12387077
theorem B5505367 : Blo 2173435 5505367 := bstep (se 1 (by rfl) ⟨4129025, by rfl⟩ : syracuseStep 5505367 = 8258051) B8258051
theorem B7340489 : Blo 2173435 7340489 := bstep (se 2 (by rfl) ⟨2752683, by rfl⟩ : syracuseStep 7340489 = 5505367) B5505367
theorem B4893659 : Blo 2173435 4893659 := bstep (se 1 (by rfl) ⟨3670244, by rfl⟩ : syracuseStep 4893659 = 7340489) B7340489
theorem B3262439 : Blo 2173435 3262439 := bstep (se 1 (by rfl) ⟨2446829, by rfl⟩ : syracuseStep 3262439 = 4893659) B4893659
theorem B2174959 : Blo 2173435 2174959 := bstep (se 1 (by rfl) ⟨1631219, by rfl⟩ : syracuseStep 2174959 = 3262439) B3262439
theorem B3262445 : Blo 2173435 3262445 := bbase (se 3 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 3262445 = 1223417) (by norm_num)
theorem B2174963 : Blo 2173435 2174963 := bstep (se 1 (by rfl) ⟨1631222, by rfl⟩ : syracuseStep 2174963 = 3262445) B3262445
theorem B4893677 : Blo 2173435 4893677 := bbase (se 3 (by rfl) ⟨917564, by rfl⟩ : syracuseStep 4893677 = 1835129) (by norm_num)
theorem B3262451 : Blo 2173435 3262451 := bstep (se 1 (by rfl) ⟨2446838, by rfl⟩ : syracuseStep 3262451 = 4893677) B4893677
theorem B2174967 : Blo 2173435 2174967 := bstep (se 1 (by rfl) ⟨1631225, by rfl⟩ : syracuseStep 2174967 = 3262451) B3262451
theorem B4645181 : Blo 2173435 4645181 := bbase (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) (by norm_num)
theorem B3096787 : Blo 2173435 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B4129049 : Blo 2173435 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B2752699 : Blo 2173435 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B3670265 : Blo 2173435 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B2446843 : Blo 2173435 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B3262457 : Blo 2173435 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B2174971 : Blo 2173435 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B12246005 : Blo 2173435 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B8164003 : Blo 2173435 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B10885337 : Blo 2173435 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B7256891 : Blo 2173435 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B4837927 : Blo 2173435 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B6450569 : Blo 2173435 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B4300379 : Blo 2173435 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B2866919 : Blo 2173435 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B7645117 : Blo 2173435 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B10193489 : Blo 2173435 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B6795659 : Blo 2173435 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B4530439 : Blo 2173435 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B6040585 : Blo 2173435 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B32216453 : Blo 2173435 32216453 := bstep (se 4 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 32216453 = 6040585) B6040585
theorem B21477635 : Blo 2173435 21477635 := bstep (se 1 (by rfl) ⟨16108226, by rfl⟩ : syracuseStep 21477635 = 32216453) B32216453
theorem B14318423 : Blo 2173435 14318423 := bstep (se 1 (by rfl) ⟨10738817, by rfl⟩ : syracuseStep 14318423 = 21477635) B21477635
theorem B9545615 : Blo 2173435 9545615 := bstep (se 1 (by rfl) ⟨7159211, by rfl⟩ : syracuseStep 9545615 = 14318423) B14318423
theorem B6363743 : Blo 2173435 6363743 := bstep (se 1 (by rfl) ⟨4772807, by rfl⟩ : syracuseStep 6363743 = 9545615) B9545615
theorem B16969981 : Blo 2173435 16969981 := bstep (se 3 (by rfl) ⟨3181871, by rfl⟩ : syracuseStep 16969981 = 6363743) B6363743
theorem B22626641 : Blo 2173435 22626641 := bstep (se 2 (by rfl) ⟨8484990, by rfl⟩ : syracuseStep 22626641 = 16969981) B16969981
theorem B15084427 : Blo 2173435 15084427 := bstep (se 1 (by rfl) ⟨11313320, by rfl⟩ : syracuseStep 15084427 = 22626641) B22626641
theorem B20112569 : Blo 2173435 20112569 := bstep (se 2 (by rfl) ⟨7542213, by rfl⟩ : syracuseStep 20112569 = 15084427) B15084427
theorem B13408379 : Blo 2173435 13408379 := bstep (se 1 (by rfl) ⟨10056284, by rfl⟩ : syracuseStep 13408379 = 20112569) B20112569
theorem B8938919 : Blo 2173435 8938919 := bstep (se 1 (by rfl) ⟨6704189, by rfl⟩ : syracuseStep 8938919 = 13408379) B13408379
theorem B5959279 : Blo 2173435 5959279 := bstep (se 1 (by rfl) ⟨4469459, by rfl⟩ : syracuseStep 5959279 = 8938919) B8938919
theorem B7945705 : Blo 2173435 7945705 := bstep (se 2 (by rfl) ⟨2979639, by rfl⟩ : syracuseStep 7945705 = 5959279) B5959279
theorem B10594273 : Blo 2173435 10594273 := bstep (se 2 (by rfl) ⟨3972852, by rfl⟩ : syracuseStep 10594273 = 7945705) B7945705
theorem B14125697 : Blo 2173435 14125697 := bstep (se 2 (by rfl) ⟨5297136, by rfl⟩ : syracuseStep 14125697 = 10594273) B10594273
theorem B9417131 : Blo 2173435 9417131 := bstep (se 1 (by rfl) ⟨7062848, by rfl⟩ : syracuseStep 9417131 = 14125697) B14125697
theorem B6278087 : Blo 2173435 6278087 := bstep (se 1 (by rfl) ⟨4708565, by rfl⟩ : syracuseStep 6278087 = 9417131) B9417131
theorem B4185391 : Blo 2173435 4185391 := bstep (se 1 (by rfl) ⟨3139043, by rfl⟩ : syracuseStep 4185391 = 6278087) B6278087
theorem B5580521 : Blo 2173435 5580521 := bstep (se 2 (by rfl) ⟨2092695, by rfl⟩ : syracuseStep 5580521 = 4185391) B4185391
theorem B3720347 : Blo 2173435 3720347 := bstep (se 1 (by rfl) ⟨2790260, by rfl⟩ : syracuseStep 3720347 = 5580521) B5580521
theorem B2480231 : Blo 2173435 2480231 := bstep (se 1 (by rfl) ⟨1860173, by rfl⟩ : syracuseStep 2480231 = 3720347) B3720347
theorem B105823189 : Blo 2173435 105823189 := bstep (se 7 (by rfl) ⟨1240115, by rfl⟩ : syracuseStep 105823189 = 2480231) B2480231
theorem B141097585 : Blo 2173435 141097585 := bstep (se 2 (by rfl) ⟨52911594, by rfl⟩ : syracuseStep 141097585 = 105823189) B105823189
theorem B188130113 : Blo 2173435 188130113 := bstep (se 2 (by rfl) ⟨70548792, by rfl⟩ : syracuseStep 188130113 = 141097585) B141097585
theorem B125420075 : Blo 2173435 125420075 := bstep (se 1 (by rfl) ⟨94065056, by rfl⟩ : syracuseStep 125420075 = 188130113) B188130113
theorem B83613383 : Blo 2173435 83613383 := bstep (se 1 (by rfl) ⟨62710037, by rfl⟩ : syracuseStep 83613383 = 125420075) B125420075
theorem B55742255 : Blo 2173435 55742255 := bstep (se 1 (by rfl) ⟨41806691, by rfl⟩ : syracuseStep 55742255 = 83613383) B83613383
theorem B37161503 : Blo 2173435 37161503 := bstep (se 1 (by rfl) ⟨27871127, by rfl⟩ : syracuseStep 37161503 = 55742255) B55742255
theorem B24774335 : Blo 2173435 24774335 := bstep (se 1 (by rfl) ⟨18580751, by rfl⟩ : syracuseStep 24774335 = 37161503) B37161503
theorem B16516223 : Blo 2173435 16516223 := bstep (se 1 (by rfl) ⟨12387167, by rfl⟩ : syracuseStep 16516223 = 24774335) B24774335
theorem B11010815 : Blo 2173435 11010815 := bstep (se 1 (by rfl) ⟨8258111, by rfl⟩ : syracuseStep 11010815 = 16516223) B16516223
theorem B7340543 : Blo 2173435 7340543 := bstep (se 1 (by rfl) ⟨5505407, by rfl⟩ : syracuseStep 7340543 = 11010815) B11010815
theorem B4893695 : Blo 2173435 4893695 := bstep (se 1 (by rfl) ⟨3670271, by rfl⟩ : syracuseStep 4893695 = 7340543) B7340543
theorem B3262463 : Blo 2173435 3262463 := bstep (se 1 (by rfl) ⟨2446847, by rfl⟩ : syracuseStep 3262463 = 4893695) B4893695
theorem B2174975 : Blo 2173435 2174975 := bstep (se 1 (by rfl) ⟨1631231, by rfl⟩ : syracuseStep 2174975 = 3262463) B3262463
theorem B3262469 : Blo 2173435 3262469 := bbase (se 4 (by rfl) ⟨305856, by rfl⟩ : syracuseStep 3262469 = 611713) (by norm_num)
theorem B2174979 : Blo 2173435 2174979 := bstep (se 1 (by rfl) ⟨1631234, by rfl⟩ : syracuseStep 2174979 = 3262469) B3262469
theorem B3670285 : Blo 2173435 3670285 := bbase (se 3 (by rfl) ⟨688178, by rfl⟩ : syracuseStep 3670285 = 1376357) (by norm_num)
theorem B4893713 : Blo 2173435 4893713 := bstep (se 2 (by rfl) ⟨1835142, by rfl⟩ : syracuseStep 4893713 = 3670285) B3670285
theorem B3262475 : Blo 2173435 3262475 := bstep (se 1 (by rfl) ⟨2446856, by rfl⟩ : syracuseStep 3262475 = 4893713) B4893713
theorem B2174983 : Blo 2173435 2174983 := bstep (se 1 (by rfl) ⟨1631237, by rfl⟩ : syracuseStep 2174983 = 3262475) B3262475
theorem B2446861 : Blo 2173435 2446861 := bbase (se 3 (by rfl) ⟨458786, by rfl⟩ : syracuseStep 2446861 = 917573) (by norm_num)
theorem B3262481 : Blo 2173435 3262481 := bstep (se 2 (by rfl) ⟨1223430, by rfl⟩ : syracuseStep 3262481 = 2446861) B2446861
theorem B2174987 : Blo 2173435 2174987 := bstep (se 1 (by rfl) ⟨1631240, by rfl⟩ : syracuseStep 2174987 = 3262481) B3262481
theorem B7340597 : Blo 2173435 7340597 := bbase (se 5 (by rfl) ⟨344090, by rfl⟩ : syracuseStep 7340597 = 688181) (by norm_num)
theorem B4893731 : Blo 2173435 4893731 := bstep (se 1 (by rfl) ⟨3670298, by rfl⟩ : syracuseStep 4893731 = 7340597) B7340597
theorem B3262487 : Blo 2173435 3262487 := bstep (se 1 (by rfl) ⟨2446865, by rfl⟩ : syracuseStep 3262487 = 4893731) B4893731
theorem B2174991 : Blo 2173435 2174991 := bstep (se 1 (by rfl) ⟨1631243, by rfl⟩ : syracuseStep 2174991 = 3262487) B3262487
theorem B3262493 : Blo 2173435 3262493 := bbase (se 3 (by rfl) ⟨611717, by rfl⟩ : syracuseStep 3262493 = 1223435) (by norm_num)
theorem B2174995 : Blo 2173435 2174995 := bstep (se 1 (by rfl) ⟨1631246, by rfl⟩ : syracuseStep 2174995 = 3262493) B3262493
theorem B4893749 : Blo 2173435 4893749 := bbase (se 5 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 4893749 = 458789) (by norm_num)
theorem B3262499 : Blo 2173435 3262499 := bstep (se 1 (by rfl) ⟨2446874, by rfl⟩ : syracuseStep 3262499 = 4893749) B4893749
theorem B2174999 : Blo 2173435 2174999 := bstep (se 1 (by rfl) ⟨1631249, by rfl⟩ : syracuseStep 2174999 = 3262499) B3262499
theorem B3919429 : Blo 2173435 3919429 := bbase (se 4 (by rfl) ⟨367446, by rfl⟩ : syracuseStep 3919429 = 734893) (by norm_num)
theorem B5225905 : Blo 2173435 5225905 := bstep (se 2 (by rfl) ⟨1959714, by rfl⟩ : syracuseStep 5225905 = 3919429) B3919429
theorem B6967873 : Blo 2173435 6967873 := bstep (se 2 (by rfl) ⟨2612952, by rfl⟩ : syracuseStep 6967873 = 5225905) B5225905
theorem B9290497 : Blo 2173435 9290497 := bstep (se 2 (by rfl) ⟨3483936, by rfl⟩ : syracuseStep 9290497 = 6967873) B6967873
theorem B12387329 : Blo 2173435 12387329 := bstep (se 2 (by rfl) ⟨4645248, by rfl⟩ : syracuseStep 12387329 = 9290497) B9290497
theorem B8258219 : Blo 2173435 8258219 := bstep (se 1 (by rfl) ⟨6193664, by rfl⟩ : syracuseStep 8258219 = 12387329) B12387329
theorem B5505479 : Blo 2173435 5505479 := bstep (se 1 (by rfl) ⟨4129109, by rfl⟩ : syracuseStep 5505479 = 8258219) B8258219
theorem B3670319 : Blo 2173435 3670319 := bstep (se 1 (by rfl) ⟨2752739, by rfl⟩ : syracuseStep 3670319 = 5505479) B5505479
theorem B2446879 : Blo 2173435 2446879 := bstep (se 1 (by rfl) ⟨1835159, by rfl⟩ : syracuseStep 2446879 = 3670319) B3670319
theorem B3262505 : Blo 2173435 3262505 := bstep (se 2 (by rfl) ⟨1223439, by rfl⟩ : syracuseStep 3262505 = 2446879) B2446879
theorem B2175003 : Blo 2173435 2175003 := bstep (se 1 (by rfl) ⟨1631252, by rfl⟩ : syracuseStep 2175003 = 3262505) B3262505
theorem B2612957 : Blo 2173435 2612957 := bbase (se 3 (by rfl) ⟨489929, by rfl⟩ : syracuseStep 2612957 = 979859) (by norm_num)
theorem B6967885 : Blo 2173435 6967885 := bstep (se 3 (by rfl) ⟨1306478, by rfl⟩ : syracuseStep 6967885 = 2612957) B2612957
theorem B9290513 : Blo 2173435 9290513 := bstep (se 2 (by rfl) ⟨3483942, by rfl⟩ : syracuseStep 9290513 = 6967885) B6967885
theorem B6193675 : Blo 2173435 6193675 := bstep (se 1 (by rfl) ⟨4645256, by rfl⟩ : syracuseStep 6193675 = 9290513) B9290513
theorem B8258233 : Blo 2173435 8258233 := bstep (se 2 (by rfl) ⟨3096837, by rfl⟩ : syracuseStep 8258233 = 6193675) B6193675
theorem B11010977 : Blo 2173435 11010977 := bstep (se 2 (by rfl) ⟨4129116, by rfl⟩ : syracuseStep 11010977 = 8258233) B8258233
theorem B7340651 : Blo 2173435 7340651 := bstep (se 1 (by rfl) ⟨5505488, by rfl⟩ : syracuseStep 7340651 = 11010977) B11010977
theorem B4893767 : Blo 2173435 4893767 := bstep (se 1 (by rfl) ⟨3670325, by rfl⟩ : syracuseStep 4893767 = 7340651) B7340651
theorem B3262511 : Blo 2173435 3262511 := bstep (se 1 (by rfl) ⟨2446883, by rfl⟩ : syracuseStep 3262511 = 4893767) B4893767
theorem B2175007 : Blo 2173435 2175007 := bstep (se 1 (by rfl) ⟨1631255, by rfl⟩ : syracuseStep 2175007 = 3262511) B3262511
theorem B3262517 : Blo 2173435 3262517 := bbase (se 5 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 3262517 = 305861) (by norm_num)
theorem B2175011 : Blo 2173435 2175011 := bstep (se 1 (by rfl) ⟨1631258, by rfl⟩ : syracuseStep 2175011 = 3262517) B3262517
theorem B5505509 : Blo 2173435 5505509 := bbase (se 4 (by rfl) ⟨516141, by rfl⟩ : syracuseStep 5505509 = 1032283) (by norm_num)
theorem B3670339 : Blo 2173435 3670339 := bstep (se 1 (by rfl) ⟨2752754, by rfl⟩ : syracuseStep 3670339 = 5505509) B5505509
theorem B4893785 : Blo 2173435 4893785 := bstep (se 2 (by rfl) ⟨1835169, by rfl⟩ : syracuseStep 4893785 = 3670339) B3670339
theorem B3262523 : Blo 2173435 3262523 := bstep (se 1 (by rfl) ⟨2446892, by rfl⟩ : syracuseStep 3262523 = 4893785) B4893785
theorem B2175015 : Blo 2173435 2175015 := bstep (se 1 (by rfl) ⟨1631261, by rfl⟩ : syracuseStep 2175015 = 3262523) B3262523
theorem B2446897 : Blo 2173435 2446897 := bbase (se 2 (by rfl) ⟨917586, by rfl⟩ : syracuseStep 2446897 = 1835173) (by norm_num)
theorem B3262529 : Blo 2173435 3262529 := bstep (se 2 (by rfl) ⟨1223448, by rfl⟩ : syracuseStep 3262529 = 2446897) B2446897
theorem B2175019 : Blo 2173435 2175019 := bstep (se 1 (by rfl) ⟨1631264, by rfl⟩ : syracuseStep 2175019 = 3262529) B3262529
theorem B2654165 : Blo 2173435 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B7077773 : Blo 2173435 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B4718515 : Blo 2173435 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B6291353 : Blo 2173435 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B1073724245 : Blo 2173435 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B715816163 : Blo 2173435 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B477210775 : Blo 2173435 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B636281033 : Blo 2173435 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B6786997685 : Blo 2173435 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B4524665123 : Blo 2173435 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B3016443415 : Blo 2173435 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B4021924553 : Blo 2173435 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B2681283035 : Blo 2173435 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B1787522023 : Blo 2173435 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B9533450789 : Blo 2173435 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B6355633859 : Blo 2173435 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B4237089239 : Blo 2173435 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B2824726159 : Blo 2173435 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B3766301545 : Blo 2173435 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B5021735393 : Blo 2173435 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B3347823595 : Blo 2173435 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B4463764793 : Blo 2173435 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B2975843195 : Blo 2173435 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B1983895463 : Blo 2173435 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B5290387901 : Blo 2173435 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B3526925267 : Blo 2173435 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B2351283511 : Blo 2173435 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B3135044681 : Blo 2173435 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B2090029787 : Blo 2173435 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B1393353191 : Blo 2173435 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B928902127 : Blo 2173435 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B1238536169 : Blo 2173435 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B825690779 : Blo 2173435 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B550460519 : Blo 2173435 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B366973679 : Blo 2173435 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B978596477 : Blo 2173435 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B652397651 : Blo 2173435 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B434931767 : Blo 2173435 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B289954511 : Blo 2173435 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B193303007 : Blo 2173435 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B128868671 : Blo 2173435 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B343649789 : Blo 2173435 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B229099859 : Blo 2173435 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B152733239 : Blo 2173435 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B101822159 : Blo 2173435 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B67881439 : Blo 2173435 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B90508585 : Blo 2173435 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B120678113 : Blo 2173435 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B80452075 : Blo 2173435 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B107269433 : Blo 2173435 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B71512955 : Blo 2173435 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B47675303 : Blo 2173435 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B31783535 : Blo 2173435 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B21189023 : Blo 2173435 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B14126015 : Blo 2173435 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B9417343 : Blo 2173435 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 2173435 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B8370971 : Blo 2173435 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 2173435 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 2173435 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B9921149 : Blo 2173435 9921149 := bstep (se 3 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 9921149 = 3720431) B3720431
theorem B6614099 : Blo 2173435 6614099 := bstep (se 1 (by rfl) ⟨4960574, by rfl⟩ : syracuseStep 6614099 = 9921149) B9921149
theorem B4409399 : Blo 2173435 4409399 := bstep (se 1 (by rfl) ⟨3307049, by rfl⟩ : syracuseStep 4409399 = 6614099) B6614099
theorem B2939599 : Blo 2173435 2939599 := bstep (se 1 (by rfl) ⟨2204699, by rfl⟩ : syracuseStep 2939599 = 4409399) B4409399
theorem B3919465 : Blo 2173435 3919465 := bstep (se 2 (by rfl) ⟨1469799, by rfl⟩ : syracuseStep 3919465 = 2939599) B2939599
theorem B5225953 : Blo 2173435 5225953 := bstep (se 2 (by rfl) ⟨1959732, by rfl⟩ : syracuseStep 5225953 = 3919465) B3919465
theorem B6967937 : Blo 2173435 6967937 := bstep (se 2 (by rfl) ⟨2612976, by rfl⟩ : syracuseStep 6967937 = 5225953) B5225953
theorem B4645291 : Blo 2173435 4645291 := bstep (se 1 (by rfl) ⟨3483968, by rfl⟩ : syracuseStep 4645291 = 6967937) B6967937
theorem B6193721 : Blo 2173435 6193721 := bstep (se 2 (by rfl) ⟨2322645, by rfl⟩ : syracuseStep 6193721 = 4645291) B4645291
theorem B4129147 : Blo 2173435 4129147 := bstep (se 1 (by rfl) ⟨3096860, by rfl⟩ : syracuseStep 4129147 = 6193721) B6193721
theorem B5505529 : Blo 2173435 5505529 := bstep (se 2 (by rfl) ⟨2064573, by rfl⟩ : syracuseStep 5505529 = 4129147) B4129147
theorem B7340705 : Blo 2173435 7340705 := bstep (se 2 (by rfl) ⟨2752764, by rfl⟩ : syracuseStep 7340705 = 5505529) B5505529
theorem B4893803 : Blo 2173435 4893803 := bstep (se 1 (by rfl) ⟨3670352, by rfl⟩ : syracuseStep 4893803 = 7340705) B7340705
theorem B3262535 : Blo 2173435 3262535 := bstep (se 1 (by rfl) ⟨2446901, by rfl⟩ : syracuseStep 3262535 = 4893803) B4893803
theorem B2175023 : Blo 2173435 2175023 := bstep (se 1 (by rfl) ⟨1631267, by rfl⟩ : syracuseStep 2175023 = 3262535) B3262535
theorem B3262541 : Blo 2173435 3262541 := bbase (se 3 (by rfl) ⟨611726, by rfl⟩ : syracuseStep 3262541 = 1223453) (by norm_num)
theorem B2175027 : Blo 2173435 2175027 := bstep (se 1 (by rfl) ⟨1631270, by rfl⟩ : syracuseStep 2175027 = 3262541) B3262541
theorem B4893821 : Blo 2173435 4893821 := bbase (se 3 (by rfl) ⟨917591, by rfl⟩ : syracuseStep 4893821 = 1835183) (by norm_num)
theorem B3262547 : Blo 2173435 3262547 := bstep (se 1 (by rfl) ⟨2446910, by rfl⟩ : syracuseStep 3262547 = 4893821) B4893821
theorem B2175031 : Blo 2173435 2175031 := bstep (se 1 (by rfl) ⟨1631273, by rfl⟩ : syracuseStep 2175031 = 3262547) B3262547
theorem B3670373 : Blo 2173435 3670373 := bbase (se 4 (by rfl) ⟨344097, by rfl⟩ : syracuseStep 3670373 = 688195) (by norm_num)
theorem B2446915 : Blo 2173435 2446915 := bstep (se 1 (by rfl) ⟨1835186, by rfl⟩ : syracuseStep 2446915 = 3670373) B3670373
theorem B3262553 : Blo 2173435 3262553 := bstep (se 2 (by rfl) ⟨1223457, by rfl⟩ : syracuseStep 3262553 = 2446915) B2446915
theorem B2175035 : Blo 2173435 2175035 := bstep (se 1 (by rfl) ⟨1631276, by rfl⟩ : syracuseStep 2175035 = 3262553) B3262553
theorem B4645325 : Blo 2173435 4645325 := bbase (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) (by norm_num)
theorem B3096883 : Blo 2173435 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B16516709 : Blo 2173435 16516709 := bstep (se 4 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 16516709 = 3096883) B3096883
theorem B11011139 : Blo 2173435 11011139 := bstep (se 1 (by rfl) ⟨8258354, by rfl⟩ : syracuseStep 11011139 = 16516709) B16516709
theorem B7340759 : Blo 2173435 7340759 := bstep (se 1 (by rfl) ⟨5505569, by rfl⟩ : syracuseStep 7340759 = 11011139) B11011139
theorem B4893839 : Blo 2173435 4893839 := bstep (se 1 (by rfl) ⟨3670379, by rfl⟩ : syracuseStep 4893839 = 7340759) B7340759
theorem B3262559 : Blo 2173435 3262559 := bstep (se 1 (by rfl) ⟨2446919, by rfl⟩ : syracuseStep 3262559 = 4893839) B4893839
theorem B2175039 : Blo 2173435 2175039 := bstep (se 1 (by rfl) ⟨1631279, by rfl⟩ : syracuseStep 2175039 = 3262559) B3262559
theorem B3262565 : Blo 2173435 3262565 := bbase (se 4 (by rfl) ⟨305865, by rfl⟩ : syracuseStep 3262565 = 611731) (by norm_num)
theorem B2175043 : Blo 2173435 2175043 := bstep (se 1 (by rfl) ⟨1631282, by rfl⟩ : syracuseStep 2175043 = 3262565) B3262565
theorem B5959477 : Blo 2173435 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B31783877 : Blo 2173435 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B21189251 : Blo 2173435 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B14126167 : Blo 2173435 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B18834889 : Blo 2173435 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B25113185 : Blo 2173435 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B16742123 : Blo 2173435 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B11161415 : Blo 2173435 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B29763773 : Blo 2173435 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B19842515 : Blo 2173435 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B13228343 : Blo 2173435 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B8818895 : Blo 2173435 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B23517053 : Blo 2173435 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B15678035 : Blo 2173435 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B10452023 : Blo 2173435 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B6968015 : Blo 2173435 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B4645343 : Blo 2173435 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B3096895 : Blo 2173435 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B4129193 : Blo 2173435 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B2752795 : Blo 2173435 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B3670393 : Blo 2173435 3670393 := bstep (se 2 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 3670393 = 2752795) B2752795
theorem B4893857 : Blo 2173435 4893857 := bstep (se 2 (by rfl) ⟨1835196, by rfl⟩ : syracuseStep 4893857 = 3670393) B3670393
theorem B3262571 : Blo 2173435 3262571 := bstep (se 1 (by rfl) ⟨2446928, by rfl⟩ : syracuseStep 3262571 = 4893857) B4893857
theorem B2175047 : Blo 2173435 2175047 := bstep (se 1 (by rfl) ⟨1631285, by rfl⟩ : syracuseStep 2175047 = 3262571) B3262571
theorem B2446933 : Blo 2173435 2446933 := bbase (se 8 (by rfl) ⟨14337, by rfl⟩ : syracuseStep 2446933 = 28675) (by norm_num)
theorem B3262577 : Blo 2173435 3262577 := bstep (se 2 (by rfl) ⟨1223466, by rfl⟩ : syracuseStep 3262577 = 2446933) B2446933
theorem B2175051 : Blo 2173435 2175051 := bstep (se 1 (by rfl) ⟨1631288, by rfl⟩ : syracuseStep 2175051 = 3262577) B3262577
theorem B2752805 : Blo 2173435 2752805 := bbase (se 4 (by rfl) ⟨258075, by rfl⟩ : syracuseStep 2752805 = 516151) (by norm_num)
theorem B7340813 : Blo 2173435 7340813 := bstep (se 3 (by rfl) ⟨1376402, by rfl⟩ : syracuseStep 7340813 = 2752805) B2752805
theorem B4893875 : Blo 2173435 4893875 := bstep (se 1 (by rfl) ⟨3670406, by rfl⟩ : syracuseStep 4893875 = 7340813) B7340813
theorem B3262583 : Blo 2173435 3262583 := bstep (se 1 (by rfl) ⟨2446937, by rfl⟩ : syracuseStep 3262583 = 4893875) B4893875
theorem B2175055 : Blo 2173435 2175055 := bstep (se 1 (by rfl) ⟨1631291, by rfl⟩ : syracuseStep 2175055 = 3262583) B3262583
theorem B3262589 : Blo 2173435 3262589 := bbase (se 3 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 3262589 = 1223471) (by norm_num)
theorem B2175059 : Blo 2173435 2175059 := bstep (se 1 (by rfl) ⟨1631294, by rfl⟩ : syracuseStep 2175059 = 3262589) B3262589
theorem B4893893 : Blo 2173435 4893893 := bbase (se 4 (by rfl) ⟨458802, by rfl⟩ : syracuseStep 4893893 = 917605) (by norm_num)
theorem B3262595 : Blo 2173435 3262595 := bstep (se 1 (by rfl) ⟨2446946, by rfl⟩ : syracuseStep 3262595 = 4893893) B4893893
theorem B2175063 : Blo 2173435 2175063 := bstep (se 1 (by rfl) ⟨1631297, by rfl⟩ : syracuseStep 2175063 = 3262595) B3262595
theorem B5879317 : Blo 2173435 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B7839089 : Blo 2173435 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B5226059 : Blo 2173435 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B13936157 : Blo 2173435 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B9290771 : Blo 2173435 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B6193847 : Blo 2173435 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B4129231 : Blo 2173435 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B5505641 : Blo 2173435 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B3670427 : Blo 2173435 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B2446951 : Blo 2173435 2446951 := bstep (se 1 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 2446951 = 3670427) B3670427
theorem B3262601 : Blo 2173435 3262601 := bstep (se 2 (by rfl) ⟨1223475, by rfl⟩ : syracuseStep 3262601 = 2446951) B2446951
theorem B2175067 : Blo 2173435 2175067 := bstep (se 1 (by rfl) ⟨1631300, by rfl⟩ : syracuseStep 2175067 = 3262601) B3262601
theorem B11011301 : Blo 2173435 11011301 := bbase (se 4 (by rfl) ⟨1032309, by rfl⟩ : syracuseStep 11011301 = 2064619) (by norm_num)
theorem B7340867 : Blo 2173435 7340867 := bstep (se 1 (by rfl) ⟨5505650, by rfl⟩ : syracuseStep 7340867 = 11011301) B11011301
theorem B4893911 : Blo 2173435 4893911 := bstep (se 1 (by rfl) ⟨3670433, by rfl⟩ : syracuseStep 4893911 = 7340867) B7340867
theorem B3262607 : Blo 2173435 3262607 := bstep (se 1 (by rfl) ⟨2446955, by rfl⟩ : syracuseStep 3262607 = 4893911) B4893911
theorem B2175071 : Blo 2173435 2175071 := bstep (se 1 (by rfl) ⟨1631303, by rfl⟩ : syracuseStep 2175071 = 3262607) B3262607
theorem B3262613 : Blo 2173435 3262613 := bbase (se 6 (by rfl) ⟨76467, by rfl⟩ : syracuseStep 3262613 = 152935) (by norm_num)
theorem B2175075 : Blo 2173435 2175075 := bstep (se 1 (by rfl) ⟨1631306, by rfl⟩ : syracuseStep 2175075 = 3262613) B3262613
theorem B9290821 : Blo 2173435 9290821 := bbase (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) (by norm_num)
theorem B12387761 : Blo 2173435 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B8258507 : Blo 2173435 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B5505671 : Blo 2173435 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B3670447 : Blo 2173435 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B4893929 : Blo 2173435 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B3262619 : Blo 2173435 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B2175079 : Blo 2173435 2175079 := bstep (se 1 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 2175079 = 3262619) B3262619
theorem B2446969 : Blo 2173435 2446969 := bbase (se 2 (by rfl) ⟨917613, by rfl⟩ : syracuseStep 2446969 = 1835227) (by norm_num)
theorem B3262625 : Blo 2173435 3262625 := bstep (se 2 (by rfl) ⟨1223484, by rfl⟩ : syracuseStep 3262625 = 2446969) B2446969
theorem B2175083 : Blo 2173435 2175083 := bstep (se 1 (by rfl) ⟨1631312, by rfl⟩ : syracuseStep 2175083 = 3262625) B3262625
theorem B3771301 : Blo 2173435 3771301 := bbase (se 4 (by rfl) ⟨353559, by rfl⟩ : syracuseStep 3771301 = 707119) (by norm_num)
theorem B5028401 : Blo 2173435 5028401 := bstep (se 2 (by rfl) ⟨1885650, by rfl⟩ : syracuseStep 5028401 = 3771301) B3771301
theorem B3352267 : Blo 2173435 3352267 := bstep (se 1 (by rfl) ⟨2514200, by rfl⟩ : syracuseStep 3352267 = 5028401) B5028401
theorem B4469689 : Blo 2173435 4469689 := bstep (se 2 (by rfl) ⟨1676133, by rfl⟩ : syracuseStep 4469689 = 3352267) B3352267
theorem B5959585 : Blo 2173435 5959585 := bstep (se 2 (by rfl) ⟨2234844, by rfl⟩ : syracuseStep 5959585 = 4469689) B4469689
theorem B7946113 : Blo 2173435 7946113 := bstep (se 2 (by rfl) ⟨2979792, by rfl⟩ : syracuseStep 7946113 = 5959585) B5959585
theorem B10594817 : Blo 2173435 10594817 := bstep (se 2 (by rfl) ⟨3973056, by rfl⟩ : syracuseStep 10594817 = 7946113) B7946113
theorem B7063211 : Blo 2173435 7063211 := bstep (se 1 (by rfl) ⟨5297408, by rfl⟩ : syracuseStep 7063211 = 10594817) B10594817
theorem B18835229 : Blo 2173435 18835229 := bstep (se 3 (by rfl) ⟨3531605, by rfl⟩ : syracuseStep 18835229 = 7063211) B7063211
theorem B12556819 : Blo 2173435 12556819 := bstep (se 1 (by rfl) ⟨9417614, by rfl⟩ : syracuseStep 12556819 = 18835229) B18835229
theorem B16742425 : Blo 2173435 16742425 := bstep (se 2 (by rfl) ⟨6278409, by rfl⟩ : syracuseStep 16742425 = 12556819) B12556819
theorem B22323233 : Blo 2173435 22323233 := bstep (se 2 (by rfl) ⟨8371212, by rfl⟩ : syracuseStep 22323233 = 16742425) B16742425
theorem B59528621 : Blo 2173435 59528621 := bstep (se 3 (by rfl) ⟨11161616, by rfl⟩ : syracuseStep 59528621 = 22323233) B22323233
theorem B39685747 : Blo 2173435 39685747 := bstep (se 1 (by rfl) ⟨29764310, by rfl⟩ : syracuseStep 39685747 = 59528621) B59528621
theorem B52914329 : Blo 2173435 52914329 := bstep (se 2 (by rfl) ⟨19842873, by rfl⟩ : syracuseStep 52914329 = 39685747) B39685747
theorem B35276219 : Blo 2173435 35276219 := bstep (se 1 (by rfl) ⟨26457164, by rfl⟩ : syracuseStep 35276219 = 52914329) B52914329
theorem B23517479 : Blo 2173435 23517479 := bstep (se 1 (by rfl) ⟨17638109, by rfl⟩ : syracuseStep 23517479 = 35276219) B35276219
theorem B15678319 : Blo 2173435 15678319 := bstep (se 1 (by rfl) ⟨11758739, by rfl⟩ : syracuseStep 15678319 = 23517479) B23517479
theorem B20904425 : Blo 2173435 20904425 := bstep (se 2 (by rfl) ⟨7839159, by rfl⟩ : syracuseStep 20904425 = 15678319) B15678319
theorem B13936283 : Blo 2173435 13936283 := bstep (se 1 (by rfl) ⟨10452212, by rfl⟩ : syracuseStep 13936283 = 20904425) B20904425
theorem B9290855 : Blo 2173435 9290855 := bstep (se 1 (by rfl) ⟨6968141, by rfl⟩ : syracuseStep 9290855 = 13936283) B13936283
theorem B6193903 : Blo 2173435 6193903 := bstep (se 1 (by rfl) ⟨4645427, by rfl⟩ : syracuseStep 6193903 = 9290855) B9290855
theorem B8258537 : Blo 2173435 8258537 := bstep (se 2 (by rfl) ⟨3096951, by rfl⟩ : syracuseStep 8258537 = 6193903) B6193903
theorem B5505691 : Blo 2173435 5505691 := bstep (se 1 (by rfl) ⟨4129268, by rfl⟩ : syracuseStep 5505691 = 8258537) B8258537
theorem B7340921 : Blo 2173435 7340921 := bstep (se 2 (by rfl) ⟨2752845, by rfl⟩ : syracuseStep 7340921 = 5505691) B5505691
theorem B4893947 : Blo 2173435 4893947 := bstep (se 1 (by rfl) ⟨3670460, by rfl⟩ : syracuseStep 4893947 = 7340921) B7340921
theorem B3262631 : Blo 2173435 3262631 := bstep (se 1 (by rfl) ⟨2446973, by rfl⟩ : syracuseStep 3262631 = 4893947) B4893947
theorem B2175087 : Blo 2173435 2175087 := bstep (se 1 (by rfl) ⟨1631315, by rfl⟩ : syracuseStep 2175087 = 3262631) B3262631
theorem B3262637 : Blo 2173435 3262637 := bbase (se 3 (by rfl) ⟨611744, by rfl⟩ : syracuseStep 3262637 = 1223489) (by norm_num)
theorem B2175091 : Blo 2173435 2175091 := bstep (se 1 (by rfl) ⟨1631318, by rfl⟩ : syracuseStep 2175091 = 3262637) B3262637
theorem B4893965 : Blo 2173435 4893965 := bbase (se 3 (by rfl) ⟨917618, by rfl⟩ : syracuseStep 4893965 = 1835237) (by norm_num)
theorem B3262643 : Blo 2173435 3262643 := bstep (se 1 (by rfl) ⟨2446982, by rfl⟩ : syracuseStep 3262643 = 4893965) B4893965
theorem B2175095 : Blo 2173435 2175095 := bstep (se 1 (by rfl) ⟨1631321, by rfl⟩ : syracuseStep 2175095 = 3262643) B3262643
theorem B2752861 : Blo 2173435 2752861 := bbase (se 3 (by rfl) ⟨516161, by rfl⟩ : syracuseStep 2752861 = 1032323) (by norm_num)
theorem B3670481 : Blo 2173435 3670481 := bstep (se 2 (by rfl) ⟨1376430, by rfl⟩ : syracuseStep 3670481 = 2752861) B2752861
theorem B2446987 : Blo 2173435 2446987 := bstep (se 1 (by rfl) ⟨1835240, by rfl⟩ : syracuseStep 2446987 = 3670481) B3670481
theorem B3262649 : Blo 2173435 3262649 := bstep (se 2 (by rfl) ⟨1223493, by rfl⟩ : syracuseStep 3262649 = 2446987) B2446987
theorem B2175099 : Blo 2173435 2175099 := bstep (se 1 (by rfl) ⟨1631324, by rfl⟩ : syracuseStep 2175099 = 3262649) B3262649
theorem B18581845 : Blo 2173435 18581845 := bbase (se 10 (by rfl) ⟨27219, by rfl⟩ : syracuseStep 18581845 = 54439) (by norm_num)
theorem B24775793 : Blo 2173435 24775793 := bstep (se 2 (by rfl) ⟨9290922, by rfl⟩ : syracuseStep 24775793 = 18581845) B18581845
theorem B16517195 : Blo 2173435 16517195 := bstep (se 1 (by rfl) ⟨12387896, by rfl⟩ : syracuseStep 16517195 = 24775793) B24775793
theorem B11011463 : Blo 2173435 11011463 := bstep (se 1 (by rfl) ⟨8258597, by rfl⟩ : syracuseStep 11011463 = 16517195) B16517195
theorem B7340975 : Blo 2173435 7340975 := bstep (se 1 (by rfl) ⟨5505731, by rfl⟩ : syracuseStep 7340975 = 11011463) B11011463
theorem B4893983 : Blo 2173435 4893983 := bstep (se 1 (by rfl) ⟨3670487, by rfl⟩ : syracuseStep 4893983 = 7340975) B7340975
theorem B3262655 : Blo 2173435 3262655 := bstep (se 1 (by rfl) ⟨2446991, by rfl⟩ : syracuseStep 3262655 = 4893983) B4893983
theorem B2175103 : Blo 2173435 2175103 := bstep (se 1 (by rfl) ⟨1631327, by rfl⟩ : syracuseStep 2175103 = 3262655) B3262655
theorem B3262661 : Blo 2173435 3262661 := bbase (se 4 (by rfl) ⟨305874, by rfl⟩ : syracuseStep 3262661 = 611749) (by norm_num)
theorem B2175107 : Blo 2173435 2175107 := bstep (se 1 (by rfl) ⟨1631330, by rfl⟩ : syracuseStep 2175107 = 3262661) B3262661
theorem B3670501 : Blo 2173435 3670501 := bbase (se 4 (by rfl) ⟨344109, by rfl⟩ : syracuseStep 3670501 = 688219) (by norm_num)
theorem B4894001 : Blo 2173435 4894001 := bstep (se 2 (by rfl) ⟨1835250, by rfl⟩ : syracuseStep 4894001 = 3670501) B3670501
theorem B3262667 : Blo 2173435 3262667 := bstep (se 1 (by rfl) ⟨2447000, by rfl⟩ : syracuseStep 3262667 = 4894001) B4894001
theorem B2175111 : Blo 2173435 2175111 := bstep (se 1 (by rfl) ⟨1631333, by rfl⟩ : syracuseStep 2175111 = 3262667) B3262667
theorem B2447005 : Blo 2173435 2447005 := bbase (se 3 (by rfl) ⟨458813, by rfl⟩ : syracuseStep 2447005 = 917627) (by norm_num)
theorem B3262673 : Blo 2173435 3262673 := bstep (se 2 (by rfl) ⟨1223502, by rfl⟩ : syracuseStep 3262673 = 2447005) B2447005
theorem B2175115 : Blo 2173435 2175115 := bstep (se 1 (by rfl) ⟨1631336, by rfl⟩ : syracuseStep 2175115 = 3262673) B3262673
theorem B7341029 : Blo 2173435 7341029 := bbase (se 4 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 7341029 = 1376443) (by norm_num)
theorem B4894019 : Blo 2173435 4894019 := bstep (se 1 (by rfl) ⟨3670514, by rfl⟩ : syracuseStep 4894019 = 7341029) B7341029
theorem B3262679 : Blo 2173435 3262679 := bstep (se 1 (by rfl) ⟨2447009, by rfl⟩ : syracuseStep 3262679 = 4894019) B4894019
theorem B2175119 : Blo 2173435 2175119 := bstep (se 1 (by rfl) ⟨1631339, by rfl⟩ : syracuseStep 2175119 = 3262679) B3262679
theorem B3262685 : Blo 2173435 3262685 := bbase (se 3 (by rfl) ⟨611753, by rfl⟩ : syracuseStep 3262685 = 1223507) (by norm_num)
theorem B2175123 : Blo 2173435 2175123 := bstep (se 1 (by rfl) ⟨1631342, by rfl⟩ : syracuseStep 2175123 = 3262685) B3262685
theorem B4894037 : Blo 2173435 4894037 := bbase (se 11 (by rfl) ⟨3584, by rfl⟩ : syracuseStep 4894037 = 7169) (by norm_num)
theorem B3262691 : Blo 2173435 3262691 := bstep (se 1 (by rfl) ⟨2447018, by rfl⟩ : syracuseStep 3262691 = 4894037) B4894037
theorem B2175127 : Blo 2173435 2175127 := bstep (se 1 (by rfl) ⟨1631345, by rfl⟩ : syracuseStep 2175127 = 3262691) B3262691
theorem B2322761 : Blo 2173435 2322761 := bbase (se 2 (by rfl) ⟨871035, by rfl⟩ : syracuseStep 2322761 = 1742071) (by norm_num)
theorem B6194029 : Blo 2173435 6194029 := bstep (se 3 (by rfl) ⟨1161380, by rfl⟩ : syracuseStep 6194029 = 2322761) B2322761
theorem B8258705 : Blo 2173435 8258705 := bstep (se 2 (by rfl) ⟨3097014, by rfl⟩ : syracuseStep 8258705 = 6194029) B6194029
theorem B5505803 : Blo 2173435 5505803 := bstep (se 1 (by rfl) ⟨4129352, by rfl⟩ : syracuseStep 5505803 = 8258705) B8258705
theorem B3670535 : Blo 2173435 3670535 := bstep (se 1 (by rfl) ⟨2752901, by rfl⟩ : syracuseStep 3670535 = 5505803) B5505803
theorem B2447023 : Blo 2173435 2447023 := bstep (se 1 (by rfl) ⟨1835267, by rfl⟩ : syracuseStep 2447023 = 3670535) B3670535
theorem B3262697 : Blo 2173435 3262697 := bstep (se 2 (by rfl) ⟨1223511, by rfl⟩ : syracuseStep 3262697 = 2447023) B2447023
theorem B2175131 : Blo 2173435 2175131 := bstep (se 1 (by rfl) ⟨1631348, by rfl⟩ : syracuseStep 2175131 = 3262697) B3262697
theorem B8371397 : Blo 2173435 8371397 := bbase (se 4 (by rfl) ⟨784818, by rfl⟩ : syracuseStep 8371397 = 1569637) (by norm_num)
theorem B5580931 : Blo 2173435 5580931 := bstep (se 1 (by rfl) ⟨4185698, by rfl⟩ : syracuseStep 5580931 = 8371397) B8371397
theorem B7441241 : Blo 2173435 7441241 := bstep (se 2 (by rfl) ⟨2790465, by rfl⟩ : syracuseStep 7441241 = 5580931) B5580931
theorem B19843309 : Blo 2173435 19843309 := bstep (se 3 (by rfl) ⟨3720620, by rfl⟩ : syracuseStep 19843309 = 7441241) B7441241
theorem B105830981 : Blo 2173435 105830981 := bstep (se 4 (by rfl) ⟨9921654, by rfl⟩ : syracuseStep 105830981 = 19843309) B19843309
theorem B70553987 : Blo 2173435 70553987 := bstep (se 1 (by rfl) ⟨52915490, by rfl⟩ : syracuseStep 70553987 = 105830981) B105830981
theorem B47035991 : Blo 2173435 47035991 := bstep (se 1 (by rfl) ⟨35276993, by rfl⟩ : syracuseStep 47035991 = 70553987) B70553987
theorem B31357327 : Blo 2173435 31357327 := bstep (se 1 (by rfl) ⟨23517995, by rfl⟩ : syracuseStep 31357327 = 47035991) B47035991
theorem B41809769 : Blo 2173435 41809769 := bstep (se 2 (by rfl) ⟨15678663, by rfl⟩ : syracuseStep 41809769 = 31357327) B31357327
theorem B27873179 : Blo 2173435 27873179 := bstep (se 1 (by rfl) ⟨20904884, by rfl⟩ : syracuseStep 27873179 = 41809769) B41809769
theorem B18582119 : Blo 2173435 18582119 := bstep (se 1 (by rfl) ⟨13936589, by rfl⟩ : syracuseStep 18582119 = 27873179) B27873179
theorem B12388079 : Blo 2173435 12388079 := bstep (se 1 (by rfl) ⟨9291059, by rfl⟩ : syracuseStep 12388079 = 18582119) B18582119
theorem B8258719 : Blo 2173435 8258719 := bstep (se 1 (by rfl) ⟨6194039, by rfl⟩ : syracuseStep 8258719 = 12388079) B12388079
theorem B11011625 : Blo 2173435 11011625 := bstep (se 2 (by rfl) ⟨4129359, by rfl⟩ : syracuseStep 11011625 = 8258719) B8258719
theorem B7341083 : Blo 2173435 7341083 := bstep (se 1 (by rfl) ⟨5505812, by rfl⟩ : syracuseStep 7341083 = 11011625) B11011625
theorem B4894055 : Blo 2173435 4894055 := bstep (se 1 (by rfl) ⟨3670541, by rfl⟩ : syracuseStep 4894055 = 7341083) B7341083
theorem B3262703 : Blo 2173435 3262703 := bstep (se 1 (by rfl) ⟨2447027, by rfl⟩ : syracuseStep 3262703 = 4894055) B4894055
theorem B2175135 : Blo 2173435 2175135 := bstep (se 1 (by rfl) ⟨1631351, by rfl⟩ : syracuseStep 2175135 = 3262703) B3262703
theorem B3262709 : Blo 2173435 3262709 := bbase (se 5 (by rfl) ⟨152939, by rfl⟩ : syracuseStep 3262709 = 305879) (by norm_num)
theorem B2175139 : Blo 2173435 2175139 := bstep (se 1 (by rfl) ⟨1631354, by rfl⟩ : syracuseStep 2175139 = 3262709) B3262709
theorem B2204821 : Blo 2173435 2204821 := bbase (se 6 (by rfl) ⟨51675, by rfl⟩ : syracuseStep 2204821 = 103351) (by norm_num)
theorem B2939761 : Blo 2173435 2939761 := bstep (se 2 (by rfl) ⟨1102410, by rfl⟩ : syracuseStep 2939761 = 2204821) B2204821
theorem B3919681 : Blo 2173435 3919681 := bstep (se 2 (by rfl) ⟨1469880, by rfl⟩ : syracuseStep 3919681 = 2939761) B2939761
theorem B20904965 : Blo 2173435 20904965 := bstep (se 4 (by rfl) ⟨1959840, by rfl⟩ : syracuseStep 20904965 = 3919681) B3919681
theorem B13936643 : Blo 2173435 13936643 := bstep (se 1 (by rfl) ⟨10452482, by rfl⟩ : syracuseStep 13936643 = 20904965) B20904965
theorem B9291095 : Blo 2173435 9291095 := bstep (se 1 (by rfl) ⟨6968321, by rfl⟩ : syracuseStep 9291095 = 13936643) B13936643
theorem B6194063 : Blo 2173435 6194063 := bstep (se 1 (by rfl) ⟨4645547, by rfl⟩ : syracuseStep 6194063 = 9291095) B9291095
theorem B4129375 : Blo 2173435 4129375 := bstep (se 1 (by rfl) ⟨3097031, by rfl⟩ : syracuseStep 4129375 = 6194063) B6194063
theorem B5505833 : Blo 2173435 5505833 := bstep (se 2 (by rfl) ⟨2064687, by rfl⟩ : syracuseStep 5505833 = 4129375) B4129375
theorem B3670555 : Blo 2173435 3670555 := bstep (se 1 (by rfl) ⟨2752916, by rfl⟩ : syracuseStep 3670555 = 5505833) B5505833
theorem B4894073 : Blo 2173435 4894073 := bstep (se 2 (by rfl) ⟨1835277, by rfl⟩ : syracuseStep 4894073 = 3670555) B3670555
theorem B3262715 : Blo 2173435 3262715 := bstep (se 1 (by rfl) ⟨2447036, by rfl⟩ : syracuseStep 3262715 = 4894073) B4894073
theorem B2175143 : Blo 2173435 2175143 := bstep (se 1 (by rfl) ⟨1631357, by rfl⟩ : syracuseStep 2175143 = 3262715) B3262715
theorem B2447041 : Blo 2173435 2447041 := bbase (se 2 (by rfl) ⟨917640, by rfl⟩ : syracuseStep 2447041 = 1835281) (by norm_num)
theorem B3262721 : Blo 2173435 3262721 := bstep (se 2 (by rfl) ⟨1223520, by rfl⟩ : syracuseStep 3262721 = 2447041) B2447041
theorem B2175147 : Blo 2173435 2175147 := bstep (se 1 (by rfl) ⟨1631360, by rfl⟩ : syracuseStep 2175147 = 3262721) B3262721
theorem B5505853 : Blo 2173435 5505853 := bbase (se 3 (by rfl) ⟨1032347, by rfl⟩ : syracuseStep 5505853 = 2064695) (by norm_num)
theorem B7341137 : Blo 2173435 7341137 := bstep (se 2 (by rfl) ⟨2752926, by rfl⟩ : syracuseStep 7341137 = 5505853) B5505853
theorem B4894091 : Blo 2173435 4894091 := bstep (se 1 (by rfl) ⟨3670568, by rfl⟩ : syracuseStep 4894091 = 7341137) B7341137
theorem B3262727 : Blo 2173435 3262727 := bstep (se 1 (by rfl) ⟨2447045, by rfl⟩ : syracuseStep 3262727 = 4894091) B4894091
theorem B2175151 : Blo 2173435 2175151 := bstep (se 1 (by rfl) ⟨1631363, by rfl⟩ : syracuseStep 2175151 = 3262727) B3262727
theorem B3262733 : Blo 2173435 3262733 := bbase (se 3 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 3262733 = 1223525) (by norm_num)
theorem B2175155 : Blo 2173435 2175155 := bstep (se 1 (by rfl) ⟨1631366, by rfl⟩ : syracuseStep 2175155 = 3262733) B3262733
theorem B4894109 : Blo 2173435 4894109 := bbase (se 3 (by rfl) ⟨917645, by rfl⟩ : syracuseStep 4894109 = 1835291) (by norm_num)
theorem B3262739 : Blo 2173435 3262739 := bstep (se 1 (by rfl) ⟨2447054, by rfl⟩ : syracuseStep 3262739 = 4894109) B4894109
theorem B2175159 : Blo 2173435 2175159 := bstep (se 1 (by rfl) ⟨1631369, by rfl⟩ : syracuseStep 2175159 = 3262739) B3262739
theorem B3670589 : Blo 2173435 3670589 := bbase (se 3 (by rfl) ⟨688235, by rfl⟩ : syracuseStep 3670589 = 1376471) (by norm_num)
theorem B2447059 : Blo 2173435 2447059 := bstep (se 1 (by rfl) ⟨1835294, by rfl⟩ : syracuseStep 2447059 = 3670589) B3670589
theorem B3262745 : Blo 2173435 3262745 := bstep (se 2 (by rfl) ⟨1223529, by rfl⟩ : syracuseStep 3262745 = 2447059) B2447059
theorem B2175163 : Blo 2173435 2175163 := bstep (se 1 (by rfl) ⟨1631372, by rfl⟩ : syracuseStep 2175163 = 3262745) B3262745
theorem B8819381 : Blo 2173435 8819381 := bbase (se 5 (by rfl) ⟨413408, by rfl⟩ : syracuseStep 8819381 = 826817) (by norm_num)
theorem B5879587 : Blo 2173435 5879587 := bstep (se 1 (by rfl) ⟨4409690, by rfl⟩ : syracuseStep 5879587 = 8819381) B8819381
theorem B7839449 : Blo 2173435 7839449 := bstep (se 2 (by rfl) ⟨2939793, by rfl⟩ : syracuseStep 7839449 = 5879587) B5879587
theorem B5226299 : Blo 2173435 5226299 := bstep (se 1 (by rfl) ⟨3919724, by rfl⟩ : syracuseStep 5226299 = 7839449) B7839449
theorem B3484199 : Blo 2173435 3484199 := bstep (se 1 (by rfl) ⟨2613149, by rfl⟩ : syracuseStep 3484199 = 5226299) B5226299
theorem B2322799 : Blo 2173435 2322799 := bstep (se 1 (by rfl) ⟨1742099, by rfl⟩ : syracuseStep 2322799 = 3484199) B3484199
theorem B12388261 : Blo 2173435 12388261 := bstep (se 4 (by rfl) ⟨1161399, by rfl⟩ : syracuseStep 12388261 = 2322799) B2322799
theorem B16517681 : Blo 2173435 16517681 := bstep (se 2 (by rfl) ⟨6194130, by rfl⟩ : syracuseStep 16517681 = 12388261) B12388261
theorem B11011787 : Blo 2173435 11011787 := bstep (se 1 (by rfl) ⟨8258840, by rfl⟩ : syracuseStep 11011787 = 16517681) B16517681
theorem B7341191 : Blo 2173435 7341191 := bstep (se 1 (by rfl) ⟨5505893, by rfl⟩ : syracuseStep 7341191 = 11011787) B11011787
theorem B4894127 : Blo 2173435 4894127 := bstep (se 1 (by rfl) ⟨3670595, by rfl⟩ : syracuseStep 4894127 = 7341191) B7341191
theorem B3262751 : Blo 2173435 3262751 := bstep (se 1 (by rfl) ⟨2447063, by rfl⟩ : syracuseStep 3262751 = 4894127) B4894127
theorem B2175167 : Blo 2173435 2175167 := bstep (se 1 (by rfl) ⟨1631375, by rfl⟩ : syracuseStep 2175167 = 3262751) B3262751
theorem B3262757 : Blo 2173435 3262757 := bbase (se 4 (by rfl) ⟨305883, by rfl⟩ : syracuseStep 3262757 = 611767) (by norm_num)
theorem B2175171 : Blo 2173435 2175171 := bstep (se 1 (by rfl) ⟨1631378, by rfl⟩ : syracuseStep 2175171 = 3262757) B3262757
theorem B2752957 : Blo 2173435 2752957 := bbase (se 3 (by rfl) ⟨516179, by rfl⟩ : syracuseStep 2752957 = 1032359) (by norm_num)
theorem B3670609 : Blo 2173435 3670609 := bstep (se 2 (by rfl) ⟨1376478, by rfl⟩ : syracuseStep 3670609 = 2752957) B2752957
theorem B4894145 : Blo 2173435 4894145 := bstep (se 2 (by rfl) ⟨1835304, by rfl⟩ : syracuseStep 4894145 = 3670609) B3670609
theorem B3262763 : Blo 2173435 3262763 := bstep (se 1 (by rfl) ⟨2447072, by rfl⟩ : syracuseStep 3262763 = 4894145) B4894145
theorem B2175175 : Blo 2173435 2175175 := bstep (se 1 (by rfl) ⟨1631381, by rfl⟩ : syracuseStep 2175175 = 3262763) B3262763
theorem B2447077 : Blo 2173435 2447077 := bbase (se 4 (by rfl) ⟨229413, by rfl⟩ : syracuseStep 2447077 = 458827) (by norm_num)
theorem B3262769 : Blo 2173435 3262769 := bstep (se 2 (by rfl) ⟨1223538, by rfl⟩ : syracuseStep 3262769 = 2447077) B2447077
theorem B2175179 : Blo 2173435 2175179 := bstep (se 1 (by rfl) ⟨1631384, by rfl⟩ : syracuseStep 2175179 = 3262769) B3262769
theorem B2613169 : Blo 2173435 2613169 := bbase (se 2 (by rfl) ⟨979938, by rfl⟩ : syracuseStep 2613169 = 1959877) (by norm_num)
theorem B3484225 : Blo 2173435 3484225 := bstep (se 2 (by rfl) ⟨1306584, by rfl⟩ : syracuseStep 3484225 = 2613169) B2613169
theorem B4645633 : Blo 2173435 4645633 := bstep (se 2 (by rfl) ⟨1742112, by rfl⟩ : syracuseStep 4645633 = 3484225) B3484225
theorem B6194177 : Blo 2173435 6194177 := bstep (se 2 (by rfl) ⟨2322816, by rfl⟩ : syracuseStep 6194177 = 4645633) B4645633
theorem B4129451 : Blo 2173435 4129451 := bstep (se 1 (by rfl) ⟨3097088, by rfl⟩ : syracuseStep 4129451 = 6194177) B6194177
theorem B2752967 : Blo 2173435 2752967 := bstep (se 1 (by rfl) ⟨2064725, by rfl⟩ : syracuseStep 2752967 = 4129451) B4129451
theorem B7341245 : Blo 2173435 7341245 := bstep (se 3 (by rfl) ⟨1376483, by rfl⟩ : syracuseStep 7341245 = 2752967) B2752967
theorem B4894163 : Blo 2173435 4894163 := bstep (se 1 (by rfl) ⟨3670622, by rfl⟩ : syracuseStep 4894163 = 7341245) B7341245
theorem B3262775 : Blo 2173435 3262775 := bstep (se 1 (by rfl) ⟨2447081, by rfl⟩ : syracuseStep 3262775 = 4894163) B4894163
theorem B2175183 : Blo 2173435 2175183 := bstep (se 1 (by rfl) ⟨1631387, by rfl⟩ : syracuseStep 2175183 = 3262775) B3262775
theorem B3262781 : Blo 2173435 3262781 := bbase (se 3 (by rfl) ⟨611771, by rfl⟩ : syracuseStep 3262781 = 1223543) (by norm_num)
theorem B2175187 : Blo 2173435 2175187 := bstep (se 1 (by rfl) ⟨1631390, by rfl⟩ : syracuseStep 2175187 = 3262781) B3262781
theorem B4894181 : Blo 2173435 4894181 := bbase (se 4 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 4894181 = 917659) (by norm_num)
theorem B3262787 : Blo 2173435 3262787 := bstep (se 1 (by rfl) ⟨2447090, by rfl⟩ : syracuseStep 3262787 = 4894181) B4894181
theorem B2175191 : Blo 2173435 2175191 := bstep (se 1 (by rfl) ⟨1631393, by rfl⟩ : syracuseStep 2175191 = 3262787) B3262787
theorem B5505965 : Blo 2173435 5505965 := bbase (se 3 (by rfl) ⟨1032368, by rfl⟩ : syracuseStep 5505965 = 2064737) (by norm_num)
theorem B3670643 : Blo 2173435 3670643 := bstep (se 1 (by rfl) ⟨2752982, by rfl⟩ : syracuseStep 3670643 = 5505965) B5505965
theorem B2447095 : Blo 2173435 2447095 := bstep (se 1 (by rfl) ⟨1835321, by rfl⟩ : syracuseStep 2447095 = 3670643) B3670643
theorem B3262793 : Blo 2173435 3262793 := bstep (se 2 (by rfl) ⟨1223547, by rfl⟩ : syracuseStep 3262793 = 2447095) B2447095
theorem B2175195 : Blo 2173435 2175195 := bstep (se 1 (by rfl) ⟨1631396, by rfl⟩ : syracuseStep 2175195 = 3262793) B3262793
theorem B6968501 : Blo 2173435 6968501 := bbase (se 5 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 6968501 = 653297) (by norm_num)
theorem B4645667 : Blo 2173435 4645667 := bstep (se 1 (by rfl) ⟨3484250, by rfl⟩ : syracuseStep 4645667 = 6968501) B6968501
theorem B3097111 : Blo 2173435 3097111 := bstep (se 1 (by rfl) ⟨2322833, by rfl⟩ : syracuseStep 3097111 = 4645667) B4645667
theorem B4129481 : Blo 2173435 4129481 := bstep (se 2 (by rfl) ⟨1548555, by rfl⟩ : syracuseStep 4129481 = 3097111) B3097111
theorem B11011949 : Blo 2173435 11011949 := bstep (se 3 (by rfl) ⟨2064740, by rfl⟩ : syracuseStep 11011949 = 4129481) B4129481
theorem B7341299 : Blo 2173435 7341299 := bstep (se 1 (by rfl) ⟨5505974, by rfl⟩ : syracuseStep 7341299 = 11011949) B11011949
theorem B4894199 : Blo 2173435 4894199 := bstep (se 1 (by rfl) ⟨3670649, by rfl⟩ : syracuseStep 4894199 = 7341299) B7341299
theorem B3262799 : Blo 2173435 3262799 := bstep (se 1 (by rfl) ⟨2447099, by rfl⟩ : syracuseStep 3262799 = 4894199) B4894199
theorem B2175199 : Blo 2173435 2175199 := bstep (se 1 (by rfl) ⟨1631399, by rfl⟩ : syracuseStep 2175199 = 3262799) B3262799
theorem B3262805 : Blo 2173435 3262805 := bbase (se 10 (by rfl) ⟨4779, by rfl⟩ : syracuseStep 3262805 = 9559) (by norm_num)
theorem B2175203 : Blo 2173435 2175203 := bstep (se 1 (by rfl) ⟨1631402, by rfl⟩ : syracuseStep 2175203 = 3262805) B3262805
theorem B6194245 : Blo 2173435 6194245 := bbase (se 4 (by rfl) ⟨580710, by rfl⟩ : syracuseStep 6194245 = 1161421) (by norm_num)
theorem B8258993 : Blo 2173435 8258993 := bstep (se 2 (by rfl) ⟨3097122, by rfl⟩ : syracuseStep 8258993 = 6194245) B6194245
theorem B5505995 : Blo 2173435 5505995 := bstep (se 1 (by rfl) ⟨4129496, by rfl⟩ : syracuseStep 5505995 = 8258993) B8258993
theorem B3670663 : Blo 2173435 3670663 := bstep (se 1 (by rfl) ⟨2752997, by rfl⟩ : syracuseStep 3670663 = 5505995) B5505995
theorem B4894217 : Blo 2173435 4894217 := bstep (se 2 (by rfl) ⟨1835331, by rfl⟩ : syracuseStep 4894217 = 3670663) B3670663
theorem B3262811 : Blo 2173435 3262811 := bstep (se 1 (by rfl) ⟨2447108, by rfl⟩ : syracuseStep 3262811 = 4894217) B4894217
theorem B2175207 : Blo 2173435 2175207 := bstep (se 1 (by rfl) ⟨1631405, by rfl⟩ : syracuseStep 2175207 = 3262811) B3262811
theorem B2447113 : Blo 2173435 2447113 := bbase (se 2 (by rfl) ⟨917667, by rfl⟩ : syracuseStep 2447113 = 1835335) (by norm_num)
theorem B3262817 : Blo 2173435 3262817 := bstep (se 2 (by rfl) ⟨1223556, by rfl⟩ : syracuseStep 3262817 = 2447113) B2447113
theorem B2175211 : Blo 2173435 2175211 := bstep (se 1 (by rfl) ⟨1631408, by rfl⟩ : syracuseStep 2175211 = 3262817) B3262817
theorem B7946581 : Blo 2173435 7946581 := bbase (se 10 (by rfl) ⟨11640, by rfl⟩ : syracuseStep 7946581 = 23281) (by norm_num)
theorem B10595441 : Blo 2173435 10595441 := bstep (se 2 (by rfl) ⟨3973290, by rfl⟩ : syracuseStep 10595441 = 7946581) B7946581
theorem B7063627 : Blo 2173435 7063627 := bstep (se 1 (by rfl) ⟨5297720, by rfl⟩ : syracuseStep 7063627 = 10595441) B10595441
theorem B9418169 : Blo 2173435 9418169 := bstep (se 2 (by rfl) ⟨3531813, by rfl⟩ : syracuseStep 9418169 = 7063627) B7063627
theorem B6278779 : Blo 2173435 6278779 := bstep (se 1 (by rfl) ⟨4709084, by rfl⟩ : syracuseStep 6278779 = 9418169) B9418169
theorem B33486821 : Blo 2173435 33486821 := bstep (se 4 (by rfl) ⟨3139389, by rfl⟩ : syracuseStep 33486821 = 6278779) B6278779
theorem B22324547 : Blo 2173435 22324547 := bstep (se 1 (by rfl) ⟨16743410, by rfl⟩ : syracuseStep 22324547 = 33486821) B33486821
theorem B14883031 : Blo 2173435 14883031 := bstep (se 1 (by rfl) ⟨11162273, by rfl⟩ : syracuseStep 14883031 = 22324547) B22324547
theorem B19844041 : Blo 2173435 19844041 := bstep (se 2 (by rfl) ⟨7441515, by rfl⟩ : syracuseStep 19844041 = 14883031) B14883031
theorem B26458721 : Blo 2173435 26458721 := bstep (se 2 (by rfl) ⟨9922020, by rfl⟩ : syracuseStep 26458721 = 19844041) B19844041
theorem B17639147 : Blo 2173435 17639147 := bstep (se 1 (by rfl) ⟨13229360, by rfl⟩ : syracuseStep 17639147 = 26458721) B26458721
theorem B11759431 : Blo 2173435 11759431 := bstep (se 1 (by rfl) ⟨8819573, by rfl⟩ : syracuseStep 11759431 = 17639147) B17639147
theorem B15679241 : Blo 2173435 15679241 := bstep (se 2 (by rfl) ⟨5879715, by rfl⟩ : syracuseStep 15679241 = 11759431) B11759431
theorem B10452827 : Blo 2173435 10452827 := bstep (se 1 (by rfl) ⟨7839620, by rfl⟩ : syracuseStep 10452827 = 15679241) B15679241
theorem B27874205 : Blo 2173435 27874205 := bstep (se 3 (by rfl) ⟨5226413, by rfl⟩ : syracuseStep 27874205 = 10452827) B10452827
theorem B18582803 : Blo 2173435 18582803 := bstep (se 1 (by rfl) ⟨13937102, by rfl⟩ : syracuseStep 18582803 = 27874205) B27874205
theorem B12388535 : Blo 2173435 12388535 := bstep (se 1 (by rfl) ⟨9291401, by rfl⟩ : syracuseStep 12388535 = 18582803) B18582803
theorem B8259023 : Blo 2173435 8259023 := bstep (se 1 (by rfl) ⟨6194267, by rfl⟩ : syracuseStep 8259023 = 12388535) B12388535
theorem B5506015 : Blo 2173435 5506015 := bstep (se 1 (by rfl) ⟨4129511, by rfl⟩ : syracuseStep 5506015 = 8259023) B8259023
theorem B7341353 : Blo 2173435 7341353 := bstep (se 2 (by rfl) ⟨2753007, by rfl⟩ : syracuseStep 7341353 = 5506015) B5506015
theorem B4894235 : Blo 2173435 4894235 := bstep (se 1 (by rfl) ⟨3670676, by rfl⟩ : syracuseStep 4894235 = 7341353) B7341353
theorem B3262823 : Blo 2173435 3262823 := bstep (se 1 (by rfl) ⟨2447117, by rfl⟩ : syracuseStep 3262823 = 4894235) B4894235
theorem B2175215 : Blo 2173435 2175215 := bstep (se 1 (by rfl) ⟨1631411, by rfl⟩ : syracuseStep 2175215 = 3262823) B3262823
theorem B3262829 : Blo 2173435 3262829 := bbase (se 3 (by rfl) ⟨611780, by rfl⟩ : syracuseStep 3262829 = 1223561) (by norm_num)
theorem B2175219 : Blo 2173435 2175219 := bstep (se 1 (by rfl) ⟨1631414, by rfl⟩ : syracuseStep 2175219 = 3262829) B3262829
theorem B4894253 : Blo 2173435 4894253 := bbase (se 3 (by rfl) ⟨917672, by rfl⟩ : syracuseStep 4894253 = 1835345) (by norm_num)
theorem B3262835 : Blo 2173435 3262835 := bstep (se 1 (by rfl) ⟨2447126, by rfl⟩ : syracuseStep 3262835 = 4894253) B4894253
theorem B2175223 : Blo 2173435 2175223 := bstep (se 1 (by rfl) ⟨1631417, by rfl⟩ : syracuseStep 2175223 = 3262835) B3262835
theorem B4185877 : Blo 2173435 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B5581169 : Blo 2173435 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B3720779 : Blo 2173435 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B39688309 : Blo 2173435 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B52917745 : Blo 2173435 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B70556993 : Blo 2173435 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B47037995 : Blo 2173435 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B31358663 : Blo 2173435 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B20905775 : Blo 2173435 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B13937183 : Blo 2173435 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B9291455 : Blo 2173435 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B6194303 : Blo 2173435 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B4129535 : Blo 2173435 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B2753023 : Blo 2173435 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B3670697 : Blo 2173435 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B2447131 : Blo 2173435 2447131 := bstep (se 1 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 2447131 = 3670697) B3670697
theorem B3262841 : Blo 2173435 3262841 := bstep (se 2 (by rfl) ⟨1223565, by rfl⟩ : syracuseStep 3262841 = 2447131) B2447131
theorem B2175227 : Blo 2173435 2175227 := bstep (se 1 (by rfl) ⟨1631420, by rfl⟩ : syracuseStep 2175227 = 3262841) B3262841
theorem B3484301 : Blo 2173435 3484301 := bbase (se 3 (by rfl) ⟨653306, by rfl⟩ : syracuseStep 3484301 = 1306613) (by norm_num)
theorem B37165877 : Blo 2173435 37165877 := bstep (se 5 (by rfl) ⟨1742150, by rfl⟩ : syracuseStep 37165877 = 3484301) B3484301
theorem B24777251 : Blo 2173435 24777251 := bstep (se 1 (by rfl) ⟨18582938, by rfl⟩ : syracuseStep 24777251 = 37165877) B37165877
theorem B16518167 : Blo 2173435 16518167 := bstep (se 1 (by rfl) ⟨12388625, by rfl⟩ : syracuseStep 16518167 = 24777251) B24777251
theorem B11012111 : Blo 2173435 11012111 := bstep (se 1 (by rfl) ⟨8259083, by rfl⟩ : syracuseStep 11012111 = 16518167) B16518167
theorem B7341407 : Blo 2173435 7341407 := bstep (se 1 (by rfl) ⟨5506055, by rfl⟩ : syracuseStep 7341407 = 11012111) B11012111
theorem B4894271 : Blo 2173435 4894271 := bstep (se 1 (by rfl) ⟨3670703, by rfl⟩ : syracuseStep 4894271 = 7341407) B7341407
theorem B3262847 : Blo 2173435 3262847 := bstep (se 1 (by rfl) ⟨2447135, by rfl⟩ : syracuseStep 3262847 = 4894271) B4894271
theorem B2175231 : Blo 2173435 2175231 := bstep (se 1 (by rfl) ⟨1631423, by rfl⟩ : syracuseStep 2175231 = 3262847) B3262847
theorem B3262853 : Blo 2173435 3262853 := bbase (se 4 (by rfl) ⟨305892, by rfl⟩ : syracuseStep 3262853 = 611785) (by norm_num)
theorem B2175235 : Blo 2173435 2175235 := bstep (se 1 (by rfl) ⟨1631426, by rfl⟩ : syracuseStep 2175235 = 3262853) B3262853
theorem B3670717 : Blo 2173435 3670717 := bbase (se 3 (by rfl) ⟨688259, by rfl⟩ : syracuseStep 3670717 = 1376519) (by norm_num)
theorem B4894289 : Blo 2173435 4894289 := bstep (se 2 (by rfl) ⟨1835358, by rfl⟩ : syracuseStep 4894289 = 3670717) B3670717
theorem B3262859 : Blo 2173435 3262859 := bstep (se 1 (by rfl) ⟨2447144, by rfl⟩ : syracuseStep 3262859 = 4894289) B4894289
theorem B2175239 : Blo 2173435 2175239 := bstep (se 1 (by rfl) ⟨1631429, by rfl⟩ : syracuseStep 2175239 = 3262859) B3262859
theorem B2447149 : Blo 2173435 2447149 := bbase (se 3 (by rfl) ⟨458840, by rfl⟩ : syracuseStep 2447149 = 917681) (by norm_num)
theorem B3262865 : Blo 2173435 3262865 := bstep (se 2 (by rfl) ⟨1223574, by rfl⟩ : syracuseStep 3262865 = 2447149) B2447149
theorem B2175243 : Blo 2173435 2175243 := bstep (se 1 (by rfl) ⟨1631432, by rfl⟩ : syracuseStep 2175243 = 3262865) B3262865
theorem B7341461 : Blo 2173435 7341461 := bbase (se 6 (by rfl) ⟨172065, by rfl⟩ : syracuseStep 7341461 = 344131) (by norm_num)
theorem B4894307 : Blo 2173435 4894307 := bstep (se 1 (by rfl) ⟨3670730, by rfl⟩ : syracuseStep 4894307 = 7341461) B7341461
theorem B3262871 : Blo 2173435 3262871 := bstep (se 1 (by rfl) ⟨2447153, by rfl⟩ : syracuseStep 3262871 = 4894307) B4894307
theorem B2175247 : Blo 2173435 2175247 := bstep (se 1 (by rfl) ⟨1631435, by rfl⟩ : syracuseStep 2175247 = 3262871) B3262871
theorem B3262877 : Blo 2173435 3262877 := bbase (se 3 (by rfl) ⟨611789, by rfl⟩ : syracuseStep 3262877 = 1223579) (by norm_num)
theorem B2175251 : Blo 2173435 2175251 := bstep (se 1 (by rfl) ⟨1631438, by rfl⟩ : syracuseStep 2175251 = 3262877) B3262877
theorem B4894325 : Blo 2173435 4894325 := bbase (se 5 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 4894325 = 458843) (by norm_num)
theorem B3262883 : Blo 2173435 3262883 := bstep (se 1 (by rfl) ⟨2447162, by rfl⟩ : syracuseStep 3262883 = 4894325) B4894325
theorem B2175255 : Blo 2173435 2175255 := bstep (se 1 (by rfl) ⟨1631441, by rfl⟩ : syracuseStep 2175255 = 3262883) B3262883
theorem B6968693 : Blo 2173435 6968693 := bbase (se 5 (by rfl) ⟨326657, by rfl⟩ : syracuseStep 6968693 = 653315) (by norm_num)
theorem B18583181 : Blo 2173435 18583181 := bstep (se 3 (by rfl) ⟨3484346, by rfl⟩ : syracuseStep 18583181 = 6968693) B6968693
theorem B12388787 : Blo 2173435 12388787 := bstep (se 1 (by rfl) ⟨9291590, by rfl⟩ : syracuseStep 12388787 = 18583181) B18583181
theorem B8259191 : Blo 2173435 8259191 := bstep (se 1 (by rfl) ⟨6194393, by rfl⟩ : syracuseStep 8259191 = 12388787) B12388787
theorem B5506127 : Blo 2173435 5506127 := bstep (se 1 (by rfl) ⟨4129595, by rfl⟩ : syracuseStep 5506127 = 8259191) B8259191
theorem B3670751 : Blo 2173435 3670751 := bstep (se 1 (by rfl) ⟨2753063, by rfl⟩ : syracuseStep 3670751 = 5506127) B5506127
theorem B2447167 : Blo 2173435 2447167 := bstep (se 1 (by rfl) ⟨1835375, by rfl⟩ : syracuseStep 2447167 = 3670751) B3670751
theorem B3262889 : Blo 2173435 3262889 := bstep (se 2 (by rfl) ⟨1223583, by rfl⟩ : syracuseStep 3262889 = 2447167) B2447167
theorem B2175259 : Blo 2173435 2175259 := bstep (se 1 (by rfl) ⟨1631444, by rfl⟩ : syracuseStep 2175259 = 3262889) B3262889
theorem B8259205 : Blo 2173435 8259205 := bbase (se 4 (by rfl) ⟨774300, by rfl⟩ : syracuseStep 8259205 = 1548601) (by norm_num)
theorem B11012273 : Blo 2173435 11012273 := bstep (se 2 (by rfl) ⟨4129602, by rfl⟩ : syracuseStep 11012273 = 8259205) B8259205
theorem B7341515 : Blo 2173435 7341515 := bstep (se 1 (by rfl) ⟨5506136, by rfl⟩ : syracuseStep 7341515 = 11012273) B11012273
theorem B4894343 : Blo 2173435 4894343 := bstep (se 1 (by rfl) ⟨3670757, by rfl⟩ : syracuseStep 4894343 = 7341515) B7341515
theorem B3262895 : Blo 2173435 3262895 := bstep (se 1 (by rfl) ⟨2447171, by rfl⟩ : syracuseStep 3262895 = 4894343) B4894343
theorem B2175263 : Blo 2173435 2175263 := bstep (se 1 (by rfl) ⟨1631447, by rfl⟩ : syracuseStep 2175263 = 3262895) B3262895
theorem B3262901 : Blo 2173435 3262901 := bbase (se 5 (by rfl) ⟨152948, by rfl⟩ : syracuseStep 3262901 = 305897) (by norm_num)
theorem B2175267 : Blo 2173435 2175267 := bstep (se 1 (by rfl) ⟨1631450, by rfl⟩ : syracuseStep 2175267 = 3262901) B3262901
theorem B5506157 : Blo 2173435 5506157 := bbase (se 3 (by rfl) ⟨1032404, by rfl⟩ : syracuseStep 5506157 = 2064809) (by norm_num)
theorem B3670771 : Blo 2173435 3670771 := bstep (se 1 (by rfl) ⟨2753078, by rfl⟩ : syracuseStep 3670771 = 5506157) B5506157
theorem B4894361 : Blo 2173435 4894361 := bstep (se 2 (by rfl) ⟨1835385, by rfl⟩ : syracuseStep 4894361 = 3670771) B3670771
theorem B3262907 : Blo 2173435 3262907 := bstep (se 1 (by rfl) ⟨2447180, by rfl⟩ : syracuseStep 3262907 = 4894361) B4894361
theorem B2175271 : Blo 2173435 2175271 := bstep (se 1 (by rfl) ⟨1631453, by rfl⟩ : syracuseStep 2175271 = 3262907) B3262907
theorem B2447185 : Blo 2173435 2447185 := bbase (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) (by norm_num)
theorem B3262913 : Blo 2173435 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B2175275 : Blo 2173435 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B8371957 : Blo 2173435 8371957 := bbase (se 5 (by rfl) ⟨392435, by rfl⟩ : syracuseStep 8371957 = 784871) (by norm_num)
theorem B11162609 : Blo 2173435 11162609 := bstep (se 2 (by rfl) ⟨4185978, by rfl⟩ : syracuseStep 11162609 = 8371957) B8371957
theorem B7441739 : Blo 2173435 7441739 := bstep (se 1 (by rfl) ⟨5581304, by rfl⟩ : syracuseStep 7441739 = 11162609) B11162609
theorem B4961159 : Blo 2173435 4961159 := bstep (se 1 (by rfl) ⟨3720869, by rfl⟩ : syracuseStep 4961159 = 7441739) B7441739
theorem B3307439 : Blo 2173435 3307439 := bstep (se 1 (by rfl) ⟨2480579, by rfl⟩ : syracuseStep 3307439 = 4961159) B4961159
theorem B8819837 : Blo 2173435 8819837 := bstep (se 3 (by rfl) ⟨1653719, by rfl⟩ : syracuseStep 8819837 = 3307439) B3307439
theorem B5879891 : Blo 2173435 5879891 := bstep (se 1 (by rfl) ⟨4409918, by rfl⟩ : syracuseStep 5879891 = 8819837) B8819837
theorem B3919927 : Blo 2173435 3919927 := bstep (se 1 (by rfl) ⟨2939945, by rfl⟩ : syracuseStep 3919927 = 5879891) B5879891
theorem B5226569 : Blo 2173435 5226569 := bstep (se 2 (by rfl) ⟨1959963, by rfl⟩ : syracuseStep 5226569 = 3919927) B3919927
theorem B3484379 : Blo 2173435 3484379 := bstep (se 1 (by rfl) ⟨2613284, by rfl⟩ : syracuseStep 3484379 = 5226569) B5226569
theorem B2322919 : Blo 2173435 2322919 := bstep (se 1 (by rfl) ⟨1742189, by rfl⟩ : syracuseStep 2322919 = 3484379) B3484379
theorem B3097225 : Blo 2173435 3097225 := bstep (se 2 (by rfl) ⟨1161459, by rfl⟩ : syracuseStep 3097225 = 2322919) B2322919
theorem B4129633 : Blo 2173435 4129633 := bstep (se 2 (by rfl) ⟨1548612, by rfl⟩ : syracuseStep 4129633 = 3097225) B3097225
theorem B5506177 : Blo 2173435 5506177 := bstep (se 2 (by rfl) ⟨2064816, by rfl⟩ : syracuseStep 5506177 = 4129633) B4129633
theorem B7341569 : Blo 2173435 7341569 := bstep (se 2 (by rfl) ⟨2753088, by rfl⟩ : syracuseStep 7341569 = 5506177) B5506177
theorem B4894379 : Blo 2173435 4894379 := bstep (se 1 (by rfl) ⟨3670784, by rfl⟩ : syracuseStep 4894379 = 7341569) B7341569
theorem B3262919 : Blo 2173435 3262919 := bstep (se 1 (by rfl) ⟨2447189, by rfl⟩ : syracuseStep 3262919 = 4894379) B4894379
theorem B2175279 : Blo 2173435 2175279 := bstep (se 1 (by rfl) ⟨1631459, by rfl⟩ : syracuseStep 2175279 = 3262919) B3262919
theorem B3262925 : Blo 2173435 3262925 := bbase (se 3 (by rfl) ⟨611798, by rfl⟩ : syracuseStep 3262925 = 1223597) (by norm_num)
theorem B2175283 : Blo 2173435 2175283 := bstep (se 1 (by rfl) ⟨1631462, by rfl⟩ : syracuseStep 2175283 = 3262925) B3262925
theorem B4894397 : Blo 2173435 4894397 := bbase (se 3 (by rfl) ⟨917699, by rfl⟩ : syracuseStep 4894397 = 1835399) (by norm_num)
theorem B3262931 : Blo 2173435 3262931 := bstep (se 1 (by rfl) ⟨2447198, by rfl⟩ : syracuseStep 3262931 = 4894397) B4894397
theorem B2175287 : Blo 2173435 2175287 := bstep (se 1 (by rfl) ⟨1631465, by rfl⟩ : syracuseStep 2175287 = 3262931) B3262931
theorem B3670805 : Blo 2173435 3670805 := bbase (se 6 (by rfl) ⟨86034, by rfl⟩ : syracuseStep 3670805 = 172069) (by norm_num)
theorem B2447203 : Blo 2173435 2447203 := bstep (se 1 (by rfl) ⟨1835402, by rfl⟩ : syracuseStep 2447203 = 3670805) B3670805
theorem B3262937 : Blo 2173435 3262937 := bstep (se 2 (by rfl) ⟨1223601, by rfl⟩ : syracuseStep 3262937 = 2447203) B2447203
theorem B2175291 : Blo 2173435 2175291 := bstep (se 1 (by rfl) ⟨1631468, by rfl⟩ : syracuseStep 2175291 = 3262937) B3262937
theorem B9418517 : Blo 2173435 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B6279011 : Blo 2173435 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B4186007 : Blo 2173435 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B2790671 : Blo 2173435 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7441789 : Blo 2173435 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B9922385 : Blo 2173435 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B26459693 : Blo 2173435 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B17639795 : Blo 2173435 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B47039453 : Blo 2173435 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B31359635 : Blo 2173435 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B20906423 : Blo 2173435 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B13937615 : Blo 2173435 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B9291743 : Blo 2173435 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B6194495 : Blo 2173435 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B16518653 : Blo 2173435 16518653 := bstep (se 3 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 16518653 = 6194495) B6194495
theorem B11012435 : Blo 2173435 11012435 := bstep (se 1 (by rfl) ⟨8259326, by rfl⟩ : syracuseStep 11012435 = 16518653) B16518653
theorem B7341623 : Blo 2173435 7341623 := bstep (se 1 (by rfl) ⟨5506217, by rfl⟩ : syracuseStep 7341623 = 11012435) B11012435
theorem B4894415 : Blo 2173435 4894415 := bstep (se 1 (by rfl) ⟨3670811, by rfl⟩ : syracuseStep 4894415 = 7341623) B7341623
theorem B3262943 : Blo 2173435 3262943 := bstep (se 1 (by rfl) ⟨2447207, by rfl⟩ : syracuseStep 3262943 = 4894415) B4894415
theorem B2175295 : Blo 2173435 2175295 := bstep (se 1 (by rfl) ⟨1631471, by rfl⟩ : syracuseStep 2175295 = 3262943) B3262943
theorem B3262949 : Blo 2173435 3262949 := bbase (se 4 (by rfl) ⟨305901, by rfl⟩ : syracuseStep 3262949 = 611803) (by norm_num)
theorem B2175299 : Blo 2173435 2175299 := bstep (se 1 (by rfl) ⟨1631474, by rfl⟩ : syracuseStep 2175299 = 3262949) B3262949
theorem B2613313 : Blo 2173435 2613313 := bbase (se 2 (by rfl) ⟨979992, by rfl⟩ : syracuseStep 2613313 = 1959985) (by norm_num)
theorem B13937669 : Blo 2173435 13937669 := bstep (se 4 (by rfl) ⟨1306656, by rfl⟩ : syracuseStep 13937669 = 2613313) B2613313
theorem B9291779 : Blo 2173435 9291779 := bstep (se 1 (by rfl) ⟨6968834, by rfl⟩ : syracuseStep 9291779 = 13937669) B13937669
theorem B6194519 : Blo 2173435 6194519 := bstep (se 1 (by rfl) ⟨4645889, by rfl⟩ : syracuseStep 6194519 = 9291779) B9291779
theorem B4129679 : Blo 2173435 4129679 := bstep (se 1 (by rfl) ⟨3097259, by rfl⟩ : syracuseStep 4129679 = 6194519) B6194519
theorem B2753119 : Blo 2173435 2753119 := bstep (se 1 (by rfl) ⟨2064839, by rfl⟩ : syracuseStep 2753119 = 4129679) B4129679
theorem B3670825 : Blo 2173435 3670825 := bstep (se 2 (by rfl) ⟨1376559, by rfl⟩ : syracuseStep 3670825 = 2753119) B2753119
theorem B4894433 : Blo 2173435 4894433 := bstep (se 2 (by rfl) ⟨1835412, by rfl⟩ : syracuseStep 4894433 = 3670825) B3670825
theorem B3262955 : Blo 2173435 3262955 := bstep (se 1 (by rfl) ⟨2447216, by rfl⟩ : syracuseStep 3262955 = 4894433) B4894433
theorem B2175303 : Blo 2173435 2175303 := bstep (se 1 (by rfl) ⟨1631477, by rfl⟩ : syracuseStep 2175303 = 3262955) B3262955
theorem B2447221 : Blo 2173435 2447221 := bbase (se 5 (by rfl) ⟨114713, by rfl⟩ : syracuseStep 2447221 = 229427) (by norm_num)
theorem B3262961 : Blo 2173435 3262961 := bstep (se 2 (by rfl) ⟨1223610, by rfl⟩ : syracuseStep 3262961 = 2447221) B2447221
theorem B2175307 : Blo 2173435 2175307 := bstep (se 1 (by rfl) ⟨1631480, by rfl⟩ : syracuseStep 2175307 = 3262961) B3262961
theorem B2753129 : Blo 2173435 2753129 := bbase (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) (by norm_num)
theorem B7341677 : Blo 2173435 7341677 := bstep (se 3 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 7341677 = 2753129) B2753129
theorem B4894451 : Blo 2173435 4894451 := bstep (se 1 (by rfl) ⟨3670838, by rfl⟩ : syracuseStep 4894451 = 7341677) B7341677
theorem B3262967 : Blo 2173435 3262967 := bstep (se 1 (by rfl) ⟨2447225, by rfl⟩ : syracuseStep 3262967 = 4894451) B4894451
theorem B2175311 : Blo 2173435 2175311 := bstep (se 1 (by rfl) ⟨1631483, by rfl⟩ : syracuseStep 2175311 = 3262967) B3262967
theorem B3262973 : Blo 2173435 3262973 := bbase (se 3 (by rfl) ⟨611807, by rfl⟩ : syracuseStep 3262973 = 1223615) (by norm_num)
theorem B2175315 : Blo 2173435 2175315 := bstep (se 1 (by rfl) ⟨1631486, by rfl⟩ : syracuseStep 2175315 = 3262973) B3262973
theorem B4894469 : Blo 2173435 4894469 := bbase (se 4 (by rfl) ⟨458856, by rfl⟩ : syracuseStep 4894469 = 917713) (by norm_num)
theorem B3262979 : Blo 2173435 3262979 := bstep (se 1 (by rfl) ⟨2447234, by rfl⟩ : syracuseStep 3262979 = 4894469) B4894469
theorem B2175319 : Blo 2173435 2175319 := bstep (se 1 (by rfl) ⟨1631489, by rfl⟩ : syracuseStep 2175319 = 3262979) B3262979
theorem B4129717 : Blo 2173435 4129717 := bbase (se 5 (by rfl) ⟨193580, by rfl⟩ : syracuseStep 4129717 = 387161) (by norm_num)
theorem B5506289 : Blo 2173435 5506289 := bstep (se 2 (by rfl) ⟨2064858, by rfl⟩ : syracuseStep 5506289 = 4129717) B4129717
theorem B3670859 : Blo 2173435 3670859 := bstep (se 1 (by rfl) ⟨2753144, by rfl⟩ : syracuseStep 3670859 = 5506289) B5506289
theorem B2447239 : Blo 2173435 2447239 := bstep (se 1 (by rfl) ⟨1835429, by rfl⟩ : syracuseStep 2447239 = 3670859) B3670859
theorem B3262985 : Blo 2173435 3262985 := bstep (se 2 (by rfl) ⟨1223619, by rfl⟩ : syracuseStep 3262985 = 2447239) B2447239
theorem B2175323 : Blo 2173435 2175323 := bstep (se 1 (by rfl) ⟨1631492, by rfl⟩ : syracuseStep 2175323 = 3262985) B3262985
theorem B11012597 : Blo 2173435 11012597 := bbase (se 5 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 11012597 = 1032431) (by norm_num)
theorem B7341731 : Blo 2173435 7341731 := bstep (se 1 (by rfl) ⟨5506298, by rfl⟩ : syracuseStep 7341731 = 11012597) B11012597
theorem B4894487 : Blo 2173435 4894487 := bstep (se 1 (by rfl) ⟨3670865, by rfl⟩ : syracuseStep 4894487 = 7341731) B7341731
theorem B3262991 : Blo 2173435 3262991 := bstep (se 1 (by rfl) ⟨2447243, by rfl⟩ : syracuseStep 3262991 = 4894487) B4894487
theorem B2175327 : Blo 2173435 2175327 := bstep (se 1 (by rfl) ⟨1631495, by rfl⟩ : syracuseStep 2175327 = 3262991) B3262991
theorem B3262997 : Blo 2173435 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B2175331 : Blo 2173435 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B18583829 : Blo 2173435 18583829 := bbase (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) (by norm_num)
theorem B12389219 : Blo 2173435 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B8259479 : Blo 2173435 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B5506319 : Blo 2173435 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B3670879 : Blo 2173435 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B4894505 : Blo 2173435 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B3263003 : Blo 2173435 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B2175335 : Blo 2173435 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B2447257 : Blo 2173435 2447257 := bbase (se 2 (by rfl) ⟨917721, by rfl⟩ : syracuseStep 2447257 = 1835443) (by norm_num)
theorem B3263009 : Blo 2173435 3263009 := bstep (se 2 (by rfl) ⟨1223628, by rfl⟩ : syracuseStep 3263009 = 2447257) B2447257
theorem B2175339 : Blo 2173435 2175339 := bstep (se 1 (by rfl) ⟨1631504, by rfl⟩ : syracuseStep 2175339 = 3263009) B3263009
theorem B8259509 : Blo 2173435 8259509 := bbase (se 5 (by rfl) ⟨387164, by rfl⟩ : syracuseStep 8259509 = 774329) (by norm_num)
theorem B5506339 : Blo 2173435 5506339 := bstep (se 1 (by rfl) ⟨4129754, by rfl⟩ : syracuseStep 5506339 = 8259509) B8259509
theorem B7341785 : Blo 2173435 7341785 := bstep (se 2 (by rfl) ⟨2753169, by rfl⟩ : syracuseStep 7341785 = 5506339) B5506339
theorem B4894523 : Blo 2173435 4894523 := bstep (se 1 (by rfl) ⟨3670892, by rfl⟩ : syracuseStep 4894523 = 7341785) B7341785
theorem B3263015 : Blo 2173435 3263015 := bstep (se 1 (by rfl) ⟨2447261, by rfl⟩ : syracuseStep 3263015 = 4894523) B4894523
theorem B2175343 : Blo 2173435 2175343 := bstep (se 1 (by rfl) ⟨1631507, by rfl⟩ : syracuseStep 2175343 = 3263015) B3263015
theorem B3263021 : Blo 2173435 3263021 := bbase (se 3 (by rfl) ⟨611816, by rfl⟩ : syracuseStep 3263021 = 1223633) (by norm_num)
theorem B2175347 : Blo 2173435 2175347 := bstep (se 1 (by rfl) ⟨1631510, by rfl⟩ : syracuseStep 2175347 = 3263021) B3263021
theorem B4894541 : Blo 2173435 4894541 := bbase (se 3 (by rfl) ⟨917726, by rfl⟩ : syracuseStep 4894541 = 1835453) (by norm_num)
theorem B3263027 : Blo 2173435 3263027 := bstep (se 1 (by rfl) ⟨2447270, by rfl⟩ : syracuseStep 3263027 = 4894541) B4894541
theorem B2175351 : Blo 2173435 2175351 := bstep (se 1 (by rfl) ⟨1631513, by rfl⟩ : syracuseStep 2175351 = 3263027) B3263027
theorem B2753185 : Blo 2173435 2753185 := bbase (se 2 (by rfl) ⟨1032444, by rfl⟩ : syracuseStep 2753185 = 2064889) (by norm_num)
theorem B3670913 : Blo 2173435 3670913 := bstep (se 2 (by rfl) ⟨1376592, by rfl⟩ : syracuseStep 3670913 = 2753185) B2753185
theorem B2447275 : Blo 2173435 2447275 := bstep (se 1 (by rfl) ⟨1835456, by rfl⟩ : syracuseStep 2447275 = 3670913) B3670913
theorem B3263033 : Blo 2173435 3263033 := bstep (se 2 (by rfl) ⟨1223637, by rfl⟩ : syracuseStep 3263033 = 2447275) B2447275
theorem B2175355 : Blo 2173435 2175355 := bstep (se 1 (by rfl) ⟨1631516, by rfl⟩ : syracuseStep 2175355 = 3263033) B3263033
theorem B24778709 : Blo 2173435 24778709 := bbase (se 7 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 24778709 = 580751) (by norm_num)
theorem B16519139 : Blo 2173435 16519139 := bstep (se 1 (by rfl) ⟨12389354, by rfl⟩ : syracuseStep 16519139 = 24778709) B24778709
theorem B11012759 : Blo 2173435 11012759 := bstep (se 1 (by rfl) ⟨8259569, by rfl⟩ : syracuseStep 11012759 = 16519139) B16519139
theorem B7341839 : Blo 2173435 7341839 := bstep (se 1 (by rfl) ⟨5506379, by rfl⟩ : syracuseStep 7341839 = 11012759) B11012759
theorem B4894559 : Blo 2173435 4894559 := bstep (se 1 (by rfl) ⟨3670919, by rfl⟩ : syracuseStep 4894559 = 7341839) B7341839
theorem B3263039 : Blo 2173435 3263039 := bstep (se 1 (by rfl) ⟨2447279, by rfl⟩ : syracuseStep 3263039 = 4894559) B4894559
theorem B2175359 : Blo 2173435 2175359 := bstep (se 1 (by rfl) ⟨1631519, by rfl⟩ : syracuseStep 2175359 = 3263039) B3263039
theorem B3263045 : Blo 2173435 3263045 := bbase (se 4 (by rfl) ⟨305910, by rfl⟩ : syracuseStep 3263045 = 611821) (by norm_num)
theorem B2175363 : Blo 2173435 2175363 := bstep (se 1 (by rfl) ⟨1631522, by rfl⟩ : syracuseStep 2175363 = 3263045) B3263045
theorem B3670933 : Blo 2173435 3670933 := bbase (se 6 (by rfl) ⟨86037, by rfl⟩ : syracuseStep 3670933 = 172075) (by norm_num)
theorem B4894577 : Blo 2173435 4894577 := bstep (se 2 (by rfl) ⟨1835466, by rfl⟩ : syracuseStep 4894577 = 3670933) B3670933
theorem B3263051 : Blo 2173435 3263051 := bstep (se 1 (by rfl) ⟨2447288, by rfl⟩ : syracuseStep 3263051 = 4894577) B4894577
theorem B2175367 : Blo 2173435 2175367 := bstep (se 1 (by rfl) ⟨1631525, by rfl⟩ : syracuseStep 2175367 = 3263051) B3263051
theorem B2447293 : Blo 2173435 2447293 := bbase (se 3 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 2447293 = 917735) (by norm_num)
theorem B3263057 : Blo 2173435 3263057 := bstep (se 2 (by rfl) ⟨1223646, by rfl⟩ : syracuseStep 3263057 = 2447293) B2447293
theorem B2175371 : Blo 2173435 2175371 := bstep (se 1 (by rfl) ⟨1631528, by rfl⟩ : syracuseStep 2175371 = 3263057) B3263057
theorem B7341893 : Blo 2173435 7341893 := bbase (se 4 (by rfl) ⟨688302, by rfl⟩ : syracuseStep 7341893 = 1376605) (by norm_num)
theorem B4894595 : Blo 2173435 4894595 := bstep (se 1 (by rfl) ⟨3670946, by rfl⟩ : syracuseStep 4894595 = 7341893) B7341893
theorem B3263063 : Blo 2173435 3263063 := bstep (se 1 (by rfl) ⟨2447297, by rfl⟩ : syracuseStep 3263063 = 4894595) B4894595
theorem B2175375 : Blo 2173435 2175375 := bstep (se 1 (by rfl) ⟨1631531, by rfl⟩ : syracuseStep 2175375 = 3263063) B3263063
theorem B3263069 : Blo 2173435 3263069 := bbase (se 3 (by rfl) ⟨611825, by rfl⟩ : syracuseStep 3263069 = 1223651) (by norm_num)
theorem B2175379 : Blo 2173435 2175379 := bstep (se 1 (by rfl) ⟨1631534, by rfl⟩ : syracuseStep 2175379 = 3263069) B3263069
theorem B4894613 : Blo 2173435 4894613 := bbase (se 6 (by rfl) ⟨114717, by rfl⟩ : syracuseStep 4894613 = 229435) (by norm_num)
theorem B3263075 : Blo 2173435 3263075 := bstep (se 1 (by rfl) ⟨2447306, by rfl⟩ : syracuseStep 3263075 = 4894613) B4894613
theorem B2175383 : Blo 2173435 2175383 := bstep (se 1 (by rfl) ⟨1631537, by rfl⟩ : syracuseStep 2175383 = 3263075) B3263075
theorem B4646069 : Blo 2173435 4646069 := bbase (se 5 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 4646069 = 435569) (by norm_num)
theorem B3097379 : Blo 2173435 3097379 := bstep (se 1 (by rfl) ⟨2323034, by rfl⟩ : syracuseStep 3097379 = 4646069) B4646069
theorem B8259677 : Blo 2173435 8259677 := bstep (se 3 (by rfl) ⟨1548689, by rfl⟩ : syracuseStep 8259677 = 3097379) B3097379
theorem B5506451 : Blo 2173435 5506451 := bstep (se 1 (by rfl) ⟨4129838, by rfl⟩ : syracuseStep 5506451 = 8259677) B8259677
theorem B3670967 : Blo 2173435 3670967 := bstep (se 1 (by rfl) ⟨2753225, by rfl⟩ : syracuseStep 3670967 = 5506451) B5506451
theorem B2447311 : Blo 2173435 2447311 := bstep (se 1 (by rfl) ⟨1835483, by rfl⟩ : syracuseStep 2447311 = 3670967) B3670967
theorem B3263081 : Blo 2173435 3263081 := bstep (se 2 (by rfl) ⟨1223655, by rfl⟩ : syracuseStep 3263081 = 2447311) B2447311
theorem B2175387 : Blo 2173435 2175387 := bstep (se 1 (by rfl) ⟨1631540, by rfl⟩ : syracuseStep 2175387 = 3263081) B3263081
theorem B3398477 : Blo 2173435 3398477 := bbase (se 3 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 3398477 = 1274429) (by norm_num)
theorem B36250421 : Blo 2173435 36250421 := bstep (se 5 (by rfl) ⟨1699238, by rfl⟩ : syracuseStep 36250421 = 3398477) B3398477
theorem B96667789 : Blo 2173435 96667789 := bstep (se 3 (by rfl) ⟨18125210, by rfl⟩ : syracuseStep 96667789 = 36250421) B36250421
theorem B128890385 : Blo 2173435 128890385 := bstep (se 2 (by rfl) ⟨48333894, by rfl⟩ : syracuseStep 128890385 = 96667789) B96667789
theorem B85926923 : Blo 2173435 85926923 := bstep (se 1 (by rfl) ⟨64445192, by rfl⟩ : syracuseStep 85926923 = 128890385) B128890385
theorem B57284615 : Blo 2173435 57284615 := bstep (se 1 (by rfl) ⟨42963461, by rfl⟩ : syracuseStep 57284615 = 85926923) B85926923
theorem B152758973 : Blo 2173435 152758973 := bstep (se 3 (by rfl) ⟨28642307, by rfl⟩ : syracuseStep 152758973 = 57284615) B57284615
theorem B101839315 : Blo 2173435 101839315 := bstep (se 1 (by rfl) ⟨76379486, by rfl⟩ : syracuseStep 101839315 = 152758973) B152758973
theorem B135785753 : Blo 2173435 135785753 := bstep (se 2 (by rfl) ⟨50919657, by rfl⟩ : syracuseStep 135785753 = 101839315) B101839315
theorem B90523835 : Blo 2173435 90523835 := bstep (se 1 (by rfl) ⟨67892876, by rfl⟩ : syracuseStep 90523835 = 135785753) B135785753
theorem B60349223 : Blo 2173435 60349223 := bstep (se 1 (by rfl) ⟨45261917, by rfl⟩ : syracuseStep 60349223 = 90523835) B90523835
theorem B160931261 : Blo 2173435 160931261 := bstep (se 3 (by rfl) ⟨30174611, by rfl⟩ : syracuseStep 160931261 = 60349223) B60349223
theorem B107287507 : Blo 2173435 107287507 := bstep (se 1 (by rfl) ⟨80465630, by rfl⟩ : syracuseStep 107287507 = 160931261) B160931261
theorem B572200037 : Blo 2173435 572200037 := bstep (se 4 (by rfl) ⟨53643753, by rfl⟩ : syracuseStep 572200037 = 107287507) B107287507
theorem B381466691 : Blo 2173435 381466691 := bstep (se 1 (by rfl) ⟨286100018, by rfl⟩ : syracuseStep 381466691 = 572200037) B572200037
theorem B254311127 : Blo 2173435 254311127 := bstep (se 1 (by rfl) ⟨190733345, by rfl⟩ : syracuseStep 254311127 = 381466691) B381466691
theorem B169540751 : Blo 2173435 169540751 := bstep (se 1 (by rfl) ⟨127155563, by rfl⟩ : syracuseStep 169540751 = 254311127) B254311127
theorem B113027167 : Blo 2173435 113027167 := bstep (se 1 (by rfl) ⟨84770375, by rfl⟩ : syracuseStep 113027167 = 169540751) B169540751
theorem B150702889 : Blo 2173435 150702889 := bstep (se 2 (by rfl) ⟨56513583, by rfl⟩ : syracuseStep 150702889 = 113027167) B113027167
theorem B200937185 : Blo 2173435 200937185 := bstep (se 2 (by rfl) ⟨75351444, by rfl⟩ : syracuseStep 200937185 = 150702889) B150702889
theorem B133958123 : Blo 2173435 133958123 := bstep (se 1 (by rfl) ⟨100468592, by rfl⟩ : syracuseStep 133958123 = 200937185) B200937185
theorem B89305415 : Blo 2173435 89305415 := bstep (se 1 (by rfl) ⟨66979061, by rfl⟩ : syracuseStep 89305415 = 133958123) B133958123
theorem B59536943 : Blo 2173435 59536943 := bstep (se 1 (by rfl) ⟨44652707, by rfl⟩ : syracuseStep 59536943 = 89305415) B89305415
theorem B39691295 : Blo 2173435 39691295 := bstep (se 1 (by rfl) ⟨29768471, by rfl⟩ : syracuseStep 39691295 = 59536943) B59536943
theorem B26460863 : Blo 2173435 26460863 := bstep (se 1 (by rfl) ⟨19845647, by rfl⟩ : syracuseStep 26460863 = 39691295) B39691295
theorem B17640575 : Blo 2173435 17640575 := bstep (se 1 (by rfl) ⟨13230431, by rfl⟩ : syracuseStep 17640575 = 26460863) B26460863
theorem B11760383 : Blo 2173435 11760383 := bstep (se 1 (by rfl) ⟨8820287, by rfl⟩ : syracuseStep 11760383 = 17640575) B17640575
theorem B7840255 : Blo 2173435 7840255 := bstep (se 1 (by rfl) ⟨5880191, by rfl⟩ : syracuseStep 7840255 = 11760383) B11760383
theorem B10453673 : Blo 2173435 10453673 := bstep (se 2 (by rfl) ⟨3920127, by rfl⟩ : syracuseStep 10453673 = 7840255) B7840255
theorem B6969115 : Blo 2173435 6969115 := bstep (se 1 (by rfl) ⟨5226836, by rfl⟩ : syracuseStep 6969115 = 10453673) B10453673
theorem B9292153 : Blo 2173435 9292153 := bstep (se 2 (by rfl) ⟨3484557, by rfl⟩ : syracuseStep 9292153 = 6969115) B6969115
theorem B12389537 : Blo 2173435 12389537 := bstep (se 2 (by rfl) ⟨4646076, by rfl⟩ : syracuseStep 12389537 = 9292153) B9292153
theorem B8259691 : Blo 2173435 8259691 := bstep (se 1 (by rfl) ⟨6194768, by rfl⟩ : syracuseStep 8259691 = 12389537) B12389537
theorem B11012921 : Blo 2173435 11012921 := bstep (se 2 (by rfl) ⟨4129845, by rfl⟩ : syracuseStep 11012921 = 8259691) B8259691
theorem B7341947 : Blo 2173435 7341947 := bstep (se 1 (by rfl) ⟨5506460, by rfl⟩ : syracuseStep 7341947 = 11012921) B11012921
theorem B4894631 : Blo 2173435 4894631 := bstep (se 1 (by rfl) ⟨3670973, by rfl⟩ : syracuseStep 4894631 = 7341947) B7341947
theorem B3263087 : Blo 2173435 3263087 := bstep (se 1 (by rfl) ⟨2447315, by rfl⟩ : syracuseStep 3263087 = 4894631) B4894631
theorem B2175391 : Blo 2173435 2175391 := bstep (se 1 (by rfl) ⟨1631543, by rfl⟩ : syracuseStep 2175391 = 3263087) B3263087
theorem B3263093 : Blo 2173435 3263093 := bbase (se 5 (by rfl) ⟨152957, by rfl⟩ : syracuseStep 3263093 = 305915) (by norm_num)
theorem B2175395 : Blo 2173435 2175395 := bstep (se 1 (by rfl) ⟨1631546, by rfl⟩ : syracuseStep 2175395 = 3263093) B3263093
theorem B4129861 : Blo 2173435 4129861 := bbase (se 4 (by rfl) ⟨387174, by rfl⟩ : syracuseStep 4129861 = 774349) (by norm_num)
theorem B5506481 : Blo 2173435 5506481 := bstep (se 2 (by rfl) ⟨2064930, by rfl⟩ : syracuseStep 5506481 = 4129861) B4129861
theorem B3670987 : Blo 2173435 3670987 := bstep (se 1 (by rfl) ⟨2753240, by rfl⟩ : syracuseStep 3670987 = 5506481) B5506481
theorem B4894649 : Blo 2173435 4894649 := bstep (se 2 (by rfl) ⟨1835493, by rfl⟩ : syracuseStep 4894649 = 3670987) B3670987
theorem B3263099 : Blo 2173435 3263099 := bstep (se 1 (by rfl) ⟨2447324, by rfl⟩ : syracuseStep 3263099 = 4894649) B4894649
theorem B2175399 : Blo 2173435 2175399 := bstep (se 1 (by rfl) ⟨1631549, by rfl⟩ : syracuseStep 2175399 = 3263099) B3263099
theorem B2447329 : Blo 2173435 2447329 := bbase (se 2 (by rfl) ⟨917748, by rfl⟩ : syracuseStep 2447329 = 1835497) (by norm_num)
theorem B3263105 : Blo 2173435 3263105 := bstep (se 2 (by rfl) ⟨1223664, by rfl⟩ : syracuseStep 3263105 = 2447329) B2447329
theorem B2175403 : Blo 2173435 2175403 := bstep (se 1 (by rfl) ⟨1631552, by rfl⟩ : syracuseStep 2175403 = 3263105) B3263105
theorem B5506501 : Blo 2173435 5506501 := bbase (se 4 (by rfl) ⟨516234, by rfl⟩ : syracuseStep 5506501 = 1032469) (by norm_num)
theorem B7342001 : Blo 2173435 7342001 := bstep (se 2 (by rfl) ⟨2753250, by rfl⟩ : syracuseStep 7342001 = 5506501) B5506501
theorem B4894667 : Blo 2173435 4894667 := bstep (se 1 (by rfl) ⟨3671000, by rfl⟩ : syracuseStep 4894667 = 7342001) B7342001
theorem B3263111 : Blo 2173435 3263111 := bstep (se 1 (by rfl) ⟨2447333, by rfl⟩ : syracuseStep 3263111 = 4894667) B4894667
theorem B2175407 : Blo 2173435 2175407 := bstep (se 1 (by rfl) ⟨1631555, by rfl⟩ : syracuseStep 2175407 = 3263111) B3263111
theorem B3263117 : Blo 2173435 3263117 := bbase (se 3 (by rfl) ⟨611834, by rfl⟩ : syracuseStep 3263117 = 1223669) (by norm_num)
theorem B2175411 : Blo 2173435 2175411 := bstep (se 1 (by rfl) ⟨1631558, by rfl⟩ : syracuseStep 2175411 = 3263117) B3263117
theorem B4894685 : Blo 2173435 4894685 := bbase (se 3 (by rfl) ⟨917753, by rfl⟩ : syracuseStep 4894685 = 1835507) (by norm_num)
theorem B3263123 : Blo 2173435 3263123 := bstep (se 1 (by rfl) ⟨2447342, by rfl⟩ : syracuseStep 3263123 = 4894685) B4894685
theorem B2175415 : Blo 2173435 2175415 := bstep (se 1 (by rfl) ⟨1631561, by rfl⟩ : syracuseStep 2175415 = 3263123) B3263123
theorem B3671021 : Blo 2173435 3671021 := bbase (se 3 (by rfl) ⟨688316, by rfl⟩ : syracuseStep 3671021 = 1376633) (by norm_num)
theorem B2447347 : Blo 2173435 2447347 := bstep (se 1 (by rfl) ⟨1835510, by rfl⟩ : syracuseStep 2447347 = 3671021) B3671021
theorem B3263129 : Blo 2173435 3263129 := bstep (se 2 (by rfl) ⟨1223673, by rfl⟩ : syracuseStep 3263129 = 2447347) B2447347
theorem B2175419 : Blo 2173435 2175419 := bstep (se 1 (by rfl) ⟨1631564, by rfl⟩ : syracuseStep 2175419 = 3263129) B3263129
theorem B2386897 : Blo 2173435 2386897 := bbase (se 2 (by rfl) ⟨895086, by rfl⟩ : syracuseStep 2386897 = 1790173) (by norm_num)
theorem B12730117 : Blo 2173435 12730117 := bstep (se 4 (by rfl) ⟨1193448, by rfl⟩ : syracuseStep 12730117 = 2386897) B2386897
theorem B16973489 : Blo 2173435 16973489 := bstep (se 2 (by rfl) ⟨6365058, by rfl⟩ : syracuseStep 16973489 = 12730117) B12730117
theorem B11315659 : Blo 2173435 11315659 := bstep (se 1 (by rfl) ⟨8486744, by rfl⟩ : syracuseStep 11315659 = 16973489) B16973489
theorem B15087545 : Blo 2173435 15087545 := bstep (se 2 (by rfl) ⟨5657829, by rfl⟩ : syracuseStep 15087545 = 11315659) B11315659
theorem B10058363 : Blo 2173435 10058363 := bstep (se 1 (by rfl) ⟨7543772, by rfl⟩ : syracuseStep 10058363 = 15087545) B15087545
theorem B6705575 : Blo 2173435 6705575 := bstep (se 1 (by rfl) ⟨5029181, by rfl⟩ : syracuseStep 6705575 = 10058363) B10058363
theorem B4470383 : Blo 2173435 4470383 := bstep (se 1 (by rfl) ⟨3352787, by rfl⟩ : syracuseStep 4470383 = 6705575) B6705575
theorem B2980255 : Blo 2173435 2980255 := bstep (se 1 (by rfl) ⟨2235191, by rfl⟩ : syracuseStep 2980255 = 4470383) B4470383
theorem B3973673 : Blo 2173435 3973673 := bstep (se 2 (by rfl) ⟨1490127, by rfl⟩ : syracuseStep 3973673 = 2980255) B2980255
theorem B2649115 : Blo 2173435 2649115 := bstep (se 1 (by rfl) ⟨1986836, by rfl⟩ : syracuseStep 2649115 = 3973673) B3973673
theorem B14128613 : Blo 2173435 14128613 := bstep (se 4 (by rfl) ⟨1324557, by rfl⟩ : syracuseStep 14128613 = 2649115) B2649115
theorem B9419075 : Blo 2173435 9419075 := bstep (se 1 (by rfl) ⟨7064306, by rfl⟩ : syracuseStep 9419075 = 14128613) B14128613
theorem B6279383 : Blo 2173435 6279383 := bstep (se 1 (by rfl) ⟨4709537, by rfl⟩ : syracuseStep 6279383 = 9419075) B9419075
theorem B4186255 : Blo 2173435 4186255 := bstep (se 1 (by rfl) ⟨3139691, by rfl⟩ : syracuseStep 4186255 = 6279383) B6279383
theorem B5581673 : Blo 2173435 5581673 := bstep (se 2 (by rfl) ⟨2093127, by rfl⟩ : syracuseStep 5581673 = 4186255) B4186255
theorem B3721115 : Blo 2173435 3721115 := bstep (se 1 (by rfl) ⟨2790836, by rfl⟩ : syracuseStep 3721115 = 5581673) B5581673
theorem B2480743 : Blo 2173435 2480743 := bstep (se 1 (by rfl) ⟨1860557, by rfl⟩ : syracuseStep 2480743 = 3721115) B3721115
theorem B3307657 : Blo 2173435 3307657 := bstep (se 2 (by rfl) ⟨1240371, by rfl⟩ : syracuseStep 3307657 = 2480743) B2480743
theorem B4410209 : Blo 2173435 4410209 := bstep (se 2 (by rfl) ⟨1653828, by rfl⟩ : syracuseStep 4410209 = 3307657) B3307657
theorem B2940139 : Blo 2173435 2940139 := bstep (se 1 (by rfl) ⟨2205104, by rfl⟩ : syracuseStep 2940139 = 4410209) B4410209
theorem B3920185 : Blo 2173435 3920185 := bstep (se 2 (by rfl) ⟨1470069, by rfl⟩ : syracuseStep 3920185 = 2940139) B2940139
theorem B5226913 : Blo 2173435 5226913 := bstep (se 2 (by rfl) ⟨1960092, by rfl⟩ : syracuseStep 5226913 = 3920185) B3920185
theorem B27876869 : Blo 2173435 27876869 := bstep (se 4 (by rfl) ⟨2613456, by rfl⟩ : syracuseStep 27876869 = 5226913) B5226913
theorem B18584579 : Blo 2173435 18584579 := bstep (se 1 (by rfl) ⟨13938434, by rfl⟩ : syracuseStep 18584579 = 27876869) B27876869
theorem B12389719 : Blo 2173435 12389719 := bstep (se 1 (by rfl) ⟨9292289, by rfl⟩ : syracuseStep 12389719 = 18584579) B18584579
theorem B16519625 : Blo 2173435 16519625 := bstep (se 2 (by rfl) ⟨6194859, by rfl⟩ : syracuseStep 16519625 = 12389719) B12389719
theorem B11013083 : Blo 2173435 11013083 := bstep (se 1 (by rfl) ⟨8259812, by rfl⟩ : syracuseStep 11013083 = 16519625) B16519625
theorem B7342055 : Blo 2173435 7342055 := bstep (se 1 (by rfl) ⟨5506541, by rfl⟩ : syracuseStep 7342055 = 11013083) B11013083
theorem B4894703 : Blo 2173435 4894703 := bstep (se 1 (by rfl) ⟨3671027, by rfl⟩ : syracuseStep 4894703 = 7342055) B7342055
theorem B3263135 : Blo 2173435 3263135 := bstep (se 1 (by rfl) ⟨2447351, by rfl⟩ : syracuseStep 3263135 = 4894703) B4894703
theorem B2175423 : Blo 2173435 2175423 := bstep (se 1 (by rfl) ⟨1631567, by rfl⟩ : syracuseStep 2175423 = 3263135) B3263135
theorem B3263141 : Blo 2173435 3263141 := bbase (se 4 (by rfl) ⟨305919, by rfl⟩ : syracuseStep 3263141 = 611839) (by norm_num)
theorem B2175427 : Blo 2173435 2175427 := bstep (se 1 (by rfl) ⟨1631570, by rfl⟩ : syracuseStep 2175427 = 3263141) B3263141
theorem B2753281 : Blo 2173435 2753281 := bbase (se 2 (by rfl) ⟨1032480, by rfl⟩ : syracuseStep 2753281 = 2064961) (by norm_num)
theorem B3671041 : Blo 2173435 3671041 := bstep (se 2 (by rfl) ⟨1376640, by rfl⟩ : syracuseStep 3671041 = 2753281) B2753281
theorem B4894721 : Blo 2173435 4894721 := bstep (se 2 (by rfl) ⟨1835520, by rfl⟩ : syracuseStep 4894721 = 3671041) B3671041
theorem B3263147 : Blo 2173435 3263147 := bstep (se 1 (by rfl) ⟨2447360, by rfl⟩ : syracuseStep 3263147 = 4894721) B4894721
theorem B2175431 : Blo 2173435 2175431 := bstep (se 1 (by rfl) ⟨1631573, by rfl⟩ : syracuseStep 2175431 = 3263147) B3263147
theorem B2447365 : Blo 2173435 2447365 := bbase (se 4 (by rfl) ⟨229440, by rfl⟩ : syracuseStep 2447365 = 458881) (by norm_num)
theorem B3263153 : Blo 2173435 3263153 := bstep (se 2 (by rfl) ⟨1223682, by rfl⟩ : syracuseStep 3263153 = 2447365) B2447365
theorem B2175435 : Blo 2173435 2175435 := bstep (se 1 (by rfl) ⟨1631576, by rfl⟩ : syracuseStep 2175435 = 3263153) B3263153
theorem C0 (j : ℕ) (h1 : 543358 ≤ j) (h2 : j ≤ 543858) : Blo 2173435 (4 * j + 3) := by
  interval_cases j
  · exact B2173435
  · exact B2173439
  · exact B2173443
  · exact B2173447
  · exact B2173451
  · exact B2173455
  · exact B2173459
  · exact B2173463
  · exact B2173467
  · exact B2173471
  · exact B2173475
  · exact B2173479
  · exact B2173483
  · exact B2173487
  · exact B2173491
  · exact B2173495
  · exact B2173499
  · exact B2173503
  · exact B2173507
  · exact B2173511
  · exact B2173515
  · exact B2173519
  · exact B2173523
  · exact B2173527
  · exact B2173531
  · exact B2173535
  · exact B2173539
  · exact B2173543
  · exact B2173547
  · exact B2173551
  · exact B2173555
  · exact B2173559
  · exact B2173563
  · exact B2173567
  · exact B2173571
  · exact B2173575
  · exact B2173579
  · exact B2173583
  · exact B2173587
  · exact B2173591
  · exact B2173595
  · exact B2173599
  · exact B2173603
  · exact B2173607
  · exact B2173611
  · exact B2173615
  · exact B2173619
  · exact B2173623
  · exact B2173627
  · exact B2173631
  · exact B2173635
  · exact B2173639
  · exact B2173643
  · exact B2173647
  · exact B2173651
  · exact B2173655
  · exact B2173659
  · exact B2173663
  · exact B2173667
  · exact B2173671
  · exact B2173675
  · exact B2173679
  · exact B2173683
  · exact B2173687
  · exact B2173691
  · exact B2173695
  · exact B2173699
  · exact B2173703
  · exact B2173707
  · exact B2173711
  · exact B2173715
  · exact B2173719
  · exact B2173723
  · exact B2173727
  · exact B2173731
  · exact B2173735
  · exact B2173739
  · exact B2173743
  · exact B2173747
  · exact B2173751
  · exact B2173755
  · exact B2173759
  · exact B2173763
  · exact B2173767
  · exact B2173771
  · exact B2173775
  · exact B2173779
  · exact B2173783
  · exact B2173787
  · exact B2173791
  · exact B2173795
  · exact B2173799
  · exact B2173803
  · exact B2173807
  · exact B2173811
  · exact B2173815
  · exact B2173819
  · exact B2173823
  · exact B2173827
  · exact B2173831
  · exact B2173835
  · exact B2173839
  · exact B2173843
  · exact B2173847
  · exact B2173851
  · exact B2173855
  · exact B2173859
  · exact B2173863
  · exact B2173867
  · exact B2173871
  · exact B2173875
  · exact B2173879
  · exact B2173883
  · exact B2173887
  · exact B2173891
  · exact B2173895
  · exact B2173899
  · exact B2173903
  · exact B2173907
  · exact B2173911
  · exact B2173915
  · exact B2173919
  · exact B2173923
  · exact B2173927
  · exact B2173931
  · exact B2173935
  · exact B2173939
  · exact B2173943
  · exact B2173947
  · exact B2173951
  · exact B2173955
  · exact B2173959
  · exact B2173963
  · exact B2173967
  · exact B2173971
  · exact B2173975
  · exact B2173979
  · exact B2173983
  · exact B2173987
  · exact B2173991
  · exact B2173995
  · exact B2173999
  · exact B2174003
  · exact B2174007
  · exact B2174011
  · exact B2174015
  · exact B2174019
  · exact B2174023
  · exact B2174027
  · exact B2174031
  · exact B2174035
  · exact B2174039
  · exact B2174043
  · exact B2174047
  · exact B2174051
  · exact B2174055
  · exact B2174059
  · exact B2174063
  · exact B2174067
  · exact B2174071
  · exact B2174075
  · exact B2174079
  · exact B2174083
  · exact B2174087
  · exact B2174091
  · exact B2174095
  · exact B2174099
  · exact B2174103
  · exact B2174107
  · exact B2174111
  · exact B2174115
  · exact B2174119
  · exact B2174123
  · exact B2174127
  · exact B2174131
  · exact B2174135
  · exact B2174139
  · exact B2174143
  · exact B2174147
  · exact B2174151
  · exact B2174155
  · exact B2174159
  · exact B2174163
  · exact B2174167
  · exact B2174171
  · exact B2174175
  · exact B2174179
  · exact B2174183
  · exact B2174187
  · exact B2174191
  · exact B2174195
  · exact B2174199
  · exact B2174203
  · exact B2174207
  · exact B2174211
  · exact B2174215
  · exact B2174219
  · exact B2174223
  · exact B2174227
  · exact B2174231
  · exact B2174235
  · exact B2174239
  · exact B2174243
  · exact B2174247
  · exact B2174251
  · exact B2174255
  · exact B2174259
  · exact B2174263
  · exact B2174267
  · exact B2174271
  · exact B2174275
  · exact B2174279
  · exact B2174283
  · exact B2174287
  · exact B2174291
  · exact B2174295
  · exact B2174299
  · exact B2174303
  · exact B2174307
  · exact B2174311
  · exact B2174315
  · exact B2174319
  · exact B2174323
  · exact B2174327
  · exact B2174331
  · exact B2174335
  · exact B2174339
  · exact B2174343
  · exact B2174347
  · exact B2174351
  · exact B2174355
  · exact B2174359
  · exact B2174363
  · exact B2174367
  · exact B2174371
  · exact B2174375
  · exact B2174379
  · exact B2174383
  · exact B2174387
  · exact B2174391
  · exact B2174395
  · exact B2174399
  · exact B2174403
  · exact B2174407
  · exact B2174411
  · exact B2174415
  · exact B2174419
  · exact B2174423
  · exact B2174427
  · exact B2174431
  · exact B2174435
  · exact B2174439
  · exact B2174443
  · exact B2174447
  · exact B2174451
  · exact B2174455
  · exact B2174459
  · exact B2174463
  · exact B2174467
  · exact B2174471
  · exact B2174475
  · exact B2174479
  · exact B2174483
  · exact B2174487
  · exact B2174491
  · exact B2174495
  · exact B2174499
  · exact B2174503
  · exact B2174507
  · exact B2174511
  · exact B2174515
  · exact B2174519
  · exact B2174523
  · exact B2174527
  · exact B2174531
  · exact B2174535
  · exact B2174539
  · exact B2174543
  · exact B2174547
  · exact B2174551
  · exact B2174555
  · exact B2174559
  · exact B2174563
  · exact B2174567
  · exact B2174571
  · exact B2174575
  · exact B2174579
  · exact B2174583
  · exact B2174587
  · exact B2174591
  · exact B2174595
  · exact B2174599
  · exact B2174603
  · exact B2174607
  · exact B2174611
  · exact B2174615
  · exact B2174619
  · exact B2174623
  · exact B2174627
  · exact B2174631
  · exact B2174635
  · exact B2174639
  · exact B2174643
  · exact B2174647
  · exact B2174651
  · exact B2174655
  · exact B2174659
  · exact B2174663
  · exact B2174667
  · exact B2174671
  · exact B2174675
  · exact B2174679
  · exact B2174683
  · exact B2174687
  · exact B2174691
  · exact B2174695
  · exact B2174699
  · exact B2174703
  · exact B2174707
  · exact B2174711
  · exact B2174715
  · exact B2174719
  · exact B2174723
  · exact B2174727
  · exact B2174731
  · exact B2174735
  · exact B2174739
  · exact B2174743
  · exact B2174747
  · exact B2174751
  · exact B2174755
  · exact B2174759
  · exact B2174763
  · exact B2174767
  · exact B2174771
  · exact B2174775
  · exact B2174779
  · exact B2174783
  · exact B2174787
  · exact B2174791
  · exact B2174795
  · exact B2174799
  · exact B2174803
  · exact B2174807
  · exact B2174811
  · exact B2174815
  · exact B2174819
  · exact B2174823
  · exact B2174827
  · exact B2174831
  · exact B2174835
  · exact B2174839
  · exact B2174843
  · exact B2174847
  · exact B2174851
  · exact B2174855
  · exact B2174859
  · exact B2174863
  · exact B2174867
  · exact B2174871
  · exact B2174875
  · exact B2174879
  · exact B2174883
  · exact B2174887
  · exact B2174891
  · exact B2174895
  · exact B2174899
  · exact B2174903
  · exact B2174907
  · exact B2174911
  · exact B2174915
  · exact B2174919
  · exact B2174923
  · exact B2174927
  · exact B2174931
  · exact B2174935
  · exact B2174939
  · exact B2174943
  · exact B2174947
  · exact B2174951
  · exact B2174955
  · exact B2174959
  · exact B2174963
  · exact B2174967
  · exact B2174971
  · exact B2174975
  · exact B2174979
  · exact B2174983
  · exact B2174987
  · exact B2174991
  · exact B2174995
  · exact B2174999
  · exact B2175003
  · exact B2175007
  · exact B2175011
  · exact B2175015
  · exact B2175019
  · exact B2175023
  · exact B2175027
  · exact B2175031
  · exact B2175035
  · exact B2175039
  · exact B2175043
  · exact B2175047
  · exact B2175051
  · exact B2175055
  · exact B2175059
  · exact B2175063
  · exact B2175067
  · exact B2175071
  · exact B2175075
  · exact B2175079
  · exact B2175083
  · exact B2175087
  · exact B2175091
  · exact B2175095
  · exact B2175099
  · exact B2175103
  · exact B2175107
  · exact B2175111
  · exact B2175115
  · exact B2175119
  · exact B2175123
  · exact B2175127
  · exact B2175131
  · exact B2175135
  · exact B2175139
  · exact B2175143
  · exact B2175147
  · exact B2175151
  · exact B2175155
  · exact B2175159
  · exact B2175163
  · exact B2175167
  · exact B2175171
  · exact B2175175
  · exact B2175179
  · exact B2175183
  · exact B2175187
  · exact B2175191
  · exact B2175195
  · exact B2175199
  · exact B2175203
  · exact B2175207
  · exact B2175211
  · exact B2175215
  · exact B2175219
  · exact B2175223
  · exact B2175227
  · exact B2175231
  · exact B2175235
  · exact B2175239
  · exact B2175243
  · exact B2175247
  · exact B2175251
  · exact B2175255
  · exact B2175259
  · exact B2175263
  · exact B2175267
  · exact B2175271
  · exact B2175275
  · exact B2175279
  · exact B2175283
  · exact B2175287
  · exact B2175291
  · exact B2175295
  · exact B2175299
  · exact B2175303
  · exact B2175307
  · exact B2175311
  · exact B2175315
  · exact B2175319
  · exact B2175323
  · exact B2175327
  · exact B2175331
  · exact B2175335
  · exact B2175339
  · exact B2175343
  · exact B2175347
  · exact B2175351
  · exact B2175355
  · exact B2175359
  · exact B2175363
  · exact B2175367
  · exact B2175371
  · exact B2175375
  · exact B2175379
  · exact B2175383
  · exact B2175387
  · exact B2175391
  · exact B2175395
  · exact B2175399
  · exact B2175403
  · exact B2175407
  · exact B2175411
  · exact B2175415
  · exact B2175419
  · exact B2175423
  · exact B2175427
  · exact B2175431
  · exact B2175435
theorem solution (m : ℕ) (hlo : 2173435 ≤ m) (hhi : m ≤ 2175435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 543358 ≤ j := by omega
    have hj2 : j ≤ 543858 := by omega
    have hb : Blo 2173435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
