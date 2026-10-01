-- Prove2me | solution 1 for syracuse_descends_range_1943435_1945435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:34.434921+00:00
-- url     : https://prove2.me/submissions/81b3d063-b581-4423-8731-ace6c1c9ab94

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

theorem B2186365 : Blo 1943435 2186365 := bbase (se 3 (by rfl) ⟨409943, by rfl⟩ : syracuseStep 2186365 = 819887) (by norm_num)
theorem B2915153 : Blo 1943435 2915153 := bstep (se 2 (by rfl) ⟨1093182, by rfl⟩ : syracuseStep 2915153 = 2186365) B2186365
theorem B1943435 : Blo 1943435 1943435 := bstep (se 1 (by rfl) ⟨1457576, by rfl⟩ : syracuseStep 1943435 = 2915153) B2915153
theorem B6559109 : Blo 1943435 6559109 := bbase (se 4 (by rfl) ⟨614916, by rfl⟩ : syracuseStep 6559109 = 1229833) (by norm_num)
theorem B4372739 : Blo 1943435 4372739 := bstep (se 1 (by rfl) ⟨3279554, by rfl⟩ : syracuseStep 4372739 = 6559109) B6559109
theorem B2915159 : Blo 1943435 2915159 := bstep (se 1 (by rfl) ⟨2186369, by rfl⟩ : syracuseStep 2915159 = 4372739) B4372739
theorem B1943439 : Blo 1943435 1943439 := bstep (se 1 (by rfl) ⟨1457579, by rfl⟩ : syracuseStep 1943439 = 2915159) B2915159
theorem B2915165 : Blo 1943435 2915165 := bbase (se 3 (by rfl) ⟨546593, by rfl⟩ : syracuseStep 2915165 = 1093187) (by norm_num)
theorem B1943443 : Blo 1943435 1943443 := bstep (se 1 (by rfl) ⟨1457582, by rfl⟩ : syracuseStep 1943443 = 2915165) B2915165
theorem B4372757 : Blo 1943435 4372757 := bbase (se 6 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 4372757 = 204973) (by norm_num)
theorem B2915171 : Blo 1943435 2915171 := bstep (se 1 (by rfl) ⟨2186378, by rfl⟩ : syracuseStep 2915171 = 4372757) B4372757
theorem B1943447 : Blo 1943435 1943447 := bstep (se 1 (by rfl) ⟨1457585, by rfl⟩ : syracuseStep 1943447 = 2915171) B2915171
theorem B7379045 : Blo 1943435 7379045 := bbase (se 4 (by rfl) ⟨691785, by rfl⟩ : syracuseStep 7379045 = 1383571) (by norm_num)
theorem B4919363 : Blo 1943435 4919363 := bstep (se 1 (by rfl) ⟨3689522, by rfl⟩ : syracuseStep 4919363 = 7379045) B7379045
theorem B3279575 : Blo 1943435 3279575 := bstep (se 1 (by rfl) ⟨2459681, by rfl⟩ : syracuseStep 3279575 = 4919363) B4919363
theorem B2186383 : Blo 1943435 2186383 := bstep (se 1 (by rfl) ⟨1639787, by rfl⟩ : syracuseStep 2186383 = 3279575) B3279575
theorem B2915177 : Blo 1943435 2915177 := bstep (se 2 (by rfl) ⟨1093191, by rfl⟩ : syracuseStep 2915177 = 2186383) B2186383
theorem B1943451 : Blo 1943435 1943451 := bstep (se 1 (by rfl) ⟨1457588, by rfl⟩ : syracuseStep 1943451 = 2915177) B2915177
theorem B2334781 : Blo 1943435 2334781 := bbase (se 3 (by rfl) ⟨437771, by rfl⟩ : syracuseStep 2334781 = 875543) (by norm_num)
theorem B3113041 : Blo 1943435 3113041 := bstep (se 2 (by rfl) ⟨1167390, by rfl⟩ : syracuseStep 3113041 = 2334781) B2334781
theorem B4150721 : Blo 1943435 4150721 := bstep (se 2 (by rfl) ⟨1556520, by rfl⟩ : syracuseStep 4150721 = 3113041) B3113041
theorem B11068589 : Blo 1943435 11068589 := bstep (se 3 (by rfl) ⟨2075360, by rfl⟩ : syracuseStep 11068589 = 4150721) B4150721
theorem B7379059 : Blo 1943435 7379059 := bstep (se 1 (by rfl) ⟨5534294, by rfl⟩ : syracuseStep 7379059 = 11068589) B11068589
theorem B9838745 : Blo 1943435 9838745 := bstep (se 2 (by rfl) ⟨3689529, by rfl⟩ : syracuseStep 9838745 = 7379059) B7379059
theorem B6559163 : Blo 1943435 6559163 := bstep (se 1 (by rfl) ⟨4919372, by rfl⟩ : syracuseStep 6559163 = 9838745) B9838745
theorem B4372775 : Blo 1943435 4372775 := bstep (se 1 (by rfl) ⟨3279581, by rfl⟩ : syracuseStep 4372775 = 6559163) B6559163
theorem B2915183 : Blo 1943435 2915183 := bstep (se 1 (by rfl) ⟨2186387, by rfl⟩ : syracuseStep 2915183 = 4372775) B4372775
theorem B1943455 : Blo 1943435 1943455 := bstep (se 1 (by rfl) ⟨1457591, by rfl⟩ : syracuseStep 1943455 = 2915183) B2915183
theorem B2915189 : Blo 1943435 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B1943459 : Blo 1943435 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B4207373 : Blo 1943435 4207373 := bbase (se 3 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 4207373 = 1577765) (by norm_num)
theorem B2804915 : Blo 1943435 2804915 := bstep (se 1 (by rfl) ⟨2103686, by rfl⟩ : syracuseStep 2804915 = 4207373) B4207373
theorem B7479773 : Blo 1943435 7479773 := bstep (se 3 (by rfl) ⟨1402457, by rfl⟩ : syracuseStep 7479773 = 2804915) B2804915
theorem B4986515 : Blo 1943435 4986515 := bstep (se 1 (by rfl) ⟨3739886, by rfl⟩ : syracuseStep 4986515 = 7479773) B7479773
theorem B3324343 : Blo 1943435 3324343 := bstep (se 1 (by rfl) ⟨2493257, by rfl⟩ : syracuseStep 3324343 = 4986515) B4986515
theorem B4432457 : Blo 1943435 4432457 := bstep (se 2 (by rfl) ⟨1662171, by rfl⟩ : syracuseStep 4432457 = 3324343) B3324343
theorem B2954971 : Blo 1943435 2954971 := bstep (se 1 (by rfl) ⟨2216228, by rfl⟩ : syracuseStep 2954971 = 4432457) B4432457
theorem B3939961 : Blo 1943435 3939961 := bstep (se 2 (by rfl) ⟨1477485, by rfl⟩ : syracuseStep 3939961 = 2954971) B2954971
theorem B5253281 : Blo 1943435 5253281 := bstep (se 2 (by rfl) ⟨1969980, by rfl⟩ : syracuseStep 5253281 = 3939961) B3939961
theorem B3502187 : Blo 1943435 3502187 := bstep (se 1 (by rfl) ⟨2626640, by rfl⟩ : syracuseStep 3502187 = 5253281) B5253281
theorem B2334791 : Blo 1943435 2334791 := bstep (se 1 (by rfl) ⟨1751093, by rfl⟩ : syracuseStep 2334791 = 3502187) B3502187
theorem B6226109 : Blo 1943435 6226109 := bstep (se 3 (by rfl) ⟨1167395, by rfl⟩ : syracuseStep 6226109 = 2334791) B2334791
theorem B4150739 : Blo 1943435 4150739 := bstep (se 1 (by rfl) ⟨3113054, by rfl⟩ : syracuseStep 4150739 = 6226109) B6226109
theorem B2767159 : Blo 1943435 2767159 := bstep (se 1 (by rfl) ⟨2075369, by rfl⟩ : syracuseStep 2767159 = 4150739) B4150739
theorem B3689545 : Blo 1943435 3689545 := bstep (se 2 (by rfl) ⟨1383579, by rfl⟩ : syracuseStep 3689545 = 2767159) B2767159
theorem B4919393 : Blo 1943435 4919393 := bstep (se 2 (by rfl) ⟨1844772, by rfl⟩ : syracuseStep 4919393 = 3689545) B3689545
theorem B3279595 : Blo 1943435 3279595 := bstep (se 1 (by rfl) ⟨2459696, by rfl⟩ : syracuseStep 3279595 = 4919393) B4919393
theorem B4372793 : Blo 1943435 4372793 := bstep (se 2 (by rfl) ⟨1639797, by rfl⟩ : syracuseStep 4372793 = 3279595) B3279595
theorem B2915195 : Blo 1943435 2915195 := bstep (se 1 (by rfl) ⟨2186396, by rfl⟩ : syracuseStep 2915195 = 4372793) B4372793
theorem B1943463 : Blo 1943435 1943463 := bstep (se 1 (by rfl) ⟨1457597, by rfl⟩ : syracuseStep 1943463 = 2915195) B2915195
theorem B2186401 : Blo 1943435 2186401 := bbase (se 2 (by rfl) ⟨819900, by rfl⟩ : syracuseStep 2186401 = 1639801) (by norm_num)
theorem B2915201 : Blo 1943435 2915201 := bstep (se 2 (by rfl) ⟨1093200, by rfl⟩ : syracuseStep 2915201 = 2186401) B2186401
theorem B1943467 : Blo 1943435 1943467 := bstep (se 1 (by rfl) ⟨1457600, by rfl⟩ : syracuseStep 1943467 = 2915201) B2915201
theorem B4919413 : Blo 1943435 4919413 := bbase (se 5 (by rfl) ⟨230597, by rfl⟩ : syracuseStep 4919413 = 461195) (by norm_num)
theorem B6559217 : Blo 1943435 6559217 := bstep (se 2 (by rfl) ⟨2459706, by rfl⟩ : syracuseStep 6559217 = 4919413) B4919413
theorem B4372811 : Blo 1943435 4372811 := bstep (se 1 (by rfl) ⟨3279608, by rfl⟩ : syracuseStep 4372811 = 6559217) B6559217
theorem B2915207 : Blo 1943435 2915207 := bstep (se 1 (by rfl) ⟨2186405, by rfl⟩ : syracuseStep 2915207 = 4372811) B4372811
theorem B1943471 : Blo 1943435 1943471 := bstep (se 1 (by rfl) ⟨1457603, by rfl⟩ : syracuseStep 1943471 = 2915207) B2915207
theorem B2915213 : Blo 1943435 2915213 := bbase (se 3 (by rfl) ⟨546602, by rfl⟩ : syracuseStep 2915213 = 1093205) (by norm_num)
theorem B1943475 : Blo 1943435 1943475 := bstep (se 1 (by rfl) ⟨1457606, by rfl⟩ : syracuseStep 1943475 = 2915213) B2915213
theorem B4372829 : Blo 1943435 4372829 := bbase (se 3 (by rfl) ⟨819905, by rfl⟩ : syracuseStep 4372829 = 1639811) (by norm_num)
theorem B2915219 : Blo 1943435 2915219 := bstep (se 1 (by rfl) ⟨2186414, by rfl⟩ : syracuseStep 2915219 = 4372829) B4372829
theorem B1943479 : Blo 1943435 1943479 := bstep (se 1 (by rfl) ⟨1457609, by rfl⟩ : syracuseStep 1943479 = 2915219) B2915219
theorem B3279629 : Blo 1943435 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B2186419 : Blo 1943435 2186419 := bstep (se 1 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 2186419 = 3279629) B3279629
theorem B2915225 : Blo 1943435 2915225 := bstep (se 2 (by rfl) ⟨1093209, by rfl⟩ : syracuseStep 2915225 = 2186419) B2186419
theorem B1943483 : Blo 1943435 1943483 := bstep (se 1 (by rfl) ⟨1457612, by rfl⟩ : syracuseStep 1943483 = 2915225) B2915225
theorem B16603157 : Blo 1943435 16603157 := bbase (se 6 (by rfl) ⟨389136, by rfl⟩ : syracuseStep 16603157 = 778273) (by norm_num)
theorem B11068771 : Blo 1943435 11068771 := bstep (se 1 (by rfl) ⟨8301578, by rfl⟩ : syracuseStep 11068771 = 16603157) B16603157
theorem B14758361 : Blo 1943435 14758361 := bstep (se 2 (by rfl) ⟨5534385, by rfl⟩ : syracuseStep 14758361 = 11068771) B11068771
theorem B9838907 : Blo 1943435 9838907 := bstep (se 1 (by rfl) ⟨7379180, by rfl⟩ : syracuseStep 9838907 = 14758361) B14758361
theorem B6559271 : Blo 1943435 6559271 := bstep (se 1 (by rfl) ⟨4919453, by rfl⟩ : syracuseStep 6559271 = 9838907) B9838907
theorem B4372847 : Blo 1943435 4372847 := bstep (se 1 (by rfl) ⟨3279635, by rfl⟩ : syracuseStep 4372847 = 6559271) B6559271
theorem B2915231 : Blo 1943435 2915231 := bstep (se 1 (by rfl) ⟨2186423, by rfl⟩ : syracuseStep 2915231 = 4372847) B4372847
theorem B1943487 : Blo 1943435 1943487 := bstep (se 1 (by rfl) ⟨1457615, by rfl⟩ : syracuseStep 1943487 = 2915231) B2915231
theorem B2915237 : Blo 1943435 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B1943491 : Blo 1943435 1943491 := bstep (se 1 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 1943491 = 2915237) B2915237
theorem B2459737 : Blo 1943435 2459737 := bbase (se 2 (by rfl) ⟨922401, by rfl⟩ : syracuseStep 2459737 = 1844803) (by norm_num)
theorem B3279649 : Blo 1943435 3279649 := bstep (se 2 (by rfl) ⟨1229868, by rfl⟩ : syracuseStep 3279649 = 2459737) B2459737
theorem B4372865 : Blo 1943435 4372865 := bstep (se 2 (by rfl) ⟨1639824, by rfl⟩ : syracuseStep 4372865 = 3279649) B3279649
theorem B2915243 : Blo 1943435 2915243 := bstep (se 1 (by rfl) ⟨2186432, by rfl⟩ : syracuseStep 2915243 = 4372865) B4372865
theorem B1943495 : Blo 1943435 1943495 := bstep (se 1 (by rfl) ⟨1457621, by rfl⟩ : syracuseStep 1943495 = 2915243) B2915243
theorem B2186437 : Blo 1943435 2186437 := bbase (se 4 (by rfl) ⟨204978, by rfl⟩ : syracuseStep 2186437 = 409957) (by norm_num)
theorem B2915249 : Blo 1943435 2915249 := bstep (se 2 (by rfl) ⟨1093218, by rfl⟩ : syracuseStep 2915249 = 2186437) B2186437
theorem B1943499 : Blo 1943435 1943499 := bstep (se 1 (by rfl) ⟨1457624, by rfl⟩ : syracuseStep 1943499 = 2915249) B2915249
theorem B3689621 : Blo 1943435 3689621 := bbase (se 6 (by rfl) ⟨86475, by rfl⟩ : syracuseStep 3689621 = 172951) (by norm_num)
theorem B2459747 : Blo 1943435 2459747 := bstep (se 1 (by rfl) ⟨1844810, by rfl⟩ : syracuseStep 2459747 = 3689621) B3689621
theorem B6559325 : Blo 1943435 6559325 := bstep (se 3 (by rfl) ⟨1229873, by rfl⟩ : syracuseStep 6559325 = 2459747) B2459747
theorem B4372883 : Blo 1943435 4372883 := bstep (se 1 (by rfl) ⟨3279662, by rfl⟩ : syracuseStep 4372883 = 6559325) B6559325
theorem B2915255 : Blo 1943435 2915255 := bstep (se 1 (by rfl) ⟨2186441, by rfl⟩ : syracuseStep 2915255 = 4372883) B4372883
theorem B1943503 : Blo 1943435 1943503 := bstep (se 1 (by rfl) ⟨1457627, by rfl⟩ : syracuseStep 1943503 = 2915255) B2915255
theorem B2915261 : Blo 1943435 2915261 := bbase (se 3 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 2915261 = 1093223) (by norm_num)
theorem B1943507 : Blo 1943435 1943507 := bstep (se 1 (by rfl) ⟨1457630, by rfl⟩ : syracuseStep 1943507 = 2915261) B2915261
theorem B4372901 : Blo 1943435 4372901 := bbase (se 4 (by rfl) ⟨409959, by rfl⟩ : syracuseStep 4372901 = 819919) (by norm_num)
theorem B2915267 : Blo 1943435 2915267 := bstep (se 1 (by rfl) ⟨2186450, by rfl⟩ : syracuseStep 2915267 = 4372901) B4372901
theorem B1943511 : Blo 1943435 1943511 := bstep (se 1 (by rfl) ⟨1457633, by rfl⟩ : syracuseStep 1943511 = 2915267) B2915267
theorem B4919525 : Blo 1943435 4919525 := bbase (se 4 (by rfl) ⟨461205, by rfl⟩ : syracuseStep 4919525 = 922411) (by norm_num)
theorem B3279683 : Blo 1943435 3279683 := bstep (se 1 (by rfl) ⟨2459762, by rfl⟩ : syracuseStep 3279683 = 4919525) B4919525
theorem B2186455 : Blo 1943435 2186455 := bstep (se 1 (by rfl) ⟨1639841, by rfl⟩ : syracuseStep 2186455 = 3279683) B3279683
theorem B2915273 : Blo 1943435 2915273 := bstep (se 2 (by rfl) ⟨1093227, by rfl⟩ : syracuseStep 2915273 = 2186455) B2186455
theorem B1943515 : Blo 1943435 1943515 := bstep (se 1 (by rfl) ⟨1457636, by rfl⟩ : syracuseStep 1943515 = 2915273) B2915273
theorem B2075429 : Blo 1943435 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B5534477 : Blo 1943435 5534477 := bstep (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) B2075429
theorem B3689651 : Blo 1943435 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B9839069 : Blo 1943435 9839069 := bstep (se 3 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 9839069 = 3689651) B3689651
theorem B6559379 : Blo 1943435 6559379 := bstep (se 1 (by rfl) ⟨4919534, by rfl⟩ : syracuseStep 6559379 = 9839069) B9839069
theorem B4372919 : Blo 1943435 4372919 := bstep (se 1 (by rfl) ⟨3279689, by rfl⟩ : syracuseStep 4372919 = 6559379) B6559379
theorem B2915279 : Blo 1943435 2915279 := bstep (se 1 (by rfl) ⟨2186459, by rfl⟩ : syracuseStep 2915279 = 4372919) B4372919
theorem B1943519 : Blo 1943435 1943519 := bstep (se 1 (by rfl) ⟨1457639, by rfl⟩ : syracuseStep 1943519 = 2915279) B2915279
theorem B2915285 : Blo 1943435 2915285 := bbase (se 7 (by rfl) ⟨34163, by rfl⟩ : syracuseStep 2915285 = 68327) (by norm_num)
theorem B1943523 : Blo 1943435 1943523 := bstep (se 1 (by rfl) ⟨1457642, by rfl⟩ : syracuseStep 1943523 = 2915285) B2915285
theorem B7379333 : Blo 1943435 7379333 := bbase (se 4 (by rfl) ⟨691812, by rfl⟩ : syracuseStep 7379333 = 1383625) (by norm_num)
theorem B4919555 : Blo 1943435 4919555 := bstep (se 1 (by rfl) ⟨3689666, by rfl⟩ : syracuseStep 4919555 = 7379333) B7379333
theorem B3279703 : Blo 1943435 3279703 := bstep (se 1 (by rfl) ⟨2459777, by rfl⟩ : syracuseStep 3279703 = 4919555) B4919555
theorem B4372937 : Blo 1943435 4372937 := bstep (se 2 (by rfl) ⟨1639851, by rfl⟩ : syracuseStep 4372937 = 3279703) B3279703
theorem B2915291 : Blo 1943435 2915291 := bstep (se 1 (by rfl) ⟨2186468, by rfl⟩ : syracuseStep 2915291 = 4372937) B4372937
theorem B1943527 : Blo 1943435 1943527 := bstep (se 1 (by rfl) ⟨1457645, by rfl⟩ : syracuseStep 1943527 = 2915291) B2915291
theorem B2186473 : Blo 1943435 2186473 := bbase (se 2 (by rfl) ⟨819927, by rfl⟩ : syracuseStep 2186473 = 1639855) (by norm_num)
theorem B2915297 : Blo 1943435 2915297 := bstep (se 2 (by rfl) ⟨1093236, by rfl⟩ : syracuseStep 2915297 = 2186473) B2186473
theorem B1943531 : Blo 1943435 1943531 := bstep (se 1 (by rfl) ⟨1457648, by rfl⟩ : syracuseStep 1943531 = 2915297) B2915297
theorem B11069045 : Blo 1943435 11069045 := bbase (se 5 (by rfl) ⟨518861, by rfl⟩ : syracuseStep 11069045 = 1037723) (by norm_num)
theorem B7379363 : Blo 1943435 7379363 := bstep (se 1 (by rfl) ⟨5534522, by rfl⟩ : syracuseStep 7379363 = 11069045) B11069045
theorem B4919575 : Blo 1943435 4919575 := bstep (se 1 (by rfl) ⟨3689681, by rfl⟩ : syracuseStep 4919575 = 7379363) B7379363
theorem B6559433 : Blo 1943435 6559433 := bstep (se 2 (by rfl) ⟨2459787, by rfl⟩ : syracuseStep 6559433 = 4919575) B4919575
theorem B4372955 : Blo 1943435 4372955 := bstep (se 1 (by rfl) ⟨3279716, by rfl⟩ : syracuseStep 4372955 = 6559433) B6559433
theorem B2915303 : Blo 1943435 2915303 := bstep (se 1 (by rfl) ⟨2186477, by rfl⟩ : syracuseStep 2915303 = 4372955) B4372955
theorem B1943535 : Blo 1943435 1943535 := bstep (se 1 (by rfl) ⟨1457651, by rfl⟩ : syracuseStep 1943535 = 2915303) B2915303
theorem B2915309 : Blo 1943435 2915309 := bbase (se 3 (by rfl) ⟨546620, by rfl⟩ : syracuseStep 2915309 = 1093241) (by norm_num)
theorem B1943539 : Blo 1943435 1943539 := bstep (se 1 (by rfl) ⟨1457654, by rfl⟩ : syracuseStep 1943539 = 2915309) B2915309
theorem B4372973 : Blo 1943435 4372973 := bbase (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) (by norm_num)
theorem B2915315 : Blo 1943435 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B1943543 : Blo 1943435 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B7004677 : Blo 1943435 7004677 := bbase (se 4 (by rfl) ⟨656688, by rfl⟩ : syracuseStep 7004677 = 1313377) (by norm_num)
theorem B9339569 : Blo 1943435 9339569 := bstep (se 2 (by rfl) ⟨3502338, by rfl⟩ : syracuseStep 9339569 = 7004677) B7004677
theorem B6226379 : Blo 1943435 6226379 := bstep (se 1 (by rfl) ⟨4669784, by rfl⟩ : syracuseStep 6226379 = 9339569) B9339569
theorem B4150919 : Blo 1943435 4150919 := bstep (se 1 (by rfl) ⟨3113189, by rfl⟩ : syracuseStep 4150919 = 6226379) B6226379
theorem B2767279 : Blo 1943435 2767279 := bstep (se 1 (by rfl) ⟨2075459, by rfl⟩ : syracuseStep 2767279 = 4150919) B4150919
theorem B3689705 : Blo 1943435 3689705 := bstep (se 2 (by rfl) ⟨1383639, by rfl⟩ : syracuseStep 3689705 = 2767279) B2767279
theorem B2459803 : Blo 1943435 2459803 := bstep (se 1 (by rfl) ⟨1844852, by rfl⟩ : syracuseStep 2459803 = 3689705) B3689705
theorem B3279737 : Blo 1943435 3279737 := bstep (se 2 (by rfl) ⟨1229901, by rfl⟩ : syracuseStep 3279737 = 2459803) B2459803
theorem B2186491 : Blo 1943435 2186491 := bstep (se 1 (by rfl) ⟨1639868, by rfl⟩ : syracuseStep 2186491 = 3279737) B3279737
theorem B2915321 : Blo 1943435 2915321 := bstep (se 2 (by rfl) ⟨1093245, by rfl⟩ : syracuseStep 2915321 = 2186491) B2186491
theorem B1943547 : Blo 1943435 1943547 := bstep (se 1 (by rfl) ⟨1457660, by rfl⟩ : syracuseStep 1943547 = 2915321) B2915321
theorem B8986261 : Blo 1943435 8986261 := bbase (se 6 (by rfl) ⟨210615, by rfl⟩ : syracuseStep 8986261 = 421231) (by norm_num)
theorem B11981681 : Blo 1943435 11981681 := bstep (se 2 (by rfl) ⟨4493130, by rfl⟩ : syracuseStep 11981681 = 8986261) B8986261
theorem B7987787 : Blo 1943435 7987787 := bstep (se 1 (by rfl) ⟨5990840, by rfl⟩ : syracuseStep 7987787 = 11981681) B11981681
theorem B5325191 : Blo 1943435 5325191 := bstep (se 1 (by rfl) ⟨3993893, by rfl⟩ : syracuseStep 5325191 = 7987787) B7987787
theorem B227208149 : Blo 1943435 227208149 := bstep (se 7 (by rfl) ⟨2662595, by rfl⟩ : syracuseStep 227208149 = 5325191) B5325191
theorem B151472099 : Blo 1943435 151472099 := bstep (se 1 (by rfl) ⟨113604074, by rfl⟩ : syracuseStep 151472099 = 227208149) B227208149
theorem B100981399 : Blo 1943435 100981399 := bstep (se 1 (by rfl) ⟨75736049, by rfl⟩ : syracuseStep 100981399 = 151472099) B151472099
theorem B134641865 : Blo 1943435 134641865 := bstep (se 2 (by rfl) ⟨50490699, by rfl⟩ : syracuseStep 134641865 = 100981399) B100981399
theorem B89761243 : Blo 1943435 89761243 := bstep (se 1 (by rfl) ⟨67320932, by rfl⟩ : syracuseStep 89761243 = 134641865) B134641865
theorem B119681657 : Blo 1943435 119681657 := bstep (se 2 (by rfl) ⟨44880621, by rfl⟩ : syracuseStep 119681657 = 89761243) B89761243
theorem B79787771 : Blo 1943435 79787771 := bstep (se 1 (by rfl) ⟨59840828, by rfl⟩ : syracuseStep 79787771 = 119681657) B119681657
theorem B53191847 : Blo 1943435 53191847 := bstep (se 1 (by rfl) ⟨39893885, by rfl⟩ : syracuseStep 53191847 = 79787771) B79787771
theorem B141844925 : Blo 1943435 141844925 := bstep (se 3 (by rfl) ⟨26595923, by rfl⟩ : syracuseStep 141844925 = 53191847) B53191847
theorem B94563283 : Blo 1943435 94563283 := bstep (se 1 (by rfl) ⟨70922462, by rfl⟩ : syracuseStep 94563283 = 141844925) B141844925
theorem B126084377 : Blo 1943435 126084377 := bstep (se 2 (by rfl) ⟨47281641, by rfl⟩ : syracuseStep 126084377 = 94563283) B94563283
theorem B84056251 : Blo 1943435 84056251 := bstep (se 1 (by rfl) ⟨63042188, by rfl⟩ : syracuseStep 84056251 = 126084377) B126084377
theorem B112075001 : Blo 1943435 112075001 := bstep (se 2 (by rfl) ⟨42028125, by rfl⟩ : syracuseStep 112075001 = 84056251) B84056251
theorem B74716667 : Blo 1943435 74716667 := bstep (se 1 (by rfl) ⟨56037500, by rfl⟩ : syracuseStep 74716667 = 112075001) B112075001
theorem B49811111 : Blo 1943435 49811111 := bstep (se 1 (by rfl) ⟨37358333, by rfl⟩ : syracuseStep 49811111 = 74716667) B74716667
theorem B33207407 : Blo 1943435 33207407 := bstep (se 1 (by rfl) ⟨24905555, by rfl⟩ : syracuseStep 33207407 = 49811111) B49811111
theorem B22138271 : Blo 1943435 22138271 := bstep (se 1 (by rfl) ⟨16603703, by rfl⟩ : syracuseStep 22138271 = 33207407) B33207407
theorem B14758847 : Blo 1943435 14758847 := bstep (se 1 (by rfl) ⟨11069135, by rfl⟩ : syracuseStep 14758847 = 22138271) B22138271
theorem B9839231 : Blo 1943435 9839231 := bstep (se 1 (by rfl) ⟨7379423, by rfl⟩ : syracuseStep 9839231 = 14758847) B14758847
theorem B6559487 : Blo 1943435 6559487 := bstep (se 1 (by rfl) ⟨4919615, by rfl⟩ : syracuseStep 6559487 = 9839231) B9839231
theorem B4372991 : Blo 1943435 4372991 := bstep (se 1 (by rfl) ⟨3279743, by rfl⟩ : syracuseStep 4372991 = 6559487) B6559487
theorem B2915327 : Blo 1943435 2915327 := bstep (se 1 (by rfl) ⟨2186495, by rfl⟩ : syracuseStep 2915327 = 4372991) B4372991
theorem B1943551 : Blo 1943435 1943551 := bstep (se 1 (by rfl) ⟨1457663, by rfl⟩ : syracuseStep 1943551 = 2915327) B2915327
theorem B2915333 : Blo 1943435 2915333 := bbase (se 4 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 2915333 = 546625) (by norm_num)
theorem B1943555 : Blo 1943435 1943555 := bstep (se 1 (by rfl) ⟨1457666, by rfl⟩ : syracuseStep 1943555 = 2915333) B2915333
theorem B3279757 : Blo 1943435 3279757 := bbase (se 3 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 3279757 = 1229909) (by norm_num)
theorem B4373009 : Blo 1943435 4373009 := bstep (se 2 (by rfl) ⟨1639878, by rfl⟩ : syracuseStep 4373009 = 3279757) B3279757
theorem B2915339 : Blo 1943435 2915339 := bstep (se 1 (by rfl) ⟨2186504, by rfl⟩ : syracuseStep 2915339 = 4373009) B4373009
theorem B1943559 : Blo 1943435 1943559 := bstep (se 1 (by rfl) ⟨1457669, by rfl⟩ : syracuseStep 1943559 = 2915339) B2915339
theorem B2186509 : Blo 1943435 2186509 := bbase (se 3 (by rfl) ⟨409970, by rfl⟩ : syracuseStep 2186509 = 819941) (by norm_num)
theorem B2915345 : Blo 1943435 2915345 := bstep (se 2 (by rfl) ⟨1093254, by rfl⟩ : syracuseStep 2915345 = 2186509) B2186509
theorem B1943563 : Blo 1943435 1943563 := bstep (se 1 (by rfl) ⟨1457672, by rfl⟩ : syracuseStep 1943563 = 2915345) B2915345
theorem B6559541 : Blo 1943435 6559541 := bbase (se 5 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 6559541 = 614957) (by norm_num)
theorem B4373027 : Blo 1943435 4373027 := bstep (se 1 (by rfl) ⟨3279770, by rfl⟩ : syracuseStep 4373027 = 6559541) B6559541
theorem B2915351 : Blo 1943435 2915351 := bstep (se 1 (by rfl) ⟨2186513, by rfl⟩ : syracuseStep 2915351 = 4373027) B4373027
theorem B1943567 : Blo 1943435 1943567 := bstep (se 1 (by rfl) ⟨1457675, by rfl⟩ : syracuseStep 1943567 = 2915351) B2915351
theorem B2915357 : Blo 1943435 2915357 := bbase (se 3 (by rfl) ⟨546629, by rfl⟩ : syracuseStep 2915357 = 1093259) (by norm_num)
theorem B1943571 : Blo 1943435 1943571 := bstep (se 1 (by rfl) ⟨1457678, by rfl⟩ : syracuseStep 1943571 = 2915357) B2915357
theorem B4373045 : Blo 1943435 4373045 := bbase (se 5 (by rfl) ⟨204986, by rfl⟩ : syracuseStep 4373045 = 409973) (by norm_num)
theorem B2915363 : Blo 1943435 2915363 := bstep (se 1 (by rfl) ⟨2186522, by rfl⟩ : syracuseStep 2915363 = 4373045) B4373045
theorem B1943575 : Blo 1943435 1943575 := bstep (se 1 (by rfl) ⟨1457681, by rfl⟩ : syracuseStep 1943575 = 2915363) B2915363
theorem B8301973 : Blo 1943435 8301973 := bbase (se 6 (by rfl) ⟨194577, by rfl⟩ : syracuseStep 8301973 = 389155) (by norm_num)
theorem B11069297 : Blo 1943435 11069297 := bstep (se 2 (by rfl) ⟨4150986, by rfl⟩ : syracuseStep 11069297 = 8301973) B8301973
theorem B7379531 : Blo 1943435 7379531 := bstep (se 1 (by rfl) ⟨5534648, by rfl⟩ : syracuseStep 7379531 = 11069297) B11069297
theorem B4919687 : Blo 1943435 4919687 := bstep (se 1 (by rfl) ⟨3689765, by rfl⟩ : syracuseStep 4919687 = 7379531) B7379531
theorem B3279791 : Blo 1943435 3279791 := bstep (se 1 (by rfl) ⟨2459843, by rfl⟩ : syracuseStep 3279791 = 4919687) B4919687
theorem B2186527 : Blo 1943435 2186527 := bstep (se 1 (by rfl) ⟨1639895, by rfl⟩ : syracuseStep 2186527 = 3279791) B3279791
theorem B2915369 : Blo 1943435 2915369 := bstep (se 2 (by rfl) ⟨1093263, by rfl⟩ : syracuseStep 2915369 = 2186527) B2186527
theorem B1943579 : Blo 1943435 1943579 := bstep (se 1 (by rfl) ⟨1457684, by rfl⟩ : syracuseStep 1943579 = 2915369) B2915369
theorem B8301989 : Blo 1943435 8301989 := bbase (se 4 (by rfl) ⟨778311, by rfl⟩ : syracuseStep 8301989 = 1556623) (by norm_num)
theorem B5534659 : Blo 1943435 5534659 := bstep (se 1 (by rfl) ⟨4150994, by rfl⟩ : syracuseStep 5534659 = 8301989) B8301989
theorem B7379545 : Blo 1943435 7379545 := bstep (se 2 (by rfl) ⟨2767329, by rfl⟩ : syracuseStep 7379545 = 5534659) B5534659
theorem B9839393 : Blo 1943435 9839393 := bstep (se 2 (by rfl) ⟨3689772, by rfl⟩ : syracuseStep 9839393 = 7379545) B7379545
theorem B6559595 : Blo 1943435 6559595 := bstep (se 1 (by rfl) ⟨4919696, by rfl⟩ : syracuseStep 6559595 = 9839393) B9839393
theorem B4373063 : Blo 1943435 4373063 := bstep (se 1 (by rfl) ⟨3279797, by rfl⟩ : syracuseStep 4373063 = 6559595) B6559595
theorem B2915375 : Blo 1943435 2915375 := bstep (se 1 (by rfl) ⟨2186531, by rfl⟩ : syracuseStep 2915375 = 4373063) B4373063
theorem B1943583 : Blo 1943435 1943583 := bstep (se 1 (by rfl) ⟨1457687, by rfl⟩ : syracuseStep 1943583 = 2915375) B2915375
theorem B2915381 : Blo 1943435 2915381 := bbase (se 5 (by rfl) ⟨136658, by rfl⟩ : syracuseStep 2915381 = 273317) (by norm_num)
theorem B1943587 : Blo 1943435 1943587 := bstep (se 1 (by rfl) ⟨1457690, by rfl⟩ : syracuseStep 1943587 = 2915381) B2915381
theorem B4919717 : Blo 1943435 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B3279811 : Blo 1943435 3279811 := bstep (se 1 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 3279811 = 4919717) B4919717
theorem B4373081 : Blo 1943435 4373081 := bstep (se 2 (by rfl) ⟨1639905, by rfl⟩ : syracuseStep 4373081 = 3279811) B3279811
theorem B2915387 : Blo 1943435 2915387 := bstep (se 1 (by rfl) ⟨2186540, by rfl⟩ : syracuseStep 2915387 = 4373081) B4373081
theorem B1943591 : Blo 1943435 1943591 := bstep (se 1 (by rfl) ⟨1457693, by rfl⟩ : syracuseStep 1943591 = 2915387) B2915387
theorem B2186545 : Blo 1943435 2186545 := bbase (se 2 (by rfl) ⟨819954, by rfl⟩ : syracuseStep 2186545 = 1639909) (by norm_num)
theorem B2915393 : Blo 1943435 2915393 := bstep (se 2 (by rfl) ⟨1093272, by rfl⟩ : syracuseStep 2915393 = 2186545) B2186545
theorem B1943595 : Blo 1943435 1943595 := bstep (se 1 (by rfl) ⟨1457696, by rfl⟩ : syracuseStep 1943595 = 2915393) B2915393
theorem B4151029 : Blo 1943435 4151029 := bbase (se 5 (by rfl) ⟨194579, by rfl⟩ : syracuseStep 4151029 = 389159) (by norm_num)
theorem B5534705 : Blo 1943435 5534705 := bstep (se 2 (by rfl) ⟨2075514, by rfl⟩ : syracuseStep 5534705 = 4151029) B4151029
theorem B3689803 : Blo 1943435 3689803 := bstep (se 1 (by rfl) ⟨2767352, by rfl⟩ : syracuseStep 3689803 = 5534705) B5534705
theorem B4919737 : Blo 1943435 4919737 := bstep (se 2 (by rfl) ⟨1844901, by rfl⟩ : syracuseStep 4919737 = 3689803) B3689803
theorem B6559649 : Blo 1943435 6559649 := bstep (se 2 (by rfl) ⟨2459868, by rfl⟩ : syracuseStep 6559649 = 4919737) B4919737
theorem B4373099 : Blo 1943435 4373099 := bstep (se 1 (by rfl) ⟨3279824, by rfl⟩ : syracuseStep 4373099 = 6559649) B6559649
theorem B2915399 : Blo 1943435 2915399 := bstep (se 1 (by rfl) ⟨2186549, by rfl⟩ : syracuseStep 2915399 = 4373099) B4373099
theorem B1943599 : Blo 1943435 1943599 := bstep (se 1 (by rfl) ⟨1457699, by rfl⟩ : syracuseStep 1943599 = 2915399) B2915399
theorem B2915405 : Blo 1943435 2915405 := bbase (se 3 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 2915405 = 1093277) (by norm_num)
theorem B1943603 : Blo 1943435 1943603 := bstep (se 1 (by rfl) ⟨1457702, by rfl⟩ : syracuseStep 1943603 = 2915405) B2915405
theorem B4373117 : Blo 1943435 4373117 := bbase (se 3 (by rfl) ⟨819959, by rfl⟩ : syracuseStep 4373117 = 1639919) (by norm_num)
theorem B2915411 : Blo 1943435 2915411 := bstep (se 1 (by rfl) ⟨2186558, by rfl⟩ : syracuseStep 2915411 = 4373117) B4373117
theorem B1943607 : Blo 1943435 1943607 := bstep (se 1 (by rfl) ⟨1457705, by rfl⟩ : syracuseStep 1943607 = 2915411) B2915411
theorem B3279845 : Blo 1943435 3279845 := bbase (se 4 (by rfl) ⟨307485, by rfl⟩ : syracuseStep 3279845 = 614971) (by norm_num)
theorem B2186563 : Blo 1943435 2186563 := bstep (se 1 (by rfl) ⟨1639922, by rfl⟩ : syracuseStep 2186563 = 3279845) B3279845
theorem B2915417 : Blo 1943435 2915417 := bstep (se 2 (by rfl) ⟨1093281, by rfl⟩ : syracuseStep 2915417 = 2186563) B2186563
theorem B1943611 : Blo 1943435 1943611 := bstep (se 1 (by rfl) ⟨1457708, by rfl⟩ : syracuseStep 1943611 = 2915417) B2915417
theorem B9339893 : Blo 1943435 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B6226595 : Blo 1943435 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B4151063 : Blo 1943435 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B2767375 : Blo 1943435 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B14759333 : Blo 1943435 14759333 := bstep (se 4 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 14759333 = 2767375) B2767375
theorem B9839555 : Blo 1943435 9839555 := bstep (se 1 (by rfl) ⟨7379666, by rfl⟩ : syracuseStep 9839555 = 14759333) B14759333
theorem B6559703 : Blo 1943435 6559703 := bstep (se 1 (by rfl) ⟨4919777, by rfl⟩ : syracuseStep 6559703 = 9839555) B9839555
theorem B4373135 : Blo 1943435 4373135 := bstep (se 1 (by rfl) ⟨3279851, by rfl⟩ : syracuseStep 4373135 = 6559703) B6559703
theorem B2915423 : Blo 1943435 2915423 := bstep (se 1 (by rfl) ⟨2186567, by rfl⟩ : syracuseStep 2915423 = 4373135) B4373135
theorem B1943615 : Blo 1943435 1943615 := bstep (se 1 (by rfl) ⟨1457711, by rfl⟩ : syracuseStep 1943615 = 2915423) B2915423
theorem B2915429 : Blo 1943435 2915429 := bbase (se 4 (by rfl) ⟨273321, by rfl⟩ : syracuseStep 2915429 = 546643) (by norm_num)
theorem B1943619 : Blo 1943435 1943619 := bstep (se 1 (by rfl) ⟨1457714, by rfl⟩ : syracuseStep 1943619 = 2915429) B2915429
theorem B15761141 : Blo 1943435 15761141 := bbase (se 5 (by rfl) ⟨738803, by rfl⟩ : syracuseStep 15761141 = 1477607) (by norm_num)
theorem B10507427 : Blo 1943435 10507427 := bstep (se 1 (by rfl) ⟨7880570, by rfl⟩ : syracuseStep 10507427 = 15761141) B15761141
theorem B7004951 : Blo 1943435 7004951 := bstep (se 1 (by rfl) ⟨5253713, by rfl⟩ : syracuseStep 7004951 = 10507427) B10507427
theorem B4669967 : Blo 1943435 4669967 := bstep (se 1 (by rfl) ⟨3502475, by rfl⟩ : syracuseStep 4669967 = 7004951) B7004951
theorem B3113311 : Blo 1943435 3113311 := bstep (se 1 (by rfl) ⟨2334983, by rfl⟩ : syracuseStep 3113311 = 4669967) B4669967
theorem B4151081 : Blo 1943435 4151081 := bstep (se 2 (by rfl) ⟨1556655, by rfl⟩ : syracuseStep 4151081 = 3113311) B3113311
theorem B2767387 : Blo 1943435 2767387 := bstep (se 1 (by rfl) ⟨2075540, by rfl⟩ : syracuseStep 2767387 = 4151081) B4151081
theorem B3689849 : Blo 1943435 3689849 := bstep (se 2 (by rfl) ⟨1383693, by rfl⟩ : syracuseStep 3689849 = 2767387) B2767387
theorem B2459899 : Blo 1943435 2459899 := bstep (se 1 (by rfl) ⟨1844924, by rfl⟩ : syracuseStep 2459899 = 3689849) B3689849
theorem B3279865 : Blo 1943435 3279865 := bstep (se 2 (by rfl) ⟨1229949, by rfl⟩ : syracuseStep 3279865 = 2459899) B2459899
theorem B4373153 : Blo 1943435 4373153 := bstep (se 2 (by rfl) ⟨1639932, by rfl⟩ : syracuseStep 4373153 = 3279865) B3279865
theorem B2915435 : Blo 1943435 2915435 := bstep (se 1 (by rfl) ⟨2186576, by rfl⟩ : syracuseStep 2915435 = 4373153) B4373153
theorem B1943623 : Blo 1943435 1943623 := bstep (se 1 (by rfl) ⟨1457717, by rfl⟩ : syracuseStep 1943623 = 2915435) B2915435
theorem B2186581 : Blo 1943435 2186581 := bbase (se 11 (by rfl) ⟨1601, by rfl⟩ : syracuseStep 2186581 = 3203) (by norm_num)
theorem B2915441 : Blo 1943435 2915441 := bstep (se 2 (by rfl) ⟨1093290, by rfl⟩ : syracuseStep 2915441 = 2186581) B2186581
theorem B1943627 : Blo 1943435 1943627 := bstep (se 1 (by rfl) ⟨1457720, by rfl⟩ : syracuseStep 1943627 = 2915441) B2915441
theorem B2459909 : Blo 1943435 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B6559757 : Blo 1943435 6559757 := bstep (se 3 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 6559757 = 2459909) B2459909
theorem B4373171 : Blo 1943435 4373171 := bstep (se 1 (by rfl) ⟨3279878, by rfl⟩ : syracuseStep 4373171 = 6559757) B6559757
theorem B2915447 : Blo 1943435 2915447 := bstep (se 1 (by rfl) ⟨2186585, by rfl⟩ : syracuseStep 2915447 = 4373171) B4373171
theorem B1943631 : Blo 1943435 1943631 := bstep (se 1 (by rfl) ⟨1457723, by rfl⟩ : syracuseStep 1943631 = 2915447) B2915447
theorem B2915453 : Blo 1943435 2915453 := bbase (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) (by norm_num)
theorem B1943635 : Blo 1943435 1943635 := bstep (se 1 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 1943635 = 2915453) B2915453
theorem B4373189 : Blo 1943435 4373189 := bbase (se 4 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 4373189 = 819973) (by norm_num)
theorem B2915459 : Blo 1943435 2915459 := bstep (se 1 (by rfl) ⟨2186594, by rfl⟩ : syracuseStep 2915459 = 4373189) B4373189
theorem B1943639 : Blo 1943435 1943639 := bstep (se 1 (by rfl) ⟨1457729, by rfl⟩ : syracuseStep 1943639 = 2915459) B2915459
theorem B7100597 : Blo 1943435 7100597 := bbase (se 5 (by rfl) ⟨332840, by rfl⟩ : syracuseStep 7100597 = 665681) (by norm_num)
theorem B4733731 : Blo 1943435 4733731 := bstep (se 1 (by rfl) ⟨3550298, by rfl⟩ : syracuseStep 4733731 = 7100597) B7100597
theorem B6311641 : Blo 1943435 6311641 := bstep (se 2 (by rfl) ⟨2366865, by rfl⟩ : syracuseStep 6311641 = 4733731) B4733731
theorem B8415521 : Blo 1943435 8415521 := bstep (se 2 (by rfl) ⟨3155820, by rfl⟩ : syracuseStep 8415521 = 6311641) B6311641
theorem B5610347 : Blo 1943435 5610347 := bstep (se 1 (by rfl) ⟨4207760, by rfl⟩ : syracuseStep 5610347 = 8415521) B8415521
theorem B3740231 : Blo 1943435 3740231 := bstep (se 1 (by rfl) ⟨2805173, by rfl⟩ : syracuseStep 3740231 = 5610347) B5610347
theorem B2493487 : Blo 1943435 2493487 := bstep (se 1 (by rfl) ⟨1870115, by rfl⟩ : syracuseStep 2493487 = 3740231) B3740231
theorem B13298597 : Blo 1943435 13298597 := bstep (se 4 (by rfl) ⟨1246743, by rfl⟩ : syracuseStep 13298597 = 2493487) B2493487
theorem B8865731 : Blo 1943435 8865731 := bstep (se 1 (by rfl) ⟨6649298, by rfl⟩ : syracuseStep 8865731 = 13298597) B13298597
theorem B23641949 : Blo 1943435 23641949 := bstep (se 3 (by rfl) ⟨4432865, by rfl⟩ : syracuseStep 23641949 = 8865731) B8865731
theorem B15761299 : Blo 1943435 15761299 := bstep (se 1 (by rfl) ⟨11820974, by rfl⟩ : syracuseStep 15761299 = 23641949) B23641949
theorem B21015065 : Blo 1943435 21015065 := bstep (se 2 (by rfl) ⟨7880649, by rfl⟩ : syracuseStep 21015065 = 15761299) B15761299
theorem B14010043 : Blo 1943435 14010043 := bstep (se 1 (by rfl) ⟨10507532, by rfl⟩ : syracuseStep 14010043 = 21015065) B21015065
theorem B18680057 : Blo 1943435 18680057 := bstep (se 2 (by rfl) ⟨7005021, by rfl⟩ : syracuseStep 18680057 = 14010043) B14010043
theorem B12453371 : Blo 1943435 12453371 := bstep (se 1 (by rfl) ⟨9340028, by rfl⟩ : syracuseStep 12453371 = 18680057) B18680057
theorem B8302247 : Blo 1943435 8302247 := bstep (se 1 (by rfl) ⟨6226685, by rfl⟩ : syracuseStep 8302247 = 12453371) B12453371
theorem B5534831 : Blo 1943435 5534831 := bstep (se 1 (by rfl) ⟨4151123, by rfl⟩ : syracuseStep 5534831 = 8302247) B8302247
theorem B3689887 : Blo 1943435 3689887 := bstep (se 1 (by rfl) ⟨2767415, by rfl⟩ : syracuseStep 3689887 = 5534831) B5534831
theorem B4919849 : Blo 1943435 4919849 := bstep (se 2 (by rfl) ⟨1844943, by rfl⟩ : syracuseStep 4919849 = 3689887) B3689887
theorem B3279899 : Blo 1943435 3279899 := bstep (se 1 (by rfl) ⟨2459924, by rfl⟩ : syracuseStep 3279899 = 4919849) B4919849
theorem B2186599 : Blo 1943435 2186599 := bstep (se 1 (by rfl) ⟨1639949, by rfl⟩ : syracuseStep 2186599 = 3279899) B3279899
theorem B2915465 : Blo 1943435 2915465 := bstep (se 2 (by rfl) ⟨1093299, by rfl⟩ : syracuseStep 2915465 = 2186599) B2186599
theorem B1943643 : Blo 1943435 1943643 := bstep (se 1 (by rfl) ⟨1457732, by rfl⟩ : syracuseStep 1943643 = 2915465) B2915465
theorem B9839717 : Blo 1943435 9839717 := bbase (se 4 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 9839717 = 1844947) (by norm_num)
theorem B6559811 : Blo 1943435 6559811 := bstep (se 1 (by rfl) ⟨4919858, by rfl⟩ : syracuseStep 6559811 = 9839717) B9839717
theorem B4373207 : Blo 1943435 4373207 := bstep (se 1 (by rfl) ⟨3279905, by rfl⟩ : syracuseStep 4373207 = 6559811) B6559811
theorem B2915471 : Blo 1943435 2915471 := bstep (se 1 (by rfl) ⟨2186603, by rfl⟩ : syracuseStep 2915471 = 4373207) B4373207
theorem B1943647 : Blo 1943435 1943647 := bstep (se 1 (by rfl) ⟨1457735, by rfl⟩ : syracuseStep 1943647 = 2915471) B2915471
theorem B2915477 : Blo 1943435 2915477 := bbase (se 6 (by rfl) ⟨68331, by rfl⟩ : syracuseStep 2915477 = 136663) (by norm_num)
theorem B1943651 : Blo 1943435 1943651 := bstep (se 1 (by rfl) ⟨1457738, by rfl⟩ : syracuseStep 1943651 = 2915477) B2915477
theorem B9340085 : Blo 1943435 9340085 := bbase (se 5 (by rfl) ⟨437816, by rfl⟩ : syracuseStep 9340085 = 875633) (by norm_num)
theorem B6226723 : Blo 1943435 6226723 := bstep (se 1 (by rfl) ⟨4670042, by rfl⟩ : syracuseStep 6226723 = 9340085) B9340085
theorem B8302297 : Blo 1943435 8302297 := bstep (se 2 (by rfl) ⟨3113361, by rfl⟩ : syracuseStep 8302297 = 6226723) B6226723
theorem B11069729 : Blo 1943435 11069729 := bstep (se 2 (by rfl) ⟨4151148, by rfl⟩ : syracuseStep 11069729 = 8302297) B8302297
theorem B7379819 : Blo 1943435 7379819 := bstep (se 1 (by rfl) ⟨5534864, by rfl⟩ : syracuseStep 7379819 = 11069729) B11069729
theorem B4919879 : Blo 1943435 4919879 := bstep (se 1 (by rfl) ⟨3689909, by rfl⟩ : syracuseStep 4919879 = 7379819) B7379819
theorem B3279919 : Blo 1943435 3279919 := bstep (se 1 (by rfl) ⟨2459939, by rfl⟩ : syracuseStep 3279919 = 4919879) B4919879
theorem B4373225 : Blo 1943435 4373225 := bstep (se 2 (by rfl) ⟨1639959, by rfl⟩ : syracuseStep 4373225 = 3279919) B3279919
theorem B2915483 : Blo 1943435 2915483 := bstep (se 1 (by rfl) ⟨2186612, by rfl⟩ : syracuseStep 2915483 = 4373225) B4373225
theorem B1943655 : Blo 1943435 1943655 := bstep (se 1 (by rfl) ⟨1457741, by rfl⟩ : syracuseStep 1943655 = 2915483) B2915483
theorem B2186617 : Blo 1943435 2186617 := bbase (se 2 (by rfl) ⟨819981, by rfl⟩ : syracuseStep 2186617 = 1639963) (by norm_num)
theorem B2915489 : Blo 1943435 2915489 := bstep (se 2 (by rfl) ⟨1093308, by rfl⟩ : syracuseStep 2915489 = 2186617) B2186617
theorem B1943659 : Blo 1943435 1943659 := bstep (se 1 (by rfl) ⟨1457744, by rfl⟩ : syracuseStep 1943659 = 2915489) B2915489
theorem B3740269 : Blo 1943435 3740269 := bbase (se 3 (by rfl) ⟨701300, by rfl⟩ : syracuseStep 3740269 = 1402601) (by norm_num)
theorem B4987025 : Blo 1943435 4987025 := bstep (se 2 (by rfl) ⟨1870134, by rfl⟩ : syracuseStep 4987025 = 3740269) B3740269
theorem B3324683 : Blo 1943435 3324683 := bstep (se 1 (by rfl) ⟨2493512, by rfl⟩ : syracuseStep 3324683 = 4987025) B4987025
theorem B8865821 : Blo 1943435 8865821 := bstep (se 3 (by rfl) ⟨1662341, by rfl⟩ : syracuseStep 8865821 = 3324683) B3324683
theorem B23642189 : Blo 1943435 23642189 := bstep (se 3 (by rfl) ⟨4432910, by rfl⟩ : syracuseStep 23642189 = 8865821) B8865821
theorem B15761459 : Blo 1943435 15761459 := bstep (se 1 (by rfl) ⟨11821094, by rfl⟩ : syracuseStep 15761459 = 23642189) B23642189
theorem B10507639 : Blo 1943435 10507639 := bstep (se 1 (by rfl) ⟨7880729, by rfl⟩ : syracuseStep 10507639 = 15761459) B15761459
theorem B14010185 : Blo 1943435 14010185 := bstep (se 2 (by rfl) ⟨5253819, by rfl⟩ : syracuseStep 14010185 = 10507639) B10507639
theorem B9340123 : Blo 1943435 9340123 := bstep (se 1 (by rfl) ⟨7005092, by rfl⟩ : syracuseStep 9340123 = 14010185) B14010185
theorem B12453497 : Blo 1943435 12453497 := bstep (se 2 (by rfl) ⟨4670061, by rfl⟩ : syracuseStep 12453497 = 9340123) B9340123
theorem B8302331 : Blo 1943435 8302331 := bstep (se 1 (by rfl) ⟨6226748, by rfl⟩ : syracuseStep 8302331 = 12453497) B12453497
theorem B5534887 : Blo 1943435 5534887 := bstep (se 1 (by rfl) ⟨4151165, by rfl⟩ : syracuseStep 5534887 = 8302331) B8302331
theorem B7379849 : Blo 1943435 7379849 := bstep (se 2 (by rfl) ⟨2767443, by rfl⟩ : syracuseStep 7379849 = 5534887) B5534887
theorem B4919899 : Blo 1943435 4919899 := bstep (se 1 (by rfl) ⟨3689924, by rfl⟩ : syracuseStep 4919899 = 7379849) B7379849
theorem B6559865 : Blo 1943435 6559865 := bstep (se 2 (by rfl) ⟨2459949, by rfl⟩ : syracuseStep 6559865 = 4919899) B4919899
theorem B4373243 : Blo 1943435 4373243 := bstep (se 1 (by rfl) ⟨3279932, by rfl⟩ : syracuseStep 4373243 = 6559865) B6559865
theorem B2915495 : Blo 1943435 2915495 := bstep (se 1 (by rfl) ⟨2186621, by rfl⟩ : syracuseStep 2915495 = 4373243) B4373243
theorem B1943663 : Blo 1943435 1943663 := bstep (se 1 (by rfl) ⟨1457747, by rfl⟩ : syracuseStep 1943663 = 2915495) B2915495
theorem B2915501 : Blo 1943435 2915501 := bbase (se 3 (by rfl) ⟨546656, by rfl⟩ : syracuseStep 2915501 = 1093313) (by norm_num)
theorem B1943667 : Blo 1943435 1943667 := bstep (se 1 (by rfl) ⟨1457750, by rfl⟩ : syracuseStep 1943667 = 2915501) B2915501
theorem B4373261 : Blo 1943435 4373261 := bbase (se 3 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 4373261 = 1639973) (by norm_num)
theorem B2915507 : Blo 1943435 2915507 := bstep (se 1 (by rfl) ⟨2186630, by rfl⟩ : syracuseStep 2915507 = 4373261) B4373261
theorem B1943671 : Blo 1943435 1943671 := bstep (se 1 (by rfl) ⟨1457753, by rfl⟩ : syracuseStep 1943671 = 2915507) B2915507
theorem B2459965 : Blo 1943435 2459965 := bbase (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) (by norm_num)
theorem B3279953 : Blo 1943435 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B2186635 : Blo 1943435 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B2915513 : Blo 1943435 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B1943675 : Blo 1943435 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B8865893 : Blo 1943435 8865893 := bbase (se 4 (by rfl) ⟨831177, by rfl⟩ : syracuseStep 8865893 = 1662355) (by norm_num)
theorem B23642381 : Blo 1943435 23642381 := bstep (se 3 (by rfl) ⟨4432946, by rfl⟩ : syracuseStep 23642381 = 8865893) B8865893
theorem B15761587 : Blo 1943435 15761587 := bstep (se 1 (by rfl) ⟨11821190, by rfl⟩ : syracuseStep 15761587 = 23642381) B23642381
theorem B21015449 : Blo 1943435 21015449 := bstep (se 2 (by rfl) ⟨7880793, by rfl⟩ : syracuseStep 21015449 = 15761587) B15761587
theorem B14010299 : Blo 1943435 14010299 := bstep (se 1 (by rfl) ⟨10507724, by rfl⟩ : syracuseStep 14010299 = 21015449) B21015449
theorem B9340199 : Blo 1943435 9340199 := bstep (se 1 (by rfl) ⟨7005149, by rfl⟩ : syracuseStep 9340199 = 14010299) B14010299
theorem B6226799 : Blo 1943435 6226799 := bstep (se 1 (by rfl) ⟨4670099, by rfl⟩ : syracuseStep 6226799 = 9340199) B9340199
theorem B16604797 : Blo 1943435 16604797 := bstep (se 3 (by rfl) ⟨3113399, by rfl⟩ : syracuseStep 16604797 = 6226799) B6226799
theorem B22139729 : Blo 1943435 22139729 := bstep (se 2 (by rfl) ⟨8302398, by rfl⟩ : syracuseStep 22139729 = 16604797) B16604797
theorem B14759819 : Blo 1943435 14759819 := bstep (se 1 (by rfl) ⟨11069864, by rfl⟩ : syracuseStep 14759819 = 22139729) B22139729
theorem B9839879 : Blo 1943435 9839879 := bstep (se 1 (by rfl) ⟨7379909, by rfl⟩ : syracuseStep 9839879 = 14759819) B14759819
theorem B6559919 : Blo 1943435 6559919 := bstep (se 1 (by rfl) ⟨4919939, by rfl⟩ : syracuseStep 6559919 = 9839879) B9839879
theorem B4373279 : Blo 1943435 4373279 := bstep (se 1 (by rfl) ⟨3279959, by rfl⟩ : syracuseStep 4373279 = 6559919) B6559919
theorem B2915519 : Blo 1943435 2915519 := bstep (se 1 (by rfl) ⟨2186639, by rfl⟩ : syracuseStep 2915519 = 4373279) B4373279
theorem B1943679 : Blo 1943435 1943679 := bstep (se 1 (by rfl) ⟨1457759, by rfl⟩ : syracuseStep 1943679 = 2915519) B2915519
theorem B2915525 : Blo 1943435 2915525 := bbase (se 4 (by rfl) ⟨273330, by rfl⟩ : syracuseStep 2915525 = 546661) (by norm_num)
theorem B1943683 : Blo 1943435 1943683 := bstep (se 1 (by rfl) ⟨1457762, by rfl⟩ : syracuseStep 1943683 = 2915525) B2915525
theorem B3279973 : Blo 1943435 3279973 := bbase (se 4 (by rfl) ⟨307497, by rfl⟩ : syracuseStep 3279973 = 614995) (by norm_num)
theorem B4373297 : Blo 1943435 4373297 := bstep (se 2 (by rfl) ⟨1639986, by rfl⟩ : syracuseStep 4373297 = 3279973) B3279973
theorem B2915531 : Blo 1943435 2915531 := bstep (se 1 (by rfl) ⟨2186648, by rfl⟩ : syracuseStep 2915531 = 4373297) B4373297
theorem B1943687 : Blo 1943435 1943687 := bstep (se 1 (by rfl) ⟨1457765, by rfl⟩ : syracuseStep 1943687 = 2915531) B2915531
theorem B2186653 : Blo 1943435 2186653 := bbase (se 3 (by rfl) ⟨409997, by rfl⟩ : syracuseStep 2186653 = 819995) (by norm_num)
theorem B2915537 : Blo 1943435 2915537 := bstep (se 2 (by rfl) ⟨1093326, by rfl⟩ : syracuseStep 2915537 = 2186653) B2186653
theorem B1943691 : Blo 1943435 1943691 := bstep (se 1 (by rfl) ⟨1457768, by rfl⟩ : syracuseStep 1943691 = 2915537) B2915537
theorem B6559973 : Blo 1943435 6559973 := bbase (se 4 (by rfl) ⟨614997, by rfl⟩ : syracuseStep 6559973 = 1229995) (by norm_num)
theorem B4373315 : Blo 1943435 4373315 := bstep (se 1 (by rfl) ⟨3279986, by rfl⟩ : syracuseStep 4373315 = 6559973) B6559973
theorem B2915543 : Blo 1943435 2915543 := bstep (se 1 (by rfl) ⟨2186657, by rfl⟩ : syracuseStep 2915543 = 4373315) B4373315
theorem B1943695 : Blo 1943435 1943695 := bstep (se 1 (by rfl) ⟨1457771, by rfl⟩ : syracuseStep 1943695 = 2915543) B2915543
theorem B2915549 : Blo 1943435 2915549 := bbase (se 3 (by rfl) ⟨546665, by rfl⟩ : syracuseStep 2915549 = 1093331) (by norm_num)
theorem B1943699 : Blo 1943435 1943699 := bstep (se 1 (by rfl) ⟨1457774, by rfl⟩ : syracuseStep 1943699 = 2915549) B2915549
theorem B4373333 : Blo 1943435 4373333 := bbase (se 9 (by rfl) ⟨12812, by rfl⟩ : syracuseStep 4373333 = 25625) (by norm_num)
theorem B2915555 : Blo 1943435 2915555 := bstep (se 1 (by rfl) ⟨2186666, by rfl⟩ : syracuseStep 2915555 = 4373333) B4373333
theorem B1943703 : Blo 1943435 1943703 := bstep (se 1 (by rfl) ⟨1457777, by rfl⟩ : syracuseStep 1943703 = 2915555) B2915555
theorem B5535013 : Blo 1943435 5535013 := bbase (se 4 (by rfl) ⟨518907, by rfl⟩ : syracuseStep 5535013 = 1037815) (by norm_num)
theorem B7380017 : Blo 1943435 7380017 := bstep (se 2 (by rfl) ⟨2767506, by rfl⟩ : syracuseStep 7380017 = 5535013) B5535013
theorem B4920011 : Blo 1943435 4920011 := bstep (se 1 (by rfl) ⟨3690008, by rfl⟩ : syracuseStep 4920011 = 7380017) B7380017
theorem B3280007 : Blo 1943435 3280007 := bstep (se 1 (by rfl) ⟨2460005, by rfl⟩ : syracuseStep 3280007 = 4920011) B4920011
theorem B2186671 : Blo 1943435 2186671 := bstep (se 1 (by rfl) ⟨1640003, by rfl⟩ : syracuseStep 2186671 = 3280007) B3280007
theorem B2915561 : Blo 1943435 2915561 := bstep (se 2 (by rfl) ⟨1093335, by rfl⟩ : syracuseStep 2915561 = 2186671) B2186671
theorem B1943707 : Blo 1943435 1943707 := bstep (se 1 (by rfl) ⟨1457780, by rfl⟩ : syracuseStep 1943707 = 2915561) B2915561
theorem B2103953 : Blo 1943435 2103953 := bbase (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) (by norm_num)
theorem B5610541 : Blo 1943435 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B7480721 : Blo 1943435 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B19948589 : Blo 1943435 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B13299059 : Blo 1943435 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B8866039 : Blo 1943435 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B11821385 : Blo 1943435 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B7880923 : Blo 1943435 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B10507897 : Blo 1943435 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B56042117 : Blo 1943435 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B37361411 : Blo 1943435 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B24907607 : Blo 1943435 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B16605071 : Blo 1943435 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B11070047 : Blo 1943435 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B7380031 : Blo 1943435 7380031 := bstep (se 1 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 7380031 = 11070047) B11070047
theorem B9840041 : Blo 1943435 9840041 := bstep (se 2 (by rfl) ⟨3690015, by rfl⟩ : syracuseStep 9840041 = 7380031) B7380031
theorem B6560027 : Blo 1943435 6560027 := bstep (se 1 (by rfl) ⟨4920020, by rfl⟩ : syracuseStep 6560027 = 9840041) B9840041
theorem B4373351 : Blo 1943435 4373351 := bstep (se 1 (by rfl) ⟨3280013, by rfl⟩ : syracuseStep 4373351 = 6560027) B6560027
theorem B2915567 : Blo 1943435 2915567 := bstep (se 1 (by rfl) ⟨2186675, by rfl⟩ : syracuseStep 2915567 = 4373351) B4373351
theorem B1943711 : Blo 1943435 1943711 := bstep (se 1 (by rfl) ⟨1457783, by rfl⟩ : syracuseStep 1943711 = 2915567) B2915567
theorem B2915573 : Blo 1943435 2915573 := bbase (se 5 (by rfl) ⟨136667, by rfl⟩ : syracuseStep 2915573 = 273335) (by norm_num)
theorem B1943715 : Blo 1943435 1943715 := bstep (se 1 (by rfl) ⟨1457786, by rfl⟩ : syracuseStep 1943715 = 2915573) B2915573
theorem B5610565 : Blo 1943435 5610565 := bbase (se 4 (by rfl) ⟨525990, by rfl⟩ : syracuseStep 5610565 = 1051981) (by norm_num)
theorem B29923013 : Blo 1943435 29923013 := bstep (se 4 (by rfl) ⟨2805282, by rfl⟩ : syracuseStep 29923013 = 5610565) B5610565
theorem B19948675 : Blo 1943435 19948675 := bstep (se 1 (by rfl) ⟨14961506, by rfl⟩ : syracuseStep 19948675 = 29923013) B29923013
theorem B26598233 : Blo 1943435 26598233 := bstep (se 2 (by rfl) ⟨9974337, by rfl⟩ : syracuseStep 26598233 = 19948675) B19948675
theorem B17732155 : Blo 1943435 17732155 := bstep (se 1 (by rfl) ⟨13299116, by rfl⟩ : syracuseStep 17732155 = 26598233) B26598233
theorem B23642873 : Blo 1943435 23642873 := bstep (se 2 (by rfl) ⟨8866077, by rfl⟩ : syracuseStep 23642873 = 17732155) B17732155
theorem B15761915 : Blo 1943435 15761915 := bstep (se 1 (by rfl) ⟨11821436, by rfl⟩ : syracuseStep 15761915 = 23642873) B23642873
theorem B10507943 : Blo 1943435 10507943 := bstep (se 1 (by rfl) ⟨7880957, by rfl⟩ : syracuseStep 10507943 = 15761915) B15761915
theorem B7005295 : Blo 1943435 7005295 := bstep (se 1 (by rfl) ⟨5253971, by rfl⟩ : syracuseStep 7005295 = 10507943) B10507943
theorem B9340393 : Blo 1943435 9340393 := bstep (se 2 (by rfl) ⟨3502647, by rfl⟩ : syracuseStep 9340393 = 7005295) B7005295
theorem B12453857 : Blo 1943435 12453857 := bstep (se 2 (by rfl) ⟨4670196, by rfl⟩ : syracuseStep 12453857 = 9340393) B9340393
theorem B8302571 : Blo 1943435 8302571 := bstep (se 1 (by rfl) ⟨6226928, by rfl⟩ : syracuseStep 8302571 = 12453857) B12453857
theorem B5535047 : Blo 1943435 5535047 := bstep (se 1 (by rfl) ⟨4151285, by rfl⟩ : syracuseStep 5535047 = 8302571) B8302571
theorem B3690031 : Blo 1943435 3690031 := bstep (se 1 (by rfl) ⟨2767523, by rfl⟩ : syracuseStep 3690031 = 5535047) B5535047
theorem B4920041 : Blo 1943435 4920041 := bstep (se 2 (by rfl) ⟨1845015, by rfl⟩ : syracuseStep 4920041 = 3690031) B3690031
theorem B3280027 : Blo 1943435 3280027 := bstep (se 1 (by rfl) ⟨2460020, by rfl⟩ : syracuseStep 3280027 = 4920041) B4920041
theorem B4373369 : Blo 1943435 4373369 := bstep (se 2 (by rfl) ⟨1640013, by rfl⟩ : syracuseStep 4373369 = 3280027) B3280027
theorem B2915579 : Blo 1943435 2915579 := bstep (se 1 (by rfl) ⟨2186684, by rfl⟩ : syracuseStep 2915579 = 4373369) B4373369
theorem B1943719 : Blo 1943435 1943719 := bstep (se 1 (by rfl) ⟨1457789, by rfl⟩ : syracuseStep 1943719 = 2915579) B2915579
theorem B2186689 : Blo 1943435 2186689 := bbase (se 2 (by rfl) ⟨820008, by rfl⟩ : syracuseStep 2186689 = 1640017) (by norm_num)
theorem B2915585 : Blo 1943435 2915585 := bstep (se 2 (by rfl) ⟨1093344, by rfl⟩ : syracuseStep 2915585 = 2186689) B2186689
theorem B1943723 : Blo 1943435 1943723 := bstep (se 1 (by rfl) ⟨1457792, by rfl⟩ : syracuseStep 1943723 = 2915585) B2915585
theorem B4920061 : Blo 1943435 4920061 := bbase (se 3 (by rfl) ⟨922511, by rfl⟩ : syracuseStep 4920061 = 1845023) (by norm_num)
theorem B6560081 : Blo 1943435 6560081 := bstep (se 2 (by rfl) ⟨2460030, by rfl⟩ : syracuseStep 6560081 = 4920061) B4920061
theorem B4373387 : Blo 1943435 4373387 := bstep (se 1 (by rfl) ⟨3280040, by rfl⟩ : syracuseStep 4373387 = 6560081) B6560081
theorem B2915591 : Blo 1943435 2915591 := bstep (se 1 (by rfl) ⟨2186693, by rfl⟩ : syracuseStep 2915591 = 4373387) B4373387
theorem B1943727 : Blo 1943435 1943727 := bstep (se 1 (by rfl) ⟨1457795, by rfl⟩ : syracuseStep 1943727 = 2915591) B2915591
theorem B2915597 : Blo 1943435 2915597 := bbase (se 3 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 2915597 = 1093349) (by norm_num)
theorem B1943731 : Blo 1943435 1943731 := bstep (se 1 (by rfl) ⟨1457798, by rfl⟩ : syracuseStep 1943731 = 2915597) B2915597
theorem B4373405 : Blo 1943435 4373405 := bbase (se 3 (by rfl) ⟨820013, by rfl⟩ : syracuseStep 4373405 = 1640027) (by norm_num)
theorem B2915603 : Blo 1943435 2915603 := bstep (se 1 (by rfl) ⟨2186702, by rfl⟩ : syracuseStep 2915603 = 4373405) B4373405
theorem B1943735 : Blo 1943435 1943735 := bstep (se 1 (by rfl) ⟨1457801, by rfl⟩ : syracuseStep 1943735 = 2915603) B2915603
theorem B3280061 : Blo 1943435 3280061 := bbase (se 3 (by rfl) ⟨615011, by rfl⟩ : syracuseStep 3280061 = 1230023) (by norm_num)
theorem B2186707 : Blo 1943435 2186707 := bstep (se 1 (by rfl) ⟨1640030, by rfl⟩ : syracuseStep 2186707 = 3280061) B3280061
theorem B2915609 : Blo 1943435 2915609 := bstep (se 2 (by rfl) ⟨1093353, by rfl⟩ : syracuseStep 2915609 = 2186707) B2186707
theorem B1943739 : Blo 1943435 1943739 := bstep (se 1 (by rfl) ⟨1457804, by rfl⟩ : syracuseStep 1943739 = 2915609) B2915609
theorem B11070229 : Blo 1943435 11070229 := bbase (se 6 (by rfl) ⟨259458, by rfl⟩ : syracuseStep 11070229 = 518917) (by norm_num)
theorem B14760305 : Blo 1943435 14760305 := bstep (se 2 (by rfl) ⟨5535114, by rfl⟩ : syracuseStep 14760305 = 11070229) B11070229
theorem B9840203 : Blo 1943435 9840203 := bstep (se 1 (by rfl) ⟨7380152, by rfl⟩ : syracuseStep 9840203 = 14760305) B14760305
theorem B6560135 : Blo 1943435 6560135 := bstep (se 1 (by rfl) ⟨4920101, by rfl⟩ : syracuseStep 6560135 = 9840203) B9840203
theorem B4373423 : Blo 1943435 4373423 := bstep (se 1 (by rfl) ⟨3280067, by rfl⟩ : syracuseStep 4373423 = 6560135) B6560135
theorem B2915615 : Blo 1943435 2915615 := bstep (se 1 (by rfl) ⟨2186711, by rfl⟩ : syracuseStep 2915615 = 4373423) B4373423
theorem B1943743 : Blo 1943435 1943743 := bstep (se 1 (by rfl) ⟨1457807, by rfl⟩ : syracuseStep 1943743 = 2915615) B2915615
theorem B2915621 : Blo 1943435 2915621 := bbase (se 4 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 2915621 = 546679) (by norm_num)
theorem B1943747 : Blo 1943435 1943747 := bstep (se 1 (by rfl) ⟨1457810, by rfl⟩ : syracuseStep 1943747 = 2915621) B2915621
theorem B2460061 : Blo 1943435 2460061 := bbase (se 3 (by rfl) ⟨461261, by rfl⟩ : syracuseStep 2460061 = 922523) (by norm_num)
theorem B3280081 : Blo 1943435 3280081 := bstep (se 2 (by rfl) ⟨1230030, by rfl⟩ : syracuseStep 3280081 = 2460061) B2460061
theorem B4373441 : Blo 1943435 4373441 := bstep (se 2 (by rfl) ⟨1640040, by rfl⟩ : syracuseStep 4373441 = 3280081) B3280081
theorem B2915627 : Blo 1943435 2915627 := bstep (se 1 (by rfl) ⟨2186720, by rfl⟩ : syracuseStep 2915627 = 4373441) B4373441
theorem B1943751 : Blo 1943435 1943751 := bstep (se 1 (by rfl) ⟨1457813, by rfl⟩ : syracuseStep 1943751 = 2915627) B2915627
theorem B2186725 : Blo 1943435 2186725 := bbase (se 4 (by rfl) ⟨205005, by rfl⟩ : syracuseStep 2186725 = 410011) (by norm_num)
theorem B2915633 : Blo 1943435 2915633 := bstep (se 2 (by rfl) ⟨1093362, by rfl⟩ : syracuseStep 2915633 = 2186725) B2186725
theorem B1943755 : Blo 1943435 1943755 := bstep (se 1 (by rfl) ⟨1457816, by rfl⟩ : syracuseStep 1943755 = 2915633) B2915633
theorem B4670293 : Blo 1943435 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B6227057 : Blo 1943435 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B4151371 : Blo 1943435 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B5535161 : Blo 1943435 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B3690107 : Blo 1943435 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B2460071 : Blo 1943435 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B6560189 : Blo 1943435 6560189 := bstep (se 3 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 6560189 = 2460071) B2460071
theorem B4373459 : Blo 1943435 4373459 := bstep (se 1 (by rfl) ⟨3280094, by rfl⟩ : syracuseStep 4373459 = 6560189) B6560189
theorem B2915639 : Blo 1943435 2915639 := bstep (se 1 (by rfl) ⟨2186729, by rfl⟩ : syracuseStep 2915639 = 4373459) B4373459
theorem B1943759 : Blo 1943435 1943759 := bstep (se 1 (by rfl) ⟨1457819, by rfl⟩ : syracuseStep 1943759 = 2915639) B2915639
theorem B2915645 : Blo 1943435 2915645 := bbase (se 3 (by rfl) ⟨546683, by rfl⟩ : syracuseStep 2915645 = 1093367) (by norm_num)
theorem B1943763 : Blo 1943435 1943763 := bstep (se 1 (by rfl) ⟨1457822, by rfl⟩ : syracuseStep 1943763 = 2915645) B2915645
theorem B4373477 : Blo 1943435 4373477 := bbase (se 4 (by rfl) ⟨410013, by rfl⟩ : syracuseStep 4373477 = 820027) (by norm_num)
theorem B2915651 : Blo 1943435 2915651 := bstep (se 1 (by rfl) ⟨2186738, by rfl⟩ : syracuseStep 2915651 = 4373477) B4373477
theorem B1943767 : Blo 1943435 1943767 := bstep (se 1 (by rfl) ⟨1457825, by rfl⟩ : syracuseStep 1943767 = 2915651) B2915651
theorem B4920173 : Blo 1943435 4920173 := bbase (se 3 (by rfl) ⟨922532, by rfl⟩ : syracuseStep 4920173 = 1845065) (by norm_num)
theorem B3280115 : Blo 1943435 3280115 := bstep (se 1 (by rfl) ⟨2460086, by rfl⟩ : syracuseStep 3280115 = 4920173) B4920173
theorem B2186743 : Blo 1943435 2186743 := bstep (se 1 (by rfl) ⟨1640057, by rfl⟩ : syracuseStep 2186743 = 3280115) B3280115
theorem B2915657 : Blo 1943435 2915657 := bstep (se 2 (by rfl) ⟨1093371, by rfl⟩ : syracuseStep 2915657 = 2186743) B2186743
theorem B1943771 : Blo 1943435 1943771 := bstep (se 1 (by rfl) ⟨1457828, by rfl⟩ : syracuseStep 1943771 = 2915657) B2915657
theorem B4151405 : Blo 1943435 4151405 := bbase (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) (by norm_num)
theorem B2767603 : Blo 1943435 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B3690137 : Blo 1943435 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B9840365 : Blo 1943435 9840365 := bstep (se 3 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 9840365 = 3690137) B3690137
theorem B6560243 : Blo 1943435 6560243 := bstep (se 1 (by rfl) ⟨4920182, by rfl⟩ : syracuseStep 6560243 = 9840365) B9840365
theorem B4373495 : Blo 1943435 4373495 := bstep (se 1 (by rfl) ⟨3280121, by rfl⟩ : syracuseStep 4373495 = 6560243) B6560243
theorem B2915663 : Blo 1943435 2915663 := bstep (se 1 (by rfl) ⟨2186747, by rfl⟩ : syracuseStep 2915663 = 4373495) B4373495
theorem B1943775 : Blo 1943435 1943775 := bstep (se 1 (by rfl) ⟨1457831, by rfl⟩ : syracuseStep 1943775 = 2915663) B2915663
theorem B2915669 : Blo 1943435 2915669 := bbase (se 11 (by rfl) ⟨2135, by rfl⟩ : syracuseStep 2915669 = 4271) (by norm_num)
theorem B1943779 : Blo 1943435 1943779 := bstep (se 1 (by rfl) ⟨1457834, by rfl⟩ : syracuseStep 1943779 = 2915669) B2915669
theorem B2216593 : Blo 1943435 2216593 := bbase (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) (by norm_num)
theorem B2955457 : Blo 1943435 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B15762437 : Blo 1943435 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B10508291 : Blo 1943435 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B7005527 : Blo 1943435 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B4670351 : Blo 1943435 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B3113567 : Blo 1943435 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B2075711 : Blo 1943435 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B5535229 : Blo 1943435 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B7380305 : Blo 1943435 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B4920203 : Blo 1943435 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B3280135 : Blo 1943435 3280135 := bstep (se 1 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 3280135 = 4920203) B4920203
theorem B4373513 : Blo 1943435 4373513 := bstep (se 2 (by rfl) ⟨1640067, by rfl⟩ : syracuseStep 4373513 = 3280135) B3280135
theorem B2915675 : Blo 1943435 2915675 := bstep (se 1 (by rfl) ⟨2186756, by rfl⟩ : syracuseStep 2915675 = 4373513) B4373513
theorem B1943783 : Blo 1943435 1943783 := bstep (se 1 (by rfl) ⟨1457837, by rfl⟩ : syracuseStep 1943783 = 2915675) B2915675
theorem B2186761 : Blo 1943435 2186761 := bbase (se 2 (by rfl) ⟨820035, by rfl⟩ : syracuseStep 2186761 = 1640071) (by norm_num)
theorem B2915681 : Blo 1943435 2915681 := bstep (se 2 (by rfl) ⟨1093380, by rfl⟩ : syracuseStep 2915681 = 2186761) B2186761
theorem B1943787 : Blo 1943435 1943787 := bstep (se 1 (by rfl) ⟨1457840, by rfl⟩ : syracuseStep 1943787 = 2915681) B2915681
theorem B5254165 : Blo 1943435 5254165 := bbase (se 6 (by rfl) ⟨123144, by rfl⟩ : syracuseStep 5254165 = 246289) (by norm_num)
theorem B28022213 : Blo 1943435 28022213 := bstep (se 4 (by rfl) ⟨2627082, by rfl⟩ : syracuseStep 28022213 = 5254165) B5254165
theorem B18681475 : Blo 1943435 18681475 := bstep (se 1 (by rfl) ⟨14011106, by rfl⟩ : syracuseStep 18681475 = 28022213) B28022213
theorem B24908633 : Blo 1943435 24908633 := bstep (se 2 (by rfl) ⟨9340737, by rfl⟩ : syracuseStep 24908633 = 18681475) B18681475
theorem B16605755 : Blo 1943435 16605755 := bstep (se 1 (by rfl) ⟨12454316, by rfl⟩ : syracuseStep 16605755 = 24908633) B24908633
theorem B11070503 : Blo 1943435 11070503 := bstep (se 1 (by rfl) ⟨8302877, by rfl⟩ : syracuseStep 11070503 = 16605755) B16605755
theorem B7380335 : Blo 1943435 7380335 := bstep (se 1 (by rfl) ⟨5535251, by rfl⟩ : syracuseStep 7380335 = 11070503) B11070503
theorem B4920223 : Blo 1943435 4920223 := bstep (se 1 (by rfl) ⟨3690167, by rfl⟩ : syracuseStep 4920223 = 7380335) B7380335
theorem B6560297 : Blo 1943435 6560297 := bstep (se 2 (by rfl) ⟨2460111, by rfl⟩ : syracuseStep 6560297 = 4920223) B4920223
theorem B4373531 : Blo 1943435 4373531 := bstep (se 1 (by rfl) ⟨3280148, by rfl⟩ : syracuseStep 4373531 = 6560297) B6560297
theorem B2915687 : Blo 1943435 2915687 := bstep (se 1 (by rfl) ⟨2186765, by rfl⟩ : syracuseStep 2915687 = 4373531) B4373531
theorem B1943791 : Blo 1943435 1943791 := bstep (se 1 (by rfl) ⟨1457843, by rfl⟩ : syracuseStep 1943791 = 2915687) B2915687
theorem B2915693 : Blo 1943435 2915693 := bbase (se 3 (by rfl) ⟨546692, by rfl⟩ : syracuseStep 2915693 = 1093385) (by norm_num)
theorem B1943795 : Blo 1943435 1943795 := bstep (se 1 (by rfl) ⟨1457846, by rfl⟩ : syracuseStep 1943795 = 2915693) B2915693
theorem B4373549 : Blo 1943435 4373549 := bbase (se 3 (by rfl) ⟨820040, by rfl⟩ : syracuseStep 4373549 = 1640081) (by norm_num)
theorem B2915699 : Blo 1943435 2915699 := bstep (se 1 (by rfl) ⟨2186774, by rfl⟩ : syracuseStep 2915699 = 4373549) B4373549
theorem B1943799 : Blo 1943435 1943799 := bstep (se 1 (by rfl) ⟨1457849, by rfl⟩ : syracuseStep 1943799 = 2915699) B2915699
theorem B2736101 : Blo 1943435 2736101 := bbase (se 4 (by rfl) ⟨256509, by rfl⟩ : syracuseStep 2736101 = 513019) (by norm_num)
theorem B7296269 : Blo 1943435 7296269 := bstep (se 3 (by rfl) ⟨1368050, by rfl⟩ : syracuseStep 7296269 = 2736101) B2736101
theorem B19456717 : Blo 1943435 19456717 := bstep (se 3 (by rfl) ⟨3648134, by rfl⟩ : syracuseStep 19456717 = 7296269) B7296269
theorem B25942289 : Blo 1943435 25942289 := bstep (se 2 (by rfl) ⟨9728358, by rfl⟩ : syracuseStep 25942289 = 19456717) B19456717
theorem B69179437 : Blo 1943435 69179437 := bstep (se 3 (by rfl) ⟨12971144, by rfl⟩ : syracuseStep 69179437 = 25942289) B25942289
theorem B92239249 : Blo 1943435 92239249 := bstep (se 2 (by rfl) ⟨34589718, by rfl⟩ : syracuseStep 92239249 = 69179437) B69179437
theorem B122985665 : Blo 1943435 122985665 := bstep (se 2 (by rfl) ⟨46119624, by rfl⟩ : syracuseStep 122985665 = 92239249) B92239249
theorem B81990443 : Blo 1943435 81990443 := bstep (se 1 (by rfl) ⟨61492832, by rfl⟩ : syracuseStep 81990443 = 122985665) B122985665
theorem B54660295 : Blo 1943435 54660295 := bstep (se 1 (by rfl) ⟨40995221, by rfl⟩ : syracuseStep 54660295 = 81990443) B81990443
theorem B72880393 : Blo 1943435 72880393 := bstep (se 2 (by rfl) ⟨27330147, by rfl⟩ : syracuseStep 72880393 = 54660295) B54660295
theorem B97173857 : Blo 1943435 97173857 := bstep (se 2 (by rfl) ⟨36440196, by rfl⟩ : syracuseStep 97173857 = 72880393) B72880393
theorem B259130285 : Blo 1943435 259130285 := bstep (se 3 (by rfl) ⟨48586928, by rfl⟩ : syracuseStep 259130285 = 97173857) B97173857
theorem B172753523 : Blo 1943435 172753523 := bstep (se 1 (by rfl) ⟨129565142, by rfl⟩ : syracuseStep 172753523 = 259130285) B259130285
theorem B115169015 : Blo 1943435 115169015 := bstep (se 1 (by rfl) ⟨86376761, by rfl⟩ : syracuseStep 115169015 = 172753523) B172753523
theorem B76779343 : Blo 1943435 76779343 := bstep (se 1 (by rfl) ⟨57584507, by rfl⟩ : syracuseStep 76779343 = 115169015) B115169015
theorem B102372457 : Blo 1943435 102372457 := bstep (se 2 (by rfl) ⟨38389671, by rfl⟩ : syracuseStep 102372457 = 76779343) B76779343
theorem B136496609 : Blo 1943435 136496609 := bstep (se 2 (by rfl) ⟨51186228, by rfl⟩ : syracuseStep 136496609 = 102372457) B102372457
theorem B90997739 : Blo 1943435 90997739 := bstep (se 1 (by rfl) ⟨68248304, by rfl⟩ : syracuseStep 90997739 = 136496609) B136496609
theorem B60665159 : Blo 1943435 60665159 := bstep (se 1 (by rfl) ⟨45498869, by rfl⟩ : syracuseStep 60665159 = 90997739) B90997739
theorem B161773757 : Blo 1943435 161773757 := bstep (se 3 (by rfl) ⟨30332579, by rfl⟩ : syracuseStep 161773757 = 60665159) B60665159
theorem B107849171 : Blo 1943435 107849171 := bstep (se 1 (by rfl) ⟨80886878, by rfl⟩ : syracuseStep 107849171 = 161773757) B161773757
theorem B71899447 : Blo 1943435 71899447 := bstep (se 1 (by rfl) ⟨53924585, by rfl⟩ : syracuseStep 71899447 = 107849171) B107849171
theorem B95865929 : Blo 1943435 95865929 := bstep (se 2 (by rfl) ⟨35949723, by rfl⟩ : syracuseStep 95865929 = 71899447) B71899447
theorem B63910619 : Blo 1943435 63910619 := bstep (se 1 (by rfl) ⟨47932964, by rfl⟩ : syracuseStep 63910619 = 95865929) B95865929
theorem B42607079 : Blo 1943435 42607079 := bstep (se 1 (by rfl) ⟨31955309, by rfl⟩ : syracuseStep 42607079 = 63910619) B63910619
theorem B28404719 : Blo 1943435 28404719 := bstep (se 1 (by rfl) ⟨21303539, by rfl⟩ : syracuseStep 28404719 = 42607079) B42607079
theorem B18936479 : Blo 1943435 18936479 := bstep (se 1 (by rfl) ⟨14202359, by rfl⟩ : syracuseStep 18936479 = 28404719) B28404719
theorem B12624319 : Blo 1943435 12624319 := bstep (se 1 (by rfl) ⟨9468239, by rfl⟩ : syracuseStep 12624319 = 18936479) B18936479
theorem B67329701 : Blo 1943435 67329701 := bstep (se 4 (by rfl) ⟨6312159, by rfl⟩ : syracuseStep 67329701 = 12624319) B12624319
theorem B44886467 : Blo 1943435 44886467 := bstep (se 1 (by rfl) ⟨33664850, by rfl⟩ : syracuseStep 44886467 = 67329701) B67329701
theorem B29924311 : Blo 1943435 29924311 := bstep (se 1 (by rfl) ⟨22443233, by rfl⟩ : syracuseStep 29924311 = 44886467) B44886467
theorem B39899081 : Blo 1943435 39899081 := bstep (se 2 (by rfl) ⟨14962155, by rfl⟩ : syracuseStep 39899081 = 29924311) B29924311
theorem B26599387 : Blo 1943435 26599387 := bstep (se 1 (by rfl) ⟨19949540, by rfl⟩ : syracuseStep 26599387 = 39899081) B39899081
theorem B35465849 : Blo 1943435 35465849 := bstep (se 2 (by rfl) ⟨13299693, by rfl⟩ : syracuseStep 35465849 = 26599387) B26599387
theorem B23643899 : Blo 1943435 23643899 := bstep (se 1 (by rfl) ⟨17732924, by rfl⟩ : syracuseStep 23643899 = 35465849) B35465849
theorem B15762599 : Blo 1943435 15762599 := bstep (se 1 (by rfl) ⟨11821949, by rfl⟩ : syracuseStep 15762599 = 23643899) B23643899
theorem B10508399 : Blo 1943435 10508399 := bstep (se 1 (by rfl) ⟨7881299, by rfl⟩ : syracuseStep 10508399 = 15762599) B15762599
theorem B7005599 : Blo 1943435 7005599 := bstep (se 1 (by rfl) ⟨5254199, by rfl⟩ : syracuseStep 7005599 = 10508399) B10508399
theorem B4670399 : Blo 1943435 4670399 := bstep (se 1 (by rfl) ⟨3502799, by rfl⟩ : syracuseStep 4670399 = 7005599) B7005599
theorem B12454397 : Blo 1943435 12454397 := bstep (se 3 (by rfl) ⟨2335199, by rfl⟩ : syracuseStep 12454397 = 4670399) B4670399
theorem B8302931 : Blo 1943435 8302931 := bstep (se 1 (by rfl) ⟨6227198, by rfl⟩ : syracuseStep 8302931 = 12454397) B12454397
theorem B5535287 : Blo 1943435 5535287 := bstep (se 1 (by rfl) ⟨4151465, by rfl⟩ : syracuseStep 5535287 = 8302931) B8302931
theorem B3690191 : Blo 1943435 3690191 := bstep (se 1 (by rfl) ⟨2767643, by rfl⟩ : syracuseStep 3690191 = 5535287) B5535287
theorem B2460127 : Blo 1943435 2460127 := bstep (se 1 (by rfl) ⟨1845095, by rfl⟩ : syracuseStep 2460127 = 3690191) B3690191
theorem B3280169 : Blo 1943435 3280169 := bstep (se 2 (by rfl) ⟨1230063, by rfl⟩ : syracuseStep 3280169 = 2460127) B2460127
theorem B2186779 : Blo 1943435 2186779 := bstep (se 1 (by rfl) ⟨1640084, by rfl⟩ : syracuseStep 2186779 = 3280169) B3280169
theorem B2915705 : Blo 1943435 2915705 := bstep (se 2 (by rfl) ⟨1093389, by rfl⟩ : syracuseStep 2915705 = 2186779) B2186779
theorem B1943803 : Blo 1943435 1943803 := bstep (se 1 (by rfl) ⟨1457852, by rfl⟩ : syracuseStep 1943803 = 2915705) B2915705
theorem B9974789 : Blo 1943435 9974789 := bbase (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) (by norm_num)
theorem B6649859 : Blo 1943435 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B4433239 : Blo 1943435 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B5910985 : Blo 1943435 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B7881313 : Blo 1943435 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B10508417 : Blo 1943435 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B7005611 : Blo 1943435 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B4670407 : Blo 1943435 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B6227209 : Blo 1943435 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B33211781 : Blo 1943435 33211781 := bstep (se 4 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 33211781 = 6227209) B6227209
theorem B22141187 : Blo 1943435 22141187 := bstep (se 1 (by rfl) ⟨16605890, by rfl⟩ : syracuseStep 22141187 = 33211781) B33211781
theorem B14760791 : Blo 1943435 14760791 := bstep (se 1 (by rfl) ⟨11070593, by rfl⟩ : syracuseStep 14760791 = 22141187) B22141187
theorem B9840527 : Blo 1943435 9840527 := bstep (se 1 (by rfl) ⟨7380395, by rfl⟩ : syracuseStep 9840527 = 14760791) B14760791
theorem B6560351 : Blo 1943435 6560351 := bstep (se 1 (by rfl) ⟨4920263, by rfl⟩ : syracuseStep 6560351 = 9840527) B9840527
theorem B4373567 : Blo 1943435 4373567 := bstep (se 1 (by rfl) ⟨3280175, by rfl⟩ : syracuseStep 4373567 = 6560351) B6560351
theorem B2915711 : Blo 1943435 2915711 := bstep (se 1 (by rfl) ⟨2186783, by rfl⟩ : syracuseStep 2915711 = 4373567) B4373567
theorem B1943807 : Blo 1943435 1943807 := bstep (se 1 (by rfl) ⟨1457855, by rfl⟩ : syracuseStep 1943807 = 2915711) B2915711
theorem B2915717 : Blo 1943435 2915717 := bbase (se 4 (by rfl) ⟨273348, by rfl⟩ : syracuseStep 2915717 = 546697) (by norm_num)
theorem B1943811 : Blo 1943435 1943811 := bstep (se 1 (by rfl) ⟨1457858, by rfl⟩ : syracuseStep 1943811 = 2915717) B2915717
theorem B3280189 : Blo 1943435 3280189 := bbase (se 3 (by rfl) ⟨615035, by rfl⟩ : syracuseStep 3280189 = 1230071) (by norm_num)
theorem B4373585 : Blo 1943435 4373585 := bstep (se 2 (by rfl) ⟨1640094, by rfl⟩ : syracuseStep 4373585 = 3280189) B3280189
theorem B2915723 : Blo 1943435 2915723 := bstep (se 1 (by rfl) ⟨2186792, by rfl⟩ : syracuseStep 2915723 = 4373585) B4373585
theorem B1943815 : Blo 1943435 1943815 := bstep (se 1 (by rfl) ⟨1457861, by rfl⟩ : syracuseStep 1943815 = 2915723) B2915723
theorem B2186797 : Blo 1943435 2186797 := bbase (se 3 (by rfl) ⟨410024, by rfl⟩ : syracuseStep 2186797 = 820049) (by norm_num)
theorem B2915729 : Blo 1943435 2915729 := bstep (se 2 (by rfl) ⟨1093398, by rfl⟩ : syracuseStep 2915729 = 2186797) B2186797
theorem B1943819 : Blo 1943435 1943819 := bstep (se 1 (by rfl) ⟨1457864, by rfl⟩ : syracuseStep 1943819 = 2915729) B2915729
theorem B6560405 : Blo 1943435 6560405 := bbase (se 6 (by rfl) ⟨153759, by rfl⟩ : syracuseStep 6560405 = 307519) (by norm_num)
theorem B4373603 : Blo 1943435 4373603 := bstep (se 1 (by rfl) ⟨3280202, by rfl⟩ : syracuseStep 4373603 = 6560405) B6560405
theorem B2915735 : Blo 1943435 2915735 := bstep (se 1 (by rfl) ⟨2186801, by rfl⟩ : syracuseStep 2915735 = 4373603) B4373603
theorem B1943823 : Blo 1943435 1943823 := bstep (se 1 (by rfl) ⟨1457867, by rfl⟩ : syracuseStep 1943823 = 2915735) B2915735
theorem B2915741 : Blo 1943435 2915741 := bbase (se 3 (by rfl) ⟨546701, by rfl⟩ : syracuseStep 2915741 = 1093403) (by norm_num)
theorem B1943827 : Blo 1943435 1943827 := bstep (se 1 (by rfl) ⟨1457870, by rfl⟩ : syracuseStep 1943827 = 2915741) B2915741
theorem B4373621 : Blo 1943435 4373621 := bbase (se 5 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 4373621 = 410027) (by norm_num)
theorem B2915747 : Blo 1943435 2915747 := bstep (se 1 (by rfl) ⟨2186810, by rfl⟩ : syracuseStep 2915747 = 4373621) B4373621
theorem B1943831 : Blo 1943435 1943831 := bstep (se 1 (by rfl) ⟨1457873, by rfl⟩ : syracuseStep 1943831 = 2915747) B2915747
theorem B16606133 : Blo 1943435 16606133 := bbase (se 5 (by rfl) ⟨778412, by rfl⟩ : syracuseStep 16606133 = 1556825) (by norm_num)
theorem B11070755 : Blo 1943435 11070755 := bstep (se 1 (by rfl) ⟨8303066, by rfl⟩ : syracuseStep 11070755 = 16606133) B16606133
theorem B7380503 : Blo 1943435 7380503 := bstep (se 1 (by rfl) ⟨5535377, by rfl⟩ : syracuseStep 7380503 = 11070755) B11070755
theorem B4920335 : Blo 1943435 4920335 := bstep (se 1 (by rfl) ⟨3690251, by rfl⟩ : syracuseStep 4920335 = 7380503) B7380503
theorem B3280223 : Blo 1943435 3280223 := bstep (se 1 (by rfl) ⟨2460167, by rfl⟩ : syracuseStep 3280223 = 4920335) B4920335
theorem B2186815 : Blo 1943435 2186815 := bstep (se 1 (by rfl) ⟨1640111, by rfl⟩ : syracuseStep 2186815 = 3280223) B3280223
theorem B2915753 : Blo 1943435 2915753 := bstep (se 2 (by rfl) ⟨1093407, by rfl⟩ : syracuseStep 2915753 = 2186815) B2186815
theorem B1943835 : Blo 1943435 1943835 := bstep (se 1 (by rfl) ⟨1457876, by rfl⟩ : syracuseStep 1943835 = 2915753) B2915753
theorem B7380517 : Blo 1943435 7380517 := bbase (se 4 (by rfl) ⟨691923, by rfl⟩ : syracuseStep 7380517 = 1383847) (by norm_num)
theorem B9840689 : Blo 1943435 9840689 := bstep (se 2 (by rfl) ⟨3690258, by rfl⟩ : syracuseStep 9840689 = 7380517) B7380517
theorem B6560459 : Blo 1943435 6560459 := bstep (se 1 (by rfl) ⟨4920344, by rfl⟩ : syracuseStep 6560459 = 9840689) B9840689
theorem B4373639 : Blo 1943435 4373639 := bstep (se 1 (by rfl) ⟨3280229, by rfl⟩ : syracuseStep 4373639 = 6560459) B6560459
theorem B2915759 : Blo 1943435 2915759 := bstep (se 1 (by rfl) ⟨2186819, by rfl⟩ : syracuseStep 2915759 = 4373639) B4373639
theorem B1943839 : Blo 1943435 1943839 := bstep (se 1 (by rfl) ⟨1457879, by rfl⟩ : syracuseStep 1943839 = 2915759) B2915759
theorem B2915765 : Blo 1943435 2915765 := bbase (se 5 (by rfl) ⟨136676, by rfl⟩ : syracuseStep 2915765 = 273353) (by norm_num)
theorem B1943843 : Blo 1943435 1943843 := bstep (se 1 (by rfl) ⟨1457882, by rfl⟩ : syracuseStep 1943843 = 2915765) B2915765
theorem B4920365 : Blo 1943435 4920365 := bbase (se 3 (by rfl) ⟨922568, by rfl⟩ : syracuseStep 4920365 = 1845137) (by norm_num)
theorem B3280243 : Blo 1943435 3280243 := bstep (se 1 (by rfl) ⟨2460182, by rfl⟩ : syracuseStep 3280243 = 4920365) B4920365
theorem B4373657 : Blo 1943435 4373657 := bstep (se 2 (by rfl) ⟨1640121, by rfl⟩ : syracuseStep 4373657 = 3280243) B3280243
theorem B2915771 : Blo 1943435 2915771 := bstep (se 1 (by rfl) ⟨2186828, by rfl⟩ : syracuseStep 2915771 = 4373657) B4373657
theorem B1943847 : Blo 1943435 1943847 := bstep (se 1 (by rfl) ⟨1457885, by rfl⟩ : syracuseStep 1943847 = 2915771) B2915771
theorem B2186833 : Blo 1943435 2186833 := bbase (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) (by norm_num)
theorem B2915777 : Blo 1943435 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1943851 : Blo 1943435 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B2767717 : Blo 1943435 2767717 := bbase (se 4 (by rfl) ⟨259473, by rfl⟩ : syracuseStep 2767717 = 518947) (by norm_num)
theorem B3690289 : Blo 1943435 3690289 := bstep (se 2 (by rfl) ⟨1383858, by rfl⟩ : syracuseStep 3690289 = 2767717) B2767717
theorem B4920385 : Blo 1943435 4920385 := bstep (se 2 (by rfl) ⟨1845144, by rfl⟩ : syracuseStep 4920385 = 3690289) B3690289
theorem B6560513 : Blo 1943435 6560513 := bstep (se 2 (by rfl) ⟨2460192, by rfl⟩ : syracuseStep 6560513 = 4920385) B4920385
theorem B4373675 : Blo 1943435 4373675 := bstep (se 1 (by rfl) ⟨3280256, by rfl⟩ : syracuseStep 4373675 = 6560513) B6560513
theorem B2915783 : Blo 1943435 2915783 := bstep (se 1 (by rfl) ⟨2186837, by rfl⟩ : syracuseStep 2915783 = 4373675) B4373675
theorem B1943855 : Blo 1943435 1943855 := bstep (se 1 (by rfl) ⟨1457891, by rfl⟩ : syracuseStep 1943855 = 2915783) B2915783
theorem B2915789 : Blo 1943435 2915789 := bbase (se 3 (by rfl) ⟨546710, by rfl⟩ : syracuseStep 2915789 = 1093421) (by norm_num)
theorem B1943859 : Blo 1943435 1943859 := bstep (se 1 (by rfl) ⟨1457894, by rfl⟩ : syracuseStep 1943859 = 2915789) B2915789
theorem B4373693 : Blo 1943435 4373693 := bbase (se 3 (by rfl) ⟨820067, by rfl⟩ : syracuseStep 4373693 = 1640135) (by norm_num)
theorem B2915795 : Blo 1943435 2915795 := bstep (se 1 (by rfl) ⟨2186846, by rfl⟩ : syracuseStep 2915795 = 4373693) B4373693
theorem B1943863 : Blo 1943435 1943863 := bstep (se 1 (by rfl) ⟨1457897, by rfl⟩ : syracuseStep 1943863 = 2915795) B2915795
theorem B3280277 : Blo 1943435 3280277 := bbase (se 6 (by rfl) ⟨76881, by rfl⟩ : syracuseStep 3280277 = 153763) (by norm_num)
theorem B2186851 : Blo 1943435 2186851 := bstep (se 1 (by rfl) ⟨1640138, by rfl⟩ : syracuseStep 2186851 = 3280277) B3280277
theorem B2915801 : Blo 1943435 2915801 := bstep (se 2 (by rfl) ⟨1093425, by rfl⟩ : syracuseStep 2915801 = 2186851) B2186851
theorem B1943867 : Blo 1943435 1943867 := bstep (se 1 (by rfl) ⟨1457900, by rfl⟩ : syracuseStep 1943867 = 2915801) B2915801
theorem B2216693 : Blo 1943435 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B5911181 : Blo 1943435 5911181 := bstep (se 3 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 5911181 = 2216693) B2216693
theorem B3940787 : Blo 1943435 3940787 := bstep (se 1 (by rfl) ⟨2955590, by rfl⟩ : syracuseStep 3940787 = 5911181) B5911181
theorem B2627191 : Blo 1943435 2627191 := bstep (se 1 (by rfl) ⟨1970393, by rfl⟩ : syracuseStep 2627191 = 3940787) B3940787
theorem B3502921 : Blo 1943435 3502921 := bstep (se 2 (by rfl) ⟨1313595, by rfl⟩ : syracuseStep 3502921 = 2627191) B2627191
theorem B4670561 : Blo 1943435 4670561 := bstep (se 2 (by rfl) ⟨1751460, by rfl⟩ : syracuseStep 4670561 = 3502921) B3502921
theorem B12454829 : Blo 1943435 12454829 := bstep (se 3 (by rfl) ⟨2335280, by rfl⟩ : syracuseStep 12454829 = 4670561) B4670561
theorem B8303219 : Blo 1943435 8303219 := bstep (se 1 (by rfl) ⟨6227414, by rfl⟩ : syracuseStep 8303219 = 12454829) B12454829
theorem B5535479 : Blo 1943435 5535479 := bstep (se 1 (by rfl) ⟨4151609, by rfl⟩ : syracuseStep 5535479 = 8303219) B8303219
theorem B14761277 : Blo 1943435 14761277 := bstep (se 3 (by rfl) ⟨2767739, by rfl⟩ : syracuseStep 14761277 = 5535479) B5535479
theorem B9840851 : Blo 1943435 9840851 := bstep (se 1 (by rfl) ⟨7380638, by rfl⟩ : syracuseStep 9840851 = 14761277) B14761277
theorem B6560567 : Blo 1943435 6560567 := bstep (se 1 (by rfl) ⟨4920425, by rfl⟩ : syracuseStep 6560567 = 9840851) B9840851
theorem B4373711 : Blo 1943435 4373711 := bstep (se 1 (by rfl) ⟨3280283, by rfl⟩ : syracuseStep 4373711 = 6560567) B6560567
theorem B2915807 : Blo 1943435 2915807 := bstep (se 1 (by rfl) ⟨2186855, by rfl⟩ : syracuseStep 2915807 = 4373711) B4373711
theorem B1943871 : Blo 1943435 1943871 := bstep (se 1 (by rfl) ⟨1457903, by rfl⟩ : syracuseStep 1943871 = 2915807) B2915807
theorem B2915813 : Blo 1943435 2915813 := bbase (se 4 (by rfl) ⟨273357, by rfl⟩ : syracuseStep 2915813 = 546715) (by norm_num)
theorem B1943875 : Blo 1943435 1943875 := bstep (se 1 (by rfl) ⟨1457906, by rfl⟩ : syracuseStep 1943875 = 2915813) B2915813
theorem B18682325 : Blo 1943435 18682325 := bbase (se 7 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 18682325 = 437867) (by norm_num)
theorem B12454883 : Blo 1943435 12454883 := bstep (se 1 (by rfl) ⟨9341162, by rfl⟩ : syracuseStep 12454883 = 18682325) B18682325
theorem B8303255 : Blo 1943435 8303255 := bstep (se 1 (by rfl) ⟨6227441, by rfl⟩ : syracuseStep 8303255 = 12454883) B12454883
theorem B5535503 : Blo 1943435 5535503 := bstep (se 1 (by rfl) ⟨4151627, by rfl⟩ : syracuseStep 5535503 = 8303255) B8303255
theorem B3690335 : Blo 1943435 3690335 := bstep (se 1 (by rfl) ⟨2767751, by rfl⟩ : syracuseStep 3690335 = 5535503) B5535503
theorem B2460223 : Blo 1943435 2460223 := bstep (se 1 (by rfl) ⟨1845167, by rfl⟩ : syracuseStep 2460223 = 3690335) B3690335
theorem B3280297 : Blo 1943435 3280297 := bstep (se 2 (by rfl) ⟨1230111, by rfl⟩ : syracuseStep 3280297 = 2460223) B2460223
theorem B4373729 : Blo 1943435 4373729 := bstep (se 2 (by rfl) ⟨1640148, by rfl⟩ : syracuseStep 4373729 = 3280297) B3280297
theorem B2915819 : Blo 1943435 2915819 := bstep (se 1 (by rfl) ⟨2186864, by rfl⟩ : syracuseStep 2915819 = 4373729) B4373729
theorem B1943879 : Blo 1943435 1943879 := bstep (se 1 (by rfl) ⟨1457909, by rfl⟩ : syracuseStep 1943879 = 2915819) B2915819
theorem B2186869 : Blo 1943435 2186869 := bbase (se 5 (by rfl) ⟨102509, by rfl⟩ : syracuseStep 2186869 = 205019) (by norm_num)
theorem B2915825 : Blo 1943435 2915825 := bstep (se 2 (by rfl) ⟨1093434, by rfl⟩ : syracuseStep 2915825 = 2186869) B2186869
theorem B1943883 : Blo 1943435 1943883 := bstep (se 1 (by rfl) ⟨1457912, by rfl⟩ : syracuseStep 1943883 = 2915825) B2915825
theorem B2460233 : Blo 1943435 2460233 := bbase (se 2 (by rfl) ⟨922587, by rfl⟩ : syracuseStep 2460233 = 1845175) (by norm_num)
theorem B6560621 : Blo 1943435 6560621 := bstep (se 3 (by rfl) ⟨1230116, by rfl⟩ : syracuseStep 6560621 = 2460233) B2460233
theorem B4373747 : Blo 1943435 4373747 := bstep (se 1 (by rfl) ⟨3280310, by rfl⟩ : syracuseStep 4373747 = 6560621) B6560621
theorem B2915831 : Blo 1943435 2915831 := bstep (se 1 (by rfl) ⟨2186873, by rfl⟩ : syracuseStep 2915831 = 4373747) B4373747
theorem B1943887 : Blo 1943435 1943887 := bstep (se 1 (by rfl) ⟨1457915, by rfl⟩ : syracuseStep 1943887 = 2915831) B2915831
theorem B2915837 : Blo 1943435 2915837 := bbase (se 3 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 2915837 = 1093439) (by norm_num)
theorem B1943891 : Blo 1943435 1943891 := bstep (se 1 (by rfl) ⟨1457918, by rfl⟩ : syracuseStep 1943891 = 2915837) B2915837
theorem B4373765 : Blo 1943435 4373765 := bbase (se 4 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 4373765 = 820081) (by norm_num)
theorem B2915843 : Blo 1943435 2915843 := bstep (se 1 (by rfl) ⟨2186882, by rfl⟩ : syracuseStep 2915843 = 4373765) B4373765
theorem B1943895 : Blo 1943435 1943895 := bstep (se 1 (by rfl) ⟨1457921, by rfl⟩ : syracuseStep 1943895 = 2915843) B2915843
theorem B3690373 : Blo 1943435 3690373 := bbase (se 4 (by rfl) ⟨345972, by rfl⟩ : syracuseStep 3690373 = 691945) (by norm_num)
theorem B4920497 : Blo 1943435 4920497 := bstep (se 2 (by rfl) ⟨1845186, by rfl⟩ : syracuseStep 4920497 = 3690373) B3690373
theorem B3280331 : Blo 1943435 3280331 := bstep (se 1 (by rfl) ⟨2460248, by rfl⟩ : syracuseStep 3280331 = 4920497) B4920497
theorem B2186887 : Blo 1943435 2186887 := bstep (se 1 (by rfl) ⟨1640165, by rfl⟩ : syracuseStep 2186887 = 3280331) B3280331
theorem B2915849 : Blo 1943435 2915849 := bstep (se 2 (by rfl) ⟨1093443, by rfl⟩ : syracuseStep 2915849 = 2186887) B2186887
theorem B1943899 : Blo 1943435 1943899 := bstep (se 1 (by rfl) ⟨1457924, by rfl⟩ : syracuseStep 1943899 = 2915849) B2915849
theorem B9841013 : Blo 1943435 9841013 := bbase (se 5 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 9841013 = 922595) (by norm_num)
theorem B6560675 : Blo 1943435 6560675 := bstep (se 1 (by rfl) ⟨4920506, by rfl⟩ : syracuseStep 6560675 = 9841013) B9841013
theorem B4373783 : Blo 1943435 4373783 := bstep (se 1 (by rfl) ⟨3280337, by rfl⟩ : syracuseStep 4373783 = 6560675) B6560675
theorem B2915855 : Blo 1943435 2915855 := bstep (se 1 (by rfl) ⟨2186891, by rfl⟩ : syracuseStep 2915855 = 4373783) B4373783
theorem B1943903 : Blo 1943435 1943903 := bstep (se 1 (by rfl) ⟨1457927, by rfl⟩ : syracuseStep 1943903 = 2915855) B2915855
theorem B2915861 : Blo 1943435 2915861 := bbase (se 6 (by rfl) ⟨68340, by rfl⟩ : syracuseStep 2915861 = 136681) (by norm_num)
theorem B1943907 : Blo 1943435 1943907 := bstep (se 1 (by rfl) ⟨1457930, by rfl⟩ : syracuseStep 1943907 = 2915861) B2915861
theorem B2627245 : Blo 1943435 2627245 := bbase (se 3 (by rfl) ⟨492608, by rfl⟩ : syracuseStep 2627245 = 985217) (by norm_num)
theorem B14011973 : Blo 1943435 14011973 := bstep (se 4 (by rfl) ⟨1313622, by rfl⟩ : syracuseStep 14011973 = 2627245) B2627245
theorem B9341315 : Blo 1943435 9341315 := bstep (se 1 (by rfl) ⟨7005986, by rfl⟩ : syracuseStep 9341315 = 14011973) B14011973
theorem B6227543 : Blo 1943435 6227543 := bstep (se 1 (by rfl) ⟨4670657, by rfl⟩ : syracuseStep 6227543 = 9341315) B9341315
theorem B16606781 : Blo 1943435 16606781 := bstep (se 3 (by rfl) ⟨3113771, by rfl⟩ : syracuseStep 16606781 = 6227543) B6227543
theorem B11071187 : Blo 1943435 11071187 := bstep (se 1 (by rfl) ⟨8303390, by rfl⟩ : syracuseStep 11071187 = 16606781) B16606781
theorem B7380791 : Blo 1943435 7380791 := bstep (se 1 (by rfl) ⟨5535593, by rfl⟩ : syracuseStep 7380791 = 11071187) B11071187
theorem B4920527 : Blo 1943435 4920527 := bstep (se 1 (by rfl) ⟨3690395, by rfl⟩ : syracuseStep 4920527 = 7380791) B7380791
theorem B3280351 : Blo 1943435 3280351 := bstep (se 1 (by rfl) ⟨2460263, by rfl⟩ : syracuseStep 3280351 = 4920527) B4920527
theorem B4373801 : Blo 1943435 4373801 := bstep (se 2 (by rfl) ⟨1640175, by rfl⟩ : syracuseStep 4373801 = 3280351) B3280351
theorem B2915867 : Blo 1943435 2915867 := bstep (se 1 (by rfl) ⟨2186900, by rfl⟩ : syracuseStep 2915867 = 4373801) B4373801
theorem B1943911 : Blo 1943435 1943911 := bstep (se 1 (by rfl) ⟨1457933, by rfl⟩ : syracuseStep 1943911 = 2915867) B2915867
theorem B2186905 : Blo 1943435 2186905 := bbase (se 2 (by rfl) ⟨820089, by rfl⟩ : syracuseStep 2186905 = 1640179) (by norm_num)
theorem B2915873 : Blo 1943435 2915873 := bstep (se 2 (by rfl) ⟨1093452, by rfl⟩ : syracuseStep 2915873 = 2186905) B2186905
theorem B1943915 : Blo 1943435 1943915 := bstep (se 1 (by rfl) ⟨1457936, by rfl⟩ : syracuseStep 1943915 = 2915873) B2915873
theorem B7380821 : Blo 1943435 7380821 := bbase (se 9 (by rfl) ⟨21623, by rfl⟩ : syracuseStep 7380821 = 43247) (by norm_num)
theorem B4920547 : Blo 1943435 4920547 := bstep (se 1 (by rfl) ⟨3690410, by rfl⟩ : syracuseStep 4920547 = 7380821) B7380821
theorem B6560729 : Blo 1943435 6560729 := bstep (se 2 (by rfl) ⟨2460273, by rfl⟩ : syracuseStep 6560729 = 4920547) B4920547
theorem B4373819 : Blo 1943435 4373819 := bstep (se 1 (by rfl) ⟨3280364, by rfl⟩ : syracuseStep 4373819 = 6560729) B6560729
theorem B2915879 : Blo 1943435 2915879 := bstep (se 1 (by rfl) ⟨2186909, by rfl⟩ : syracuseStep 2915879 = 4373819) B4373819
theorem B1943919 : Blo 1943435 1943919 := bstep (se 1 (by rfl) ⟨1457939, by rfl⟩ : syracuseStep 1943919 = 2915879) B2915879
theorem B2915885 : Blo 1943435 2915885 := bbase (se 3 (by rfl) ⟨546728, by rfl⟩ : syracuseStep 2915885 = 1093457) (by norm_num)
theorem B1943923 : Blo 1943435 1943923 := bstep (se 1 (by rfl) ⟨1457942, by rfl⟩ : syracuseStep 1943923 = 2915885) B2915885
theorem B4373837 : Blo 1943435 4373837 := bbase (se 3 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 4373837 = 1640189) (by norm_num)
theorem B2915891 : Blo 1943435 2915891 := bstep (se 1 (by rfl) ⟨2186918, by rfl⟩ : syracuseStep 2915891 = 4373837) B4373837
theorem B1943927 : Blo 1943435 1943927 := bstep (se 1 (by rfl) ⟨1457945, by rfl⟩ : syracuseStep 1943927 = 2915891) B2915891
theorem B2460289 : Blo 1943435 2460289 := bbase (se 2 (by rfl) ⟨922608, by rfl⟩ : syracuseStep 2460289 = 1845217) (by norm_num)
theorem B3280385 : Blo 1943435 3280385 := bstep (se 2 (by rfl) ⟨1230144, by rfl⟩ : syracuseStep 3280385 = 2460289) B2460289
theorem B2186923 : Blo 1943435 2186923 := bstep (se 1 (by rfl) ⟨1640192, by rfl⟩ : syracuseStep 2186923 = 3280385) B3280385
theorem B2915897 : Blo 1943435 2915897 := bstep (se 2 (by rfl) ⟨1093461, by rfl⟩ : syracuseStep 2915897 = 2186923) B2186923
theorem B1943931 : Blo 1943435 1943931 := bstep (se 1 (by rfl) ⟨1457948, by rfl⟩ : syracuseStep 1943931 = 2915897) B2915897
theorem B2075873 : Blo 1943435 2075873 := bbase (se 2 (by rfl) ⟨778452, by rfl⟩ : syracuseStep 2075873 = 1556905) (by norm_num)
theorem B22142645 : Blo 1943435 22142645 := bstep (se 5 (by rfl) ⟨1037936, by rfl⟩ : syracuseStep 22142645 = 2075873) B2075873
theorem B14761763 : Blo 1943435 14761763 := bstep (se 1 (by rfl) ⟨11071322, by rfl⟩ : syracuseStep 14761763 = 22142645) B22142645
theorem B9841175 : Blo 1943435 9841175 := bstep (se 1 (by rfl) ⟨7380881, by rfl⟩ : syracuseStep 9841175 = 14761763) B14761763
theorem B6560783 : Blo 1943435 6560783 := bstep (se 1 (by rfl) ⟨4920587, by rfl⟩ : syracuseStep 6560783 = 9841175) B9841175
theorem B4373855 : Blo 1943435 4373855 := bstep (se 1 (by rfl) ⟨3280391, by rfl⟩ : syracuseStep 4373855 = 6560783) B6560783
theorem B2915903 : Blo 1943435 2915903 := bstep (se 1 (by rfl) ⟨2186927, by rfl⟩ : syracuseStep 2915903 = 4373855) B4373855
theorem B1943935 : Blo 1943435 1943935 := bstep (se 1 (by rfl) ⟨1457951, by rfl⟩ : syracuseStep 1943935 = 2915903) B2915903
theorem B2915909 : Blo 1943435 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B1943939 : Blo 1943435 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B3280405 : Blo 1943435 3280405 := bbase (se 6 (by rfl) ⟨76884, by rfl⟩ : syracuseStep 3280405 = 153769) (by norm_num)
theorem B4373873 : Blo 1943435 4373873 := bstep (se 2 (by rfl) ⟨1640202, by rfl⟩ : syracuseStep 4373873 = 3280405) B3280405
theorem B2915915 : Blo 1943435 2915915 := bstep (se 1 (by rfl) ⟨2186936, by rfl⟩ : syracuseStep 2915915 = 4373873) B4373873
theorem B1943943 : Blo 1943435 1943943 := bstep (se 1 (by rfl) ⟨1457957, by rfl⟩ : syracuseStep 1943943 = 2915915) B2915915
theorem B2186941 : Blo 1943435 2186941 := bbase (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) (by norm_num)
theorem B2915921 : Blo 1943435 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B1943947 : Blo 1943435 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B6560837 : Blo 1943435 6560837 := bbase (se 4 (by rfl) ⟨615078, by rfl⟩ : syracuseStep 6560837 = 1230157) (by norm_num)
theorem B4373891 : Blo 1943435 4373891 := bstep (se 1 (by rfl) ⟨3280418, by rfl⟩ : syracuseStep 4373891 = 6560837) B6560837
theorem B2915927 : Blo 1943435 2915927 := bstep (se 1 (by rfl) ⟨2186945, by rfl⟩ : syracuseStep 2915927 = 4373891) B4373891
theorem B1943951 : Blo 1943435 1943951 := bstep (se 1 (by rfl) ⟨1457963, by rfl⟩ : syracuseStep 1943951 = 2915927) B2915927
theorem B2915933 : Blo 1943435 2915933 := bbase (se 3 (by rfl) ⟨546737, by rfl⟩ : syracuseStep 2915933 = 1093475) (by norm_num)
theorem B1943955 : Blo 1943435 1943955 := bstep (se 1 (by rfl) ⟨1457966, by rfl⟩ : syracuseStep 1943955 = 2915933) B2915933
theorem B4373909 : Blo 1943435 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B2915939 : Blo 1943435 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B1943959 : Blo 1943435 1943959 := bstep (se 1 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 1943959 = 2915939) B2915939
theorem B4734509 : Blo 1943435 4734509 := bbase (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) (by norm_num)
theorem B12625357 : Blo 1943435 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B16833809 : Blo 1943435 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B44890157 : Blo 1943435 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B119707085 : Blo 1943435 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B79804723 : Blo 1943435 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B106406297 : Blo 1943435 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B70937531 : Blo 1943435 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B47291687 : Blo 1943435 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B31527791 : Blo 1943435 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B21018527 : Blo 1943435 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B14012351 : Blo 1943435 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B9341567 : Blo 1943435 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B6227711 : Blo 1943435 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B4151807 : Blo 1943435 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B2767871 : Blo 1943435 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B7380989 : Blo 1943435 7380989 := bstep (se 3 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 7380989 = 2767871) B2767871
theorem B4920659 : Blo 1943435 4920659 := bstep (se 1 (by rfl) ⟨3690494, by rfl⟩ : syracuseStep 4920659 = 7380989) B7380989
theorem B3280439 : Blo 1943435 3280439 := bstep (se 1 (by rfl) ⟨2460329, by rfl⟩ : syracuseStep 3280439 = 4920659) B4920659
theorem B2186959 : Blo 1943435 2186959 := bstep (se 1 (by rfl) ⟨1640219, by rfl⟩ : syracuseStep 2186959 = 3280439) B3280439
theorem B2915945 : Blo 1943435 2915945 := bstep (se 2 (by rfl) ⟨1093479, by rfl⟩ : syracuseStep 2915945 = 2186959) B2186959
theorem B1943963 : Blo 1943435 1943963 := bstep (se 1 (by rfl) ⟨1457972, by rfl⟩ : syracuseStep 1943963 = 2915945) B2915945
theorem B3113861 : Blo 1943435 3113861 := bbase (se 4 (by rfl) ⟨291924, by rfl⟩ : syracuseStep 3113861 = 583849) (by norm_num)
theorem B8303629 : Blo 1943435 8303629 := bstep (se 3 (by rfl) ⟨1556930, by rfl⟩ : syracuseStep 8303629 = 3113861) B3113861
theorem B11071505 : Blo 1943435 11071505 := bstep (se 2 (by rfl) ⟨4151814, by rfl⟩ : syracuseStep 11071505 = 8303629) B8303629
theorem B7381003 : Blo 1943435 7381003 := bstep (se 1 (by rfl) ⟨5535752, by rfl⟩ : syracuseStep 7381003 = 11071505) B11071505
theorem B9841337 : Blo 1943435 9841337 := bstep (se 2 (by rfl) ⟨3690501, by rfl⟩ : syracuseStep 9841337 = 7381003) B7381003
theorem B6560891 : Blo 1943435 6560891 := bstep (se 1 (by rfl) ⟨4920668, by rfl⟩ : syracuseStep 6560891 = 9841337) B9841337
theorem B4373927 : Blo 1943435 4373927 := bstep (se 1 (by rfl) ⟨3280445, by rfl⟩ : syracuseStep 4373927 = 6560891) B6560891
theorem B2915951 : Blo 1943435 2915951 := bstep (se 1 (by rfl) ⟨2186963, by rfl⟩ : syracuseStep 2915951 = 4373927) B4373927
theorem B1943967 : Blo 1943435 1943967 := bstep (se 1 (by rfl) ⟨1457975, by rfl⟩ : syracuseStep 1943967 = 2915951) B2915951
theorem B2915957 : Blo 1943435 2915957 := bbase (se 5 (by rfl) ⟨136685, by rfl⟩ : syracuseStep 2915957 = 273371) (by norm_num)
theorem B1943971 : Blo 1943435 1943971 := bstep (se 1 (by rfl) ⟨1457978, by rfl⟩ : syracuseStep 1943971 = 2915957) B2915957
theorem B3690517 : Blo 1943435 3690517 := bbase (se 6 (by rfl) ⟨86496, by rfl⟩ : syracuseStep 3690517 = 172993) (by norm_num)
theorem B4920689 : Blo 1943435 4920689 := bstep (se 2 (by rfl) ⟨1845258, by rfl⟩ : syracuseStep 4920689 = 3690517) B3690517
theorem B3280459 : Blo 1943435 3280459 := bstep (se 1 (by rfl) ⟨2460344, by rfl⟩ : syracuseStep 3280459 = 4920689) B4920689
theorem B4373945 : Blo 1943435 4373945 := bstep (se 2 (by rfl) ⟨1640229, by rfl⟩ : syracuseStep 4373945 = 3280459) B3280459
theorem B2915963 : Blo 1943435 2915963 := bstep (se 1 (by rfl) ⟨2186972, by rfl⟩ : syracuseStep 2915963 = 4373945) B4373945
theorem B1943975 : Blo 1943435 1943975 := bstep (se 1 (by rfl) ⟨1457981, by rfl⟩ : syracuseStep 1943975 = 2915963) B2915963
theorem B2186977 : Blo 1943435 2186977 := bbase (se 2 (by rfl) ⟨820116, by rfl⟩ : syracuseStep 2186977 = 1640233) (by norm_num)
theorem B2915969 : Blo 1943435 2915969 := bstep (se 2 (by rfl) ⟨1093488, by rfl⟩ : syracuseStep 2915969 = 2186977) B2186977
theorem B1943979 : Blo 1943435 1943979 := bstep (se 1 (by rfl) ⟨1457984, by rfl⟩ : syracuseStep 1943979 = 2915969) B2915969
theorem B4920709 : Blo 1943435 4920709 := bbase (se 4 (by rfl) ⟨461316, by rfl⟩ : syracuseStep 4920709 = 922633) (by norm_num)
theorem B6560945 : Blo 1943435 6560945 := bstep (se 2 (by rfl) ⟨2460354, by rfl⟩ : syracuseStep 6560945 = 4920709) B4920709
theorem B4373963 : Blo 1943435 4373963 := bstep (se 1 (by rfl) ⟨3280472, by rfl⟩ : syracuseStep 4373963 = 6560945) B6560945
theorem B2915975 : Blo 1943435 2915975 := bstep (se 1 (by rfl) ⟨2186981, by rfl⟩ : syracuseStep 2915975 = 4373963) B4373963
theorem B1943983 : Blo 1943435 1943983 := bstep (se 1 (by rfl) ⟨1457987, by rfl⟩ : syracuseStep 1943983 = 2915975) B2915975
theorem B2915981 : Blo 1943435 2915981 := bbase (se 3 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 2915981 = 1093493) (by norm_num)
theorem B1943987 : Blo 1943435 1943987 := bstep (se 1 (by rfl) ⟨1457990, by rfl⟩ : syracuseStep 1943987 = 2915981) B2915981
theorem B4373981 : Blo 1943435 4373981 := bbase (se 3 (by rfl) ⟨820121, by rfl⟩ : syracuseStep 4373981 = 1640243) (by norm_num)
theorem B2915987 : Blo 1943435 2915987 := bstep (se 1 (by rfl) ⟨2186990, by rfl⟩ : syracuseStep 2915987 = 4373981) B4373981
theorem B1943991 : Blo 1943435 1943991 := bstep (se 1 (by rfl) ⟨1457993, by rfl⟩ : syracuseStep 1943991 = 2915987) B2915987
theorem B3280493 : Blo 1943435 3280493 := bbase (se 3 (by rfl) ⟨615092, by rfl⟩ : syracuseStep 3280493 = 1230185) (by norm_num)
theorem B2186995 : Blo 1943435 2186995 := bstep (se 1 (by rfl) ⟨1640246, by rfl⟩ : syracuseStep 2186995 = 3280493) B3280493
theorem B2915993 : Blo 1943435 2915993 := bstep (se 2 (by rfl) ⟨1093497, by rfl⟩ : syracuseStep 2915993 = 2186995) B2186995
theorem B1943995 : Blo 1943435 1943995 := bstep (se 1 (by rfl) ⟨1457996, by rfl⟩ : syracuseStep 1943995 = 2915993) B2915993
theorem B2104265 : Blo 1943435 2104265 := bbase (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) (by norm_num)
theorem B5611373 : Blo 1943435 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B3740915 : Blo 1943435 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B9975773 : Blo 1943435 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B6650515 : Blo 1943435 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B8867353 : Blo 1943435 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B11823137 : Blo 1943435 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B7882091 : Blo 1943435 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B5254727 : Blo 1943435 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B14012605 : Blo 1943435 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B18683473 : Blo 1943435 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B24911297 : Blo 1943435 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B16607531 : Blo 1943435 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B11071687 : Blo 1943435 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B14762249 : Blo 1943435 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B9841499 : Blo 1943435 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B6560999 : Blo 1943435 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B4373999 : Blo 1943435 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B2915999 : Blo 1943435 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B1943999 : Blo 1943435 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B2916005 : Blo 1943435 2916005 := bbase (se 4 (by rfl) ⟨273375, by rfl⟩ : syracuseStep 2916005 = 546751) (by norm_num)
theorem B1944003 : Blo 1943435 1944003 := bstep (se 1 (by rfl) ⟨1458002, by rfl⟩ : syracuseStep 1944003 = 2916005) B2916005
theorem B2460385 : Blo 1943435 2460385 := bbase (se 2 (by rfl) ⟨922644, by rfl⟩ : syracuseStep 2460385 = 1845289) (by norm_num)
theorem B3280513 : Blo 1943435 3280513 := bstep (se 2 (by rfl) ⟨1230192, by rfl⟩ : syracuseStep 3280513 = 2460385) B2460385
theorem B4374017 : Blo 1943435 4374017 := bstep (se 2 (by rfl) ⟨1640256, by rfl⟩ : syracuseStep 4374017 = 3280513) B3280513
theorem B2916011 : Blo 1943435 2916011 := bstep (se 1 (by rfl) ⟨2187008, by rfl⟩ : syracuseStep 2916011 = 4374017) B4374017
theorem B1944007 : Blo 1943435 1944007 := bstep (se 1 (by rfl) ⟨1458005, by rfl⟩ : syracuseStep 1944007 = 2916011) B2916011
theorem B2187013 : Blo 1943435 2187013 := bbase (se 4 (by rfl) ⟨205032, by rfl⟩ : syracuseStep 2187013 = 410065) (by norm_num)
theorem B2916017 : Blo 1943435 2916017 := bstep (se 2 (by rfl) ⟨1093506, by rfl⟩ : syracuseStep 2916017 = 2187013) B2187013
theorem B1944011 : Blo 1943435 1944011 := bstep (se 1 (by rfl) ⟨1458008, by rfl⟩ : syracuseStep 1944011 = 2916017) B2916017
theorem B4670909 : Blo 1943435 4670909 := bbase (se 3 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 4670909 = 1751591) (by norm_num)
theorem B3113939 : Blo 1943435 3113939 := bstep (se 1 (by rfl) ⟨2335454, by rfl⟩ : syracuseStep 3113939 = 4670909) B4670909
theorem B2075959 : Blo 1943435 2075959 := bstep (se 1 (by rfl) ⟨1556969, by rfl⟩ : syracuseStep 2075959 = 3113939) B3113939
theorem B2767945 : Blo 1943435 2767945 := bstep (se 2 (by rfl) ⟨1037979, by rfl⟩ : syracuseStep 2767945 = 2075959) B2075959
theorem B3690593 : Blo 1943435 3690593 := bstep (se 2 (by rfl) ⟨1383972, by rfl⟩ : syracuseStep 3690593 = 2767945) B2767945
theorem B2460395 : Blo 1943435 2460395 := bstep (se 1 (by rfl) ⟨1845296, by rfl⟩ : syracuseStep 2460395 = 3690593) B3690593
theorem B6561053 : Blo 1943435 6561053 := bstep (se 3 (by rfl) ⟨1230197, by rfl⟩ : syracuseStep 6561053 = 2460395) B2460395
theorem B4374035 : Blo 1943435 4374035 := bstep (se 1 (by rfl) ⟨3280526, by rfl⟩ : syracuseStep 4374035 = 6561053) B6561053
theorem B2916023 : Blo 1943435 2916023 := bstep (se 1 (by rfl) ⟨2187017, by rfl⟩ : syracuseStep 2916023 = 4374035) B4374035
theorem B1944015 : Blo 1943435 1944015 := bstep (se 1 (by rfl) ⟨1458011, by rfl⟩ : syracuseStep 1944015 = 2916023) B2916023
theorem B2916029 : Blo 1943435 2916029 := bbase (se 3 (by rfl) ⟨546755, by rfl⟩ : syracuseStep 2916029 = 1093511) (by norm_num)
theorem B1944019 : Blo 1943435 1944019 := bstep (se 1 (by rfl) ⟨1458014, by rfl⟩ : syracuseStep 1944019 = 2916029) B2916029
theorem B4374053 : Blo 1943435 4374053 := bbase (se 4 (by rfl) ⟨410067, by rfl⟩ : syracuseStep 4374053 = 820135) (by norm_num)
theorem B2916035 : Blo 1943435 2916035 := bstep (se 1 (by rfl) ⟨2187026, by rfl⟩ : syracuseStep 2916035 = 4374053) B4374053
theorem B1944023 : Blo 1943435 1944023 := bstep (se 1 (by rfl) ⟨1458017, by rfl⟩ : syracuseStep 1944023 = 2916035) B2916035
theorem B4920821 : Blo 1943435 4920821 := bbase (se 5 (by rfl) ⟨230663, by rfl⟩ : syracuseStep 4920821 = 461327) (by norm_num)
theorem B3280547 : Blo 1943435 3280547 := bstep (se 1 (by rfl) ⟨2460410, by rfl⟩ : syracuseStep 3280547 = 4920821) B4920821
theorem B2187031 : Blo 1943435 2187031 := bstep (se 1 (by rfl) ⟨1640273, by rfl⟩ : syracuseStep 2187031 = 3280547) B3280547
theorem B2916041 : Blo 1943435 2916041 := bstep (se 2 (by rfl) ⟨1093515, by rfl⟩ : syracuseStep 2916041 = 2187031) B2187031
theorem B1944027 : Blo 1943435 1944027 := bstep (se 1 (by rfl) ⟨1458020, by rfl⟩ : syracuseStep 1944027 = 2916041) B2916041
theorem B2493985 : Blo 1943435 2493985 := bbase (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) (by norm_num)
theorem B3325313 : Blo 1943435 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2216875 : Blo 1943435 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B2955833 : Blo 1943435 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B31528885 : Blo 1943435 31528885 := bstep (se 5 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 31528885 = 2955833) B2955833
theorem B42038513 : Blo 1943435 42038513 := bstep (se 2 (by rfl) ⟨15764442, by rfl⟩ : syracuseStep 42038513 = 31528885) B31528885
theorem B28025675 : Blo 1943435 28025675 := bstep (se 1 (by rfl) ⟨21019256, by rfl⟩ : syracuseStep 28025675 = 42038513) B42038513
theorem B18683783 : Blo 1943435 18683783 := bstep (se 1 (by rfl) ⟨14012837, by rfl⟩ : syracuseStep 18683783 = 28025675) B28025675
theorem B12455855 : Blo 1943435 12455855 := bstep (se 1 (by rfl) ⟨9341891, by rfl⟩ : syracuseStep 12455855 = 18683783) B18683783
theorem B8303903 : Blo 1943435 8303903 := bstep (se 1 (by rfl) ⟨6227927, by rfl⟩ : syracuseStep 8303903 = 12455855) B12455855
theorem B5535935 : Blo 1943435 5535935 := bstep (se 1 (by rfl) ⟨4151951, by rfl⟩ : syracuseStep 5535935 = 8303903) B8303903
theorem B3690623 : Blo 1943435 3690623 := bstep (se 1 (by rfl) ⟨2767967, by rfl⟩ : syracuseStep 3690623 = 5535935) B5535935
theorem B9841661 : Blo 1943435 9841661 := bstep (se 3 (by rfl) ⟨1845311, by rfl⟩ : syracuseStep 9841661 = 3690623) B3690623
theorem B6561107 : Blo 1943435 6561107 := bstep (se 1 (by rfl) ⟨4920830, by rfl⟩ : syracuseStep 6561107 = 9841661) B9841661
theorem B4374071 : Blo 1943435 4374071 := bstep (se 1 (by rfl) ⟨3280553, by rfl⟩ : syracuseStep 4374071 = 6561107) B6561107
theorem B2916047 : Blo 1943435 2916047 := bstep (se 1 (by rfl) ⟨2187035, by rfl⟩ : syracuseStep 2916047 = 4374071) B4374071
theorem B1944031 : Blo 1943435 1944031 := bstep (se 1 (by rfl) ⟨1458023, by rfl⟩ : syracuseStep 1944031 = 2916047) B2916047
theorem B2916053 : Blo 1943435 2916053 := bbase (se 7 (by rfl) ⟨34172, by rfl⟩ : syracuseStep 2916053 = 68345) (by norm_num)
theorem B1944035 : Blo 1943435 1944035 := bstep (se 1 (by rfl) ⟨1458026, by rfl⟩ : syracuseStep 1944035 = 2916053) B2916053
theorem B5611493 : Blo 1943435 5611493 := bbase (se 4 (by rfl) ⟨526077, by rfl⟩ : syracuseStep 5611493 = 1052155) (by norm_num)
theorem B3740995 : Blo 1943435 3740995 := bstep (se 1 (by rfl) ⟨2805746, by rfl⟩ : syracuseStep 3740995 = 5611493) B5611493
theorem B4987993 : Blo 1943435 4987993 := bstep (se 2 (by rfl) ⟨1870497, by rfl⟩ : syracuseStep 4987993 = 3740995) B3740995
theorem B6650657 : Blo 1943435 6650657 := bstep (se 2 (by rfl) ⟨2493996, by rfl⟩ : syracuseStep 6650657 = 4987993) B4987993
theorem B4433771 : Blo 1943435 4433771 := bstep (se 1 (by rfl) ⟨3325328, by rfl⟩ : syracuseStep 4433771 = 6650657) B6650657
theorem B2955847 : Blo 1943435 2955847 := bstep (se 1 (by rfl) ⟨2216885, by rfl⟩ : syracuseStep 2955847 = 4433771) B4433771
theorem B3941129 : Blo 1943435 3941129 := bstep (se 2 (by rfl) ⟨1477923, by rfl⟩ : syracuseStep 3941129 = 2955847) B2955847
theorem B2627419 : Blo 1943435 2627419 := bstep (se 1 (by rfl) ⟨1970564, by rfl⟩ : syracuseStep 2627419 = 3941129) B3941129
theorem B3503225 : Blo 1943435 3503225 := bstep (se 2 (by rfl) ⟨1313709, by rfl⟩ : syracuseStep 3503225 = 2627419) B2627419
theorem B2335483 : Blo 1943435 2335483 := bstep (se 1 (by rfl) ⟨1751612, by rfl⟩ : syracuseStep 2335483 = 3503225) B3503225
theorem B3113977 : Blo 1943435 3113977 := bstep (se 2 (by rfl) ⟨1167741, by rfl⟩ : syracuseStep 3113977 = 2335483) B2335483
theorem B4151969 : Blo 1943435 4151969 := bstep (se 2 (by rfl) ⟨1556988, by rfl⟩ : syracuseStep 4151969 = 3113977) B3113977
theorem B2767979 : Blo 1943435 2767979 := bstep (se 1 (by rfl) ⟨2075984, by rfl⟩ : syracuseStep 2767979 = 4151969) B4151969
theorem B7381277 : Blo 1943435 7381277 := bstep (se 3 (by rfl) ⟨1383989, by rfl⟩ : syracuseStep 7381277 = 2767979) B2767979
theorem B4920851 : Blo 1943435 4920851 := bstep (se 1 (by rfl) ⟨3690638, by rfl⟩ : syracuseStep 4920851 = 7381277) B7381277
theorem B3280567 : Blo 1943435 3280567 := bstep (se 1 (by rfl) ⟨2460425, by rfl⟩ : syracuseStep 3280567 = 4920851) B4920851
theorem B4374089 : Blo 1943435 4374089 := bstep (se 2 (by rfl) ⟨1640283, by rfl⟩ : syracuseStep 4374089 = 3280567) B3280567
theorem B2916059 : Blo 1943435 2916059 := bstep (se 1 (by rfl) ⟨2187044, by rfl⟩ : syracuseStep 2916059 = 4374089) B4374089
theorem B1944039 : Blo 1943435 1944039 := bstep (se 1 (by rfl) ⟨1458029, by rfl⟩ : syracuseStep 1944039 = 2916059) B2916059
theorem B2187049 : Blo 1943435 2187049 := bbase (se 2 (by rfl) ⟨820143, by rfl⟩ : syracuseStep 2187049 = 1640287) (by norm_num)
theorem B2916065 : Blo 1943435 2916065 := bstep (se 2 (by rfl) ⟨1093524, by rfl⟩ : syracuseStep 2916065 = 2187049) B2187049
theorem B1944043 : Blo 1943435 1944043 := bstep (se 1 (by rfl) ⟨1458032, by rfl⟩ : syracuseStep 1944043 = 2916065) B2916065
theorem B12455957 : Blo 1943435 12455957 := bbase (se 6 (by rfl) ⟨291936, by rfl⟩ : syracuseStep 12455957 = 583873) (by norm_num)
theorem B8303971 : Blo 1943435 8303971 := bstep (se 1 (by rfl) ⟨6227978, by rfl⟩ : syracuseStep 8303971 = 12455957) B12455957
theorem B11071961 : Blo 1943435 11071961 := bstep (se 2 (by rfl) ⟨4151985, by rfl⟩ : syracuseStep 11071961 = 8303971) B8303971
theorem B7381307 : Blo 1943435 7381307 := bstep (se 1 (by rfl) ⟨5535980, by rfl⟩ : syracuseStep 7381307 = 11071961) B11071961
theorem B4920871 : Blo 1943435 4920871 := bstep (se 1 (by rfl) ⟨3690653, by rfl⟩ : syracuseStep 4920871 = 7381307) B7381307
theorem B6561161 : Blo 1943435 6561161 := bstep (se 2 (by rfl) ⟨2460435, by rfl⟩ : syracuseStep 6561161 = 4920871) B4920871
theorem B4374107 : Blo 1943435 4374107 := bstep (se 1 (by rfl) ⟨3280580, by rfl⟩ : syracuseStep 4374107 = 6561161) B6561161
theorem B2916071 : Blo 1943435 2916071 := bstep (se 1 (by rfl) ⟨2187053, by rfl⟩ : syracuseStep 2916071 = 4374107) B4374107
theorem B1944047 : Blo 1943435 1944047 := bstep (se 1 (by rfl) ⟨1458035, by rfl⟩ : syracuseStep 1944047 = 2916071) B2916071
theorem B2916077 : Blo 1943435 2916077 := bbase (se 3 (by rfl) ⟨546764, by rfl⟩ : syracuseStep 2916077 = 1093529) (by norm_num)
theorem B1944051 : Blo 1943435 1944051 := bstep (se 1 (by rfl) ⟨1458038, by rfl⟩ : syracuseStep 1944051 = 2916077) B2916077
theorem B4374125 : Blo 1943435 4374125 := bbase (se 3 (by rfl) ⟨820148, by rfl⟩ : syracuseStep 4374125 = 1640297) (by norm_num)
theorem B2916083 : Blo 1943435 2916083 := bstep (se 1 (by rfl) ⟨2187062, by rfl⟩ : syracuseStep 2916083 = 4374125) B4374125
theorem B1944055 : Blo 1943435 1944055 := bstep (se 1 (by rfl) ⟨1458041, by rfl⟩ : syracuseStep 1944055 = 2916083) B2916083
theorem B3690677 : Blo 1943435 3690677 := bbase (se 5 (by rfl) ⟨173000, by rfl⟩ : syracuseStep 3690677 = 346001) (by norm_num)
theorem B2460451 : Blo 1943435 2460451 := bstep (se 1 (by rfl) ⟨1845338, by rfl⟩ : syracuseStep 2460451 = 3690677) B3690677
theorem B3280601 : Blo 1943435 3280601 := bstep (se 2 (by rfl) ⟨1230225, by rfl⟩ : syracuseStep 3280601 = 2460451) B2460451
theorem B2187067 : Blo 1943435 2187067 := bstep (se 1 (by rfl) ⟨1640300, by rfl⟩ : syracuseStep 2187067 = 3280601) B3280601
theorem B2916089 : Blo 1943435 2916089 := bstep (se 2 (by rfl) ⟨1093533, by rfl⟩ : syracuseStep 2916089 = 2187067) B2187067
theorem B1944059 : Blo 1943435 1944059 := bstep (se 1 (by rfl) ⟨1458044, by rfl⟩ : syracuseStep 1944059 = 2916089) B2916089
theorem B14964149 : Blo 1943435 14964149 := bbase (se 5 (by rfl) ⟨701444, by rfl⟩ : syracuseStep 14964149 = 1402889) (by norm_num)
theorem B9976099 : Blo 1943435 9976099 := bstep (se 1 (by rfl) ⟨7482074, by rfl⟩ : syracuseStep 9976099 = 14964149) B14964149
theorem B13301465 : Blo 1943435 13301465 := bstep (se 2 (by rfl) ⟨4988049, by rfl⟩ : syracuseStep 13301465 = 9976099) B9976099
theorem B141882293 : Blo 1943435 141882293 := bstep (se 5 (by rfl) ⟨6650732, by rfl⟩ : syracuseStep 141882293 = 13301465) B13301465
theorem B94588195 : Blo 1943435 94588195 := bstep (se 1 (by rfl) ⟨70941146, by rfl⟩ : syracuseStep 94588195 = 141882293) B141882293
theorem B126117593 : Blo 1943435 126117593 := bstep (se 2 (by rfl) ⟨47294097, by rfl⟩ : syracuseStep 126117593 = 94588195) B94588195
theorem B84078395 : Blo 1943435 84078395 := bstep (se 1 (by rfl) ⟨63058796, by rfl⟩ : syracuseStep 84078395 = 126117593) B126117593
theorem B56052263 : Blo 1943435 56052263 := bstep (se 1 (by rfl) ⟨42039197, by rfl⟩ : syracuseStep 56052263 = 84078395) B84078395
theorem B37368175 : Blo 1943435 37368175 := bstep (se 1 (by rfl) ⟨28026131, by rfl⟩ : syracuseStep 37368175 = 56052263) B56052263
theorem B49824233 : Blo 1943435 49824233 := bstep (se 2 (by rfl) ⟨18684087, by rfl⟩ : syracuseStep 49824233 = 37368175) B37368175
theorem B33216155 : Blo 1943435 33216155 := bstep (se 1 (by rfl) ⟨24912116, by rfl⟩ : syracuseStep 33216155 = 49824233) B49824233
theorem B22144103 : Blo 1943435 22144103 := bstep (se 1 (by rfl) ⟨16608077, by rfl⟩ : syracuseStep 22144103 = 33216155) B33216155
theorem B14762735 : Blo 1943435 14762735 := bstep (se 1 (by rfl) ⟨11072051, by rfl⟩ : syracuseStep 14762735 = 22144103) B22144103
theorem B9841823 : Blo 1943435 9841823 := bstep (se 1 (by rfl) ⟨7381367, by rfl⟩ : syracuseStep 9841823 = 14762735) B14762735
theorem B6561215 : Blo 1943435 6561215 := bstep (se 1 (by rfl) ⟨4920911, by rfl⟩ : syracuseStep 6561215 = 9841823) B9841823
theorem B4374143 : Blo 1943435 4374143 := bstep (se 1 (by rfl) ⟨3280607, by rfl⟩ : syracuseStep 4374143 = 6561215) B6561215
theorem B2916095 : Blo 1943435 2916095 := bstep (se 1 (by rfl) ⟨2187071, by rfl⟩ : syracuseStep 2916095 = 4374143) B4374143
theorem B1944063 : Blo 1943435 1944063 := bstep (se 1 (by rfl) ⟨1458047, by rfl⟩ : syracuseStep 1944063 = 2916095) B2916095
theorem B2916101 : Blo 1943435 2916101 := bbase (se 4 (by rfl) ⟨273384, by rfl⟩ : syracuseStep 2916101 = 546769) (by norm_num)
theorem B1944067 : Blo 1943435 1944067 := bstep (se 1 (by rfl) ⟨1458050, by rfl⟩ : syracuseStep 1944067 = 2916101) B2916101
theorem B3280621 : Blo 1943435 3280621 := bbase (se 3 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 3280621 = 1230233) (by norm_num)
theorem B4374161 : Blo 1943435 4374161 := bstep (se 2 (by rfl) ⟨1640310, by rfl⟩ : syracuseStep 4374161 = 3280621) B3280621
theorem B2916107 : Blo 1943435 2916107 := bstep (se 1 (by rfl) ⟨2187080, by rfl⟩ : syracuseStep 2916107 = 4374161) B4374161
theorem B1944071 : Blo 1943435 1944071 := bstep (se 1 (by rfl) ⟨1458053, by rfl⟩ : syracuseStep 1944071 = 2916107) B2916107
theorem B2187085 : Blo 1943435 2187085 := bbase (se 3 (by rfl) ⟨410078, by rfl⟩ : syracuseStep 2187085 = 820157) (by norm_num)
theorem B2916113 : Blo 1943435 2916113 := bstep (se 2 (by rfl) ⟨1093542, by rfl⟩ : syracuseStep 2916113 = 2187085) B2187085
theorem B1944075 : Blo 1943435 1944075 := bstep (se 1 (by rfl) ⟨1458056, by rfl⟩ : syracuseStep 1944075 = 2916113) B2916113
theorem B6561269 : Blo 1943435 6561269 := bbase (se 5 (by rfl) ⟨307559, by rfl⟩ : syracuseStep 6561269 = 615119) (by norm_num)
theorem B4374179 : Blo 1943435 4374179 := bstep (se 1 (by rfl) ⟨3280634, by rfl⟩ : syracuseStep 4374179 = 6561269) B6561269
theorem B2916119 : Blo 1943435 2916119 := bstep (se 1 (by rfl) ⟨2187089, by rfl⟩ : syracuseStep 2916119 = 4374179) B4374179
theorem B1944079 : Blo 1943435 1944079 := bstep (se 1 (by rfl) ⟨1458059, by rfl⟩ : syracuseStep 1944079 = 2916119) B2916119
theorem B2916125 : Blo 1943435 2916125 := bbase (se 3 (by rfl) ⟨546773, by rfl⟩ : syracuseStep 2916125 = 1093547) (by norm_num)
theorem B1944083 : Blo 1943435 1944083 := bstep (se 1 (by rfl) ⟨1458062, by rfl⟩ : syracuseStep 1944083 = 2916125) B2916125
theorem B4374197 : Blo 1943435 4374197 := bbase (se 5 (by rfl) ⟨205040, by rfl⟩ : syracuseStep 4374197 = 410081) (by norm_num)
theorem B2916131 : Blo 1943435 2916131 := bstep (se 1 (by rfl) ⟨2187098, by rfl⟩ : syracuseStep 2916131 = 4374197) B4374197
theorem B1944087 : Blo 1943435 1944087 := bstep (se 1 (by rfl) ⟨1458065, by rfl⟩ : syracuseStep 1944087 = 2916131) B2916131
theorem B11072213 : Blo 1943435 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B7381475 : Blo 1943435 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B4920983 : Blo 1943435 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B3280655 : Blo 1943435 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B2187103 : Blo 1943435 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B2916137 : Blo 1943435 2916137 := bstep (se 2 (by rfl) ⟨1093551, by rfl⟩ : syracuseStep 2916137 = 2187103) B2187103
theorem B1944091 : Blo 1943435 1944091 := bstep (se 1 (by rfl) ⟨1458068, by rfl⟩ : syracuseStep 1944091 = 2916137) B2916137
theorem B5536117 : Blo 1943435 5536117 := bbase (se 5 (by rfl) ⟨259505, by rfl⟩ : syracuseStep 5536117 = 519011) (by norm_num)
theorem B7381489 : Blo 1943435 7381489 := bstep (se 2 (by rfl) ⟨2768058, by rfl⟩ : syracuseStep 7381489 = 5536117) B5536117
theorem B9841985 : Blo 1943435 9841985 := bstep (se 2 (by rfl) ⟨3690744, by rfl⟩ : syracuseStep 9841985 = 7381489) B7381489
theorem B6561323 : Blo 1943435 6561323 := bstep (se 1 (by rfl) ⟨4920992, by rfl⟩ : syracuseStep 6561323 = 9841985) B9841985
theorem B4374215 : Blo 1943435 4374215 := bstep (se 1 (by rfl) ⟨3280661, by rfl⟩ : syracuseStep 4374215 = 6561323) B6561323
theorem B2916143 : Blo 1943435 2916143 := bstep (se 1 (by rfl) ⟨2187107, by rfl⟩ : syracuseStep 2916143 = 4374215) B4374215
theorem B1944095 : Blo 1943435 1944095 := bstep (se 1 (by rfl) ⟨1458071, by rfl⟩ : syracuseStep 1944095 = 2916143) B2916143
theorem B2916149 : Blo 1943435 2916149 := bbase (se 5 (by rfl) ⟨136694, by rfl⟩ : syracuseStep 2916149 = 273389) (by norm_num)
theorem B1944099 : Blo 1943435 1944099 := bstep (se 1 (by rfl) ⟨1458074, by rfl⟩ : syracuseStep 1944099 = 2916149) B2916149
theorem B4921013 : Blo 1943435 4921013 := bbase (se 5 (by rfl) ⟨230672, by rfl⟩ : syracuseStep 4921013 = 461345) (by norm_num)
theorem B3280675 : Blo 1943435 3280675 := bstep (se 1 (by rfl) ⟨2460506, by rfl⟩ : syracuseStep 3280675 = 4921013) B4921013
theorem B4374233 : Blo 1943435 4374233 := bstep (se 2 (by rfl) ⟨1640337, by rfl⟩ : syracuseStep 4374233 = 3280675) B3280675
theorem B2916155 : Blo 1943435 2916155 := bstep (se 1 (by rfl) ⟨2187116, by rfl⟩ : syracuseStep 2916155 = 4374233) B4374233
theorem B1944103 : Blo 1943435 1944103 := bstep (se 1 (by rfl) ⟨1458077, by rfl⟩ : syracuseStep 1944103 = 2916155) B2916155
theorem B2187121 : Blo 1943435 2187121 := bbase (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) (by norm_num)
theorem B2916161 : Blo 1943435 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B1944107 : Blo 1943435 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B8304245 : Blo 1943435 8304245 := bbase (se 5 (by rfl) ⟨389261, by rfl⟩ : syracuseStep 8304245 = 778523) (by norm_num)
theorem B5536163 : Blo 1943435 5536163 := bstep (se 1 (by rfl) ⟨4152122, by rfl⟩ : syracuseStep 5536163 = 8304245) B8304245
theorem B3690775 : Blo 1943435 3690775 := bstep (se 1 (by rfl) ⟨2768081, by rfl⟩ : syracuseStep 3690775 = 5536163) B5536163
theorem B4921033 : Blo 1943435 4921033 := bstep (se 2 (by rfl) ⟨1845387, by rfl⟩ : syracuseStep 4921033 = 3690775) B3690775
theorem B6561377 : Blo 1943435 6561377 := bstep (se 2 (by rfl) ⟨2460516, by rfl⟩ : syracuseStep 6561377 = 4921033) B4921033
theorem B4374251 : Blo 1943435 4374251 := bstep (se 1 (by rfl) ⟨3280688, by rfl⟩ : syracuseStep 4374251 = 6561377) B6561377
theorem B2916167 : Blo 1943435 2916167 := bstep (se 1 (by rfl) ⟨2187125, by rfl⟩ : syracuseStep 2916167 = 4374251) B4374251
theorem B1944111 : Blo 1943435 1944111 := bstep (se 1 (by rfl) ⟨1458083, by rfl⟩ : syracuseStep 1944111 = 2916167) B2916167
theorem B2916173 : Blo 1943435 2916173 := bbase (se 3 (by rfl) ⟨546782, by rfl⟩ : syracuseStep 2916173 = 1093565) (by norm_num)
theorem B1944115 : Blo 1943435 1944115 := bstep (se 1 (by rfl) ⟨1458086, by rfl⟩ : syracuseStep 1944115 = 2916173) B2916173
theorem B4374269 : Blo 1943435 4374269 := bbase (se 3 (by rfl) ⟨820175, by rfl⟩ : syracuseStep 4374269 = 1640351) (by norm_num)
theorem B2916179 : Blo 1943435 2916179 := bstep (se 1 (by rfl) ⟨2187134, by rfl⟩ : syracuseStep 2916179 = 4374269) B4374269
theorem B1944119 : Blo 1943435 1944119 := bstep (se 1 (by rfl) ⟨1458089, by rfl⟩ : syracuseStep 1944119 = 2916179) B2916179
theorem B3280709 : Blo 1943435 3280709 := bbase (se 4 (by rfl) ⟨307566, by rfl⟩ : syracuseStep 3280709 = 615133) (by norm_num)
theorem B2187139 : Blo 1943435 2187139 := bstep (se 1 (by rfl) ⟨1640354, by rfl⟩ : syracuseStep 2187139 = 3280709) B3280709
theorem B2916185 : Blo 1943435 2916185 := bstep (se 2 (by rfl) ⟨1093569, by rfl⟩ : syracuseStep 2916185 = 2187139) B2187139
theorem B1944123 : Blo 1943435 1944123 := bstep (se 1 (by rfl) ⟨1458092, by rfl⟩ : syracuseStep 1944123 = 2916185) B2916185
theorem B14763221 : Blo 1943435 14763221 := bbase (se 7 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 14763221 = 346013) (by norm_num)
theorem B9842147 : Blo 1943435 9842147 := bstep (se 1 (by rfl) ⟨7381610, by rfl⟩ : syracuseStep 9842147 = 14763221) B14763221
theorem B6561431 : Blo 1943435 6561431 := bstep (se 1 (by rfl) ⟨4921073, by rfl⟩ : syracuseStep 6561431 = 9842147) B9842147
theorem B4374287 : Blo 1943435 4374287 := bstep (se 1 (by rfl) ⟨3280715, by rfl⟩ : syracuseStep 4374287 = 6561431) B6561431
theorem B2916191 : Blo 1943435 2916191 := bstep (se 1 (by rfl) ⟨2187143, by rfl⟩ : syracuseStep 2916191 = 4374287) B4374287
theorem B1944127 : Blo 1943435 1944127 := bstep (se 1 (by rfl) ⟨1458095, by rfl⟩ : syracuseStep 1944127 = 2916191) B2916191
theorem B2916197 : Blo 1943435 2916197 := bbase (se 4 (by rfl) ⟨273393, by rfl⟩ : syracuseStep 2916197 = 546787) (by norm_num)
theorem B1944131 : Blo 1943435 1944131 := bstep (se 1 (by rfl) ⟨1458098, by rfl⟩ : syracuseStep 1944131 = 2916197) B2916197
theorem B3690821 : Blo 1943435 3690821 := bbase (se 4 (by rfl) ⟨346014, by rfl⟩ : syracuseStep 3690821 = 692029) (by norm_num)
theorem B2460547 : Blo 1943435 2460547 := bstep (se 1 (by rfl) ⟨1845410, by rfl⟩ : syracuseStep 2460547 = 3690821) B3690821
theorem B3280729 : Blo 1943435 3280729 := bstep (se 2 (by rfl) ⟨1230273, by rfl⟩ : syracuseStep 3280729 = 2460547) B2460547
theorem B4374305 : Blo 1943435 4374305 := bstep (se 2 (by rfl) ⟨1640364, by rfl⟩ : syracuseStep 4374305 = 3280729) B3280729
theorem B2916203 : Blo 1943435 2916203 := bstep (se 1 (by rfl) ⟨2187152, by rfl⟩ : syracuseStep 2916203 = 4374305) B4374305
theorem B1944135 : Blo 1943435 1944135 := bstep (se 1 (by rfl) ⟨1458101, by rfl⟩ : syracuseStep 1944135 = 2916203) B2916203
theorem B2187157 : Blo 1943435 2187157 := bbase (se 6 (by rfl) ⟨51261, by rfl⟩ : syracuseStep 2187157 = 102523) (by norm_num)
theorem B2916209 : Blo 1943435 2916209 := bstep (se 2 (by rfl) ⟨1093578, by rfl⟩ : syracuseStep 2916209 = 2187157) B2187157
theorem B1944139 : Blo 1943435 1944139 := bstep (se 1 (by rfl) ⟨1458104, by rfl⟩ : syracuseStep 1944139 = 2916209) B2916209
theorem B2460557 : Blo 1943435 2460557 := bbase (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) (by norm_num)
theorem B6561485 : Blo 1943435 6561485 := bstep (se 3 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 6561485 = 2460557) B2460557
theorem B4374323 : Blo 1943435 4374323 := bstep (se 1 (by rfl) ⟨3280742, by rfl⟩ : syracuseStep 4374323 = 6561485) B6561485
theorem B2916215 : Blo 1943435 2916215 := bstep (se 1 (by rfl) ⟨2187161, by rfl⟩ : syracuseStep 2916215 = 4374323) B4374323
theorem B1944143 : Blo 1943435 1944143 := bstep (se 1 (by rfl) ⟨1458107, by rfl⟩ : syracuseStep 1944143 = 2916215) B2916215
theorem B2916221 : Blo 1943435 2916221 := bbase (se 3 (by rfl) ⟨546791, by rfl⟩ : syracuseStep 2916221 = 1093583) (by norm_num)
theorem B1944147 : Blo 1943435 1944147 := bstep (se 1 (by rfl) ⟨1458110, by rfl⟩ : syracuseStep 1944147 = 2916221) B2916221
theorem B4374341 : Blo 1943435 4374341 := bbase (se 4 (by rfl) ⟨410094, by rfl⟩ : syracuseStep 4374341 = 820189) (by norm_num)
theorem B2916227 : Blo 1943435 2916227 := bstep (se 1 (by rfl) ⟨2187170, by rfl⟩ : syracuseStep 2916227 = 4374341) B4374341
theorem B1944151 : Blo 1943435 1944151 := bstep (se 1 (by rfl) ⟨1458113, by rfl⟩ : syracuseStep 1944151 = 2916227) B2916227
theorem B4671245 : Blo 1943435 4671245 := bbase (se 3 (by rfl) ⟨875858, by rfl⟩ : syracuseStep 4671245 = 1751717) (by norm_num)
theorem B3114163 : Blo 1943435 3114163 := bstep (se 1 (by rfl) ⟨2335622, by rfl⟩ : syracuseStep 3114163 = 4671245) B4671245
theorem B4152217 : Blo 1943435 4152217 := bstep (se 2 (by rfl) ⟨1557081, by rfl⟩ : syracuseStep 4152217 = 3114163) B3114163
theorem B5536289 : Blo 1943435 5536289 := bstep (se 2 (by rfl) ⟨2076108, by rfl⟩ : syracuseStep 5536289 = 4152217) B4152217
theorem B3690859 : Blo 1943435 3690859 := bstep (se 1 (by rfl) ⟨2768144, by rfl⟩ : syracuseStep 3690859 = 5536289) B5536289
theorem B4921145 : Blo 1943435 4921145 := bstep (se 2 (by rfl) ⟨1845429, by rfl⟩ : syracuseStep 4921145 = 3690859) B3690859
theorem B3280763 : Blo 1943435 3280763 := bstep (se 1 (by rfl) ⟨2460572, by rfl⟩ : syracuseStep 3280763 = 4921145) B4921145
theorem B2187175 : Blo 1943435 2187175 := bstep (se 1 (by rfl) ⟨1640381, by rfl⟩ : syracuseStep 2187175 = 3280763) B3280763
theorem B2916233 : Blo 1943435 2916233 := bstep (se 2 (by rfl) ⟨1093587, by rfl⟩ : syracuseStep 2916233 = 2187175) B2187175
theorem B1944155 : Blo 1943435 1944155 := bstep (se 1 (by rfl) ⟨1458116, by rfl⟩ : syracuseStep 1944155 = 2916233) B2916233
theorem B9842309 : Blo 1943435 9842309 := bbase (se 4 (by rfl) ⟨922716, by rfl⟩ : syracuseStep 9842309 = 1845433) (by norm_num)
theorem B6561539 : Blo 1943435 6561539 := bstep (se 1 (by rfl) ⟨4921154, by rfl⟩ : syracuseStep 6561539 = 9842309) B9842309
theorem B4374359 : Blo 1943435 4374359 := bstep (se 1 (by rfl) ⟨3280769, by rfl⟩ : syracuseStep 4374359 = 6561539) B6561539
theorem B2916239 : Blo 1943435 2916239 := bstep (se 1 (by rfl) ⟨2187179, by rfl⟩ : syracuseStep 2916239 = 4374359) B4374359
theorem B1944159 : Blo 1943435 1944159 := bstep (se 1 (by rfl) ⟨1458119, by rfl⟩ : syracuseStep 1944159 = 2916239) B2916239
theorem B2916245 : Blo 1943435 2916245 := bbase (se 6 (by rfl) ⟨68349, by rfl⟩ : syracuseStep 2916245 = 136699) (by norm_num)
theorem B1944163 : Blo 1943435 1944163 := bstep (se 1 (by rfl) ⟨1458122, by rfl⟩ : syracuseStep 1944163 = 2916245) B2916245
theorem B2076121 : Blo 1943435 2076121 := bbase (se 2 (by rfl) ⟨778545, by rfl⟩ : syracuseStep 2076121 = 1557091) (by norm_num)
theorem B11072645 : Blo 1943435 11072645 := bstep (se 4 (by rfl) ⟨1038060, by rfl⟩ : syracuseStep 11072645 = 2076121) B2076121
theorem B7381763 : Blo 1943435 7381763 := bstep (se 1 (by rfl) ⟨5536322, by rfl⟩ : syracuseStep 7381763 = 11072645) B11072645
theorem B4921175 : Blo 1943435 4921175 := bstep (se 1 (by rfl) ⟨3690881, by rfl⟩ : syracuseStep 4921175 = 7381763) B7381763
theorem B3280783 : Blo 1943435 3280783 := bstep (se 1 (by rfl) ⟨2460587, by rfl⟩ : syracuseStep 3280783 = 4921175) B4921175
theorem B4374377 : Blo 1943435 4374377 := bstep (se 2 (by rfl) ⟨1640391, by rfl⟩ : syracuseStep 4374377 = 3280783) B3280783
theorem B2916251 : Blo 1943435 2916251 := bstep (se 1 (by rfl) ⟨2187188, by rfl⟩ : syracuseStep 2916251 = 4374377) B4374377
theorem B1944167 : Blo 1943435 1944167 := bstep (se 1 (by rfl) ⟨1458125, by rfl⟩ : syracuseStep 1944167 = 2916251) B2916251
theorem B2187193 : Blo 1943435 2187193 := bbase (se 2 (by rfl) ⟨820197, by rfl⟩ : syracuseStep 2187193 = 1640395) (by norm_num)
theorem B2916257 : Blo 1943435 2916257 := bstep (se 2 (by rfl) ⟨1093596, by rfl⟩ : syracuseStep 2916257 = 2187193) B2187193
theorem B1944171 : Blo 1943435 1944171 := bstep (se 1 (by rfl) ⟨1458128, by rfl⟩ : syracuseStep 1944171 = 2916257) B2916257
theorem B6228389 : Blo 1943435 6228389 := bbase (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) (by norm_num)
theorem B4152259 : Blo 1943435 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B5536345 : Blo 1943435 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B7381793 : Blo 1943435 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B4921195 : Blo 1943435 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B6561593 : Blo 1943435 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B4374395 : Blo 1943435 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B2916263 : Blo 1943435 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B1944175 : Blo 1943435 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B2916269 : Blo 1943435 2916269 := bbase (se 3 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 2916269 = 1093601) (by norm_num)
theorem B1944179 : Blo 1943435 1944179 := bstep (se 1 (by rfl) ⟨1458134, by rfl⟩ : syracuseStep 1944179 = 2916269) B2916269
theorem B4374413 : Blo 1943435 4374413 := bbase (se 3 (by rfl) ⟨820202, by rfl⟩ : syracuseStep 4374413 = 1640405) (by norm_num)
theorem B2916275 : Blo 1943435 2916275 := bstep (se 1 (by rfl) ⟨2187206, by rfl⟩ : syracuseStep 2916275 = 4374413) B4374413
theorem B1944183 : Blo 1943435 1944183 := bstep (se 1 (by rfl) ⟨1458137, by rfl⟩ : syracuseStep 1944183 = 2916275) B2916275
theorem B2460613 : Blo 1943435 2460613 := bbase (se 4 (by rfl) ⟨230682, by rfl⟩ : syracuseStep 2460613 = 461365) (by norm_num)
theorem B3280817 : Blo 1943435 3280817 := bstep (se 2 (by rfl) ⟨1230306, by rfl⟩ : syracuseStep 3280817 = 2460613) B2460613
theorem B2187211 : Blo 1943435 2187211 := bstep (se 1 (by rfl) ⟨1640408, by rfl⟩ : syracuseStep 2187211 = 3280817) B3280817
theorem B2916281 : Blo 1943435 2916281 := bstep (se 2 (by rfl) ⟨1093605, by rfl⟩ : syracuseStep 2916281 = 2187211) B2187211
theorem B1944187 : Blo 1943435 1944187 := bstep (se 1 (by rfl) ⟨1458140, by rfl⟩ : syracuseStep 1944187 = 2916281) B2916281
theorem B6651173 : Blo 1943435 6651173 := bbase (se 4 (by rfl) ⟨623547, by rfl⟩ : syracuseStep 6651173 = 1247095) (by norm_num)
theorem B4434115 : Blo 1943435 4434115 := bstep (se 1 (by rfl) ⟨3325586, by rfl⟩ : syracuseStep 4434115 = 6651173) B6651173
theorem B5912153 : Blo 1943435 5912153 := bstep (se 2 (by rfl) ⟨2217057, by rfl⟩ : syracuseStep 5912153 = 4434115) B4434115
theorem B3941435 : Blo 1943435 3941435 := bstep (se 1 (by rfl) ⟨2956076, by rfl⟩ : syracuseStep 3941435 = 5912153) B5912153
theorem B2627623 : Blo 1943435 2627623 := bstep (se 1 (by rfl) ⟨1970717, by rfl⟩ : syracuseStep 2627623 = 3941435) B3941435
theorem B14013989 : Blo 1943435 14013989 := bstep (se 4 (by rfl) ⟨1313811, by rfl⟩ : syracuseStep 14013989 = 2627623) B2627623
theorem B9342659 : Blo 1943435 9342659 := bstep (se 1 (by rfl) ⟨7006994, by rfl⟩ : syracuseStep 9342659 = 14013989) B14013989
theorem B24913757 : Blo 1943435 24913757 := bstep (se 3 (by rfl) ⟨4671329, by rfl⟩ : syracuseStep 24913757 = 9342659) B9342659
theorem B16609171 : Blo 1943435 16609171 := bstep (se 1 (by rfl) ⟨12456878, by rfl⟩ : syracuseStep 16609171 = 24913757) B24913757
theorem B22145561 : Blo 1943435 22145561 := bstep (se 2 (by rfl) ⟨8304585, by rfl⟩ : syracuseStep 22145561 = 16609171) B16609171
theorem B14763707 : Blo 1943435 14763707 := bstep (se 1 (by rfl) ⟨11072780, by rfl⟩ : syracuseStep 14763707 = 22145561) B22145561
theorem B9842471 : Blo 1943435 9842471 := bstep (se 1 (by rfl) ⟨7381853, by rfl⟩ : syracuseStep 9842471 = 14763707) B14763707
theorem B6561647 : Blo 1943435 6561647 := bstep (se 1 (by rfl) ⟨4921235, by rfl⟩ : syracuseStep 6561647 = 9842471) B9842471
theorem B4374431 : Blo 1943435 4374431 := bstep (se 1 (by rfl) ⟨3280823, by rfl⟩ : syracuseStep 4374431 = 6561647) B6561647
theorem B2916287 : Blo 1943435 2916287 := bstep (se 1 (by rfl) ⟨2187215, by rfl⟩ : syracuseStep 2916287 = 4374431) B4374431
theorem B1944191 : Blo 1943435 1944191 := bstep (se 1 (by rfl) ⟨1458143, by rfl⟩ : syracuseStep 1944191 = 2916287) B2916287
theorem B2916293 : Blo 1943435 2916293 := bbase (se 4 (by rfl) ⟨273402, by rfl⟩ : syracuseStep 2916293 = 546805) (by norm_num)
theorem B1944195 : Blo 1943435 1944195 := bstep (se 1 (by rfl) ⟨1458146, by rfl⟩ : syracuseStep 1944195 = 2916293) B2916293
theorem B3280837 : Blo 1943435 3280837 := bbase (se 4 (by rfl) ⟨307578, by rfl⟩ : syracuseStep 3280837 = 615157) (by norm_num)
theorem B4374449 : Blo 1943435 4374449 := bstep (se 2 (by rfl) ⟨1640418, by rfl⟩ : syracuseStep 4374449 = 3280837) B3280837
theorem B2916299 : Blo 1943435 2916299 := bstep (se 1 (by rfl) ⟨2187224, by rfl⟩ : syracuseStep 2916299 = 4374449) B4374449
theorem B1944199 : Blo 1943435 1944199 := bstep (se 1 (by rfl) ⟨1458149, by rfl⟩ : syracuseStep 1944199 = 2916299) B2916299
theorem B2187229 : Blo 1943435 2187229 := bbase (se 3 (by rfl) ⟨410105, by rfl⟩ : syracuseStep 2187229 = 820211) (by norm_num)
theorem B2916305 : Blo 1943435 2916305 := bstep (se 2 (by rfl) ⟨1093614, by rfl⟩ : syracuseStep 2916305 = 2187229) B2187229
theorem B1944203 : Blo 1943435 1944203 := bstep (se 1 (by rfl) ⟨1458152, by rfl⟩ : syracuseStep 1944203 = 2916305) B2916305
theorem B6561701 : Blo 1943435 6561701 := bbase (se 4 (by rfl) ⟨615159, by rfl⟩ : syracuseStep 6561701 = 1230319) (by norm_num)
theorem B4374467 : Blo 1943435 4374467 := bstep (se 1 (by rfl) ⟨3280850, by rfl⟩ : syracuseStep 4374467 = 6561701) B6561701
theorem B2916311 : Blo 1943435 2916311 := bstep (se 1 (by rfl) ⟨2187233, by rfl⟩ : syracuseStep 2916311 = 4374467) B4374467
theorem B1944207 : Blo 1943435 1944207 := bstep (se 1 (by rfl) ⟨1458155, by rfl⟩ : syracuseStep 1944207 = 2916311) B2916311
theorem B2916317 : Blo 1943435 2916317 := bbase (se 3 (by rfl) ⟨546809, by rfl⟩ : syracuseStep 2916317 = 1093619) (by norm_num)
theorem B1944211 : Blo 1943435 1944211 := bstep (se 1 (by rfl) ⟨1458158, by rfl⟩ : syracuseStep 1944211 = 2916317) B2916317
theorem B4374485 : Blo 1943435 4374485 := bbase (se 7 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 4374485 = 102527) (by norm_num)
theorem B2916323 : Blo 1943435 2916323 := bstep (se 1 (by rfl) ⟨2187242, by rfl⟩ : syracuseStep 2916323 = 4374485) B4374485
theorem B1944215 : Blo 1943435 1944215 := bstep (se 1 (by rfl) ⟨1458161, by rfl⟩ : syracuseStep 1944215 = 2916323) B2916323
theorem B3503549 : Blo 1943435 3503549 := bbase (se 3 (by rfl) ⟨656915, by rfl⟩ : syracuseStep 3503549 = 1313831) (by norm_num)
theorem B2335699 : Blo 1943435 2335699 := bstep (se 1 (by rfl) ⟨1751774, by rfl⟩ : syracuseStep 2335699 = 3503549) B3503549
theorem B12457061 : Blo 1943435 12457061 := bstep (se 4 (by rfl) ⟨1167849, by rfl⟩ : syracuseStep 12457061 = 2335699) B2335699
theorem B8304707 : Blo 1943435 8304707 := bstep (se 1 (by rfl) ⟨6228530, by rfl⟩ : syracuseStep 8304707 = 12457061) B12457061
theorem B5536471 : Blo 1943435 5536471 := bstep (se 1 (by rfl) ⟨4152353, by rfl⟩ : syracuseStep 5536471 = 8304707) B8304707
theorem B7381961 : Blo 1943435 7381961 := bstep (se 2 (by rfl) ⟨2768235, by rfl⟩ : syracuseStep 7381961 = 5536471) B5536471
theorem B4921307 : Blo 1943435 4921307 := bstep (se 1 (by rfl) ⟨3690980, by rfl⟩ : syracuseStep 4921307 = 7381961) B7381961
theorem B3280871 : Blo 1943435 3280871 := bstep (se 1 (by rfl) ⟨2460653, by rfl⟩ : syracuseStep 3280871 = 4921307) B4921307
theorem B2187247 : Blo 1943435 2187247 := bstep (se 1 (by rfl) ⟨1640435, by rfl⟩ : syracuseStep 2187247 = 3280871) B3280871
theorem B2916329 : Blo 1943435 2916329 := bstep (se 2 (by rfl) ⟨1093623, by rfl⟩ : syracuseStep 2916329 = 2187247) B2187247
theorem B1944219 : Blo 1943435 1944219 := bstep (se 1 (by rfl) ⟨1458164, by rfl⟩ : syracuseStep 1944219 = 2916329) B2916329
theorem B11824501 : Blo 1943435 11824501 := bbase (se 5 (by rfl) ⟨554273, by rfl⟩ : syracuseStep 11824501 = 1108547) (by norm_num)
theorem B15766001 : Blo 1943435 15766001 := bstep (se 2 (by rfl) ⟨5912250, by rfl⟩ : syracuseStep 15766001 = 11824501) B11824501
theorem B10510667 : Blo 1943435 10510667 := bstep (se 1 (by rfl) ⟨7883000, by rfl⟩ : syracuseStep 10510667 = 15766001) B15766001
theorem B7007111 : Blo 1943435 7007111 := bstep (se 1 (by rfl) ⟨5255333, by rfl⟩ : syracuseStep 7007111 = 10510667) B10510667
theorem B4671407 : Blo 1943435 4671407 := bstep (se 1 (by rfl) ⟨3503555, by rfl⟩ : syracuseStep 4671407 = 7007111) B7007111
theorem B3114271 : Blo 1943435 3114271 := bstep (se 1 (by rfl) ⟨2335703, by rfl⟩ : syracuseStep 3114271 = 4671407) B4671407
theorem B16609445 : Blo 1943435 16609445 := bstep (se 4 (by rfl) ⟨1557135, by rfl⟩ : syracuseStep 16609445 = 3114271) B3114271
theorem B11072963 : Blo 1943435 11072963 := bstep (se 1 (by rfl) ⟨8304722, by rfl⟩ : syracuseStep 11072963 = 16609445) B16609445
theorem B7381975 : Blo 1943435 7381975 := bstep (se 1 (by rfl) ⟨5536481, by rfl⟩ : syracuseStep 7381975 = 11072963) B11072963
theorem B9842633 : Blo 1943435 9842633 := bstep (se 2 (by rfl) ⟨3690987, by rfl⟩ : syracuseStep 9842633 = 7381975) B7381975
theorem B6561755 : Blo 1943435 6561755 := bstep (se 1 (by rfl) ⟨4921316, by rfl⟩ : syracuseStep 6561755 = 9842633) B9842633
theorem B4374503 : Blo 1943435 4374503 := bstep (se 1 (by rfl) ⟨3280877, by rfl⟩ : syracuseStep 4374503 = 6561755) B6561755
theorem B2916335 : Blo 1943435 2916335 := bstep (se 1 (by rfl) ⟨2187251, by rfl⟩ : syracuseStep 2916335 = 4374503) B4374503
theorem B1944223 : Blo 1943435 1944223 := bstep (se 1 (by rfl) ⟨1458167, by rfl⟩ : syracuseStep 1944223 = 2916335) B2916335
theorem B2916341 : Blo 1943435 2916341 := bbase (se 5 (by rfl) ⟨136703, by rfl⟩ : syracuseStep 2916341 = 273407) (by norm_num)
theorem B1944227 : Blo 1943435 1944227 := bstep (se 1 (by rfl) ⟨1458170, by rfl⟩ : syracuseStep 1944227 = 2916341) B2916341
theorem B7007141 : Blo 1943435 7007141 := bbase (se 4 (by rfl) ⟨656919, by rfl⟩ : syracuseStep 7007141 = 1313839) (by norm_num)
theorem B4671427 : Blo 1943435 4671427 := bstep (se 1 (by rfl) ⟨3503570, by rfl⟩ : syracuseStep 4671427 = 7007141) B7007141
theorem B6228569 : Blo 1943435 6228569 := bstep (se 2 (by rfl) ⟨2335713, by rfl⟩ : syracuseStep 6228569 = 4671427) B4671427
theorem B4152379 : Blo 1943435 4152379 := bstep (se 1 (by rfl) ⟨3114284, by rfl⟩ : syracuseStep 4152379 = 6228569) B6228569
theorem B5536505 : Blo 1943435 5536505 := bstep (se 2 (by rfl) ⟨2076189, by rfl⟩ : syracuseStep 5536505 = 4152379) B4152379
theorem B3691003 : Blo 1943435 3691003 := bstep (se 1 (by rfl) ⟨2768252, by rfl⟩ : syracuseStep 3691003 = 5536505) B5536505
theorem B4921337 : Blo 1943435 4921337 := bstep (se 2 (by rfl) ⟨1845501, by rfl⟩ : syracuseStep 4921337 = 3691003) B3691003
theorem B3280891 : Blo 1943435 3280891 := bstep (se 1 (by rfl) ⟨2460668, by rfl⟩ : syracuseStep 3280891 = 4921337) B4921337
theorem B4374521 : Blo 1943435 4374521 := bstep (se 2 (by rfl) ⟨1640445, by rfl⟩ : syracuseStep 4374521 = 3280891) B3280891
theorem B2916347 : Blo 1943435 2916347 := bstep (se 1 (by rfl) ⟨2187260, by rfl⟩ : syracuseStep 2916347 = 4374521) B4374521
theorem B1944231 : Blo 1943435 1944231 := bstep (se 1 (by rfl) ⟨1458173, by rfl⟩ : syracuseStep 1944231 = 2916347) B2916347
theorem B2187265 : Blo 1943435 2187265 := bbase (se 2 (by rfl) ⟨820224, by rfl⟩ : syracuseStep 2187265 = 1640449) (by norm_num)
theorem B2916353 : Blo 1943435 2916353 := bstep (se 2 (by rfl) ⟨1093632, by rfl⟩ : syracuseStep 2916353 = 2187265) B2187265
theorem B1944235 : Blo 1943435 1944235 := bstep (se 1 (by rfl) ⟨1458176, by rfl⟩ : syracuseStep 1944235 = 2916353) B2916353
theorem B4921357 : Blo 1943435 4921357 := bbase (se 3 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 4921357 = 1845509) (by norm_num)
theorem B6561809 : Blo 1943435 6561809 := bstep (se 2 (by rfl) ⟨2460678, by rfl⟩ : syracuseStep 6561809 = 4921357) B4921357
theorem B4374539 : Blo 1943435 4374539 := bstep (se 1 (by rfl) ⟨3280904, by rfl⟩ : syracuseStep 4374539 = 6561809) B6561809
theorem B2916359 : Blo 1943435 2916359 := bstep (se 1 (by rfl) ⟨2187269, by rfl⟩ : syracuseStep 2916359 = 4374539) B4374539
theorem B1944239 : Blo 1943435 1944239 := bstep (se 1 (by rfl) ⟨1458179, by rfl⟩ : syracuseStep 1944239 = 2916359) B2916359
theorem B2916365 : Blo 1943435 2916365 := bbase (se 3 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 2916365 = 1093637) (by norm_num)
theorem B1944243 : Blo 1943435 1944243 := bstep (se 1 (by rfl) ⟨1458182, by rfl⟩ : syracuseStep 1944243 = 2916365) B2916365
theorem B4374557 : Blo 1943435 4374557 := bbase (se 3 (by rfl) ⟨820229, by rfl⟩ : syracuseStep 4374557 = 1640459) (by norm_num)
theorem B2916371 : Blo 1943435 2916371 := bstep (se 1 (by rfl) ⟨2187278, by rfl⟩ : syracuseStep 2916371 = 4374557) B4374557
theorem B1944247 : Blo 1943435 1944247 := bstep (se 1 (by rfl) ⟨1458185, by rfl⟩ : syracuseStep 1944247 = 2916371) B2916371
theorem B3280925 : Blo 1943435 3280925 := bbase (se 3 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 3280925 = 1230347) (by norm_num)
theorem B2187283 : Blo 1943435 2187283 := bstep (se 1 (by rfl) ⟨1640462, by rfl⟩ : syracuseStep 2187283 = 3280925) B3280925
theorem B2916377 : Blo 1943435 2916377 := bstep (se 2 (by rfl) ⟨1093641, by rfl⟩ : syracuseStep 2916377 = 2187283) B2187283
theorem B1944251 : Blo 1943435 1944251 := bstep (se 1 (by rfl) ⟨1458188, by rfl⟩ : syracuseStep 1944251 = 2916377) B2916377
theorem B3078829 : Blo 1943435 3078829 := bbase (se 3 (by rfl) ⟨577280, by rfl⟩ : syracuseStep 3078829 = 1154561) (by norm_num)
theorem B16420421 : Blo 1943435 16420421 := bstep (se 4 (by rfl) ⟨1539414, by rfl⟩ : syracuseStep 16420421 = 3078829) B3078829
theorem B10946947 : Blo 1943435 10946947 := bstep (se 1 (by rfl) ⟨8210210, by rfl⟩ : syracuseStep 10946947 = 16420421) B16420421
theorem B14595929 : Blo 1943435 14595929 := bstep (se 2 (by rfl) ⟨5473473, by rfl⟩ : syracuseStep 14595929 = 10946947) B10946947
theorem B9730619 : Blo 1943435 9730619 := bstep (se 1 (by rfl) ⟨7297964, by rfl⟩ : syracuseStep 9730619 = 14595929) B14595929
theorem B6487079 : Blo 1943435 6487079 := bstep (se 1 (by rfl) ⟨4865309, by rfl⟩ : syracuseStep 6487079 = 9730619) B9730619
theorem B17298877 : Blo 1943435 17298877 := bstep (se 3 (by rfl) ⟨3243539, by rfl⟩ : syracuseStep 17298877 = 6487079) B6487079
theorem B23065169 : Blo 1943435 23065169 := bstep (se 2 (by rfl) ⟨8649438, by rfl⟩ : syracuseStep 23065169 = 17298877) B17298877
theorem B61507117 : Blo 1943435 61507117 := bstep (se 3 (by rfl) ⟨11532584, by rfl⟩ : syracuseStep 61507117 = 23065169) B23065169
theorem B328037957 : Blo 1943435 328037957 := bstep (se 4 (by rfl) ⟨30753558, by rfl⟩ : syracuseStep 328037957 = 61507117) B61507117
theorem B218691971 : Blo 1943435 218691971 := bstep (se 1 (by rfl) ⟨164018978, by rfl⟩ : syracuseStep 218691971 = 328037957) B328037957
theorem B145794647 : Blo 1943435 145794647 := bstep (se 1 (by rfl) ⟨109345985, by rfl⟩ : syracuseStep 145794647 = 218691971) B218691971
theorem B97196431 : Blo 1943435 97196431 := bstep (se 1 (by rfl) ⟨72897323, by rfl⟩ : syracuseStep 97196431 = 145794647) B145794647
theorem B129595241 : Blo 1943435 129595241 := bstep (se 2 (by rfl) ⟨48598215, by rfl⟩ : syracuseStep 129595241 = 97196431) B97196431
theorem B86396827 : Blo 1943435 86396827 := bstep (se 1 (by rfl) ⟨64797620, by rfl⟩ : syracuseStep 86396827 = 129595241) B129595241
theorem B115195769 : Blo 1943435 115195769 := bstep (se 2 (by rfl) ⟨43198413, by rfl⟩ : syracuseStep 115195769 = 86396827) B86396827
theorem B76797179 : Blo 1943435 76797179 := bstep (se 1 (by rfl) ⟨57597884, by rfl⟩ : syracuseStep 76797179 = 115195769) B115195769
theorem B51198119 : Blo 1943435 51198119 := bstep (se 1 (by rfl) ⟨38398589, by rfl⟩ : syracuseStep 51198119 = 76797179) B76797179
theorem B34132079 : Blo 1943435 34132079 := bstep (se 1 (by rfl) ⟨25599059, by rfl⟩ : syracuseStep 34132079 = 51198119) B51198119
theorem B22754719 : Blo 1943435 22754719 := bstep (se 1 (by rfl) ⟨17066039, by rfl⟩ : syracuseStep 22754719 = 34132079) B34132079
theorem B30339625 : Blo 1943435 30339625 := bstep (se 2 (by rfl) ⟨11377359, by rfl⟩ : syracuseStep 30339625 = 22754719) B22754719
theorem B40452833 : Blo 1943435 40452833 := bstep (se 2 (by rfl) ⟨15169812, by rfl⟩ : syracuseStep 40452833 = 30339625) B30339625
theorem B26968555 : Blo 1943435 26968555 := bstep (se 1 (by rfl) ⟨20226416, by rfl⟩ : syracuseStep 26968555 = 40452833) B40452833
theorem B143832293 : Blo 1943435 143832293 := bstep (se 4 (by rfl) ⟨13484277, by rfl⟩ : syracuseStep 143832293 = 26968555) B26968555
theorem B95888195 : Blo 1943435 95888195 := bstep (se 1 (by rfl) ⟨71916146, by rfl⟩ : syracuseStep 95888195 = 143832293) B143832293
theorem B63925463 : Blo 1943435 63925463 := bstep (se 1 (by rfl) ⟨47944097, by rfl⟩ : syracuseStep 63925463 = 95888195) B95888195
theorem B170467901 : Blo 1943435 170467901 := bstep (se 3 (by rfl) ⟨31962731, by rfl⟩ : syracuseStep 170467901 = 63925463) B63925463
theorem B113645267 : Blo 1943435 113645267 := bstep (se 1 (by rfl) ⟨85233950, by rfl⟩ : syracuseStep 113645267 = 170467901) B170467901
theorem B75763511 : Blo 1943435 75763511 := bstep (se 1 (by rfl) ⟨56822633, by rfl⟩ : syracuseStep 75763511 = 113645267) B113645267
theorem B50509007 : Blo 1943435 50509007 := bstep (se 1 (by rfl) ⟨37881755, by rfl⟩ : syracuseStep 50509007 = 75763511) B75763511
theorem B33672671 : Blo 1943435 33672671 := bstep (se 1 (by rfl) ⟨25254503, by rfl⟩ : syracuseStep 33672671 = 50509007) B50509007
theorem B22448447 : Blo 1943435 22448447 := bstep (se 1 (by rfl) ⟨16836335, by rfl⟩ : syracuseStep 22448447 = 33672671) B33672671
theorem B14965631 : Blo 1943435 14965631 := bstep (se 1 (by rfl) ⟨11224223, by rfl⟩ : syracuseStep 14965631 = 22448447) B22448447
theorem B9977087 : Blo 1943435 9977087 := bstep (se 1 (by rfl) ⟨7482815, by rfl⟩ : syracuseStep 9977087 = 14965631) B14965631
theorem B6651391 : Blo 1943435 6651391 := bstep (se 1 (by rfl) ⟨4988543, by rfl⟩ : syracuseStep 6651391 = 9977087) B9977087
theorem B8868521 : Blo 1943435 8868521 := bstep (se 2 (by rfl) ⟨3325695, by rfl⟩ : syracuseStep 8868521 = 6651391) B6651391
theorem B5912347 : Blo 1943435 5912347 := bstep (se 1 (by rfl) ⟨4434260, by rfl⟩ : syracuseStep 5912347 = 8868521) B8868521
theorem B7883129 : Blo 1943435 7883129 := bstep (se 2 (by rfl) ⟨2956173, by rfl⟩ : syracuseStep 7883129 = 5912347) B5912347
theorem B21021677 : Blo 1943435 21021677 := bstep (se 3 (by rfl) ⟨3941564, by rfl⟩ : syracuseStep 21021677 = 7883129) B7883129
theorem B14014451 : Blo 1943435 14014451 := bstep (se 1 (by rfl) ⟨10510838, by rfl⟩ : syracuseStep 14014451 = 21021677) B21021677
theorem B9342967 : Blo 1943435 9342967 := bstep (se 1 (by rfl) ⟨7007225, by rfl⟩ : syracuseStep 9342967 = 14014451) B14014451
theorem B12457289 : Blo 1943435 12457289 := bstep (se 2 (by rfl) ⟨4671483, by rfl⟩ : syracuseStep 12457289 = 9342967) B9342967
theorem B8304859 : Blo 1943435 8304859 := bstep (se 1 (by rfl) ⟨6228644, by rfl⟩ : syracuseStep 8304859 = 12457289) B12457289
theorem B11073145 : Blo 1943435 11073145 := bstep (se 2 (by rfl) ⟨4152429, by rfl⟩ : syracuseStep 11073145 = 8304859) B8304859
theorem B14764193 : Blo 1943435 14764193 := bstep (se 2 (by rfl) ⟨5536572, by rfl⟩ : syracuseStep 14764193 = 11073145) B11073145
theorem B9842795 : Blo 1943435 9842795 := bstep (se 1 (by rfl) ⟨7382096, by rfl⟩ : syracuseStep 9842795 = 14764193) B14764193
theorem B6561863 : Blo 1943435 6561863 := bstep (se 1 (by rfl) ⟨4921397, by rfl⟩ : syracuseStep 6561863 = 9842795) B9842795
theorem B4374575 : Blo 1943435 4374575 := bstep (se 1 (by rfl) ⟨3280931, by rfl⟩ : syracuseStep 4374575 = 6561863) B6561863
theorem B2916383 : Blo 1943435 2916383 := bstep (se 1 (by rfl) ⟨2187287, by rfl⟩ : syracuseStep 2916383 = 4374575) B4374575
theorem B1944255 : Blo 1943435 1944255 := bstep (se 1 (by rfl) ⟨1458191, by rfl⟩ : syracuseStep 1944255 = 2916383) B2916383
theorem B2916389 : Blo 1943435 2916389 := bbase (se 4 (by rfl) ⟨273411, by rfl⟩ : syracuseStep 2916389 = 546823) (by norm_num)
theorem B1944259 : Blo 1943435 1944259 := bstep (se 1 (by rfl) ⟨1458194, by rfl⟩ : syracuseStep 1944259 = 2916389) B2916389
theorem B2460709 : Blo 1943435 2460709 := bbase (se 4 (by rfl) ⟨230691, by rfl⟩ : syracuseStep 2460709 = 461383) (by norm_num)
theorem B3280945 : Blo 1943435 3280945 := bstep (se 2 (by rfl) ⟨1230354, by rfl⟩ : syracuseStep 3280945 = 2460709) B2460709
theorem B4374593 : Blo 1943435 4374593 := bstep (se 2 (by rfl) ⟨1640472, by rfl⟩ : syracuseStep 4374593 = 3280945) B3280945
theorem B2916395 : Blo 1943435 2916395 := bstep (se 1 (by rfl) ⟨2187296, by rfl⟩ : syracuseStep 2916395 = 4374593) B4374593
theorem B1944263 : Blo 1943435 1944263 := bstep (se 1 (by rfl) ⟨1458197, by rfl⟩ : syracuseStep 1944263 = 2916395) B2916395
theorem B2187301 : Blo 1943435 2187301 := bbase (se 4 (by rfl) ⟨205059, by rfl⟩ : syracuseStep 2187301 = 410119) (by norm_num)
theorem B2916401 : Blo 1943435 2916401 := bstep (se 2 (by rfl) ⟨1093650, by rfl⟩ : syracuseStep 2916401 = 2187301) B2187301
theorem B1944267 : Blo 1943435 1944267 := bstep (se 1 (by rfl) ⟨1458200, by rfl⟩ : syracuseStep 1944267 = 2916401) B2916401
theorem B7007285 : Blo 1943435 7007285 := bbase (se 5 (by rfl) ⟨328466, by rfl⟩ : syracuseStep 7007285 = 656933) (by norm_num)
theorem B4671523 : Blo 1943435 4671523 := bstep (se 1 (by rfl) ⟨3503642, by rfl⟩ : syracuseStep 4671523 = 7007285) B7007285
theorem B6228697 : Blo 1943435 6228697 := bstep (se 2 (by rfl) ⟨2335761, by rfl⟩ : syracuseStep 6228697 = 4671523) B4671523
theorem B8304929 : Blo 1943435 8304929 := bstep (se 2 (by rfl) ⟨3114348, by rfl⟩ : syracuseStep 8304929 = 6228697) B6228697
theorem B5536619 : Blo 1943435 5536619 := bstep (se 1 (by rfl) ⟨4152464, by rfl⟩ : syracuseStep 5536619 = 8304929) B8304929
theorem B3691079 : Blo 1943435 3691079 := bstep (se 1 (by rfl) ⟨2768309, by rfl⟩ : syracuseStep 3691079 = 5536619) B5536619
theorem B2460719 : Blo 1943435 2460719 := bstep (se 1 (by rfl) ⟨1845539, by rfl⟩ : syracuseStep 2460719 = 3691079) B3691079
theorem B6561917 : Blo 1943435 6561917 := bstep (se 3 (by rfl) ⟨1230359, by rfl⟩ : syracuseStep 6561917 = 2460719) B2460719
theorem B4374611 : Blo 1943435 4374611 := bstep (se 1 (by rfl) ⟨3280958, by rfl⟩ : syracuseStep 4374611 = 6561917) B6561917
theorem B2916407 : Blo 1943435 2916407 := bstep (se 1 (by rfl) ⟨2187305, by rfl⟩ : syracuseStep 2916407 = 4374611) B4374611
theorem B1944271 : Blo 1943435 1944271 := bstep (se 1 (by rfl) ⟨1458203, by rfl⟩ : syracuseStep 1944271 = 2916407) B2916407
theorem B2916413 : Blo 1943435 2916413 := bbase (se 3 (by rfl) ⟨546827, by rfl⟩ : syracuseStep 2916413 = 1093655) (by norm_num)
theorem B1944275 : Blo 1943435 1944275 := bstep (se 1 (by rfl) ⟨1458206, by rfl⟩ : syracuseStep 1944275 = 2916413) B2916413
theorem B4374629 : Blo 1943435 4374629 := bbase (se 4 (by rfl) ⟨410121, by rfl⟩ : syracuseStep 4374629 = 820243) (by norm_num)
theorem B2916419 : Blo 1943435 2916419 := bstep (se 1 (by rfl) ⟨2187314, by rfl⟩ : syracuseStep 2916419 = 4374629) B4374629
theorem B1944279 : Blo 1943435 1944279 := bstep (se 1 (by rfl) ⟨1458209, by rfl⟩ : syracuseStep 1944279 = 2916419) B2916419
theorem B4921469 : Blo 1943435 4921469 := bbase (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) (by norm_num)
theorem B3280979 : Blo 1943435 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B2187319 : Blo 1943435 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B2916425 : Blo 1943435 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B1944283 : Blo 1943435 1944283 := bstep (se 1 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 1944283 = 2916425) B2916425
theorem B3691109 : Blo 1943435 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B9842957 : Blo 1943435 9842957 := bstep (se 3 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 9842957 = 3691109) B3691109
theorem B6561971 : Blo 1943435 6561971 := bstep (se 1 (by rfl) ⟨4921478, by rfl⟩ : syracuseStep 6561971 = 9842957) B9842957
theorem B4374647 : Blo 1943435 4374647 := bstep (se 1 (by rfl) ⟨3280985, by rfl⟩ : syracuseStep 4374647 = 6561971) B6561971
theorem B2916431 : Blo 1943435 2916431 := bstep (se 1 (by rfl) ⟨2187323, by rfl⟩ : syracuseStep 2916431 = 4374647) B4374647
theorem B1944287 : Blo 1943435 1944287 := bstep (se 1 (by rfl) ⟨1458215, by rfl⟩ : syracuseStep 1944287 = 2916431) B2916431
theorem B2916437 : Blo 1943435 2916437 := bbase (se 8 (by rfl) ⟨17088, by rfl⟩ : syracuseStep 2916437 = 34177) (by norm_num)
theorem B1944291 : Blo 1943435 1944291 := bstep (se 1 (by rfl) ⟨1458218, by rfl⟩ : syracuseStep 1944291 = 2916437) B2916437
theorem B14014741 : Blo 1943435 14014741 := bbase (se 6 (by rfl) ⟨328470, by rfl⟩ : syracuseStep 14014741 = 656941) (by norm_num)
theorem B18686321 : Blo 1943435 18686321 := bstep (se 2 (by rfl) ⟨7007370, by rfl⟩ : syracuseStep 18686321 = 14014741) B14014741
theorem B12457547 : Blo 1943435 12457547 := bstep (se 1 (by rfl) ⟨9343160, by rfl⟩ : syracuseStep 12457547 = 18686321) B18686321
theorem B8305031 : Blo 1943435 8305031 := bstep (se 1 (by rfl) ⟨6228773, by rfl⟩ : syracuseStep 8305031 = 12457547) B12457547
theorem B5536687 : Blo 1943435 5536687 := bstep (se 1 (by rfl) ⟨4152515, by rfl⟩ : syracuseStep 5536687 = 8305031) B8305031
theorem B7382249 : Blo 1943435 7382249 := bstep (se 2 (by rfl) ⟨2768343, by rfl⟩ : syracuseStep 7382249 = 5536687) B5536687
theorem B4921499 : Blo 1943435 4921499 := bstep (se 1 (by rfl) ⟨3691124, by rfl⟩ : syracuseStep 4921499 = 7382249) B7382249
theorem B3280999 : Blo 1943435 3280999 := bstep (se 1 (by rfl) ⟨2460749, by rfl⟩ : syracuseStep 3280999 = 4921499) B4921499
theorem B4374665 : Blo 1943435 4374665 := bstep (se 2 (by rfl) ⟨1640499, by rfl⟩ : syracuseStep 4374665 = 3280999) B3280999
theorem B2916443 : Blo 1943435 2916443 := bstep (se 1 (by rfl) ⟨2187332, by rfl⟩ : syracuseStep 2916443 = 4374665) B4374665
theorem B1944295 : Blo 1943435 1944295 := bstep (se 1 (by rfl) ⟨1458221, by rfl⟩ : syracuseStep 1944295 = 2916443) B2916443
theorem B2187337 : Blo 1943435 2187337 := bbase (se 2 (by rfl) ⟨820251, by rfl⟩ : syracuseStep 2187337 = 1640503) (by norm_num)
theorem B2916449 : Blo 1943435 2916449 := bstep (se 2 (by rfl) ⟨1093668, by rfl⟩ : syracuseStep 2916449 = 2187337) B2187337
theorem B1944299 : Blo 1943435 1944299 := bstep (se 1 (by rfl) ⟨1458224, by rfl⟩ : syracuseStep 1944299 = 2916449) B2916449
theorem B2528365 : Blo 1943435 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B3371153 : Blo 1943435 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B8989741 : Blo 1943435 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B11986321 : Blo 1943435 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B15981761 : Blo 1943435 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B10654507 : Blo 1943435 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B56824037 : Blo 1943435 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B37882691 : Blo 1943435 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B25255127 : Blo 1943435 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B16836751 : Blo 1943435 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B22449001 : Blo 1943435 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B29932001 : Blo 1943435 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B19954667 : Blo 1943435 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B13303111 : Blo 1943435 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B17737481 : Blo 1943435 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B11824987 : Blo 1943435 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B15766649 : Blo 1943435 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B10511099 : Blo 1943435 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B7007399 : Blo 1943435 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B4671599 : Blo 1943435 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B12457597 : Blo 1943435 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B16610129 : Blo 1943435 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B11073419 : Blo 1943435 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B7382279 : Blo 1943435 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B4921519 : Blo 1943435 4921519 := bstep (se 1 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 4921519 = 7382279) B7382279
theorem B6562025 : Blo 1943435 6562025 := bstep (se 2 (by rfl) ⟨2460759, by rfl⟩ : syracuseStep 6562025 = 4921519) B4921519
theorem B4374683 : Blo 1943435 4374683 := bstep (se 1 (by rfl) ⟨3281012, by rfl⟩ : syracuseStep 4374683 = 6562025) B6562025
theorem B2916455 : Blo 1943435 2916455 := bstep (se 1 (by rfl) ⟨2187341, by rfl⟩ : syracuseStep 2916455 = 4374683) B4374683
theorem B1944303 : Blo 1943435 1944303 := bstep (se 1 (by rfl) ⟨1458227, by rfl⟩ : syracuseStep 1944303 = 2916455) B2916455
theorem B2916461 : Blo 1943435 2916461 := bbase (se 3 (by rfl) ⟨546836, by rfl⟩ : syracuseStep 2916461 = 1093673) (by norm_num)
theorem B1944307 : Blo 1943435 1944307 := bstep (se 1 (by rfl) ⟨1458230, by rfl⟩ : syracuseStep 1944307 = 2916461) B2916461
theorem B4374701 : Blo 1943435 4374701 := bbase (se 3 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 4374701 = 1640513) (by norm_num)
theorem B2916467 : Blo 1943435 2916467 := bstep (se 1 (by rfl) ⟨2187350, by rfl⟩ : syracuseStep 2916467 = 4374701) B4374701
theorem B1944311 : Blo 1943435 1944311 := bstep (se 1 (by rfl) ⟨1458233, by rfl⟩ : syracuseStep 1944311 = 2916467) B2916467
theorem B3599981 : Blo 1943435 3599981 := bbase (se 3 (by rfl) ⟨674996, by rfl⟩ : syracuseStep 3599981 = 1349993) (by norm_num)
theorem B2399987 : Blo 1943435 2399987 := bstep (se 1 (by rfl) ⟨1799990, by rfl⟩ : syracuseStep 2399987 = 3599981) B3599981
theorem B6399965 : Blo 1943435 6399965 := bstep (se 3 (by rfl) ⟨1199993, by rfl⟩ : syracuseStep 6399965 = 2399987) B2399987
theorem B4266643 : Blo 1943435 4266643 := bstep (se 1 (by rfl) ⟨3199982, by rfl⟩ : syracuseStep 4266643 = 6399965) B6399965
theorem B5688857 : Blo 1943435 5688857 := bstep (se 2 (by rfl) ⟨2133321, by rfl⟩ : syracuseStep 5688857 = 4266643) B4266643
theorem B15170285 : Blo 1943435 15170285 := bstep (se 3 (by rfl) ⟨2844428, by rfl⟩ : syracuseStep 15170285 = 5688857) B5688857
theorem B40454093 : Blo 1943435 40454093 := bstep (se 3 (by rfl) ⟨7585142, by rfl⟩ : syracuseStep 40454093 = 15170285) B15170285
theorem B107877581 : Blo 1943435 107877581 := bstep (se 3 (by rfl) ⟨20227046, by rfl⟩ : syracuseStep 107877581 = 40454093) B40454093
theorem B71918387 : Blo 1943435 71918387 := bstep (se 1 (by rfl) ⟨53938790, by rfl⟩ : syracuseStep 71918387 = 107877581) B107877581
theorem B47945591 : Blo 1943435 47945591 := bstep (se 1 (by rfl) ⟨35959193, by rfl⟩ : syracuseStep 47945591 = 71918387) B71918387
theorem B31963727 : Blo 1943435 31963727 := bstep (se 1 (by rfl) ⟨23972795, by rfl⟩ : syracuseStep 31963727 = 47945591) B47945591
theorem B21309151 : Blo 1943435 21309151 := bstep (se 1 (by rfl) ⟨15981863, by rfl⟩ : syracuseStep 21309151 = 31963727) B31963727
theorem B28412201 : Blo 1943435 28412201 := bstep (se 2 (by rfl) ⟨10654575, by rfl⟩ : syracuseStep 28412201 = 21309151) B21309151
theorem B18941467 : Blo 1943435 18941467 := bstep (se 1 (by rfl) ⟨14206100, by rfl⟩ : syracuseStep 18941467 = 28412201) B28412201
theorem B25255289 : Blo 1943435 25255289 := bstep (se 2 (by rfl) ⟨9470733, by rfl⟩ : syracuseStep 25255289 = 18941467) B18941467
theorem B16836859 : Blo 1943435 16836859 := bstep (se 1 (by rfl) ⟨12627644, by rfl⟩ : syracuseStep 16836859 = 25255289) B25255289
theorem B22449145 : Blo 1943435 22449145 := bstep (se 2 (by rfl) ⟨8418429, by rfl⟩ : syracuseStep 22449145 = 16836859) B16836859
theorem B29932193 : Blo 1943435 29932193 := bstep (se 2 (by rfl) ⟨11224572, by rfl⟩ : syracuseStep 29932193 = 22449145) B22449145
theorem B79819181 : Blo 1943435 79819181 := bstep (se 3 (by rfl) ⟨14966096, by rfl⟩ : syracuseStep 79819181 = 29932193) B29932193
theorem B53212787 : Blo 1943435 53212787 := bstep (se 1 (by rfl) ⟨39909590, by rfl⟩ : syracuseStep 53212787 = 79819181) B79819181
theorem B35475191 : Blo 1943435 35475191 := bstep (se 1 (by rfl) ⟨26606393, by rfl⟩ : syracuseStep 35475191 = 53212787) B53212787
theorem B23650127 : Blo 1943435 23650127 := bstep (se 1 (by rfl) ⟨17737595, by rfl⟩ : syracuseStep 23650127 = 35475191) B35475191
theorem B15766751 : Blo 1943435 15766751 := bstep (se 1 (by rfl) ⟨11825063, by rfl⟩ : syracuseStep 15766751 = 23650127) B23650127
theorem B10511167 : Blo 1943435 10511167 := bstep (se 1 (by rfl) ⟨7883375, by rfl⟩ : syracuseStep 10511167 = 15766751) B15766751
theorem B14014889 : Blo 1943435 14014889 := bstep (se 2 (by rfl) ⟨5255583, by rfl⟩ : syracuseStep 14014889 = 10511167) B10511167
theorem B9343259 : Blo 1943435 9343259 := bstep (se 1 (by rfl) ⟨7007444, by rfl⟩ : syracuseStep 9343259 = 14014889) B14014889
theorem B6228839 : Blo 1943435 6228839 := bstep (se 1 (by rfl) ⟨4671629, by rfl⟩ : syracuseStep 6228839 = 9343259) B9343259
theorem B4152559 : Blo 1943435 4152559 := bstep (se 1 (by rfl) ⟨3114419, by rfl⟩ : syracuseStep 4152559 = 6228839) B6228839
theorem B5536745 : Blo 1943435 5536745 := bstep (se 2 (by rfl) ⟨2076279, by rfl⟩ : syracuseStep 5536745 = 4152559) B4152559
theorem B3691163 : Blo 1943435 3691163 := bstep (se 1 (by rfl) ⟨2768372, by rfl⟩ : syracuseStep 3691163 = 5536745) B5536745
theorem B2460775 : Blo 1943435 2460775 := bstep (se 1 (by rfl) ⟨1845581, by rfl⟩ : syracuseStep 2460775 = 3691163) B3691163
theorem B3281033 : Blo 1943435 3281033 := bstep (se 2 (by rfl) ⟨1230387, by rfl⟩ : syracuseStep 3281033 = 2460775) B2460775
theorem B2187355 : Blo 1943435 2187355 := bstep (se 1 (by rfl) ⟨1640516, by rfl⟩ : syracuseStep 2187355 = 3281033) B3281033
theorem B2916473 : Blo 1943435 2916473 := bstep (se 2 (by rfl) ⟨1093677, by rfl⟩ : syracuseStep 2916473 = 2187355) B2187355
theorem B1944315 : Blo 1943435 1944315 := bstep (se 1 (by rfl) ⟨1458236, by rfl⟩ : syracuseStep 1944315 = 2916473) B2916473
theorem B4671637 : Blo 1943435 4671637 := bbase (se 6 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 4671637 = 218983) (by norm_num)
theorem B24915397 : Blo 1943435 24915397 := bstep (se 4 (by rfl) ⟨2335818, by rfl⟩ : syracuseStep 24915397 = 4671637) B4671637
theorem B33220529 : Blo 1943435 33220529 := bstep (se 2 (by rfl) ⟨12457698, by rfl⟩ : syracuseStep 33220529 = 24915397) B24915397
theorem B22147019 : Blo 1943435 22147019 := bstep (se 1 (by rfl) ⟨16610264, by rfl⟩ : syracuseStep 22147019 = 33220529) B33220529
theorem B14764679 : Blo 1943435 14764679 := bstep (se 1 (by rfl) ⟨11073509, by rfl⟩ : syracuseStep 14764679 = 22147019) B22147019
theorem B9843119 : Blo 1943435 9843119 := bstep (se 1 (by rfl) ⟨7382339, by rfl⟩ : syracuseStep 9843119 = 14764679) B14764679
theorem B6562079 : Blo 1943435 6562079 := bstep (se 1 (by rfl) ⟨4921559, by rfl⟩ : syracuseStep 6562079 = 9843119) B9843119
theorem B4374719 : Blo 1943435 4374719 := bstep (se 1 (by rfl) ⟨3281039, by rfl⟩ : syracuseStep 4374719 = 6562079) B6562079
theorem B2916479 : Blo 1943435 2916479 := bstep (se 1 (by rfl) ⟨2187359, by rfl⟩ : syracuseStep 2916479 = 4374719) B4374719
theorem B1944319 : Blo 1943435 1944319 := bstep (se 1 (by rfl) ⟨1458239, by rfl⟩ : syracuseStep 1944319 = 2916479) B2916479
theorem B2916485 : Blo 1943435 2916485 := bbase (se 4 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 2916485 = 546841) (by norm_num)
theorem B1944323 : Blo 1943435 1944323 := bstep (se 1 (by rfl) ⟨1458242, by rfl⟩ : syracuseStep 1944323 = 2916485) B2916485
theorem B3281053 : Blo 1943435 3281053 := bbase (se 3 (by rfl) ⟨615197, by rfl⟩ : syracuseStep 3281053 = 1230395) (by norm_num)
theorem B4374737 : Blo 1943435 4374737 := bstep (se 2 (by rfl) ⟨1640526, by rfl⟩ : syracuseStep 4374737 = 3281053) B3281053
theorem B2916491 : Blo 1943435 2916491 := bstep (se 1 (by rfl) ⟨2187368, by rfl⟩ : syracuseStep 2916491 = 4374737) B4374737
theorem B1944327 : Blo 1943435 1944327 := bstep (se 1 (by rfl) ⟨1458245, by rfl⟩ : syracuseStep 1944327 = 2916491) B2916491
theorem B2187373 : Blo 1943435 2187373 := bbase (se 3 (by rfl) ⟨410132, by rfl⟩ : syracuseStep 2187373 = 820265) (by norm_num)
theorem B2916497 : Blo 1943435 2916497 := bstep (se 2 (by rfl) ⟨1093686, by rfl⟩ : syracuseStep 2916497 = 2187373) B2187373
theorem B1944331 : Blo 1943435 1944331 := bstep (se 1 (by rfl) ⟨1458248, by rfl⟩ : syracuseStep 1944331 = 2916497) B2916497
theorem B6562133 : Blo 1943435 6562133 := bbase (se 10 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 6562133 = 19225) (by norm_num)
theorem B4374755 : Blo 1943435 4374755 := bstep (se 1 (by rfl) ⟨3281066, by rfl⟩ : syracuseStep 4374755 = 6562133) B6562133
theorem B2916503 : Blo 1943435 2916503 := bstep (se 1 (by rfl) ⟨2187377, by rfl⟩ : syracuseStep 2916503 = 4374755) B4374755
theorem B1944335 : Blo 1943435 1944335 := bstep (se 1 (by rfl) ⟨1458251, by rfl⟩ : syracuseStep 1944335 = 2916503) B2916503
theorem B2916509 : Blo 1943435 2916509 := bbase (se 3 (by rfl) ⟨546845, by rfl⟩ : syracuseStep 2916509 = 1093691) (by norm_num)
theorem B1944339 : Blo 1943435 1944339 := bstep (se 1 (by rfl) ⟨1458254, by rfl⟩ : syracuseStep 1944339 = 2916509) B2916509
theorem B4374773 : Blo 1943435 4374773 := bbase (se 5 (by rfl) ⟨205067, by rfl⟩ : syracuseStep 4374773 = 410135) (by norm_num)
theorem B2916515 : Blo 1943435 2916515 := bstep (se 1 (by rfl) ⟨2187386, by rfl⟩ : syracuseStep 2916515 = 4374773) B4374773
theorem B1944343 : Blo 1943435 1944343 := bstep (se 1 (by rfl) ⟨1458257, by rfl⟩ : syracuseStep 1944343 = 2916515) B2916515
theorem B5255669 : Blo 1943435 5255669 := bbase (se 5 (by rfl) ⟨246359, by rfl⟩ : syracuseStep 5255669 = 492719) (by norm_num)
theorem B3503779 : Blo 1943435 3503779 := bstep (se 1 (by rfl) ⟨2627834, by rfl⟩ : syracuseStep 3503779 = 5255669) B5255669
theorem B18686821 : Blo 1943435 18686821 := bstep (se 4 (by rfl) ⟨1751889, by rfl⟩ : syracuseStep 18686821 = 3503779) B3503779
theorem B24915761 : Blo 1943435 24915761 := bstep (se 2 (by rfl) ⟨9343410, by rfl⟩ : syracuseStep 24915761 = 18686821) B18686821
theorem B16610507 : Blo 1943435 16610507 := bstep (se 1 (by rfl) ⟨12457880, by rfl⟩ : syracuseStep 16610507 = 24915761) B24915761
theorem B11073671 : Blo 1943435 11073671 := bstep (se 1 (by rfl) ⟨8305253, by rfl⟩ : syracuseStep 11073671 = 16610507) B16610507
theorem B7382447 : Blo 1943435 7382447 := bstep (se 1 (by rfl) ⟨5536835, by rfl⟩ : syracuseStep 7382447 = 11073671) B11073671
theorem B4921631 : Blo 1943435 4921631 := bstep (se 1 (by rfl) ⟨3691223, by rfl⟩ : syracuseStep 4921631 = 7382447) B7382447
theorem B3281087 : Blo 1943435 3281087 := bstep (se 1 (by rfl) ⟨2460815, by rfl⟩ : syracuseStep 3281087 = 4921631) B4921631
theorem B2187391 : Blo 1943435 2187391 := bstep (se 1 (by rfl) ⟨1640543, by rfl⟩ : syracuseStep 2187391 = 3281087) B3281087
theorem B2916521 : Blo 1943435 2916521 := bstep (se 2 (by rfl) ⟨1093695, by rfl⟩ : syracuseStep 2916521 = 2187391) B2187391
theorem B1944347 : Blo 1943435 1944347 := bstep (se 1 (by rfl) ⟨1458260, by rfl⟩ : syracuseStep 1944347 = 2916521) B2916521
theorem B7007573 : Blo 1943435 7007573 := bbase (se 11 (by rfl) ⟨5132, by rfl⟩ : syracuseStep 7007573 = 10265) (by norm_num)
theorem B4671715 : Blo 1943435 4671715 := bstep (se 1 (by rfl) ⟨3503786, by rfl⟩ : syracuseStep 4671715 = 7007573) B7007573
theorem B6228953 : Blo 1943435 6228953 := bstep (se 2 (by rfl) ⟨2335857, by rfl⟩ : syracuseStep 6228953 = 4671715) B4671715
theorem B4152635 : Blo 1943435 4152635 := bstep (se 1 (by rfl) ⟨3114476, by rfl⟩ : syracuseStep 4152635 = 6228953) B6228953
theorem B2768423 : Blo 1943435 2768423 := bstep (se 1 (by rfl) ⟨2076317, by rfl⟩ : syracuseStep 2768423 = 4152635) B4152635
theorem B7382461 : Blo 1943435 7382461 := bstep (se 3 (by rfl) ⟨1384211, by rfl⟩ : syracuseStep 7382461 = 2768423) B2768423
theorem B9843281 : Blo 1943435 9843281 := bstep (se 2 (by rfl) ⟨3691230, by rfl⟩ : syracuseStep 9843281 = 7382461) B7382461
theorem B6562187 : Blo 1943435 6562187 := bstep (se 1 (by rfl) ⟨4921640, by rfl⟩ : syracuseStep 6562187 = 9843281) B9843281
theorem B4374791 : Blo 1943435 4374791 := bstep (se 1 (by rfl) ⟨3281093, by rfl⟩ : syracuseStep 4374791 = 6562187) B6562187
theorem B2916527 : Blo 1943435 2916527 := bstep (se 1 (by rfl) ⟨2187395, by rfl⟩ : syracuseStep 2916527 = 4374791) B4374791
theorem B1944351 : Blo 1943435 1944351 := bstep (se 1 (by rfl) ⟨1458263, by rfl⟩ : syracuseStep 1944351 = 2916527) B2916527
theorem B2916533 : Blo 1943435 2916533 := bbase (se 5 (by rfl) ⟨136712, by rfl⟩ : syracuseStep 2916533 = 273425) (by norm_num)
theorem B1944355 : Blo 1943435 1944355 := bstep (se 1 (by rfl) ⟨1458266, by rfl⟩ : syracuseStep 1944355 = 2916533) B2916533
theorem B4921661 : Blo 1943435 4921661 := bbase (se 3 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 4921661 = 1845623) (by norm_num)
theorem B3281107 : Blo 1943435 3281107 := bstep (se 1 (by rfl) ⟨2460830, by rfl⟩ : syracuseStep 3281107 = 4921661) B4921661
theorem B4374809 : Blo 1943435 4374809 := bstep (se 2 (by rfl) ⟨1640553, by rfl⟩ : syracuseStep 4374809 = 3281107) B3281107
theorem B2916539 : Blo 1943435 2916539 := bstep (se 1 (by rfl) ⟨2187404, by rfl⟩ : syracuseStep 2916539 = 4374809) B4374809
theorem B1944359 : Blo 1943435 1944359 := bstep (se 1 (by rfl) ⟨1458269, by rfl⟩ : syracuseStep 1944359 = 2916539) B2916539
theorem B2187409 : Blo 1943435 2187409 := bbase (se 2 (by rfl) ⟨820278, by rfl⟩ : syracuseStep 2187409 = 1640557) (by norm_num)
theorem B2916545 : Blo 1943435 2916545 := bstep (se 2 (by rfl) ⟨1093704, by rfl⟩ : syracuseStep 2916545 = 2187409) B2187409
theorem B1944363 : Blo 1943435 1944363 := bstep (se 1 (by rfl) ⟨1458272, by rfl⟩ : syracuseStep 1944363 = 2916545) B2916545
theorem B3691261 : Blo 1943435 3691261 := bbase (se 3 (by rfl) ⟨692111, by rfl⟩ : syracuseStep 3691261 = 1384223) (by norm_num)
theorem B4921681 : Blo 1943435 4921681 := bstep (se 2 (by rfl) ⟨1845630, by rfl⟩ : syracuseStep 4921681 = 3691261) B3691261
theorem B6562241 : Blo 1943435 6562241 := bstep (se 2 (by rfl) ⟨2460840, by rfl⟩ : syracuseStep 6562241 = 4921681) B4921681
theorem B4374827 : Blo 1943435 4374827 := bstep (se 1 (by rfl) ⟨3281120, by rfl⟩ : syracuseStep 4374827 = 6562241) B6562241
theorem B2916551 : Blo 1943435 2916551 := bstep (se 1 (by rfl) ⟨2187413, by rfl⟩ : syracuseStep 2916551 = 4374827) B4374827
theorem B1944367 : Blo 1943435 1944367 := bstep (se 1 (by rfl) ⟨1458275, by rfl⟩ : syracuseStep 1944367 = 2916551) B2916551
theorem B2916557 : Blo 1943435 2916557 := bbase (se 3 (by rfl) ⟨546854, by rfl⟩ : syracuseStep 2916557 = 1093709) (by norm_num)
theorem B1944371 : Blo 1943435 1944371 := bstep (se 1 (by rfl) ⟨1458278, by rfl⟩ : syracuseStep 1944371 = 2916557) B2916557
theorem B4374845 : Blo 1943435 4374845 := bbase (se 3 (by rfl) ⟨820283, by rfl⟩ : syracuseStep 4374845 = 1640567) (by norm_num)
theorem B2916563 : Blo 1943435 2916563 := bstep (se 1 (by rfl) ⟨2187422, by rfl⟩ : syracuseStep 2916563 = 4374845) B4374845
theorem B1944375 : Blo 1943435 1944375 := bstep (se 1 (by rfl) ⟨1458281, by rfl⟩ : syracuseStep 1944375 = 2916563) B2916563
theorem B3281141 : Blo 1943435 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B2187427 : Blo 1943435 2187427 := bstep (se 1 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 2187427 = 3281141) B3281141
theorem B2916569 : Blo 1943435 2916569 := bstep (se 2 (by rfl) ⟨1093713, by rfl⟩ : syracuseStep 2916569 = 2187427) B2187427
theorem B1944379 : Blo 1943435 1944379 := bstep (se 1 (by rfl) ⟨1458284, by rfl⟩ : syracuseStep 1944379 = 2916569) B2916569
theorem B6651829 : Blo 1943435 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B8869105 : Blo 1943435 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B47301893 : Blo 1943435 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B31534595 : Blo 1943435 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B21023063 : Blo 1943435 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B14015375 : Blo 1943435 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B9343583 : Blo 1943435 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B6229055 : Blo 1943435 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B4152703 : Blo 1943435 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B5536937 : Blo 1943435 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B14765165 : Blo 1943435 14765165 := bstep (se 3 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 14765165 = 5536937) B5536937
theorem B9843443 : Blo 1943435 9843443 := bstep (se 1 (by rfl) ⟨7382582, by rfl⟩ : syracuseStep 9843443 = 14765165) B14765165
theorem B6562295 : Blo 1943435 6562295 := bstep (se 1 (by rfl) ⟨4921721, by rfl⟩ : syracuseStep 6562295 = 9843443) B9843443
theorem B4374863 : Blo 1943435 4374863 := bstep (se 1 (by rfl) ⟨3281147, by rfl⟩ : syracuseStep 4374863 = 6562295) B6562295
theorem B2916575 : Blo 1943435 2916575 := bstep (se 1 (by rfl) ⟨2187431, by rfl⟩ : syracuseStep 2916575 = 4374863) B4374863
theorem B1944383 : Blo 1943435 1944383 := bstep (se 1 (by rfl) ⟨1458287, by rfl⟩ : syracuseStep 1944383 = 2916575) B2916575
theorem B2916581 : Blo 1943435 2916581 := bbase (se 4 (by rfl) ⟨273429, by rfl⟩ : syracuseStep 2916581 = 546859) (by norm_num)
theorem B1944387 : Blo 1943435 1944387 := bstep (se 1 (by rfl) ⟨1458290, by rfl⟩ : syracuseStep 1944387 = 2916581) B2916581
theorem B3114541 : Blo 1943435 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B4152721 : Blo 1943435 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B5536961 : Blo 1943435 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B3691307 : Blo 1943435 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B2460871 : Blo 1943435 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B3281161 : Blo 1943435 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B4374881 : Blo 1943435 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B2916587 : Blo 1943435 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B1944391 : Blo 1943435 1944391 := bstep (se 1 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 1944391 = 2916587) B2916587
theorem B2187445 : Blo 1943435 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B2916593 : Blo 1943435 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B1944395 : Blo 1943435 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B2460881 : Blo 1943435 2460881 := bbase (se 2 (by rfl) ⟨922830, by rfl⟩ : syracuseStep 2460881 = 1845661) (by norm_num)
theorem B6562349 : Blo 1943435 6562349 := bstep (se 3 (by rfl) ⟨1230440, by rfl⟩ : syracuseStep 6562349 = 2460881) B2460881
theorem B4374899 : Blo 1943435 4374899 := bstep (se 1 (by rfl) ⟨3281174, by rfl⟩ : syracuseStep 4374899 = 6562349) B6562349
theorem B2916599 : Blo 1943435 2916599 := bstep (se 1 (by rfl) ⟨2187449, by rfl⟩ : syracuseStep 2916599 = 4374899) B4374899
theorem B1944399 : Blo 1943435 1944399 := bstep (se 1 (by rfl) ⟨1458299, by rfl⟩ : syracuseStep 1944399 = 2916599) B2916599
theorem B2916605 : Blo 1943435 2916605 := bbase (se 3 (by rfl) ⟨546863, by rfl⟩ : syracuseStep 2916605 = 1093727) (by norm_num)
theorem B1944403 : Blo 1943435 1944403 := bstep (se 1 (by rfl) ⟨1458302, by rfl⟩ : syracuseStep 1944403 = 2916605) B2916605
theorem B4374917 : Blo 1943435 4374917 := bbase (se 4 (by rfl) ⟨410148, by rfl⟩ : syracuseStep 4374917 = 820297) (by norm_num)
theorem B2916611 : Blo 1943435 2916611 := bstep (se 1 (by rfl) ⟨2187458, by rfl⟩ : syracuseStep 2916611 = 4374917) B4374917
theorem B1944407 : Blo 1943435 1944407 := bstep (se 1 (by rfl) ⟨1458305, by rfl⟩ : syracuseStep 1944407 = 2916611) B2916611
theorem B2768509 : Blo 1943435 2768509 := bbase (se 3 (by rfl) ⟨519095, by rfl⟩ : syracuseStep 2768509 = 1038191) (by norm_num)
theorem B3691345 : Blo 1943435 3691345 := bstep (se 2 (by rfl) ⟨1384254, by rfl⟩ : syracuseStep 3691345 = 2768509) B2768509
theorem B4921793 : Blo 1943435 4921793 := bstep (se 2 (by rfl) ⟨1845672, by rfl⟩ : syracuseStep 4921793 = 3691345) B3691345
theorem B3281195 : Blo 1943435 3281195 := bstep (se 1 (by rfl) ⟨2460896, by rfl⟩ : syracuseStep 3281195 = 4921793) B4921793
theorem B2187463 : Blo 1943435 2187463 := bstep (se 1 (by rfl) ⟨1640597, by rfl⟩ : syracuseStep 2187463 = 3281195) B3281195
theorem B2916617 : Blo 1943435 2916617 := bstep (se 2 (by rfl) ⟨1093731, by rfl⟩ : syracuseStep 2916617 = 2187463) B2187463
theorem B1944411 : Blo 1943435 1944411 := bstep (se 1 (by rfl) ⟨1458308, by rfl⟩ : syracuseStep 1944411 = 2916617) B2916617
theorem B9843605 : Blo 1943435 9843605 := bbase (se 6 (by rfl) ⟨230709, by rfl⟩ : syracuseStep 9843605 = 461419) (by norm_num)
theorem B6562403 : Blo 1943435 6562403 := bstep (se 1 (by rfl) ⟨4921802, by rfl⟩ : syracuseStep 6562403 = 9843605) B9843605
theorem B4374935 : Blo 1943435 4374935 := bstep (se 1 (by rfl) ⟨3281201, by rfl⟩ : syracuseStep 4374935 = 6562403) B6562403
theorem B2916623 : Blo 1943435 2916623 := bstep (se 1 (by rfl) ⟨2187467, by rfl⟩ : syracuseStep 2916623 = 4374935) B4374935
theorem B1944415 : Blo 1943435 1944415 := bstep (se 1 (by rfl) ⟨1458311, by rfl⟩ : syracuseStep 1944415 = 2916623) B2916623
theorem B2916629 : Blo 1943435 2916629 := bbase (se 6 (by rfl) ⟨68358, by rfl⟩ : syracuseStep 2916629 = 136717) (by norm_num)
theorem B1944419 : Blo 1943435 1944419 := bstep (se 1 (by rfl) ⟨1458314, by rfl⟩ : syracuseStep 1944419 = 2916629) B2916629
theorem B10114085 : Blo 1943435 10114085 := bbase (se 4 (by rfl) ⟨948195, by rfl⟩ : syracuseStep 10114085 = 1896391) (by norm_num)
theorem B6742723 : Blo 1943435 6742723 := bstep (se 1 (by rfl) ⟨5057042, by rfl⟩ : syracuseStep 6742723 = 10114085) B10114085
theorem B8990297 : Blo 1943435 8990297 := bstep (se 2 (by rfl) ⟨3371361, by rfl⟩ : syracuseStep 8990297 = 6742723) B6742723
theorem B5993531 : Blo 1943435 5993531 := bstep (se 1 (by rfl) ⟨4495148, by rfl⟩ : syracuseStep 5993531 = 8990297) B8990297
theorem B3995687 : Blo 1943435 3995687 := bstep (se 1 (by rfl) ⟨2996765, by rfl⟩ : syracuseStep 3995687 = 5993531) B5993531
theorem B10655165 : Blo 1943435 10655165 := bstep (se 3 (by rfl) ⟨1997843, by rfl⟩ : syracuseStep 10655165 = 3995687) B3995687
theorem B7103443 : Blo 1943435 7103443 := bstep (se 1 (by rfl) ⟨5327582, by rfl⟩ : syracuseStep 7103443 = 10655165) B10655165
theorem B9471257 : Blo 1943435 9471257 := bstep (se 2 (by rfl) ⟨3551721, by rfl⟩ : syracuseStep 9471257 = 7103443) B7103443
theorem B6314171 : Blo 1943435 6314171 := bstep (se 1 (by rfl) ⟨4735628, by rfl⟩ : syracuseStep 6314171 = 9471257) B9471257
theorem B16837789 : Blo 1943435 16837789 := bstep (se 3 (by rfl) ⟨3157085, by rfl⟩ : syracuseStep 16837789 = 6314171) B6314171
theorem B22450385 : Blo 1943435 22450385 := bstep (se 2 (by rfl) ⟨8418894, by rfl⟩ : syracuseStep 22450385 = 16837789) B16837789
theorem B14966923 : Blo 1943435 14966923 := bstep (se 1 (by rfl) ⟨11225192, by rfl⟩ : syracuseStep 14966923 = 22450385) B22450385
theorem B19955897 : Blo 1943435 19955897 := bstep (se 2 (by rfl) ⟨7483461, by rfl⟩ : syracuseStep 19955897 = 14966923) B14966923
theorem B13303931 : Blo 1943435 13303931 := bstep (se 1 (by rfl) ⟨9977948, by rfl⟩ : syracuseStep 13303931 = 19955897) B19955897
theorem B35477149 : Blo 1943435 35477149 := bstep (se 3 (by rfl) ⟨6651965, by rfl⟩ : syracuseStep 35477149 = 13303931) B13303931
theorem B47302865 : Blo 1943435 47302865 := bstep (se 2 (by rfl) ⟨17738574, by rfl⟩ : syracuseStep 47302865 = 35477149) B35477149
theorem B31535243 : Blo 1943435 31535243 := bstep (se 1 (by rfl) ⟨23651432, by rfl⟩ : syracuseStep 31535243 = 47302865) B47302865
theorem B21023495 : Blo 1943435 21023495 := bstep (se 1 (by rfl) ⟨15767621, by rfl⟩ : syracuseStep 21023495 = 31535243) B31535243
theorem B14015663 : Blo 1943435 14015663 := bstep (se 1 (by rfl) ⟨10511747, by rfl⟩ : syracuseStep 14015663 = 21023495) B21023495
theorem B9343775 : Blo 1943435 9343775 := bstep (se 1 (by rfl) ⟨7007831, by rfl⟩ : syracuseStep 9343775 = 14015663) B14015663
theorem B24916733 : Blo 1943435 24916733 := bstep (se 3 (by rfl) ⟨4671887, by rfl⟩ : syracuseStep 24916733 = 9343775) B9343775
theorem B16611155 : Blo 1943435 16611155 := bstep (se 1 (by rfl) ⟨12458366, by rfl⟩ : syracuseStep 16611155 = 24916733) B24916733
theorem B11074103 : Blo 1943435 11074103 := bstep (se 1 (by rfl) ⟨8305577, by rfl⟩ : syracuseStep 11074103 = 16611155) B16611155
theorem B7382735 : Blo 1943435 7382735 := bstep (se 1 (by rfl) ⟨5537051, by rfl⟩ : syracuseStep 7382735 = 11074103) B11074103
theorem B4921823 : Blo 1943435 4921823 := bstep (se 1 (by rfl) ⟨3691367, by rfl⟩ : syracuseStep 4921823 = 7382735) B7382735
theorem B3281215 : Blo 1943435 3281215 := bstep (se 1 (by rfl) ⟨2460911, by rfl⟩ : syracuseStep 3281215 = 4921823) B4921823
theorem B4374953 : Blo 1943435 4374953 := bstep (se 2 (by rfl) ⟨1640607, by rfl⟩ : syracuseStep 4374953 = 3281215) B3281215
theorem B2916635 : Blo 1943435 2916635 := bstep (se 1 (by rfl) ⟨2187476, by rfl⟩ : syracuseStep 2916635 = 4374953) B4374953
theorem B1944423 : Blo 1943435 1944423 := bstep (se 1 (by rfl) ⟨1458317, by rfl⟩ : syracuseStep 1944423 = 2916635) B2916635
theorem B2187481 : Blo 1943435 2187481 := bbase (se 2 (by rfl) ⟨820305, by rfl⟩ : syracuseStep 2187481 = 1640611) (by norm_num)
theorem B2916641 : Blo 1943435 2916641 := bstep (se 2 (by rfl) ⟨1093740, by rfl⟩ : syracuseStep 2916641 = 2187481) B2187481
theorem B1944427 : Blo 1943435 1944427 := bstep (se 1 (by rfl) ⟨1458320, by rfl⟩ : syracuseStep 1944427 = 2916641) B2916641
theorem B3114605 : Blo 1943435 3114605 := bbase (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) (by norm_num)
theorem B2076403 : Blo 1943435 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B2768537 : Blo 1943435 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B7382765 : Blo 1943435 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B4921843 : Blo 1943435 4921843 := bstep (se 1 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 4921843 = 7382765) B7382765
theorem B6562457 : Blo 1943435 6562457 := bstep (se 2 (by rfl) ⟨2460921, by rfl⟩ : syracuseStep 6562457 = 4921843) B4921843
theorem B4374971 : Blo 1943435 4374971 := bstep (se 1 (by rfl) ⟨3281228, by rfl⟩ : syracuseStep 4374971 = 6562457) B6562457
theorem B2916647 : Blo 1943435 2916647 := bstep (se 1 (by rfl) ⟨2187485, by rfl⟩ : syracuseStep 2916647 = 4374971) B4374971
theorem B1944431 : Blo 1943435 1944431 := bstep (se 1 (by rfl) ⟨1458323, by rfl⟩ : syracuseStep 1944431 = 2916647) B2916647
theorem B2916653 : Blo 1943435 2916653 := bbase (se 3 (by rfl) ⟨546872, by rfl⟩ : syracuseStep 2916653 = 1093745) (by norm_num)
theorem B1944435 : Blo 1943435 1944435 := bstep (se 1 (by rfl) ⟨1458326, by rfl⟩ : syracuseStep 1944435 = 2916653) B2916653
theorem B4374989 : Blo 1943435 4374989 := bbase (se 3 (by rfl) ⟨820310, by rfl⟩ : syracuseStep 4374989 = 1640621) (by norm_num)
theorem B2916659 : Blo 1943435 2916659 := bstep (se 1 (by rfl) ⟨2187494, by rfl⟩ : syracuseStep 2916659 = 4374989) B4374989
theorem B1944439 : Blo 1943435 1944439 := bstep (se 1 (by rfl) ⟨1458329, by rfl⟩ : syracuseStep 1944439 = 2916659) B2916659
theorem B2460937 : Blo 1943435 2460937 := bbase (se 2 (by rfl) ⟨922851, by rfl⟩ : syracuseStep 2460937 = 1845703) (by norm_num)
theorem B3281249 : Blo 1943435 3281249 := bstep (se 2 (by rfl) ⟨1230468, by rfl⟩ : syracuseStep 3281249 = 2460937) B2460937
theorem B2187499 : Blo 1943435 2187499 := bstep (se 1 (by rfl) ⟨1640624, by rfl⟩ : syracuseStep 2187499 = 3281249) B3281249
theorem B2916665 : Blo 1943435 2916665 := bstep (se 2 (by rfl) ⟨1093749, by rfl⟩ : syracuseStep 2916665 = 2187499) B2187499
theorem B1944443 : Blo 1943435 1944443 := bstep (se 1 (by rfl) ⟨1458332, by rfl⟩ : syracuseStep 1944443 = 2916665) B2916665
theorem B1970977 : Blo 1943435 1970977 := bbase (se 2 (by rfl) ⟨739116, by rfl⟩ : syracuseStep 1970977 = 1478233) (by norm_num)
theorem B2627969 : Blo 1943435 2627969 := bstep (se 2 (by rfl) ⟨985488, by rfl⟩ : syracuseStep 2627969 = 1970977) B1970977
theorem B28031669 : Blo 1943435 28031669 := bstep (se 5 (by rfl) ⟨1313984, by rfl⟩ : syracuseStep 28031669 = 2627969) B2627969
theorem B18687779 : Blo 1943435 18687779 := bstep (se 1 (by rfl) ⟨14015834, by rfl⟩ : syracuseStep 18687779 = 28031669) B28031669
theorem B12458519 : Blo 1943435 12458519 := bstep (se 1 (by rfl) ⟨9343889, by rfl⟩ : syracuseStep 12458519 = 18687779) B18687779
theorem B8305679 : Blo 1943435 8305679 := bstep (se 1 (by rfl) ⟨6229259, by rfl⟩ : syracuseStep 8305679 = 12458519) B12458519
theorem B22148477 : Blo 1943435 22148477 := bstep (se 3 (by rfl) ⟨4152839, by rfl⟩ : syracuseStep 22148477 = 8305679) B8305679
theorem B14765651 : Blo 1943435 14765651 := bstep (se 1 (by rfl) ⟨11074238, by rfl⟩ : syracuseStep 14765651 = 22148477) B22148477
theorem B9843767 : Blo 1943435 9843767 := bstep (se 1 (by rfl) ⟨7382825, by rfl⟩ : syracuseStep 9843767 = 14765651) B14765651
theorem B6562511 : Blo 1943435 6562511 := bstep (se 1 (by rfl) ⟨4921883, by rfl⟩ : syracuseStep 6562511 = 9843767) B9843767
theorem B4375007 : Blo 1943435 4375007 := bstep (se 1 (by rfl) ⟨3281255, by rfl⟩ : syracuseStep 4375007 = 6562511) B6562511
theorem B2916671 : Blo 1943435 2916671 := bstep (se 1 (by rfl) ⟨2187503, by rfl⟩ : syracuseStep 2916671 = 4375007) B4375007
theorem B1944447 : Blo 1943435 1944447 := bstep (se 1 (by rfl) ⟨1458335, by rfl⟩ : syracuseStep 1944447 = 2916671) B2916671
theorem B2916677 : Blo 1943435 2916677 := bbase (se 4 (by rfl) ⟨273438, by rfl⟩ : syracuseStep 2916677 = 546877) (by norm_num)
theorem B1944451 : Blo 1943435 1944451 := bstep (se 1 (by rfl) ⟨1458338, by rfl⟩ : syracuseStep 1944451 = 2916677) B2916677
theorem B3281269 : Blo 1943435 3281269 := bbase (se 5 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 3281269 = 307619) (by norm_num)
theorem B4375025 : Blo 1943435 4375025 := bstep (se 2 (by rfl) ⟨1640634, by rfl⟩ : syracuseStep 4375025 = 3281269) B3281269
theorem B2916683 : Blo 1943435 2916683 := bstep (se 1 (by rfl) ⟨2187512, by rfl⟩ : syracuseStep 2916683 = 4375025) B4375025
theorem B1944455 : Blo 1943435 1944455 := bstep (se 1 (by rfl) ⟨1458341, by rfl⟩ : syracuseStep 1944455 = 2916683) B2916683
theorem B2187517 : Blo 1943435 2187517 := bbase (se 3 (by rfl) ⟨410159, by rfl⟩ : syracuseStep 2187517 = 820319) (by norm_num)
theorem B2916689 : Blo 1943435 2916689 := bstep (se 2 (by rfl) ⟨1093758, by rfl⟩ : syracuseStep 2916689 = 2187517) B2187517
theorem B1944459 : Blo 1943435 1944459 := bstep (se 1 (by rfl) ⟨1458344, by rfl⟩ : syracuseStep 1944459 = 2916689) B2916689
theorem B6562565 : Blo 1943435 6562565 := bbase (se 4 (by rfl) ⟨615240, by rfl⟩ : syracuseStep 6562565 = 1230481) (by norm_num)
theorem B4375043 : Blo 1943435 4375043 := bstep (se 1 (by rfl) ⟨3281282, by rfl⟩ : syracuseStep 4375043 = 6562565) B6562565
theorem B2916695 : Blo 1943435 2916695 := bstep (se 1 (by rfl) ⟨2187521, by rfl⟩ : syracuseStep 2916695 = 4375043) B4375043
theorem B1944463 : Blo 1943435 1944463 := bstep (se 1 (by rfl) ⟨1458347, by rfl⟩ : syracuseStep 1944463 = 2916695) B2916695
theorem B2916701 : Blo 1943435 2916701 := bbase (se 3 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 2916701 = 1093763) (by norm_num)
theorem B1944467 : Blo 1943435 1944467 := bstep (se 1 (by rfl) ⟨1458350, by rfl⟩ : syracuseStep 1944467 = 2916701) B2916701
theorem B4375061 : Blo 1943435 4375061 := bbase (se 6 (by rfl) ⟨102540, by rfl⟩ : syracuseStep 4375061 = 205081) (by norm_num)
theorem B2916707 : Blo 1943435 2916707 := bstep (se 1 (by rfl) ⟨2187530, by rfl⟩ : syracuseStep 2916707 = 4375061) B4375061
theorem B1944471 : Blo 1943435 1944471 := bstep (se 1 (by rfl) ⟨1458353, by rfl⟩ : syracuseStep 1944471 = 2916707) B2916707
theorem B7382933 : Blo 1943435 7382933 := bbase (se 6 (by rfl) ⟨173037, by rfl⟩ : syracuseStep 7382933 = 346075) (by norm_num)
theorem B4921955 : Blo 1943435 4921955 := bstep (se 1 (by rfl) ⟨3691466, by rfl⟩ : syracuseStep 4921955 = 7382933) B7382933
theorem B3281303 : Blo 1943435 3281303 := bstep (se 1 (by rfl) ⟨2460977, by rfl⟩ : syracuseStep 3281303 = 4921955) B4921955
theorem B2187535 : Blo 1943435 2187535 := bstep (se 1 (by rfl) ⟨1640651, by rfl⟩ : syracuseStep 2187535 = 3281303) B3281303
theorem B2916713 : Blo 1943435 2916713 := bstep (se 2 (by rfl) ⟨1093767, by rfl⟩ : syracuseStep 2916713 = 2187535) B2187535
theorem B1944475 : Blo 1943435 1944475 := bstep (se 1 (by rfl) ⟨1458356, by rfl⟩ : syracuseStep 1944475 = 2916713) B2916713
theorem B11074421 : Blo 1943435 11074421 := bbase (se 5 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 11074421 = 1038227) (by norm_num)
theorem B7382947 : Blo 1943435 7382947 := bstep (se 1 (by rfl) ⟨5537210, by rfl⟩ : syracuseStep 7382947 = 11074421) B11074421
theorem B9843929 : Blo 1943435 9843929 := bstep (se 2 (by rfl) ⟨3691473, by rfl⟩ : syracuseStep 9843929 = 7382947) B7382947
theorem B6562619 : Blo 1943435 6562619 := bstep (se 1 (by rfl) ⟨4921964, by rfl⟩ : syracuseStep 6562619 = 9843929) B9843929
theorem B4375079 : Blo 1943435 4375079 := bstep (se 1 (by rfl) ⟨3281309, by rfl⟩ : syracuseStep 4375079 = 6562619) B6562619
theorem B2916719 : Blo 1943435 2916719 := bstep (se 1 (by rfl) ⟨2187539, by rfl⟩ : syracuseStep 2916719 = 4375079) B4375079
theorem B1944479 : Blo 1943435 1944479 := bstep (se 1 (by rfl) ⟨1458359, by rfl⟩ : syracuseStep 1944479 = 2916719) B2916719
theorem B2916725 : Blo 1943435 2916725 := bbase (se 5 (by rfl) ⟨136721, by rfl⟩ : syracuseStep 2916725 = 273443) (by norm_num)
theorem B1944483 : Blo 1943435 1944483 := bstep (se 1 (by rfl) ⟨1458362, by rfl⟩ : syracuseStep 1944483 = 2916725) B2916725
theorem B3942037 : Blo 1943435 3942037 := bbase (se 6 (by rfl) ⟨92391, by rfl⟩ : syracuseStep 3942037 = 184783) (by norm_num)
theorem B5256049 : Blo 1943435 5256049 := bstep (se 2 (by rfl) ⟨1971018, by rfl⟩ : syracuseStep 5256049 = 3942037) B3942037
theorem B7008065 : Blo 1943435 7008065 := bstep (se 2 (by rfl) ⟨2628024, by rfl⟩ : syracuseStep 7008065 = 5256049) B5256049
theorem B4672043 : Blo 1943435 4672043 := bstep (se 1 (by rfl) ⟨3504032, by rfl⟩ : syracuseStep 4672043 = 7008065) B7008065
theorem B3114695 : Blo 1943435 3114695 := bstep (se 1 (by rfl) ⟨2336021, by rfl⟩ : syracuseStep 3114695 = 4672043) B4672043
theorem B2076463 : Blo 1943435 2076463 := bstep (se 1 (by rfl) ⟨1557347, by rfl⟩ : syracuseStep 2076463 = 3114695) B3114695
theorem B2768617 : Blo 1943435 2768617 := bstep (se 2 (by rfl) ⟨1038231, by rfl⟩ : syracuseStep 2768617 = 2076463) B2076463
theorem B3691489 : Blo 1943435 3691489 := bstep (se 2 (by rfl) ⟨1384308, by rfl⟩ : syracuseStep 3691489 = 2768617) B2768617
theorem B4921985 : Blo 1943435 4921985 := bstep (se 2 (by rfl) ⟨1845744, by rfl⟩ : syracuseStep 4921985 = 3691489) B3691489
theorem B3281323 : Blo 1943435 3281323 := bstep (se 1 (by rfl) ⟨2460992, by rfl⟩ : syracuseStep 3281323 = 4921985) B4921985
theorem B4375097 : Blo 1943435 4375097 := bstep (se 2 (by rfl) ⟨1640661, by rfl⟩ : syracuseStep 4375097 = 3281323) B3281323
theorem B2916731 : Blo 1943435 2916731 := bstep (se 1 (by rfl) ⟨2187548, by rfl⟩ : syracuseStep 2916731 = 4375097) B4375097
theorem B1944487 : Blo 1943435 1944487 := bstep (se 1 (by rfl) ⟨1458365, by rfl⟩ : syracuseStep 1944487 = 2916731) B2916731
theorem B2187553 : Blo 1943435 2187553 := bbase (se 2 (by rfl) ⟨820332, by rfl⟩ : syracuseStep 2187553 = 1640665) (by norm_num)
theorem B2916737 : Blo 1943435 2916737 := bstep (se 2 (by rfl) ⟨1093776, by rfl⟩ : syracuseStep 2916737 = 2187553) B2187553
theorem B1944491 : Blo 1943435 1944491 := bstep (se 1 (by rfl) ⟨1458368, by rfl⟩ : syracuseStep 1944491 = 2916737) B2916737
theorem B4922005 : Blo 1943435 4922005 := bbase (se 6 (by rfl) ⟨115359, by rfl⟩ : syracuseStep 4922005 = 230719) (by norm_num)
theorem B6562673 : Blo 1943435 6562673 := bstep (se 2 (by rfl) ⟨2461002, by rfl⟩ : syracuseStep 6562673 = 4922005) B4922005
theorem B4375115 : Blo 1943435 4375115 := bstep (se 1 (by rfl) ⟨3281336, by rfl⟩ : syracuseStep 4375115 = 6562673) B6562673
theorem B2916743 : Blo 1943435 2916743 := bstep (se 1 (by rfl) ⟨2187557, by rfl⟩ : syracuseStep 2916743 = 4375115) B4375115
theorem B1944495 : Blo 1943435 1944495 := bstep (se 1 (by rfl) ⟨1458371, by rfl⟩ : syracuseStep 1944495 = 2916743) B2916743
theorem B2916749 : Blo 1943435 2916749 := bbase (se 3 (by rfl) ⟨546890, by rfl⟩ : syracuseStep 2916749 = 1093781) (by norm_num)
theorem B1944499 : Blo 1943435 1944499 := bstep (se 1 (by rfl) ⟨1458374, by rfl⟩ : syracuseStep 1944499 = 2916749) B2916749
theorem B4375133 : Blo 1943435 4375133 := bbase (se 3 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 4375133 = 1640675) (by norm_num)
theorem B2916755 : Blo 1943435 2916755 := bstep (se 1 (by rfl) ⟨2187566, by rfl⟩ : syracuseStep 2916755 = 4375133) B4375133
theorem B1944503 : Blo 1943435 1944503 := bstep (se 1 (by rfl) ⟨1458377, by rfl⟩ : syracuseStep 1944503 = 2916755) B2916755
theorem B3281357 : Blo 1943435 3281357 := bbase (se 3 (by rfl) ⟨615254, by rfl⟩ : syracuseStep 3281357 = 1230509) (by norm_num)
theorem B2187571 : Blo 1943435 2187571 := bstep (se 1 (by rfl) ⟨1640678, by rfl⟩ : syracuseStep 2187571 = 3281357) B3281357
theorem B2916761 : Blo 1943435 2916761 := bstep (se 2 (by rfl) ⟨1093785, by rfl⟩ : syracuseStep 2916761 = 2187571) B2187571
theorem B1944507 : Blo 1943435 1944507 := bstep (se 1 (by rfl) ⟨1458380, by rfl⟩ : syracuseStep 1944507 = 2916761) B2916761
theorem B9344197 : Blo 1943435 9344197 := bbase (se 4 (by rfl) ⟨876018, by rfl⟩ : syracuseStep 9344197 = 1752037) (by norm_num)
theorem B12458929 : Blo 1943435 12458929 := bstep (se 2 (by rfl) ⟨4672098, by rfl⟩ : syracuseStep 12458929 = 9344197) B9344197
theorem B16611905 : Blo 1943435 16611905 := bstep (se 2 (by rfl) ⟨6229464, by rfl⟩ : syracuseStep 16611905 = 12458929) B12458929
theorem B11074603 : Blo 1943435 11074603 := bstep (se 1 (by rfl) ⟨8305952, by rfl⟩ : syracuseStep 11074603 = 16611905) B16611905
theorem B14766137 : Blo 1943435 14766137 := bstep (se 2 (by rfl) ⟨5537301, by rfl⟩ : syracuseStep 14766137 = 11074603) B11074603
theorem B9844091 : Blo 1943435 9844091 := bstep (se 1 (by rfl) ⟨7383068, by rfl⟩ : syracuseStep 9844091 = 14766137) B14766137
theorem B6562727 : Blo 1943435 6562727 := bstep (se 1 (by rfl) ⟨4922045, by rfl⟩ : syracuseStep 6562727 = 9844091) B9844091
theorem B4375151 : Blo 1943435 4375151 := bstep (se 1 (by rfl) ⟨3281363, by rfl⟩ : syracuseStep 4375151 = 6562727) B6562727
theorem B2916767 : Blo 1943435 2916767 := bstep (se 1 (by rfl) ⟨2187575, by rfl⟩ : syracuseStep 2916767 = 4375151) B4375151
theorem B1944511 : Blo 1943435 1944511 := bstep (se 1 (by rfl) ⟨1458383, by rfl⟩ : syracuseStep 1944511 = 2916767) B2916767
theorem B2916773 : Blo 1943435 2916773 := bbase (se 4 (by rfl) ⟨273447, by rfl⟩ : syracuseStep 2916773 = 546895) (by norm_num)
theorem B1944515 : Blo 1943435 1944515 := bstep (se 1 (by rfl) ⟨1458386, by rfl⟩ : syracuseStep 1944515 = 2916773) B2916773
theorem B2461033 : Blo 1943435 2461033 := bbase (se 2 (by rfl) ⟨922887, by rfl⟩ : syracuseStep 2461033 = 1845775) (by norm_num)
theorem B3281377 : Blo 1943435 3281377 := bstep (se 2 (by rfl) ⟨1230516, by rfl⟩ : syracuseStep 3281377 = 2461033) B2461033
theorem B4375169 : Blo 1943435 4375169 := bstep (se 2 (by rfl) ⟨1640688, by rfl⟩ : syracuseStep 4375169 = 3281377) B3281377
theorem B2916779 : Blo 1943435 2916779 := bstep (se 1 (by rfl) ⟨2187584, by rfl⟩ : syracuseStep 2916779 = 4375169) B4375169
theorem B1944519 : Blo 1943435 1944519 := bstep (se 1 (by rfl) ⟨1458389, by rfl⟩ : syracuseStep 1944519 = 2916779) B2916779
theorem B2187589 : Blo 1943435 2187589 := bbase (se 4 (by rfl) ⟨205086, by rfl⟩ : syracuseStep 2187589 = 410173) (by norm_num)
theorem B2916785 : Blo 1943435 2916785 := bstep (se 2 (by rfl) ⟨1093794, by rfl⟩ : syracuseStep 2916785 = 2187589) B2187589
theorem B1944523 : Blo 1943435 1944523 := bstep (se 1 (by rfl) ⟨1458392, by rfl⟩ : syracuseStep 1944523 = 2916785) B2916785
theorem B3691565 : Blo 1943435 3691565 := bbase (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) (by norm_num)
theorem B2461043 : Blo 1943435 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B6562781 : Blo 1943435 6562781 := bstep (se 3 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 6562781 = 2461043) B2461043
theorem B4375187 : Blo 1943435 4375187 := bstep (se 1 (by rfl) ⟨3281390, by rfl⟩ : syracuseStep 4375187 = 6562781) B6562781
theorem B2916791 : Blo 1943435 2916791 := bstep (se 1 (by rfl) ⟨2187593, by rfl⟩ : syracuseStep 2916791 = 4375187) B4375187
theorem B1944527 : Blo 1943435 1944527 := bstep (se 1 (by rfl) ⟨1458395, by rfl⟩ : syracuseStep 1944527 = 2916791) B2916791
theorem B2916797 : Blo 1943435 2916797 := bbase (se 3 (by rfl) ⟨546899, by rfl⟩ : syracuseStep 2916797 = 1093799) (by norm_num)
theorem B1944531 : Blo 1943435 1944531 := bstep (se 1 (by rfl) ⟨1458398, by rfl⟩ : syracuseStep 1944531 = 2916797) B2916797
theorem B4375205 : Blo 1943435 4375205 := bbase (se 4 (by rfl) ⟨410175, by rfl⟩ : syracuseStep 4375205 = 820351) (by norm_num)
theorem B2916803 : Blo 1943435 2916803 := bstep (se 1 (by rfl) ⟨2187602, by rfl⟩ : syracuseStep 2916803 = 4375205) B4375205
theorem B1944535 : Blo 1943435 1944535 := bstep (se 1 (by rfl) ⟨1458401, by rfl⟩ : syracuseStep 1944535 = 2916803) B2916803
theorem B4922117 : Blo 1943435 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B3281411 : Blo 1943435 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2187607 : Blo 1943435 2187607 := bstep (se 1 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 2187607 = 3281411) B3281411
theorem B2916809 : Blo 1943435 2916809 := bstep (se 2 (by rfl) ⟨1093803, by rfl⟩ : syracuseStep 2916809 = 2187607) B2187607
theorem B1944539 : Blo 1943435 1944539 := bstep (se 1 (by rfl) ⟨1458404, by rfl⟩ : syracuseStep 1944539 = 2916809) B2916809
theorem B4153045 : Blo 1943435 4153045 := bbase (se 7 (by rfl) ⟨48668, by rfl⟩ : syracuseStep 4153045 = 97337) (by norm_num)
theorem B5537393 : Blo 1943435 5537393 := bstep (se 2 (by rfl) ⟨2076522, by rfl⟩ : syracuseStep 5537393 = 4153045) B4153045
theorem B3691595 : Blo 1943435 3691595 := bstep (se 1 (by rfl) ⟨2768696, by rfl⟩ : syracuseStep 3691595 = 5537393) B5537393
theorem B9844253 : Blo 1943435 9844253 := bstep (se 3 (by rfl) ⟨1845797, by rfl⟩ : syracuseStep 9844253 = 3691595) B3691595
theorem B6562835 : Blo 1943435 6562835 := bstep (se 1 (by rfl) ⟨4922126, by rfl⟩ : syracuseStep 6562835 = 9844253) B9844253
theorem B4375223 : Blo 1943435 4375223 := bstep (se 1 (by rfl) ⟨3281417, by rfl⟩ : syracuseStep 4375223 = 6562835) B6562835
theorem B2916815 : Blo 1943435 2916815 := bstep (se 1 (by rfl) ⟨2187611, by rfl⟩ : syracuseStep 2916815 = 4375223) B4375223
theorem B1944543 : Blo 1943435 1944543 := bstep (se 1 (by rfl) ⟨1458407, by rfl⟩ : syracuseStep 1944543 = 2916815) B2916815
theorem B2916821 : Blo 1943435 2916821 := bbase (se 7 (by rfl) ⟨34181, by rfl⟩ : syracuseStep 2916821 = 68363) (by norm_num)
theorem B1944547 : Blo 1943435 1944547 := bstep (se 1 (by rfl) ⟨1458410, by rfl⟩ : syracuseStep 1944547 = 2916821) B2916821
theorem B7383221 : Blo 1943435 7383221 := bbase (se 5 (by rfl) ⟨346088, by rfl⟩ : syracuseStep 7383221 = 692177) (by norm_num)
theorem B4922147 : Blo 1943435 4922147 := bstep (se 1 (by rfl) ⟨3691610, by rfl⟩ : syracuseStep 4922147 = 7383221) B7383221
theorem B3281431 : Blo 1943435 3281431 := bstep (se 1 (by rfl) ⟨2461073, by rfl⟩ : syracuseStep 3281431 = 4922147) B4922147
theorem B4375241 : Blo 1943435 4375241 := bstep (se 2 (by rfl) ⟨1640715, by rfl⟩ : syracuseStep 4375241 = 3281431) B3281431
theorem B2916827 : Blo 1943435 2916827 := bstep (se 1 (by rfl) ⟨2187620, by rfl⟩ : syracuseStep 2916827 = 4375241) B4375241
theorem B1944551 : Blo 1943435 1944551 := bstep (se 1 (by rfl) ⟨1458413, by rfl⟩ : syracuseStep 1944551 = 2916827) B2916827
theorem B2187625 : Blo 1943435 2187625 := bbase (se 2 (by rfl) ⟨820359, by rfl⟩ : syracuseStep 2187625 = 1640719) (by norm_num)
theorem B2916833 : Blo 1943435 2916833 := bstep (se 2 (by rfl) ⟨1093812, by rfl⟩ : syracuseStep 2916833 = 2187625) B2187625
theorem B1944555 : Blo 1943435 1944555 := bstep (se 1 (by rfl) ⟨1458416, by rfl⟩ : syracuseStep 1944555 = 2916833) B2916833
theorem B2956637 : Blo 1943435 2956637 := bbase (se 3 (by rfl) ⟨554369, by rfl⟩ : syracuseStep 2956637 = 1108739) (by norm_num)
theorem B1971091 : Blo 1943435 1971091 := bstep (se 1 (by rfl) ⟨1478318, by rfl⟩ : syracuseStep 1971091 = 2956637) B2956637
theorem B2628121 : Blo 1943435 2628121 := bstep (se 2 (by rfl) ⟨985545, by rfl⟩ : syracuseStep 2628121 = 1971091) B1971091
theorem B3504161 : Blo 1943435 3504161 := bstep (se 2 (by rfl) ⟨1314060, by rfl⟩ : syracuseStep 3504161 = 2628121) B2628121
theorem B9344429 : Blo 1943435 9344429 := bstep (se 3 (by rfl) ⟨1752080, by rfl⟩ : syracuseStep 9344429 = 3504161) B3504161
theorem B6229619 : Blo 1943435 6229619 := bstep (se 1 (by rfl) ⟨4672214, by rfl⟩ : syracuseStep 6229619 = 9344429) B9344429
theorem B4153079 : Blo 1943435 4153079 := bstep (se 1 (by rfl) ⟨3114809, by rfl⟩ : syracuseStep 4153079 = 6229619) B6229619
theorem B11074877 : Blo 1943435 11074877 := bstep (se 3 (by rfl) ⟨2076539, by rfl⟩ : syracuseStep 11074877 = 4153079) B4153079
theorem B7383251 : Blo 1943435 7383251 := bstep (se 1 (by rfl) ⟨5537438, by rfl⟩ : syracuseStep 7383251 = 11074877) B11074877
theorem B4922167 : Blo 1943435 4922167 := bstep (se 1 (by rfl) ⟨3691625, by rfl⟩ : syracuseStep 4922167 = 7383251) B7383251
theorem B6562889 : Blo 1943435 6562889 := bstep (se 2 (by rfl) ⟨2461083, by rfl⟩ : syracuseStep 6562889 = 4922167) B4922167
theorem B4375259 : Blo 1943435 4375259 := bstep (se 1 (by rfl) ⟨3281444, by rfl⟩ : syracuseStep 4375259 = 6562889) B6562889
theorem B2916839 : Blo 1943435 2916839 := bstep (se 1 (by rfl) ⟨2187629, by rfl⟩ : syracuseStep 2916839 = 4375259) B4375259
theorem B1944559 : Blo 1943435 1944559 := bstep (se 1 (by rfl) ⟨1458419, by rfl⟩ : syracuseStep 1944559 = 2916839) B2916839
theorem B2916845 : Blo 1943435 2916845 := bbase (se 3 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 2916845 = 1093817) (by norm_num)
theorem B1944563 : Blo 1943435 1944563 := bstep (se 1 (by rfl) ⟨1458422, by rfl⟩ : syracuseStep 1944563 = 2916845) B2916845
theorem B4375277 : Blo 1943435 4375277 := bbase (se 3 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 4375277 = 1640729) (by norm_num)
theorem B2916851 : Blo 1943435 2916851 := bstep (se 1 (by rfl) ⟨2187638, by rfl⟩ : syracuseStep 2916851 = 4375277) B4375277
theorem B1944567 : Blo 1943435 1944567 := bstep (se 1 (by rfl) ⟨1458425, by rfl⟩ : syracuseStep 1944567 = 2916851) B2916851
theorem B2076553 : Blo 1943435 2076553 := bbase (se 2 (by rfl) ⟨778707, by rfl⟩ : syracuseStep 2076553 = 1557415) (by norm_num)
theorem B2768737 : Blo 1943435 2768737 := bstep (se 2 (by rfl) ⟨1038276, by rfl⟩ : syracuseStep 2768737 = 2076553) B2076553
theorem B3691649 : Blo 1943435 3691649 := bstep (se 2 (by rfl) ⟨1384368, by rfl⟩ : syracuseStep 3691649 = 2768737) B2768737
theorem B2461099 : Blo 1943435 2461099 := bstep (se 1 (by rfl) ⟨1845824, by rfl⟩ : syracuseStep 2461099 = 3691649) B3691649
theorem B3281465 : Blo 1943435 3281465 := bstep (se 2 (by rfl) ⟨1230549, by rfl⟩ : syracuseStep 3281465 = 2461099) B2461099
theorem B2187643 : Blo 1943435 2187643 := bstep (se 1 (by rfl) ⟨1640732, by rfl⟩ : syracuseStep 2187643 = 3281465) B3281465
theorem B2916857 : Blo 1943435 2916857 := bstep (se 2 (by rfl) ⟨1093821, by rfl⟩ : syracuseStep 2916857 = 2187643) B2187643
theorem B1944571 : Blo 1943435 1944571 := bstep (se 1 (by rfl) ⟨1458428, by rfl⟩ : syracuseStep 1944571 = 2916857) B2916857
theorem B16202069 : Blo 1943435 16202069 := bbase (se 10 (by rfl) ⟨23733, by rfl⟩ : syracuseStep 16202069 = 47467) (by norm_num)
theorem B10801379 : Blo 1943435 10801379 := bstep (se 1 (by rfl) ⟨8101034, by rfl⟩ : syracuseStep 10801379 = 16202069) B16202069
theorem B7200919 : Blo 1943435 7200919 := bstep (se 1 (by rfl) ⟨5400689, by rfl⟩ : syracuseStep 7200919 = 10801379) B10801379
theorem B38404901 : Blo 1943435 38404901 := bstep (se 4 (by rfl) ⟨3600459, by rfl⟩ : syracuseStep 38404901 = 7200919) B7200919
theorem B102413069 : Blo 1943435 102413069 := bstep (se 3 (by rfl) ⟨19202450, by rfl⟩ : syracuseStep 102413069 = 38404901) B38404901
theorem B68275379 : Blo 1943435 68275379 := bstep (se 1 (by rfl) ⟨51206534, by rfl⟩ : syracuseStep 68275379 = 102413069) B102413069
theorem B45516919 : Blo 1943435 45516919 := bstep (se 1 (by rfl) ⟨34137689, by rfl⟩ : syracuseStep 45516919 = 68275379) B68275379
theorem B60689225 : Blo 1943435 60689225 := bstep (se 2 (by rfl) ⟨22758459, by rfl⟩ : syracuseStep 60689225 = 45516919) B45516919
theorem B40459483 : Blo 1943435 40459483 := bstep (se 1 (by rfl) ⟨30344612, by rfl⟩ : syracuseStep 40459483 = 60689225) B60689225
theorem B215783909 : Blo 1943435 215783909 := bstep (se 4 (by rfl) ⟨20229741, by rfl⟩ : syracuseStep 215783909 = 40459483) B40459483
theorem B143855939 : Blo 1943435 143855939 := bstep (se 1 (by rfl) ⟨107891954, by rfl⟩ : syracuseStep 143855939 = 215783909) B215783909
theorem B95903959 : Blo 1943435 95903959 := bstep (se 1 (by rfl) ⟨71927969, by rfl⟩ : syracuseStep 95903959 = 143855939) B143855939
theorem B127871945 : Blo 1943435 127871945 := bstep (se 2 (by rfl) ⟨47951979, by rfl⟩ : syracuseStep 127871945 = 95903959) B95903959
theorem B85247963 : Blo 1943435 85247963 := bstep (se 1 (by rfl) ⟨63935972, by rfl⟩ : syracuseStep 85247963 = 127871945) B127871945
theorem B56831975 : Blo 1943435 56831975 := bstep (se 1 (by rfl) ⟨42623981, by rfl⟩ : syracuseStep 56831975 = 85247963) B85247963
theorem B37887983 : Blo 1943435 37887983 := bstep (se 1 (by rfl) ⟨28415987, by rfl⟩ : syracuseStep 37887983 = 56831975) B56831975
theorem B25258655 : Blo 1943435 25258655 := bstep (se 1 (by rfl) ⟨18943991, by rfl⟩ : syracuseStep 25258655 = 37887983) B37887983
theorem B16839103 : Blo 1943435 16839103 := bstep (se 1 (by rfl) ⟨12629327, by rfl⟩ : syracuseStep 16839103 = 25258655) B25258655
theorem B22452137 : Blo 1943435 22452137 := bstep (se 2 (by rfl) ⟨8419551, by rfl⟩ : syracuseStep 22452137 = 16839103) B16839103
theorem B14968091 : Blo 1943435 14968091 := bstep (se 1 (by rfl) ⟨11226068, by rfl⟩ : syracuseStep 14968091 = 22452137) B22452137
theorem B9978727 : Blo 1943435 9978727 := bstep (se 1 (by rfl) ⟨7484045, by rfl⟩ : syracuseStep 9978727 = 14968091) B14968091
theorem B13304969 : Blo 1943435 13304969 := bstep (se 2 (by rfl) ⟨4989363, by rfl⟩ : syracuseStep 13304969 = 9978727) B9978727
theorem B8869979 : Blo 1943435 8869979 := bstep (se 1 (by rfl) ⟨6652484, by rfl⟩ : syracuseStep 8869979 = 13304969) B13304969
theorem B23653277 : Blo 1943435 23653277 := bstep (se 3 (by rfl) ⟨4434989, by rfl⟩ : syracuseStep 23653277 = 8869979) B8869979
theorem B15768851 : Blo 1943435 15768851 := bstep (se 1 (by rfl) ⟨11826638, by rfl⟩ : syracuseStep 15768851 = 23653277) B23653277
theorem B42050269 : Blo 1943435 42050269 := bstep (se 3 (by rfl) ⟨7884425, by rfl⟩ : syracuseStep 42050269 = 15768851) B15768851
theorem B56067025 : Blo 1943435 56067025 := bstep (se 2 (by rfl) ⟨21025134, by rfl⟩ : syracuseStep 56067025 = 42050269) B42050269
theorem B74756033 : Blo 1943435 74756033 := bstep (se 2 (by rfl) ⟨28033512, by rfl⟩ : syracuseStep 74756033 = 56067025) B56067025
theorem B49837355 : Blo 1943435 49837355 := bstep (se 1 (by rfl) ⟨37378016, by rfl⟩ : syracuseStep 49837355 = 74756033) B74756033
theorem B33224903 : Blo 1943435 33224903 := bstep (se 1 (by rfl) ⟨24918677, by rfl⟩ : syracuseStep 33224903 = 49837355) B49837355
theorem B22149935 : Blo 1943435 22149935 := bstep (se 1 (by rfl) ⟨16612451, by rfl⟩ : syracuseStep 22149935 = 33224903) B33224903
theorem B14766623 : Blo 1943435 14766623 := bstep (se 1 (by rfl) ⟨11074967, by rfl⟩ : syracuseStep 14766623 = 22149935) B22149935
theorem B9844415 : Blo 1943435 9844415 := bstep (se 1 (by rfl) ⟨7383311, by rfl⟩ : syracuseStep 9844415 = 14766623) B14766623
theorem B6562943 : Blo 1943435 6562943 := bstep (se 1 (by rfl) ⟨4922207, by rfl⟩ : syracuseStep 6562943 = 9844415) B9844415
theorem B4375295 : Blo 1943435 4375295 := bstep (se 1 (by rfl) ⟨3281471, by rfl⟩ : syracuseStep 4375295 = 6562943) B6562943
theorem B2916863 : Blo 1943435 2916863 := bstep (se 1 (by rfl) ⟨2187647, by rfl⟩ : syracuseStep 2916863 = 4375295) B4375295
theorem B1944575 : Blo 1943435 1944575 := bstep (se 1 (by rfl) ⟨1458431, by rfl⟩ : syracuseStep 1944575 = 2916863) B2916863
theorem B2916869 : Blo 1943435 2916869 := bbase (se 4 (by rfl) ⟨273456, by rfl⟩ : syracuseStep 2916869 = 546913) (by norm_num)
theorem B1944579 : Blo 1943435 1944579 := bstep (se 1 (by rfl) ⟨1458434, by rfl⟩ : syracuseStep 1944579 = 2916869) B2916869
theorem B3281485 : Blo 1943435 3281485 := bbase (se 3 (by rfl) ⟨615278, by rfl⟩ : syracuseStep 3281485 = 1230557) (by norm_num)
theorem B4375313 : Blo 1943435 4375313 := bstep (se 2 (by rfl) ⟨1640742, by rfl⟩ : syracuseStep 4375313 = 3281485) B3281485
theorem B2916875 : Blo 1943435 2916875 := bstep (se 1 (by rfl) ⟨2187656, by rfl⟩ : syracuseStep 2916875 = 4375313) B4375313
theorem B1944583 : Blo 1943435 1944583 := bstep (se 1 (by rfl) ⟨1458437, by rfl⟩ : syracuseStep 1944583 = 2916875) B2916875
theorem B2187661 : Blo 1943435 2187661 := bbase (se 3 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 2187661 = 820373) (by norm_num)
theorem B2916881 : Blo 1943435 2916881 := bstep (se 2 (by rfl) ⟨1093830, by rfl⟩ : syracuseStep 2916881 = 2187661) B2187661
theorem B1944587 : Blo 1943435 1944587 := bstep (se 1 (by rfl) ⟨1458440, by rfl⟩ : syracuseStep 1944587 = 2916881) B2916881
theorem B6562997 : Blo 1943435 6562997 := bbase (se 5 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 6562997 = 615281) (by norm_num)
theorem B4375331 : Blo 1943435 4375331 := bstep (se 1 (by rfl) ⟨3281498, by rfl⟩ : syracuseStep 4375331 = 6562997) B6562997
theorem B2916887 : Blo 1943435 2916887 := bstep (se 1 (by rfl) ⟨2187665, by rfl⟩ : syracuseStep 2916887 = 4375331) B4375331
theorem B1944591 : Blo 1943435 1944591 := bstep (se 1 (by rfl) ⟨1458443, by rfl⟩ : syracuseStep 1944591 = 2916887) B2916887
theorem B2916893 : Blo 1943435 2916893 := bbase (se 3 (by rfl) ⟨546917, by rfl⟩ : syracuseStep 2916893 = 1093835) (by norm_num)
theorem B1944595 : Blo 1943435 1944595 := bstep (se 1 (by rfl) ⟨1458446, by rfl⟩ : syracuseStep 1944595 = 2916893) B2916893
theorem B4375349 : Blo 1943435 4375349 := bbase (se 5 (by rfl) ⟨205094, by rfl⟩ : syracuseStep 4375349 = 410189) (by norm_num)
theorem B2916899 : Blo 1943435 2916899 := bstep (se 1 (by rfl) ⟨2187674, by rfl⟩ : syracuseStep 2916899 = 4375349) B4375349
theorem B1944599 : Blo 1943435 1944599 := bstep (se 1 (by rfl) ⟨1458449, by rfl⟩ : syracuseStep 1944599 = 2916899) B2916899
theorem B1998029 : Blo 1943435 1998029 := bbase (se 3 (by rfl) ⟨374630, by rfl⟩ : syracuseStep 1998029 = 749261) (by norm_num)
theorem B5328077 : Blo 1943435 5328077 := bstep (se 3 (by rfl) ⟨999014, by rfl⟩ : syracuseStep 5328077 = 1998029) B1998029
theorem B14208205 : Blo 1943435 14208205 := bstep (se 3 (by rfl) ⟨2664038, by rfl⟩ : syracuseStep 14208205 = 5328077) B5328077
theorem B18944273 : Blo 1943435 18944273 := bstep (se 2 (by rfl) ⟨7104102, by rfl⟩ : syracuseStep 18944273 = 14208205) B14208205
theorem B12629515 : Blo 1943435 12629515 := bstep (se 1 (by rfl) ⟨9472136, by rfl⟩ : syracuseStep 12629515 = 18944273) B18944273
theorem B16839353 : Blo 1943435 16839353 := bstep (se 2 (by rfl) ⟨6314757, by rfl⟩ : syracuseStep 16839353 = 12629515) B12629515
theorem B44904941 : Blo 1943435 44904941 := bstep (se 3 (by rfl) ⟨8419676, by rfl⟩ : syracuseStep 44904941 = 16839353) B16839353
theorem B29936627 : Blo 1943435 29936627 := bstep (se 1 (by rfl) ⟨22452470, by rfl⟩ : syracuseStep 29936627 = 44904941) B44904941
theorem B19957751 : Blo 1943435 19957751 := bstep (se 1 (by rfl) ⟨14968313, by rfl⟩ : syracuseStep 19957751 = 29936627) B29936627
theorem B13305167 : Blo 1943435 13305167 := bstep (se 1 (by rfl) ⟨9978875, by rfl⟩ : syracuseStep 13305167 = 19957751) B19957751
theorem B8870111 : Blo 1943435 8870111 := bstep (se 1 (by rfl) ⟨6652583, by rfl⟩ : syracuseStep 8870111 = 13305167) B13305167
theorem B5913407 : Blo 1943435 5913407 := bstep (se 1 (by rfl) ⟨4435055, by rfl⟩ : syracuseStep 5913407 = 8870111) B8870111
theorem B3942271 : Blo 1943435 3942271 := bstep (se 1 (by rfl) ⟨2956703, by rfl⟩ : syracuseStep 3942271 = 5913407) B5913407
theorem B5256361 : Blo 1943435 5256361 := bstep (se 2 (by rfl) ⟨1971135, by rfl⟩ : syracuseStep 5256361 = 3942271) B3942271
theorem B7008481 : Blo 1943435 7008481 := bstep (se 2 (by rfl) ⟨2628180, by rfl⟩ : syracuseStep 7008481 = 5256361) B5256361
theorem B9344641 : Blo 1943435 9344641 := bstep (se 2 (by rfl) ⟨3504240, by rfl⟩ : syracuseStep 9344641 = 7008481) B7008481
theorem B12459521 : Blo 1943435 12459521 := bstep (se 2 (by rfl) ⟨4672320, by rfl⟩ : syracuseStep 12459521 = 9344641) B9344641
theorem B8306347 : Blo 1943435 8306347 := bstep (se 1 (by rfl) ⟨6229760, by rfl⟩ : syracuseStep 8306347 = 12459521) B12459521
theorem B11075129 : Blo 1943435 11075129 := bstep (se 2 (by rfl) ⟨4153173, by rfl⟩ : syracuseStep 11075129 = 8306347) B8306347
theorem B7383419 : Blo 1943435 7383419 := bstep (se 1 (by rfl) ⟨5537564, by rfl⟩ : syracuseStep 7383419 = 11075129) B11075129
theorem B4922279 : Blo 1943435 4922279 := bstep (se 1 (by rfl) ⟨3691709, by rfl⟩ : syracuseStep 4922279 = 7383419) B7383419
theorem B3281519 : Blo 1943435 3281519 := bstep (se 1 (by rfl) ⟨2461139, by rfl⟩ : syracuseStep 3281519 = 4922279) B4922279
theorem B2187679 : Blo 1943435 2187679 := bstep (se 1 (by rfl) ⟨1640759, by rfl⟩ : syracuseStep 2187679 = 3281519) B3281519
theorem B2916905 : Blo 1943435 2916905 := bstep (se 2 (by rfl) ⟨1093839, by rfl⟩ : syracuseStep 2916905 = 2187679) B2187679
theorem B1944603 : Blo 1943435 1944603 := bstep (se 1 (by rfl) ⟨1458452, by rfl⟩ : syracuseStep 1944603 = 2916905) B2916905
theorem B2956709 : Blo 1943435 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B7884557 : Blo 1943435 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B5256371 : Blo 1943435 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B14016989 : Blo 1943435 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B9344659 : Blo 1943435 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B12459545 : Blo 1943435 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B8306363 : Blo 1943435 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B5537575 : Blo 1943435 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B7383433 : Blo 1943435 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B9844577 : Blo 1943435 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B6563051 : Blo 1943435 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B4375367 : Blo 1943435 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B2916911 : Blo 1943435 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B1944607 : Blo 1943435 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B2916917 : Blo 1943435 2916917 := bbase (se 5 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 2916917 = 273461) (by norm_num)
theorem B1944611 : Blo 1943435 1944611 := bstep (se 1 (by rfl) ⟨1458458, by rfl⟩ : syracuseStep 1944611 = 2916917) B2916917
theorem B4922309 : Blo 1943435 4922309 := bbase (se 4 (by rfl) ⟨461466, by rfl⟩ : syracuseStep 4922309 = 922933) (by norm_num)
theorem B3281539 : Blo 1943435 3281539 := bstep (se 1 (by rfl) ⟨2461154, by rfl⟩ : syracuseStep 3281539 = 4922309) B4922309
theorem B4375385 : Blo 1943435 4375385 := bstep (se 2 (by rfl) ⟨1640769, by rfl⟩ : syracuseStep 4375385 = 3281539) B3281539
theorem B2916923 : Blo 1943435 2916923 := bstep (se 1 (by rfl) ⟨2187692, by rfl⟩ : syracuseStep 2916923 = 4375385) B4375385
theorem B1944615 : Blo 1943435 1944615 := bstep (se 1 (by rfl) ⟨1458461, by rfl⟩ : syracuseStep 1944615 = 2916923) B2916923
theorem B2187697 : Blo 1943435 2187697 := bbase (se 2 (by rfl) ⟨820386, by rfl⟩ : syracuseStep 2187697 = 1640773) (by norm_num)
theorem B2916929 : Blo 1943435 2916929 := bstep (se 2 (by rfl) ⟨1093848, by rfl⟩ : syracuseStep 2916929 = 2187697) B2187697
theorem B1944619 : Blo 1943435 1944619 := bstep (se 1 (by rfl) ⟨1458464, by rfl⟩ : syracuseStep 1944619 = 2916929) B2916929
theorem B5537621 : Blo 1943435 5537621 := bbase (se 9 (by rfl) ⟨16223, by rfl⟩ : syracuseStep 5537621 = 32447) (by norm_num)
theorem B3691747 : Blo 1943435 3691747 := bstep (se 1 (by rfl) ⟨2768810, by rfl⟩ : syracuseStep 3691747 = 5537621) B5537621
theorem B4922329 : Blo 1943435 4922329 := bstep (se 2 (by rfl) ⟨1845873, by rfl⟩ : syracuseStep 4922329 = 3691747) B3691747
theorem B6563105 : Blo 1943435 6563105 := bstep (se 2 (by rfl) ⟨2461164, by rfl⟩ : syracuseStep 6563105 = 4922329) B4922329
theorem B4375403 : Blo 1943435 4375403 := bstep (se 1 (by rfl) ⟨3281552, by rfl⟩ : syracuseStep 4375403 = 6563105) B6563105
theorem B2916935 : Blo 1943435 2916935 := bstep (se 1 (by rfl) ⟨2187701, by rfl⟩ : syracuseStep 2916935 = 4375403) B4375403
theorem B1944623 : Blo 1943435 1944623 := bstep (se 1 (by rfl) ⟨1458467, by rfl⟩ : syracuseStep 1944623 = 2916935) B2916935
theorem B2916941 : Blo 1943435 2916941 := bbase (se 3 (by rfl) ⟨546926, by rfl⟩ : syracuseStep 2916941 = 1093853) (by norm_num)
theorem B1944627 : Blo 1943435 1944627 := bstep (se 1 (by rfl) ⟨1458470, by rfl⟩ : syracuseStep 1944627 = 2916941) B2916941
theorem B4375421 : Blo 1943435 4375421 := bbase (se 3 (by rfl) ⟨820391, by rfl⟩ : syracuseStep 4375421 = 1640783) (by norm_num)
theorem B2916947 : Blo 1943435 2916947 := bstep (se 1 (by rfl) ⟨2187710, by rfl⟩ : syracuseStep 2916947 = 4375421) B4375421
theorem B1944631 : Blo 1943435 1944631 := bstep (se 1 (by rfl) ⟨1458473, by rfl⟩ : syracuseStep 1944631 = 2916947) B2916947
theorem B3281573 : Blo 1943435 3281573 := bbase (se 4 (by rfl) ⟨307647, by rfl⟩ : syracuseStep 3281573 = 615295) (by norm_num)
theorem B2187715 : Blo 1943435 2187715 := bstep (se 1 (by rfl) ⟨1640786, by rfl⟩ : syracuseStep 2187715 = 3281573) B3281573
theorem B2916953 : Blo 1943435 2916953 := bstep (se 2 (by rfl) ⟨1093857, by rfl⟩ : syracuseStep 2916953 = 2187715) B2187715
theorem B1944635 : Blo 1943435 1944635 := bstep (se 1 (by rfl) ⟨1458476, by rfl⟩ : syracuseStep 1944635 = 2916953) B2916953
theorem B2076625 : Blo 1943435 2076625 := bbase (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) (by norm_num)
theorem B2768833 : Blo 1943435 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B14767109 : Blo 1943435 14767109 := bstep (se 4 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 14767109 = 2768833) B2768833
theorem B9844739 : Blo 1943435 9844739 := bstep (se 1 (by rfl) ⟨7383554, by rfl⟩ : syracuseStep 9844739 = 14767109) B14767109
theorem B6563159 : Blo 1943435 6563159 := bstep (se 1 (by rfl) ⟨4922369, by rfl⟩ : syracuseStep 6563159 = 9844739) B9844739
theorem B4375439 : Blo 1943435 4375439 := bstep (se 1 (by rfl) ⟨3281579, by rfl⟩ : syracuseStep 4375439 = 6563159) B6563159
theorem B2916959 : Blo 1943435 2916959 := bstep (se 1 (by rfl) ⟨2187719, by rfl⟩ : syracuseStep 2916959 = 4375439) B4375439
theorem B1944639 : Blo 1943435 1944639 := bstep (se 1 (by rfl) ⟨1458479, by rfl⟩ : syracuseStep 1944639 = 2916959) B2916959
theorem B2916965 : Blo 1943435 2916965 := bbase (se 4 (by rfl) ⟨273465, by rfl⟩ : syracuseStep 2916965 = 546931) (by norm_num)
theorem B1944643 : Blo 1943435 1944643 := bstep (se 1 (by rfl) ⟨1458482, by rfl⟩ : syracuseStep 1944643 = 2916965) B2916965
theorem B2768845 : Blo 1943435 2768845 := bbase (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) (by norm_num)
theorem B3691793 : Blo 1943435 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B2461195 : Blo 1943435 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B3281593 : Blo 1943435 3281593 := bstep (se 2 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 3281593 = 2461195) B2461195
theorem B4375457 : Blo 1943435 4375457 := bstep (se 2 (by rfl) ⟨1640796, by rfl⟩ : syracuseStep 4375457 = 3281593) B3281593
theorem B2916971 : Blo 1943435 2916971 := bstep (se 1 (by rfl) ⟨2187728, by rfl⟩ : syracuseStep 2916971 = 4375457) B4375457
theorem B1944647 : Blo 1943435 1944647 := bstep (se 1 (by rfl) ⟨1458485, by rfl⟩ : syracuseStep 1944647 = 2916971) B2916971
theorem B2187733 : Blo 1943435 2187733 := bbase (se 7 (by rfl) ⟨25637, by rfl⟩ : syracuseStep 2187733 = 51275) (by norm_num)
theorem B2916977 : Blo 1943435 2916977 := bstep (se 2 (by rfl) ⟨1093866, by rfl⟩ : syracuseStep 2916977 = 2187733) B2187733
theorem B1944651 : Blo 1943435 1944651 := bstep (se 1 (by rfl) ⟨1458488, by rfl⟩ : syracuseStep 1944651 = 2916977) B2916977
theorem B2461205 : Blo 1943435 2461205 := bbase (se 6 (by rfl) ⟨57684, by rfl⟩ : syracuseStep 2461205 = 115369) (by norm_num)
theorem B6563213 : Blo 1943435 6563213 := bstep (se 3 (by rfl) ⟨1230602, by rfl⟩ : syracuseStep 6563213 = 2461205) B2461205
theorem B4375475 : Blo 1943435 4375475 := bstep (se 1 (by rfl) ⟨3281606, by rfl⟩ : syracuseStep 4375475 = 6563213) B6563213
theorem B2916983 : Blo 1943435 2916983 := bstep (se 1 (by rfl) ⟨2187737, by rfl⟩ : syracuseStep 2916983 = 4375475) B4375475
theorem B1944655 : Blo 1943435 1944655 := bstep (se 1 (by rfl) ⟨1458491, by rfl⟩ : syracuseStep 1944655 = 2916983) B2916983
theorem B2916989 : Blo 1943435 2916989 := bbase (se 3 (by rfl) ⟨546935, by rfl⟩ : syracuseStep 2916989 = 1093871) (by norm_num)
theorem B1944659 : Blo 1943435 1944659 := bstep (se 1 (by rfl) ⟨1458494, by rfl⟩ : syracuseStep 1944659 = 2916989) B2916989
theorem B4375493 : Blo 1943435 4375493 := bbase (se 4 (by rfl) ⟨410202, by rfl⟩ : syracuseStep 4375493 = 820405) (by norm_num)
theorem B2916995 : Blo 1943435 2916995 := bstep (se 1 (by rfl) ⟨2187746, by rfl⟩ : syracuseStep 2916995 = 4375493) B4375493
theorem B1944663 : Blo 1943435 1944663 := bstep (se 1 (by rfl) ⟨1458497, by rfl⟩ : syracuseStep 1944663 = 2916995) B2916995
theorem B2217601 : Blo 1943435 2217601 := bbase (se 2 (by rfl) ⟨831600, by rfl⟩ : syracuseStep 2217601 = 1663201) (by norm_num)
theorem B11827205 : Blo 1943435 11827205 := bstep (se 4 (by rfl) ⟨1108800, by rfl⟩ : syracuseStep 11827205 = 2217601) B2217601
theorem B7884803 : Blo 1943435 7884803 := bstep (se 1 (by rfl) ⟨5913602, by rfl⟩ : syracuseStep 7884803 = 11827205) B11827205
theorem B5256535 : Blo 1943435 5256535 := bstep (se 1 (by rfl) ⟨3942401, by rfl⟩ : syracuseStep 5256535 = 7884803) B7884803
theorem B7008713 : Blo 1943435 7008713 := bstep (se 2 (by rfl) ⟨2628267, by rfl⟩ : syracuseStep 7008713 = 5256535) B5256535
theorem B4672475 : Blo 1943435 4672475 := bstep (se 1 (by rfl) ⟨3504356, by rfl⟩ : syracuseStep 4672475 = 7008713) B7008713
theorem B3114983 : Blo 1943435 3114983 := bstep (se 1 (by rfl) ⟨2336237, by rfl⟩ : syracuseStep 3114983 = 4672475) B4672475
theorem B8306621 : Blo 1943435 8306621 := bstep (se 3 (by rfl) ⟨1557491, by rfl⟩ : syracuseStep 8306621 = 3114983) B3114983
theorem B5537747 : Blo 1943435 5537747 := bstep (se 1 (by rfl) ⟨4153310, by rfl⟩ : syracuseStep 5537747 = 8306621) B8306621
theorem B3691831 : Blo 1943435 3691831 := bstep (se 1 (by rfl) ⟨2768873, by rfl⟩ : syracuseStep 3691831 = 5537747) B5537747
theorem B4922441 : Blo 1943435 4922441 := bstep (se 2 (by rfl) ⟨1845915, by rfl⟩ : syracuseStep 4922441 = 3691831) B3691831
theorem B3281627 : Blo 1943435 3281627 := bstep (se 1 (by rfl) ⟨2461220, by rfl⟩ : syracuseStep 3281627 = 4922441) B4922441
theorem B2187751 : Blo 1943435 2187751 := bstep (se 1 (by rfl) ⟨1640813, by rfl⟩ : syracuseStep 2187751 = 3281627) B3281627
theorem B2917001 : Blo 1943435 2917001 := bstep (se 2 (by rfl) ⟨1093875, by rfl⟩ : syracuseStep 2917001 = 2187751) B2187751
theorem B1944667 : Blo 1943435 1944667 := bstep (se 1 (by rfl) ⟨1458500, by rfl⟩ : syracuseStep 1944667 = 2917001) B2917001
theorem B9844901 : Blo 1943435 9844901 := bbase (se 4 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 9844901 = 1845919) (by norm_num)
theorem B6563267 : Blo 1943435 6563267 := bstep (se 1 (by rfl) ⟨4922450, by rfl⟩ : syracuseStep 6563267 = 9844901) B9844901
theorem B4375511 : Blo 1943435 4375511 := bstep (se 1 (by rfl) ⟨3281633, by rfl⟩ : syracuseStep 4375511 = 6563267) B6563267
theorem B2917007 : Blo 1943435 2917007 := bstep (se 1 (by rfl) ⟨2187755, by rfl⟩ : syracuseStep 2917007 = 4375511) B4375511
theorem B1944671 : Blo 1943435 1944671 := bstep (se 1 (by rfl) ⟨1458503, by rfl⟩ : syracuseStep 1944671 = 2917007) B2917007
theorem B2917013 : Blo 1943435 2917013 := bbase (se 6 (by rfl) ⟨68367, by rfl⟩ : syracuseStep 2917013 = 136735) (by norm_num)
theorem B1944675 : Blo 1943435 1944675 := bstep (se 1 (by rfl) ⟨1458506, by rfl⟩ : syracuseStep 1944675 = 2917013) B2917013
theorem B7690069 : Blo 1943435 7690069 := bbase (se 9 (by rfl) ⟨22529, by rfl⟩ : syracuseStep 7690069 = 45059) (by norm_num)
theorem B41013701 : Blo 1943435 41013701 := bstep (se 4 (by rfl) ⟨3845034, by rfl⟩ : syracuseStep 41013701 = 7690069) B7690069
theorem B27342467 : Blo 1943435 27342467 := bstep (se 1 (by rfl) ⟨20506850, by rfl⟩ : syracuseStep 27342467 = 41013701) B41013701
theorem B18228311 : Blo 1943435 18228311 := bstep (se 1 (by rfl) ⟨13671233, by rfl⟩ : syracuseStep 18228311 = 27342467) B27342467
theorem B12152207 : Blo 1943435 12152207 := bstep (se 1 (by rfl) ⟨9114155, by rfl⟩ : syracuseStep 12152207 = 18228311) B18228311
theorem B8101471 : Blo 1943435 8101471 := bstep (se 1 (by rfl) ⟨6076103, by rfl⟩ : syracuseStep 8101471 = 12152207) B12152207
theorem B10801961 : Blo 1943435 10801961 := bstep (se 2 (by rfl) ⟨4050735, by rfl⟩ : syracuseStep 10801961 = 8101471) B8101471
theorem B7201307 : Blo 1943435 7201307 := bstep (se 1 (by rfl) ⟨5400980, by rfl⟩ : syracuseStep 7201307 = 10801961) B10801961
theorem B4800871 : Blo 1943435 4800871 := bstep (se 1 (by rfl) ⟨3600653, by rfl⟩ : syracuseStep 4800871 = 7201307) B7201307
theorem B6401161 : Blo 1943435 6401161 := bstep (se 2 (by rfl) ⟨2400435, by rfl⟩ : syracuseStep 6401161 = 4800871) B4800871
theorem B8534881 : Blo 1943435 8534881 := bstep (se 2 (by rfl) ⟨3200580, by rfl⟩ : syracuseStep 8534881 = 6401161) B6401161
theorem B11379841 : Blo 1943435 11379841 := bstep (se 2 (by rfl) ⟨4267440, by rfl⟩ : syracuseStep 11379841 = 8534881) B8534881
theorem B60692485 : Blo 1943435 60692485 := bstep (se 4 (by rfl) ⟨5689920, by rfl⟩ : syracuseStep 60692485 = 11379841) B11379841
theorem B80923313 : Blo 1943435 80923313 := bstep (se 2 (by rfl) ⟨30346242, by rfl⟩ : syracuseStep 80923313 = 60692485) B60692485
theorem B53948875 : Blo 1943435 53948875 := bstep (se 1 (by rfl) ⟨40461656, by rfl⟩ : syracuseStep 53948875 = 80923313) B80923313
theorem B71931833 : Blo 1943435 71931833 := bstep (se 2 (by rfl) ⟨26974437, by rfl⟩ : syracuseStep 71931833 = 53948875) B53948875
theorem B47954555 : Blo 1943435 47954555 := bstep (se 1 (by rfl) ⟨35965916, by rfl⟩ : syracuseStep 47954555 = 71931833) B71931833
theorem B31969703 : Blo 1943435 31969703 := bstep (se 1 (by rfl) ⟨23977277, by rfl⟩ : syracuseStep 31969703 = 47954555) B47954555
theorem B21313135 : Blo 1943435 21313135 := bstep (se 1 (by rfl) ⟨15984851, by rfl⟩ : syracuseStep 21313135 = 31969703) B31969703
theorem B28417513 : Blo 1943435 28417513 := bstep (se 2 (by rfl) ⟨10656567, by rfl⟩ : syracuseStep 28417513 = 21313135) B21313135
theorem B37890017 : Blo 1943435 37890017 := bstep (se 2 (by rfl) ⟨14208756, by rfl⟩ : syracuseStep 37890017 = 28417513) B28417513
theorem B25260011 : Blo 1943435 25260011 := bstep (se 1 (by rfl) ⟨18945008, by rfl⟩ : syracuseStep 25260011 = 37890017) B37890017
theorem B16840007 : Blo 1943435 16840007 := bstep (se 1 (by rfl) ⟨12630005, by rfl⟩ : syracuseStep 16840007 = 25260011) B25260011
theorem B11226671 : Blo 1943435 11226671 := bstep (se 1 (by rfl) ⟨8420003, by rfl⟩ : syracuseStep 11226671 = 16840007) B16840007
theorem B7484447 : Blo 1943435 7484447 := bstep (se 1 (by rfl) ⟨5613335, by rfl⟩ : syracuseStep 7484447 = 11226671) B11226671
theorem B19958525 : Blo 1943435 19958525 := bstep (se 3 (by rfl) ⟨3742223, by rfl⟩ : syracuseStep 19958525 = 7484447) B7484447
theorem B13305683 : Blo 1943435 13305683 := bstep (se 1 (by rfl) ⟨9979262, by rfl⟩ : syracuseStep 13305683 = 19958525) B19958525
theorem B8870455 : Blo 1943435 8870455 := bstep (se 1 (by rfl) ⟨6652841, by rfl⟩ : syracuseStep 8870455 = 13305683) B13305683
theorem B47309093 : Blo 1943435 47309093 := bstep (se 4 (by rfl) ⟨4435227, by rfl⟩ : syracuseStep 47309093 = 8870455) B8870455
theorem B31539395 : Blo 1943435 31539395 := bstep (se 1 (by rfl) ⟨23654546, by rfl⟩ : syracuseStep 31539395 = 47309093) B47309093
theorem B21026263 : Blo 1943435 21026263 := bstep (se 1 (by rfl) ⟨15769697, by rfl⟩ : syracuseStep 21026263 = 31539395) B31539395
theorem B28035017 : Blo 1943435 28035017 := bstep (se 2 (by rfl) ⟨10513131, by rfl⟩ : syracuseStep 28035017 = 21026263) B21026263
theorem B18690011 : Blo 1943435 18690011 := bstep (se 1 (by rfl) ⟨14017508, by rfl⟩ : syracuseStep 18690011 = 28035017) B28035017
theorem B12460007 : Blo 1943435 12460007 := bstep (se 1 (by rfl) ⟨9345005, by rfl⟩ : syracuseStep 12460007 = 18690011) B18690011
theorem B8306671 : Blo 1943435 8306671 := bstep (se 1 (by rfl) ⟨6230003, by rfl⟩ : syracuseStep 8306671 = 12460007) B12460007
theorem B11075561 : Blo 1943435 11075561 := bstep (se 2 (by rfl) ⟨4153335, by rfl⟩ : syracuseStep 11075561 = 8306671) B8306671
theorem B7383707 : Blo 1943435 7383707 := bstep (se 1 (by rfl) ⟨5537780, by rfl⟩ : syracuseStep 7383707 = 11075561) B11075561
theorem B4922471 : Blo 1943435 4922471 := bstep (se 1 (by rfl) ⟨3691853, by rfl⟩ : syracuseStep 4922471 = 7383707) B7383707
theorem B3281647 : Blo 1943435 3281647 := bstep (se 1 (by rfl) ⟨2461235, by rfl⟩ : syracuseStep 3281647 = 4922471) B4922471
theorem B4375529 : Blo 1943435 4375529 := bstep (se 2 (by rfl) ⟨1640823, by rfl⟩ : syracuseStep 4375529 = 3281647) B3281647
theorem B2917019 : Blo 1943435 2917019 := bstep (se 1 (by rfl) ⟨2187764, by rfl⟩ : syracuseStep 2917019 = 4375529) B4375529
theorem B1944679 : Blo 1943435 1944679 := bstep (se 1 (by rfl) ⟨1458509, by rfl⟩ : syracuseStep 1944679 = 2917019) B2917019
theorem B2187769 : Blo 1943435 2187769 := bbase (se 2 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 2187769 = 1640827) (by norm_num)
theorem B2917025 : Blo 1943435 2917025 := bstep (se 2 (by rfl) ⟨1093884, by rfl⟩ : syracuseStep 2917025 = 2187769) B2187769
theorem B1944683 : Blo 1943435 1944683 := bstep (se 1 (by rfl) ⟨1458512, by rfl⟩ : syracuseStep 1944683 = 2917025) B2917025
theorem B2336261 : Blo 1943435 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B6230029 : Blo 1943435 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B8306705 : Blo 1943435 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B5537803 : Blo 1943435 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B7383737 : Blo 1943435 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B4922491 : Blo 1943435 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B6563321 : Blo 1943435 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B4375547 : Blo 1943435 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B2917031 : Blo 1943435 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B1944687 : Blo 1943435 1944687 := bstep (se 1 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 1944687 = 2917031) B2917031
theorem B2917037 : Blo 1943435 2917037 := bbase (se 3 (by rfl) ⟨546944, by rfl⟩ : syracuseStep 2917037 = 1093889) (by norm_num)
theorem B1944691 : Blo 1943435 1944691 := bstep (se 1 (by rfl) ⟨1458518, by rfl⟩ : syracuseStep 1944691 = 2917037) B2917037
theorem B4375565 : Blo 1943435 4375565 := bbase (se 3 (by rfl) ⟨820418, by rfl⟩ : syracuseStep 4375565 = 1640837) (by norm_num)
theorem B2917043 : Blo 1943435 2917043 := bstep (se 1 (by rfl) ⟨2187782, by rfl⟩ : syracuseStep 2917043 = 4375565) B4375565
theorem B1944695 : Blo 1943435 1944695 := bstep (se 1 (by rfl) ⟨1458521, by rfl⟩ : syracuseStep 1944695 = 2917043) B2917043
theorem B2461261 : Blo 1943435 2461261 := bbase (se 3 (by rfl) ⟨461486, by rfl⟩ : syracuseStep 2461261 = 922973) (by norm_num)
theorem B3281681 : Blo 1943435 3281681 := bstep (se 2 (by rfl) ⟨1230630, by rfl⟩ : syracuseStep 3281681 = 2461261) B2461261
theorem B2187787 : Blo 1943435 2187787 := bstep (se 1 (by rfl) ⟨1640840, by rfl⟩ : syracuseStep 2187787 = 3281681) B3281681
theorem B2917049 : Blo 1943435 2917049 := bstep (se 2 (by rfl) ⟨1093893, by rfl⟩ : syracuseStep 2917049 = 2187787) B2187787
theorem B1944699 : Blo 1943435 1944699 := bstep (se 1 (by rfl) ⟨1458524, by rfl⟩ : syracuseStep 1944699 = 2917049) B2917049
theorem B20507093 : Blo 1943435 20507093 := bbase (se 7 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 20507093 = 480635) (by norm_num)
theorem B13671395 : Blo 1943435 13671395 := bstep (se 1 (by rfl) ⟨10253546, by rfl⟩ : syracuseStep 13671395 = 20507093) B20507093
theorem B9114263 : Blo 1943435 9114263 := bstep (se 1 (by rfl) ⟨6835697, by rfl⟩ : syracuseStep 9114263 = 13671395) B13671395
theorem B6076175 : Blo 1943435 6076175 := bstep (se 1 (by rfl) ⟨4557131, by rfl⟩ : syracuseStep 6076175 = 9114263) B9114263
theorem B16203133 : Blo 1943435 16203133 := bstep (se 3 (by rfl) ⟨3038087, by rfl⟩ : syracuseStep 16203133 = 6076175) B6076175
theorem B21604177 : Blo 1943435 21604177 := bstep (se 2 (by rfl) ⟨8101566, by rfl⟩ : syracuseStep 21604177 = 16203133) B16203133
theorem B115222277 : Blo 1943435 115222277 := bstep (se 4 (by rfl) ⟨10802088, by rfl⟩ : syracuseStep 115222277 = 21604177) B21604177
theorem B76814851 : Blo 1943435 76814851 := bstep (se 1 (by rfl) ⟨57611138, by rfl⟩ : syracuseStep 76814851 = 115222277) B115222277
theorem B102419801 : Blo 1943435 102419801 := bstep (se 2 (by rfl) ⟨38407425, by rfl⟩ : syracuseStep 102419801 = 76814851) B76814851
theorem B68279867 : Blo 1943435 68279867 := bstep (se 1 (by rfl) ⟨51209900, by rfl⟩ : syracuseStep 68279867 = 102419801) B102419801
theorem B45519911 : Blo 1943435 45519911 := bstep (se 1 (by rfl) ⟨34139933, by rfl⟩ : syracuseStep 45519911 = 68279867) B68279867
theorem B30346607 : Blo 1943435 30346607 := bstep (se 1 (by rfl) ⟨22759955, by rfl⟩ : syracuseStep 30346607 = 45519911) B45519911
theorem B80924285 : Blo 1943435 80924285 := bstep (se 3 (by rfl) ⟨15173303, by rfl⟩ : syracuseStep 80924285 = 30346607) B30346607
theorem B215798093 : Blo 1943435 215798093 := bstep (se 3 (by rfl) ⟨40462142, by rfl⟩ : syracuseStep 215798093 = 80924285) B80924285
theorem B143865395 : Blo 1943435 143865395 := bstep (se 1 (by rfl) ⟨107899046, by rfl⟩ : syracuseStep 143865395 = 215798093) B215798093
theorem B95910263 : Blo 1943435 95910263 := bstep (se 1 (by rfl) ⟨71932697, by rfl⟩ : syracuseStep 95910263 = 143865395) B143865395
theorem B63940175 : Blo 1943435 63940175 := bstep (se 1 (by rfl) ⟨47955131, by rfl⟩ : syracuseStep 63940175 = 95910263) B95910263
theorem B42626783 : Blo 1943435 42626783 := bstep (se 1 (by rfl) ⟨31970087, by rfl⟩ : syracuseStep 42626783 = 63940175) B63940175
theorem B113671421 : Blo 1943435 113671421 := bstep (se 3 (by rfl) ⟨21313391, by rfl⟩ : syracuseStep 113671421 = 42626783) B42626783
theorem B75780947 : Blo 1943435 75780947 := bstep (se 1 (by rfl) ⟨56835710, by rfl⟩ : syracuseStep 75780947 = 113671421) B113671421
theorem B50520631 : Blo 1943435 50520631 := bstep (se 1 (by rfl) ⟨37890473, by rfl⟩ : syracuseStep 50520631 = 75780947) B75780947
theorem B67360841 : Blo 1943435 67360841 := bstep (se 2 (by rfl) ⟨25260315, by rfl⟩ : syracuseStep 67360841 = 50520631) B50520631
theorem B44907227 : Blo 1943435 44907227 := bstep (se 1 (by rfl) ⟨33680420, by rfl⟩ : syracuseStep 44907227 = 67360841) B67360841
theorem B29938151 : Blo 1943435 29938151 := bstep (se 1 (by rfl) ⟨22453613, by rfl⟩ : syracuseStep 29938151 = 44907227) B44907227
theorem B19958767 : Blo 1943435 19958767 := bstep (se 1 (by rfl) ⟨14969075, by rfl⟩ : syracuseStep 19958767 = 29938151) B29938151
theorem B106446757 : Blo 1943435 106446757 := bstep (se 4 (by rfl) ⟨9979383, by rfl⟩ : syracuseStep 106446757 = 19958767) B19958767
theorem B141929009 : Blo 1943435 141929009 := bstep (se 2 (by rfl) ⟨53223378, by rfl⟩ : syracuseStep 141929009 = 106446757) B106446757
theorem B94619339 : Blo 1943435 94619339 := bstep (se 1 (by rfl) ⟨70964504, by rfl⟩ : syracuseStep 94619339 = 141929009) B141929009
theorem B63079559 : Blo 1943435 63079559 := bstep (se 1 (by rfl) ⟨47309669, by rfl⟩ : syracuseStep 63079559 = 94619339) B94619339
theorem B42053039 : Blo 1943435 42053039 := bstep (se 1 (by rfl) ⟨31539779, by rfl⟩ : syracuseStep 42053039 = 63079559) B63079559
theorem B28035359 : Blo 1943435 28035359 := bstep (se 1 (by rfl) ⟨21026519, by rfl⟩ : syracuseStep 28035359 = 42053039) B42053039
theorem B18690239 : Blo 1943435 18690239 := bstep (se 1 (by rfl) ⟨14017679, by rfl⟩ : syracuseStep 18690239 = 28035359) B28035359
theorem B12460159 : Blo 1943435 12460159 := bstep (se 1 (by rfl) ⟨9345119, by rfl⟩ : syracuseStep 12460159 = 18690239) B18690239
theorem B16613545 : Blo 1943435 16613545 := bstep (se 2 (by rfl) ⟨6230079, by rfl⟩ : syracuseStep 16613545 = 12460159) B12460159
theorem B22151393 : Blo 1943435 22151393 := bstep (se 2 (by rfl) ⟨8306772, by rfl⟩ : syracuseStep 22151393 = 16613545) B16613545
theorem B14767595 : Blo 1943435 14767595 := bstep (se 1 (by rfl) ⟨11075696, by rfl⟩ : syracuseStep 14767595 = 22151393) B22151393
theorem B9845063 : Blo 1943435 9845063 := bstep (se 1 (by rfl) ⟨7383797, by rfl⟩ : syracuseStep 9845063 = 14767595) B14767595
theorem B6563375 : Blo 1943435 6563375 := bstep (se 1 (by rfl) ⟨4922531, by rfl⟩ : syracuseStep 6563375 = 9845063) B9845063
theorem B4375583 : Blo 1943435 4375583 := bstep (se 1 (by rfl) ⟨3281687, by rfl⟩ : syracuseStep 4375583 = 6563375) B6563375
theorem B2917055 : Blo 1943435 2917055 := bstep (se 1 (by rfl) ⟨2187791, by rfl⟩ : syracuseStep 2917055 = 4375583) B4375583
theorem B1944703 : Blo 1943435 1944703 := bstep (se 1 (by rfl) ⟨1458527, by rfl⟩ : syracuseStep 1944703 = 2917055) B2917055
theorem B2917061 : Blo 1943435 2917061 := bbase (se 4 (by rfl) ⟨273474, by rfl⟩ : syracuseStep 2917061 = 546949) (by norm_num)
theorem B1944707 : Blo 1943435 1944707 := bstep (se 1 (by rfl) ⟨1458530, by rfl⟩ : syracuseStep 1944707 = 2917061) B2917061
theorem B3281701 : Blo 1943435 3281701 := bbase (se 4 (by rfl) ⟨307659, by rfl⟩ : syracuseStep 3281701 = 615319) (by norm_num)
theorem B4375601 : Blo 1943435 4375601 := bstep (se 2 (by rfl) ⟨1640850, by rfl⟩ : syracuseStep 4375601 = 3281701) B3281701
theorem B2917067 : Blo 1943435 2917067 := bstep (se 1 (by rfl) ⟨2187800, by rfl⟩ : syracuseStep 2917067 = 4375601) B4375601
theorem B1944711 : Blo 1943435 1944711 := bstep (se 1 (by rfl) ⟨1458533, by rfl⟩ : syracuseStep 1944711 = 2917067) B2917067
theorem B2187805 : Blo 1943435 2187805 := bbase (se 3 (by rfl) ⟨410213, by rfl⟩ : syracuseStep 2187805 = 820427) (by norm_num)
theorem B2917073 : Blo 1943435 2917073 := bstep (se 2 (by rfl) ⟨1093902, by rfl⟩ : syracuseStep 2917073 = 2187805) B2187805
theorem B1944715 : Blo 1943435 1944715 := bstep (se 1 (by rfl) ⟨1458536, by rfl⟩ : syracuseStep 1944715 = 2917073) B2917073
theorem B6563429 : Blo 1943435 6563429 := bbase (se 4 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 6563429 = 1230643) (by norm_num)
theorem B4375619 : Blo 1943435 4375619 := bstep (se 1 (by rfl) ⟨3281714, by rfl⟩ : syracuseStep 4375619 = 6563429) B6563429
theorem B2917079 : Blo 1943435 2917079 := bstep (se 1 (by rfl) ⟨2187809, by rfl⟩ : syracuseStep 2917079 = 4375619) B4375619
theorem B1944719 : Blo 1943435 1944719 := bstep (se 1 (by rfl) ⟨1458539, by rfl⟩ : syracuseStep 1944719 = 2917079) B2917079
theorem B2917085 : Blo 1943435 2917085 := bbase (se 3 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 2917085 = 1093907) (by norm_num)
theorem B1944723 : Blo 1943435 1944723 := bstep (se 1 (by rfl) ⟨1458542, by rfl⟩ : syracuseStep 1944723 = 2917085) B2917085
theorem B4375637 : Blo 1943435 4375637 := bbase (se 8 (by rfl) ⟨25638, by rfl⟩ : syracuseStep 4375637 = 51277) (by norm_num)
theorem B2917091 : Blo 1943435 2917091 := bstep (se 1 (by rfl) ⟨2187818, by rfl⟩ : syracuseStep 2917091 = 4375637) B4375637
theorem B1944727 : Blo 1943435 1944727 := bstep (se 1 (by rfl) ⟨1458545, by rfl⟩ : syracuseStep 1944727 = 2917091) B2917091
theorem B3742325 : Blo 1943435 3742325 := bbase (se 5 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 3742325 = 350843) (by norm_num)
theorem B2494883 : Blo 1943435 2494883 := bstep (se 1 (by rfl) ⟨1871162, by rfl⟩ : syracuseStep 2494883 = 3742325) B3742325
theorem B6653021 : Blo 1943435 6653021 := bstep (se 3 (by rfl) ⟨1247441, by rfl⟩ : syracuseStep 6653021 = 2494883) B2494883
theorem B17741389 : Blo 1943435 17741389 := bstep (se 3 (by rfl) ⟨3326510, by rfl⟩ : syracuseStep 17741389 = 6653021) B6653021
theorem B23655185 : Blo 1943435 23655185 := bstep (se 2 (by rfl) ⟨8870694, by rfl⟩ : syracuseStep 23655185 = 17741389) B17741389
theorem B15770123 : Blo 1943435 15770123 := bstep (se 1 (by rfl) ⟨11827592, by rfl⟩ : syracuseStep 15770123 = 23655185) B23655185
theorem B10513415 : Blo 1943435 10513415 := bstep (se 1 (by rfl) ⟨7885061, by rfl⟩ : syracuseStep 10513415 = 15770123) B15770123
theorem B7008943 : Blo 1943435 7008943 := bstep (se 1 (by rfl) ⟨5256707, by rfl⟩ : syracuseStep 7008943 = 10513415) B10513415
theorem B9345257 : Blo 1943435 9345257 := bstep (se 2 (by rfl) ⟨3504471, by rfl⟩ : syracuseStep 9345257 = 7008943) B7008943
theorem B6230171 : Blo 1943435 6230171 := bstep (se 1 (by rfl) ⟨4672628, by rfl⟩ : syracuseStep 6230171 = 9345257) B9345257
theorem B4153447 : Blo 1943435 4153447 := bstep (se 1 (by rfl) ⟨3115085, by rfl⟩ : syracuseStep 4153447 = 6230171) B6230171
theorem B5537929 : Blo 1943435 5537929 := bstep (se 2 (by rfl) ⟨2076723, by rfl⟩ : syracuseStep 5537929 = 4153447) B4153447
theorem B7383905 : Blo 1943435 7383905 := bstep (se 2 (by rfl) ⟨2768964, by rfl⟩ : syracuseStep 7383905 = 5537929) B5537929
theorem B4922603 : Blo 1943435 4922603 := bstep (se 1 (by rfl) ⟨3691952, by rfl⟩ : syracuseStep 4922603 = 7383905) B7383905
theorem B3281735 : Blo 1943435 3281735 := bstep (se 1 (by rfl) ⟨2461301, by rfl⟩ : syracuseStep 3281735 = 4922603) B4922603
theorem B2187823 : Blo 1943435 2187823 := bstep (se 1 (by rfl) ⟨1640867, by rfl⟩ : syracuseStep 2187823 = 3281735) B3281735
theorem B2917097 : Blo 1943435 2917097 := bstep (se 2 (by rfl) ⟨1093911, by rfl⟩ : syracuseStep 2917097 = 2187823) B2187823
theorem B1944731 : Blo 1943435 1944731 := bstep (se 1 (by rfl) ⟨1458548, by rfl⟩ : syracuseStep 1944731 = 2917097) B2917097
theorem B4736389 : Blo 1943435 4736389 := bbase (se 4 (by rfl) ⟨444036, by rfl⟩ : syracuseStep 4736389 = 888073) (by norm_num)
theorem B6315185 : Blo 1943435 6315185 := bstep (se 2 (by rfl) ⟨2368194, by rfl⟩ : syracuseStep 6315185 = 4736389) B4736389
theorem B16840493 : Blo 1943435 16840493 := bstep (se 3 (by rfl) ⟨3157592, by rfl⟩ : syracuseStep 16840493 = 6315185) B6315185
theorem B11226995 : Blo 1943435 11226995 := bstep (se 1 (by rfl) ⟨8420246, by rfl⟩ : syracuseStep 11226995 = 16840493) B16840493
theorem B7484663 : Blo 1943435 7484663 := bstep (se 1 (by rfl) ⟨5613497, by rfl⟩ : syracuseStep 7484663 = 11226995) B11226995
theorem B4989775 : Blo 1943435 4989775 := bstep (se 1 (by rfl) ⟨3742331, by rfl⟩ : syracuseStep 4989775 = 7484663) B7484663
theorem B6653033 : Blo 1943435 6653033 := bstep (se 2 (by rfl) ⟨2494887, by rfl⟩ : syracuseStep 6653033 = 4989775) B4989775
theorem B4435355 : Blo 1943435 4435355 := bstep (se 1 (by rfl) ⟨3326516, by rfl⟩ : syracuseStep 4435355 = 6653033) B6653033
theorem B11827613 : Blo 1943435 11827613 := bstep (se 3 (by rfl) ⟨2217677, by rfl⟩ : syracuseStep 11827613 = 4435355) B4435355
theorem B7885075 : Blo 1943435 7885075 := bstep (se 1 (by rfl) ⟨5913806, by rfl⟩ : syracuseStep 7885075 = 11827613) B11827613
theorem B10513433 : Blo 1943435 10513433 := bstep (se 2 (by rfl) ⟨3942537, by rfl⟩ : syracuseStep 10513433 = 7885075) B7885075
theorem B28035821 : Blo 1943435 28035821 := bstep (se 3 (by rfl) ⟨5256716, by rfl⟩ : syracuseStep 28035821 = 10513433) B10513433
theorem B18690547 : Blo 1943435 18690547 := bstep (se 1 (by rfl) ⟨14017910, by rfl⟩ : syracuseStep 18690547 = 28035821) B28035821
theorem B24920729 : Blo 1943435 24920729 := bstep (se 2 (by rfl) ⟨9345273, by rfl⟩ : syracuseStep 24920729 = 18690547) B18690547
theorem B16613819 : Blo 1943435 16613819 := bstep (se 1 (by rfl) ⟨12460364, by rfl⟩ : syracuseStep 16613819 = 24920729) B24920729
theorem B11075879 : Blo 1943435 11075879 := bstep (se 1 (by rfl) ⟨8306909, by rfl⟩ : syracuseStep 11075879 = 16613819) B16613819
theorem B7383919 : Blo 1943435 7383919 := bstep (se 1 (by rfl) ⟨5537939, by rfl⟩ : syracuseStep 7383919 = 11075879) B11075879
theorem B9845225 : Blo 1943435 9845225 := bstep (se 2 (by rfl) ⟨3691959, by rfl⟩ : syracuseStep 9845225 = 7383919) B7383919
theorem B6563483 : Blo 1943435 6563483 := bstep (se 1 (by rfl) ⟨4922612, by rfl⟩ : syracuseStep 6563483 = 9845225) B9845225
theorem B4375655 : Blo 1943435 4375655 := bstep (se 1 (by rfl) ⟨3281741, by rfl⟩ : syracuseStep 4375655 = 6563483) B6563483
theorem B2917103 : Blo 1943435 2917103 := bstep (se 1 (by rfl) ⟨2187827, by rfl⟩ : syracuseStep 2917103 = 4375655) B4375655
theorem B1944735 : Blo 1943435 1944735 := bstep (se 1 (by rfl) ⟨1458551, by rfl⟩ : syracuseStep 1944735 = 2917103) B2917103
theorem B2917109 : Blo 1943435 2917109 := bbase (se 5 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 2917109 = 273479) (by norm_num)
theorem B1944739 : Blo 1943435 1944739 := bstep (se 1 (by rfl) ⟨1458554, by rfl⟩ : syracuseStep 1944739 = 2917109) B2917109
theorem B3504493 : Blo 1943435 3504493 := bbase (se 3 (by rfl) ⟨657092, by rfl⟩ : syracuseStep 3504493 = 1314185) (by norm_num)
theorem B4672657 : Blo 1943435 4672657 := bstep (se 2 (by rfl) ⟨1752246, by rfl⟩ : syracuseStep 4672657 = 3504493) B3504493
theorem B6230209 : Blo 1943435 6230209 := bstep (se 2 (by rfl) ⟨2336328, by rfl⟩ : syracuseStep 6230209 = 4672657) B4672657
theorem B8306945 : Blo 1943435 8306945 := bstep (se 2 (by rfl) ⟨3115104, by rfl⟩ : syracuseStep 8306945 = 6230209) B6230209
theorem B5537963 : Blo 1943435 5537963 := bstep (se 1 (by rfl) ⟨4153472, by rfl⟩ : syracuseStep 5537963 = 8306945) B8306945
theorem B3691975 : Blo 1943435 3691975 := bstep (se 1 (by rfl) ⟨2768981, by rfl⟩ : syracuseStep 3691975 = 5537963) B5537963
theorem B4922633 : Blo 1943435 4922633 := bstep (se 2 (by rfl) ⟨1845987, by rfl⟩ : syracuseStep 4922633 = 3691975) B3691975
theorem B3281755 : Blo 1943435 3281755 := bstep (se 1 (by rfl) ⟨2461316, by rfl⟩ : syracuseStep 3281755 = 4922633) B4922633
theorem B4375673 : Blo 1943435 4375673 := bstep (se 2 (by rfl) ⟨1640877, by rfl⟩ : syracuseStep 4375673 = 3281755) B3281755
theorem B2917115 : Blo 1943435 2917115 := bstep (se 1 (by rfl) ⟨2187836, by rfl⟩ : syracuseStep 2917115 = 4375673) B4375673
theorem B1944743 : Blo 1943435 1944743 := bstep (se 1 (by rfl) ⟨1458557, by rfl⟩ : syracuseStep 1944743 = 2917115) B2917115
theorem B2187841 : Blo 1943435 2187841 := bbase (se 2 (by rfl) ⟨820440, by rfl⟩ : syracuseStep 2187841 = 1640881) (by norm_num)
theorem B2917121 : Blo 1943435 2917121 := bstep (se 2 (by rfl) ⟨1093920, by rfl⟩ : syracuseStep 2917121 = 2187841) B2187841
theorem B1944747 : Blo 1943435 1944747 := bstep (se 1 (by rfl) ⟨1458560, by rfl⟩ : syracuseStep 1944747 = 2917121) B2917121
theorem B4922653 : Blo 1943435 4922653 := bbase (se 3 (by rfl) ⟨922997, by rfl⟩ : syracuseStep 4922653 = 1845995) (by norm_num)
theorem B6563537 : Blo 1943435 6563537 := bstep (se 2 (by rfl) ⟨2461326, by rfl⟩ : syracuseStep 6563537 = 4922653) B4922653
theorem B4375691 : Blo 1943435 4375691 := bstep (se 1 (by rfl) ⟨3281768, by rfl⟩ : syracuseStep 4375691 = 6563537) B6563537
theorem B2917127 : Blo 1943435 2917127 := bstep (se 1 (by rfl) ⟨2187845, by rfl⟩ : syracuseStep 2917127 = 4375691) B4375691
theorem B1944751 : Blo 1943435 1944751 := bstep (se 1 (by rfl) ⟨1458563, by rfl⟩ : syracuseStep 1944751 = 2917127) B2917127
theorem B2917133 : Blo 1943435 2917133 := bbase (se 3 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 2917133 = 1093925) (by norm_num)
theorem B1944755 : Blo 1943435 1944755 := bstep (se 1 (by rfl) ⟨1458566, by rfl⟩ : syracuseStep 1944755 = 2917133) B2917133
theorem B4375709 : Blo 1943435 4375709 := bbase (se 3 (by rfl) ⟨820445, by rfl⟩ : syracuseStep 4375709 = 1640891) (by norm_num)
theorem B2917139 : Blo 1943435 2917139 := bstep (se 1 (by rfl) ⟨2187854, by rfl⟩ : syracuseStep 2917139 = 4375709) B4375709
theorem B1944759 : Blo 1943435 1944759 := bstep (se 1 (by rfl) ⟨1458569, by rfl⟩ : syracuseStep 1944759 = 2917139) B2917139
theorem B3281789 : Blo 1943435 3281789 := bbase (se 3 (by rfl) ⟨615335, by rfl⟩ : syracuseStep 3281789 = 1230671) (by norm_num)
theorem B2187859 : Blo 1943435 2187859 := bstep (se 1 (by rfl) ⟨1640894, by rfl⟩ : syracuseStep 2187859 = 3281789) B3281789
theorem B2917145 : Blo 1943435 2917145 := bstep (se 2 (by rfl) ⟨1093929, by rfl⟩ : syracuseStep 2917145 = 2187859) B2187859
theorem B1944763 : Blo 1943435 1944763 := bstep (se 1 (by rfl) ⟨1458572, by rfl⟩ : syracuseStep 1944763 = 2917145) B2917145
theorem B2336357 : Blo 1943435 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B6230285 : Blo 1943435 6230285 := bstep (se 3 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 6230285 = 2336357) B2336357
theorem B4153523 : Blo 1943435 4153523 := bstep (se 1 (by rfl) ⟨3115142, by rfl⟩ : syracuseStep 4153523 = 6230285) B6230285
theorem B11076061 : Blo 1943435 11076061 := bstep (se 3 (by rfl) ⟨2076761, by rfl⟩ : syracuseStep 11076061 = 4153523) B4153523
theorem B14768081 : Blo 1943435 14768081 := bstep (se 2 (by rfl) ⟨5538030, by rfl⟩ : syracuseStep 14768081 = 11076061) B11076061
theorem B9845387 : Blo 1943435 9845387 := bstep (se 1 (by rfl) ⟨7384040, by rfl⟩ : syracuseStep 9845387 = 14768081) B14768081
theorem B6563591 : Blo 1943435 6563591 := bstep (se 1 (by rfl) ⟨4922693, by rfl⟩ : syracuseStep 6563591 = 9845387) B9845387
theorem B4375727 : Blo 1943435 4375727 := bstep (se 1 (by rfl) ⟨3281795, by rfl⟩ : syracuseStep 4375727 = 6563591) B6563591
theorem B2917151 : Blo 1943435 2917151 := bstep (se 1 (by rfl) ⟨2187863, by rfl⟩ : syracuseStep 2917151 = 4375727) B4375727
theorem B1944767 : Blo 1943435 1944767 := bstep (se 1 (by rfl) ⟨1458575, by rfl⟩ : syracuseStep 1944767 = 2917151) B2917151
theorem B2917157 : Blo 1943435 2917157 := bbase (se 4 (by rfl) ⟨273483, by rfl⟩ : syracuseStep 2917157 = 546967) (by norm_num)
theorem B1944771 : Blo 1943435 1944771 := bstep (se 1 (by rfl) ⟨1458578, by rfl⟩ : syracuseStep 1944771 = 2917157) B2917157
theorem B2461357 : Blo 1943435 2461357 := bbase (se 3 (by rfl) ⟨461504, by rfl⟩ : syracuseStep 2461357 = 923009) (by norm_num)
theorem B3281809 : Blo 1943435 3281809 := bstep (se 2 (by rfl) ⟨1230678, by rfl⟩ : syracuseStep 3281809 = 2461357) B2461357
theorem B4375745 : Blo 1943435 4375745 := bstep (se 2 (by rfl) ⟨1640904, by rfl⟩ : syracuseStep 4375745 = 3281809) B3281809
theorem B2917163 : Blo 1943435 2917163 := bstep (se 1 (by rfl) ⟨2187872, by rfl⟩ : syracuseStep 2917163 = 4375745) B4375745
theorem B1944775 : Blo 1943435 1944775 := bstep (se 1 (by rfl) ⟨1458581, by rfl⟩ : syracuseStep 1944775 = 2917163) B2917163
theorem B2187877 : Blo 1943435 2187877 := bbase (se 4 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 2187877 = 410227) (by norm_num)
theorem B2917169 : Blo 1943435 2917169 := bstep (se 2 (by rfl) ⟨1093938, by rfl⟩ : syracuseStep 2917169 = 2187877) B2187877
theorem B1944779 : Blo 1943435 1944779 := bstep (se 1 (by rfl) ⟨1458584, by rfl⟩ : syracuseStep 1944779 = 2917169) B2917169
theorem B2336377 : Blo 1943435 2336377 := bbase (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) (by norm_num)
theorem B3115169 : Blo 1943435 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B2076779 : Blo 1943435 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B5538077 : Blo 1943435 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B3692051 : Blo 1943435 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B2461367 : Blo 1943435 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B6563645 : Blo 1943435 6563645 := bstep (se 3 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 6563645 = 2461367) B2461367
theorem B4375763 : Blo 1943435 4375763 := bstep (se 1 (by rfl) ⟨3281822, by rfl⟩ : syracuseStep 4375763 = 6563645) B6563645
theorem B2917175 : Blo 1943435 2917175 := bstep (se 1 (by rfl) ⟨2187881, by rfl⟩ : syracuseStep 2917175 = 4375763) B4375763
theorem B1944783 : Blo 1943435 1944783 := bstep (se 1 (by rfl) ⟨1458587, by rfl⟩ : syracuseStep 1944783 = 2917175) B2917175
theorem B2917181 : Blo 1943435 2917181 := bbase (se 3 (by rfl) ⟨546971, by rfl⟩ : syracuseStep 2917181 = 1093943) (by norm_num)
theorem B1944787 : Blo 1943435 1944787 := bstep (se 1 (by rfl) ⟨1458590, by rfl⟩ : syracuseStep 1944787 = 2917181) B2917181
theorem B4375781 : Blo 1943435 4375781 := bbase (se 4 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 4375781 = 820459) (by norm_num)
theorem B2917187 : Blo 1943435 2917187 := bstep (se 1 (by rfl) ⟨2187890, by rfl⟩ : syracuseStep 2917187 = 4375781) B4375781
theorem B1944791 : Blo 1943435 1944791 := bstep (se 1 (by rfl) ⟨1458593, by rfl⟩ : syracuseStep 1944791 = 2917187) B2917187
theorem B4922765 : Blo 1943435 4922765 := bbase (se 3 (by rfl) ⟨923018, by rfl⟩ : syracuseStep 4922765 = 1846037) (by norm_num)
theorem B3281843 : Blo 1943435 3281843 := bstep (se 1 (by rfl) ⟨2461382, by rfl⟩ : syracuseStep 3281843 = 4922765) B4922765
theorem B2187895 : Blo 1943435 2187895 := bstep (se 1 (by rfl) ⟨1640921, by rfl⟩ : syracuseStep 2187895 = 3281843) B3281843
theorem B2917193 : Blo 1943435 2917193 := bstep (se 2 (by rfl) ⟨1093947, by rfl⟩ : syracuseStep 2917193 = 2187895) B2187895
theorem B1944795 : Blo 1943435 1944795 := bstep (se 1 (by rfl) ⟨1458596, by rfl⟩ : syracuseStep 1944795 = 2917193) B2917193
theorem B2769061 : Blo 1943435 2769061 := bbase (se 4 (by rfl) ⟨259599, by rfl⟩ : syracuseStep 2769061 = 519199) (by norm_num)
theorem B3692081 : Blo 1943435 3692081 := bstep (se 2 (by rfl) ⟨1384530, by rfl⟩ : syracuseStep 3692081 = 2769061) B2769061
theorem B9845549 : Blo 1943435 9845549 := bstep (se 3 (by rfl) ⟨1846040, by rfl⟩ : syracuseStep 9845549 = 3692081) B3692081
theorem B6563699 : Blo 1943435 6563699 := bstep (se 1 (by rfl) ⟨4922774, by rfl⟩ : syracuseStep 6563699 = 9845549) B9845549
theorem B4375799 : Blo 1943435 4375799 := bstep (se 1 (by rfl) ⟨3281849, by rfl⟩ : syracuseStep 4375799 = 6563699) B6563699
theorem B2917199 : Blo 1943435 2917199 := bstep (se 1 (by rfl) ⟨2187899, by rfl⟩ : syracuseStep 2917199 = 4375799) B4375799
theorem B1944799 : Blo 1943435 1944799 := bstep (se 1 (by rfl) ⟨1458599, by rfl⟩ : syracuseStep 1944799 = 2917199) B2917199
theorem B2917205 : Blo 1943435 2917205 := bbase (se 9 (by rfl) ⟨8546, by rfl⟩ : syracuseStep 2917205 = 17093) (by norm_num)
theorem B1944803 : Blo 1943435 1944803 := bstep (se 1 (by rfl) ⟨1458602, by rfl⟩ : syracuseStep 1944803 = 2917205) B2917205
theorem B3942685 : Blo 1943435 3942685 := bbase (se 3 (by rfl) ⟨739253, by rfl⟩ : syracuseStep 3942685 = 1478507) (by norm_num)
theorem B5256913 : Blo 1943435 5256913 := bstep (se 2 (by rfl) ⟨1971342, by rfl⟩ : syracuseStep 5256913 = 3942685) B3942685
theorem B7009217 : Blo 1943435 7009217 := bstep (se 2 (by rfl) ⟨2628456, by rfl⟩ : syracuseStep 7009217 = 5256913) B5256913
theorem B4672811 : Blo 1943435 4672811 := bstep (se 1 (by rfl) ⟨3504608, by rfl⟩ : syracuseStep 4672811 = 7009217) B7009217
theorem B3115207 : Blo 1943435 3115207 := bstep (se 1 (by rfl) ⟨2336405, by rfl⟩ : syracuseStep 3115207 = 4672811) B4672811
theorem B4153609 : Blo 1943435 4153609 := bstep (se 2 (by rfl) ⟨1557603, by rfl⟩ : syracuseStep 4153609 = 3115207) B3115207
theorem B5538145 : Blo 1943435 5538145 := bstep (se 2 (by rfl) ⟨2076804, by rfl⟩ : syracuseStep 5538145 = 4153609) B4153609
theorem B7384193 : Blo 1943435 7384193 := bstep (se 2 (by rfl) ⟨2769072, by rfl⟩ : syracuseStep 7384193 = 5538145) B5538145
theorem B4922795 : Blo 1943435 4922795 := bstep (se 1 (by rfl) ⟨3692096, by rfl⟩ : syracuseStep 4922795 = 7384193) B7384193
theorem B3281863 : Blo 1943435 3281863 := bstep (se 1 (by rfl) ⟨2461397, by rfl⟩ : syracuseStep 3281863 = 4922795) B4922795
theorem B4375817 : Blo 1943435 4375817 := bstep (se 2 (by rfl) ⟨1640931, by rfl⟩ : syracuseStep 4375817 = 3281863) B3281863
theorem B2917211 : Blo 1943435 2917211 := bstep (se 1 (by rfl) ⟨2187908, by rfl⟩ : syracuseStep 2917211 = 4375817) B4375817
theorem B1944807 : Blo 1943435 1944807 := bstep (se 1 (by rfl) ⟨1458605, by rfl⟩ : syracuseStep 1944807 = 2917211) B2917211
theorem B2187913 : Blo 1943435 2187913 := bbase (se 2 (by rfl) ⟨820467, by rfl⟩ : syracuseStep 2187913 = 1640935) (by norm_num)
theorem B2917217 : Blo 1943435 2917217 := bstep (se 2 (by rfl) ⟨1093956, by rfl⟩ : syracuseStep 2917217 = 2187913) B2187913
theorem B1944811 : Blo 1943435 1944811 := bstep (se 1 (by rfl) ⟨1458608, by rfl⟩ : syracuseStep 1944811 = 2917217) B2917217
theorem B17984213 : Blo 1943435 17984213 := bbase (se 7 (by rfl) ⟨210752, by rfl⟩ : syracuseStep 17984213 = 421505) (by norm_num)
theorem B11989475 : Blo 1943435 11989475 := bstep (se 1 (by rfl) ⟨8992106, by rfl⟩ : syracuseStep 11989475 = 17984213) B17984213
theorem B7992983 : Blo 1943435 7992983 := bstep (se 1 (by rfl) ⟨5994737, by rfl⟩ : syracuseStep 7992983 = 11989475) B11989475
theorem B5328655 : Blo 1943435 5328655 := bstep (se 1 (by rfl) ⟨3996491, by rfl⟩ : syracuseStep 5328655 = 7992983) B7992983
theorem B28419493 : Blo 1943435 28419493 := bstep (se 4 (by rfl) ⟨2664327, by rfl⟩ : syracuseStep 28419493 = 5328655) B5328655
theorem B37892657 : Blo 1943435 37892657 := bstep (se 2 (by rfl) ⟨14209746, by rfl⟩ : syracuseStep 37892657 = 28419493) B28419493
theorem B101047085 : Blo 1943435 101047085 := bstep (se 3 (by rfl) ⟨18946328, by rfl⟩ : syracuseStep 101047085 = 37892657) B37892657
theorem B67364723 : Blo 1943435 67364723 := bstep (se 1 (by rfl) ⟨50523542, by rfl⟩ : syracuseStep 67364723 = 101047085) B101047085
theorem B44909815 : Blo 1943435 44909815 := bstep (se 1 (by rfl) ⟨33682361, by rfl⟩ : syracuseStep 44909815 = 67364723) B67364723
theorem B59879753 : Blo 1943435 59879753 := bstep (se 2 (by rfl) ⟨22454907, by rfl⟩ : syracuseStep 59879753 = 44909815) B44909815
theorem B39919835 : Blo 1943435 39919835 := bstep (se 1 (by rfl) ⟨29939876, by rfl⟩ : syracuseStep 39919835 = 59879753) B59879753
theorem B106452893 : Blo 1943435 106452893 := bstep (se 3 (by rfl) ⟨19959917, by rfl⟩ : syracuseStep 106452893 = 39919835) B39919835
theorem B70968595 : Blo 1943435 70968595 := bstep (se 1 (by rfl) ⟨53226446, by rfl⟩ : syracuseStep 70968595 = 106452893) B106452893
theorem B94624793 : Blo 1943435 94624793 := bstep (se 2 (by rfl) ⟨35484297, by rfl⟩ : syracuseStep 94624793 = 70968595) B70968595
theorem B63083195 : Blo 1943435 63083195 := bstep (se 1 (by rfl) ⟨47312396, by rfl⟩ : syracuseStep 63083195 = 94624793) B94624793
theorem B42055463 : Blo 1943435 42055463 := bstep (se 1 (by rfl) ⟨31541597, by rfl⟩ : syracuseStep 42055463 = 63083195) B63083195
theorem B28036975 : Blo 1943435 28036975 := bstep (se 1 (by rfl) ⟨21027731, by rfl⟩ : syracuseStep 28036975 = 42055463) B42055463
theorem B37382633 : Blo 1943435 37382633 := bstep (se 2 (by rfl) ⟨14018487, by rfl⟩ : syracuseStep 37382633 = 28036975) B28036975
theorem B24921755 : Blo 1943435 24921755 := bstep (se 1 (by rfl) ⟨18691316, by rfl⟩ : syracuseStep 24921755 = 37382633) B37382633
theorem B16614503 : Blo 1943435 16614503 := bstep (se 1 (by rfl) ⟨12460877, by rfl⟩ : syracuseStep 16614503 = 24921755) B24921755
theorem B11076335 : Blo 1943435 11076335 := bstep (se 1 (by rfl) ⟨8307251, by rfl⟩ : syracuseStep 11076335 = 16614503) B16614503
theorem B7384223 : Blo 1943435 7384223 := bstep (se 1 (by rfl) ⟨5538167, by rfl⟩ : syracuseStep 7384223 = 11076335) B11076335
theorem B4922815 : Blo 1943435 4922815 := bstep (se 1 (by rfl) ⟨3692111, by rfl⟩ : syracuseStep 4922815 = 7384223) B7384223
theorem B6563753 : Blo 1943435 6563753 := bstep (se 2 (by rfl) ⟨2461407, by rfl⟩ : syracuseStep 6563753 = 4922815) B4922815
theorem B4375835 : Blo 1943435 4375835 := bstep (se 1 (by rfl) ⟨3281876, by rfl⟩ : syracuseStep 4375835 = 6563753) B6563753
theorem B2917223 : Blo 1943435 2917223 := bstep (se 1 (by rfl) ⟨2187917, by rfl⟩ : syracuseStep 2917223 = 4375835) B4375835
theorem B1944815 : Blo 1943435 1944815 := bstep (se 1 (by rfl) ⟨1458611, by rfl⟩ : syracuseStep 1944815 = 2917223) B2917223
theorem B2917229 : Blo 1943435 2917229 := bbase (se 3 (by rfl) ⟨546980, by rfl⟩ : syracuseStep 2917229 = 1093961) (by norm_num)
theorem B1944819 : Blo 1943435 1944819 := bstep (se 1 (by rfl) ⟨1458614, by rfl⟩ : syracuseStep 1944819 = 2917229) B2917229
theorem B4375853 : Blo 1943435 4375853 := bbase (se 3 (by rfl) ⟨820472, by rfl⟩ : syracuseStep 4375853 = 1640945) (by norm_num)
theorem B2917235 : Blo 1943435 2917235 := bstep (se 1 (by rfl) ⟨2187926, by rfl⟩ : syracuseStep 2917235 = 4375853) B4375853
theorem B1944823 : Blo 1943435 1944823 := bstep (se 1 (by rfl) ⟨1458617, by rfl⟩ : syracuseStep 1944823 = 2917235) B2917235
theorem B4990013 : Blo 1943435 4990013 := bbase (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) (by norm_num)
theorem B3326675 : Blo 1943435 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B8871133 : Blo 1943435 8871133 := bstep (se 3 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 8871133 = 3326675) B3326675
theorem B11828177 : Blo 1943435 11828177 := bstep (se 2 (by rfl) ⟨4435566, by rfl⟩ : syracuseStep 11828177 = 8871133) B8871133
theorem B7885451 : Blo 1943435 7885451 := bstep (se 1 (by rfl) ⟨5914088, by rfl⟩ : syracuseStep 7885451 = 11828177) B11828177
theorem B21027869 : Blo 1943435 21027869 := bstep (se 3 (by rfl) ⟨3942725, by rfl⟩ : syracuseStep 21027869 = 7885451) B7885451
theorem B14018579 : Blo 1943435 14018579 := bstep (se 1 (by rfl) ⟨10513934, by rfl⟩ : syracuseStep 14018579 = 21027869) B21027869
theorem B9345719 : Blo 1943435 9345719 := bstep (se 1 (by rfl) ⟨7009289, by rfl⟩ : syracuseStep 9345719 = 14018579) B14018579
theorem B6230479 : Blo 1943435 6230479 := bstep (se 1 (by rfl) ⟨4672859, by rfl⟩ : syracuseStep 6230479 = 9345719) B9345719
theorem B8307305 : Blo 1943435 8307305 := bstep (se 2 (by rfl) ⟨3115239, by rfl⟩ : syracuseStep 8307305 = 6230479) B6230479
theorem B5538203 : Blo 1943435 5538203 := bstep (se 1 (by rfl) ⟨4153652, by rfl⟩ : syracuseStep 5538203 = 8307305) B8307305
theorem B3692135 : Blo 1943435 3692135 := bstep (se 1 (by rfl) ⟨2769101, by rfl⟩ : syracuseStep 3692135 = 5538203) B5538203
theorem B2461423 : Blo 1943435 2461423 := bstep (se 1 (by rfl) ⟨1846067, by rfl⟩ : syracuseStep 2461423 = 3692135) B3692135
theorem B3281897 : Blo 1943435 3281897 := bstep (se 2 (by rfl) ⟨1230711, by rfl⟩ : syracuseStep 3281897 = 2461423) B2461423
theorem B2187931 : Blo 1943435 2187931 := bstep (se 1 (by rfl) ⟨1640948, by rfl⟩ : syracuseStep 2187931 = 3281897) B3281897
theorem B2917241 : Blo 1943435 2917241 := bstep (se 2 (by rfl) ⟨1093965, by rfl⟩ : syracuseStep 2917241 = 2187931) B2187931
theorem B1944827 : Blo 1943435 1944827 := bstep (se 1 (by rfl) ⟨1458620, by rfl⟩ : syracuseStep 1944827 = 2917241) B2917241
theorem B7009301 : Blo 1943435 7009301 := bbase (se 6 (by rfl) ⟨164280, by rfl⟩ : syracuseStep 7009301 = 328561) (by norm_num)
theorem B18691469 : Blo 1943435 18691469 := bstep (se 3 (by rfl) ⟨3504650, by rfl⟩ : syracuseStep 18691469 = 7009301) B7009301
theorem B12460979 : Blo 1943435 12460979 := bstep (se 1 (by rfl) ⟨9345734, by rfl⟩ : syracuseStep 12460979 = 18691469) B18691469
theorem B33229277 : Blo 1943435 33229277 := bstep (se 3 (by rfl) ⟨6230489, by rfl⟩ : syracuseStep 33229277 = 12460979) B12460979
theorem B22152851 : Blo 1943435 22152851 := bstep (se 1 (by rfl) ⟨16614638, by rfl⟩ : syracuseStep 22152851 = 33229277) B33229277
theorem B14768567 : Blo 1943435 14768567 := bstep (se 1 (by rfl) ⟨11076425, by rfl⟩ : syracuseStep 14768567 = 22152851) B22152851
theorem B9845711 : Blo 1943435 9845711 := bstep (se 1 (by rfl) ⟨7384283, by rfl⟩ : syracuseStep 9845711 = 14768567) B14768567
theorem B6563807 : Blo 1943435 6563807 := bstep (se 1 (by rfl) ⟨4922855, by rfl⟩ : syracuseStep 6563807 = 9845711) B9845711
theorem B4375871 : Blo 1943435 4375871 := bstep (se 1 (by rfl) ⟨3281903, by rfl⟩ : syracuseStep 4375871 = 6563807) B6563807
theorem B2917247 : Blo 1943435 2917247 := bstep (se 1 (by rfl) ⟨2187935, by rfl⟩ : syracuseStep 2917247 = 4375871) B4375871
theorem B1944831 : Blo 1943435 1944831 := bstep (se 1 (by rfl) ⟨1458623, by rfl⟩ : syracuseStep 1944831 = 2917247) B2917247
theorem B2917253 : Blo 1943435 2917253 := bbase (se 4 (by rfl) ⟨273492, by rfl⟩ : syracuseStep 2917253 = 546985) (by norm_num)
theorem B1944835 : Blo 1943435 1944835 := bstep (se 1 (by rfl) ⟨1458626, by rfl⟩ : syracuseStep 1944835 = 2917253) B2917253
theorem B3281917 : Blo 1943435 3281917 := bbase (se 3 (by rfl) ⟨615359, by rfl⟩ : syracuseStep 3281917 = 1230719) (by norm_num)
theorem B4375889 : Blo 1943435 4375889 := bstep (se 2 (by rfl) ⟨1640958, by rfl⟩ : syracuseStep 4375889 = 3281917) B3281917
theorem B2917259 : Blo 1943435 2917259 := bstep (se 1 (by rfl) ⟨2187944, by rfl⟩ : syracuseStep 2917259 = 4375889) B4375889
theorem B1944839 : Blo 1943435 1944839 := bstep (se 1 (by rfl) ⟨1458629, by rfl⟩ : syracuseStep 1944839 = 2917259) B2917259
theorem B2187949 : Blo 1943435 2187949 := bbase (se 3 (by rfl) ⟨410240, by rfl⟩ : syracuseStep 2187949 = 820481) (by norm_num)
theorem B2917265 : Blo 1943435 2917265 := bstep (se 2 (by rfl) ⟨1093974, by rfl⟩ : syracuseStep 2917265 = 2187949) B2187949
theorem B1944843 : Blo 1943435 1944843 := bstep (se 1 (by rfl) ⟨1458632, by rfl⟩ : syracuseStep 1944843 = 2917265) B2917265
theorem B6563861 : Blo 1943435 6563861 := bbase (se 6 (by rfl) ⟨153840, by rfl⟩ : syracuseStep 6563861 = 307681) (by norm_num)
theorem B4375907 : Blo 1943435 4375907 := bstep (se 1 (by rfl) ⟨3281930, by rfl⟩ : syracuseStep 4375907 = 6563861) B6563861
theorem B2917271 : Blo 1943435 2917271 := bstep (se 1 (by rfl) ⟨2187953, by rfl⟩ : syracuseStep 2917271 = 4375907) B4375907
theorem B1944847 : Blo 1943435 1944847 := bstep (se 1 (by rfl) ⟨1458635, by rfl⟩ : syracuseStep 1944847 = 2917271) B2917271
theorem B2917277 : Blo 1943435 2917277 := bbase (se 3 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 2917277 = 1093979) (by norm_num)
theorem B1944851 : Blo 1943435 1944851 := bstep (se 1 (by rfl) ⟨1458638, by rfl⟩ : syracuseStep 1944851 = 2917277) B2917277
theorem B4375925 : Blo 1943435 4375925 := bbase (se 5 (by rfl) ⟨205121, by rfl⟩ : syracuseStep 4375925 = 410243) (by norm_num)
theorem B2917283 : Blo 1943435 2917283 := bstep (se 1 (by rfl) ⟨2187962, by rfl⟩ : syracuseStep 2917283 = 4375925) B4375925
theorem B1944855 : Blo 1943435 1944855 := bstep (se 1 (by rfl) ⟨1458641, by rfl⟩ : syracuseStep 1944855 = 2917283) B2917283
theorem B4736693 : Blo 1943435 4736693 := bbase (se 5 (by rfl) ⟨222032, by rfl⟩ : syracuseStep 4736693 = 444065) (by norm_num)
theorem B3157795 : Blo 1943435 3157795 := bstep (se 1 (by rfl) ⟨2368346, by rfl⟩ : syracuseStep 3157795 = 4736693) B4736693
theorem B4210393 : Blo 1943435 4210393 := bstep (se 2 (by rfl) ⟨1578897, by rfl⟩ : syracuseStep 4210393 = 3157795) B3157795
theorem B5613857 : Blo 1943435 5613857 := bstep (se 2 (by rfl) ⟨2105196, by rfl⟩ : syracuseStep 5613857 = 4210393) B4210393
theorem B3742571 : Blo 1943435 3742571 := bstep (se 1 (by rfl) ⟨2806928, by rfl⟩ : syracuseStep 3742571 = 5613857) B5613857
theorem B2495047 : Blo 1943435 2495047 := bstep (se 1 (by rfl) ⟨1871285, by rfl⟩ : syracuseStep 2495047 = 3742571) B3742571
theorem B3326729 : Blo 1943435 3326729 := bstep (se 2 (by rfl) ⟨1247523, by rfl⟩ : syracuseStep 3326729 = 2495047) B2495047
theorem B8871277 : Blo 1943435 8871277 := bstep (se 3 (by rfl) ⟨1663364, by rfl⟩ : syracuseStep 8871277 = 3326729) B3326729
theorem B11828369 : Blo 1943435 11828369 := bstep (se 2 (by rfl) ⟨4435638, by rfl⟩ : syracuseStep 11828369 = 8871277) B8871277
theorem B31542317 : Blo 1943435 31542317 := bstep (se 3 (by rfl) ⟨5914184, by rfl⟩ : syracuseStep 31542317 = 11828369) B11828369
theorem B21028211 : Blo 1943435 21028211 := bstep (se 1 (by rfl) ⟨15771158, by rfl⟩ : syracuseStep 21028211 = 31542317) B31542317
theorem B14018807 : Blo 1943435 14018807 := bstep (se 1 (by rfl) ⟨10514105, by rfl⟩ : syracuseStep 14018807 = 21028211) B21028211
theorem B9345871 : Blo 1943435 9345871 := bstep (se 1 (by rfl) ⟨7009403, by rfl⟩ : syracuseStep 9345871 = 14018807) B14018807
theorem B12461161 : Blo 1943435 12461161 := bstep (se 2 (by rfl) ⟨4672935, by rfl⟩ : syracuseStep 12461161 = 9345871) B9345871
theorem B16614881 : Blo 1943435 16614881 := bstep (se 2 (by rfl) ⟨6230580, by rfl⟩ : syracuseStep 16614881 = 12461161) B12461161
theorem B11076587 : Blo 1943435 11076587 := bstep (se 1 (by rfl) ⟨8307440, by rfl⟩ : syracuseStep 11076587 = 16614881) B16614881
theorem B7384391 : Blo 1943435 7384391 := bstep (se 1 (by rfl) ⟨5538293, by rfl⟩ : syracuseStep 7384391 = 11076587) B11076587
theorem B4922927 : Blo 1943435 4922927 := bstep (se 1 (by rfl) ⟨3692195, by rfl⟩ : syracuseStep 4922927 = 7384391) B7384391
theorem B3281951 : Blo 1943435 3281951 := bstep (se 1 (by rfl) ⟨2461463, by rfl⟩ : syracuseStep 3281951 = 4922927) B4922927
theorem B2187967 : Blo 1943435 2187967 := bstep (se 1 (by rfl) ⟨1640975, by rfl⟩ : syracuseStep 2187967 = 3281951) B3281951
theorem B2917289 : Blo 1943435 2917289 := bstep (se 2 (by rfl) ⟨1093983, by rfl⟩ : syracuseStep 2917289 = 2187967) B2187967
theorem B1944859 : Blo 1943435 1944859 := bstep (se 1 (by rfl) ⟨1458644, by rfl⟩ : syracuseStep 1944859 = 2917289) B2917289
theorem B7384405 : Blo 1943435 7384405 := bbase (se 11 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 7384405 = 10817) (by norm_num)
theorem B9845873 : Blo 1943435 9845873 := bstep (se 2 (by rfl) ⟨3692202, by rfl⟩ : syracuseStep 9845873 = 7384405) B7384405
theorem B6563915 : Blo 1943435 6563915 := bstep (se 1 (by rfl) ⟨4922936, by rfl⟩ : syracuseStep 6563915 = 9845873) B9845873
theorem B4375943 : Blo 1943435 4375943 := bstep (se 1 (by rfl) ⟨3281957, by rfl⟩ : syracuseStep 4375943 = 6563915) B6563915
theorem B2917295 : Blo 1943435 2917295 := bstep (se 1 (by rfl) ⟨2187971, by rfl⟩ : syracuseStep 2917295 = 4375943) B4375943
theorem B1944863 : Blo 1943435 1944863 := bstep (se 1 (by rfl) ⟨1458647, by rfl⟩ : syracuseStep 1944863 = 2917295) B2917295
theorem B2917301 : Blo 1943435 2917301 := bbase (se 5 (by rfl) ⟨136748, by rfl⟩ : syracuseStep 2917301 = 273497) (by norm_num)
theorem B1944867 : Blo 1943435 1944867 := bstep (se 1 (by rfl) ⟨1458650, by rfl⟩ : syracuseStep 1944867 = 2917301) B2917301
theorem B4922957 : Blo 1943435 4922957 := bbase (se 3 (by rfl) ⟨923054, by rfl⟩ : syracuseStep 4922957 = 1846109) (by norm_num)
theorem B3281971 : Blo 1943435 3281971 := bstep (se 1 (by rfl) ⟨2461478, by rfl⟩ : syracuseStep 3281971 = 4922957) B4922957
theorem B4375961 : Blo 1943435 4375961 := bstep (se 2 (by rfl) ⟨1640985, by rfl⟩ : syracuseStep 4375961 = 3281971) B3281971
theorem B2917307 : Blo 1943435 2917307 := bstep (se 1 (by rfl) ⟨2187980, by rfl⟩ : syracuseStep 2917307 = 4375961) B4375961
theorem B1944871 : Blo 1943435 1944871 := bstep (se 1 (by rfl) ⟨1458653, by rfl⟩ : syracuseStep 1944871 = 2917307) B2917307
theorem B2187985 : Blo 1943435 2187985 := bbase (se 2 (by rfl) ⟨820494, by rfl⟩ : syracuseStep 2187985 = 1640989) (by norm_num)
theorem B2917313 : Blo 1943435 2917313 := bstep (se 2 (by rfl) ⟨1093992, by rfl⟩ : syracuseStep 2917313 = 2187985) B2187985
theorem B1944875 : Blo 1943435 1944875 := bstep (se 1 (by rfl) ⟨1458656, by rfl⟩ : syracuseStep 1944875 = 2917313) B2917313
theorem B6230645 : Blo 1943435 6230645 := bbase (se 5 (by rfl) ⟨292061, by rfl⟩ : syracuseStep 6230645 = 584123) (by norm_num)
theorem B4153763 : Blo 1943435 4153763 := bstep (se 1 (by rfl) ⟨3115322, by rfl⟩ : syracuseStep 4153763 = 6230645) B6230645
theorem B2769175 : Blo 1943435 2769175 := bstep (se 1 (by rfl) ⟨2076881, by rfl⟩ : syracuseStep 2769175 = 4153763) B4153763
theorem B3692233 : Blo 1943435 3692233 := bstep (se 2 (by rfl) ⟨1384587, by rfl⟩ : syracuseStep 3692233 = 2769175) B2769175
theorem B4922977 : Blo 1943435 4922977 := bstep (se 2 (by rfl) ⟨1846116, by rfl⟩ : syracuseStep 4922977 = 3692233) B3692233
theorem B6563969 : Blo 1943435 6563969 := bstep (se 2 (by rfl) ⟨2461488, by rfl⟩ : syracuseStep 6563969 = 4922977) B4922977
theorem B4375979 : Blo 1943435 4375979 := bstep (se 1 (by rfl) ⟨3281984, by rfl⟩ : syracuseStep 4375979 = 6563969) B6563969
theorem B2917319 : Blo 1943435 2917319 := bstep (se 1 (by rfl) ⟨2187989, by rfl⟩ : syracuseStep 2917319 = 4375979) B4375979
theorem B1944879 : Blo 1943435 1944879 := bstep (se 1 (by rfl) ⟨1458659, by rfl⟩ : syracuseStep 1944879 = 2917319) B2917319
theorem B2917325 : Blo 1943435 2917325 := bbase (se 3 (by rfl) ⟨546998, by rfl⟩ : syracuseStep 2917325 = 1093997) (by norm_num)
theorem B1944883 : Blo 1943435 1944883 := bstep (se 1 (by rfl) ⟨1458662, by rfl⟩ : syracuseStep 1944883 = 2917325) B2917325
theorem B4375997 : Blo 1943435 4375997 := bbase (se 3 (by rfl) ⟨820499, by rfl⟩ : syracuseStep 4375997 = 1640999) (by norm_num)
theorem B2917331 : Blo 1943435 2917331 := bstep (se 1 (by rfl) ⟨2187998, by rfl⟩ : syracuseStep 2917331 = 4375997) B4375997
theorem B1944887 : Blo 1943435 1944887 := bstep (se 1 (by rfl) ⟨1458665, by rfl⟩ : syracuseStep 1944887 = 2917331) B2917331
theorem B3282005 : Blo 1943435 3282005 := bbase (se 8 (by rfl) ⟨19230, by rfl⟩ : syracuseStep 3282005 = 38461) (by norm_num)
theorem B2188003 : Blo 1943435 2188003 := bstep (se 1 (by rfl) ⟨1641002, by rfl⟩ : syracuseStep 2188003 = 3282005) B3282005
theorem B2917337 : Blo 1943435 2917337 := bstep (se 2 (by rfl) ⟨1094001, by rfl⟩ : syracuseStep 2917337 = 2188003) B2188003
theorem B1944891 : Blo 1943435 1944891 := bstep (se 1 (by rfl) ⟨1458668, by rfl⟩ : syracuseStep 1944891 = 2917337) B2917337
theorem B9473557 : Blo 1943435 9473557 := bbase (se 6 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 9473557 = 444073) (by norm_num)
theorem B12631409 : Blo 1943435 12631409 := bstep (se 2 (by rfl) ⟨4736778, by rfl⟩ : syracuseStep 12631409 = 9473557) B9473557
theorem B8420939 : Blo 1943435 8420939 := bstep (se 1 (by rfl) ⟨6315704, by rfl⟩ : syracuseStep 8420939 = 12631409) B12631409
theorem B5613959 : Blo 1943435 5613959 := bstep (se 1 (by rfl) ⟨4210469, by rfl⟩ : syracuseStep 5613959 = 8420939) B8420939
theorem B14970557 : Blo 1943435 14970557 := bstep (se 3 (by rfl) ⟨2806979, by rfl⟩ : syracuseStep 14970557 = 5613959) B5613959
theorem B9980371 : Blo 1943435 9980371 := bstep (se 1 (by rfl) ⟨7485278, by rfl⟩ : syracuseStep 9980371 = 14970557) B14970557
theorem B13307161 : Blo 1943435 13307161 := bstep (se 2 (by rfl) ⟨4990185, by rfl⟩ : syracuseStep 13307161 = 9980371) B9980371
theorem B17742881 : Blo 1943435 17742881 := bstep (se 2 (by rfl) ⟨6653580, by rfl⟩ : syracuseStep 17742881 = 13307161) B13307161
theorem B11828587 : Blo 1943435 11828587 := bstep (se 1 (by rfl) ⟨8871440, by rfl⟩ : syracuseStep 11828587 = 17742881) B17742881
theorem B15771449 : Blo 1943435 15771449 := bstep (se 2 (by rfl) ⟨5914293, by rfl⟩ : syracuseStep 15771449 = 11828587) B11828587
theorem B10514299 : Blo 1943435 10514299 := bstep (se 1 (by rfl) ⟨7885724, by rfl⟩ : syracuseStep 10514299 = 15771449) B15771449
theorem B14019065 : Blo 1943435 14019065 := bstep (se 2 (by rfl) ⟨5257149, by rfl⟩ : syracuseStep 14019065 = 10514299) B10514299
theorem B9346043 : Blo 1943435 9346043 := bstep (se 1 (by rfl) ⟨7009532, by rfl⟩ : syracuseStep 9346043 = 14019065) B14019065
theorem B6230695 : Blo 1943435 6230695 := bstep (se 1 (by rfl) ⟨4673021, by rfl⟩ : syracuseStep 6230695 = 9346043) B9346043
theorem B8307593 : Blo 1943435 8307593 := bstep (se 2 (by rfl) ⟨3115347, by rfl⟩ : syracuseStep 8307593 = 6230695) B6230695
theorem B5538395 : Blo 1943435 5538395 := bstep (se 1 (by rfl) ⟨4153796, by rfl⟩ : syracuseStep 5538395 = 8307593) B8307593
theorem B14769053 : Blo 1943435 14769053 := bstep (se 3 (by rfl) ⟨2769197, by rfl⟩ : syracuseStep 14769053 = 5538395) B5538395
theorem B9846035 : Blo 1943435 9846035 := bstep (se 1 (by rfl) ⟨7384526, by rfl⟩ : syracuseStep 9846035 = 14769053) B14769053
theorem B6564023 : Blo 1943435 6564023 := bstep (se 1 (by rfl) ⟨4923017, by rfl⟩ : syracuseStep 6564023 = 9846035) B9846035
theorem B4376015 : Blo 1943435 4376015 := bstep (se 1 (by rfl) ⟨3282011, by rfl⟩ : syracuseStep 4376015 = 6564023) B6564023
theorem B2917343 : Blo 1943435 2917343 := bstep (se 1 (by rfl) ⟨2188007, by rfl⟩ : syracuseStep 2917343 = 4376015) B4376015
theorem B1944895 : Blo 1943435 1944895 := bstep (se 1 (by rfl) ⟨1458671, by rfl⟩ : syracuseStep 1944895 = 2917343) B2917343
theorem B2917349 : Blo 1943435 2917349 := bbase (se 4 (by rfl) ⟨273501, by rfl⟩ : syracuseStep 2917349 = 547003) (by norm_num)
theorem B1944899 : Blo 1943435 1944899 := bstep (se 1 (by rfl) ⟨1458674, by rfl⟩ : syracuseStep 1944899 = 2917349) B2917349
theorem B2336521 : Blo 1943435 2336521 := bbase (se 2 (by rfl) ⟨876195, by rfl⟩ : syracuseStep 2336521 = 1752391) (by norm_num)
theorem B3115361 : Blo 1943435 3115361 := bstep (se 2 (by rfl) ⟨1168260, by rfl⟩ : syracuseStep 3115361 = 2336521) B2336521
theorem B8307629 : Blo 1943435 8307629 := bstep (se 3 (by rfl) ⟨1557680, by rfl⟩ : syracuseStep 8307629 = 3115361) B3115361
theorem B5538419 : Blo 1943435 5538419 := bstep (se 1 (by rfl) ⟨4153814, by rfl⟩ : syracuseStep 5538419 = 8307629) B8307629
theorem B3692279 : Blo 1943435 3692279 := bstep (se 1 (by rfl) ⟨2769209, by rfl⟩ : syracuseStep 3692279 = 5538419) B5538419
theorem B2461519 : Blo 1943435 2461519 := bstep (se 1 (by rfl) ⟨1846139, by rfl⟩ : syracuseStep 2461519 = 3692279) B3692279
theorem B3282025 : Blo 1943435 3282025 := bstep (se 2 (by rfl) ⟨1230759, by rfl⟩ : syracuseStep 3282025 = 2461519) B2461519
theorem B4376033 : Blo 1943435 4376033 := bstep (se 2 (by rfl) ⟨1641012, by rfl⟩ : syracuseStep 4376033 = 3282025) B3282025
theorem B2917355 : Blo 1943435 2917355 := bstep (se 1 (by rfl) ⟨2188016, by rfl⟩ : syracuseStep 2917355 = 4376033) B4376033
theorem B1944903 : Blo 1943435 1944903 := bstep (se 1 (by rfl) ⟨1458677, by rfl⟩ : syracuseStep 1944903 = 2917355) B2917355
theorem B2188021 : Blo 1943435 2188021 := bbase (se 5 (by rfl) ⟨102563, by rfl⟩ : syracuseStep 2188021 = 205127) (by norm_num)
theorem B2917361 : Blo 1943435 2917361 := bstep (se 2 (by rfl) ⟨1094010, by rfl⟩ : syracuseStep 2917361 = 2188021) B2188021
theorem B1944907 : Blo 1943435 1944907 := bstep (se 1 (by rfl) ⟨1458680, by rfl⟩ : syracuseStep 1944907 = 2917361) B2917361
theorem B2461529 : Blo 1943435 2461529 := bbase (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) (by norm_num)
theorem B6564077 : Blo 1943435 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B4376051 : Blo 1943435 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B2917367 : Blo 1943435 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B1944911 : Blo 1943435 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B2917373 : Blo 1943435 2917373 := bbase (se 3 (by rfl) ⟨547007, by rfl⟩ : syracuseStep 2917373 = 1094015) (by norm_num)
theorem B1944915 : Blo 1943435 1944915 := bstep (se 1 (by rfl) ⟨1458686, by rfl⟩ : syracuseStep 1944915 = 2917373) B2917373
theorem B4376069 : Blo 1943435 4376069 := bbase (se 4 (by rfl) ⟨410256, by rfl⟩ : syracuseStep 4376069 = 820513) (by norm_num)
theorem B2917379 : Blo 1943435 2917379 := bstep (se 1 (by rfl) ⟨2188034, by rfl⟩ : syracuseStep 2917379 = 4376069) B4376069
theorem B1944919 : Blo 1943435 1944919 := bstep (se 1 (by rfl) ⟨1458689, by rfl⟩ : syracuseStep 1944919 = 2917379) B2917379
theorem B3692317 : Blo 1943435 3692317 := bbase (se 3 (by rfl) ⟨692309, by rfl⟩ : syracuseStep 3692317 = 1384619) (by norm_num)
theorem B4923089 : Blo 1943435 4923089 := bstep (se 2 (by rfl) ⟨1846158, by rfl⟩ : syracuseStep 4923089 = 3692317) B3692317
theorem B3282059 : Blo 1943435 3282059 := bstep (se 1 (by rfl) ⟨2461544, by rfl⟩ : syracuseStep 3282059 = 4923089) B4923089
theorem B2188039 : Blo 1943435 2188039 := bstep (se 1 (by rfl) ⟨1641029, by rfl⟩ : syracuseStep 2188039 = 3282059) B3282059
theorem B2917385 : Blo 1943435 2917385 := bstep (se 2 (by rfl) ⟨1094019, by rfl⟩ : syracuseStep 2917385 = 2188039) B2188039
theorem B1944923 : Blo 1943435 1944923 := bstep (se 1 (by rfl) ⟨1458692, by rfl⟩ : syracuseStep 1944923 = 2917385) B2917385
theorem B9846197 : Blo 1943435 9846197 := bbase (se 5 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 9846197 = 923081) (by norm_num)
theorem B6564131 : Blo 1943435 6564131 := bstep (se 1 (by rfl) ⟨4923098, by rfl⟩ : syracuseStep 6564131 = 9846197) B9846197
theorem B4376087 : Blo 1943435 4376087 := bstep (se 1 (by rfl) ⟨3282065, by rfl⟩ : syracuseStep 4376087 = 6564131) B6564131
theorem B2917391 : Blo 1943435 2917391 := bstep (se 1 (by rfl) ⟨2188043, by rfl⟩ : syracuseStep 2917391 = 4376087) B4376087
theorem B1944927 : Blo 1943435 1944927 := bstep (se 1 (by rfl) ⟨1458695, by rfl⟩ : syracuseStep 1944927 = 2917391) B2917391
theorem B2917397 : Blo 1943435 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B1944931 : Blo 1943435 1944931 := bstep (se 1 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 1944931 = 2917397) B2917397
theorem B11228149 : Blo 1943435 11228149 := bbase (se 5 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 11228149 = 1052639) (by norm_num)
theorem B14970865 : Blo 1943435 14970865 := bstep (se 2 (by rfl) ⟨5614074, by rfl⟩ : syracuseStep 14970865 = 11228149) B11228149
theorem B19961153 : Blo 1943435 19961153 := bstep (se 2 (by rfl) ⟨7485432, by rfl⟩ : syracuseStep 19961153 = 14970865) B14970865
theorem B13307435 : Blo 1943435 13307435 := bstep (se 1 (by rfl) ⟨9980576, by rfl⟩ : syracuseStep 13307435 = 19961153) B19961153
theorem B8871623 : Blo 1943435 8871623 := bstep (se 1 (by rfl) ⟨6653717, by rfl⟩ : syracuseStep 8871623 = 13307435) B13307435
theorem B5914415 : Blo 1943435 5914415 := bstep (se 1 (by rfl) ⟨4435811, by rfl⟩ : syracuseStep 5914415 = 8871623) B8871623
theorem B15771773 : Blo 1943435 15771773 := bstep (se 3 (by rfl) ⟨2957207, by rfl⟩ : syracuseStep 15771773 = 5914415) B5914415
theorem B42058061 : Blo 1943435 42058061 := bstep (se 3 (by rfl) ⟨7885886, by rfl⟩ : syracuseStep 42058061 = 15771773) B15771773
theorem B28038707 : Blo 1943435 28038707 := bstep (se 1 (by rfl) ⟨21029030, by rfl⟩ : syracuseStep 28038707 = 42058061) B42058061
theorem B18692471 : Blo 1943435 18692471 := bstep (se 1 (by rfl) ⟨14019353, by rfl⟩ : syracuseStep 18692471 = 28038707) B28038707
theorem B12461647 : Blo 1943435 12461647 := bstep (se 1 (by rfl) ⟨9346235, by rfl⟩ : syracuseStep 12461647 = 18692471) B18692471
theorem B16615529 : Blo 1943435 16615529 := bstep (se 2 (by rfl) ⟨6230823, by rfl⟩ : syracuseStep 16615529 = 12461647) B12461647
theorem B11077019 : Blo 1943435 11077019 := bstep (se 1 (by rfl) ⟨8307764, by rfl⟩ : syracuseStep 11077019 = 16615529) B16615529
theorem B7384679 : Blo 1943435 7384679 := bstep (se 1 (by rfl) ⟨5538509, by rfl⟩ : syracuseStep 7384679 = 11077019) B11077019
theorem B4923119 : Blo 1943435 4923119 := bstep (se 1 (by rfl) ⟨3692339, by rfl⟩ : syracuseStep 4923119 = 7384679) B7384679
theorem B3282079 : Blo 1943435 3282079 := bstep (se 1 (by rfl) ⟨2461559, by rfl⟩ : syracuseStep 3282079 = 4923119) B4923119
theorem B4376105 : Blo 1943435 4376105 := bstep (se 2 (by rfl) ⟨1641039, by rfl⟩ : syracuseStep 4376105 = 3282079) B3282079
theorem B2917403 : Blo 1943435 2917403 := bstep (se 1 (by rfl) ⟨2188052, by rfl⟩ : syracuseStep 2917403 = 4376105) B4376105
theorem B1944935 : Blo 1943435 1944935 := bstep (se 1 (by rfl) ⟨1458701, by rfl⟩ : syracuseStep 1944935 = 2917403) B2917403
theorem B2188057 : Blo 1943435 2188057 := bbase (se 2 (by rfl) ⟨820521, by rfl⟩ : syracuseStep 2188057 = 1641043) (by norm_num)
theorem B2917409 : Blo 1943435 2917409 := bstep (se 2 (by rfl) ⟨1094028, by rfl⟩ : syracuseStep 2917409 = 2188057) B2188057
theorem B1944939 : Blo 1943435 1944939 := bstep (se 1 (by rfl) ⟨1458704, by rfl⟩ : syracuseStep 1944939 = 2917409) B2917409
theorem B7384709 : Blo 1943435 7384709 := bbase (se 4 (by rfl) ⟨692316, by rfl⟩ : syracuseStep 7384709 = 1384633) (by norm_num)
theorem B4923139 : Blo 1943435 4923139 := bstep (se 1 (by rfl) ⟨3692354, by rfl⟩ : syracuseStep 4923139 = 7384709) B7384709
theorem B6564185 : Blo 1943435 6564185 := bstep (se 2 (by rfl) ⟨2461569, by rfl⟩ : syracuseStep 6564185 = 4923139) B4923139
theorem B4376123 : Blo 1943435 4376123 := bstep (se 1 (by rfl) ⟨3282092, by rfl⟩ : syracuseStep 4376123 = 6564185) B6564185
theorem B2917415 : Blo 1943435 2917415 := bstep (se 1 (by rfl) ⟨2188061, by rfl⟩ : syracuseStep 2917415 = 4376123) B4376123
theorem B1944943 : Blo 1943435 1944943 := bstep (se 1 (by rfl) ⟨1458707, by rfl⟩ : syracuseStep 1944943 = 2917415) B2917415
theorem B2917421 : Blo 1943435 2917421 := bbase (se 3 (by rfl) ⟨547016, by rfl⟩ : syracuseStep 2917421 = 1094033) (by norm_num)
theorem B1944947 : Blo 1943435 1944947 := bstep (se 1 (by rfl) ⟨1458710, by rfl⟩ : syracuseStep 1944947 = 2917421) B2917421
theorem B4376141 : Blo 1943435 4376141 := bbase (se 3 (by rfl) ⟨820526, by rfl⟩ : syracuseStep 4376141 = 1641053) (by norm_num)
theorem B2917427 : Blo 1943435 2917427 := bstep (se 1 (by rfl) ⟨2188070, by rfl⟩ : syracuseStep 2917427 = 4376141) B4376141
theorem B1944951 : Blo 1943435 1944951 := bstep (se 1 (by rfl) ⟨1458713, by rfl⟩ : syracuseStep 1944951 = 2917427) B2917427
theorem B2461585 : Blo 1943435 2461585 := bbase (se 2 (by rfl) ⟨923094, by rfl⟩ : syracuseStep 2461585 = 1846189) (by norm_num)
theorem B3282113 : Blo 1943435 3282113 := bstep (se 2 (by rfl) ⟨1230792, by rfl⟩ : syracuseStep 3282113 = 2461585) B2461585
theorem B2188075 : Blo 1943435 2188075 := bstep (se 1 (by rfl) ⟨1641056, by rfl⟩ : syracuseStep 2188075 = 3282113) B3282113
theorem B2917433 : Blo 1943435 2917433 := bstep (se 2 (by rfl) ⟨1094037, by rfl⟩ : syracuseStep 2917433 = 2188075) B2188075
theorem B1944955 : Blo 1943435 1944955 := bstep (se 1 (by rfl) ⟨1458716, by rfl⟩ : syracuseStep 1944955 = 2917433) B2917433
theorem B4153933 : Blo 1943435 4153933 := bbase (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) (by norm_num)
theorem B22154309 : Blo 1943435 22154309 := bstep (se 4 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 22154309 = 4153933) B4153933
theorem B14769539 : Blo 1943435 14769539 := bstep (se 1 (by rfl) ⟨11077154, by rfl⟩ : syracuseStep 14769539 = 22154309) B22154309
theorem B9846359 : Blo 1943435 9846359 := bstep (se 1 (by rfl) ⟨7384769, by rfl⟩ : syracuseStep 9846359 = 14769539) B14769539
theorem B6564239 : Blo 1943435 6564239 := bstep (se 1 (by rfl) ⟨4923179, by rfl⟩ : syracuseStep 6564239 = 9846359) B9846359
theorem B4376159 : Blo 1943435 4376159 := bstep (se 1 (by rfl) ⟨3282119, by rfl⟩ : syracuseStep 4376159 = 6564239) B6564239
theorem B2917439 : Blo 1943435 2917439 := bstep (se 1 (by rfl) ⟨2188079, by rfl⟩ : syracuseStep 2917439 = 4376159) B4376159
theorem B1944959 : Blo 1943435 1944959 := bstep (se 1 (by rfl) ⟨1458719, by rfl⟩ : syracuseStep 1944959 = 2917439) B2917439
theorem B2917445 : Blo 1943435 2917445 := bbase (se 4 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 2917445 = 547021) (by norm_num)
theorem B1944963 : Blo 1943435 1944963 := bstep (se 1 (by rfl) ⟨1458722, by rfl⟩ : syracuseStep 1944963 = 2917445) B2917445
theorem B3282133 : Blo 1943435 3282133 := bbase (se 7 (by rfl) ⟨38462, by rfl⟩ : syracuseStep 3282133 = 76925) (by norm_num)
theorem B4376177 : Blo 1943435 4376177 := bstep (se 2 (by rfl) ⟨1641066, by rfl⟩ : syracuseStep 4376177 = 3282133) B3282133
theorem B2917451 : Blo 1943435 2917451 := bstep (se 1 (by rfl) ⟨2188088, by rfl⟩ : syracuseStep 2917451 = 4376177) B4376177
theorem B1944967 : Blo 1943435 1944967 := bstep (se 1 (by rfl) ⟨1458725, by rfl⟩ : syracuseStep 1944967 = 2917451) B2917451
theorem B2188093 : Blo 1943435 2188093 := bbase (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) (by norm_num)
theorem B2917457 : Blo 1943435 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B1944971 : Blo 1943435 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B6564293 : Blo 1943435 6564293 := bbase (se 4 (by rfl) ⟨615402, by rfl⟩ : syracuseStep 6564293 = 1230805) (by norm_num)
theorem B4376195 : Blo 1943435 4376195 := bstep (se 1 (by rfl) ⟨3282146, by rfl⟩ : syracuseStep 4376195 = 6564293) B6564293
theorem B2917463 : Blo 1943435 2917463 := bstep (se 1 (by rfl) ⟨2188097, by rfl⟩ : syracuseStep 2917463 = 4376195) B4376195
theorem B1944975 : Blo 1943435 1944975 := bstep (se 1 (by rfl) ⟨1458731, by rfl⟩ : syracuseStep 1944975 = 2917463) B2917463
theorem B2917469 : Blo 1943435 2917469 := bbase (se 3 (by rfl) ⟨547025, by rfl⟩ : syracuseStep 2917469 = 1094051) (by norm_num)
theorem B1944979 : Blo 1943435 1944979 := bstep (se 1 (by rfl) ⟨1458734, by rfl⟩ : syracuseStep 1944979 = 2917469) B2917469
theorem B4376213 : Blo 1943435 4376213 := bbase (se 6 (by rfl) ⟨102567, by rfl⟩ : syracuseStep 4376213 = 205135) (by norm_num)
theorem B2917475 : Blo 1943435 2917475 := bstep (se 1 (by rfl) ⟨2188106, by rfl⟩ : syracuseStep 2917475 = 4376213) B4376213
theorem B1944983 : Blo 1943435 1944983 := bstep (se 1 (by rfl) ⟨1458737, by rfl⟩ : syracuseStep 1944983 = 2917475) B2917475
theorem B2076997 : Blo 1943435 2076997 := bbase (se 4 (by rfl) ⟨194718, by rfl⟩ : syracuseStep 2076997 = 389437) (by norm_num)
theorem B2769329 : Blo 1943435 2769329 := bstep (se 2 (by rfl) ⟨1038498, by rfl⟩ : syracuseStep 2769329 = 2076997) B2076997
theorem B7384877 : Blo 1943435 7384877 := bstep (se 3 (by rfl) ⟨1384664, by rfl⟩ : syracuseStep 7384877 = 2769329) B2769329
theorem B4923251 : Blo 1943435 4923251 := bstep (se 1 (by rfl) ⟨3692438, by rfl⟩ : syracuseStep 4923251 = 7384877) B7384877
theorem B3282167 : Blo 1943435 3282167 := bstep (se 1 (by rfl) ⟨2461625, by rfl⟩ : syracuseStep 3282167 = 4923251) B4923251
theorem B2188111 : Blo 1943435 2188111 := bstep (se 1 (by rfl) ⟨1641083, by rfl⟩ : syracuseStep 2188111 = 3282167) B3282167
theorem B2917481 : Blo 1943435 2917481 := bstep (se 2 (by rfl) ⟨1094055, by rfl⟩ : syracuseStep 2917481 = 2188111) B2188111
theorem B1944987 : Blo 1943435 1944987 := bstep (se 1 (by rfl) ⟨1458740, by rfl⟩ : syracuseStep 1944987 = 2917481) B2917481
theorem B12462005 : Blo 1943435 12462005 := bbase (se 5 (by rfl) ⟨584156, by rfl⟩ : syracuseStep 12462005 = 1168313) (by norm_num)
theorem B8308003 : Blo 1943435 8308003 := bstep (se 1 (by rfl) ⟨6231002, by rfl⟩ : syracuseStep 8308003 = 12462005) B12462005
theorem B11077337 : Blo 1943435 11077337 := bstep (se 2 (by rfl) ⟨4154001, by rfl⟩ : syracuseStep 11077337 = 8308003) B8308003
theorem B7384891 : Blo 1943435 7384891 := bstep (se 1 (by rfl) ⟨5538668, by rfl⟩ : syracuseStep 7384891 = 11077337) B11077337
theorem B9846521 : Blo 1943435 9846521 := bstep (se 2 (by rfl) ⟨3692445, by rfl⟩ : syracuseStep 9846521 = 7384891) B7384891
theorem B6564347 : Blo 1943435 6564347 := bstep (se 1 (by rfl) ⟨4923260, by rfl⟩ : syracuseStep 6564347 = 9846521) B9846521
theorem B4376231 : Blo 1943435 4376231 := bstep (se 1 (by rfl) ⟨3282173, by rfl⟩ : syracuseStep 4376231 = 6564347) B6564347
theorem B2917487 : Blo 1943435 2917487 := bstep (se 1 (by rfl) ⟨2188115, by rfl⟩ : syracuseStep 2917487 = 4376231) B4376231
theorem B1944991 : Blo 1943435 1944991 := bstep (se 1 (by rfl) ⟨1458743, by rfl⟩ : syracuseStep 1944991 = 2917487) B2917487
theorem B2917493 : Blo 1943435 2917493 := bbase (se 5 (by rfl) ⟨136757, by rfl⟩ : syracuseStep 2917493 = 273515) (by norm_num)
theorem B1944995 : Blo 1943435 1944995 := bstep (se 1 (by rfl) ⟨1458746, by rfl⟩ : syracuseStep 1944995 = 2917493) B2917493
theorem B3692461 : Blo 1943435 3692461 := bbase (se 3 (by rfl) ⟨692336, by rfl⟩ : syracuseStep 3692461 = 1384673) (by norm_num)
theorem B4923281 : Blo 1943435 4923281 := bstep (se 2 (by rfl) ⟨1846230, by rfl⟩ : syracuseStep 4923281 = 3692461) B3692461
theorem B3282187 : Blo 1943435 3282187 := bstep (se 1 (by rfl) ⟨2461640, by rfl⟩ : syracuseStep 3282187 = 4923281) B4923281
theorem B4376249 : Blo 1943435 4376249 := bstep (se 2 (by rfl) ⟨1641093, by rfl⟩ : syracuseStep 4376249 = 3282187) B3282187
theorem B2917499 : Blo 1943435 2917499 := bstep (se 1 (by rfl) ⟨2188124, by rfl⟩ : syracuseStep 2917499 = 4376249) B4376249
theorem B1944999 : Blo 1943435 1944999 := bstep (se 1 (by rfl) ⟨1458749, by rfl⟩ : syracuseStep 1944999 = 2917499) B2917499
theorem B2188129 : Blo 1943435 2188129 := bbase (se 2 (by rfl) ⟨820548, by rfl⟩ : syracuseStep 2188129 = 1641097) (by norm_num)
theorem B2917505 : Blo 1943435 2917505 := bstep (se 2 (by rfl) ⟨1094064, by rfl⟩ : syracuseStep 2917505 = 2188129) B2188129
theorem B1945003 : Blo 1943435 1945003 := bstep (se 1 (by rfl) ⟨1458752, by rfl⟩ : syracuseStep 1945003 = 2917505) B2917505
theorem B4923301 : Blo 1943435 4923301 := bbase (se 4 (by rfl) ⟨461559, by rfl⟩ : syracuseStep 4923301 = 923119) (by norm_num)
theorem B6564401 : Blo 1943435 6564401 := bstep (se 2 (by rfl) ⟨2461650, by rfl⟩ : syracuseStep 6564401 = 4923301) B4923301
theorem B4376267 : Blo 1943435 4376267 := bstep (se 1 (by rfl) ⟨3282200, by rfl⟩ : syracuseStep 4376267 = 6564401) B6564401
theorem B2917511 : Blo 1943435 2917511 := bstep (se 1 (by rfl) ⟨2188133, by rfl⟩ : syracuseStep 2917511 = 4376267) B4376267
theorem B1945007 : Blo 1943435 1945007 := bstep (se 1 (by rfl) ⟨1458755, by rfl⟩ : syracuseStep 1945007 = 2917511) B2917511
theorem B2917517 : Blo 1943435 2917517 := bbase (se 3 (by rfl) ⟨547034, by rfl⟩ : syracuseStep 2917517 = 1094069) (by norm_num)
theorem B1945011 : Blo 1943435 1945011 := bstep (se 1 (by rfl) ⟨1458758, by rfl⟩ : syracuseStep 1945011 = 2917517) B2917517
theorem B4376285 : Blo 1943435 4376285 := bbase (se 3 (by rfl) ⟨820553, by rfl⟩ : syracuseStep 4376285 = 1641107) (by norm_num)
theorem B2917523 : Blo 1943435 2917523 := bstep (se 1 (by rfl) ⟨2188142, by rfl⟩ : syracuseStep 2917523 = 4376285) B4376285
theorem B1945015 : Blo 1943435 1945015 := bstep (se 1 (by rfl) ⟨1458761, by rfl⟩ : syracuseStep 1945015 = 2917523) B2917523
theorem B3282221 : Blo 1943435 3282221 := bbase (se 3 (by rfl) ⟨615416, by rfl⟩ : syracuseStep 3282221 = 1230833) (by norm_num)
theorem B2188147 : Blo 1943435 2188147 := bstep (se 1 (by rfl) ⟨1641110, by rfl⟩ : syracuseStep 2188147 = 3282221) B3282221
theorem B2917529 : Blo 1943435 2917529 := bstep (se 2 (by rfl) ⟨1094073, by rfl⟩ : syracuseStep 2917529 = 2188147) B2188147
theorem B1945019 : Blo 1943435 1945019 := bstep (se 1 (by rfl) ⟨1458764, by rfl⟩ : syracuseStep 1945019 = 2917529) B2917529
theorem B11829365 : Blo 1943435 11829365 := bbase (se 5 (by rfl) ⟨554501, by rfl⟩ : syracuseStep 11829365 = 1109003) (by norm_num)
theorem B7886243 : Blo 1943435 7886243 := bstep (se 1 (by rfl) ⟨5914682, by rfl⟩ : syracuseStep 7886243 = 11829365) B11829365
theorem B5257495 : Blo 1943435 5257495 := bstep (se 1 (by rfl) ⟨3943121, by rfl⟩ : syracuseStep 5257495 = 7886243) B7886243
theorem B7009993 : Blo 1943435 7009993 := bstep (se 2 (by rfl) ⟨2628747, by rfl⟩ : syracuseStep 7009993 = 5257495) B5257495
theorem B37386629 : Blo 1943435 37386629 := bstep (se 4 (by rfl) ⟨3504996, by rfl⟩ : syracuseStep 37386629 = 7009993) B7009993
theorem B24924419 : Blo 1943435 24924419 := bstep (se 1 (by rfl) ⟨18693314, by rfl⟩ : syracuseStep 24924419 = 37386629) B37386629
theorem B16616279 : Blo 1943435 16616279 := bstep (se 1 (by rfl) ⟨12462209, by rfl⟩ : syracuseStep 16616279 = 24924419) B24924419
theorem B11077519 : Blo 1943435 11077519 := bstep (se 1 (by rfl) ⟨8308139, by rfl⟩ : syracuseStep 11077519 = 16616279) B16616279
theorem B14770025 : Blo 1943435 14770025 := bstep (se 2 (by rfl) ⟨5538759, by rfl⟩ : syracuseStep 14770025 = 11077519) B11077519
theorem B9846683 : Blo 1943435 9846683 := bstep (se 1 (by rfl) ⟨7385012, by rfl⟩ : syracuseStep 9846683 = 14770025) B14770025
theorem B6564455 : Blo 1943435 6564455 := bstep (se 1 (by rfl) ⟨4923341, by rfl⟩ : syracuseStep 6564455 = 9846683) B9846683
theorem B4376303 : Blo 1943435 4376303 := bstep (se 1 (by rfl) ⟨3282227, by rfl⟩ : syracuseStep 4376303 = 6564455) B6564455
theorem B2917535 : Blo 1943435 2917535 := bstep (se 1 (by rfl) ⟨2188151, by rfl⟩ : syracuseStep 2917535 = 4376303) B4376303
theorem B1945023 : Blo 1943435 1945023 := bstep (se 1 (by rfl) ⟨1458767, by rfl⟩ : syracuseStep 1945023 = 2917535) B2917535
theorem B2917541 : Blo 1943435 2917541 := bbase (se 4 (by rfl) ⟨273519, by rfl⟩ : syracuseStep 2917541 = 547039) (by norm_num)
theorem B1945027 : Blo 1943435 1945027 := bstep (se 1 (by rfl) ⟨1458770, by rfl⟩ : syracuseStep 1945027 = 2917541) B2917541
theorem B2461681 : Blo 1943435 2461681 := bbase (se 2 (by rfl) ⟨923130, by rfl⟩ : syracuseStep 2461681 = 1846261) (by norm_num)
theorem B3282241 : Blo 1943435 3282241 := bstep (se 2 (by rfl) ⟨1230840, by rfl⟩ : syracuseStep 3282241 = 2461681) B2461681
theorem B4376321 : Blo 1943435 4376321 := bstep (se 2 (by rfl) ⟨1641120, by rfl⟩ : syracuseStep 4376321 = 3282241) B3282241
theorem B2917547 : Blo 1943435 2917547 := bstep (se 1 (by rfl) ⟨2188160, by rfl⟩ : syracuseStep 2917547 = 4376321) B4376321
theorem B1945031 : Blo 1943435 1945031 := bstep (se 1 (by rfl) ⟨1458773, by rfl⟩ : syracuseStep 1945031 = 2917547) B2917547
theorem B2188165 : Blo 1943435 2188165 := bbase (se 4 (by rfl) ⟨205140, by rfl⟩ : syracuseStep 2188165 = 410281) (by norm_num)
theorem B2917553 : Blo 1943435 2917553 := bstep (se 2 (by rfl) ⟨1094082, by rfl⟩ : syracuseStep 2917553 = 2188165) B2188165
theorem B1945035 : Blo 1943435 1945035 := bstep (se 1 (by rfl) ⟨1458776, by rfl⟩ : syracuseStep 1945035 = 2917553) B2917553
theorem B5257541 : Blo 1943435 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B3505027 : Blo 1943435 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B4673369 : Blo 1943435 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B3115579 : Blo 1943435 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B4154105 : Blo 1943435 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B2769403 : Blo 1943435 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B3692537 : Blo 1943435 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B2461691 : Blo 1943435 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B6564509 : Blo 1943435 6564509 := bstep (se 3 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 6564509 = 2461691) B2461691
theorem B4376339 : Blo 1943435 4376339 := bstep (se 1 (by rfl) ⟨3282254, by rfl⟩ : syracuseStep 4376339 = 6564509) B6564509
theorem B2917559 : Blo 1943435 2917559 := bstep (se 1 (by rfl) ⟨2188169, by rfl⟩ : syracuseStep 2917559 = 4376339) B4376339
theorem B1945039 : Blo 1943435 1945039 := bstep (se 1 (by rfl) ⟨1458779, by rfl⟩ : syracuseStep 1945039 = 2917559) B2917559
theorem B2917565 : Blo 1943435 2917565 := bbase (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) (by norm_num)
theorem B1945043 : Blo 1943435 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B4376357 : Blo 1943435 4376357 := bbase (se 4 (by rfl) ⟨410283, by rfl⟩ : syracuseStep 4376357 = 820567) (by norm_num)
theorem B2917571 : Blo 1943435 2917571 := bstep (se 1 (by rfl) ⟨2188178, by rfl⟩ : syracuseStep 2917571 = 4376357) B4376357
theorem B1945047 : Blo 1943435 1945047 := bstep (se 1 (by rfl) ⟨1458785, by rfl⟩ : syracuseStep 1945047 = 2917571) B2917571
theorem B4923413 : Blo 1943435 4923413 := bbase (se 6 (by rfl) ⟨115392, by rfl⟩ : syracuseStep 4923413 = 230785) (by norm_num)
theorem B3282275 : Blo 1943435 3282275 := bstep (se 1 (by rfl) ⟨2461706, by rfl⟩ : syracuseStep 3282275 = 4923413) B4923413
theorem B2188183 : Blo 1943435 2188183 := bstep (se 1 (by rfl) ⟨1641137, by rfl⟩ : syracuseStep 2188183 = 3282275) B3282275
theorem B2917577 : Blo 1943435 2917577 := bstep (se 2 (by rfl) ⟨1094091, by rfl⟩ : syracuseStep 2917577 = 2188183) B2188183
theorem B1945051 : Blo 1943435 1945051 := bstep (se 1 (by rfl) ⟨1458788, by rfl⟩ : syracuseStep 1945051 = 2917577) B2917577
theorem B8308277 : Blo 1943435 8308277 := bbase (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) (by norm_num)
theorem B5538851 : Blo 1943435 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B3692567 : Blo 1943435 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B9846845 : Blo 1943435 9846845 := bstep (se 3 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 9846845 = 3692567) B3692567
theorem B6564563 : Blo 1943435 6564563 := bstep (se 1 (by rfl) ⟨4923422, by rfl⟩ : syracuseStep 6564563 = 9846845) B9846845
theorem B4376375 : Blo 1943435 4376375 := bstep (se 1 (by rfl) ⟨3282281, by rfl⟩ : syracuseStep 4376375 = 6564563) B6564563
theorem B2917583 : Blo 1943435 2917583 := bstep (se 1 (by rfl) ⟨2188187, by rfl⟩ : syracuseStep 2917583 = 4376375) B4376375
theorem B1945055 : Blo 1943435 1945055 := bstep (se 1 (by rfl) ⟨1458791, by rfl⟩ : syracuseStep 1945055 = 2917583) B2917583
theorem B2917589 : Blo 1943435 2917589 := bbase (se 7 (by rfl) ⟨34190, by rfl⟩ : syracuseStep 2917589 = 68381) (by norm_num)
theorem B1945059 : Blo 1943435 1945059 := bstep (se 1 (by rfl) ⟨1458794, by rfl⟩ : syracuseStep 1945059 = 2917589) B2917589
theorem B2769437 : Blo 1943435 2769437 := bbase (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) (by norm_num)
theorem B7385165 : Blo 1943435 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B4923443 : Blo 1943435 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B3282295 : Blo 1943435 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B4376393 : Blo 1943435 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B2917595 : Blo 1943435 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B1945063 : Blo 1943435 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B2188201 : Blo 1943435 2188201 := bbase (se 2 (by rfl) ⟨820575, by rfl⟩ : syracuseStep 2188201 = 1641151) (by norm_num)
theorem B2917601 : Blo 1943435 2917601 := bstep (se 2 (by rfl) ⟨1094100, by rfl⟩ : syracuseStep 2917601 = 2188201) B2188201
theorem B1945067 : Blo 1943435 1945067 := bstep (se 1 (by rfl) ⟨1458800, by rfl⟩ : syracuseStep 1945067 = 2917601) B2917601
theorem B2218061 : Blo 1943435 2218061 := bbase (se 3 (by rfl) ⟨415886, by rfl⟩ : syracuseStep 2218061 = 831773) (by norm_num)
theorem B5914829 : Blo 1943435 5914829 := bstep (se 3 (by rfl) ⟨1109030, by rfl⟩ : syracuseStep 5914829 = 2218061) B2218061
theorem B15772877 : Blo 1943435 15772877 := bstep (se 3 (by rfl) ⟨2957414, by rfl⟩ : syracuseStep 15772877 = 5914829) B5914829
theorem B10515251 : Blo 1943435 10515251 := bstep (se 1 (by rfl) ⟨7886438, by rfl⟩ : syracuseStep 10515251 = 15772877) B15772877
theorem B7010167 : Blo 1943435 7010167 := bstep (se 1 (by rfl) ⟨5257625, by rfl⟩ : syracuseStep 7010167 = 10515251) B10515251
theorem B9346889 : Blo 1943435 9346889 := bstep (se 2 (by rfl) ⟨3505083, by rfl⟩ : syracuseStep 9346889 = 7010167) B7010167
theorem B6231259 : Blo 1943435 6231259 := bstep (se 1 (by rfl) ⟨4673444, by rfl⟩ : syracuseStep 6231259 = 9346889) B9346889
theorem B8308345 : Blo 1943435 8308345 := bstep (se 2 (by rfl) ⟨3115629, by rfl⟩ : syracuseStep 8308345 = 6231259) B6231259
theorem B11077793 : Blo 1943435 11077793 := bstep (se 2 (by rfl) ⟨4154172, by rfl⟩ : syracuseStep 11077793 = 8308345) B8308345
theorem B7385195 : Blo 1943435 7385195 := bstep (se 1 (by rfl) ⟨5538896, by rfl⟩ : syracuseStep 7385195 = 11077793) B11077793
theorem B4923463 : Blo 1943435 4923463 := bstep (se 1 (by rfl) ⟨3692597, by rfl⟩ : syracuseStep 4923463 = 7385195) B7385195
theorem B6564617 : Blo 1943435 6564617 := bstep (se 2 (by rfl) ⟨2461731, by rfl⟩ : syracuseStep 6564617 = 4923463) B4923463
theorem B4376411 : Blo 1943435 4376411 := bstep (se 1 (by rfl) ⟨3282308, by rfl⟩ : syracuseStep 4376411 = 6564617) B6564617
theorem B2917607 : Blo 1943435 2917607 := bstep (se 1 (by rfl) ⟨2188205, by rfl⟩ : syracuseStep 2917607 = 4376411) B4376411
theorem B1945071 : Blo 1943435 1945071 := bstep (se 1 (by rfl) ⟨1458803, by rfl⟩ : syracuseStep 1945071 = 2917607) B2917607
theorem B2917613 : Blo 1943435 2917613 := bbase (se 3 (by rfl) ⟨547052, by rfl⟩ : syracuseStep 2917613 = 1094105) (by norm_num)
theorem B1945075 : Blo 1943435 1945075 := bstep (se 1 (by rfl) ⟨1458806, by rfl⟩ : syracuseStep 1945075 = 2917613) B2917613
theorem B4376429 : Blo 1943435 4376429 := bbase (se 3 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 4376429 = 1641161) (by norm_num)
theorem B2917619 : Blo 1943435 2917619 := bstep (se 1 (by rfl) ⟨2188214, by rfl⟩ : syracuseStep 2917619 = 4376429) B4376429
theorem B1945079 : Blo 1943435 1945079 := bstep (se 1 (by rfl) ⟨1458809, by rfl⟩ : syracuseStep 1945079 = 2917619) B2917619
theorem B3692621 : Blo 1943435 3692621 := bbase (se 3 (by rfl) ⟨692366, by rfl⟩ : syracuseStep 3692621 = 1384733) (by norm_num)
theorem B2461747 : Blo 1943435 2461747 := bstep (se 1 (by rfl) ⟨1846310, by rfl⟩ : syracuseStep 2461747 = 3692621) B3692621
theorem B3282329 : Blo 1943435 3282329 := bstep (se 2 (by rfl) ⟨1230873, by rfl⟩ : syracuseStep 3282329 = 2461747) B2461747
theorem B2188219 : Blo 1943435 2188219 := bstep (se 1 (by rfl) ⟨1641164, by rfl⟩ : syracuseStep 2188219 = 3282329) B3282329
theorem B2917625 : Blo 1943435 2917625 := bstep (se 2 (by rfl) ⟨1094109, by rfl⟩ : syracuseStep 2917625 = 2188219) B2188219
theorem B1945083 : Blo 1943435 1945083 := bstep (se 1 (by rfl) ⟨1458812, by rfl⟩ : syracuseStep 1945083 = 2917625) B2917625
theorem B70978517 : Blo 1943435 70978517 := bbase (se 7 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 70978517 = 1663559) (by norm_num)
theorem B47319011 : Blo 1943435 47319011 := bstep (se 1 (by rfl) ⟨35489258, by rfl⟩ : syracuseStep 47319011 = 70978517) B70978517
theorem B31546007 : Blo 1943435 31546007 := bstep (se 1 (by rfl) ⟨23659505, by rfl⟩ : syracuseStep 31546007 = 47319011) B47319011
theorem B21030671 : Blo 1943435 21030671 := bstep (se 1 (by rfl) ⟨15773003, by rfl⟩ : syracuseStep 21030671 = 31546007) B31546007
theorem B14020447 : Blo 1943435 14020447 := bstep (se 1 (by rfl) ⟨10515335, by rfl⟩ : syracuseStep 14020447 = 21030671) B21030671
theorem B18693929 : Blo 1943435 18693929 := bstep (se 2 (by rfl) ⟨7010223, by rfl⟩ : syracuseStep 18693929 = 14020447) B14020447
theorem B49850477 : Blo 1943435 49850477 := bstep (se 3 (by rfl) ⟨9346964, by rfl⟩ : syracuseStep 49850477 = 18693929) B18693929
theorem B33233651 : Blo 1943435 33233651 := bstep (se 1 (by rfl) ⟨24925238, by rfl⟩ : syracuseStep 33233651 = 49850477) B49850477
theorem B22155767 : Blo 1943435 22155767 := bstep (se 1 (by rfl) ⟨16616825, by rfl⟩ : syracuseStep 22155767 = 33233651) B33233651
theorem B14770511 : Blo 1943435 14770511 := bstep (se 1 (by rfl) ⟨11077883, by rfl⟩ : syracuseStep 14770511 = 22155767) B22155767
theorem B9847007 : Blo 1943435 9847007 := bstep (se 1 (by rfl) ⟨7385255, by rfl⟩ : syracuseStep 9847007 = 14770511) B14770511
theorem B6564671 : Blo 1943435 6564671 := bstep (se 1 (by rfl) ⟨4923503, by rfl⟩ : syracuseStep 6564671 = 9847007) B9847007
theorem B4376447 : Blo 1943435 4376447 := bstep (se 1 (by rfl) ⟨3282335, by rfl⟩ : syracuseStep 4376447 = 6564671) B6564671
theorem B2917631 : Blo 1943435 2917631 := bstep (se 1 (by rfl) ⟨2188223, by rfl⟩ : syracuseStep 2917631 = 4376447) B4376447
theorem B1945087 : Blo 1943435 1945087 := bstep (se 1 (by rfl) ⟨1458815, by rfl⟩ : syracuseStep 1945087 = 2917631) B2917631
theorem B2917637 : Blo 1943435 2917637 := bbase (se 4 (by rfl) ⟨273528, by rfl⟩ : syracuseStep 2917637 = 547057) (by norm_num)
theorem B1945091 : Blo 1943435 1945091 := bstep (se 1 (by rfl) ⟨1458818, by rfl⟩ : syracuseStep 1945091 = 2917637) B2917637
theorem B3282349 : Blo 1943435 3282349 := bbase (se 3 (by rfl) ⟨615440, by rfl⟩ : syracuseStep 3282349 = 1230881) (by norm_num)
theorem B4376465 : Blo 1943435 4376465 := bstep (se 2 (by rfl) ⟨1641174, by rfl⟩ : syracuseStep 4376465 = 3282349) B3282349
theorem B2917643 : Blo 1943435 2917643 := bstep (se 1 (by rfl) ⟨2188232, by rfl⟩ : syracuseStep 2917643 = 4376465) B4376465
theorem B1945095 : Blo 1943435 1945095 := bstep (se 1 (by rfl) ⟨1458821, by rfl⟩ : syracuseStep 1945095 = 2917643) B2917643
theorem B2188237 : Blo 1943435 2188237 := bbase (se 3 (by rfl) ⟨410294, by rfl⟩ : syracuseStep 2188237 = 820589) (by norm_num)
theorem B2917649 : Blo 1943435 2917649 := bstep (se 2 (by rfl) ⟨1094118, by rfl⟩ : syracuseStep 2917649 = 2188237) B2188237
theorem B1945099 : Blo 1943435 1945099 := bstep (se 1 (by rfl) ⟨1458824, by rfl⟩ : syracuseStep 1945099 = 2917649) B2917649
theorem B6564725 : Blo 1943435 6564725 := bbase (se 5 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 6564725 = 615443) (by norm_num)
theorem B4376483 : Blo 1943435 4376483 := bstep (se 1 (by rfl) ⟨3282362, by rfl⟩ : syracuseStep 4376483 = 6564725) B6564725
theorem B2917655 : Blo 1943435 2917655 := bstep (se 1 (by rfl) ⟨2188241, by rfl⟩ : syracuseStep 2917655 = 4376483) B4376483
theorem B1945103 : Blo 1943435 1945103 := bstep (se 1 (by rfl) ⟨1458827, by rfl⟩ : syracuseStep 1945103 = 2917655) B2917655
theorem B2917661 : Blo 1943435 2917661 := bbase (se 3 (by rfl) ⟨547061, by rfl⟩ : syracuseStep 2917661 = 1094123) (by norm_num)
theorem B1945107 : Blo 1943435 1945107 := bstep (se 1 (by rfl) ⟨1458830, by rfl⟩ : syracuseStep 1945107 = 2917661) B2917661
theorem B4376501 : Blo 1943435 4376501 := bbase (se 5 (by rfl) ⟨205148, by rfl⟩ : syracuseStep 4376501 = 410297) (by norm_num)
theorem B2917667 : Blo 1943435 2917667 := bstep (se 1 (by rfl) ⟨2188250, by rfl⟩ : syracuseStep 2917667 = 4376501) B4376501
theorem B1945111 : Blo 1943435 1945111 := bstep (se 1 (by rfl) ⟨1458833, by rfl⟩ : syracuseStep 1945111 = 2917667) B2917667
theorem B15773237 : Blo 1943435 15773237 := bbase (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) (by norm_num)
theorem B10515491 : Blo 1943435 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B7010327 : Blo 1943435 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B4673551 : Blo 1943435 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B6231401 : Blo 1943435 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B4154267 : Blo 1943435 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B11078045 : Blo 1943435 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B7385363 : Blo 1943435 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B4923575 : Blo 1943435 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B3282383 : Blo 1943435 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B2188255 : Blo 1943435 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B2917673 : Blo 1943435 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B1945115 : Blo 1943435 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B6231413 : Blo 1943435 6231413 := bbase (se 5 (by rfl) ⟨292097, by rfl⟩ : syracuseStep 6231413 = 584195) (by norm_num)
theorem B4154275 : Blo 1943435 4154275 := bstep (se 1 (by rfl) ⟨3115706, by rfl⟩ : syracuseStep 4154275 = 6231413) B6231413
theorem B5539033 : Blo 1943435 5539033 := bstep (se 2 (by rfl) ⟨2077137, by rfl⟩ : syracuseStep 5539033 = 4154275) B4154275
theorem B7385377 : Blo 1943435 7385377 := bstep (se 2 (by rfl) ⟨2769516, by rfl⟩ : syracuseStep 7385377 = 5539033) B5539033
theorem B9847169 : Blo 1943435 9847169 := bstep (se 2 (by rfl) ⟨3692688, by rfl⟩ : syracuseStep 9847169 = 7385377) B7385377
theorem B6564779 : Blo 1943435 6564779 := bstep (se 1 (by rfl) ⟨4923584, by rfl⟩ : syracuseStep 6564779 = 9847169) B9847169
theorem B4376519 : Blo 1943435 4376519 := bstep (se 1 (by rfl) ⟨3282389, by rfl⟩ : syracuseStep 4376519 = 6564779) B6564779
theorem B2917679 : Blo 1943435 2917679 := bstep (se 1 (by rfl) ⟨2188259, by rfl⟩ : syracuseStep 2917679 = 4376519) B4376519
theorem B1945119 : Blo 1943435 1945119 := bstep (se 1 (by rfl) ⟨1458839, by rfl⟩ : syracuseStep 1945119 = 2917679) B2917679
theorem B2917685 : Blo 1943435 2917685 := bbase (se 5 (by rfl) ⟨136766, by rfl⟩ : syracuseStep 2917685 = 273533) (by norm_num)
theorem B1945123 : Blo 1943435 1945123 := bstep (se 1 (by rfl) ⟨1458842, by rfl⟩ : syracuseStep 1945123 = 2917685) B2917685
theorem B4923605 : Blo 1943435 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B3282403 : Blo 1943435 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B4376537 : Blo 1943435 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B2917691 : Blo 1943435 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B1945127 : Blo 1943435 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B2188273 : Blo 1943435 2188273 := bbase (se 2 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 2188273 = 1641205) (by norm_num)
theorem B2917697 : Blo 1943435 2917697 := bstep (se 2 (by rfl) ⟨1094136, by rfl⟩ : syracuseStep 2917697 = 2188273) B2188273
theorem B1945131 : Blo 1943435 1945131 := bstep (se 1 (by rfl) ⟨1458848, by rfl⟩ : syracuseStep 1945131 = 2917697) B2917697
theorem B9981605 : Blo 1943435 9981605 := bbase (se 4 (by rfl) ⟨935775, by rfl⟩ : syracuseStep 9981605 = 1871551) (by norm_num)
theorem B6654403 : Blo 1943435 6654403 := bstep (se 1 (by rfl) ⟨4990802, by rfl⟩ : syracuseStep 6654403 = 9981605) B9981605
theorem B8872537 : Blo 1943435 8872537 := bstep (se 2 (by rfl) ⟨3327201, by rfl⟩ : syracuseStep 8872537 = 6654403) B6654403
theorem B11830049 : Blo 1943435 11830049 := bstep (se 2 (by rfl) ⟨4436268, by rfl⟩ : syracuseStep 11830049 = 8872537) B8872537
theorem B7886699 : Blo 1943435 7886699 := bstep (se 1 (by rfl) ⟨5915024, by rfl⟩ : syracuseStep 7886699 = 11830049) B11830049
theorem B5257799 : Blo 1943435 5257799 := bstep (se 1 (by rfl) ⟨3943349, by rfl⟩ : syracuseStep 5257799 = 7886699) B7886699
theorem B3505199 : Blo 1943435 3505199 := bstep (se 1 (by rfl) ⟨2628899, by rfl⟩ : syracuseStep 3505199 = 5257799) B5257799
theorem B9347197 : Blo 1943435 9347197 := bstep (se 3 (by rfl) ⟨1752599, by rfl⟩ : syracuseStep 9347197 = 3505199) B3505199
theorem B12462929 : Blo 1943435 12462929 := bstep (se 2 (by rfl) ⟨4673598, by rfl⟩ : syracuseStep 12462929 = 9347197) B9347197
theorem B8308619 : Blo 1943435 8308619 := bstep (se 1 (by rfl) ⟨6231464, by rfl⟩ : syracuseStep 8308619 = 12462929) B12462929
theorem B5539079 : Blo 1943435 5539079 := bstep (se 1 (by rfl) ⟨4154309, by rfl⟩ : syracuseStep 5539079 = 8308619) B8308619
theorem B3692719 : Blo 1943435 3692719 := bstep (se 1 (by rfl) ⟨2769539, by rfl⟩ : syracuseStep 3692719 = 5539079) B5539079
theorem B4923625 : Blo 1943435 4923625 := bstep (se 2 (by rfl) ⟨1846359, by rfl⟩ : syracuseStep 4923625 = 3692719) B3692719
theorem B6564833 : Blo 1943435 6564833 := bstep (se 2 (by rfl) ⟨2461812, by rfl⟩ : syracuseStep 6564833 = 4923625) B4923625
theorem B4376555 : Blo 1943435 4376555 := bstep (se 1 (by rfl) ⟨3282416, by rfl⟩ : syracuseStep 4376555 = 6564833) B6564833
theorem B2917703 : Blo 1943435 2917703 := bstep (se 1 (by rfl) ⟨2188277, by rfl⟩ : syracuseStep 2917703 = 4376555) B4376555
theorem B1945135 : Blo 1943435 1945135 := bstep (se 1 (by rfl) ⟨1458851, by rfl⟩ : syracuseStep 1945135 = 2917703) B2917703
theorem B2917709 : Blo 1943435 2917709 := bbase (se 3 (by rfl) ⟨547070, by rfl⟩ : syracuseStep 2917709 = 1094141) (by norm_num)
theorem B1945139 : Blo 1943435 1945139 := bstep (se 1 (by rfl) ⟨1458854, by rfl⟩ : syracuseStep 1945139 = 2917709) B2917709
theorem B4376573 : Blo 1943435 4376573 := bbase (se 3 (by rfl) ⟨820607, by rfl⟩ : syracuseStep 4376573 = 1641215) (by norm_num)
theorem B2917715 : Blo 1943435 2917715 := bstep (se 1 (by rfl) ⟨2188286, by rfl⟩ : syracuseStep 2917715 = 4376573) B4376573
theorem B1945143 : Blo 1943435 1945143 := bstep (se 1 (by rfl) ⟨1458857, by rfl⟩ : syracuseStep 1945143 = 2917715) B2917715
theorem B3282437 : Blo 1943435 3282437 := bbase (se 4 (by rfl) ⟨307728, by rfl⟩ : syracuseStep 3282437 = 615457) (by norm_num)
theorem B2188291 : Blo 1943435 2188291 := bstep (se 1 (by rfl) ⟨1641218, by rfl⟩ : syracuseStep 2188291 = 3282437) B3282437
theorem B2917721 : Blo 1943435 2917721 := bstep (se 2 (by rfl) ⟨1094145, by rfl⟩ : syracuseStep 2917721 = 2188291) B2188291
theorem B1945147 : Blo 1943435 1945147 := bstep (se 1 (by rfl) ⟨1458860, by rfl⟩ : syracuseStep 1945147 = 2917721) B2917721
theorem B14770997 : Blo 1943435 14770997 := bbase (se 5 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 14770997 = 1384781) (by norm_num)
theorem B9847331 : Blo 1943435 9847331 := bstep (se 1 (by rfl) ⟨7385498, by rfl⟩ : syracuseStep 9847331 = 14770997) B14770997
theorem B6564887 : Blo 1943435 6564887 := bstep (se 1 (by rfl) ⟨4923665, by rfl⟩ : syracuseStep 6564887 = 9847331) B9847331
theorem B4376591 : Blo 1943435 4376591 := bstep (se 1 (by rfl) ⟨3282443, by rfl⟩ : syracuseStep 4376591 = 6564887) B6564887
theorem B2917727 : Blo 1943435 2917727 := bstep (se 1 (by rfl) ⟨2188295, by rfl⟩ : syracuseStep 2917727 = 4376591) B4376591
theorem B1945151 : Blo 1943435 1945151 := bstep (se 1 (by rfl) ⟨1458863, by rfl⟩ : syracuseStep 1945151 = 2917727) B2917727
theorem B2917733 : Blo 1943435 2917733 := bbase (se 4 (by rfl) ⟨273537, by rfl⟩ : syracuseStep 2917733 = 547075) (by norm_num)
theorem B1945155 : Blo 1943435 1945155 := bstep (se 1 (by rfl) ⟨1458866, by rfl⟩ : syracuseStep 1945155 = 2917733) B2917733
theorem B3692765 : Blo 1943435 3692765 := bbase (se 3 (by rfl) ⟨692393, by rfl⟩ : syracuseStep 3692765 = 1384787) (by norm_num)
theorem B2461843 : Blo 1943435 2461843 := bstep (se 1 (by rfl) ⟨1846382, by rfl⟩ : syracuseStep 2461843 = 3692765) B3692765
theorem B3282457 : Blo 1943435 3282457 := bstep (se 2 (by rfl) ⟨1230921, by rfl⟩ : syracuseStep 3282457 = 2461843) B2461843
theorem B4376609 : Blo 1943435 4376609 := bstep (se 2 (by rfl) ⟨1641228, by rfl⟩ : syracuseStep 4376609 = 3282457) B3282457
theorem B2917739 : Blo 1943435 2917739 := bstep (se 1 (by rfl) ⟨2188304, by rfl⟩ : syracuseStep 2917739 = 4376609) B4376609
theorem B1945159 : Blo 1943435 1945159 := bstep (se 1 (by rfl) ⟨1458869, by rfl⟩ : syracuseStep 1945159 = 2917739) B2917739
theorem B2188309 : Blo 1943435 2188309 := bbase (se 6 (by rfl) ⟨51288, by rfl⟩ : syracuseStep 2188309 = 102577) (by norm_num)
theorem B2917745 : Blo 1943435 2917745 := bstep (se 2 (by rfl) ⟨1094154, by rfl⟩ : syracuseStep 2917745 = 2188309) B2188309
theorem B1945163 : Blo 1943435 1945163 := bstep (se 1 (by rfl) ⟨1458872, by rfl⟩ : syracuseStep 1945163 = 2917745) B2917745
theorem B2461853 : Blo 1943435 2461853 := bbase (se 3 (by rfl) ⟨461597, by rfl⟩ : syracuseStep 2461853 = 923195) (by norm_num)
theorem B6564941 : Blo 1943435 6564941 := bstep (se 3 (by rfl) ⟨1230926, by rfl⟩ : syracuseStep 6564941 = 2461853) B2461853
theorem B4376627 : Blo 1943435 4376627 := bstep (se 1 (by rfl) ⟨3282470, by rfl⟩ : syracuseStep 4376627 = 6564941) B6564941
theorem B2917751 : Blo 1943435 2917751 := bstep (se 1 (by rfl) ⟨2188313, by rfl⟩ : syracuseStep 2917751 = 4376627) B4376627
theorem B1945167 : Blo 1943435 1945167 := bstep (se 1 (by rfl) ⟨1458875, by rfl⟩ : syracuseStep 1945167 = 2917751) B2917751
theorem B2917757 : Blo 1943435 2917757 := bbase (se 3 (by rfl) ⟨547079, by rfl⟩ : syracuseStep 2917757 = 1094159) (by norm_num)
theorem B1945171 : Blo 1943435 1945171 := bstep (se 1 (by rfl) ⟨1458878, by rfl⟩ : syracuseStep 1945171 = 2917757) B2917757
theorem B4376645 : Blo 1943435 4376645 := bbase (se 4 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 4376645 = 820621) (by norm_num)
theorem B2917763 : Blo 1943435 2917763 := bstep (se 1 (by rfl) ⟨2188322, by rfl⟩ : syracuseStep 2917763 = 4376645) B4376645
theorem B1945175 : Blo 1943435 1945175 := bstep (se 1 (by rfl) ⟨1458881, by rfl⟩ : syracuseStep 1945175 = 2917763) B2917763
theorem B5539205 : Blo 1943435 5539205 := bbase (se 4 (by rfl) ⟨519300, by rfl⟩ : syracuseStep 5539205 = 1038601) (by norm_num)
theorem B3692803 : Blo 1943435 3692803 := bstep (se 1 (by rfl) ⟨2769602, by rfl⟩ : syracuseStep 3692803 = 5539205) B5539205
theorem B4923737 : Blo 1943435 4923737 := bstep (se 2 (by rfl) ⟨1846401, by rfl⟩ : syracuseStep 4923737 = 3692803) B3692803
theorem B3282491 : Blo 1943435 3282491 := bstep (se 1 (by rfl) ⟨2461868, by rfl⟩ : syracuseStep 3282491 = 4923737) B4923737
theorem B2188327 : Blo 1943435 2188327 := bstep (se 1 (by rfl) ⟨1641245, by rfl⟩ : syracuseStep 2188327 = 3282491) B3282491
theorem B2917769 : Blo 1943435 2917769 := bstep (se 2 (by rfl) ⟨1094163, by rfl⟩ : syracuseStep 2917769 = 2188327) B2188327
theorem B1945179 : Blo 1943435 1945179 := bstep (se 1 (by rfl) ⟨1458884, by rfl⟩ : syracuseStep 1945179 = 2917769) B2917769
theorem B9847493 : Blo 1943435 9847493 := bbase (se 4 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 9847493 = 1846405) (by norm_num)
theorem B6564995 : Blo 1943435 6564995 := bstep (se 1 (by rfl) ⟨4923746, by rfl⟩ : syracuseStep 6564995 = 9847493) B9847493
theorem B4376663 : Blo 1943435 4376663 := bstep (se 1 (by rfl) ⟨3282497, by rfl⟩ : syracuseStep 4376663 = 6564995) B6564995
theorem B2917775 : Blo 1943435 2917775 := bstep (se 1 (by rfl) ⟨2188331, by rfl⟩ : syracuseStep 2917775 = 4376663) B4376663
theorem B1945183 : Blo 1943435 1945183 := bstep (se 1 (by rfl) ⟨1458887, by rfl⟩ : syracuseStep 1945183 = 2917775) B2917775
theorem B2917781 : Blo 1943435 2917781 := bbase (se 6 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 2917781 = 136771) (by norm_num)
theorem B1945187 : Blo 1943435 1945187 := bstep (se 1 (by rfl) ⟨1458890, by rfl⟩ : syracuseStep 1945187 = 2917781) B2917781
theorem B4154429 : Blo 1943435 4154429 := bbase (se 3 (by rfl) ⟨778955, by rfl⟩ : syracuseStep 4154429 = 1557911) (by norm_num)
theorem B11078477 : Blo 1943435 11078477 := bstep (se 3 (by rfl) ⟨2077214, by rfl⟩ : syracuseStep 11078477 = 4154429) B4154429
theorem B7385651 : Blo 1943435 7385651 := bstep (se 1 (by rfl) ⟨5539238, by rfl⟩ : syracuseStep 7385651 = 11078477) B11078477
theorem B4923767 : Blo 1943435 4923767 := bstep (se 1 (by rfl) ⟨3692825, by rfl⟩ : syracuseStep 4923767 = 7385651) B7385651
theorem B3282511 : Blo 1943435 3282511 := bstep (se 1 (by rfl) ⟨2461883, by rfl⟩ : syracuseStep 3282511 = 4923767) B4923767
theorem B4376681 : Blo 1943435 4376681 := bstep (se 2 (by rfl) ⟨1641255, by rfl⟩ : syracuseStep 4376681 = 3282511) B3282511
theorem B2917787 : Blo 1943435 2917787 := bstep (se 1 (by rfl) ⟨2188340, by rfl⟩ : syracuseStep 2917787 = 4376681) B4376681
theorem B1945191 : Blo 1943435 1945191 := bstep (se 1 (by rfl) ⟨1458893, by rfl⟩ : syracuseStep 1945191 = 2917787) B2917787
theorem B2188345 : Blo 1943435 2188345 := bbase (se 2 (by rfl) ⟨820629, by rfl⟩ : syracuseStep 2188345 = 1641259) (by norm_num)
theorem B2917793 : Blo 1943435 2917793 := bstep (se 2 (by rfl) ⟨1094172, by rfl⟩ : syracuseStep 2917793 = 2188345) B2188345
theorem B1945195 : Blo 1943435 1945195 := bstep (se 1 (by rfl) ⟨1458896, by rfl⟩ : syracuseStep 1945195 = 2917793) B2917793
theorem B5257973 : Blo 1943435 5257973 := bbase (se 5 (by rfl) ⟨246467, by rfl⟩ : syracuseStep 5257973 = 492935) (by norm_num)
theorem B3505315 : Blo 1943435 3505315 := bstep (se 1 (by rfl) ⟨2628986, by rfl⟩ : syracuseStep 3505315 = 5257973) B5257973
theorem B4673753 : Blo 1943435 4673753 := bstep (se 2 (by rfl) ⟨1752657, by rfl⟩ : syracuseStep 4673753 = 3505315) B3505315
theorem B3115835 : Blo 1943435 3115835 := bstep (se 1 (by rfl) ⟨2336876, by rfl⟩ : syracuseStep 3115835 = 4673753) B4673753
theorem B2077223 : Blo 1943435 2077223 := bstep (se 1 (by rfl) ⟨1557917, by rfl⟩ : syracuseStep 2077223 = 3115835) B3115835
theorem B5539261 : Blo 1943435 5539261 := bstep (se 3 (by rfl) ⟨1038611, by rfl⟩ : syracuseStep 5539261 = 2077223) B2077223
theorem B7385681 : Blo 1943435 7385681 := bstep (se 2 (by rfl) ⟨2769630, by rfl⟩ : syracuseStep 7385681 = 5539261) B5539261
theorem B4923787 : Blo 1943435 4923787 := bstep (se 1 (by rfl) ⟨3692840, by rfl⟩ : syracuseStep 4923787 = 7385681) B7385681
theorem B6565049 : Blo 1943435 6565049 := bstep (se 2 (by rfl) ⟨2461893, by rfl⟩ : syracuseStep 6565049 = 4923787) B4923787
theorem B4376699 : Blo 1943435 4376699 := bstep (se 1 (by rfl) ⟨3282524, by rfl⟩ : syracuseStep 4376699 = 6565049) B6565049
theorem B2917799 : Blo 1943435 2917799 := bstep (se 1 (by rfl) ⟨2188349, by rfl⟩ : syracuseStep 2917799 = 4376699) B4376699
theorem B1945199 : Blo 1943435 1945199 := bstep (se 1 (by rfl) ⟨1458899, by rfl⟩ : syracuseStep 1945199 = 2917799) B2917799
theorem B2917805 : Blo 1943435 2917805 := bbase (se 3 (by rfl) ⟨547088, by rfl⟩ : syracuseStep 2917805 = 1094177) (by norm_num)
theorem B1945203 : Blo 1943435 1945203 := bstep (se 1 (by rfl) ⟨1458902, by rfl⟩ : syracuseStep 1945203 = 2917805) B2917805
theorem B4376717 : Blo 1943435 4376717 := bbase (se 3 (by rfl) ⟨820634, by rfl⟩ : syracuseStep 4376717 = 1641269) (by norm_num)
theorem B2917811 : Blo 1943435 2917811 := bstep (se 1 (by rfl) ⟨2188358, by rfl⟩ : syracuseStep 2917811 = 4376717) B4376717
theorem B1945207 : Blo 1943435 1945207 := bstep (se 1 (by rfl) ⟨1458905, by rfl⟩ : syracuseStep 1945207 = 2917811) B2917811
theorem B2461909 : Blo 1943435 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B3282545 : Blo 1943435 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B2188363 : Blo 1943435 2188363 := bstep (se 1 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 2188363 = 3282545) B3282545
theorem B2917817 : Blo 1943435 2917817 := bstep (se 2 (by rfl) ⟨1094181, by rfl⟩ : syracuseStep 2917817 = 2188363) B2188363
theorem B1945211 : Blo 1943435 1945211 := bstep (se 1 (by rfl) ⟨1458908, by rfl⟩ : syracuseStep 1945211 = 2917817) B2917817
theorem B19964021 : Blo 1943435 19964021 := bbase (se 5 (by rfl) ⟨935813, by rfl⟩ : syracuseStep 19964021 = 1871627) (by norm_num)
theorem B212949557 : Blo 1943435 212949557 := bstep (se 5 (by rfl) ⟨9982010, by rfl⟩ : syracuseStep 212949557 = 19964021) B19964021
theorem B141966371 : Blo 1943435 141966371 := bstep (se 1 (by rfl) ⟨106474778, by rfl⟩ : syracuseStep 141966371 = 212949557) B212949557
theorem B94644247 : Blo 1943435 94644247 := bstep (se 1 (by rfl) ⟨70983185, by rfl⟩ : syracuseStep 94644247 = 141966371) B141966371
theorem B126192329 : Blo 1943435 126192329 := bstep (se 2 (by rfl) ⟨47322123, by rfl⟩ : syracuseStep 126192329 = 94644247) B94644247
theorem B84128219 : Blo 1943435 84128219 := bstep (se 1 (by rfl) ⟨63096164, by rfl⟩ : syracuseStep 84128219 = 126192329) B126192329
theorem B56085479 : Blo 1943435 56085479 := bstep (se 1 (by rfl) ⟨42064109, by rfl⟩ : syracuseStep 56085479 = 84128219) B84128219
theorem B37390319 : Blo 1943435 37390319 := bstep (se 1 (by rfl) ⟨28042739, by rfl⟩ : syracuseStep 37390319 = 56085479) B56085479
theorem B24926879 : Blo 1943435 24926879 := bstep (se 1 (by rfl) ⟨18695159, by rfl⟩ : syracuseStep 24926879 = 37390319) B37390319
theorem B16617919 : Blo 1943435 16617919 := bstep (se 1 (by rfl) ⟨12463439, by rfl⟩ : syracuseStep 16617919 = 24926879) B24926879
theorem B22157225 : Blo 1943435 22157225 := bstep (se 2 (by rfl) ⟨8308959, by rfl⟩ : syracuseStep 22157225 = 16617919) B16617919
theorem B14771483 : Blo 1943435 14771483 := bstep (se 1 (by rfl) ⟨11078612, by rfl⟩ : syracuseStep 14771483 = 22157225) B22157225
theorem B9847655 : Blo 1943435 9847655 := bstep (se 1 (by rfl) ⟨7385741, by rfl⟩ : syracuseStep 9847655 = 14771483) B14771483
theorem B6565103 : Blo 1943435 6565103 := bstep (se 1 (by rfl) ⟨4923827, by rfl⟩ : syracuseStep 6565103 = 9847655) B9847655
theorem B4376735 : Blo 1943435 4376735 := bstep (se 1 (by rfl) ⟨3282551, by rfl⟩ : syracuseStep 4376735 = 6565103) B6565103
theorem B2917823 : Blo 1943435 2917823 := bstep (se 1 (by rfl) ⟨2188367, by rfl⟩ : syracuseStep 2917823 = 4376735) B4376735
theorem B1945215 : Blo 1943435 1945215 := bstep (se 1 (by rfl) ⟨1458911, by rfl⟩ : syracuseStep 1945215 = 2917823) B2917823
theorem B2917829 : Blo 1943435 2917829 := bbase (se 4 (by rfl) ⟨273546, by rfl⟩ : syracuseStep 2917829 = 547093) (by norm_num)
theorem B1945219 : Blo 1943435 1945219 := bstep (se 1 (by rfl) ⟨1458914, by rfl⟩ : syracuseStep 1945219 = 2917829) B2917829
theorem B3282565 : Blo 1943435 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B4376753 : Blo 1943435 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B2917835 : Blo 1943435 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1945223 : Blo 1943435 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B2188381 : Blo 1943435 2188381 := bbase (se 3 (by rfl) ⟨410321, by rfl⟩ : syracuseStep 2188381 = 820643) (by norm_num)
theorem B2917841 : Blo 1943435 2917841 := bstep (se 2 (by rfl) ⟨1094190, by rfl⟩ : syracuseStep 2917841 = 2188381) B2188381
theorem B1945227 : Blo 1943435 1945227 := bstep (se 1 (by rfl) ⟨1458920, by rfl⟩ : syracuseStep 1945227 = 2917841) B2917841
theorem B6565157 : Blo 1943435 6565157 := bbase (se 4 (by rfl) ⟨615483, by rfl⟩ : syracuseStep 6565157 = 1230967) (by norm_num)
theorem B4376771 : Blo 1943435 4376771 := bstep (se 1 (by rfl) ⟨3282578, by rfl⟩ : syracuseStep 4376771 = 6565157) B6565157
theorem B2917847 : Blo 1943435 2917847 := bstep (se 1 (by rfl) ⟨2188385, by rfl⟩ : syracuseStep 2917847 = 4376771) B4376771
theorem B1945231 : Blo 1943435 1945231 := bstep (se 1 (by rfl) ⟨1458923, by rfl⟩ : syracuseStep 1945231 = 2917847) B2917847
theorem B2917853 : Blo 1943435 2917853 := bbase (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) (by norm_num)
theorem B1945235 : Blo 1943435 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B4376789 : Blo 1943435 4376789 := bbase (se 7 (by rfl) ⟨51290, by rfl⟩ : syracuseStep 4376789 = 102581) (by norm_num)
theorem B2917859 : Blo 1943435 2917859 := bstep (se 1 (by rfl) ⟨2188394, by rfl⟩ : syracuseStep 2917859 = 4376789) B4376789
theorem B1945239 : Blo 1943435 1945239 := bstep (se 1 (by rfl) ⟨1458929, by rfl⟩ : syracuseStep 1945239 = 2917859) B2917859
theorem B9347717 : Blo 1943435 9347717 := bbase (se 4 (by rfl) ⟨876348, by rfl⟩ : syracuseStep 9347717 = 1752697) (by norm_num)
theorem B6231811 : Blo 1943435 6231811 := bstep (se 1 (by rfl) ⟨4673858, by rfl⟩ : syracuseStep 6231811 = 9347717) B9347717
theorem B8309081 : Blo 1943435 8309081 := bstep (se 2 (by rfl) ⟨3115905, by rfl⟩ : syracuseStep 8309081 = 6231811) B6231811
theorem B5539387 : Blo 1943435 5539387 := bstep (se 1 (by rfl) ⟨4154540, by rfl⟩ : syracuseStep 5539387 = 8309081) B8309081
theorem B7385849 : Blo 1943435 7385849 := bstep (se 2 (by rfl) ⟨2769693, by rfl⟩ : syracuseStep 7385849 = 5539387) B5539387
theorem B4923899 : Blo 1943435 4923899 := bstep (se 1 (by rfl) ⟨3692924, by rfl⟩ : syracuseStep 4923899 = 7385849) B7385849
theorem B3282599 : Blo 1943435 3282599 := bstep (se 1 (by rfl) ⟨2461949, by rfl⟩ : syracuseStep 3282599 = 4923899) B4923899
theorem B2188399 : Blo 1943435 2188399 := bstep (se 1 (by rfl) ⟨1641299, by rfl⟩ : syracuseStep 2188399 = 3282599) B3282599
theorem B2917865 : Blo 1943435 2917865 := bstep (se 2 (by rfl) ⟨1094199, by rfl⟩ : syracuseStep 2917865 = 2188399) B2188399
theorem B1945243 : Blo 1943435 1945243 := bstep (se 1 (by rfl) ⟨1458932, by rfl⟩ : syracuseStep 1945243 = 2917865) B2917865
theorem B5258101 : Blo 1943435 5258101 := bbase (se 5 (by rfl) ⟨246473, by rfl⟩ : syracuseStep 5258101 = 492947) (by norm_num)
theorem B7010801 : Blo 1943435 7010801 := bstep (se 2 (by rfl) ⟨2629050, by rfl⟩ : syracuseStep 7010801 = 5258101) B5258101
theorem B4673867 : Blo 1943435 4673867 := bstep (se 1 (by rfl) ⟨3505400, by rfl⟩ : syracuseStep 4673867 = 7010801) B7010801
theorem B12463645 : Blo 1943435 12463645 := bstep (se 3 (by rfl) ⟨2336933, by rfl⟩ : syracuseStep 12463645 = 4673867) B4673867
theorem B16618193 : Blo 1943435 16618193 := bstep (se 2 (by rfl) ⟨6231822, by rfl⟩ : syracuseStep 16618193 = 12463645) B12463645
theorem B11078795 : Blo 1943435 11078795 := bstep (se 1 (by rfl) ⟨8309096, by rfl⟩ : syracuseStep 11078795 = 16618193) B16618193
theorem B7385863 : Blo 1943435 7385863 := bstep (se 1 (by rfl) ⟨5539397, by rfl⟩ : syracuseStep 7385863 = 11078795) B11078795
theorem B9847817 : Blo 1943435 9847817 := bstep (se 2 (by rfl) ⟨3692931, by rfl⟩ : syracuseStep 9847817 = 7385863) B7385863
theorem B6565211 : Blo 1943435 6565211 := bstep (se 1 (by rfl) ⟨4923908, by rfl⟩ : syracuseStep 6565211 = 9847817) B9847817
theorem B4376807 : Blo 1943435 4376807 := bstep (se 1 (by rfl) ⟨3282605, by rfl⟩ : syracuseStep 4376807 = 6565211) B6565211
theorem B2917871 : Blo 1943435 2917871 := bstep (se 1 (by rfl) ⟨2188403, by rfl⟩ : syracuseStep 2917871 = 4376807) B4376807
theorem B1945247 : Blo 1943435 1945247 := bstep (se 1 (by rfl) ⟨1458935, by rfl⟩ : syracuseStep 1945247 = 2917871) B2917871
theorem B2917877 : Blo 1943435 2917877 := bbase (se 5 (by rfl) ⟨136775, by rfl⟩ : syracuseStep 2917877 = 273551) (by norm_num)
theorem B1945251 : Blo 1943435 1945251 := bstep (se 1 (by rfl) ⟨1458938, by rfl⟩ : syracuseStep 1945251 = 2917877) B2917877
theorem B3115925 : Blo 1943435 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B2077283 : Blo 1943435 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B5539421 : Blo 1943435 5539421 := bstep (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) B2077283
theorem B3692947 : Blo 1943435 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B4923929 : Blo 1943435 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B3282619 : Blo 1943435 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B4376825 : Blo 1943435 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B2917883 : Blo 1943435 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B1945255 : Blo 1943435 1945255 := bstep (se 1 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 1945255 = 2917883) B2917883
theorem B2188417 : Blo 1943435 2188417 := bbase (se 2 (by rfl) ⟨820656, by rfl⟩ : syracuseStep 2188417 = 1641313) (by norm_num)
theorem B2917889 : Blo 1943435 2917889 := bstep (se 2 (by rfl) ⟨1094208, by rfl⟩ : syracuseStep 2917889 = 2188417) B2188417
theorem B1945259 : Blo 1943435 1945259 := bstep (se 1 (by rfl) ⟨1458944, by rfl⟩ : syracuseStep 1945259 = 2917889) B2917889
theorem B4923949 : Blo 1943435 4923949 := bbase (se 3 (by rfl) ⟨923240, by rfl⟩ : syracuseStep 4923949 = 1846481) (by norm_num)
theorem B6565265 : Blo 1943435 6565265 := bstep (se 2 (by rfl) ⟨2461974, by rfl⟩ : syracuseStep 6565265 = 4923949) B4923949
theorem B4376843 : Blo 1943435 4376843 := bstep (se 1 (by rfl) ⟨3282632, by rfl⟩ : syracuseStep 4376843 = 6565265) B6565265
theorem B2917895 : Blo 1943435 2917895 := bstep (se 1 (by rfl) ⟨2188421, by rfl⟩ : syracuseStep 2917895 = 4376843) B4376843
theorem B1945263 : Blo 1943435 1945263 := bstep (se 1 (by rfl) ⟨1458947, by rfl⟩ : syracuseStep 1945263 = 2917895) B2917895
theorem B2917901 : Blo 1943435 2917901 := bbase (se 3 (by rfl) ⟨547106, by rfl⟩ : syracuseStep 2917901 = 1094213) (by norm_num)
theorem B1945267 : Blo 1943435 1945267 := bstep (se 1 (by rfl) ⟨1458950, by rfl⟩ : syracuseStep 1945267 = 2917901) B2917901
theorem B4376861 : Blo 1943435 4376861 := bbase (se 3 (by rfl) ⟨820661, by rfl⟩ : syracuseStep 4376861 = 1641323) (by norm_num)
theorem B2917907 : Blo 1943435 2917907 := bstep (se 1 (by rfl) ⟨2188430, by rfl⟩ : syracuseStep 2917907 = 4376861) B4376861
theorem B1945271 : Blo 1943435 1945271 := bstep (se 1 (by rfl) ⟨1458953, by rfl⟩ : syracuseStep 1945271 = 2917907) B2917907
theorem B3282653 : Blo 1943435 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B2188435 : Blo 1943435 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B2917913 : Blo 1943435 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B1945275 : Blo 1943435 1945275 := bstep (se 1 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 1945275 = 2917913) B2917913
theorem B6231925 : Blo 1943435 6231925 := bbase (se 5 (by rfl) ⟨292121, by rfl⟩ : syracuseStep 6231925 = 584243) (by norm_num)
theorem B8309233 : Blo 1943435 8309233 := bstep (se 2 (by rfl) ⟨3115962, by rfl⟩ : syracuseStep 8309233 = 6231925) B6231925
theorem B11078977 : Blo 1943435 11078977 := bstep (se 2 (by rfl) ⟨4154616, by rfl⟩ : syracuseStep 11078977 = 8309233) B8309233
theorem B14771969 : Blo 1943435 14771969 := bstep (se 2 (by rfl) ⟨5539488, by rfl⟩ : syracuseStep 14771969 = 11078977) B11078977
theorem B9847979 : Blo 1943435 9847979 := bstep (se 1 (by rfl) ⟨7385984, by rfl⟩ : syracuseStep 9847979 = 14771969) B14771969
theorem B6565319 : Blo 1943435 6565319 := bstep (se 1 (by rfl) ⟨4923989, by rfl⟩ : syracuseStep 6565319 = 9847979) B9847979
theorem B4376879 : Blo 1943435 4376879 := bstep (se 1 (by rfl) ⟨3282659, by rfl⟩ : syracuseStep 4376879 = 6565319) B6565319
theorem B2917919 : Blo 1943435 2917919 := bstep (se 1 (by rfl) ⟨2188439, by rfl⟩ : syracuseStep 2917919 = 4376879) B4376879
theorem B1945279 : Blo 1943435 1945279 := bstep (se 1 (by rfl) ⟨1458959, by rfl⟩ : syracuseStep 1945279 = 2917919) B2917919
theorem B2917925 : Blo 1943435 2917925 := bbase (se 4 (by rfl) ⟨273555, by rfl⟩ : syracuseStep 2917925 = 547111) (by norm_num)
theorem B1945283 : Blo 1943435 1945283 := bstep (se 1 (by rfl) ⟨1458962, by rfl⟩ : syracuseStep 1945283 = 2917925) B2917925
theorem B2462005 : Blo 1943435 2462005 := bbase (se 5 (by rfl) ⟨115406, by rfl⟩ : syracuseStep 2462005 = 230813) (by norm_num)
theorem B3282673 : Blo 1943435 3282673 := bstep (se 2 (by rfl) ⟨1231002, by rfl⟩ : syracuseStep 3282673 = 2462005) B2462005
theorem B4376897 : Blo 1943435 4376897 := bstep (se 2 (by rfl) ⟨1641336, by rfl⟩ : syracuseStep 4376897 = 3282673) B3282673
theorem B2917931 : Blo 1943435 2917931 := bstep (se 1 (by rfl) ⟨2188448, by rfl⟩ : syracuseStep 2917931 = 4376897) B4376897
theorem B1945287 : Blo 1943435 1945287 := bstep (se 1 (by rfl) ⟨1458965, by rfl⟩ : syracuseStep 1945287 = 2917931) B2917931
theorem B2188453 : Blo 1943435 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B2917937 : Blo 1943435 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B1945291 : Blo 1943435 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B2807557 : Blo 1943435 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B59894549 : Blo 1943435 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B39929699 : Blo 1943435 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B26619799 : Blo 1943435 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B35493065 : Blo 1943435 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B23662043 : Blo 1943435 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B15774695 : Blo 1943435 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B10516463 : Blo 1943435 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B7010975 : Blo 1943435 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B18695933 : Blo 1943435 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B12463955 : Blo 1943435 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B8309303 : Blo 1943435 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B5539535 : Blo 1943435 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B3693023 : Blo 1943435 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B2462015 : Blo 1943435 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B6565373 : Blo 1943435 6565373 := bstep (se 3 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 6565373 = 2462015) B2462015
theorem B4376915 : Blo 1943435 4376915 := bstep (se 1 (by rfl) ⟨3282686, by rfl⟩ : syracuseStep 4376915 = 6565373) B6565373
theorem B2917943 : Blo 1943435 2917943 := bstep (se 1 (by rfl) ⟨2188457, by rfl⟩ : syracuseStep 2917943 = 4376915) B4376915
theorem B1945295 : Blo 1943435 1945295 := bstep (se 1 (by rfl) ⟨1458971, by rfl⟩ : syracuseStep 1945295 = 2917943) B2917943
theorem B2917949 : Blo 1943435 2917949 := bbase (se 3 (by rfl) ⟨547115, by rfl⟩ : syracuseStep 2917949 = 1094231) (by norm_num)
theorem B1945299 : Blo 1943435 1945299 := bstep (se 1 (by rfl) ⟨1458974, by rfl⟩ : syracuseStep 1945299 = 2917949) B2917949
theorem B4376933 : Blo 1943435 4376933 := bbase (se 4 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 4376933 = 820675) (by norm_num)
theorem B2917955 : Blo 1943435 2917955 := bstep (se 1 (by rfl) ⟨2188466, by rfl⟩ : syracuseStep 2917955 = 4376933) B4376933
theorem B1945303 : Blo 1943435 1945303 := bstep (se 1 (by rfl) ⟨1458977, by rfl⟩ : syracuseStep 1945303 = 2917955) B2917955
theorem B4924061 : Blo 1943435 4924061 := bbase (se 3 (by rfl) ⟨923261, by rfl⟩ : syracuseStep 4924061 = 1846523) (by norm_num)
theorem B3282707 : Blo 1943435 3282707 := bstep (se 1 (by rfl) ⟨2462030, by rfl⟩ : syracuseStep 3282707 = 4924061) B4924061
theorem B2188471 : Blo 1943435 2188471 := bstep (se 1 (by rfl) ⟨1641353, by rfl⟩ : syracuseStep 2188471 = 3282707) B3282707
theorem B2917961 : Blo 1943435 2917961 := bstep (se 2 (by rfl) ⟨1094235, by rfl⟩ : syracuseStep 2917961 = 2188471) B2188471
theorem B1945307 : Blo 1943435 1945307 := bstep (se 1 (by rfl) ⟨1458980, by rfl⟩ : syracuseStep 1945307 = 2917961) B2917961
theorem B3693053 : Blo 1943435 3693053 := bbase (se 3 (by rfl) ⟨692447, by rfl⟩ : syracuseStep 3693053 = 1384895) (by norm_num)
theorem B9848141 : Blo 1943435 9848141 := bstep (se 3 (by rfl) ⟨1846526, by rfl⟩ : syracuseStep 9848141 = 3693053) B3693053
theorem B6565427 : Blo 1943435 6565427 := bstep (se 1 (by rfl) ⟨4924070, by rfl⟩ : syracuseStep 6565427 = 9848141) B9848141
theorem B4376951 : Blo 1943435 4376951 := bstep (se 1 (by rfl) ⟨3282713, by rfl⟩ : syracuseStep 4376951 = 6565427) B6565427
theorem B2917967 : Blo 1943435 2917967 := bstep (se 1 (by rfl) ⟨2188475, by rfl⟩ : syracuseStep 2917967 = 4376951) B4376951
theorem B1945311 : Blo 1943435 1945311 := bstep (se 1 (by rfl) ⟨1458983, by rfl⟩ : syracuseStep 1945311 = 2917967) B2917967
theorem B2917973 : Blo 1943435 2917973 := bbase (se 8 (by rfl) ⟨17097, by rfl⟩ : syracuseStep 2917973 = 34195) (by norm_num)
theorem B1945315 : Blo 1943435 1945315 := bstep (se 1 (by rfl) ⟨1458986, by rfl⟩ : syracuseStep 1945315 = 2917973) B2917973
theorem B3327517 : Blo 1943435 3327517 := bbase (se 3 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 3327517 = 1247819) (by norm_num)
theorem B4436689 : Blo 1943435 4436689 := bstep (se 2 (by rfl) ⟨1663758, by rfl⟩ : syracuseStep 4436689 = 3327517) B3327517
theorem B5915585 : Blo 1943435 5915585 := bstep (se 2 (by rfl) ⟨2218344, by rfl⟩ : syracuseStep 5915585 = 4436689) B4436689
theorem B3943723 : Blo 1943435 3943723 := bstep (se 1 (by rfl) ⟨2957792, by rfl⟩ : syracuseStep 3943723 = 5915585) B5915585
theorem B5258297 : Blo 1943435 5258297 := bstep (se 2 (by rfl) ⟨1971861, by rfl⟩ : syracuseStep 5258297 = 3943723) B3943723
theorem B3505531 : Blo 1943435 3505531 := bstep (se 1 (by rfl) ⟨2629148, by rfl⟩ : syracuseStep 3505531 = 5258297) B5258297
theorem B4674041 : Blo 1943435 4674041 := bstep (se 2 (by rfl) ⟨1752765, by rfl⟩ : syracuseStep 4674041 = 3505531) B3505531
theorem B3116027 : Blo 1943435 3116027 := bstep (se 1 (by rfl) ⟨2337020, by rfl⟩ : syracuseStep 3116027 = 4674041) B4674041
theorem B8309405 : Blo 1943435 8309405 := bstep (se 3 (by rfl) ⟨1558013, by rfl⟩ : syracuseStep 8309405 = 3116027) B3116027
theorem B5539603 : Blo 1943435 5539603 := bstep (se 1 (by rfl) ⟨4154702, by rfl⟩ : syracuseStep 5539603 = 8309405) B8309405
theorem B7386137 : Blo 1943435 7386137 := bstep (se 2 (by rfl) ⟨2769801, by rfl⟩ : syracuseStep 7386137 = 5539603) B5539603
theorem B4924091 : Blo 1943435 4924091 := bstep (se 1 (by rfl) ⟨3693068, by rfl⟩ : syracuseStep 4924091 = 7386137) B7386137
theorem B3282727 : Blo 1943435 3282727 := bstep (se 1 (by rfl) ⟨2462045, by rfl⟩ : syracuseStep 3282727 = 4924091) B4924091
theorem B4376969 : Blo 1943435 4376969 := bstep (se 2 (by rfl) ⟨1641363, by rfl⟩ : syracuseStep 4376969 = 3282727) B3282727
theorem B2917979 : Blo 1943435 2917979 := bstep (se 1 (by rfl) ⟨2188484, by rfl⟩ : syracuseStep 2917979 = 4376969) B4376969
theorem B1945319 : Blo 1943435 1945319 := bstep (se 1 (by rfl) ⟨1458989, by rfl⟩ : syracuseStep 1945319 = 2917979) B2917979
theorem B2188489 : Blo 1943435 2188489 := bbase (se 2 (by rfl) ⟨820683, by rfl⟩ : syracuseStep 2188489 = 1641367) (by norm_num)
theorem B2917985 : Blo 1943435 2917985 := bstep (se 2 (by rfl) ⟨1094244, by rfl⟩ : syracuseStep 2917985 = 2188489) B2188489
theorem B1945323 : Blo 1943435 1945323 := bstep (se 1 (by rfl) ⟨1458992, by rfl⟩ : syracuseStep 1945323 = 2917985) B2917985
theorem B1971869 : Blo 1943435 1971869 := bbase (se 3 (by rfl) ⟨369725, by rfl⟩ : syracuseStep 1971869 = 739451) (by norm_num)
theorem B21033269 : Blo 1943435 21033269 := bstep (se 5 (by rfl) ⟨985934, by rfl⟩ : syracuseStep 21033269 = 1971869) B1971869
theorem B14022179 : Blo 1943435 14022179 := bstep (se 1 (by rfl) ⟨10516634, by rfl⟩ : syracuseStep 14022179 = 21033269) B21033269
theorem B9348119 : Blo 1943435 9348119 := bstep (se 1 (by rfl) ⟨7011089, by rfl⟩ : syracuseStep 9348119 = 14022179) B14022179
theorem B6232079 : Blo 1943435 6232079 := bstep (se 1 (by rfl) ⟨4674059, by rfl⟩ : syracuseStep 6232079 = 9348119) B9348119
theorem B16618877 : Blo 1943435 16618877 := bstep (se 3 (by rfl) ⟨3116039, by rfl⟩ : syracuseStep 16618877 = 6232079) B6232079
theorem B11079251 : Blo 1943435 11079251 := bstep (se 1 (by rfl) ⟨8309438, by rfl⟩ : syracuseStep 11079251 = 16618877) B16618877
theorem B7386167 : Blo 1943435 7386167 := bstep (se 1 (by rfl) ⟨5539625, by rfl⟩ : syracuseStep 7386167 = 11079251) B11079251
theorem B4924111 : Blo 1943435 4924111 := bstep (se 1 (by rfl) ⟨3693083, by rfl⟩ : syracuseStep 4924111 = 7386167) B7386167
theorem B6565481 : Blo 1943435 6565481 := bstep (se 2 (by rfl) ⟨2462055, by rfl⟩ : syracuseStep 6565481 = 4924111) B4924111
theorem B4376987 : Blo 1943435 4376987 := bstep (se 1 (by rfl) ⟨3282740, by rfl⟩ : syracuseStep 4376987 = 6565481) B6565481
theorem B2917991 : Blo 1943435 2917991 := bstep (se 1 (by rfl) ⟨2188493, by rfl⟩ : syracuseStep 2917991 = 4376987) B4376987
theorem B1945327 : Blo 1943435 1945327 := bstep (se 1 (by rfl) ⟨1458995, by rfl⟩ : syracuseStep 1945327 = 2917991) B2917991
theorem B2917997 : Blo 1943435 2917997 := bbase (se 3 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 2917997 = 1094249) (by norm_num)
theorem B1945331 : Blo 1943435 1945331 := bstep (se 1 (by rfl) ⟨1458998, by rfl⟩ : syracuseStep 1945331 = 2917997) B2917997
theorem B4377005 : Blo 1943435 4377005 := bbase (se 3 (by rfl) ⟨820688, by rfl⟩ : syracuseStep 4377005 = 1641377) (by norm_num)
theorem B2918003 : Blo 1943435 2918003 := bstep (se 1 (by rfl) ⟨2188502, by rfl⟩ : syracuseStep 2918003 = 4377005) B4377005
theorem B1945335 : Blo 1943435 1945335 := bstep (se 1 (by rfl) ⟨1459001, by rfl⟩ : syracuseStep 1945335 = 2918003) B2918003
theorem B2077373 : Blo 1943435 2077373 := bbase (se 3 (by rfl) ⟨389507, by rfl⟩ : syracuseStep 2077373 = 779015) (by norm_num)
theorem B5539661 : Blo 1943435 5539661 := bstep (se 3 (by rfl) ⟨1038686, by rfl⟩ : syracuseStep 5539661 = 2077373) B2077373
theorem B3693107 : Blo 1943435 3693107 := bstep (se 1 (by rfl) ⟨2769830, by rfl⟩ : syracuseStep 3693107 = 5539661) B5539661
theorem B2462071 : Blo 1943435 2462071 := bstep (se 1 (by rfl) ⟨1846553, by rfl⟩ : syracuseStep 2462071 = 3693107) B3693107
theorem B3282761 : Blo 1943435 3282761 := bstep (se 2 (by rfl) ⟨1231035, by rfl⟩ : syracuseStep 3282761 = 2462071) B2462071
theorem B2188507 : Blo 1943435 2188507 := bstep (se 1 (by rfl) ⟨1641380, by rfl⟩ : syracuseStep 2188507 = 3282761) B3282761
theorem B2918009 : Blo 1943435 2918009 := bstep (se 2 (by rfl) ⟨1094253, by rfl⟩ : syracuseStep 2918009 = 2188507) B2188507
theorem B1945339 : Blo 1943435 1945339 := bstep (se 1 (by rfl) ⟨1459004, by rfl⟩ : syracuseStep 1945339 = 2918009) B2918009
theorem B4052117 : Blo 1943435 4052117 := bbase (se 6 (by rfl) ⟨94971, by rfl⟩ : syracuseStep 4052117 = 189943) (by norm_num)
theorem B10805645 : Blo 1943435 10805645 := bstep (se 3 (by rfl) ⟨2026058, by rfl⟩ : syracuseStep 10805645 = 4052117) B4052117
theorem B7203763 : Blo 1943435 7203763 := bstep (se 1 (by rfl) ⟨5402822, by rfl⟩ : syracuseStep 7203763 = 10805645) B10805645
theorem B9605017 : Blo 1943435 9605017 := bstep (se 2 (by rfl) ⟨3601881, by rfl⟩ : syracuseStep 9605017 = 7203763) B7203763
theorem B12806689 : Blo 1943435 12806689 := bstep (se 2 (by rfl) ⟨4802508, by rfl⟩ : syracuseStep 12806689 = 9605017) B9605017
theorem B17075585 : Blo 1943435 17075585 := bstep (se 2 (by rfl) ⟨6403344, by rfl⟩ : syracuseStep 17075585 = 12806689) B12806689
theorem B11383723 : Blo 1943435 11383723 := bstep (se 1 (by rfl) ⟨8537792, by rfl⟩ : syracuseStep 11383723 = 17075585) B17075585
theorem B60713189 : Blo 1943435 60713189 := bstep (se 4 (by rfl) ⟨5691861, by rfl⟩ : syracuseStep 60713189 = 11383723) B11383723
theorem B40475459 : Blo 1943435 40475459 := bstep (se 1 (by rfl) ⟨30356594, by rfl⟩ : syracuseStep 40475459 = 60713189) B60713189
theorem B26983639 : Blo 1943435 26983639 := bstep (se 1 (by rfl) ⟨20237729, by rfl⟩ : syracuseStep 26983639 = 40475459) B40475459
theorem B35978185 : Blo 1943435 35978185 := bstep (se 2 (by rfl) ⟨13491819, by rfl⟩ : syracuseStep 35978185 = 26983639) B26983639
theorem B47970913 : Blo 1943435 47970913 := bstep (se 2 (by rfl) ⟨17989092, by rfl⟩ : syracuseStep 47970913 = 35978185) B35978185
theorem B63961217 : Blo 1943435 63961217 := bstep (se 2 (by rfl) ⟨23985456, by rfl⟩ : syracuseStep 63961217 = 47970913) B47970913
theorem B42640811 : Blo 1943435 42640811 := bstep (se 1 (by rfl) ⟨31980608, by rfl⟩ : syracuseStep 42640811 = 63961217) B63961217
theorem B28427207 : Blo 1943435 28427207 := bstep (se 1 (by rfl) ⟨21320405, by rfl⟩ : syracuseStep 28427207 = 42640811) B42640811
theorem B75805885 : Blo 1943435 75805885 := bstep (se 3 (by rfl) ⟨14213603, by rfl⟩ : syracuseStep 75805885 = 28427207) B28427207
theorem B101074513 : Blo 1943435 101074513 := bstep (se 2 (by rfl) ⟨37902942, by rfl⟩ : syracuseStep 101074513 = 75805885) B75805885
theorem B134766017 : Blo 1943435 134766017 := bstep (se 2 (by rfl) ⟨50537256, by rfl⟩ : syracuseStep 134766017 = 101074513) B101074513
theorem B89844011 : Blo 1943435 89844011 := bstep (se 1 (by rfl) ⟨67383008, by rfl⟩ : syracuseStep 89844011 = 134766017) B134766017
theorem B59896007 : Blo 1943435 59896007 := bstep (se 1 (by rfl) ⟨44922005, by rfl⟩ : syracuseStep 59896007 = 89844011) B89844011
theorem B39930671 : Blo 1943435 39930671 := bstep (se 1 (by rfl) ⟨29948003, by rfl⟩ : syracuseStep 39930671 = 59896007) B59896007
theorem B26620447 : Blo 1943435 26620447 := bstep (se 1 (by rfl) ⟨19965335, by rfl⟩ : syracuseStep 26620447 = 39930671) B39930671
theorem B35493929 : Blo 1943435 35493929 := bstep (se 2 (by rfl) ⟨13310223, by rfl⟩ : syracuseStep 35493929 = 26620447) B26620447
theorem B23662619 : Blo 1943435 23662619 := bstep (se 1 (by rfl) ⟨17746964, by rfl⟩ : syracuseStep 23662619 = 35493929) B35493929
theorem B15775079 : Blo 1943435 15775079 := bstep (se 1 (by rfl) ⟨11831309, by rfl⟩ : syracuseStep 15775079 = 23662619) B23662619
theorem B42066877 : Blo 1943435 42066877 := bstep (se 3 (by rfl) ⟨7887539, by rfl⟩ : syracuseStep 42066877 = 15775079) B15775079
theorem B56089169 : Blo 1943435 56089169 := bstep (se 2 (by rfl) ⟨21033438, by rfl⟩ : syracuseStep 56089169 = 42066877) B42066877
theorem B37392779 : Blo 1943435 37392779 := bstep (se 1 (by rfl) ⟨28044584, by rfl⟩ : syracuseStep 37392779 = 56089169) B56089169
theorem B24928519 : Blo 1943435 24928519 := bstep (se 1 (by rfl) ⟨18696389, by rfl⟩ : syracuseStep 24928519 = 37392779) B37392779
theorem B33238025 : Blo 1943435 33238025 := bstep (se 2 (by rfl) ⟨12464259, by rfl⟩ : syracuseStep 33238025 = 24928519) B24928519
theorem B22158683 : Blo 1943435 22158683 := bstep (se 1 (by rfl) ⟨16619012, by rfl⟩ : syracuseStep 22158683 = 33238025) B33238025
theorem B14772455 : Blo 1943435 14772455 := bstep (se 1 (by rfl) ⟨11079341, by rfl⟩ : syracuseStep 14772455 = 22158683) B22158683
theorem B9848303 : Blo 1943435 9848303 := bstep (se 1 (by rfl) ⟨7386227, by rfl⟩ : syracuseStep 9848303 = 14772455) B14772455
theorem B6565535 : Blo 1943435 6565535 := bstep (se 1 (by rfl) ⟨4924151, by rfl⟩ : syracuseStep 6565535 = 9848303) B9848303
theorem B4377023 : Blo 1943435 4377023 := bstep (se 1 (by rfl) ⟨3282767, by rfl⟩ : syracuseStep 4377023 = 6565535) B6565535
theorem B2918015 : Blo 1943435 2918015 := bstep (se 1 (by rfl) ⟨2188511, by rfl⟩ : syracuseStep 2918015 = 4377023) B4377023
theorem B1945343 : Blo 1943435 1945343 := bstep (se 1 (by rfl) ⟨1459007, by rfl⟩ : syracuseStep 1945343 = 2918015) B2918015
theorem B2918021 : Blo 1943435 2918021 := bbase (se 4 (by rfl) ⟨273564, by rfl⟩ : syracuseStep 2918021 = 547129) (by norm_num)
theorem B1945347 : Blo 1943435 1945347 := bstep (se 1 (by rfl) ⟨1459010, by rfl⟩ : syracuseStep 1945347 = 2918021) B2918021
theorem B3282781 : Blo 1943435 3282781 := bbase (se 3 (by rfl) ⟨615521, by rfl⟩ : syracuseStep 3282781 = 1231043) (by norm_num)
theorem B4377041 : Blo 1943435 4377041 := bstep (se 2 (by rfl) ⟨1641390, by rfl⟩ : syracuseStep 4377041 = 3282781) B3282781
theorem B2918027 : Blo 1943435 2918027 := bstep (se 1 (by rfl) ⟨2188520, by rfl⟩ : syracuseStep 2918027 = 4377041) B4377041
theorem B1945351 : Blo 1943435 1945351 := bstep (se 1 (by rfl) ⟨1459013, by rfl⟩ : syracuseStep 1945351 = 2918027) B2918027
theorem B2188525 : Blo 1943435 2188525 := bbase (se 3 (by rfl) ⟨410348, by rfl⟩ : syracuseStep 2188525 = 820697) (by norm_num)
theorem B2918033 : Blo 1943435 2918033 := bstep (se 2 (by rfl) ⟨1094262, by rfl⟩ : syracuseStep 2918033 = 2188525) B2188525
theorem B1945355 : Blo 1943435 1945355 := bstep (se 1 (by rfl) ⟨1459016, by rfl⟩ : syracuseStep 1945355 = 2918033) B2918033
theorem B6565589 : Blo 1943435 6565589 := bbase (se 7 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 6565589 = 153881) (by norm_num)
theorem B4377059 : Blo 1943435 4377059 := bstep (se 1 (by rfl) ⟨3282794, by rfl⟩ : syracuseStep 4377059 = 6565589) B6565589
theorem B2918039 : Blo 1943435 2918039 := bstep (se 1 (by rfl) ⟨2188529, by rfl⟩ : syracuseStep 2918039 = 4377059) B4377059
theorem B1945359 : Blo 1943435 1945359 := bstep (se 1 (by rfl) ⟨1459019, by rfl⟩ : syracuseStep 1945359 = 2918039) B2918039
theorem B2918045 : Blo 1943435 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B1945363 : Blo 1943435 1945363 := bstep (se 1 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 1945363 = 2918045) B2918045
theorem B4377077 : Blo 1943435 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B2918051 : Blo 1943435 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B1945367 : Blo 1943435 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B2368969 : Blo 1943435 2368969 := bbase (se 2 (by rfl) ⟨888363, by rfl⟩ : syracuseStep 2368969 = 1776727) (by norm_num)
theorem B12634501 : Blo 1943435 12634501 := bstep (se 4 (by rfl) ⟨1184484, by rfl⟩ : syracuseStep 12634501 = 2368969) B2368969
theorem B16846001 : Blo 1943435 16846001 := bstep (se 2 (by rfl) ⟨6317250, by rfl⟩ : syracuseStep 16846001 = 12634501) B12634501
theorem B11230667 : Blo 1943435 11230667 := bstep (se 1 (by rfl) ⟨8423000, by rfl⟩ : syracuseStep 11230667 = 16846001) B16846001
theorem B7487111 : Blo 1943435 7487111 := bstep (se 1 (by rfl) ⟨5615333, by rfl⟩ : syracuseStep 7487111 = 11230667) B11230667
theorem B19965629 : Blo 1943435 19965629 := bstep (se 3 (by rfl) ⟨3743555, by rfl⟩ : syracuseStep 19965629 = 7487111) B7487111
theorem B13310419 : Blo 1943435 13310419 := bstep (se 1 (by rfl) ⟨9982814, by rfl⟩ : syracuseStep 13310419 = 19965629) B19965629
theorem B17747225 : Blo 1943435 17747225 := bstep (se 2 (by rfl) ⟨6655209, by rfl⟩ : syracuseStep 17747225 = 13310419) B13310419
theorem B11831483 : Blo 1943435 11831483 := bstep (se 1 (by rfl) ⟨8873612, by rfl⟩ : syracuseStep 11831483 = 17747225) B17747225
theorem B7887655 : Blo 1943435 7887655 := bstep (se 1 (by rfl) ⟨5915741, by rfl⟩ : syracuseStep 7887655 = 11831483) B11831483
theorem B10516873 : Blo 1943435 10516873 := bstep (se 2 (by rfl) ⟨3943827, by rfl⟩ : syracuseStep 10516873 = 7887655) B7887655
theorem B14022497 : Blo 1943435 14022497 := bstep (se 2 (by rfl) ⟨5258436, by rfl⟩ : syracuseStep 14022497 = 10516873) B10516873
theorem B37393325 : Blo 1943435 37393325 := bstep (se 3 (by rfl) ⟨7011248, by rfl⟩ : syracuseStep 37393325 = 14022497) B14022497
theorem B24928883 : Blo 1943435 24928883 := bstep (se 1 (by rfl) ⟨18696662, by rfl⟩ : syracuseStep 24928883 = 37393325) B37393325
theorem B16619255 : Blo 1943435 16619255 := bstep (se 1 (by rfl) ⟨12464441, by rfl⟩ : syracuseStep 16619255 = 24928883) B24928883
theorem B11079503 : Blo 1943435 11079503 := bstep (se 1 (by rfl) ⟨8309627, by rfl⟩ : syracuseStep 11079503 = 16619255) B16619255
theorem B7386335 : Blo 1943435 7386335 := bstep (se 1 (by rfl) ⟨5539751, by rfl⟩ : syracuseStep 7386335 = 11079503) B11079503
theorem B4924223 : Blo 1943435 4924223 := bstep (se 1 (by rfl) ⟨3693167, by rfl⟩ : syracuseStep 4924223 = 7386335) B7386335
theorem B3282815 : Blo 1943435 3282815 := bstep (se 1 (by rfl) ⟨2462111, by rfl⟩ : syracuseStep 3282815 = 4924223) B4924223
theorem B2188543 : Blo 1943435 2188543 := bstep (se 1 (by rfl) ⟨1641407, by rfl⟩ : syracuseStep 2188543 = 3282815) B3282815
theorem B2918057 : Blo 1943435 2918057 := bstep (se 2 (by rfl) ⟨1094271, by rfl⟩ : syracuseStep 2918057 = 2188543) B2188543
theorem B1945371 : Blo 1943435 1945371 := bstep (se 1 (by rfl) ⟨1459028, by rfl⟩ : syracuseStep 1945371 = 2918057) B2918057
theorem B3116117 : Blo 1943435 3116117 := bbase (se 8 (by rfl) ⟨18258, by rfl⟩ : syracuseStep 3116117 = 36517) (by norm_num)
theorem B2077411 : Blo 1943435 2077411 := bstep (se 1 (by rfl) ⟨1558058, by rfl⟩ : syracuseStep 2077411 = 3116117) B3116117
theorem B2769881 : Blo 1943435 2769881 := bstep (se 2 (by rfl) ⟨1038705, by rfl⟩ : syracuseStep 2769881 = 2077411) B2077411
theorem B7386349 : Blo 1943435 7386349 := bstep (se 3 (by rfl) ⟨1384940, by rfl⟩ : syracuseStep 7386349 = 2769881) B2769881
theorem B9848465 : Blo 1943435 9848465 := bstep (se 2 (by rfl) ⟨3693174, by rfl⟩ : syracuseStep 9848465 = 7386349) B7386349
theorem B6565643 : Blo 1943435 6565643 := bstep (se 1 (by rfl) ⟨4924232, by rfl⟩ : syracuseStep 6565643 = 9848465) B9848465
theorem B4377095 : Blo 1943435 4377095 := bstep (se 1 (by rfl) ⟨3282821, by rfl⟩ : syracuseStep 4377095 = 6565643) B6565643
theorem B2918063 : Blo 1943435 2918063 := bstep (se 1 (by rfl) ⟨2188547, by rfl⟩ : syracuseStep 2918063 = 4377095) B4377095
theorem B1945375 : Blo 1943435 1945375 := bstep (se 1 (by rfl) ⟨1459031, by rfl⟩ : syracuseStep 1945375 = 2918063) B2918063
theorem B2918069 : Blo 1943435 2918069 := bbase (se 5 (by rfl) ⟨136784, by rfl⟩ : syracuseStep 2918069 = 273569) (by norm_num)
theorem B1945379 : Blo 1943435 1945379 := bstep (se 1 (by rfl) ⟨1459034, by rfl⟩ : syracuseStep 1945379 = 2918069) B2918069
theorem B4924253 : Blo 1943435 4924253 := bbase (se 3 (by rfl) ⟨923297, by rfl⟩ : syracuseStep 4924253 = 1846595) (by norm_num)
theorem B3282835 : Blo 1943435 3282835 := bstep (se 1 (by rfl) ⟨2462126, by rfl⟩ : syracuseStep 3282835 = 4924253) B4924253
theorem B4377113 : Blo 1943435 4377113 := bstep (se 2 (by rfl) ⟨1641417, by rfl⟩ : syracuseStep 4377113 = 3282835) B3282835
theorem B2918075 : Blo 1943435 2918075 := bstep (se 1 (by rfl) ⟨2188556, by rfl⟩ : syracuseStep 2918075 = 4377113) B4377113
theorem B1945383 : Blo 1943435 1945383 := bstep (se 1 (by rfl) ⟨1459037, by rfl⟩ : syracuseStep 1945383 = 2918075) B2918075
theorem B2188561 : Blo 1943435 2188561 := bbase (se 2 (by rfl) ⟨820710, by rfl⟩ : syracuseStep 2188561 = 1641421) (by norm_num)
theorem B2918081 : Blo 1943435 2918081 := bstep (se 2 (by rfl) ⟨1094280, by rfl⟩ : syracuseStep 2918081 = 2188561) B2188561
theorem B1945387 : Blo 1943435 1945387 := bstep (se 1 (by rfl) ⟨1459040, by rfl⟩ : syracuseStep 1945387 = 2918081) B2918081
theorem B3693205 : Blo 1943435 3693205 := bbase (se 6 (by rfl) ⟨86559, by rfl⟩ : syracuseStep 3693205 = 173119) (by norm_num)
theorem B4924273 : Blo 1943435 4924273 := bstep (se 2 (by rfl) ⟨1846602, by rfl⟩ : syracuseStep 4924273 = 3693205) B3693205
theorem B6565697 : Blo 1943435 6565697 := bstep (se 2 (by rfl) ⟨2462136, by rfl⟩ : syracuseStep 6565697 = 4924273) B4924273
theorem B4377131 : Blo 1943435 4377131 := bstep (se 1 (by rfl) ⟨3282848, by rfl⟩ : syracuseStep 4377131 = 6565697) B6565697
theorem B2918087 : Blo 1943435 2918087 := bstep (se 1 (by rfl) ⟨2188565, by rfl⟩ : syracuseStep 2918087 = 4377131) B4377131
theorem B1945391 : Blo 1943435 1945391 := bstep (se 1 (by rfl) ⟨1459043, by rfl⟩ : syracuseStep 1945391 = 2918087) B2918087
theorem B2918093 : Blo 1943435 2918093 := bbase (se 3 (by rfl) ⟨547142, by rfl⟩ : syracuseStep 2918093 = 1094285) (by norm_num)
theorem B1945395 : Blo 1943435 1945395 := bstep (se 1 (by rfl) ⟨1459046, by rfl⟩ : syracuseStep 1945395 = 2918093) B2918093
theorem B4377149 : Blo 1943435 4377149 := bbase (se 3 (by rfl) ⟨820715, by rfl⟩ : syracuseStep 4377149 = 1641431) (by norm_num)
theorem B2918099 : Blo 1943435 2918099 := bstep (se 1 (by rfl) ⟨2188574, by rfl⟩ : syracuseStep 2918099 = 4377149) B4377149
theorem B1945399 : Blo 1943435 1945399 := bstep (se 1 (by rfl) ⟨1459049, by rfl⟩ : syracuseStep 1945399 = 2918099) B2918099
theorem B3282869 : Blo 1943435 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B2188579 : Blo 1943435 2188579 := bstep (se 1 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 2188579 = 3282869) B3282869
theorem B2918105 : Blo 1943435 2918105 := bstep (se 2 (by rfl) ⟨1094289, by rfl⟩ : syracuseStep 2918105 = 2188579) B2188579
theorem B1945403 : Blo 1943435 1945403 := bstep (se 1 (by rfl) ⟨1459052, by rfl⟩ : syracuseStep 1945403 = 2918105) B2918105
theorem B2077445 : Blo 1943435 2077445 := bbase (se 4 (by rfl) ⟨194760, by rfl⟩ : syracuseStep 2077445 = 389521) (by norm_num)
theorem B5539853 : Blo 1943435 5539853 := bstep (se 3 (by rfl) ⟨1038722, by rfl⟩ : syracuseStep 5539853 = 2077445) B2077445
theorem B14772941 : Blo 1943435 14772941 := bstep (se 3 (by rfl) ⟨2769926, by rfl⟩ : syracuseStep 14772941 = 5539853) B5539853
theorem B9848627 : Blo 1943435 9848627 := bstep (se 1 (by rfl) ⟨7386470, by rfl⟩ : syracuseStep 9848627 = 14772941) B14772941
theorem B6565751 : Blo 1943435 6565751 := bstep (se 1 (by rfl) ⟨4924313, by rfl⟩ : syracuseStep 6565751 = 9848627) B9848627
theorem B4377167 : Blo 1943435 4377167 := bstep (se 1 (by rfl) ⟨3282875, by rfl⟩ : syracuseStep 4377167 = 6565751) B6565751
theorem B2918111 : Blo 1943435 2918111 := bstep (se 1 (by rfl) ⟨2188583, by rfl⟩ : syracuseStep 2918111 = 4377167) B4377167
theorem B1945407 : Blo 1943435 1945407 := bstep (se 1 (by rfl) ⟨1459055, by rfl⟩ : syracuseStep 1945407 = 2918111) B2918111
theorem B2918117 : Blo 1943435 2918117 := bbase (se 4 (by rfl) ⟨273573, by rfl⟩ : syracuseStep 2918117 = 547147) (by norm_num)
theorem B1945411 : Blo 1943435 1945411 := bstep (se 1 (by rfl) ⟨1459058, by rfl⟩ : syracuseStep 1945411 = 2918117) B2918117
theorem B5539877 : Blo 1943435 5539877 := bbase (se 4 (by rfl) ⟨519363, by rfl⟩ : syracuseStep 5539877 = 1038727) (by norm_num)
theorem B3693251 : Blo 1943435 3693251 := bstep (se 1 (by rfl) ⟨2769938, by rfl⟩ : syracuseStep 3693251 = 5539877) B5539877
theorem B2462167 : Blo 1943435 2462167 := bstep (se 1 (by rfl) ⟨1846625, by rfl⟩ : syracuseStep 2462167 = 3693251) B3693251
theorem B3282889 : Blo 1943435 3282889 := bstep (se 2 (by rfl) ⟨1231083, by rfl⟩ : syracuseStep 3282889 = 2462167) B2462167
theorem B4377185 : Blo 1943435 4377185 := bstep (se 2 (by rfl) ⟨1641444, by rfl⟩ : syracuseStep 4377185 = 3282889) B3282889
theorem B2918123 : Blo 1943435 2918123 := bstep (se 1 (by rfl) ⟨2188592, by rfl⟩ : syracuseStep 2918123 = 4377185) B4377185
theorem B1945415 : Blo 1943435 1945415 := bstep (se 1 (by rfl) ⟨1459061, by rfl⟩ : syracuseStep 1945415 = 2918123) B2918123
theorem B2188597 : Blo 1943435 2188597 := bbase (se 5 (by rfl) ⟨102590, by rfl⟩ : syracuseStep 2188597 = 205181) (by norm_num)
theorem B2918129 : Blo 1943435 2918129 := bstep (se 2 (by rfl) ⟨1094298, by rfl⟩ : syracuseStep 2918129 = 2188597) B2188597
theorem B1945419 : Blo 1943435 1945419 := bstep (se 1 (by rfl) ⟨1459064, by rfl⟩ : syracuseStep 1945419 = 2918129) B2918129
theorem B2462177 : Blo 1943435 2462177 := bbase (se 2 (by rfl) ⟨923316, by rfl⟩ : syracuseStep 2462177 = 1846633) (by norm_num)
theorem B6565805 : Blo 1943435 6565805 := bstep (se 3 (by rfl) ⟨1231088, by rfl⟩ : syracuseStep 6565805 = 2462177) B2462177
theorem B4377203 : Blo 1943435 4377203 := bstep (se 1 (by rfl) ⟨3282902, by rfl⟩ : syracuseStep 4377203 = 6565805) B6565805
theorem B2918135 : Blo 1943435 2918135 := bstep (se 1 (by rfl) ⟨2188601, by rfl⟩ : syracuseStep 2918135 = 4377203) B4377203
theorem B1945423 : Blo 1943435 1945423 := bstep (se 1 (by rfl) ⟨1459067, by rfl⟩ : syracuseStep 1945423 = 2918135) B2918135
theorem B2918141 : Blo 1943435 2918141 := bbase (se 3 (by rfl) ⟨547151, by rfl⟩ : syracuseStep 2918141 = 1094303) (by norm_num)
theorem B1945427 : Blo 1943435 1945427 := bstep (se 1 (by rfl) ⟨1459070, by rfl⟩ : syracuseStep 1945427 = 2918141) B2918141
theorem B4377221 : Blo 1943435 4377221 := bbase (se 4 (by rfl) ⟨410364, by rfl⟩ : syracuseStep 4377221 = 820729) (by norm_num)
theorem B2918147 : Blo 1943435 2918147 := bstep (se 1 (by rfl) ⟨2188610, by rfl⟩ : syracuseStep 2918147 = 4377221) B4377221
theorem B1945431 : Blo 1943435 1945431 := bstep (se 1 (by rfl) ⟨1459073, by rfl⟩ : syracuseStep 1945431 = 2918147) B2918147
theorem B2218477 : Blo 1943435 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2957969 : Blo 1943435 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B7887917 : Blo 1943435 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B5258611 : Blo 1943435 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B7011481 : Blo 1943435 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B9348641 : Blo 1943435 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B6232427 : Blo 1943435 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B4154951 : Blo 1943435 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B2769967 : Blo 1943435 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B3693289 : Blo 1943435 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B4924385 : Blo 1943435 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B3282923 : Blo 1943435 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B2188615 : Blo 1943435 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B2918153 : Blo 1943435 2918153 := bstep (se 2 (by rfl) ⟨1094307, by rfl⟩ : syracuseStep 2918153 = 2188615) B2188615
theorem B1945435 : Blo 1943435 1945435 := bstep (se 1 (by rfl) ⟨1459076, by rfl⟩ : syracuseStep 1945435 = 2918153) B2918153
theorem C0 (j : ℕ) (h1 : 485858 ≤ j) (h2 : j ≤ 486358) : Blo 1943435 (4 * j + 3) := by
  interval_cases j
  · exact B1943435
  · exact B1943439
  · exact B1943443
  · exact B1943447
  · exact B1943451
  · exact B1943455
  · exact B1943459
  · exact B1943463
  · exact B1943467
  · exact B1943471
  · exact B1943475
  · exact B1943479
  · exact B1943483
  · exact B1943487
  · exact B1943491
  · exact B1943495
  · exact B1943499
  · exact B1943503
  · exact B1943507
  · exact B1943511
  · exact B1943515
  · exact B1943519
  · exact B1943523
  · exact B1943527
  · exact B1943531
  · exact B1943535
  · exact B1943539
  · exact B1943543
  · exact B1943547
  · exact B1943551
  · exact B1943555
  · exact B1943559
  · exact B1943563
  · exact B1943567
  · exact B1943571
  · exact B1943575
  · exact B1943579
  · exact B1943583
  · exact B1943587
  · exact B1943591
  · exact B1943595
  · exact B1943599
  · exact B1943603
  · exact B1943607
  · exact B1943611
  · exact B1943615
  · exact B1943619
  · exact B1943623
  · exact B1943627
  · exact B1943631
  · exact B1943635
  · exact B1943639
  · exact B1943643
  · exact B1943647
  · exact B1943651
  · exact B1943655
  · exact B1943659
  · exact B1943663
  · exact B1943667
  · exact B1943671
  · exact B1943675
  · exact B1943679
  · exact B1943683
  · exact B1943687
  · exact B1943691
  · exact B1943695
  · exact B1943699
  · exact B1943703
  · exact B1943707
  · exact B1943711
  · exact B1943715
  · exact B1943719
  · exact B1943723
  · exact B1943727
  · exact B1943731
  · exact B1943735
  · exact B1943739
  · exact B1943743
  · exact B1943747
  · exact B1943751
  · exact B1943755
  · exact B1943759
  · exact B1943763
  · exact B1943767
  · exact B1943771
  · exact B1943775
  · exact B1943779
  · exact B1943783
  · exact B1943787
  · exact B1943791
  · exact B1943795
  · exact B1943799
  · exact B1943803
  · exact B1943807
  · exact B1943811
  · exact B1943815
  · exact B1943819
  · exact B1943823
  · exact B1943827
  · exact B1943831
  · exact B1943835
  · exact B1943839
  · exact B1943843
  · exact B1943847
  · exact B1943851
  · exact B1943855
  · exact B1943859
  · exact B1943863
  · exact B1943867
  · exact B1943871
  · exact B1943875
  · exact B1943879
  · exact B1943883
  · exact B1943887
  · exact B1943891
  · exact B1943895
  · exact B1943899
  · exact B1943903
  · exact B1943907
  · exact B1943911
  · exact B1943915
  · exact B1943919
  · exact B1943923
  · exact B1943927
  · exact B1943931
  · exact B1943935
  · exact B1943939
  · exact B1943943
  · exact B1943947
  · exact B1943951
  · exact B1943955
  · exact B1943959
  · exact B1943963
  · exact B1943967
  · exact B1943971
  · exact B1943975
  · exact B1943979
  · exact B1943983
  · exact B1943987
  · exact B1943991
  · exact B1943995
  · exact B1943999
  · exact B1944003
  · exact B1944007
  · exact B1944011
  · exact B1944015
  · exact B1944019
  · exact B1944023
  · exact B1944027
  · exact B1944031
  · exact B1944035
  · exact B1944039
  · exact B1944043
  · exact B1944047
  · exact B1944051
  · exact B1944055
  · exact B1944059
  · exact B1944063
  · exact B1944067
  · exact B1944071
  · exact B1944075
  · exact B1944079
  · exact B1944083
  · exact B1944087
  · exact B1944091
  · exact B1944095
  · exact B1944099
  · exact B1944103
  · exact B1944107
  · exact B1944111
  · exact B1944115
  · exact B1944119
  · exact B1944123
  · exact B1944127
  · exact B1944131
  · exact B1944135
  · exact B1944139
  · exact B1944143
  · exact B1944147
  · exact B1944151
  · exact B1944155
  · exact B1944159
  · exact B1944163
  · exact B1944167
  · exact B1944171
  · exact B1944175
  · exact B1944179
  · exact B1944183
  · exact B1944187
  · exact B1944191
  · exact B1944195
  · exact B1944199
  · exact B1944203
  · exact B1944207
  · exact B1944211
  · exact B1944215
  · exact B1944219
  · exact B1944223
  · exact B1944227
  · exact B1944231
  · exact B1944235
  · exact B1944239
  · exact B1944243
  · exact B1944247
  · exact B1944251
  · exact B1944255
  · exact B1944259
  · exact B1944263
  · exact B1944267
  · exact B1944271
  · exact B1944275
  · exact B1944279
  · exact B1944283
  · exact B1944287
  · exact B1944291
  · exact B1944295
  · exact B1944299
  · exact B1944303
  · exact B1944307
  · exact B1944311
  · exact B1944315
  · exact B1944319
  · exact B1944323
  · exact B1944327
  · exact B1944331
  · exact B1944335
  · exact B1944339
  · exact B1944343
  · exact B1944347
  · exact B1944351
  · exact B1944355
  · exact B1944359
  · exact B1944363
  · exact B1944367
  · exact B1944371
  · exact B1944375
  · exact B1944379
  · exact B1944383
  · exact B1944387
  · exact B1944391
  · exact B1944395
  · exact B1944399
  · exact B1944403
  · exact B1944407
  · exact B1944411
  · exact B1944415
  · exact B1944419
  · exact B1944423
  · exact B1944427
  · exact B1944431
  · exact B1944435
  · exact B1944439
  · exact B1944443
  · exact B1944447
  · exact B1944451
  · exact B1944455
  · exact B1944459
  · exact B1944463
  · exact B1944467
  · exact B1944471
  · exact B1944475
  · exact B1944479
  · exact B1944483
  · exact B1944487
  · exact B1944491
  · exact B1944495
  · exact B1944499
  · exact B1944503
  · exact B1944507
  · exact B1944511
  · exact B1944515
  · exact B1944519
  · exact B1944523
  · exact B1944527
  · exact B1944531
  · exact B1944535
  · exact B1944539
  · exact B1944543
  · exact B1944547
  · exact B1944551
  · exact B1944555
  · exact B1944559
  · exact B1944563
  · exact B1944567
  · exact B1944571
  · exact B1944575
  · exact B1944579
  · exact B1944583
  · exact B1944587
  · exact B1944591
  · exact B1944595
  · exact B1944599
  · exact B1944603
  · exact B1944607
  · exact B1944611
  · exact B1944615
  · exact B1944619
  · exact B1944623
  · exact B1944627
  · exact B1944631
  · exact B1944635
  · exact B1944639
  · exact B1944643
  · exact B1944647
  · exact B1944651
  · exact B1944655
  · exact B1944659
  · exact B1944663
  · exact B1944667
  · exact B1944671
  · exact B1944675
  · exact B1944679
  · exact B1944683
  · exact B1944687
  · exact B1944691
  · exact B1944695
  · exact B1944699
  · exact B1944703
  · exact B1944707
  · exact B1944711
  · exact B1944715
  · exact B1944719
  · exact B1944723
  · exact B1944727
  · exact B1944731
  · exact B1944735
  · exact B1944739
  · exact B1944743
  · exact B1944747
  · exact B1944751
  · exact B1944755
  · exact B1944759
  · exact B1944763
  · exact B1944767
  · exact B1944771
  · exact B1944775
  · exact B1944779
  · exact B1944783
  · exact B1944787
  · exact B1944791
  · exact B1944795
  · exact B1944799
  · exact B1944803
  · exact B1944807
  · exact B1944811
  · exact B1944815
  · exact B1944819
  · exact B1944823
  · exact B1944827
  · exact B1944831
  · exact B1944835
  · exact B1944839
  · exact B1944843
  · exact B1944847
  · exact B1944851
  · exact B1944855
  · exact B1944859
  · exact B1944863
  · exact B1944867
  · exact B1944871
  · exact B1944875
  · exact B1944879
  · exact B1944883
  · exact B1944887
  · exact B1944891
  · exact B1944895
  · exact B1944899
  · exact B1944903
  · exact B1944907
  · exact B1944911
  · exact B1944915
  · exact B1944919
  · exact B1944923
  · exact B1944927
  · exact B1944931
  · exact B1944935
  · exact B1944939
  · exact B1944943
  · exact B1944947
  · exact B1944951
  · exact B1944955
  · exact B1944959
  · exact B1944963
  · exact B1944967
  · exact B1944971
  · exact B1944975
  · exact B1944979
  · exact B1944983
  · exact B1944987
  · exact B1944991
  · exact B1944995
  · exact B1944999
  · exact B1945003
  · exact B1945007
  · exact B1945011
  · exact B1945015
  · exact B1945019
  · exact B1945023
  · exact B1945027
  · exact B1945031
  · exact B1945035
  · exact B1945039
  · exact B1945043
  · exact B1945047
  · exact B1945051
  · exact B1945055
  · exact B1945059
  · exact B1945063
  · exact B1945067
  · exact B1945071
  · exact B1945075
  · exact B1945079
  · exact B1945083
  · exact B1945087
  · exact B1945091
  · exact B1945095
  · exact B1945099
  · exact B1945103
  · exact B1945107
  · exact B1945111
  · exact B1945115
  · exact B1945119
  · exact B1945123
  · exact B1945127
  · exact B1945131
  · exact B1945135
  · exact B1945139
  · exact B1945143
  · exact B1945147
  · exact B1945151
  · exact B1945155
  · exact B1945159
  · exact B1945163
  · exact B1945167
  · exact B1945171
  · exact B1945175
  · exact B1945179
  · exact B1945183
  · exact B1945187
  · exact B1945191
  · exact B1945195
  · exact B1945199
  · exact B1945203
  · exact B1945207
  · exact B1945211
  · exact B1945215
  · exact B1945219
  · exact B1945223
  · exact B1945227
  · exact B1945231
  · exact B1945235
  · exact B1945239
  · exact B1945243
  · exact B1945247
  · exact B1945251
  · exact B1945255
  · exact B1945259
  · exact B1945263
  · exact B1945267
  · exact B1945271
  · exact B1945275
  · exact B1945279
  · exact B1945283
  · exact B1945287
  · exact B1945291
  · exact B1945295
  · exact B1945299
  · exact B1945303
  · exact B1945307
  · exact B1945311
  · exact B1945315
  · exact B1945319
  · exact B1945323
  · exact B1945327
  · exact B1945331
  · exact B1945335
  · exact B1945339
  · exact B1945343
  · exact B1945347
  · exact B1945351
  · exact B1945355
  · exact B1945359
  · exact B1945363
  · exact B1945367
  · exact B1945371
  · exact B1945375
  · exact B1945379
  · exact B1945383
  · exact B1945387
  · exact B1945391
  · exact B1945395
  · exact B1945399
  · exact B1945403
  · exact B1945407
  · exact B1945411
  · exact B1945415
  · exact B1945419
  · exact B1945423
  · exact B1945427
  · exact B1945431
  · exact B1945435
theorem solution (m : ℕ) (hlo : 1943435 ≤ m) (hhi : m ≤ 1945435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 485858 ≤ j := by omega
    have hj2 : j ≤ 486358 := by omega
    have hb : Blo 1943435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
