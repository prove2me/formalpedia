-- Prove2me | solution 1 for syracuse_descends_range_2045435_2047435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:20.174928+00:00
-- url     : https://prove2.me/submissions/d15c45bc-91b2-4064-8b67-ad56752ae09e

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

theorem B3883133 : Blo 2045435 3883133 := bbase (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) (by norm_num)
theorem B2588755 : Blo 2045435 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B3451673 : Blo 2045435 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B2301115 : Blo 2045435 2301115 := bstep (se 1 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 2301115 = 3451673) B3451673
theorem B3068153 : Blo 2045435 3068153 := bstep (se 2 (by rfl) ⟨1150557, by rfl⟩ : syracuseStep 3068153 = 2301115) B2301115
theorem B2045435 : Blo 2045435 2045435 := bstep (se 1 (by rfl) ⟨1534076, by rfl⟩ : syracuseStep 2045435 = 3068153) B3068153
theorem B3498773 : Blo 2045435 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B9330061 : Blo 2045435 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B12440081 : Blo 2045435 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B8293387 : Blo 2045435 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B11057849 : Blo 2045435 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B7371899 : Blo 2045435 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B4914599 : Blo 2045435 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B52422389 : Blo 2045435 52422389 := bstep (se 5 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 52422389 = 4914599) B4914599
theorem B34948259 : Blo 2045435 34948259 := bstep (se 1 (by rfl) ⟨26211194, by rfl⟩ : syracuseStep 34948259 = 52422389) B52422389
theorem B23298839 : Blo 2045435 23298839 := bstep (se 1 (by rfl) ⟨17474129, by rfl⟩ : syracuseStep 23298839 = 34948259) B34948259
theorem B15532559 : Blo 2045435 15532559 := bstep (se 1 (by rfl) ⟨11649419, by rfl⟩ : syracuseStep 15532559 = 23298839) B23298839
theorem B10355039 : Blo 2045435 10355039 := bstep (se 1 (by rfl) ⟨7766279, by rfl⟩ : syracuseStep 10355039 = 15532559) B15532559
theorem B6903359 : Blo 2045435 6903359 := bstep (se 1 (by rfl) ⟨5177519, by rfl⟩ : syracuseStep 6903359 = 10355039) B10355039
theorem B4602239 : Blo 2045435 4602239 := bstep (se 1 (by rfl) ⟨3451679, by rfl⟩ : syracuseStep 4602239 = 6903359) B6903359
theorem B3068159 : Blo 2045435 3068159 := bstep (se 1 (by rfl) ⟨2301119, by rfl⟩ : syracuseStep 3068159 = 4602239) B4602239
theorem B2045439 : Blo 2045435 2045439 := bstep (se 1 (by rfl) ⟨1534079, by rfl⟩ : syracuseStep 2045439 = 3068159) B3068159
theorem B3068165 : Blo 2045435 3068165 := bbase (se 4 (by rfl) ⟨287640, by rfl⟩ : syracuseStep 3068165 = 575281) (by norm_num)
theorem B2045443 : Blo 2045435 2045443 := bstep (se 1 (by rfl) ⟨1534082, by rfl⟩ : syracuseStep 2045443 = 3068165) B3068165
theorem B3451693 : Blo 2045435 3451693 := bbase (se 3 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 3451693 = 1294385) (by norm_num)
theorem B4602257 : Blo 2045435 4602257 := bstep (se 2 (by rfl) ⟨1725846, by rfl⟩ : syracuseStep 4602257 = 3451693) B3451693
theorem B3068171 : Blo 2045435 3068171 := bstep (se 1 (by rfl) ⟨2301128, by rfl⟩ : syracuseStep 3068171 = 4602257) B4602257
theorem B2045447 : Blo 2045435 2045447 := bstep (se 1 (by rfl) ⟨1534085, by rfl⟩ : syracuseStep 2045447 = 3068171) B3068171
theorem B2301133 : Blo 2045435 2301133 := bbase (se 3 (by rfl) ⟨431462, by rfl⟩ : syracuseStep 2301133 = 862925) (by norm_num)
theorem B3068177 : Blo 2045435 3068177 := bstep (se 2 (by rfl) ⟨1150566, by rfl⟩ : syracuseStep 3068177 = 2301133) B2301133
theorem B2045451 : Blo 2045435 2045451 := bstep (se 1 (by rfl) ⟨1534088, by rfl⟩ : syracuseStep 2045451 = 3068177) B3068177
theorem B6903413 : Blo 2045435 6903413 := bbase (se 5 (by rfl) ⟨323597, by rfl⟩ : syracuseStep 6903413 = 647195) (by norm_num)
theorem B4602275 : Blo 2045435 4602275 := bstep (se 1 (by rfl) ⟨3451706, by rfl⟩ : syracuseStep 4602275 = 6903413) B6903413
theorem B3068183 : Blo 2045435 3068183 := bstep (se 1 (by rfl) ⟨2301137, by rfl⟩ : syracuseStep 3068183 = 4602275) B4602275
theorem B2045455 : Blo 2045435 2045455 := bstep (se 1 (by rfl) ⟨1534091, by rfl⟩ : syracuseStep 2045455 = 3068183) B3068183
theorem B3068189 : Blo 2045435 3068189 := bbase (se 3 (by rfl) ⟨575285, by rfl⟩ : syracuseStep 3068189 = 1150571) (by norm_num)
theorem B2045459 : Blo 2045435 2045459 := bstep (se 1 (by rfl) ⟨1534094, by rfl⟩ : syracuseStep 2045459 = 3068189) B3068189
theorem B4602293 : Blo 2045435 4602293 := bbase (se 5 (by rfl) ⟨215732, by rfl⟩ : syracuseStep 4602293 = 431465) (by norm_num)
theorem B3068195 : Blo 2045435 3068195 := bstep (se 1 (by rfl) ⟨2301146, by rfl⟩ : syracuseStep 3068195 = 4602293) B4602293
theorem B2045463 : Blo 2045435 2045463 := bstep (se 1 (by rfl) ⟨1534097, by rfl⟩ : syracuseStep 2045463 = 3068195) B3068195
theorem B3276445 : Blo 2045435 3276445 := bbase (se 3 (by rfl) ⟨614333, by rfl⟩ : syracuseStep 3276445 = 1228667) (by norm_num)
theorem B4368593 : Blo 2045435 4368593 := bstep (se 2 (by rfl) ⟨1638222, by rfl⟩ : syracuseStep 4368593 = 3276445) B3276445
theorem B11649581 : Blo 2045435 11649581 := bstep (se 3 (by rfl) ⟨2184296, by rfl⟩ : syracuseStep 11649581 = 4368593) B4368593
theorem B7766387 : Blo 2045435 7766387 := bstep (se 1 (by rfl) ⟨5824790, by rfl⟩ : syracuseStep 7766387 = 11649581) B11649581
theorem B5177591 : Blo 2045435 5177591 := bstep (se 1 (by rfl) ⟨3883193, by rfl⟩ : syracuseStep 5177591 = 7766387) B7766387
theorem B3451727 : Blo 2045435 3451727 := bstep (se 1 (by rfl) ⟨2588795, by rfl⟩ : syracuseStep 3451727 = 5177591) B5177591
theorem B2301151 : Blo 2045435 2301151 := bstep (se 1 (by rfl) ⟨1725863, by rfl⟩ : syracuseStep 2301151 = 3451727) B3451727
theorem B3068201 : Blo 2045435 3068201 := bstep (se 2 (by rfl) ⟨1150575, by rfl⟩ : syracuseStep 3068201 = 2301151) B2301151
theorem B2045467 : Blo 2045435 2045467 := bstep (se 1 (by rfl) ⟨1534100, by rfl⟩ : syracuseStep 2045467 = 3068201) B3068201
theorem B4914677 : Blo 2045435 4914677 := bbase (se 5 (by rfl) ⟨230375, by rfl⟩ : syracuseStep 4914677 = 460751) (by norm_num)
theorem B3276451 : Blo 2045435 3276451 := bstep (se 1 (by rfl) ⟨2457338, by rfl⟩ : syracuseStep 3276451 = 4914677) B4914677
theorem B4368601 : Blo 2045435 4368601 := bstep (se 2 (by rfl) ⟨1638225, by rfl⟩ : syracuseStep 4368601 = 3276451) B3276451
theorem B5824801 : Blo 2045435 5824801 := bstep (se 2 (by rfl) ⟨2184300, by rfl⟩ : syracuseStep 5824801 = 4368601) B4368601
theorem B7766401 : Blo 2045435 7766401 := bstep (se 2 (by rfl) ⟨2912400, by rfl⟩ : syracuseStep 7766401 = 5824801) B5824801
theorem B10355201 : Blo 2045435 10355201 := bstep (se 2 (by rfl) ⟨3883200, by rfl⟩ : syracuseStep 10355201 = 7766401) B7766401
theorem B6903467 : Blo 2045435 6903467 := bstep (se 1 (by rfl) ⟨5177600, by rfl⟩ : syracuseStep 6903467 = 10355201) B10355201
theorem B4602311 : Blo 2045435 4602311 := bstep (se 1 (by rfl) ⟨3451733, by rfl⟩ : syracuseStep 4602311 = 6903467) B6903467
theorem B3068207 : Blo 2045435 3068207 := bstep (se 1 (by rfl) ⟨2301155, by rfl⟩ : syracuseStep 3068207 = 4602311) B4602311
theorem B2045471 : Blo 2045435 2045471 := bstep (se 1 (by rfl) ⟨1534103, by rfl⟩ : syracuseStep 2045471 = 3068207) B3068207
theorem B3068213 : Blo 2045435 3068213 := bbase (se 5 (by rfl) ⟨143822, by rfl⟩ : syracuseStep 3068213 = 287645) (by norm_num)
theorem B2045475 : Blo 2045435 2045475 := bstep (se 1 (by rfl) ⟨1534106, by rfl⟩ : syracuseStep 2045475 = 3068213) B3068213
theorem B5177621 : Blo 2045435 5177621 := bbase (se 6 (by rfl) ⟨121350, by rfl⟩ : syracuseStep 5177621 = 242701) (by norm_num)
theorem B3451747 : Blo 2045435 3451747 := bstep (se 1 (by rfl) ⟨2588810, by rfl⟩ : syracuseStep 3451747 = 5177621) B5177621
theorem B4602329 : Blo 2045435 4602329 := bstep (se 2 (by rfl) ⟨1725873, by rfl⟩ : syracuseStep 4602329 = 3451747) B3451747
theorem B3068219 : Blo 2045435 3068219 := bstep (se 1 (by rfl) ⟨2301164, by rfl⟩ : syracuseStep 3068219 = 4602329) B4602329
theorem B2045479 : Blo 2045435 2045479 := bstep (se 1 (by rfl) ⟨1534109, by rfl⟩ : syracuseStep 2045479 = 3068219) B3068219
theorem B2301169 : Blo 2045435 2301169 := bbase (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) (by norm_num)
theorem B3068225 : Blo 2045435 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B2045483 : Blo 2045435 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B4793309 : Blo 2045435 4793309 := bbase (se 3 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 4793309 = 1797491) (by norm_num)
theorem B3195539 : Blo 2045435 3195539 := bstep (se 1 (by rfl) ⟨2396654, by rfl⟩ : syracuseStep 3195539 = 4793309) B4793309
theorem B2130359 : Blo 2045435 2130359 := bstep (se 1 (by rfl) ⟨1597769, by rfl⟩ : syracuseStep 2130359 = 3195539) B3195539
theorem B5680957 : Blo 2045435 5680957 := bstep (se 3 (by rfl) ⟨1065179, by rfl⟩ : syracuseStep 5680957 = 2130359) B2130359
theorem B7574609 : Blo 2045435 7574609 := bstep (se 2 (by rfl) ⟨2840478, by rfl⟩ : syracuseStep 7574609 = 5680957) B5680957
theorem B5049739 : Blo 2045435 5049739 := bstep (se 1 (by rfl) ⟨3787304, by rfl⟩ : syracuseStep 5049739 = 7574609) B7574609
theorem B6732985 : Blo 2045435 6732985 := bstep (se 2 (by rfl) ⟨2524869, by rfl⟩ : syracuseStep 6732985 = 5049739) B5049739
theorem B8977313 : Blo 2045435 8977313 := bstep (se 2 (by rfl) ⟨3366492, by rfl⟩ : syracuseStep 8977313 = 6732985) B6732985
theorem B5984875 : Blo 2045435 5984875 := bstep (se 1 (by rfl) ⟨4488656, by rfl⟩ : syracuseStep 5984875 = 8977313) B8977313
theorem B7979833 : Blo 2045435 7979833 := bstep (se 2 (by rfl) ⟨2992437, by rfl⟩ : syracuseStep 7979833 = 5984875) B5984875
theorem B10639777 : Blo 2045435 10639777 := bstep (se 2 (by rfl) ⟨3989916, by rfl⟩ : syracuseStep 10639777 = 7979833) B7979833
theorem B14186369 : Blo 2045435 14186369 := bstep (se 2 (by rfl) ⟨5319888, by rfl⟩ : syracuseStep 14186369 = 10639777) B10639777
theorem B9457579 : Blo 2045435 9457579 := bstep (se 1 (by rfl) ⟨7093184, by rfl⟩ : syracuseStep 9457579 = 14186369) B14186369
theorem B50440421 : Blo 2045435 50440421 := bstep (se 4 (by rfl) ⟨4728789, by rfl⟩ : syracuseStep 50440421 = 9457579) B9457579
theorem B33626947 : Blo 2045435 33626947 := bstep (se 1 (by rfl) ⟨25220210, by rfl⟩ : syracuseStep 33626947 = 50440421) B50440421
theorem B44835929 : Blo 2045435 44835929 := bstep (se 2 (by rfl) ⟨16813473, by rfl⟩ : syracuseStep 44835929 = 33626947) B33626947
theorem B29890619 : Blo 2045435 29890619 := bstep (se 1 (by rfl) ⟨22417964, by rfl⟩ : syracuseStep 29890619 = 44835929) B44835929
theorem B19927079 : Blo 2045435 19927079 := bstep (se 1 (by rfl) ⟨14945309, by rfl⟩ : syracuseStep 19927079 = 29890619) B29890619
theorem B13284719 : Blo 2045435 13284719 := bstep (se 1 (by rfl) ⟨9963539, by rfl⟩ : syracuseStep 13284719 = 19927079) B19927079
theorem B8856479 : Blo 2045435 8856479 := bstep (se 1 (by rfl) ⟨6642359, by rfl⟩ : syracuseStep 8856479 = 13284719) B13284719
theorem B23617277 : Blo 2045435 23617277 := bstep (se 3 (by rfl) ⟨4428239, by rfl⟩ : syracuseStep 23617277 = 8856479) B8856479
theorem B15744851 : Blo 2045435 15744851 := bstep (se 1 (by rfl) ⟨11808638, by rfl⟩ : syracuseStep 15744851 = 23617277) B23617277
theorem B10496567 : Blo 2045435 10496567 := bstep (se 1 (by rfl) ⟨7872425, by rfl⟩ : syracuseStep 10496567 = 15744851) B15744851
theorem B27990845 : Blo 2045435 27990845 := bstep (se 3 (by rfl) ⟨5248283, by rfl⟩ : syracuseStep 27990845 = 10496567) B10496567
theorem B18660563 : Blo 2045435 18660563 := bstep (se 1 (by rfl) ⟨13995422, by rfl⟩ : syracuseStep 18660563 = 27990845) B27990845
theorem B12440375 : Blo 2045435 12440375 := bstep (se 1 (by rfl) ⟨9330281, by rfl⟩ : syracuseStep 12440375 = 18660563) B18660563
theorem B8293583 : Blo 2045435 8293583 := bstep (se 1 (by rfl) ⟨6220187, by rfl⟩ : syracuseStep 8293583 = 12440375) B12440375
theorem B5529055 : Blo 2045435 5529055 := bstep (se 1 (by rfl) ⟨4146791, by rfl⟩ : syracuseStep 5529055 = 8293583) B8293583
theorem B7372073 : Blo 2045435 7372073 := bstep (se 2 (by rfl) ⟨2764527, by rfl⟩ : syracuseStep 7372073 = 5529055) B5529055
theorem B19658861 : Blo 2045435 19658861 := bstep (se 3 (by rfl) ⟨3686036, by rfl⟩ : syracuseStep 19658861 = 7372073) B7372073
theorem B13105907 : Blo 2045435 13105907 := bstep (se 1 (by rfl) ⟨9829430, by rfl⟩ : syracuseStep 13105907 = 19658861) B19658861
theorem B8737271 : Blo 2045435 8737271 := bstep (se 1 (by rfl) ⟨6552953, by rfl⟩ : syracuseStep 8737271 = 13105907) B13105907
theorem B5824847 : Blo 2045435 5824847 := bstep (se 1 (by rfl) ⟨4368635, by rfl⟩ : syracuseStep 5824847 = 8737271) B8737271
theorem B3883231 : Blo 2045435 3883231 := bstep (se 1 (by rfl) ⟨2912423, by rfl⟩ : syracuseStep 3883231 = 5824847) B5824847
theorem B5177641 : Blo 2045435 5177641 := bstep (se 2 (by rfl) ⟨1941615, by rfl⟩ : syracuseStep 5177641 = 3883231) B3883231
theorem B6903521 : Blo 2045435 6903521 := bstep (se 2 (by rfl) ⟨2588820, by rfl⟩ : syracuseStep 6903521 = 5177641) B5177641
theorem B4602347 : Blo 2045435 4602347 := bstep (se 1 (by rfl) ⟨3451760, by rfl⟩ : syracuseStep 4602347 = 6903521) B6903521
theorem B3068231 : Blo 2045435 3068231 := bstep (se 1 (by rfl) ⟨2301173, by rfl⟩ : syracuseStep 3068231 = 4602347) B4602347
theorem B2045487 : Blo 2045435 2045487 := bstep (se 1 (by rfl) ⟨1534115, by rfl⟩ : syracuseStep 2045487 = 3068231) B3068231
theorem B3068237 : Blo 2045435 3068237 := bbase (se 3 (by rfl) ⟨575294, by rfl⟩ : syracuseStep 3068237 = 1150589) (by norm_num)
theorem B2045491 : Blo 2045435 2045491 := bstep (se 1 (by rfl) ⟨1534118, by rfl⟩ : syracuseStep 2045491 = 3068237) B3068237
theorem B4602365 : Blo 2045435 4602365 := bbase (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) (by norm_num)
theorem B3068243 : Blo 2045435 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B2045495 : Blo 2045435 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B3451781 : Blo 2045435 3451781 := bbase (se 4 (by rfl) ⟨323604, by rfl⟩ : syracuseStep 3451781 = 647209) (by norm_num)
theorem B2301187 : Blo 2045435 2301187 := bstep (se 1 (by rfl) ⟨1725890, by rfl⟩ : syracuseStep 2301187 = 3451781) B3451781
theorem B3068249 : Blo 2045435 3068249 := bstep (se 2 (by rfl) ⟨1150593, by rfl⟩ : syracuseStep 3068249 = 2301187) B2301187
theorem B2045499 : Blo 2045435 2045499 := bstep (se 1 (by rfl) ⟨1534124, by rfl⟩ : syracuseStep 2045499 = 3068249) B3068249
theorem B15533045 : Blo 2045435 15533045 := bbase (se 5 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 15533045 = 1456223) (by norm_num)
theorem B10355363 : Blo 2045435 10355363 := bstep (se 1 (by rfl) ⟨7766522, by rfl⟩ : syracuseStep 10355363 = 15533045) B15533045
theorem B6903575 : Blo 2045435 6903575 := bstep (se 1 (by rfl) ⟨5177681, by rfl⟩ : syracuseStep 6903575 = 10355363) B10355363
theorem B4602383 : Blo 2045435 4602383 := bstep (se 1 (by rfl) ⟨3451787, by rfl⟩ : syracuseStep 4602383 = 6903575) B6903575
theorem B3068255 : Blo 2045435 3068255 := bstep (se 1 (by rfl) ⟨2301191, by rfl⟩ : syracuseStep 3068255 = 4602383) B4602383
theorem B2045503 : Blo 2045435 2045503 := bstep (se 1 (by rfl) ⟨1534127, by rfl⟩ : syracuseStep 2045503 = 3068255) B3068255
theorem B3068261 : Blo 2045435 3068261 := bbase (se 4 (by rfl) ⟨287649, by rfl⟩ : syracuseStep 3068261 = 575299) (by norm_num)
theorem B2045507 : Blo 2045435 2045507 := bstep (se 1 (by rfl) ⟨1534130, by rfl⟩ : syracuseStep 2045507 = 3068261) B3068261
theorem B3883277 : Blo 2045435 3883277 := bbase (se 3 (by rfl) ⟨728114, by rfl⟩ : syracuseStep 3883277 = 1456229) (by norm_num)
theorem B2588851 : Blo 2045435 2588851 := bstep (se 1 (by rfl) ⟨1941638, by rfl⟩ : syracuseStep 2588851 = 3883277) B3883277
theorem B3451801 : Blo 2045435 3451801 := bstep (se 2 (by rfl) ⟨1294425, by rfl⟩ : syracuseStep 3451801 = 2588851) B2588851
theorem B4602401 : Blo 2045435 4602401 := bstep (se 2 (by rfl) ⟨1725900, by rfl⟩ : syracuseStep 4602401 = 3451801) B3451801
theorem B3068267 : Blo 2045435 3068267 := bstep (se 1 (by rfl) ⟨2301200, by rfl⟩ : syracuseStep 3068267 = 4602401) B4602401
theorem B2045511 : Blo 2045435 2045511 := bstep (se 1 (by rfl) ⟨1534133, by rfl⟩ : syracuseStep 2045511 = 3068267) B3068267
theorem B2301205 : Blo 2045435 2301205 := bbase (se 6 (by rfl) ⟨53934, by rfl⟩ : syracuseStep 2301205 = 107869) (by norm_num)
theorem B3068273 : Blo 2045435 3068273 := bstep (se 2 (by rfl) ⟨1150602, by rfl⟩ : syracuseStep 3068273 = 2301205) B2301205
theorem B2045515 : Blo 2045435 2045515 := bstep (se 1 (by rfl) ⟨1534136, by rfl⟩ : syracuseStep 2045515 = 3068273) B3068273
theorem B2588861 : Blo 2045435 2588861 := bbase (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) (by norm_num)
theorem B6903629 : Blo 2045435 6903629 := bstep (se 3 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 6903629 = 2588861) B2588861
theorem B4602419 : Blo 2045435 4602419 := bstep (se 1 (by rfl) ⟨3451814, by rfl⟩ : syracuseStep 4602419 = 6903629) B6903629
theorem B3068279 : Blo 2045435 3068279 := bstep (se 1 (by rfl) ⟨2301209, by rfl⟩ : syracuseStep 3068279 = 4602419) B4602419
theorem B2045519 : Blo 2045435 2045519 := bstep (se 1 (by rfl) ⟨1534139, by rfl⟩ : syracuseStep 2045519 = 3068279) B3068279
theorem B3068285 : Blo 2045435 3068285 := bbase (se 3 (by rfl) ⟨575303, by rfl⟩ : syracuseStep 3068285 = 1150607) (by norm_num)
theorem B2045523 : Blo 2045435 2045523 := bstep (se 1 (by rfl) ⟨1534142, by rfl⟩ : syracuseStep 2045523 = 3068285) B3068285
theorem B4602437 : Blo 2045435 4602437 := bbase (se 4 (by rfl) ⟨431478, by rfl⟩ : syracuseStep 4602437 = 862957) (by norm_num)
theorem B3068291 : Blo 2045435 3068291 := bstep (se 1 (by rfl) ⟨2301218, by rfl⟩ : syracuseStep 3068291 = 4602437) B4602437
theorem B2045527 : Blo 2045435 2045527 := bstep (se 1 (by rfl) ⟨1534145, by rfl⟩ : syracuseStep 2045527 = 3068291) B3068291
theorem B2184365 : Blo 2045435 2184365 := bbase (se 3 (by rfl) ⟨409568, by rfl⟩ : syracuseStep 2184365 = 819137) (by norm_num)
theorem B5824973 : Blo 2045435 5824973 := bstep (se 3 (by rfl) ⟨1092182, by rfl⟩ : syracuseStep 5824973 = 2184365) B2184365
theorem B3883315 : Blo 2045435 3883315 := bstep (se 1 (by rfl) ⟨2912486, by rfl⟩ : syracuseStep 3883315 = 5824973) B5824973
theorem B5177753 : Blo 2045435 5177753 := bstep (se 2 (by rfl) ⟨1941657, by rfl⟩ : syracuseStep 5177753 = 3883315) B3883315
theorem B3451835 : Blo 2045435 3451835 := bstep (se 1 (by rfl) ⟨2588876, by rfl⟩ : syracuseStep 3451835 = 5177753) B5177753
theorem B2301223 : Blo 2045435 2301223 := bstep (se 1 (by rfl) ⟨1725917, by rfl⟩ : syracuseStep 2301223 = 3451835) B3451835
theorem B3068297 : Blo 2045435 3068297 := bstep (se 2 (by rfl) ⟨1150611, by rfl⟩ : syracuseStep 3068297 = 2301223) B2301223
theorem B2045531 : Blo 2045435 2045531 := bstep (se 1 (by rfl) ⟨1534148, by rfl⟩ : syracuseStep 2045531 = 3068297) B3068297
theorem B10355525 : Blo 2045435 10355525 := bbase (se 4 (by rfl) ⟨970830, by rfl⟩ : syracuseStep 10355525 = 1941661) (by norm_num)
theorem B6903683 : Blo 2045435 6903683 := bstep (se 1 (by rfl) ⟨5177762, by rfl⟩ : syracuseStep 6903683 = 10355525) B10355525
theorem B4602455 : Blo 2045435 4602455 := bstep (se 1 (by rfl) ⟨3451841, by rfl⟩ : syracuseStep 4602455 = 6903683) B6903683
theorem B3068303 : Blo 2045435 3068303 := bstep (se 1 (by rfl) ⟨2301227, by rfl⟩ : syracuseStep 3068303 = 4602455) B4602455
theorem B2045535 : Blo 2045435 2045535 := bstep (se 1 (by rfl) ⟨1534151, by rfl⟩ : syracuseStep 2045535 = 3068303) B3068303
theorem B3068309 : Blo 2045435 3068309 := bbase (se 6 (by rfl) ⟨71913, by rfl⟩ : syracuseStep 3068309 = 143827) (by norm_num)
theorem B2045539 : Blo 2045435 2045539 := bstep (se 1 (by rfl) ⟨1534154, by rfl⟩ : syracuseStep 2045539 = 3068309) B3068309
theorem B2457425 : Blo 2045435 2457425 := bbase (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) (by norm_num)
theorem B6553133 : Blo 2045435 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B4368755 : Blo 2045435 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B11650013 : Blo 2045435 11650013 := bstep (se 3 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 11650013 = 4368755) B4368755
theorem B7766675 : Blo 2045435 7766675 := bstep (se 1 (by rfl) ⟨5825006, by rfl⟩ : syracuseStep 7766675 = 11650013) B11650013
theorem B5177783 : Blo 2045435 5177783 := bstep (se 1 (by rfl) ⟨3883337, by rfl⟩ : syracuseStep 5177783 = 7766675) B7766675
theorem B3451855 : Blo 2045435 3451855 := bstep (se 1 (by rfl) ⟨2588891, by rfl⟩ : syracuseStep 3451855 = 5177783) B5177783
theorem B4602473 : Blo 2045435 4602473 := bstep (se 2 (by rfl) ⟨1725927, by rfl⟩ : syracuseStep 4602473 = 3451855) B3451855
theorem B3068315 : Blo 2045435 3068315 := bstep (se 1 (by rfl) ⟨2301236, by rfl⟩ : syracuseStep 3068315 = 4602473) B4602473
theorem B2045543 : Blo 2045435 2045543 := bstep (se 1 (by rfl) ⟨1534157, by rfl⟩ : syracuseStep 2045543 = 3068315) B3068315
theorem B2301241 : Blo 2045435 2301241 := bbase (se 2 (by rfl) ⟨862965, by rfl⟩ : syracuseStep 2301241 = 1725931) (by norm_num)
theorem B3068321 : Blo 2045435 3068321 := bstep (se 2 (by rfl) ⟨1150620, by rfl⟩ : syracuseStep 3068321 = 2301241) B2301241
theorem B2045547 : Blo 2045435 2045547 := bstep (se 1 (by rfl) ⟨1534160, by rfl⟩ : syracuseStep 2045547 = 3068321) B3068321
theorem B5825029 : Blo 2045435 5825029 := bbase (se 4 (by rfl) ⟨546096, by rfl⟩ : syracuseStep 5825029 = 1092193) (by norm_num)
theorem B7766705 : Blo 2045435 7766705 := bstep (se 2 (by rfl) ⟨2912514, by rfl⟩ : syracuseStep 7766705 = 5825029) B5825029
theorem B5177803 : Blo 2045435 5177803 := bstep (se 1 (by rfl) ⟨3883352, by rfl⟩ : syracuseStep 5177803 = 7766705) B7766705
theorem B6903737 : Blo 2045435 6903737 := bstep (se 2 (by rfl) ⟨2588901, by rfl⟩ : syracuseStep 6903737 = 5177803) B5177803
theorem B4602491 : Blo 2045435 4602491 := bstep (se 1 (by rfl) ⟨3451868, by rfl⟩ : syracuseStep 4602491 = 6903737) B6903737
theorem B3068327 : Blo 2045435 3068327 := bstep (se 1 (by rfl) ⟨2301245, by rfl⟩ : syracuseStep 3068327 = 4602491) B4602491
theorem B2045551 : Blo 2045435 2045551 := bstep (se 1 (by rfl) ⟨1534163, by rfl⟩ : syracuseStep 2045551 = 3068327) B3068327
theorem B3068333 : Blo 2045435 3068333 := bbase (se 3 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 3068333 = 1150625) (by norm_num)
theorem B2045555 : Blo 2045435 2045555 := bstep (se 1 (by rfl) ⟨1534166, by rfl⟩ : syracuseStep 2045555 = 3068333) B3068333
theorem B4602509 : Blo 2045435 4602509 := bbase (se 3 (by rfl) ⟨862970, by rfl⟩ : syracuseStep 4602509 = 1725941) (by norm_num)
theorem B3068339 : Blo 2045435 3068339 := bstep (se 1 (by rfl) ⟨2301254, by rfl⟩ : syracuseStep 3068339 = 4602509) B4602509
theorem B2045559 : Blo 2045435 2045559 := bstep (se 1 (by rfl) ⟨1534169, by rfl⟩ : syracuseStep 2045559 = 3068339) B3068339
theorem B2588917 : Blo 2045435 2588917 := bbase (se 5 (by rfl) ⟨121355, by rfl⟩ : syracuseStep 2588917 = 242711) (by norm_num)
theorem B3451889 : Blo 2045435 3451889 := bstep (se 2 (by rfl) ⟨1294458, by rfl⟩ : syracuseStep 3451889 = 2588917) B2588917
theorem B2301259 : Blo 2045435 2301259 := bstep (se 1 (by rfl) ⟨1725944, by rfl⟩ : syracuseStep 2301259 = 3451889) B3451889
theorem B3068345 : Blo 2045435 3068345 := bstep (se 2 (by rfl) ⟨1150629, by rfl⟩ : syracuseStep 3068345 = 2301259) B2301259
theorem B2045563 : Blo 2045435 2045563 := bstep (se 1 (by rfl) ⟨1534172, by rfl⟩ : syracuseStep 2045563 = 3068345) B3068345
theorem B39319253 : Blo 2045435 39319253 := bbase (se 7 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 39319253 = 921545) (by norm_num)
theorem B26212835 : Blo 2045435 26212835 := bstep (se 1 (by rfl) ⟨19659626, by rfl⟩ : syracuseStep 26212835 = 39319253) B39319253
theorem B17475223 : Blo 2045435 17475223 := bstep (se 1 (by rfl) ⟨13106417, by rfl⟩ : syracuseStep 17475223 = 26212835) B26212835
theorem B23300297 : Blo 2045435 23300297 := bstep (se 2 (by rfl) ⟨8737611, by rfl⟩ : syracuseStep 23300297 = 17475223) B17475223
theorem B15533531 : Blo 2045435 15533531 := bstep (se 1 (by rfl) ⟨11650148, by rfl⟩ : syracuseStep 15533531 = 23300297) B23300297
theorem B10355687 : Blo 2045435 10355687 := bstep (se 1 (by rfl) ⟨7766765, by rfl⟩ : syracuseStep 10355687 = 15533531) B15533531
theorem B6903791 : Blo 2045435 6903791 := bstep (se 1 (by rfl) ⟨5177843, by rfl⟩ : syracuseStep 6903791 = 10355687) B10355687
theorem B4602527 : Blo 2045435 4602527 := bstep (se 1 (by rfl) ⟨3451895, by rfl⟩ : syracuseStep 4602527 = 6903791) B6903791
theorem B3068351 : Blo 2045435 3068351 := bstep (se 1 (by rfl) ⟨2301263, by rfl⟩ : syracuseStep 3068351 = 4602527) B4602527
theorem B2045567 : Blo 2045435 2045567 := bstep (se 1 (by rfl) ⟨1534175, by rfl⟩ : syracuseStep 2045567 = 3068351) B3068351
theorem B3068357 : Blo 2045435 3068357 := bbase (se 4 (by rfl) ⟨287658, by rfl⟩ : syracuseStep 3068357 = 575317) (by norm_num)
theorem B2045571 : Blo 2045435 2045571 := bstep (se 1 (by rfl) ⟨1534178, by rfl⟩ : syracuseStep 2045571 = 3068357) B3068357
theorem B3451909 : Blo 2045435 3451909 := bbase (se 4 (by rfl) ⟨323616, by rfl⟩ : syracuseStep 3451909 = 647233) (by norm_num)
theorem B4602545 : Blo 2045435 4602545 := bstep (se 2 (by rfl) ⟨1725954, by rfl⟩ : syracuseStep 4602545 = 3451909) B3451909
theorem B3068363 : Blo 2045435 3068363 := bstep (se 1 (by rfl) ⟨2301272, by rfl⟩ : syracuseStep 3068363 = 4602545) B4602545
theorem B2045575 : Blo 2045435 2045575 := bstep (se 1 (by rfl) ⟨1534181, by rfl⟩ : syracuseStep 2045575 = 3068363) B3068363
theorem B2301277 : Blo 2045435 2301277 := bbase (se 3 (by rfl) ⟨431489, by rfl⟩ : syracuseStep 2301277 = 862979) (by norm_num)
theorem B3068369 : Blo 2045435 3068369 := bstep (se 2 (by rfl) ⟨1150638, by rfl⟩ : syracuseStep 3068369 = 2301277) B2301277
theorem B2045579 : Blo 2045435 2045579 := bstep (se 1 (by rfl) ⟨1534184, by rfl⟩ : syracuseStep 2045579 = 3068369) B3068369
theorem B6903845 : Blo 2045435 6903845 := bbase (se 4 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 6903845 = 1294471) (by norm_num)
theorem B4602563 : Blo 2045435 4602563 := bstep (se 1 (by rfl) ⟨3451922, by rfl⟩ : syracuseStep 4602563 = 6903845) B6903845
theorem B3068375 : Blo 2045435 3068375 := bstep (se 1 (by rfl) ⟨2301281, by rfl⟩ : syracuseStep 3068375 = 4602563) B4602563
theorem B2045583 : Blo 2045435 2045583 := bstep (se 1 (by rfl) ⟨1534187, by rfl⟩ : syracuseStep 2045583 = 3068375) B3068375
theorem B3068381 : Blo 2045435 3068381 := bbase (se 3 (by rfl) ⟨575321, by rfl⟩ : syracuseStep 3068381 = 1150643) (by norm_num)
theorem B2045587 : Blo 2045435 2045587 := bstep (se 1 (by rfl) ⟨1534190, by rfl⟩ : syracuseStep 2045587 = 3068381) B3068381
theorem B4602581 : Blo 2045435 4602581 := bbase (se 7 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 4602581 = 107873) (by norm_num)
theorem B3068387 : Blo 2045435 3068387 := bstep (se 1 (by rfl) ⟨2301290, by rfl⟩ : syracuseStep 3068387 = 4602581) B4602581
theorem B2045591 : Blo 2045435 2045591 := bstep (se 1 (by rfl) ⟨1534193, by rfl⟩ : syracuseStep 2045591 = 3068387) B3068387
theorem B8737733 : Blo 2045435 8737733 := bbase (se 4 (by rfl) ⟨819162, by rfl⟩ : syracuseStep 8737733 = 1638325) (by norm_num)
theorem B5825155 : Blo 2045435 5825155 := bstep (se 1 (by rfl) ⟨4368866, by rfl⟩ : syracuseStep 5825155 = 8737733) B8737733
theorem B7766873 : Blo 2045435 7766873 := bstep (se 2 (by rfl) ⟨2912577, by rfl⟩ : syracuseStep 7766873 = 5825155) B5825155
theorem B5177915 : Blo 2045435 5177915 := bstep (se 1 (by rfl) ⟨3883436, by rfl⟩ : syracuseStep 5177915 = 7766873) B7766873
theorem B3451943 : Blo 2045435 3451943 := bstep (se 1 (by rfl) ⟨2588957, by rfl⟩ : syracuseStep 3451943 = 5177915) B5177915
theorem B2301295 : Blo 2045435 2301295 := bstep (se 1 (by rfl) ⟨1725971, by rfl⟩ : syracuseStep 2301295 = 3451943) B3451943
theorem B3068393 : Blo 2045435 3068393 := bstep (se 2 (by rfl) ⟨1150647, by rfl⟩ : syracuseStep 3068393 = 2301295) B2301295
theorem B2045595 : Blo 2045435 2045595 := bstep (se 1 (by rfl) ⟨1534196, by rfl⟩ : syracuseStep 2045595 = 3068393) B3068393
theorem B7473061 : Blo 2045435 7473061 := bbase (se 4 (by rfl) ⟨700599, by rfl⟩ : syracuseStep 7473061 = 1401199) (by norm_num)
theorem B9964081 : Blo 2045435 9964081 := bstep (se 2 (by rfl) ⟨3736530, by rfl⟩ : syracuseStep 9964081 = 7473061) B7473061
theorem B53141765 : Blo 2045435 53141765 := bstep (se 4 (by rfl) ⟨4982040, by rfl⟩ : syracuseStep 53141765 = 9964081) B9964081
theorem B141711373 : Blo 2045435 141711373 := bstep (se 3 (by rfl) ⟨26570882, by rfl⟩ : syracuseStep 141711373 = 53141765) B53141765
theorem B188948497 : Blo 2045435 188948497 := bstep (se 2 (by rfl) ⟨70855686, by rfl⟩ : syracuseStep 188948497 = 141711373) B141711373
theorem B251931329 : Blo 2045435 251931329 := bstep (se 2 (by rfl) ⟨94474248, by rfl⟩ : syracuseStep 251931329 = 188948497) B188948497
theorem B167954219 : Blo 2045435 167954219 := bstep (se 1 (by rfl) ⟨125965664, by rfl⟩ : syracuseStep 167954219 = 251931329) B251931329
theorem B111969479 : Blo 2045435 111969479 := bstep (se 1 (by rfl) ⟨83977109, by rfl⟩ : syracuseStep 111969479 = 167954219) B167954219
theorem B74646319 : Blo 2045435 74646319 := bstep (se 1 (by rfl) ⟨55984739, by rfl⟩ : syracuseStep 74646319 = 111969479) B111969479
theorem B99528425 : Blo 2045435 99528425 := bstep (se 2 (by rfl) ⟨37323159, by rfl⟩ : syracuseStep 99528425 = 74646319) B74646319
theorem B66352283 : Blo 2045435 66352283 := bstep (se 1 (by rfl) ⟨49764212, by rfl⟩ : syracuseStep 66352283 = 99528425) B99528425
theorem B44234855 : Blo 2045435 44234855 := bstep (se 1 (by rfl) ⟨33176141, by rfl⟩ : syracuseStep 44234855 = 66352283) B66352283
theorem B29489903 : Blo 2045435 29489903 := bstep (se 1 (by rfl) ⟨22117427, by rfl⟩ : syracuseStep 29489903 = 44234855) B44234855
theorem B19659935 : Blo 2045435 19659935 := bstep (se 1 (by rfl) ⟨14744951, by rfl⟩ : syracuseStep 19659935 = 29489903) B29489903
theorem B13106623 : Blo 2045435 13106623 := bstep (se 1 (by rfl) ⟨9829967, by rfl⟩ : syracuseStep 13106623 = 19659935) B19659935
theorem B17475497 : Blo 2045435 17475497 := bstep (se 2 (by rfl) ⟨6553311, by rfl⟩ : syracuseStep 17475497 = 13106623) B13106623
theorem B11650331 : Blo 2045435 11650331 := bstep (se 1 (by rfl) ⟨8737748, by rfl⟩ : syracuseStep 11650331 = 17475497) B17475497
theorem B7766887 : Blo 2045435 7766887 := bstep (se 1 (by rfl) ⟨5825165, by rfl⟩ : syracuseStep 7766887 = 11650331) B11650331
theorem B10355849 : Blo 2045435 10355849 := bstep (se 2 (by rfl) ⟨3883443, by rfl⟩ : syracuseStep 10355849 = 7766887) B7766887
theorem B6903899 : Blo 2045435 6903899 := bstep (se 1 (by rfl) ⟨5177924, by rfl⟩ : syracuseStep 6903899 = 10355849) B10355849
theorem B4602599 : Blo 2045435 4602599 := bstep (se 1 (by rfl) ⟨3451949, by rfl⟩ : syracuseStep 4602599 = 6903899) B6903899
theorem B3068399 : Blo 2045435 3068399 := bstep (se 1 (by rfl) ⟨2301299, by rfl⟩ : syracuseStep 3068399 = 4602599) B4602599
theorem B2045599 : Blo 2045435 2045599 := bstep (se 1 (by rfl) ⟨1534199, by rfl⟩ : syracuseStep 2045599 = 3068399) B3068399
theorem B3068405 : Blo 2045435 3068405 := bbase (se 5 (by rfl) ⟨143831, by rfl⟩ : syracuseStep 3068405 = 287663) (by norm_num)
theorem B2045603 : Blo 2045435 2045603 := bstep (se 1 (by rfl) ⟨1534202, by rfl⟩ : syracuseStep 2045603 = 3068405) B3068405
theorem B5825189 : Blo 2045435 5825189 := bbase (se 4 (by rfl) ⟨546111, by rfl⟩ : syracuseStep 5825189 = 1092223) (by norm_num)
theorem B3883459 : Blo 2045435 3883459 := bstep (se 1 (by rfl) ⟨2912594, by rfl⟩ : syracuseStep 3883459 = 5825189) B5825189
theorem B5177945 : Blo 2045435 5177945 := bstep (se 2 (by rfl) ⟨1941729, by rfl⟩ : syracuseStep 5177945 = 3883459) B3883459
theorem B3451963 : Blo 2045435 3451963 := bstep (se 1 (by rfl) ⟨2588972, by rfl⟩ : syracuseStep 3451963 = 5177945) B5177945
theorem B4602617 : Blo 2045435 4602617 := bstep (se 2 (by rfl) ⟨1725981, by rfl⟩ : syracuseStep 4602617 = 3451963) B3451963
theorem B3068411 : Blo 2045435 3068411 := bstep (se 1 (by rfl) ⟨2301308, by rfl⟩ : syracuseStep 3068411 = 4602617) B4602617
theorem B2045607 : Blo 2045435 2045607 := bstep (se 1 (by rfl) ⟨1534205, by rfl⟩ : syracuseStep 2045607 = 3068411) B3068411
theorem B2301313 : Blo 2045435 2301313 := bbase (se 2 (by rfl) ⟨862992, by rfl⟩ : syracuseStep 2301313 = 1725985) (by norm_num)
theorem B3068417 : Blo 2045435 3068417 := bstep (se 2 (by rfl) ⟨1150656, by rfl⟩ : syracuseStep 3068417 = 2301313) B2301313
theorem B2045611 : Blo 2045435 2045611 := bstep (se 1 (by rfl) ⟨1534208, by rfl⟩ : syracuseStep 2045611 = 3068417) B3068417
theorem B5177965 : Blo 2045435 5177965 := bbase (se 3 (by rfl) ⟨970868, by rfl⟩ : syracuseStep 5177965 = 1941737) (by norm_num)
theorem B6903953 : Blo 2045435 6903953 := bstep (se 2 (by rfl) ⟨2588982, by rfl⟩ : syracuseStep 6903953 = 5177965) B5177965
theorem B4602635 : Blo 2045435 4602635 := bstep (se 1 (by rfl) ⟨3451976, by rfl⟩ : syracuseStep 4602635 = 6903953) B6903953
theorem B3068423 : Blo 2045435 3068423 := bstep (se 1 (by rfl) ⟨2301317, by rfl⟩ : syracuseStep 3068423 = 4602635) B4602635
theorem B2045615 : Blo 2045435 2045615 := bstep (se 1 (by rfl) ⟨1534211, by rfl⟩ : syracuseStep 2045615 = 3068423) B3068423
theorem B3068429 : Blo 2045435 3068429 := bbase (se 3 (by rfl) ⟨575330, by rfl⟩ : syracuseStep 3068429 = 1150661) (by norm_num)
theorem B2045619 : Blo 2045435 2045619 := bstep (se 1 (by rfl) ⟨1534214, by rfl⟩ : syracuseStep 2045619 = 3068429) B3068429
theorem B4602653 : Blo 2045435 4602653 := bbase (se 3 (by rfl) ⟨862997, by rfl⟩ : syracuseStep 4602653 = 1725995) (by norm_num)
theorem B3068435 : Blo 2045435 3068435 := bstep (se 1 (by rfl) ⟨2301326, by rfl⟩ : syracuseStep 3068435 = 4602653) B4602653
theorem B2045623 : Blo 2045435 2045623 := bstep (se 1 (by rfl) ⟨1534217, by rfl⟩ : syracuseStep 2045623 = 3068435) B3068435
theorem B3451997 : Blo 2045435 3451997 := bbase (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) (by norm_num)
theorem B2301331 : Blo 2045435 2301331 := bstep (se 1 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 2301331 = 3451997) B3451997
theorem B3068441 : Blo 2045435 3068441 := bstep (se 2 (by rfl) ⟨1150665, by rfl⟩ : syracuseStep 3068441 = 2301331) B2301331
theorem B2045627 : Blo 2045435 2045627 := bstep (se 1 (by rfl) ⟨1534220, by rfl⟩ : syracuseStep 2045627 = 3068441) B3068441
theorem B4915061 : Blo 2045435 4915061 := bbase (se 5 (by rfl) ⟨230393, by rfl⟩ : syracuseStep 4915061 = 460787) (by norm_num)
theorem B3276707 : Blo 2045435 3276707 := bstep (se 1 (by rfl) ⟨2457530, by rfl⟩ : syracuseStep 3276707 = 4915061) B4915061
theorem B8737885 : Blo 2045435 8737885 := bstep (se 3 (by rfl) ⟨1638353, by rfl⟩ : syracuseStep 8737885 = 3276707) B3276707
theorem B11650513 : Blo 2045435 11650513 := bstep (se 2 (by rfl) ⟨4368942, by rfl⟩ : syracuseStep 11650513 = 8737885) B8737885
theorem B15534017 : Blo 2045435 15534017 := bstep (se 2 (by rfl) ⟨5825256, by rfl⟩ : syracuseStep 15534017 = 11650513) B11650513
theorem B10356011 : Blo 2045435 10356011 := bstep (se 1 (by rfl) ⟨7767008, by rfl⟩ : syracuseStep 10356011 = 15534017) B15534017
theorem B6904007 : Blo 2045435 6904007 := bstep (se 1 (by rfl) ⟨5178005, by rfl⟩ : syracuseStep 6904007 = 10356011) B10356011
theorem B4602671 : Blo 2045435 4602671 := bstep (se 1 (by rfl) ⟨3452003, by rfl⟩ : syracuseStep 4602671 = 6904007) B6904007
theorem B3068447 : Blo 2045435 3068447 := bstep (se 1 (by rfl) ⟨2301335, by rfl⟩ : syracuseStep 3068447 = 4602671) B4602671
theorem B2045631 : Blo 2045435 2045631 := bstep (se 1 (by rfl) ⟨1534223, by rfl⟩ : syracuseStep 2045631 = 3068447) B3068447
theorem B3068453 : Blo 2045435 3068453 := bbase (se 4 (by rfl) ⟨287667, by rfl⟩ : syracuseStep 3068453 = 575335) (by norm_num)
theorem B2045635 : Blo 2045435 2045635 := bstep (se 1 (by rfl) ⟨1534226, by rfl⟩ : syracuseStep 2045635 = 3068453) B3068453
theorem B2589013 : Blo 2045435 2589013 := bbase (se 10 (by rfl) ⟨3792, by rfl⟩ : syracuseStep 2589013 = 7585) (by norm_num)
theorem B3452017 : Blo 2045435 3452017 := bstep (se 2 (by rfl) ⟨1294506, by rfl⟩ : syracuseStep 3452017 = 2589013) B2589013
theorem B4602689 : Blo 2045435 4602689 := bstep (se 2 (by rfl) ⟨1726008, by rfl⟩ : syracuseStep 4602689 = 3452017) B3452017
theorem B3068459 : Blo 2045435 3068459 := bstep (se 1 (by rfl) ⟨2301344, by rfl⟩ : syracuseStep 3068459 = 4602689) B4602689
theorem B2045639 : Blo 2045435 2045639 := bstep (se 1 (by rfl) ⟨1534229, by rfl⟩ : syracuseStep 2045639 = 3068459) B3068459
theorem B2301349 : Blo 2045435 2301349 := bbase (se 4 (by rfl) ⟨215751, by rfl⟩ : syracuseStep 2301349 = 431503) (by norm_num)
theorem B3068465 : Blo 2045435 3068465 := bstep (se 2 (by rfl) ⟨1150674, by rfl⟩ : syracuseStep 3068465 = 2301349) B2301349
theorem B2045643 : Blo 2045435 2045643 := bstep (se 1 (by rfl) ⟨1534232, by rfl⟩ : syracuseStep 2045643 = 3068465) B3068465
theorem B13106933 : Blo 2045435 13106933 := bbase (se 5 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 13106933 = 1228775) (by norm_num)
theorem B8737955 : Blo 2045435 8737955 := bstep (se 1 (by rfl) ⟨6553466, by rfl⟩ : syracuseStep 8737955 = 13106933) B13106933
theorem B5825303 : Blo 2045435 5825303 := bstep (se 1 (by rfl) ⟨4368977, by rfl⟩ : syracuseStep 5825303 = 8737955) B8737955
theorem B3883535 : Blo 2045435 3883535 := bstep (se 1 (by rfl) ⟨2912651, by rfl⟩ : syracuseStep 3883535 = 5825303) B5825303
theorem B2589023 : Blo 2045435 2589023 := bstep (se 1 (by rfl) ⟨1941767, by rfl⟩ : syracuseStep 2589023 = 3883535) B3883535
theorem B6904061 : Blo 2045435 6904061 := bstep (se 3 (by rfl) ⟨1294511, by rfl⟩ : syracuseStep 6904061 = 2589023) B2589023
theorem B4602707 : Blo 2045435 4602707 := bstep (se 1 (by rfl) ⟨3452030, by rfl⟩ : syracuseStep 4602707 = 6904061) B6904061
theorem B3068471 : Blo 2045435 3068471 := bstep (se 1 (by rfl) ⟨2301353, by rfl⟩ : syracuseStep 3068471 = 4602707) B4602707
theorem B2045647 : Blo 2045435 2045647 := bstep (se 1 (by rfl) ⟨1534235, by rfl⟩ : syracuseStep 2045647 = 3068471) B3068471
theorem B3068477 : Blo 2045435 3068477 := bbase (se 3 (by rfl) ⟨575339, by rfl⟩ : syracuseStep 3068477 = 1150679) (by norm_num)
theorem B2045651 : Blo 2045435 2045651 := bstep (se 1 (by rfl) ⟨1534238, by rfl⟩ : syracuseStep 2045651 = 3068477) B3068477
theorem B4602725 : Blo 2045435 4602725 := bbase (se 4 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 4602725 = 863011) (by norm_num)
theorem B3068483 : Blo 2045435 3068483 := bstep (se 1 (by rfl) ⟨2301362, by rfl⟩ : syracuseStep 3068483 = 4602725) B4602725
theorem B2045655 : Blo 2045435 2045655 := bstep (se 1 (by rfl) ⟨1534241, by rfl⟩ : syracuseStep 2045655 = 3068483) B3068483
theorem B5178077 : Blo 2045435 5178077 := bbase (se 3 (by rfl) ⟨970889, by rfl⟩ : syracuseStep 5178077 = 1941779) (by norm_num)
theorem B3452051 : Blo 2045435 3452051 := bstep (se 1 (by rfl) ⟨2589038, by rfl⟩ : syracuseStep 3452051 = 5178077) B5178077
theorem B2301367 : Blo 2045435 2301367 := bstep (se 1 (by rfl) ⟨1726025, by rfl⟩ : syracuseStep 2301367 = 3452051) B3452051
theorem B3068489 : Blo 2045435 3068489 := bstep (se 2 (by rfl) ⟨1150683, by rfl⟩ : syracuseStep 3068489 = 2301367) B2301367
theorem B2045659 : Blo 2045435 2045659 := bstep (se 1 (by rfl) ⟨1534244, by rfl⟩ : syracuseStep 2045659 = 3068489) B3068489
theorem B3883565 : Blo 2045435 3883565 := bbase (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) (by norm_num)
theorem B10356173 : Blo 2045435 10356173 := bstep (se 3 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 10356173 = 3883565) B3883565
theorem B6904115 : Blo 2045435 6904115 := bstep (se 1 (by rfl) ⟨5178086, by rfl⟩ : syracuseStep 6904115 = 10356173) B10356173
theorem B4602743 : Blo 2045435 4602743 := bstep (se 1 (by rfl) ⟨3452057, by rfl⟩ : syracuseStep 4602743 = 6904115) B6904115
theorem B3068495 : Blo 2045435 3068495 := bstep (se 1 (by rfl) ⟨2301371, by rfl⟩ : syracuseStep 3068495 = 4602743) B4602743
theorem B2045663 : Blo 2045435 2045663 := bstep (se 1 (by rfl) ⟨1534247, by rfl⟩ : syracuseStep 2045663 = 3068495) B3068495
theorem B3068501 : Blo 2045435 3068501 := bbase (se 8 (by rfl) ⟨17979, by rfl⟩ : syracuseStep 3068501 = 35959) (by norm_num)
theorem B2045667 : Blo 2045435 2045667 := bstep (se 1 (by rfl) ⟨1534250, by rfl⟩ : syracuseStep 2045667 = 3068501) B3068501
theorem B6998341 : Blo 2045435 6998341 := bbase (se 4 (by rfl) ⟨656094, by rfl⟩ : syracuseStep 6998341 = 1312189) (by norm_num)
theorem B9331121 : Blo 2045435 9331121 := bstep (se 2 (by rfl) ⟨3499170, by rfl⟩ : syracuseStep 9331121 = 6998341) B6998341
theorem B6220747 : Blo 2045435 6220747 := bstep (se 1 (by rfl) ⟨4665560, by rfl⟩ : syracuseStep 6220747 = 9331121) B9331121
theorem B8294329 : Blo 2045435 8294329 := bstep (se 2 (by rfl) ⟨3110373, by rfl⟩ : syracuseStep 8294329 = 6220747) B6220747
theorem B11059105 : Blo 2045435 11059105 := bstep (se 2 (by rfl) ⟨4147164, by rfl⟩ : syracuseStep 11059105 = 8294329) B8294329
theorem B14745473 : Blo 2045435 14745473 := bstep (se 2 (by rfl) ⟨5529552, by rfl⟩ : syracuseStep 14745473 = 11059105) B11059105
theorem B9830315 : Blo 2045435 9830315 := bstep (se 1 (by rfl) ⟨7372736, by rfl⟩ : syracuseStep 9830315 = 14745473) B14745473
theorem B6553543 : Blo 2045435 6553543 := bstep (se 1 (by rfl) ⟨4915157, by rfl⟩ : syracuseStep 6553543 = 9830315) B9830315
theorem B8738057 : Blo 2045435 8738057 := bstep (se 2 (by rfl) ⟨3276771, by rfl⟩ : syracuseStep 8738057 = 6553543) B6553543
theorem B5825371 : Blo 2045435 5825371 := bstep (se 1 (by rfl) ⟨4369028, by rfl⟩ : syracuseStep 5825371 = 8738057) B8738057
theorem B7767161 : Blo 2045435 7767161 := bstep (se 2 (by rfl) ⟨2912685, by rfl⟩ : syracuseStep 7767161 = 5825371) B5825371
theorem B5178107 : Blo 2045435 5178107 := bstep (se 1 (by rfl) ⟨3883580, by rfl⟩ : syracuseStep 5178107 = 7767161) B7767161
theorem B3452071 : Blo 2045435 3452071 := bstep (se 1 (by rfl) ⟨2589053, by rfl⟩ : syracuseStep 3452071 = 5178107) B5178107
theorem B4602761 : Blo 2045435 4602761 := bstep (se 2 (by rfl) ⟨1726035, by rfl⟩ : syracuseStep 4602761 = 3452071) B3452071
theorem B3068507 : Blo 2045435 3068507 := bstep (se 1 (by rfl) ⟨2301380, by rfl⟩ : syracuseStep 3068507 = 4602761) B4602761
theorem B2045671 : Blo 2045435 2045671 := bstep (se 1 (by rfl) ⟨1534253, by rfl⟩ : syracuseStep 2045671 = 3068507) B3068507
theorem B2301385 : Blo 2045435 2301385 := bbase (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) (by norm_num)
theorem B3068513 : Blo 2045435 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B2045675 : Blo 2045435 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B17476181 : Blo 2045435 17476181 := bbase (se 8 (by rfl) ⟨102399, by rfl⟩ : syracuseStep 17476181 = 204799) (by norm_num)
theorem B11650787 : Blo 2045435 11650787 := bstep (se 1 (by rfl) ⟨8738090, by rfl⟩ : syracuseStep 11650787 = 17476181) B17476181
theorem B7767191 : Blo 2045435 7767191 := bstep (se 1 (by rfl) ⟨5825393, by rfl⟩ : syracuseStep 7767191 = 11650787) B11650787
theorem B5178127 : Blo 2045435 5178127 := bstep (se 1 (by rfl) ⟨3883595, by rfl⟩ : syracuseStep 5178127 = 7767191) B7767191
theorem B6904169 : Blo 2045435 6904169 := bstep (se 2 (by rfl) ⟨2589063, by rfl⟩ : syracuseStep 6904169 = 5178127) B5178127
theorem B4602779 : Blo 2045435 4602779 := bstep (se 1 (by rfl) ⟨3452084, by rfl⟩ : syracuseStep 4602779 = 6904169) B6904169
theorem B3068519 : Blo 2045435 3068519 := bstep (se 1 (by rfl) ⟨2301389, by rfl⟩ : syracuseStep 3068519 = 4602779) B4602779
theorem B2045679 : Blo 2045435 2045679 := bstep (se 1 (by rfl) ⟨1534259, by rfl⟩ : syracuseStep 2045679 = 3068519) B3068519
theorem B3068525 : Blo 2045435 3068525 := bbase (se 3 (by rfl) ⟨575348, by rfl⟩ : syracuseStep 3068525 = 1150697) (by norm_num)
theorem B2045683 : Blo 2045435 2045683 := bstep (se 1 (by rfl) ⟨1534262, by rfl⟩ : syracuseStep 2045683 = 3068525) B3068525
theorem B4602797 : Blo 2045435 4602797 := bbase (se 3 (by rfl) ⟨863024, by rfl⟩ : syracuseStep 4602797 = 1726049) (by norm_num)
theorem B3068531 : Blo 2045435 3068531 := bstep (se 1 (by rfl) ⟨2301398, by rfl⟩ : syracuseStep 3068531 = 4602797) B4602797
theorem B2045687 : Blo 2045435 2045687 := bstep (se 1 (by rfl) ⟨1534265, by rfl⟩ : syracuseStep 2045687 = 3068531) B3068531
theorem B5825429 : Blo 2045435 5825429 := bbase (se 6 (by rfl) ⟨136533, by rfl⟩ : syracuseStep 5825429 = 273067) (by norm_num)
theorem B3883619 : Blo 2045435 3883619 := bstep (se 1 (by rfl) ⟨2912714, by rfl⟩ : syracuseStep 3883619 = 5825429) B5825429
theorem B2589079 : Blo 2045435 2589079 := bstep (se 1 (by rfl) ⟨1941809, by rfl⟩ : syracuseStep 2589079 = 3883619) B3883619
theorem B3452105 : Blo 2045435 3452105 := bstep (se 2 (by rfl) ⟨1294539, by rfl⟩ : syracuseStep 3452105 = 2589079) B2589079
theorem B2301403 : Blo 2045435 2301403 := bstep (se 1 (by rfl) ⟨1726052, by rfl⟩ : syracuseStep 2301403 = 3452105) B3452105
theorem B3068537 : Blo 2045435 3068537 := bstep (se 2 (by rfl) ⟨1150701, by rfl⟩ : syracuseStep 3068537 = 2301403) B2301403
theorem B2045691 : Blo 2045435 2045691 := bstep (se 1 (by rfl) ⟨1534268, by rfl⟩ : syracuseStep 2045691 = 3068537) B3068537
theorem B29491285 : Blo 2045435 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B39321713 : Blo 2045435 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B26214475 : Blo 2045435 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B34952633 : Blo 2045435 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B23301755 : Blo 2045435 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B15534503 : Blo 2045435 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B10356335 : Blo 2045435 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B6904223 : Blo 2045435 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B4602815 : Blo 2045435 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B3068543 : Blo 2045435 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B2045695 : Blo 2045435 2045695 := bstep (se 1 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 2045695 = 3068543) B3068543
theorem B3068549 : Blo 2045435 3068549 := bbase (se 4 (by rfl) ⟨287676, by rfl⟩ : syracuseStep 3068549 = 575353) (by norm_num)
theorem B2045699 : Blo 2045435 2045699 := bstep (se 1 (by rfl) ⟨1534274, by rfl⟩ : syracuseStep 2045699 = 3068549) B3068549
theorem B3452125 : Blo 2045435 3452125 := bbase (se 3 (by rfl) ⟨647273, by rfl⟩ : syracuseStep 3452125 = 1294547) (by norm_num)
theorem B4602833 : Blo 2045435 4602833 := bstep (se 2 (by rfl) ⟨1726062, by rfl⟩ : syracuseStep 4602833 = 3452125) B3452125
theorem B3068555 : Blo 2045435 3068555 := bstep (se 1 (by rfl) ⟨2301416, by rfl⟩ : syracuseStep 3068555 = 4602833) B4602833
theorem B2045703 : Blo 2045435 2045703 := bstep (se 1 (by rfl) ⟨1534277, by rfl⟩ : syracuseStep 2045703 = 3068555) B3068555
theorem B2301421 : Blo 2045435 2301421 := bbase (se 3 (by rfl) ⟨431516, by rfl⟩ : syracuseStep 2301421 = 863033) (by norm_num)
theorem B3068561 : Blo 2045435 3068561 := bstep (se 2 (by rfl) ⟨1150710, by rfl⟩ : syracuseStep 3068561 = 2301421) B2301421
theorem B2045707 : Blo 2045435 2045707 := bstep (se 1 (by rfl) ⟨1534280, by rfl⟩ : syracuseStep 2045707 = 3068561) B3068561
theorem B6904277 : Blo 2045435 6904277 := bbase (se 7 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 6904277 = 161819) (by norm_num)
theorem B4602851 : Blo 2045435 4602851 := bstep (se 1 (by rfl) ⟨3452138, by rfl⟩ : syracuseStep 4602851 = 6904277) B6904277
theorem B3068567 : Blo 2045435 3068567 := bstep (se 1 (by rfl) ⟨2301425, by rfl⟩ : syracuseStep 3068567 = 4602851) B4602851
theorem B2045711 : Blo 2045435 2045711 := bstep (se 1 (by rfl) ⟨1534283, by rfl⟩ : syracuseStep 2045711 = 3068567) B3068567
theorem B3068573 : Blo 2045435 3068573 := bbase (se 3 (by rfl) ⟨575357, by rfl⟩ : syracuseStep 3068573 = 1150715) (by norm_num)
theorem B2045715 : Blo 2045435 2045715 := bstep (se 1 (by rfl) ⟨1534286, by rfl⟩ : syracuseStep 2045715 = 3068573) B3068573
theorem B4602869 : Blo 2045435 4602869 := bbase (se 5 (by rfl) ⟨215759, by rfl⟩ : syracuseStep 4602869 = 431519) (by norm_num)
theorem B3068579 : Blo 2045435 3068579 := bstep (se 1 (by rfl) ⟨2301434, by rfl⟩ : syracuseStep 3068579 = 4602869) B4602869
theorem B2045719 : Blo 2045435 2045719 := bstep (se 1 (by rfl) ⟨1534289, by rfl⟩ : syracuseStep 2045719 = 3068579) B3068579
theorem B5050325 : Blo 2045435 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B3366883 : Blo 2045435 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B4489177 : Blo 2045435 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B5985569 : Blo 2045435 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B3990379 : Blo 2045435 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B5320505 : Blo 2045435 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3547003 : Blo 2045435 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B4729337 : Blo 2045435 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B3152891 : Blo 2045435 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B8407709 : Blo 2045435 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B5605139 : Blo 2045435 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B14947037 : Blo 2045435 14947037 := bstep (se 3 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 14947037 = 5605139) B5605139
theorem B9964691 : Blo 2045435 9964691 := bstep (se 1 (by rfl) ⟨7473518, by rfl⟩ : syracuseStep 9964691 = 14947037) B14947037
theorem B6643127 : Blo 2045435 6643127 := bstep (se 1 (by rfl) ⟨4982345, by rfl⟩ : syracuseStep 6643127 = 9964691) B9964691
theorem B4428751 : Blo 2045435 4428751 := bstep (se 1 (by rfl) ⟨3321563, by rfl⟩ : syracuseStep 4428751 = 6643127) B6643127
theorem B5905001 : Blo 2045435 5905001 := bstep (se 2 (by rfl) ⟨2214375, by rfl⟩ : syracuseStep 5905001 = 4428751) B4428751
theorem B3936667 : Blo 2045435 3936667 := bstep (se 1 (by rfl) ⟨2952500, by rfl⟩ : syracuseStep 3936667 = 5905001) B5905001
theorem B5248889 : Blo 2045435 5248889 := bstep (se 2 (by rfl) ⟨1968333, by rfl⟩ : syracuseStep 5248889 = 3936667) B3936667
theorem B3499259 : Blo 2045435 3499259 := bstep (se 1 (by rfl) ⟨2624444, by rfl⟩ : syracuseStep 3499259 = 5248889) B5248889
theorem B9331357 : Blo 2045435 9331357 := bstep (se 3 (by rfl) ⟨1749629, by rfl⟩ : syracuseStep 9331357 = 3499259) B3499259
theorem B12441809 : Blo 2045435 12441809 := bstep (se 2 (by rfl) ⟨4665678, by rfl⟩ : syracuseStep 12441809 = 9331357) B9331357
theorem B33178157 : Blo 2045435 33178157 := bstep (se 3 (by rfl) ⟨6220904, by rfl⟩ : syracuseStep 33178157 = 12441809) B12441809
theorem B22118771 : Blo 2045435 22118771 := bstep (se 1 (by rfl) ⟨16589078, by rfl⟩ : syracuseStep 22118771 = 33178157) B33178157
theorem B58983389 : Blo 2045435 58983389 := bstep (se 3 (by rfl) ⟨11059385, by rfl⟩ : syracuseStep 58983389 = 22118771) B22118771
theorem B39322259 : Blo 2045435 39322259 := bstep (se 1 (by rfl) ⟨29491694, by rfl⟩ : syracuseStep 39322259 = 58983389) B58983389
theorem B26214839 : Blo 2045435 26214839 := bstep (se 1 (by rfl) ⟨19661129, by rfl⟩ : syracuseStep 26214839 = 39322259) B39322259
theorem B17476559 : Blo 2045435 17476559 := bstep (se 1 (by rfl) ⟨13107419, by rfl⟩ : syracuseStep 17476559 = 26214839) B26214839
theorem B11651039 : Blo 2045435 11651039 := bstep (se 1 (by rfl) ⟨8738279, by rfl⟩ : syracuseStep 11651039 = 17476559) B17476559
theorem B7767359 : Blo 2045435 7767359 := bstep (se 1 (by rfl) ⟨5825519, by rfl⟩ : syracuseStep 7767359 = 11651039) B11651039
theorem B5178239 : Blo 2045435 5178239 := bstep (se 1 (by rfl) ⟨3883679, by rfl⟩ : syracuseStep 5178239 = 7767359) B7767359
theorem B3452159 : Blo 2045435 3452159 := bstep (se 1 (by rfl) ⟨2589119, by rfl⟩ : syracuseStep 3452159 = 5178239) B5178239
theorem B2301439 : Blo 2045435 2301439 := bstep (se 1 (by rfl) ⟨1726079, by rfl⟩ : syracuseStep 2301439 = 3452159) B3452159
theorem B3068585 : Blo 2045435 3068585 := bstep (se 2 (by rfl) ⟨1150719, by rfl⟩ : syracuseStep 3068585 = 2301439) B2301439
theorem B2045723 : Blo 2045435 2045723 := bstep (se 1 (by rfl) ⟨1534292, by rfl⟩ : syracuseStep 2045723 = 3068585) B3068585
theorem B2912765 : Blo 2045435 2912765 := bbase (se 3 (by rfl) ⟨546143, by rfl⟩ : syracuseStep 2912765 = 1092287) (by norm_num)
theorem B7767373 : Blo 2045435 7767373 := bstep (se 3 (by rfl) ⟨1456382, by rfl⟩ : syracuseStep 7767373 = 2912765) B2912765
theorem B10356497 : Blo 2045435 10356497 := bstep (se 2 (by rfl) ⟨3883686, by rfl⟩ : syracuseStep 10356497 = 7767373) B7767373
theorem B6904331 : Blo 2045435 6904331 := bstep (se 1 (by rfl) ⟨5178248, by rfl⟩ : syracuseStep 6904331 = 10356497) B10356497
theorem B4602887 : Blo 2045435 4602887 := bstep (se 1 (by rfl) ⟨3452165, by rfl⟩ : syracuseStep 4602887 = 6904331) B6904331
theorem B3068591 : Blo 2045435 3068591 := bstep (se 1 (by rfl) ⟨2301443, by rfl⟩ : syracuseStep 3068591 = 4602887) B4602887
theorem B2045727 : Blo 2045435 2045727 := bstep (se 1 (by rfl) ⟨1534295, by rfl⟩ : syracuseStep 2045727 = 3068591) B3068591
theorem B3068597 : Blo 2045435 3068597 := bbase (se 5 (by rfl) ⟨143840, by rfl⟩ : syracuseStep 3068597 = 287681) (by norm_num)
theorem B2045731 : Blo 2045435 2045731 := bstep (se 1 (by rfl) ⟨1534298, by rfl⟩ : syracuseStep 2045731 = 3068597) B3068597
theorem B5178269 : Blo 2045435 5178269 := bbase (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) (by norm_num)
theorem B3452179 : Blo 2045435 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B4602905 : Blo 2045435 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B3068603 : Blo 2045435 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B2045735 : Blo 2045435 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B2301457 : Blo 2045435 2301457 := bbase (se 2 (by rfl) ⟨863046, by rfl⟩ : syracuseStep 2301457 = 1726093) (by norm_num)
theorem B3068609 : Blo 2045435 3068609 := bstep (se 2 (by rfl) ⟨1150728, by rfl⟩ : syracuseStep 3068609 = 2301457) B2301457
theorem B2045739 : Blo 2045435 2045739 := bstep (se 1 (by rfl) ⟨1534304, by rfl⟩ : syracuseStep 2045739 = 3068609) B3068609
theorem B3883717 : Blo 2045435 3883717 := bbase (se 4 (by rfl) ⟨364098, by rfl⟩ : syracuseStep 3883717 = 728197) (by norm_num)
theorem B5178289 : Blo 2045435 5178289 := bstep (se 2 (by rfl) ⟨1941858, by rfl⟩ : syracuseStep 5178289 = 3883717) B3883717
theorem B6904385 : Blo 2045435 6904385 := bstep (se 2 (by rfl) ⟨2589144, by rfl⟩ : syracuseStep 6904385 = 5178289) B5178289
theorem B4602923 : Blo 2045435 4602923 := bstep (se 1 (by rfl) ⟨3452192, by rfl⟩ : syracuseStep 4602923 = 6904385) B6904385
theorem B3068615 : Blo 2045435 3068615 := bstep (se 1 (by rfl) ⟨2301461, by rfl⟩ : syracuseStep 3068615 = 4602923) B4602923
theorem B2045743 : Blo 2045435 2045743 := bstep (se 1 (by rfl) ⟨1534307, by rfl⟩ : syracuseStep 2045743 = 3068615) B3068615
theorem B3068621 : Blo 2045435 3068621 := bbase (se 3 (by rfl) ⟨575366, by rfl⟩ : syracuseStep 3068621 = 1150733) (by norm_num)
theorem B2045747 : Blo 2045435 2045747 := bstep (se 1 (by rfl) ⟨1534310, by rfl⟩ : syracuseStep 2045747 = 3068621) B3068621
theorem B4602941 : Blo 2045435 4602941 := bbase (se 3 (by rfl) ⟨863051, by rfl⟩ : syracuseStep 4602941 = 1726103) (by norm_num)
theorem B3068627 : Blo 2045435 3068627 := bstep (se 1 (by rfl) ⟨2301470, by rfl⟩ : syracuseStep 3068627 = 4602941) B4602941
theorem B2045751 : Blo 2045435 2045751 := bstep (se 1 (by rfl) ⟨1534313, by rfl⟩ : syracuseStep 2045751 = 3068627) B3068627
theorem B3452213 : Blo 2045435 3452213 := bbase (se 5 (by rfl) ⟨161822, by rfl⟩ : syracuseStep 3452213 = 323645) (by norm_num)
theorem B2301475 : Blo 2045435 2301475 := bstep (se 1 (by rfl) ⟨1726106, by rfl⟩ : syracuseStep 2301475 = 3452213) B3452213
theorem B3068633 : Blo 2045435 3068633 := bstep (se 2 (by rfl) ⟨1150737, by rfl⟩ : syracuseStep 3068633 = 2301475) B2301475
theorem B2045755 : Blo 2045435 2045755 := bstep (se 1 (by rfl) ⟨1534316, by rfl⟩ : syracuseStep 2045755 = 3068633) B3068633
theorem B5825621 : Blo 2045435 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B15534989 : Blo 2045435 15534989 := bstep (se 3 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 15534989 = 5825621) B5825621
theorem B10356659 : Blo 2045435 10356659 := bstep (se 1 (by rfl) ⟨7767494, by rfl⟩ : syracuseStep 10356659 = 15534989) B15534989
theorem B6904439 : Blo 2045435 6904439 := bstep (se 1 (by rfl) ⟨5178329, by rfl⟩ : syracuseStep 6904439 = 10356659) B10356659
theorem B4602959 : Blo 2045435 4602959 := bstep (se 1 (by rfl) ⟨3452219, by rfl⟩ : syracuseStep 4602959 = 6904439) B6904439
theorem B3068639 : Blo 2045435 3068639 := bstep (se 1 (by rfl) ⟨2301479, by rfl⟩ : syracuseStep 3068639 = 4602959) B4602959
theorem B2045759 : Blo 2045435 2045759 := bstep (se 1 (by rfl) ⟨1534319, by rfl⟩ : syracuseStep 2045759 = 3068639) B3068639
theorem B3068645 : Blo 2045435 3068645 := bbase (se 4 (by rfl) ⟨287685, by rfl⟩ : syracuseStep 3068645 = 575371) (by norm_num)
theorem B2045763 : Blo 2045435 2045763 := bstep (se 1 (by rfl) ⟨1534322, by rfl⟩ : syracuseStep 2045763 = 3068645) B3068645
theorem B2184617 : Blo 2045435 2184617 := bbase (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) (by norm_num)
theorem B5825645 : Blo 2045435 5825645 := bstep (se 3 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 5825645 = 2184617) B2184617
theorem B3883763 : Blo 2045435 3883763 := bstep (se 1 (by rfl) ⟨2912822, by rfl⟩ : syracuseStep 3883763 = 5825645) B5825645
theorem B2589175 : Blo 2045435 2589175 := bstep (se 1 (by rfl) ⟨1941881, by rfl⟩ : syracuseStep 2589175 = 3883763) B3883763
theorem B3452233 : Blo 2045435 3452233 := bstep (se 2 (by rfl) ⟨1294587, by rfl⟩ : syracuseStep 3452233 = 2589175) B2589175
theorem B4602977 : Blo 2045435 4602977 := bstep (se 2 (by rfl) ⟨1726116, by rfl⟩ : syracuseStep 4602977 = 3452233) B3452233
theorem B3068651 : Blo 2045435 3068651 := bstep (se 1 (by rfl) ⟨2301488, by rfl⟩ : syracuseStep 3068651 = 4602977) B4602977
theorem B2045767 : Blo 2045435 2045767 := bstep (se 1 (by rfl) ⟨1534325, by rfl⟩ : syracuseStep 2045767 = 3068651) B3068651
theorem B2301493 : Blo 2045435 2301493 := bbase (se 5 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 2301493 = 215765) (by norm_num)
theorem B3068657 : Blo 2045435 3068657 := bstep (se 2 (by rfl) ⟨1150746, by rfl⟩ : syracuseStep 3068657 = 2301493) B2301493
theorem B2045771 : Blo 2045435 2045771 := bstep (se 1 (by rfl) ⟨1534328, by rfl⟩ : syracuseStep 2045771 = 3068657) B3068657
theorem B2589185 : Blo 2045435 2589185 := bbase (se 2 (by rfl) ⟨970944, by rfl⟩ : syracuseStep 2589185 = 1941889) (by norm_num)
theorem B6904493 : Blo 2045435 6904493 := bstep (se 3 (by rfl) ⟨1294592, by rfl⟩ : syracuseStep 6904493 = 2589185) B2589185
theorem B4602995 : Blo 2045435 4602995 := bstep (se 1 (by rfl) ⟨3452246, by rfl⟩ : syracuseStep 4602995 = 6904493) B6904493
theorem B3068663 : Blo 2045435 3068663 := bstep (se 1 (by rfl) ⟨2301497, by rfl⟩ : syracuseStep 3068663 = 4602995) B4602995
theorem B2045775 : Blo 2045435 2045775 := bstep (se 1 (by rfl) ⟨1534331, by rfl⟩ : syracuseStep 2045775 = 3068663) B3068663
theorem B3068669 : Blo 2045435 3068669 := bbase (se 3 (by rfl) ⟨575375, by rfl⟩ : syracuseStep 3068669 = 1150751) (by norm_num)
theorem B2045779 : Blo 2045435 2045779 := bstep (se 1 (by rfl) ⟨1534334, by rfl⟩ : syracuseStep 2045779 = 3068669) B3068669
theorem B4603013 : Blo 2045435 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B3068675 : Blo 2045435 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B2045783 : Blo 2045435 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B4369277 : Blo 2045435 4369277 := bbase (se 3 (by rfl) ⟨819239, by rfl⟩ : syracuseStep 4369277 = 1638479) (by norm_num)
theorem B2912851 : Blo 2045435 2912851 := bstep (se 1 (by rfl) ⟨2184638, by rfl⟩ : syracuseStep 2912851 = 4369277) B4369277
theorem B3883801 : Blo 2045435 3883801 := bstep (se 2 (by rfl) ⟨1456425, by rfl⟩ : syracuseStep 3883801 = 2912851) B2912851
theorem B5178401 : Blo 2045435 5178401 := bstep (se 2 (by rfl) ⟨1941900, by rfl⟩ : syracuseStep 5178401 = 3883801) B3883801
theorem B3452267 : Blo 2045435 3452267 := bstep (se 1 (by rfl) ⟨2589200, by rfl⟩ : syracuseStep 3452267 = 5178401) B5178401
theorem B2301511 : Blo 2045435 2301511 := bstep (se 1 (by rfl) ⟨1726133, by rfl⟩ : syracuseStep 2301511 = 3452267) B3452267
theorem B3068681 : Blo 2045435 3068681 := bstep (se 2 (by rfl) ⟨1150755, by rfl⟩ : syracuseStep 3068681 = 2301511) B2301511
theorem B2045787 : Blo 2045435 2045787 := bstep (se 1 (by rfl) ⟨1534340, by rfl⟩ : syracuseStep 2045787 = 3068681) B3068681
theorem B10356821 : Blo 2045435 10356821 := bbase (se 8 (by rfl) ⟨60684, by rfl⟩ : syracuseStep 10356821 = 121369) (by norm_num)
theorem B6904547 : Blo 2045435 6904547 := bstep (se 1 (by rfl) ⟨5178410, by rfl⟩ : syracuseStep 6904547 = 10356821) B10356821
theorem B4603031 : Blo 2045435 4603031 := bstep (se 1 (by rfl) ⟨3452273, by rfl⟩ : syracuseStep 4603031 = 6904547) B6904547
theorem B3068687 : Blo 2045435 3068687 := bstep (se 1 (by rfl) ⟨2301515, by rfl⟩ : syracuseStep 3068687 = 4603031) B4603031
theorem B2045791 : Blo 2045435 2045791 := bstep (se 1 (by rfl) ⟨1534343, by rfl⟩ : syracuseStep 2045791 = 3068687) B3068687
theorem B3068693 : Blo 2045435 3068693 := bbase (se 6 (by rfl) ⟨71922, by rfl⟩ : syracuseStep 3068693 = 143845) (by norm_num)
theorem B2045795 : Blo 2045435 2045795 := bstep (se 1 (by rfl) ⟨1534346, by rfl⟩ : syracuseStep 2045795 = 3068693) B3068693
theorem B2764949 : Blo 2045435 2764949 := bbase (se 6 (by rfl) ⟨64803, by rfl⟩ : syracuseStep 2764949 = 129607) (by norm_num)
theorem B7373197 : Blo 2045435 7373197 := bstep (se 3 (by rfl) ⟨1382474, by rfl⟩ : syracuseStep 7373197 = 2764949) B2764949
theorem B39323717 : Blo 2045435 39323717 := bstep (se 4 (by rfl) ⟨3686598, by rfl⟩ : syracuseStep 39323717 = 7373197) B7373197
theorem B26215811 : Blo 2045435 26215811 := bstep (se 1 (by rfl) ⟨19661858, by rfl⟩ : syracuseStep 26215811 = 39323717) B39323717
theorem B17477207 : Blo 2045435 17477207 := bstep (se 1 (by rfl) ⟨13107905, by rfl⟩ : syracuseStep 17477207 = 26215811) B26215811
theorem B11651471 : Blo 2045435 11651471 := bstep (se 1 (by rfl) ⟨8738603, by rfl⟩ : syracuseStep 11651471 = 17477207) B17477207
theorem B7767647 : Blo 2045435 7767647 := bstep (se 1 (by rfl) ⟨5825735, by rfl⟩ : syracuseStep 7767647 = 11651471) B11651471
theorem B5178431 : Blo 2045435 5178431 := bstep (se 1 (by rfl) ⟨3883823, by rfl⟩ : syracuseStep 5178431 = 7767647) B7767647
theorem B3452287 : Blo 2045435 3452287 := bstep (se 1 (by rfl) ⟨2589215, by rfl⟩ : syracuseStep 3452287 = 5178431) B5178431
theorem B4603049 : Blo 2045435 4603049 := bstep (se 2 (by rfl) ⟨1726143, by rfl⟩ : syracuseStep 4603049 = 3452287) B3452287
theorem B3068699 : Blo 2045435 3068699 := bstep (se 1 (by rfl) ⟨2301524, by rfl⟩ : syracuseStep 3068699 = 4603049) B4603049
theorem B2045799 : Blo 2045435 2045799 := bstep (se 1 (by rfl) ⟨1534349, by rfl⟩ : syracuseStep 2045799 = 3068699) B3068699
theorem B2301529 : Blo 2045435 2301529 := bbase (se 2 (by rfl) ⟨863073, by rfl⟩ : syracuseStep 2301529 = 1726147) (by norm_num)
theorem B3068705 : Blo 2045435 3068705 := bstep (se 2 (by rfl) ⟨1150764, by rfl⟩ : syracuseStep 3068705 = 2301529) B2301529
theorem B2045803 : Blo 2045435 2045803 := bstep (se 1 (by rfl) ⟨1534352, by rfl⟩ : syracuseStep 2045803 = 3068705) B3068705
theorem B15747317 : Blo 2045435 15747317 := bbase (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) (by norm_num)
theorem B10498211 : Blo 2045435 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B6998807 : Blo 2045435 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B4665871 : Blo 2045435 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B6221161 : Blo 2045435 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B8294881 : Blo 2045435 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B11059841 : Blo 2045435 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B7373227 : Blo 2045435 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B9830969 : Blo 2045435 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B6553979 : Blo 2045435 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B4369319 : Blo 2045435 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B2912879 : Blo 2045435 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B7767677 : Blo 2045435 7767677 := bstep (se 3 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 7767677 = 2912879) B2912879
theorem B5178451 : Blo 2045435 5178451 := bstep (se 1 (by rfl) ⟨3883838, by rfl⟩ : syracuseStep 5178451 = 7767677) B7767677
theorem B6904601 : Blo 2045435 6904601 := bstep (se 2 (by rfl) ⟨2589225, by rfl⟩ : syracuseStep 6904601 = 5178451) B5178451
theorem B4603067 : Blo 2045435 4603067 := bstep (se 1 (by rfl) ⟨3452300, by rfl⟩ : syracuseStep 4603067 = 6904601) B6904601
theorem B3068711 : Blo 2045435 3068711 := bstep (se 1 (by rfl) ⟨2301533, by rfl⟩ : syracuseStep 3068711 = 4603067) B4603067
theorem B2045807 : Blo 2045435 2045807 := bstep (se 1 (by rfl) ⟨1534355, by rfl⟩ : syracuseStep 2045807 = 3068711) B3068711
theorem B3068717 : Blo 2045435 3068717 := bbase (se 3 (by rfl) ⟨575384, by rfl⟩ : syracuseStep 3068717 = 1150769) (by norm_num)
theorem B2045811 : Blo 2045435 2045811 := bstep (se 1 (by rfl) ⟨1534358, by rfl⟩ : syracuseStep 2045811 = 3068717) B3068717
theorem B4603085 : Blo 2045435 4603085 := bbase (se 3 (by rfl) ⟨863078, by rfl⟩ : syracuseStep 4603085 = 1726157) (by norm_num)
theorem B3068723 : Blo 2045435 3068723 := bstep (se 1 (by rfl) ⟨2301542, by rfl⟩ : syracuseStep 3068723 = 4603085) B4603085
theorem B2045815 : Blo 2045435 2045815 := bstep (se 1 (by rfl) ⟨1534361, by rfl⟩ : syracuseStep 2045815 = 3068723) B3068723
theorem B2589241 : Blo 2045435 2589241 := bbase (se 2 (by rfl) ⟨970965, by rfl⟩ : syracuseStep 2589241 = 1941931) (by norm_num)
theorem B3452321 : Blo 2045435 3452321 := bstep (se 2 (by rfl) ⟨1294620, by rfl⟩ : syracuseStep 3452321 = 2589241) B2589241
theorem B2301547 : Blo 2045435 2301547 := bstep (se 1 (by rfl) ⟨1726160, by rfl⟩ : syracuseStep 2301547 = 3452321) B3452321
theorem B3068729 : Blo 2045435 3068729 := bstep (se 2 (by rfl) ⟨1150773, by rfl⟩ : syracuseStep 3068729 = 2301547) B2301547
theorem B2045819 : Blo 2045435 2045819 := bstep (se 1 (by rfl) ⟨1534364, by rfl⟩ : syracuseStep 2045819 = 3068729) B3068729
theorem B2457761 : Blo 2045435 2457761 := bbase (se 2 (by rfl) ⟨921660, by rfl⟩ : syracuseStep 2457761 = 1843321) (by norm_num)
theorem B6554029 : Blo 2045435 6554029 := bstep (se 3 (by rfl) ⟨1228880, by rfl⟩ : syracuseStep 6554029 = 2457761) B2457761
theorem B8738705 : Blo 2045435 8738705 := bstep (se 2 (by rfl) ⟨3277014, by rfl⟩ : syracuseStep 8738705 = 6554029) B6554029
theorem B23303213 : Blo 2045435 23303213 := bstep (se 3 (by rfl) ⟨4369352, by rfl⟩ : syracuseStep 23303213 = 8738705) B8738705
theorem B15535475 : Blo 2045435 15535475 := bstep (se 1 (by rfl) ⟨11651606, by rfl⟩ : syracuseStep 15535475 = 23303213) B23303213
theorem B10356983 : Blo 2045435 10356983 := bstep (se 1 (by rfl) ⟨7767737, by rfl⟩ : syracuseStep 10356983 = 15535475) B15535475
theorem B6904655 : Blo 2045435 6904655 := bstep (se 1 (by rfl) ⟨5178491, by rfl⟩ : syracuseStep 6904655 = 10356983) B10356983
theorem B4603103 : Blo 2045435 4603103 := bstep (se 1 (by rfl) ⟨3452327, by rfl⟩ : syracuseStep 4603103 = 6904655) B6904655
theorem B3068735 : Blo 2045435 3068735 := bstep (se 1 (by rfl) ⟨2301551, by rfl⟩ : syracuseStep 3068735 = 4603103) B4603103
theorem B2045823 : Blo 2045435 2045823 := bstep (se 1 (by rfl) ⟨1534367, by rfl⟩ : syracuseStep 2045823 = 3068735) B3068735
theorem B3068741 : Blo 2045435 3068741 := bbase (se 4 (by rfl) ⟨287694, by rfl⟩ : syracuseStep 3068741 = 575389) (by norm_num)
theorem B2045827 : Blo 2045435 2045827 := bstep (se 1 (by rfl) ⟨1534370, by rfl⟩ : syracuseStep 2045827 = 3068741) B3068741
theorem B3452341 : Blo 2045435 3452341 := bbase (se 5 (by rfl) ⟨161828, by rfl⟩ : syracuseStep 3452341 = 323657) (by norm_num)
theorem B4603121 : Blo 2045435 4603121 := bstep (se 2 (by rfl) ⟨1726170, by rfl⟩ : syracuseStep 4603121 = 3452341) B3452341
theorem B3068747 : Blo 2045435 3068747 := bstep (se 1 (by rfl) ⟨2301560, by rfl⟩ : syracuseStep 3068747 = 4603121) B4603121
theorem B2045831 : Blo 2045435 2045831 := bstep (se 1 (by rfl) ⟨1534373, by rfl⟩ : syracuseStep 2045831 = 3068747) B3068747
theorem B2301565 : Blo 2045435 2301565 := bbase (se 3 (by rfl) ⟨431543, by rfl⟩ : syracuseStep 2301565 = 863087) (by norm_num)
theorem B3068753 : Blo 2045435 3068753 := bstep (se 2 (by rfl) ⟨1150782, by rfl⟩ : syracuseStep 3068753 = 2301565) B2301565
theorem B2045835 : Blo 2045435 2045835 := bstep (se 1 (by rfl) ⟨1534376, by rfl⟩ : syracuseStep 2045835 = 3068753) B3068753
theorem B6904709 : Blo 2045435 6904709 := bbase (se 4 (by rfl) ⟨647316, by rfl⟩ : syracuseStep 6904709 = 1294633) (by norm_num)
theorem B4603139 : Blo 2045435 4603139 := bstep (se 1 (by rfl) ⟨3452354, by rfl⟩ : syracuseStep 4603139 = 6904709) B6904709
theorem B3068759 : Blo 2045435 3068759 := bstep (se 1 (by rfl) ⟨2301569, by rfl⟩ : syracuseStep 3068759 = 4603139) B4603139
theorem B2045839 : Blo 2045435 2045839 := bstep (se 1 (by rfl) ⟨1534379, by rfl⟩ : syracuseStep 2045839 = 3068759) B3068759
theorem B3068765 : Blo 2045435 3068765 := bbase (se 3 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 3068765 = 1150787) (by norm_num)
theorem B2045843 : Blo 2045435 2045843 := bstep (se 1 (by rfl) ⟨1534382, by rfl⟩ : syracuseStep 2045843 = 3068765) B3068765
theorem B4603157 : Blo 2045435 4603157 := bbase (se 6 (by rfl) ⟨107886, by rfl⟩ : syracuseStep 4603157 = 215773) (by norm_num)
theorem B3068771 : Blo 2045435 3068771 := bstep (se 1 (by rfl) ⟨2301578, by rfl⟩ : syracuseStep 3068771 = 4603157) B4603157
theorem B2045847 : Blo 2045435 2045847 := bstep (se 1 (by rfl) ⟨1534385, by rfl⟩ : syracuseStep 2045847 = 3068771) B3068771
theorem B7767845 : Blo 2045435 7767845 := bbase (se 4 (by rfl) ⟨728235, by rfl⟩ : syracuseStep 7767845 = 1456471) (by norm_num)
theorem B5178563 : Blo 2045435 5178563 := bstep (se 1 (by rfl) ⟨3883922, by rfl⟩ : syracuseStep 5178563 = 7767845) B7767845
theorem B3452375 : Blo 2045435 3452375 := bstep (se 1 (by rfl) ⟨2589281, by rfl⟩ : syracuseStep 3452375 = 5178563) B5178563
theorem B2301583 : Blo 2045435 2301583 := bstep (se 1 (by rfl) ⟨1726187, by rfl⟩ : syracuseStep 2301583 = 3452375) B3452375
theorem B3068777 : Blo 2045435 3068777 := bstep (se 2 (by rfl) ⟨1150791, by rfl⟩ : syracuseStep 3068777 = 2301583) B2301583
theorem B2045851 : Blo 2045435 2045851 := bstep (se 1 (by rfl) ⟨1534388, by rfl⟩ : syracuseStep 2045851 = 3068777) B3068777
theorem B4369421 : Blo 2045435 4369421 := bbase (se 3 (by rfl) ⟨819266, by rfl⟩ : syracuseStep 4369421 = 1638533) (by norm_num)
theorem B11651789 : Blo 2045435 11651789 := bstep (se 3 (by rfl) ⟨2184710, by rfl⟩ : syracuseStep 11651789 = 4369421) B4369421
theorem B7767859 : Blo 2045435 7767859 := bstep (se 1 (by rfl) ⟨5825894, by rfl⟩ : syracuseStep 7767859 = 11651789) B11651789
theorem B10357145 : Blo 2045435 10357145 := bstep (se 2 (by rfl) ⟨3883929, by rfl⟩ : syracuseStep 10357145 = 7767859) B7767859
theorem B6904763 : Blo 2045435 6904763 := bstep (se 1 (by rfl) ⟨5178572, by rfl⟩ : syracuseStep 6904763 = 10357145) B10357145
theorem B4603175 : Blo 2045435 4603175 := bstep (se 1 (by rfl) ⟨3452381, by rfl⟩ : syracuseStep 4603175 = 6904763) B6904763
theorem B3068783 : Blo 2045435 3068783 := bstep (se 1 (by rfl) ⟨2301587, by rfl⟩ : syracuseStep 3068783 = 4603175) B4603175
theorem B2045855 : Blo 2045435 2045855 := bstep (se 1 (by rfl) ⟨1534391, by rfl⟩ : syracuseStep 2045855 = 3068783) B3068783
theorem B3068789 : Blo 2045435 3068789 := bbase (se 5 (by rfl) ⟨143849, by rfl⟩ : syracuseStep 3068789 = 287699) (by norm_num)
theorem B2045859 : Blo 2045435 2045859 := bstep (se 1 (by rfl) ⟨1534394, by rfl⟩ : syracuseStep 2045859 = 3068789) B3068789
theorem B5050669 : Blo 2045435 5050669 := bbase (se 3 (by rfl) ⟨947000, by rfl⟩ : syracuseStep 5050669 = 1894001) (by norm_num)
theorem B6734225 : Blo 2045435 6734225 := bstep (se 2 (by rfl) ⟨2525334, by rfl⟩ : syracuseStep 6734225 = 5050669) B5050669
theorem B17957933 : Blo 2045435 17957933 := bstep (se 3 (by rfl) ⟨3367112, by rfl⟩ : syracuseStep 17957933 = 6734225) B6734225
theorem B11971955 : Blo 2045435 11971955 := bstep (se 1 (by rfl) ⟨8978966, by rfl⟩ : syracuseStep 11971955 = 17957933) B17957933
theorem B7981303 : Blo 2045435 7981303 := bstep (se 1 (by rfl) ⟨5985977, by rfl⟩ : syracuseStep 7981303 = 11971955) B11971955
theorem B10641737 : Blo 2045435 10641737 := bstep (se 2 (by rfl) ⟨3990651, by rfl⟩ : syracuseStep 10641737 = 7981303) B7981303
theorem B28377965 : Blo 2045435 28377965 := bstep (se 3 (by rfl) ⟨5320868, by rfl⟩ : syracuseStep 28377965 = 10641737) B10641737
theorem B18918643 : Blo 2045435 18918643 := bstep (se 1 (by rfl) ⟨14188982, by rfl⟩ : syracuseStep 18918643 = 28377965) B28377965
theorem B25224857 : Blo 2045435 25224857 := bstep (se 2 (by rfl) ⟨9459321, by rfl⟩ : syracuseStep 25224857 = 18918643) B18918643
theorem B16816571 : Blo 2045435 16816571 := bstep (se 1 (by rfl) ⟨12612428, by rfl⟩ : syracuseStep 16816571 = 25224857) B25224857
theorem B11211047 : Blo 2045435 11211047 := bstep (se 1 (by rfl) ⟨8408285, by rfl⟩ : syracuseStep 11211047 = 16816571) B16816571
theorem B7474031 : Blo 2045435 7474031 := bstep (se 1 (by rfl) ⟨5605523, by rfl⟩ : syracuseStep 7474031 = 11211047) B11211047
theorem B4982687 : Blo 2045435 4982687 := bstep (se 1 (by rfl) ⟨3737015, by rfl⟩ : syracuseStep 4982687 = 7474031) B7474031
theorem B3321791 : Blo 2045435 3321791 := bstep (se 1 (by rfl) ⟨2491343, by rfl⟩ : syracuseStep 3321791 = 4982687) B4982687
theorem B2214527 : Blo 2045435 2214527 := bstep (se 1 (by rfl) ⟨1660895, by rfl⟩ : syracuseStep 2214527 = 3321791) B3321791
theorem B5905405 : Blo 2045435 5905405 := bstep (se 3 (by rfl) ⟨1107263, by rfl⟩ : syracuseStep 5905405 = 2214527) B2214527
theorem B31495493 : Blo 2045435 31495493 := bstep (se 4 (by rfl) ⟨2952702, by rfl⟩ : syracuseStep 31495493 = 5905405) B5905405
theorem B20996995 : Blo 2045435 20996995 := bstep (se 1 (by rfl) ⟨15747746, by rfl⟩ : syracuseStep 20996995 = 31495493) B31495493
theorem B27995993 : Blo 2045435 27995993 := bstep (se 2 (by rfl) ⟨10498497, by rfl⟩ : syracuseStep 27995993 = 20996995) B20996995
theorem B18663995 : Blo 2045435 18663995 := bstep (se 1 (by rfl) ⟨13997996, by rfl⟩ : syracuseStep 18663995 = 27995993) B27995993
theorem B12442663 : Blo 2045435 12442663 := bstep (se 1 (by rfl) ⟨9331997, by rfl⟩ : syracuseStep 12442663 = 18663995) B18663995
theorem B16590217 : Blo 2045435 16590217 := bstep (se 2 (by rfl) ⟨6221331, by rfl⟩ : syracuseStep 16590217 = 12442663) B12442663
theorem B22120289 : Blo 2045435 22120289 := bstep (se 2 (by rfl) ⟨8295108, by rfl⟩ : syracuseStep 22120289 = 16590217) B16590217
theorem B14746859 : Blo 2045435 14746859 := bstep (se 1 (by rfl) ⟨11060144, by rfl⟩ : syracuseStep 14746859 = 22120289) B22120289
theorem B9831239 : Blo 2045435 9831239 := bstep (se 1 (by rfl) ⟨7373429, by rfl⟩ : syracuseStep 9831239 = 14746859) B14746859
theorem B6554159 : Blo 2045435 6554159 := bstep (se 1 (by rfl) ⟨4915619, by rfl⟩ : syracuseStep 6554159 = 9831239) B9831239
theorem B4369439 : Blo 2045435 4369439 := bstep (se 1 (by rfl) ⟨3277079, by rfl⟩ : syracuseStep 4369439 = 6554159) B6554159
theorem B2912959 : Blo 2045435 2912959 := bstep (se 1 (by rfl) ⟨2184719, by rfl⟩ : syracuseStep 2912959 = 4369439) B4369439
theorem B3883945 : Blo 2045435 3883945 := bstep (se 2 (by rfl) ⟨1456479, by rfl⟩ : syracuseStep 3883945 = 2912959) B2912959
theorem B5178593 : Blo 2045435 5178593 := bstep (se 2 (by rfl) ⟨1941972, by rfl⟩ : syracuseStep 5178593 = 3883945) B3883945
theorem B3452395 : Blo 2045435 3452395 := bstep (se 1 (by rfl) ⟨2589296, by rfl⟩ : syracuseStep 3452395 = 5178593) B5178593
theorem B4603193 : Blo 2045435 4603193 := bstep (se 2 (by rfl) ⟨1726197, by rfl⟩ : syracuseStep 4603193 = 3452395) B3452395
theorem B3068795 : Blo 2045435 3068795 := bstep (se 1 (by rfl) ⟨2301596, by rfl⟩ : syracuseStep 3068795 = 4603193) B4603193
theorem B2045863 : Blo 2045435 2045863 := bstep (se 1 (by rfl) ⟨1534397, by rfl⟩ : syracuseStep 2045863 = 3068795) B3068795
theorem B2301601 : Blo 2045435 2301601 := bbase (se 2 (by rfl) ⟨863100, by rfl⟩ : syracuseStep 2301601 = 1726201) (by norm_num)
theorem B3068801 : Blo 2045435 3068801 := bstep (se 2 (by rfl) ⟨1150800, by rfl⟩ : syracuseStep 3068801 = 2301601) B2301601
theorem B2045867 : Blo 2045435 2045867 := bstep (se 1 (by rfl) ⟨1534400, by rfl⟩ : syracuseStep 2045867 = 3068801) B3068801
theorem B5178613 : Blo 2045435 5178613 := bbase (se 5 (by rfl) ⟨242747, by rfl⟩ : syracuseStep 5178613 = 485495) (by norm_num)
theorem B6904817 : Blo 2045435 6904817 := bstep (se 2 (by rfl) ⟨2589306, by rfl⟩ : syracuseStep 6904817 = 5178613) B5178613
theorem B4603211 : Blo 2045435 4603211 := bstep (se 1 (by rfl) ⟨3452408, by rfl⟩ : syracuseStep 4603211 = 6904817) B6904817
theorem B3068807 : Blo 2045435 3068807 := bstep (se 1 (by rfl) ⟨2301605, by rfl⟩ : syracuseStep 3068807 = 4603211) B4603211
theorem B2045871 : Blo 2045435 2045871 := bstep (se 1 (by rfl) ⟨1534403, by rfl⟩ : syracuseStep 2045871 = 3068807) B3068807
theorem B3068813 : Blo 2045435 3068813 := bbase (se 3 (by rfl) ⟨575402, by rfl⟩ : syracuseStep 3068813 = 1150805) (by norm_num)
theorem B2045875 : Blo 2045435 2045875 := bstep (se 1 (by rfl) ⟨1534406, by rfl⟩ : syracuseStep 2045875 = 3068813) B3068813
theorem B4603229 : Blo 2045435 4603229 := bbase (se 3 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 4603229 = 1726211) (by norm_num)
theorem B3068819 : Blo 2045435 3068819 := bstep (se 1 (by rfl) ⟨2301614, by rfl⟩ : syracuseStep 3068819 = 4603229) B4603229
theorem B2045879 : Blo 2045435 2045879 := bstep (se 1 (by rfl) ⟨1534409, by rfl⟩ : syracuseStep 2045879 = 3068819) B3068819
theorem B3452429 : Blo 2045435 3452429 := bbase (se 3 (by rfl) ⟨647330, by rfl⟩ : syracuseStep 3452429 = 1294661) (by norm_num)
theorem B2301619 : Blo 2045435 2301619 := bstep (se 1 (by rfl) ⟨1726214, by rfl⟩ : syracuseStep 2301619 = 3452429) B3452429
theorem B3068825 : Blo 2045435 3068825 := bstep (se 2 (by rfl) ⟨1150809, by rfl⟩ : syracuseStep 3068825 = 2301619) B2301619
theorem B2045883 : Blo 2045435 2045883 := bstep (se 1 (by rfl) ⟨1534412, by rfl⟩ : syracuseStep 2045883 = 3068825) B3068825
theorem B3277117 : Blo 2045435 3277117 := bbase (se 3 (by rfl) ⟨614459, by rfl⟩ : syracuseStep 3277117 = 1228919) (by norm_num)
theorem B17477957 : Blo 2045435 17477957 := bstep (se 4 (by rfl) ⟨1638558, by rfl⟩ : syracuseStep 17477957 = 3277117) B3277117
theorem B11651971 : Blo 2045435 11651971 := bstep (se 1 (by rfl) ⟨8738978, by rfl⟩ : syracuseStep 11651971 = 17477957) B17477957
theorem B15535961 : Blo 2045435 15535961 := bstep (se 2 (by rfl) ⟨5825985, by rfl⟩ : syracuseStep 15535961 = 11651971) B11651971
theorem B10357307 : Blo 2045435 10357307 := bstep (se 1 (by rfl) ⟨7767980, by rfl⟩ : syracuseStep 10357307 = 15535961) B15535961
theorem B6904871 : Blo 2045435 6904871 := bstep (se 1 (by rfl) ⟨5178653, by rfl⟩ : syracuseStep 6904871 = 10357307) B10357307
theorem B4603247 : Blo 2045435 4603247 := bstep (se 1 (by rfl) ⟨3452435, by rfl⟩ : syracuseStep 4603247 = 6904871) B6904871
theorem B3068831 : Blo 2045435 3068831 := bstep (se 1 (by rfl) ⟨2301623, by rfl⟩ : syracuseStep 3068831 = 4603247) B4603247
theorem B2045887 : Blo 2045435 2045887 := bstep (se 1 (by rfl) ⟨1534415, by rfl⟩ : syracuseStep 2045887 = 3068831) B3068831
theorem B3068837 : Blo 2045435 3068837 := bbase (se 4 (by rfl) ⟨287703, by rfl⟩ : syracuseStep 3068837 = 575407) (by norm_num)
theorem B2045891 : Blo 2045435 2045891 := bstep (se 1 (by rfl) ⟨1534418, by rfl⟩ : syracuseStep 2045891 = 3068837) B3068837
theorem B2589337 : Blo 2045435 2589337 := bbase (se 2 (by rfl) ⟨971001, by rfl⟩ : syracuseStep 2589337 = 1942003) (by norm_num)
theorem B3452449 : Blo 2045435 3452449 := bstep (se 2 (by rfl) ⟨1294668, by rfl⟩ : syracuseStep 3452449 = 2589337) B2589337
theorem B4603265 : Blo 2045435 4603265 := bstep (se 2 (by rfl) ⟨1726224, by rfl⟩ : syracuseStep 4603265 = 3452449) B3452449
theorem B3068843 : Blo 2045435 3068843 := bstep (se 1 (by rfl) ⟨2301632, by rfl⟩ : syracuseStep 3068843 = 4603265) B4603265
theorem B2045895 : Blo 2045435 2045895 := bstep (se 1 (by rfl) ⟨1534421, by rfl⟩ : syracuseStep 2045895 = 3068843) B3068843
theorem B2301637 : Blo 2045435 2301637 := bbase (se 4 (by rfl) ⟨215778, by rfl⟩ : syracuseStep 2301637 = 431557) (by norm_num)
theorem B3068849 : Blo 2045435 3068849 := bstep (se 2 (by rfl) ⟨1150818, by rfl⟩ : syracuseStep 3068849 = 2301637) B2301637
theorem B2045899 : Blo 2045435 2045899 := bstep (se 1 (by rfl) ⟨1534424, by rfl⟩ : syracuseStep 2045899 = 3068849) B3068849
theorem B3884021 : Blo 2045435 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B2589347 : Blo 2045435 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B6904925 : Blo 2045435 6904925 := bstep (se 3 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 6904925 = 2589347) B2589347
theorem B4603283 : Blo 2045435 4603283 := bstep (se 1 (by rfl) ⟨3452462, by rfl⟩ : syracuseStep 4603283 = 6904925) B6904925
theorem B3068855 : Blo 2045435 3068855 := bstep (se 1 (by rfl) ⟨2301641, by rfl⟩ : syracuseStep 3068855 = 4603283) B4603283
theorem B2045903 : Blo 2045435 2045903 := bstep (se 1 (by rfl) ⟨1534427, by rfl⟩ : syracuseStep 2045903 = 3068855) B3068855
theorem B3068861 : Blo 2045435 3068861 := bbase (se 3 (by rfl) ⟨575411, by rfl⟩ : syracuseStep 3068861 = 1150823) (by norm_num)
theorem B2045907 : Blo 2045435 2045907 := bstep (se 1 (by rfl) ⟨1534430, by rfl⟩ : syracuseStep 2045907 = 3068861) B3068861
theorem B4603301 : Blo 2045435 4603301 := bbase (se 4 (by rfl) ⟨431559, by rfl⟩ : syracuseStep 4603301 = 863119) (by norm_num)
theorem B3068867 : Blo 2045435 3068867 := bstep (se 1 (by rfl) ⟨2301650, by rfl⟩ : syracuseStep 3068867 = 4603301) B4603301
theorem B2045911 : Blo 2045435 2045911 := bstep (se 1 (by rfl) ⟨1534433, by rfl⟩ : syracuseStep 2045911 = 3068867) B3068867
theorem B5178725 : Blo 2045435 5178725 := bbase (se 4 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 5178725 = 971011) (by norm_num)
theorem B3452483 : Blo 2045435 3452483 := bstep (se 1 (by rfl) ⟨2589362, by rfl⟩ : syracuseStep 3452483 = 5178725) B5178725
theorem B2301655 : Blo 2045435 2301655 := bstep (se 1 (by rfl) ⟨1726241, by rfl⟩ : syracuseStep 2301655 = 3452483) B3452483
theorem B3068873 : Blo 2045435 3068873 := bstep (se 2 (by rfl) ⟨1150827, by rfl⟩ : syracuseStep 3068873 = 2301655) B2301655
theorem B2045915 : Blo 2045435 2045915 := bstep (se 1 (by rfl) ⟨1534436, by rfl⟩ : syracuseStep 2045915 = 3068873) B3068873
theorem B2457877 : Blo 2045435 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B3277169 : Blo 2045435 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B2184779 : Blo 2045435 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B5826077 : Blo 2045435 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B3884051 : Blo 2045435 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B10357469 : Blo 2045435 10357469 := bstep (se 3 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 10357469 = 3884051) B3884051
theorem B6904979 : Blo 2045435 6904979 := bstep (se 1 (by rfl) ⟨5178734, by rfl⟩ : syracuseStep 6904979 = 10357469) B10357469
theorem B4603319 : Blo 2045435 4603319 := bstep (se 1 (by rfl) ⟨3452489, by rfl⟩ : syracuseStep 4603319 = 6904979) B6904979
theorem B3068879 : Blo 2045435 3068879 := bstep (se 1 (by rfl) ⟨2301659, by rfl⟩ : syracuseStep 3068879 = 4603319) B4603319
theorem B2045919 : Blo 2045435 2045919 := bstep (se 1 (by rfl) ⟨1534439, by rfl⟩ : syracuseStep 2045919 = 3068879) B3068879
theorem B3068885 : Blo 2045435 3068885 := bbase (se 7 (by rfl) ⟨35963, by rfl⟩ : syracuseStep 3068885 = 71927) (by norm_num)
theorem B2045923 : Blo 2045435 2045923 := bstep (se 1 (by rfl) ⟨1534442, by rfl⟩ : syracuseStep 2045923 = 3068885) B3068885
theorem B7768133 : Blo 2045435 7768133 := bbase (se 4 (by rfl) ⟨728262, by rfl⟩ : syracuseStep 7768133 = 1456525) (by norm_num)
theorem B5178755 : Blo 2045435 5178755 := bstep (se 1 (by rfl) ⟨3884066, by rfl⟩ : syracuseStep 5178755 = 7768133) B7768133
theorem B3452503 : Blo 2045435 3452503 := bstep (se 1 (by rfl) ⟨2589377, by rfl⟩ : syracuseStep 3452503 = 5178755) B5178755
theorem B4603337 : Blo 2045435 4603337 := bstep (se 2 (by rfl) ⟨1726251, by rfl⟩ : syracuseStep 4603337 = 3452503) B3452503
theorem B3068891 : Blo 2045435 3068891 := bstep (se 1 (by rfl) ⟨2301668, by rfl⟩ : syracuseStep 3068891 = 4603337) B4603337
theorem B2045927 : Blo 2045435 2045927 := bstep (se 1 (by rfl) ⟨1534445, by rfl⟩ : syracuseStep 2045927 = 3068891) B3068891
theorem B2301673 : Blo 2045435 2301673 := bbase (se 2 (by rfl) ⟨863127, by rfl⟩ : syracuseStep 2301673 = 1726255) (by norm_num)
theorem B3068897 : Blo 2045435 3068897 := bstep (se 2 (by rfl) ⟨1150836, by rfl⟩ : syracuseStep 3068897 = 2301673) B2301673
theorem B2045931 : Blo 2045435 2045931 := bstep (se 1 (by rfl) ⟨1534448, by rfl⟩ : syracuseStep 2045931 = 3068897) B3068897
theorem B11652245 : Blo 2045435 11652245 := bbase (se 6 (by rfl) ⟨273099, by rfl⟩ : syracuseStep 11652245 = 546199) (by norm_num)
theorem B7768163 : Blo 2045435 7768163 := bstep (se 1 (by rfl) ⟨5826122, by rfl⟩ : syracuseStep 7768163 = 11652245) B11652245
theorem B5178775 : Blo 2045435 5178775 := bstep (se 1 (by rfl) ⟨3884081, by rfl⟩ : syracuseStep 5178775 = 7768163) B7768163
theorem B6905033 : Blo 2045435 6905033 := bstep (se 2 (by rfl) ⟨2589387, by rfl⟩ : syracuseStep 6905033 = 5178775) B5178775
theorem B4603355 : Blo 2045435 4603355 := bstep (se 1 (by rfl) ⟨3452516, by rfl⟩ : syracuseStep 4603355 = 6905033) B6905033
theorem B3068903 : Blo 2045435 3068903 := bstep (se 1 (by rfl) ⟨2301677, by rfl⟩ : syracuseStep 3068903 = 4603355) B4603355
theorem B2045935 : Blo 2045435 2045935 := bstep (se 1 (by rfl) ⟨1534451, by rfl⟩ : syracuseStep 2045935 = 3068903) B3068903
theorem B3068909 : Blo 2045435 3068909 := bbase (se 3 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 3068909 = 1150841) (by norm_num)
theorem B2045939 : Blo 2045435 2045939 := bstep (se 1 (by rfl) ⟨1534454, by rfl⟩ : syracuseStep 2045939 = 3068909) B3068909
theorem B4603373 : Blo 2045435 4603373 := bbase (se 3 (by rfl) ⟨863132, by rfl⟩ : syracuseStep 4603373 = 1726265) (by norm_num)
theorem B3068915 : Blo 2045435 3068915 := bstep (se 1 (by rfl) ⟨2301686, by rfl⟩ : syracuseStep 3068915 = 4603373) B4603373
theorem B2045943 : Blo 2045435 2045943 := bstep (se 1 (by rfl) ⟨1534457, by rfl⟩ : syracuseStep 2045943 = 3068915) B3068915
theorem B3499645 : Blo 2045435 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B4666193 : Blo 2045435 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B3110795 : Blo 2045435 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B2073863 : Blo 2045435 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B5530301 : Blo 2045435 5530301 := bstep (se 3 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 5530301 = 2073863) B2073863
theorem B3686867 : Blo 2045435 3686867 := bstep (se 1 (by rfl) ⟨2765150, by rfl⟩ : syracuseStep 3686867 = 5530301) B5530301
theorem B2457911 : Blo 2045435 2457911 := bstep (se 1 (by rfl) ⟨1843433, by rfl⟩ : syracuseStep 2457911 = 3686867) B3686867
theorem B6554429 : Blo 2045435 6554429 := bstep (se 3 (by rfl) ⟨1228955, by rfl⟩ : syracuseStep 6554429 = 2457911) B2457911
theorem B4369619 : Blo 2045435 4369619 := bstep (se 1 (by rfl) ⟨3277214, by rfl⟩ : syracuseStep 4369619 = 6554429) B6554429
theorem B2913079 : Blo 2045435 2913079 := bstep (se 1 (by rfl) ⟨2184809, by rfl⟩ : syracuseStep 2913079 = 4369619) B4369619
theorem B3884105 : Blo 2045435 3884105 := bstep (se 2 (by rfl) ⟨1456539, by rfl⟩ : syracuseStep 3884105 = 2913079) B2913079
theorem B2589403 : Blo 2045435 2589403 := bstep (se 1 (by rfl) ⟨1942052, by rfl⟩ : syracuseStep 2589403 = 3884105) B3884105
theorem B3452537 : Blo 2045435 3452537 := bstep (se 2 (by rfl) ⟨1294701, by rfl⟩ : syracuseStep 3452537 = 2589403) B2589403
theorem B2301691 : Blo 2045435 2301691 := bstep (se 1 (by rfl) ⟨1726268, by rfl⟩ : syracuseStep 2301691 = 3452537) B3452537
theorem B3068921 : Blo 2045435 3068921 := bstep (se 2 (by rfl) ⟨1150845, by rfl⟩ : syracuseStep 3068921 = 2301691) B2301691
theorem B2045947 : Blo 2045435 2045947 := bstep (se 1 (by rfl) ⟨1534460, by rfl⟩ : syracuseStep 2045947 = 3068921) B3068921
theorem B5918005 : Blo 2045435 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B31562693 : Blo 2045435 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B21041795 : Blo 2045435 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B14027863 : Blo 2045435 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B18703817 : Blo 2045435 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B12469211 : Blo 2045435 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B8312807 : Blo 2045435 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B5541871 : Blo 2045435 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B7389161 : Blo 2045435 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B4926107 : Blo 2045435 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B3284071 : Blo 2045435 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B17515045 : Blo 2045435 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B93413573 : Blo 2045435 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B62275715 : Blo 2045435 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B41517143 : Blo 2045435 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B27678095 : Blo 2045435 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B18452063 : Blo 2045435 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B12301375 : Blo 2045435 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B16401833 : Blo 2045435 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B174952885 : Blo 2045435 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B233270513 : Blo 2045435 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B155513675 : Blo 2045435 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B103675783 : Blo 2045435 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B138234377 : Blo 2045435 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B92156251 : Blo 2045435 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B122875001 : Blo 2045435 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B81916667 : Blo 2045435 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B54611111 : Blo 2045435 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B36407407 : Blo 2045435 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B48543209 : Blo 2045435 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B32362139 : Blo 2045435 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B21574759 : Blo 2045435 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B28766345 : Blo 2045435 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B76710253 : Blo 2045435 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B102280337 : Blo 2045435 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B68186891 : Blo 2045435 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B181831709 : Blo 2045435 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B121221139 : Blo 2045435 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B161628185 : Blo 2045435 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B107752123 : Blo 2045435 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B143669497 : Blo 2045435 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B191559329 : Blo 2045435 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B127706219 : Blo 2045435 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B85137479 : Blo 2045435 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B56758319 : Blo 2045435 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B37838879 : Blo 2045435 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B25225919 : Blo 2045435 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B16817279 : Blo 2045435 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B44846077 : Blo 2045435 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 2045435 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B39863179 : Blo 2045435 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 2045435 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 2045435 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 2045435 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 2045435 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 2045435 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 2045435 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 2045435 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 2045435 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 2045435 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 2045435 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B117979901 : Blo 2045435 117979901 := bstep (se 3 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 117979901 = 44242463) B44242463
theorem B78653267 : Blo 2045435 78653267 := bstep (se 1 (by rfl) ⟨58989950, by rfl⟩ : syracuseStep 78653267 = 117979901) B117979901
theorem B52435511 : Blo 2045435 52435511 := bstep (se 1 (by rfl) ⟨39326633, by rfl⟩ : syracuseStep 52435511 = 78653267) B78653267
theorem B34957007 : Blo 2045435 34957007 := bstep (se 1 (by rfl) ⟨26217755, by rfl⟩ : syracuseStep 34957007 = 52435511) B52435511
theorem B23304671 : Blo 2045435 23304671 := bstep (se 1 (by rfl) ⟨17478503, by rfl⟩ : syracuseStep 23304671 = 34957007) B34957007
theorem B15536447 : Blo 2045435 15536447 := bstep (se 1 (by rfl) ⟨11652335, by rfl⟩ : syracuseStep 15536447 = 23304671) B23304671
theorem B10357631 : Blo 2045435 10357631 := bstep (se 1 (by rfl) ⟨7768223, by rfl⟩ : syracuseStep 10357631 = 15536447) B15536447
theorem B6905087 : Blo 2045435 6905087 := bstep (se 1 (by rfl) ⟨5178815, by rfl⟩ : syracuseStep 6905087 = 10357631) B10357631
theorem B4603391 : Blo 2045435 4603391 := bstep (se 1 (by rfl) ⟨3452543, by rfl⟩ : syracuseStep 4603391 = 6905087) B6905087
theorem B3068927 : Blo 2045435 3068927 := bstep (se 1 (by rfl) ⟨2301695, by rfl⟩ : syracuseStep 3068927 = 4603391) B4603391
theorem B2045951 : Blo 2045435 2045951 := bstep (se 1 (by rfl) ⟨1534463, by rfl⟩ : syracuseStep 2045951 = 3068927) B3068927
theorem B3068933 : Blo 2045435 3068933 := bbase (se 4 (by rfl) ⟨287712, by rfl⟩ : syracuseStep 3068933 = 575425) (by norm_num)
theorem B2045955 : Blo 2045435 2045955 := bstep (se 1 (by rfl) ⟨1534466, by rfl⟩ : syracuseStep 2045955 = 3068933) B3068933
theorem B3452557 : Blo 2045435 3452557 := bbase (se 3 (by rfl) ⟨647354, by rfl⟩ : syracuseStep 3452557 = 1294709) (by norm_num)
theorem B4603409 : Blo 2045435 4603409 := bstep (se 2 (by rfl) ⟨1726278, by rfl⟩ : syracuseStep 4603409 = 3452557) B3452557
theorem B3068939 : Blo 2045435 3068939 := bstep (se 1 (by rfl) ⟨2301704, by rfl⟩ : syracuseStep 3068939 = 4603409) B4603409
theorem B2045959 : Blo 2045435 2045959 := bstep (se 1 (by rfl) ⟨1534469, by rfl⟩ : syracuseStep 2045959 = 3068939) B3068939
theorem B2301709 : Blo 2045435 2301709 := bbase (se 3 (by rfl) ⟨431570, by rfl⟩ : syracuseStep 2301709 = 863141) (by norm_num)
theorem B3068945 : Blo 2045435 3068945 := bstep (se 2 (by rfl) ⟨1150854, by rfl⟩ : syracuseStep 3068945 = 2301709) B2301709
theorem B2045963 : Blo 2045435 2045963 := bstep (se 1 (by rfl) ⟨1534472, by rfl⟩ : syracuseStep 2045963 = 3068945) B3068945
theorem B6905141 : Blo 2045435 6905141 := bbase (se 5 (by rfl) ⟨323678, by rfl⟩ : syracuseStep 6905141 = 647357) (by norm_num)
theorem B4603427 : Blo 2045435 4603427 := bstep (se 1 (by rfl) ⟨3452570, by rfl⟩ : syracuseStep 4603427 = 6905141) B6905141
theorem B3068951 : Blo 2045435 3068951 := bstep (se 1 (by rfl) ⟨2301713, by rfl⟩ : syracuseStep 3068951 = 4603427) B4603427
theorem B2045967 : Blo 2045435 2045967 := bstep (se 1 (by rfl) ⟨1534475, by rfl⟩ : syracuseStep 2045967 = 3068951) B3068951
theorem B3068957 : Blo 2045435 3068957 := bbase (se 3 (by rfl) ⟨575429, by rfl⟩ : syracuseStep 3068957 = 1150859) (by norm_num)
theorem B2045971 : Blo 2045435 2045971 := bstep (se 1 (by rfl) ⟨1534478, by rfl⟩ : syracuseStep 2045971 = 3068957) B3068957
theorem B4603445 : Blo 2045435 4603445 := bbase (se 5 (by rfl) ⟨215786, by rfl⟩ : syracuseStep 4603445 = 431573) (by norm_num)
theorem B3068963 : Blo 2045435 3068963 := bstep (se 1 (by rfl) ⟨2301722, by rfl⟩ : syracuseStep 3068963 = 4603445) B4603445
theorem B2045975 : Blo 2045435 2045975 := bstep (se 1 (by rfl) ⟨1534481, by rfl⟩ : syracuseStep 2045975 = 3068963) B3068963
theorem B2457949 : Blo 2045435 2457949 := bbase (se 3 (by rfl) ⟨460865, by rfl⟩ : syracuseStep 2457949 = 921731) (by norm_num)
theorem B3277265 : Blo 2045435 3277265 := bstep (se 2 (by rfl) ⟨1228974, by rfl⟩ : syracuseStep 3277265 = 2457949) B2457949
theorem B8739373 : Blo 2045435 8739373 := bstep (se 3 (by rfl) ⟨1638632, by rfl⟩ : syracuseStep 8739373 = 3277265) B3277265
theorem B11652497 : Blo 2045435 11652497 := bstep (se 2 (by rfl) ⟨4369686, by rfl⟩ : syracuseStep 11652497 = 8739373) B8739373
theorem B7768331 : Blo 2045435 7768331 := bstep (se 1 (by rfl) ⟨5826248, by rfl⟩ : syracuseStep 7768331 = 11652497) B11652497
theorem B5178887 : Blo 2045435 5178887 := bstep (se 1 (by rfl) ⟨3884165, by rfl⟩ : syracuseStep 5178887 = 7768331) B7768331
theorem B3452591 : Blo 2045435 3452591 := bstep (se 1 (by rfl) ⟨2589443, by rfl⟩ : syracuseStep 3452591 = 5178887) B5178887
theorem B2301727 : Blo 2045435 2301727 := bstep (se 1 (by rfl) ⟨1726295, by rfl⟩ : syracuseStep 2301727 = 3452591) B3452591
theorem B3068969 : Blo 2045435 3068969 := bstep (se 2 (by rfl) ⟨1150863, by rfl⟩ : syracuseStep 3068969 = 2301727) B2301727
theorem B2045979 : Blo 2045435 2045979 := bstep (se 1 (by rfl) ⟨1534484, by rfl⟩ : syracuseStep 2045979 = 3068969) B3068969
theorem B7373861 : Blo 2045435 7373861 := bbase (se 4 (by rfl) ⟨691299, by rfl⟩ : syracuseStep 7373861 = 1382599) (by norm_num)
theorem B4915907 : Blo 2045435 4915907 := bstep (se 1 (by rfl) ⟨3686930, by rfl⟩ : syracuseStep 4915907 = 7373861) B7373861
theorem B3277271 : Blo 2045435 3277271 := bstep (se 1 (by rfl) ⟨2457953, by rfl⟩ : syracuseStep 3277271 = 4915907) B4915907
theorem B8739389 : Blo 2045435 8739389 := bstep (se 3 (by rfl) ⟨1638635, by rfl⟩ : syracuseStep 8739389 = 3277271) B3277271
theorem B5826259 : Blo 2045435 5826259 := bstep (se 1 (by rfl) ⟨4369694, by rfl⟩ : syracuseStep 5826259 = 8739389) B8739389
theorem B7768345 : Blo 2045435 7768345 := bstep (se 2 (by rfl) ⟨2913129, by rfl⟩ : syracuseStep 7768345 = 5826259) B5826259
theorem B10357793 : Blo 2045435 10357793 := bstep (se 2 (by rfl) ⟨3884172, by rfl⟩ : syracuseStep 10357793 = 7768345) B7768345
theorem B6905195 : Blo 2045435 6905195 := bstep (se 1 (by rfl) ⟨5178896, by rfl⟩ : syracuseStep 6905195 = 10357793) B10357793
theorem B4603463 : Blo 2045435 4603463 := bstep (se 1 (by rfl) ⟨3452597, by rfl⟩ : syracuseStep 4603463 = 6905195) B6905195
theorem B3068975 : Blo 2045435 3068975 := bstep (se 1 (by rfl) ⟨2301731, by rfl⟩ : syracuseStep 3068975 = 4603463) B4603463
theorem B2045983 : Blo 2045435 2045983 := bstep (se 1 (by rfl) ⟨1534487, by rfl⟩ : syracuseStep 2045983 = 3068975) B3068975
theorem B3068981 : Blo 2045435 3068981 := bbase (se 5 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 3068981 = 287717) (by norm_num)
theorem B2045987 : Blo 2045435 2045987 := bstep (se 1 (by rfl) ⟨1534490, by rfl⟩ : syracuseStep 2045987 = 3068981) B3068981
theorem B5178917 : Blo 2045435 5178917 := bbase (se 4 (by rfl) ⟨485523, by rfl⟩ : syracuseStep 5178917 = 971047) (by norm_num)
theorem B3452611 : Blo 2045435 3452611 := bstep (se 1 (by rfl) ⟨2589458, by rfl⟩ : syracuseStep 3452611 = 5178917) B5178917
theorem B4603481 : Blo 2045435 4603481 := bstep (se 2 (by rfl) ⟨1726305, by rfl⟩ : syracuseStep 4603481 = 3452611) B3452611
theorem B3068987 : Blo 2045435 3068987 := bstep (se 1 (by rfl) ⟨2301740, by rfl⟩ : syracuseStep 3068987 = 4603481) B4603481
theorem B2045991 : Blo 2045435 2045991 := bstep (se 1 (by rfl) ⟨1534493, by rfl⟩ : syracuseStep 2045991 = 3068987) B3068987
theorem B2301745 : Blo 2045435 2301745 := bbase (se 2 (by rfl) ⟨863154, by rfl⟩ : syracuseStep 2301745 = 1726309) (by norm_num)
theorem B3068993 : Blo 2045435 3068993 := bstep (se 2 (by rfl) ⟨1150872, by rfl⟩ : syracuseStep 3068993 = 2301745) B2301745
theorem B2045995 : Blo 2045435 2045995 := bstep (se 1 (by rfl) ⟨1534496, by rfl⟩ : syracuseStep 2045995 = 3068993) B3068993
theorem B2457973 : Blo 2045435 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B3277297 : Blo 2045435 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B4369729 : Blo 2045435 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B5826305 : Blo 2045435 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B3884203 : Blo 2045435 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B5178937 : Blo 2045435 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B6905249 : Blo 2045435 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B4603499 : Blo 2045435 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B3068999 : Blo 2045435 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B2045999 : Blo 2045435 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B3069005 : Blo 2045435 3069005 := bbase (se 3 (by rfl) ⟨575438, by rfl⟩ : syracuseStep 3069005 = 1150877) (by norm_num)
theorem B2046003 : Blo 2045435 2046003 := bstep (se 1 (by rfl) ⟨1534502, by rfl⟩ : syracuseStep 2046003 = 3069005) B3069005
theorem B4603517 : Blo 2045435 4603517 := bbase (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) (by norm_num)
theorem B3069011 : Blo 2045435 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B2046007 : Blo 2045435 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B3452645 : Blo 2045435 3452645 := bbase (se 4 (by rfl) ⟨323685, by rfl⟩ : syracuseStep 3452645 = 647371) (by norm_num)
theorem B2301763 : Blo 2045435 2301763 := bstep (se 1 (by rfl) ⟨1726322, by rfl⟩ : syracuseStep 2301763 = 3452645) B3452645
theorem B3069017 : Blo 2045435 3069017 := bstep (se 2 (by rfl) ⟨1150881, by rfl⟩ : syracuseStep 3069017 = 2301763) B2301763
theorem B2046011 : Blo 2045435 2046011 := bstep (se 1 (by rfl) ⟨1534508, by rfl⟩ : syracuseStep 2046011 = 3069017) B3069017
theorem B6554645 : Blo 2045435 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B4369763 : Blo 2045435 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B2913175 : Blo 2045435 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B15536933 : Blo 2045435 15536933 := bstep (se 4 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 15536933 = 2913175) B2913175
theorem B10357955 : Blo 2045435 10357955 := bstep (se 1 (by rfl) ⟨7768466, by rfl⟩ : syracuseStep 10357955 = 15536933) B15536933
theorem B6905303 : Blo 2045435 6905303 := bstep (se 1 (by rfl) ⟨5178977, by rfl⟩ : syracuseStep 6905303 = 10357955) B10357955
theorem B4603535 : Blo 2045435 4603535 := bstep (se 1 (by rfl) ⟨3452651, by rfl⟩ : syracuseStep 4603535 = 6905303) B6905303
theorem B3069023 : Blo 2045435 3069023 := bstep (se 1 (by rfl) ⟨2301767, by rfl⟩ : syracuseStep 3069023 = 4603535) B4603535
theorem B2046015 : Blo 2045435 2046015 := bstep (se 1 (by rfl) ⟨1534511, by rfl⟩ : syracuseStep 2046015 = 3069023) B3069023
theorem B3069029 : Blo 2045435 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B2046019 : Blo 2045435 2046019 := bstep (se 1 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 2046019 = 3069029) B3069029
theorem B4369781 : Blo 2045435 4369781 := bbase (se 5 (by rfl) ⟨204833, by rfl⟩ : syracuseStep 4369781 = 409667) (by norm_num)
theorem B2913187 : Blo 2045435 2913187 := bstep (se 1 (by rfl) ⟨2184890, by rfl⟩ : syracuseStep 2913187 = 4369781) B4369781
theorem B3884249 : Blo 2045435 3884249 := bstep (se 2 (by rfl) ⟨1456593, by rfl⟩ : syracuseStep 3884249 = 2913187) B2913187
theorem B2589499 : Blo 2045435 2589499 := bstep (se 1 (by rfl) ⟨1942124, by rfl⟩ : syracuseStep 2589499 = 3884249) B3884249
theorem B3452665 : Blo 2045435 3452665 := bstep (se 2 (by rfl) ⟨1294749, by rfl⟩ : syracuseStep 3452665 = 2589499) B2589499
theorem B4603553 : Blo 2045435 4603553 := bstep (se 2 (by rfl) ⟨1726332, by rfl⟩ : syracuseStep 4603553 = 3452665) B3452665
theorem B3069035 : Blo 2045435 3069035 := bstep (se 1 (by rfl) ⟨2301776, by rfl⟩ : syracuseStep 3069035 = 4603553) B4603553
theorem B2046023 : Blo 2045435 2046023 := bstep (se 1 (by rfl) ⟨1534517, by rfl⟩ : syracuseStep 2046023 = 3069035) B3069035
theorem B2301781 : Blo 2045435 2301781 := bbase (se 9 (by rfl) ⟨6743, by rfl⟩ : syracuseStep 2301781 = 13487) (by norm_num)
theorem B3069041 : Blo 2045435 3069041 := bstep (se 2 (by rfl) ⟨1150890, by rfl⟩ : syracuseStep 3069041 = 2301781) B2301781
theorem B2046027 : Blo 2045435 2046027 := bstep (se 1 (by rfl) ⟨1534520, by rfl⟩ : syracuseStep 2046027 = 3069041) B3069041
theorem B2589509 : Blo 2045435 2589509 := bbase (se 4 (by rfl) ⟨242766, by rfl⟩ : syracuseStep 2589509 = 485533) (by norm_num)
theorem B6905357 : Blo 2045435 6905357 := bstep (se 3 (by rfl) ⟨1294754, by rfl⟩ : syracuseStep 6905357 = 2589509) B2589509
theorem B4603571 : Blo 2045435 4603571 := bstep (se 1 (by rfl) ⟨3452678, by rfl⟩ : syracuseStep 4603571 = 6905357) B6905357
theorem B3069047 : Blo 2045435 3069047 := bstep (se 1 (by rfl) ⟨2301785, by rfl⟩ : syracuseStep 3069047 = 4603571) B4603571
theorem B2046031 : Blo 2045435 2046031 := bstep (se 1 (by rfl) ⟨1534523, by rfl⟩ : syracuseStep 2046031 = 3069047) B3069047
theorem B3069053 : Blo 2045435 3069053 := bbase (se 3 (by rfl) ⟨575447, by rfl⟩ : syracuseStep 3069053 = 1150895) (by norm_num)
theorem B2046035 : Blo 2045435 2046035 := bstep (se 1 (by rfl) ⟨1534526, by rfl⟩ : syracuseStep 2046035 = 3069053) B3069053
theorem B4603589 : Blo 2045435 4603589 := bbase (se 4 (by rfl) ⟨431586, by rfl⟩ : syracuseStep 4603589 = 863173) (by norm_num)
theorem B3069059 : Blo 2045435 3069059 := bstep (se 1 (by rfl) ⟨2301794, by rfl⟩ : syracuseStep 3069059 = 4603589) B4603589
theorem B2046039 : Blo 2045435 2046039 := bstep (se 1 (by rfl) ⟨1534529, by rfl⟩ : syracuseStep 2046039 = 3069059) B3069059
theorem B5905925 : Blo 2045435 5905925 := bbase (se 4 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 5905925 = 1107361) (by norm_num)
theorem B3937283 : Blo 2045435 3937283 := bstep (se 1 (by rfl) ⟨2952962, by rfl⟩ : syracuseStep 3937283 = 5905925) B5905925
theorem B2624855 : Blo 2045435 2624855 := bstep (se 1 (by rfl) ⟨1968641, by rfl⟩ : syracuseStep 2624855 = 3937283) B3937283
theorem B27998453 : Blo 2045435 27998453 := bstep (se 5 (by rfl) ⟨1312427, by rfl⟩ : syracuseStep 27998453 = 2624855) B2624855
theorem B18665635 : Blo 2045435 18665635 := bstep (se 1 (by rfl) ⟨13999226, by rfl⟩ : syracuseStep 18665635 = 27998453) B27998453
theorem B24887513 : Blo 2045435 24887513 := bstep (se 2 (by rfl) ⟨9332817, by rfl⟩ : syracuseStep 24887513 = 18665635) B18665635
theorem B66366701 : Blo 2045435 66366701 := bstep (se 3 (by rfl) ⟨12443756, by rfl⟩ : syracuseStep 66366701 = 24887513) B24887513
theorem B44244467 : Blo 2045435 44244467 := bstep (se 1 (by rfl) ⟨33183350, by rfl⟩ : syracuseStep 44244467 = 66366701) B66366701
theorem B29496311 : Blo 2045435 29496311 := bstep (se 1 (by rfl) ⟨22122233, by rfl⟩ : syracuseStep 29496311 = 44244467) B44244467
theorem B19664207 : Blo 2045435 19664207 := bstep (se 1 (by rfl) ⟨14748155, by rfl⟩ : syracuseStep 19664207 = 29496311) B29496311
theorem B13109471 : Blo 2045435 13109471 := bstep (se 1 (by rfl) ⟨9832103, by rfl⟩ : syracuseStep 13109471 = 19664207) B19664207
theorem B8739647 : Blo 2045435 8739647 := bstep (se 1 (by rfl) ⟨6554735, by rfl⟩ : syracuseStep 8739647 = 13109471) B13109471
theorem B5826431 : Blo 2045435 5826431 := bstep (se 1 (by rfl) ⟨4369823, by rfl⟩ : syracuseStep 5826431 = 8739647) B8739647
theorem B3884287 : Blo 2045435 3884287 := bstep (se 1 (by rfl) ⟨2913215, by rfl⟩ : syracuseStep 3884287 = 5826431) B5826431
theorem B5179049 : Blo 2045435 5179049 := bstep (se 2 (by rfl) ⟨1942143, by rfl⟩ : syracuseStep 5179049 = 3884287) B3884287
theorem B3452699 : Blo 2045435 3452699 := bstep (se 1 (by rfl) ⟨2589524, by rfl⟩ : syracuseStep 3452699 = 5179049) B5179049
theorem B2301799 : Blo 2045435 2301799 := bstep (se 1 (by rfl) ⟨1726349, by rfl⟩ : syracuseStep 2301799 = 3452699) B3452699
theorem B3069065 : Blo 2045435 3069065 := bstep (se 2 (by rfl) ⟨1150899, by rfl⟩ : syracuseStep 3069065 = 2301799) B2301799
theorem B2046043 : Blo 2045435 2046043 := bstep (se 1 (by rfl) ⟨1534532, by rfl⟩ : syracuseStep 2046043 = 3069065) B3069065
theorem B10358117 : Blo 2045435 10358117 := bbase (se 4 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 10358117 = 1942147) (by norm_num)
theorem B6905411 : Blo 2045435 6905411 := bstep (se 1 (by rfl) ⟨5179058, by rfl⟩ : syracuseStep 6905411 = 10358117) B10358117
theorem B4603607 : Blo 2045435 4603607 := bstep (se 1 (by rfl) ⟨3452705, by rfl⟩ : syracuseStep 4603607 = 6905411) B6905411
theorem B3069071 : Blo 2045435 3069071 := bstep (se 1 (by rfl) ⟨2301803, by rfl⟩ : syracuseStep 3069071 = 4603607) B4603607
theorem B2046047 : Blo 2045435 2046047 := bstep (se 1 (by rfl) ⟨1534535, by rfl⟩ : syracuseStep 2046047 = 3069071) B3069071
theorem B3069077 : Blo 2045435 3069077 := bbase (se 6 (by rfl) ⟨71931, by rfl⟩ : syracuseStep 3069077 = 143863) (by norm_num)
theorem B2046051 : Blo 2045435 2046051 := bstep (se 1 (by rfl) ⟨1534538, by rfl⟩ : syracuseStep 2046051 = 3069077) B3069077
theorem B6554773 : Blo 2045435 6554773 := bbase (se 6 (by rfl) ⟨153627, by rfl⟩ : syracuseStep 6554773 = 307255) (by norm_num)
theorem B8739697 : Blo 2045435 8739697 := bstep (se 2 (by rfl) ⟨3277386, by rfl⟩ : syracuseStep 8739697 = 6554773) B6554773
theorem B11652929 : Blo 2045435 11652929 := bstep (se 2 (by rfl) ⟨4369848, by rfl⟩ : syracuseStep 11652929 = 8739697) B8739697
theorem B7768619 : Blo 2045435 7768619 := bstep (se 1 (by rfl) ⟨5826464, by rfl⟩ : syracuseStep 7768619 = 11652929) B11652929
theorem B5179079 : Blo 2045435 5179079 := bstep (se 1 (by rfl) ⟨3884309, by rfl⟩ : syracuseStep 5179079 = 7768619) B7768619
theorem B3452719 : Blo 2045435 3452719 := bstep (se 1 (by rfl) ⟨2589539, by rfl⟩ : syracuseStep 3452719 = 5179079) B5179079
theorem B4603625 : Blo 2045435 4603625 := bstep (se 2 (by rfl) ⟨1726359, by rfl⟩ : syracuseStep 4603625 = 3452719) B3452719
theorem B3069083 : Blo 2045435 3069083 := bstep (se 1 (by rfl) ⟨2301812, by rfl⟩ : syracuseStep 3069083 = 4603625) B4603625
theorem B2046055 : Blo 2045435 2046055 := bstep (se 1 (by rfl) ⟨1534541, by rfl⟩ : syracuseStep 2046055 = 3069083) B3069083
theorem B2301817 : Blo 2045435 2301817 := bbase (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) (by norm_num)
theorem B3069089 : Blo 2045435 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B2046059 : Blo 2045435 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B7374149 : Blo 2045435 7374149 := bbase (se 4 (by rfl) ⟨691326, by rfl⟩ : syracuseStep 7374149 = 1382653) (by norm_num)
theorem B4916099 : Blo 2045435 4916099 := bstep (se 1 (by rfl) ⟨3687074, by rfl⟩ : syracuseStep 4916099 = 7374149) B7374149
theorem B13109597 : Blo 2045435 13109597 := bstep (se 3 (by rfl) ⟨2458049, by rfl⟩ : syracuseStep 13109597 = 4916099) B4916099
theorem B8739731 : Blo 2045435 8739731 := bstep (se 1 (by rfl) ⟨6554798, by rfl⟩ : syracuseStep 8739731 = 13109597) B13109597
theorem B5826487 : Blo 2045435 5826487 := bstep (se 1 (by rfl) ⟨4369865, by rfl⟩ : syracuseStep 5826487 = 8739731) B8739731
theorem B7768649 : Blo 2045435 7768649 := bstep (se 2 (by rfl) ⟨2913243, by rfl⟩ : syracuseStep 7768649 = 5826487) B5826487
theorem B5179099 : Blo 2045435 5179099 := bstep (se 1 (by rfl) ⟨3884324, by rfl⟩ : syracuseStep 5179099 = 7768649) B7768649
theorem B6905465 : Blo 2045435 6905465 := bstep (se 2 (by rfl) ⟨2589549, by rfl⟩ : syracuseStep 6905465 = 5179099) B5179099
theorem B4603643 : Blo 2045435 4603643 := bstep (se 1 (by rfl) ⟨3452732, by rfl⟩ : syracuseStep 4603643 = 6905465) B6905465
theorem B3069095 : Blo 2045435 3069095 := bstep (se 1 (by rfl) ⟨2301821, by rfl⟩ : syracuseStep 3069095 = 4603643) B4603643
theorem B2046063 : Blo 2045435 2046063 := bstep (se 1 (by rfl) ⟨1534547, by rfl⟩ : syracuseStep 2046063 = 3069095) B3069095
theorem B3069101 : Blo 2045435 3069101 := bbase (se 3 (by rfl) ⟨575456, by rfl⟩ : syracuseStep 3069101 = 1150913) (by norm_num)
theorem B2046067 : Blo 2045435 2046067 := bstep (se 1 (by rfl) ⟨1534550, by rfl⟩ : syracuseStep 2046067 = 3069101) B3069101
theorem B4603661 : Blo 2045435 4603661 := bbase (se 3 (by rfl) ⟨863186, by rfl⟩ : syracuseStep 4603661 = 1726373) (by norm_num)
theorem B3069107 : Blo 2045435 3069107 := bstep (se 1 (by rfl) ⟨2301830, by rfl⟩ : syracuseStep 3069107 = 4603661) B4603661
theorem B2046071 : Blo 2045435 2046071 := bstep (se 1 (by rfl) ⟨1534553, by rfl⟩ : syracuseStep 2046071 = 3069107) B3069107
theorem B2589565 : Blo 2045435 2589565 := bbase (se 3 (by rfl) ⟨485543, by rfl⟩ : syracuseStep 2589565 = 971087) (by norm_num)
theorem B3452753 : Blo 2045435 3452753 := bstep (se 2 (by rfl) ⟨1294782, by rfl⟩ : syracuseStep 3452753 = 2589565) B2589565
theorem B2301835 : Blo 2045435 2301835 := bstep (se 1 (by rfl) ⟨1726376, by rfl⟩ : syracuseStep 2301835 = 3452753) B3452753
theorem B3069113 : Blo 2045435 3069113 := bstep (se 2 (by rfl) ⟨1150917, by rfl⟩ : syracuseStep 3069113 = 2301835) B2301835
theorem B2046075 : Blo 2045435 2046075 := bstep (se 1 (by rfl) ⟨1534556, by rfl⟩ : syracuseStep 2046075 = 3069113) B3069113
theorem B5321429 : Blo 2045435 5321429 := bbase (se 7 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 5321429 = 124721) (by norm_num)
theorem B3547619 : Blo 2045435 3547619 := bstep (se 1 (by rfl) ⟨2660714, by rfl⟩ : syracuseStep 3547619 = 5321429) B5321429
theorem B2365079 : Blo 2045435 2365079 := bstep (se 1 (by rfl) ⟨1773809, by rfl⟩ : syracuseStep 2365079 = 3547619) B3547619
theorem B6306877 : Blo 2045435 6306877 := bstep (se 3 (by rfl) ⟨1182539, by rfl⟩ : syracuseStep 6306877 = 2365079) B2365079
theorem B8409169 : Blo 2045435 8409169 := bstep (se 2 (by rfl) ⟨3153438, by rfl⟩ : syracuseStep 8409169 = 6306877) B6306877
theorem B11212225 : Blo 2045435 11212225 := bstep (se 2 (by rfl) ⟨4204584, by rfl⟩ : syracuseStep 11212225 = 8409169) B8409169
theorem B59798533 : Blo 2045435 59798533 := bstep (se 4 (by rfl) ⟨5606112, by rfl⟩ : syracuseStep 59798533 = 11212225) B11212225
theorem B79731377 : Blo 2045435 79731377 := bstep (se 2 (by rfl) ⟨29899266, by rfl⟩ : syracuseStep 79731377 = 59798533) B59798533
theorem B53154251 : Blo 2045435 53154251 := bstep (se 1 (by rfl) ⟨39865688, by rfl⟩ : syracuseStep 53154251 = 79731377) B79731377
theorem B35436167 : Blo 2045435 35436167 := bstep (se 1 (by rfl) ⟨26577125, by rfl⟩ : syracuseStep 35436167 = 53154251) B53154251
theorem B23624111 : Blo 2045435 23624111 := bstep (se 1 (by rfl) ⟨17718083, by rfl⟩ : syracuseStep 23624111 = 35436167) B35436167
theorem B15749407 : Blo 2045435 15749407 := bstep (se 1 (by rfl) ⟨11812055, by rfl⟩ : syracuseStep 15749407 = 23624111) B23624111
theorem B20999209 : Blo 2045435 20999209 := bstep (se 2 (by rfl) ⟨7874703, by rfl⟩ : syracuseStep 20999209 = 15749407) B15749407
theorem B27998945 : Blo 2045435 27998945 := bstep (se 2 (by rfl) ⟨10499604, by rfl⟩ : syracuseStep 27998945 = 20999209) B20999209
theorem B18665963 : Blo 2045435 18665963 := bstep (se 1 (by rfl) ⟨13999472, by rfl⟩ : syracuseStep 18665963 = 27998945) B27998945
theorem B12443975 : Blo 2045435 12443975 := bstep (se 1 (by rfl) ⟨9332981, by rfl⟩ : syracuseStep 12443975 = 18665963) B18665963
theorem B8295983 : Blo 2045435 8295983 := bstep (se 1 (by rfl) ⟨6221987, by rfl⟩ : syracuseStep 8295983 = 12443975) B12443975
theorem B5530655 : Blo 2045435 5530655 := bstep (se 1 (by rfl) ⟨4147991, by rfl⟩ : syracuseStep 5530655 = 8295983) B8295983
theorem B3687103 : Blo 2045435 3687103 := bstep (se 1 (by rfl) ⟨2765327, by rfl⟩ : syracuseStep 3687103 = 5530655) B5530655
theorem B4916137 : Blo 2045435 4916137 := bstep (se 2 (by rfl) ⟨1843551, by rfl⟩ : syracuseStep 4916137 = 3687103) B3687103
theorem B6554849 : Blo 2045435 6554849 := bstep (se 2 (by rfl) ⟨2458068, by rfl⟩ : syracuseStep 6554849 = 4916137) B4916137
theorem B17479597 : Blo 2045435 17479597 := bstep (se 3 (by rfl) ⟨3277424, by rfl⟩ : syracuseStep 17479597 = 6554849) B6554849
theorem B23306129 : Blo 2045435 23306129 := bstep (se 2 (by rfl) ⟨8739798, by rfl⟩ : syracuseStep 23306129 = 17479597) B17479597
theorem B15537419 : Blo 2045435 15537419 := bstep (se 1 (by rfl) ⟨11653064, by rfl⟩ : syracuseStep 15537419 = 23306129) B23306129
theorem B10358279 : Blo 2045435 10358279 := bstep (se 1 (by rfl) ⟨7768709, by rfl⟩ : syracuseStep 10358279 = 15537419) B15537419
theorem B6905519 : Blo 2045435 6905519 := bstep (se 1 (by rfl) ⟨5179139, by rfl⟩ : syracuseStep 6905519 = 10358279) B10358279
theorem B4603679 : Blo 2045435 4603679 := bstep (se 1 (by rfl) ⟨3452759, by rfl⟩ : syracuseStep 4603679 = 6905519) B6905519
theorem B3069119 : Blo 2045435 3069119 := bstep (se 1 (by rfl) ⟨2301839, by rfl⟩ : syracuseStep 3069119 = 4603679) B4603679
theorem B2046079 : Blo 2045435 2046079 := bstep (se 1 (by rfl) ⟨1534559, by rfl⟩ : syracuseStep 2046079 = 3069119) B3069119
theorem B3069125 : Blo 2045435 3069125 := bbase (se 4 (by rfl) ⟨287730, by rfl⟩ : syracuseStep 3069125 = 575461) (by norm_num)
theorem B2046083 : Blo 2045435 2046083 := bstep (se 1 (by rfl) ⟨1534562, by rfl⟩ : syracuseStep 2046083 = 3069125) B3069125
theorem B3452773 : Blo 2045435 3452773 := bbase (se 4 (by rfl) ⟨323697, by rfl⟩ : syracuseStep 3452773 = 647395) (by norm_num)
theorem B4603697 : Blo 2045435 4603697 := bstep (se 2 (by rfl) ⟨1726386, by rfl⟩ : syracuseStep 4603697 = 3452773) B3452773
theorem B3069131 : Blo 2045435 3069131 := bstep (se 1 (by rfl) ⟨2301848, by rfl⟩ : syracuseStep 3069131 = 4603697) B4603697
theorem B2046087 : Blo 2045435 2046087 := bstep (se 1 (by rfl) ⟨1534565, by rfl⟩ : syracuseStep 2046087 = 3069131) B3069131
theorem B2301853 : Blo 2045435 2301853 := bbase (se 3 (by rfl) ⟨431597, by rfl⟩ : syracuseStep 2301853 = 863195) (by norm_num)
theorem B3069137 : Blo 2045435 3069137 := bstep (se 2 (by rfl) ⟨1150926, by rfl⟩ : syracuseStep 3069137 = 2301853) B2301853
theorem B2046091 : Blo 2045435 2046091 := bstep (se 1 (by rfl) ⟨1534568, by rfl⟩ : syracuseStep 2046091 = 3069137) B3069137
theorem B6905573 : Blo 2045435 6905573 := bbase (se 4 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 6905573 = 1294795) (by norm_num)
theorem B4603715 : Blo 2045435 4603715 := bstep (se 1 (by rfl) ⟨3452786, by rfl⟩ : syracuseStep 4603715 = 6905573) B6905573
theorem B3069143 : Blo 2045435 3069143 := bstep (se 1 (by rfl) ⟨2301857, by rfl⟩ : syracuseStep 3069143 = 4603715) B4603715
theorem B2046095 : Blo 2045435 2046095 := bstep (se 1 (by rfl) ⟨1534571, by rfl⟩ : syracuseStep 2046095 = 3069143) B3069143
theorem B3069149 : Blo 2045435 3069149 := bbase (se 3 (by rfl) ⟨575465, by rfl⟩ : syracuseStep 3069149 = 1150931) (by norm_num)
theorem B2046099 : Blo 2045435 2046099 := bstep (se 1 (by rfl) ⟨1534574, by rfl⟩ : syracuseStep 2046099 = 3069149) B3069149
theorem B4603733 : Blo 2045435 4603733 := bbase (se 9 (by rfl) ⟨13487, by rfl⟩ : syracuseStep 4603733 = 26975) (by norm_num)
theorem B3069155 : Blo 2045435 3069155 := bstep (se 1 (by rfl) ⟨2301866, by rfl⟩ : syracuseStep 3069155 = 4603733) B4603733
theorem B2046103 : Blo 2045435 2046103 := bstep (se 1 (by rfl) ⟨1534577, by rfl⟩ : syracuseStep 2046103 = 3069155) B3069155
theorem B5826613 : Blo 2045435 5826613 := bbase (se 5 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 5826613 = 546245) (by norm_num)
theorem B7768817 : Blo 2045435 7768817 := bstep (se 2 (by rfl) ⟨2913306, by rfl⟩ : syracuseStep 7768817 = 5826613) B5826613
theorem B5179211 : Blo 2045435 5179211 := bstep (se 1 (by rfl) ⟨3884408, by rfl⟩ : syracuseStep 5179211 = 7768817) B7768817
theorem B3452807 : Blo 2045435 3452807 := bstep (se 1 (by rfl) ⟨2589605, by rfl⟩ : syracuseStep 3452807 = 5179211) B5179211
theorem B2301871 : Blo 2045435 2301871 := bstep (se 1 (by rfl) ⟨1726403, by rfl⟩ : syracuseStep 2301871 = 3452807) B3452807
theorem B3069161 : Blo 2045435 3069161 := bstep (se 2 (by rfl) ⟨1150935, by rfl⟩ : syracuseStep 3069161 = 2301871) B2301871
theorem B2046107 : Blo 2045435 2046107 := bstep (se 1 (by rfl) ⟨1534580, by rfl⟩ : syracuseStep 2046107 = 3069161) B3069161
theorem B9333125 : Blo 2045435 9333125 := bbase (se 4 (by rfl) ⟨874980, by rfl⟩ : syracuseStep 9333125 = 1749961) (by norm_num)
theorem B99553333 : Blo 2045435 99553333 := bstep (se 5 (by rfl) ⟨4666562, by rfl⟩ : syracuseStep 99553333 = 9333125) B9333125
theorem B132737777 : Blo 2045435 132737777 := bstep (se 2 (by rfl) ⟨49776666, by rfl⟩ : syracuseStep 132737777 = 99553333) B99553333
theorem B88491851 : Blo 2045435 88491851 := bstep (se 1 (by rfl) ⟨66368888, by rfl⟩ : syracuseStep 88491851 = 132737777) B132737777
theorem B58994567 : Blo 2045435 58994567 := bstep (se 1 (by rfl) ⟨44245925, by rfl⟩ : syracuseStep 58994567 = 88491851) B88491851
theorem B39329711 : Blo 2045435 39329711 := bstep (se 1 (by rfl) ⟨29497283, by rfl⟩ : syracuseStep 39329711 = 58994567) B58994567
theorem B26219807 : Blo 2045435 26219807 := bstep (se 1 (by rfl) ⟨19664855, by rfl⟩ : syracuseStep 26219807 = 39329711) B39329711
theorem B17479871 : Blo 2045435 17479871 := bstep (se 1 (by rfl) ⟨13109903, by rfl⟩ : syracuseStep 17479871 = 26219807) B26219807
theorem B11653247 : Blo 2045435 11653247 := bstep (se 1 (by rfl) ⟨8739935, by rfl⟩ : syracuseStep 11653247 = 17479871) B17479871
theorem B7768831 : Blo 2045435 7768831 := bstep (se 1 (by rfl) ⟨5826623, by rfl⟩ : syracuseStep 7768831 = 11653247) B11653247
theorem B10358441 : Blo 2045435 10358441 := bstep (se 2 (by rfl) ⟨3884415, by rfl⟩ : syracuseStep 10358441 = 7768831) B7768831
theorem B6905627 : Blo 2045435 6905627 := bstep (se 1 (by rfl) ⟨5179220, by rfl⟩ : syracuseStep 6905627 = 10358441) B10358441
theorem B4603751 : Blo 2045435 4603751 := bstep (se 1 (by rfl) ⟨3452813, by rfl⟩ : syracuseStep 4603751 = 6905627) B6905627
theorem B3069167 : Blo 2045435 3069167 := bstep (se 1 (by rfl) ⟨2301875, by rfl⟩ : syracuseStep 3069167 = 4603751) B4603751
theorem B2046111 : Blo 2045435 2046111 := bstep (se 1 (by rfl) ⟨1534583, by rfl⟩ : syracuseStep 2046111 = 3069167) B3069167
theorem B3069173 : Blo 2045435 3069173 := bbase (se 5 (by rfl) ⟨143867, by rfl⟩ : syracuseStep 3069173 = 287735) (by norm_num)
theorem B2046115 : Blo 2045435 2046115 := bstep (se 1 (by rfl) ⟨1534586, by rfl⟩ : syracuseStep 2046115 = 3069173) B3069173
theorem B2458117 : Blo 2045435 2458117 := bbase (se 4 (by rfl) ⟨230448, by rfl⟩ : syracuseStep 2458117 = 460897) (by norm_num)
theorem B13109957 : Blo 2045435 13109957 := bstep (se 4 (by rfl) ⟨1229058, by rfl⟩ : syracuseStep 13109957 = 2458117) B2458117
theorem B8739971 : Blo 2045435 8739971 := bstep (se 1 (by rfl) ⟨6554978, by rfl⟩ : syracuseStep 8739971 = 13109957) B13109957
theorem B5826647 : Blo 2045435 5826647 := bstep (se 1 (by rfl) ⟨4369985, by rfl⟩ : syracuseStep 5826647 = 8739971) B8739971
theorem B3884431 : Blo 2045435 3884431 := bstep (se 1 (by rfl) ⟨2913323, by rfl⟩ : syracuseStep 3884431 = 5826647) B5826647
theorem B5179241 : Blo 2045435 5179241 := bstep (se 2 (by rfl) ⟨1942215, by rfl⟩ : syracuseStep 5179241 = 3884431) B3884431
theorem B3452827 : Blo 2045435 3452827 := bstep (se 1 (by rfl) ⟨2589620, by rfl⟩ : syracuseStep 3452827 = 5179241) B5179241
theorem B4603769 : Blo 2045435 4603769 := bstep (se 2 (by rfl) ⟨1726413, by rfl⟩ : syracuseStep 4603769 = 3452827) B3452827
theorem B3069179 : Blo 2045435 3069179 := bstep (se 1 (by rfl) ⟨2301884, by rfl⟩ : syracuseStep 3069179 = 4603769) B4603769
theorem B2046119 : Blo 2045435 2046119 := bstep (se 1 (by rfl) ⟨1534589, by rfl⟩ : syracuseStep 2046119 = 3069179) B3069179
theorem B2301889 : Blo 2045435 2301889 := bbase (se 2 (by rfl) ⟨863208, by rfl⟩ : syracuseStep 2301889 = 1726417) (by norm_num)
theorem B3069185 : Blo 2045435 3069185 := bstep (se 2 (by rfl) ⟨1150944, by rfl⟩ : syracuseStep 3069185 = 2301889) B2301889
theorem B2046123 : Blo 2045435 2046123 := bstep (se 1 (by rfl) ⟨1534592, by rfl⟩ : syracuseStep 2046123 = 3069185) B3069185
theorem B5179261 : Blo 2045435 5179261 := bbase (se 3 (by rfl) ⟨971111, by rfl⟩ : syracuseStep 5179261 = 1942223) (by norm_num)
theorem B6905681 : Blo 2045435 6905681 := bstep (se 2 (by rfl) ⟨2589630, by rfl⟩ : syracuseStep 6905681 = 5179261) B5179261
theorem B4603787 : Blo 2045435 4603787 := bstep (se 1 (by rfl) ⟨3452840, by rfl⟩ : syracuseStep 4603787 = 6905681) B6905681
theorem B3069191 : Blo 2045435 3069191 := bstep (se 1 (by rfl) ⟨2301893, by rfl⟩ : syracuseStep 3069191 = 4603787) B4603787
theorem B2046127 : Blo 2045435 2046127 := bstep (se 1 (by rfl) ⟨1534595, by rfl⟩ : syracuseStep 2046127 = 3069191) B3069191
theorem B3069197 : Blo 2045435 3069197 := bbase (se 3 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 3069197 = 1150949) (by norm_num)
theorem B2046131 : Blo 2045435 2046131 := bstep (se 1 (by rfl) ⟨1534598, by rfl⟩ : syracuseStep 2046131 = 3069197) B3069197
theorem B4603805 : Blo 2045435 4603805 := bbase (se 3 (by rfl) ⟨863213, by rfl⟩ : syracuseStep 4603805 = 1726427) (by norm_num)
theorem B3069203 : Blo 2045435 3069203 := bstep (se 1 (by rfl) ⟨2301902, by rfl⟩ : syracuseStep 3069203 = 4603805) B4603805
theorem B2046135 : Blo 2045435 2046135 := bstep (se 1 (by rfl) ⟨1534601, by rfl⟩ : syracuseStep 2046135 = 3069203) B3069203
theorem B3452861 : Blo 2045435 3452861 := bbase (se 3 (by rfl) ⟨647411, by rfl⟩ : syracuseStep 3452861 = 1294823) (by norm_num)
theorem B2301907 : Blo 2045435 2301907 := bstep (se 1 (by rfl) ⟨1726430, by rfl⟩ : syracuseStep 2301907 = 3452861) B3452861
theorem B3069209 : Blo 2045435 3069209 := bstep (se 2 (by rfl) ⟨1150953, by rfl⟩ : syracuseStep 3069209 = 2301907) B2301907
theorem B2046139 : Blo 2045435 2046139 := bstep (se 1 (by rfl) ⟨1534604, by rfl⟩ : syracuseStep 2046139 = 3069209) B3069209
theorem B11653429 : Blo 2045435 11653429 := bbase (se 5 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 11653429 = 1092509) (by norm_num)
theorem B15537905 : Blo 2045435 15537905 := bstep (se 2 (by rfl) ⟨5826714, by rfl⟩ : syracuseStep 15537905 = 11653429) B11653429
theorem B10358603 : Blo 2045435 10358603 := bstep (se 1 (by rfl) ⟨7768952, by rfl⟩ : syracuseStep 10358603 = 15537905) B15537905
theorem B6905735 : Blo 2045435 6905735 := bstep (se 1 (by rfl) ⟨5179301, by rfl⟩ : syracuseStep 6905735 = 10358603) B10358603
theorem B4603823 : Blo 2045435 4603823 := bstep (se 1 (by rfl) ⟨3452867, by rfl⟩ : syracuseStep 4603823 = 6905735) B6905735
theorem B3069215 : Blo 2045435 3069215 := bstep (se 1 (by rfl) ⟨2301911, by rfl⟩ : syracuseStep 3069215 = 4603823) B4603823
theorem B2046143 : Blo 2045435 2046143 := bstep (se 1 (by rfl) ⟨1534607, by rfl⟩ : syracuseStep 2046143 = 3069215) B3069215
theorem B3069221 : Blo 2045435 3069221 := bbase (se 4 (by rfl) ⟨287739, by rfl⟩ : syracuseStep 3069221 = 575479) (by norm_num)
theorem B2046147 : Blo 2045435 2046147 := bstep (se 1 (by rfl) ⟨1534610, by rfl⟩ : syracuseStep 2046147 = 3069221) B3069221
theorem B2589661 : Blo 2045435 2589661 := bbase (se 3 (by rfl) ⟨485561, by rfl⟩ : syracuseStep 2589661 = 971123) (by norm_num)
theorem B3452881 : Blo 2045435 3452881 := bstep (se 2 (by rfl) ⟨1294830, by rfl⟩ : syracuseStep 3452881 = 2589661) B2589661
theorem B4603841 : Blo 2045435 4603841 := bstep (se 2 (by rfl) ⟨1726440, by rfl⟩ : syracuseStep 4603841 = 3452881) B3452881
theorem B3069227 : Blo 2045435 3069227 := bstep (se 1 (by rfl) ⟨2301920, by rfl⟩ : syracuseStep 3069227 = 4603841) B4603841
theorem B2046151 : Blo 2045435 2046151 := bstep (se 1 (by rfl) ⟨1534613, by rfl⟩ : syracuseStep 2046151 = 3069227) B3069227
theorem B2301925 : Blo 2045435 2301925 := bbase (se 4 (by rfl) ⟨215805, by rfl⟩ : syracuseStep 2301925 = 431611) (by norm_num)
theorem B3069233 : Blo 2045435 3069233 := bstep (se 2 (by rfl) ⟨1150962, by rfl⟩ : syracuseStep 3069233 = 2301925) B2301925
theorem B2046155 : Blo 2045435 2046155 := bstep (se 1 (by rfl) ⟨1534616, by rfl⟩ : syracuseStep 2046155 = 3069233) B3069233
theorem B9832661 : Blo 2045435 9832661 := bbase (se 7 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 9832661 = 230453) (by norm_num)
theorem B6555107 : Blo 2045435 6555107 := bstep (se 1 (by rfl) ⟨4916330, by rfl⟩ : syracuseStep 6555107 = 9832661) B9832661
theorem B4370071 : Blo 2045435 4370071 := bstep (se 1 (by rfl) ⟨3277553, by rfl⟩ : syracuseStep 4370071 = 6555107) B6555107
theorem B5826761 : Blo 2045435 5826761 := bstep (se 2 (by rfl) ⟨2185035, by rfl⟩ : syracuseStep 5826761 = 4370071) B4370071
theorem B3884507 : Blo 2045435 3884507 := bstep (se 1 (by rfl) ⟨2913380, by rfl⟩ : syracuseStep 3884507 = 5826761) B5826761
theorem B2589671 : Blo 2045435 2589671 := bstep (se 1 (by rfl) ⟨1942253, by rfl⟩ : syracuseStep 2589671 = 3884507) B3884507
theorem B6905789 : Blo 2045435 6905789 := bstep (se 3 (by rfl) ⟨1294835, by rfl⟩ : syracuseStep 6905789 = 2589671) B2589671
theorem B4603859 : Blo 2045435 4603859 := bstep (se 1 (by rfl) ⟨3452894, by rfl⟩ : syracuseStep 4603859 = 6905789) B6905789
theorem B3069239 : Blo 2045435 3069239 := bstep (se 1 (by rfl) ⟨2301929, by rfl⟩ : syracuseStep 3069239 = 4603859) B4603859
theorem B2046159 : Blo 2045435 2046159 := bstep (se 1 (by rfl) ⟨1534619, by rfl⟩ : syracuseStep 2046159 = 3069239) B3069239
theorem B3069245 : Blo 2045435 3069245 := bbase (se 3 (by rfl) ⟨575483, by rfl⟩ : syracuseStep 3069245 = 1150967) (by norm_num)
theorem B2046163 : Blo 2045435 2046163 := bstep (se 1 (by rfl) ⟨1534622, by rfl⟩ : syracuseStep 2046163 = 3069245) B3069245
theorem B4603877 : Blo 2045435 4603877 := bbase (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) (by norm_num)
theorem B3069251 : Blo 2045435 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B2046167 : Blo 2045435 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B5179373 : Blo 2045435 5179373 := bbase (se 3 (by rfl) ⟨971132, by rfl⟩ : syracuseStep 5179373 = 1942265) (by norm_num)
theorem B3452915 : Blo 2045435 3452915 := bstep (se 1 (by rfl) ⟨2589686, by rfl⟩ : syracuseStep 3452915 = 5179373) B5179373
theorem B2301943 : Blo 2045435 2301943 := bstep (se 1 (by rfl) ⟨1726457, by rfl⟩ : syracuseStep 2301943 = 3452915) B3452915
theorem B3069257 : Blo 2045435 3069257 := bstep (se 2 (by rfl) ⟨1150971, by rfl⟩ : syracuseStep 3069257 = 2301943) B2301943
theorem B2046171 : Blo 2045435 2046171 := bstep (se 1 (by rfl) ⟨1534628, by rfl⟩ : syracuseStep 2046171 = 3069257) B3069257
theorem B3687277 : Blo 2045435 3687277 := bbase (se 3 (by rfl) ⟨691364, by rfl⟩ : syracuseStep 3687277 = 1382729) (by norm_num)
theorem B4916369 : Blo 2045435 4916369 := bstep (se 2 (by rfl) ⟨1843638, by rfl⟩ : syracuseStep 4916369 = 3687277) B3687277
theorem B3277579 : Blo 2045435 3277579 := bstep (se 1 (by rfl) ⟨2458184, by rfl⟩ : syracuseStep 3277579 = 4916369) B4916369
theorem B4370105 : Blo 2045435 4370105 := bstep (se 2 (by rfl) ⟨1638789, by rfl⟩ : syracuseStep 4370105 = 3277579) B3277579
theorem B2913403 : Blo 2045435 2913403 := bstep (se 1 (by rfl) ⟨2185052, by rfl⟩ : syracuseStep 2913403 = 4370105) B4370105
theorem B3884537 : Blo 2045435 3884537 := bstep (se 2 (by rfl) ⟨1456701, by rfl⟩ : syracuseStep 3884537 = 2913403) B2913403
theorem B10358765 : Blo 2045435 10358765 := bstep (se 3 (by rfl) ⟨1942268, by rfl⟩ : syracuseStep 10358765 = 3884537) B3884537
theorem B6905843 : Blo 2045435 6905843 := bstep (se 1 (by rfl) ⟨5179382, by rfl⟩ : syracuseStep 6905843 = 10358765) B10358765
theorem B4603895 : Blo 2045435 4603895 := bstep (se 1 (by rfl) ⟨3452921, by rfl⟩ : syracuseStep 4603895 = 6905843) B6905843
theorem B3069263 : Blo 2045435 3069263 := bstep (se 1 (by rfl) ⟨2301947, by rfl⟩ : syracuseStep 3069263 = 4603895) B4603895
theorem B2046175 : Blo 2045435 2046175 := bstep (se 1 (by rfl) ⟨1534631, by rfl⟩ : syracuseStep 2046175 = 3069263) B3069263
theorem B3069269 : Blo 2045435 3069269 := bbase (se 15 (by rfl) ⟨140, by rfl⟩ : syracuseStep 3069269 = 281) (by norm_num)
theorem B2046179 : Blo 2045435 2046179 := bstep (se 1 (by rfl) ⟨1534634, by rfl⟩ : syracuseStep 2046179 = 3069269) B3069269
theorem B2185061 : Blo 2045435 2185061 := bbase (se 4 (by rfl) ⟨204849, by rfl⟩ : syracuseStep 2185061 = 409699) (by norm_num)
theorem B5826829 : Blo 2045435 5826829 := bstep (se 3 (by rfl) ⟨1092530, by rfl⟩ : syracuseStep 5826829 = 2185061) B2185061
theorem B7769105 : Blo 2045435 7769105 := bstep (se 2 (by rfl) ⟨2913414, by rfl⟩ : syracuseStep 7769105 = 5826829) B5826829
theorem B5179403 : Blo 2045435 5179403 := bstep (se 1 (by rfl) ⟨3884552, by rfl⟩ : syracuseStep 5179403 = 7769105) B7769105
theorem B3452935 : Blo 2045435 3452935 := bstep (se 1 (by rfl) ⟨2589701, by rfl⟩ : syracuseStep 3452935 = 5179403) B5179403
theorem B4603913 : Blo 2045435 4603913 := bstep (se 2 (by rfl) ⟨1726467, by rfl⟩ : syracuseStep 4603913 = 3452935) B3452935
theorem B3069275 : Blo 2045435 3069275 := bstep (se 1 (by rfl) ⟨2301956, by rfl⟩ : syracuseStep 3069275 = 4603913) B4603913
theorem B2046183 : Blo 2045435 2046183 := bstep (se 1 (by rfl) ⟨1534637, by rfl⟩ : syracuseStep 2046183 = 3069275) B3069275
theorem B2301961 : Blo 2045435 2301961 := bbase (se 2 (by rfl) ⟨863235, by rfl⟩ : syracuseStep 2301961 = 1726471) (by norm_num)
theorem B3069281 : Blo 2045435 3069281 := bstep (se 2 (by rfl) ⟨1150980, by rfl⟩ : syracuseStep 3069281 = 2301961) B2301961
theorem B2046187 : Blo 2045435 2046187 := bstep (se 1 (by rfl) ⟨1534640, by rfl⟩ : syracuseStep 2046187 = 3069281) B3069281
theorem B2074109 : Blo 2045435 2074109 := bbase (se 3 (by rfl) ⟨388895, by rfl⟩ : syracuseStep 2074109 = 777791) (by norm_num)
theorem B22123829 : Blo 2045435 22123829 := bstep (se 5 (by rfl) ⟨1037054, by rfl⟩ : syracuseStep 22123829 = 2074109) B2074109
theorem B14749219 : Blo 2045435 14749219 := bstep (se 1 (by rfl) ⟨11061914, by rfl⟩ : syracuseStep 14749219 = 22123829) B22123829
theorem B19665625 : Blo 2045435 19665625 := bstep (se 2 (by rfl) ⟨7374609, by rfl⟩ : syracuseStep 19665625 = 14749219) B14749219
theorem B26220833 : Blo 2045435 26220833 := bstep (se 2 (by rfl) ⟨9832812, by rfl⟩ : syracuseStep 26220833 = 19665625) B19665625
theorem B17480555 : Blo 2045435 17480555 := bstep (se 1 (by rfl) ⟨13110416, by rfl⟩ : syracuseStep 17480555 = 26220833) B26220833
theorem B11653703 : Blo 2045435 11653703 := bstep (se 1 (by rfl) ⟨8740277, by rfl⟩ : syracuseStep 11653703 = 17480555) B17480555
theorem B7769135 : Blo 2045435 7769135 := bstep (se 1 (by rfl) ⟨5826851, by rfl⟩ : syracuseStep 7769135 = 11653703) B11653703
theorem B5179423 : Blo 2045435 5179423 := bstep (se 1 (by rfl) ⟨3884567, by rfl⟩ : syracuseStep 5179423 = 7769135) B7769135
theorem B6905897 : Blo 2045435 6905897 := bstep (se 2 (by rfl) ⟨2589711, by rfl⟩ : syracuseStep 6905897 = 5179423) B5179423
theorem B4603931 : Blo 2045435 4603931 := bstep (se 1 (by rfl) ⟨3452948, by rfl⟩ : syracuseStep 4603931 = 6905897) B6905897
theorem B3069287 : Blo 2045435 3069287 := bstep (se 1 (by rfl) ⟨2301965, by rfl⟩ : syracuseStep 3069287 = 4603931) B4603931
theorem B2046191 : Blo 2045435 2046191 := bstep (se 1 (by rfl) ⟨1534643, by rfl⟩ : syracuseStep 2046191 = 3069287) B3069287
theorem B3069293 : Blo 2045435 3069293 := bbase (se 3 (by rfl) ⟨575492, by rfl⟩ : syracuseStep 3069293 = 1150985) (by norm_num)
theorem B2046195 : Blo 2045435 2046195 := bstep (se 1 (by rfl) ⟨1534646, by rfl⟩ : syracuseStep 2046195 = 3069293) B3069293
theorem B4603949 : Blo 2045435 4603949 := bbase (se 3 (by rfl) ⟨863240, by rfl⟩ : syracuseStep 4603949 = 1726481) (by norm_num)
theorem B3069299 : Blo 2045435 3069299 := bstep (se 1 (by rfl) ⟨2301974, by rfl⟩ : syracuseStep 3069299 = 4603949) B4603949
theorem B2046199 : Blo 2045435 2046199 := bstep (se 1 (by rfl) ⟨1534649, by rfl⟩ : syracuseStep 2046199 = 3069299) B3069299
theorem B4262213 : Blo 2045435 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2841475 : Blo 2045435 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B3788633 : Blo 2045435 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B2525755 : Blo 2045435 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3367673 : Blo 2045435 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2245115 : Blo 2045435 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B5986973 : Blo 2045435 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B15965261 : Blo 2045435 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B10643507 : Blo 2045435 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B7095671 : Blo 2045435 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B4730447 : Blo 2045435 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B12614525 : Blo 2045435 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B8409683 : Blo 2045435 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B5606455 : Blo 2045435 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B7475273 : Blo 2045435 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B4983515 : Blo 2045435 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B3322343 : Blo 2045435 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B8859581 : Blo 2045435 8859581 := bstep (se 3 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 8859581 = 3322343) B3322343
theorem B5906387 : Blo 2045435 5906387 := bstep (se 1 (by rfl) ⟨4429790, by rfl⟩ : syracuseStep 5906387 = 8859581) B8859581
theorem B3937591 : Blo 2045435 3937591 := bstep (se 1 (by rfl) ⟨2953193, by rfl⟩ : syracuseStep 3937591 = 5906387) B5906387
theorem B21000485 : Blo 2045435 21000485 := bstep (se 4 (by rfl) ⟨1968795, by rfl⟩ : syracuseStep 21000485 = 3937591) B3937591
theorem B56001293 : Blo 2045435 56001293 := bstep (se 3 (by rfl) ⟨10500242, by rfl⟩ : syracuseStep 56001293 = 21000485) B21000485
theorem B37334195 : Blo 2045435 37334195 := bstep (se 1 (by rfl) ⟨28000646, by rfl⟩ : syracuseStep 37334195 = 56001293) B56001293
theorem B24889463 : Blo 2045435 24889463 := bstep (se 1 (by rfl) ⟨18667097, by rfl⟩ : syracuseStep 24889463 = 37334195) B37334195
theorem B16592975 : Blo 2045435 16592975 := bstep (se 1 (by rfl) ⟨12444731, by rfl⟩ : syracuseStep 16592975 = 24889463) B24889463
theorem B11061983 : Blo 2045435 11061983 := bstep (se 1 (by rfl) ⟨8296487, by rfl⟩ : syracuseStep 11061983 = 16592975) B16592975
theorem B7374655 : Blo 2045435 7374655 := bstep (se 1 (by rfl) ⟨5530991, by rfl⟩ : syracuseStep 7374655 = 11061983) B11061983
theorem B9832873 : Blo 2045435 9832873 := bstep (se 2 (by rfl) ⟨3687327, by rfl⟩ : syracuseStep 9832873 = 7374655) B7374655
theorem B13110497 : Blo 2045435 13110497 := bstep (se 2 (by rfl) ⟨4916436, by rfl⟩ : syracuseStep 13110497 = 9832873) B9832873
theorem B8740331 : Blo 2045435 8740331 := bstep (se 1 (by rfl) ⟨6555248, by rfl⟩ : syracuseStep 8740331 = 13110497) B13110497
theorem B5826887 : Blo 2045435 5826887 := bstep (se 1 (by rfl) ⟨4370165, by rfl⟩ : syracuseStep 5826887 = 8740331) B8740331
theorem B3884591 : Blo 2045435 3884591 := bstep (se 1 (by rfl) ⟨2913443, by rfl⟩ : syracuseStep 3884591 = 5826887) B5826887
theorem B2589727 : Blo 2045435 2589727 := bstep (se 1 (by rfl) ⟨1942295, by rfl⟩ : syracuseStep 2589727 = 3884591) B3884591
theorem B3452969 : Blo 2045435 3452969 := bstep (se 2 (by rfl) ⟨1294863, by rfl⟩ : syracuseStep 3452969 = 2589727) B2589727
theorem B2301979 : Blo 2045435 2301979 := bstep (se 1 (by rfl) ⟨1726484, by rfl⟩ : syracuseStep 2301979 = 3452969) B3452969
theorem B3069305 : Blo 2045435 3069305 := bstep (se 2 (by rfl) ⟨1150989, by rfl⟩ : syracuseStep 3069305 = 2301979) B2301979
theorem B2046203 : Blo 2045435 2046203 := bstep (se 1 (by rfl) ⟨1534652, by rfl⟩ : syracuseStep 2046203 = 3069305) B3069305
theorem B8296501 : Blo 2045435 8296501 := bbase (se 5 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 8296501 = 777797) (by norm_num)
theorem B11062001 : Blo 2045435 11062001 := bstep (se 2 (by rfl) ⟨4148250, by rfl⟩ : syracuseStep 11062001 = 8296501) B8296501
theorem B7374667 : Blo 2045435 7374667 := bstep (se 1 (by rfl) ⟨5531000, by rfl⟩ : syracuseStep 7374667 = 11062001) B11062001
theorem B9832889 : Blo 2045435 9832889 := bstep (se 2 (by rfl) ⟨3687333, by rfl⟩ : syracuseStep 9832889 = 7374667) B7374667
theorem B6555259 : Blo 2045435 6555259 := bstep (se 1 (by rfl) ⟨4916444, by rfl⟩ : syracuseStep 6555259 = 9832889) B9832889
theorem B34961381 : Blo 2045435 34961381 := bstep (se 4 (by rfl) ⟨3277629, by rfl⟩ : syracuseStep 34961381 = 6555259) B6555259
theorem B23307587 : Blo 2045435 23307587 := bstep (se 1 (by rfl) ⟨17480690, by rfl⟩ : syracuseStep 23307587 = 34961381) B34961381
theorem B15538391 : Blo 2045435 15538391 := bstep (se 1 (by rfl) ⟨11653793, by rfl⟩ : syracuseStep 15538391 = 23307587) B23307587
theorem B10358927 : Blo 2045435 10358927 := bstep (se 1 (by rfl) ⟨7769195, by rfl⟩ : syracuseStep 10358927 = 15538391) B15538391
theorem B6905951 : Blo 2045435 6905951 := bstep (se 1 (by rfl) ⟨5179463, by rfl⟩ : syracuseStep 6905951 = 10358927) B10358927
theorem B4603967 : Blo 2045435 4603967 := bstep (se 1 (by rfl) ⟨3452975, by rfl⟩ : syracuseStep 4603967 = 6905951) B6905951
theorem B3069311 : Blo 2045435 3069311 := bstep (se 1 (by rfl) ⟨2301983, by rfl⟩ : syracuseStep 3069311 = 4603967) B4603967
theorem B2046207 : Blo 2045435 2046207 := bstep (se 1 (by rfl) ⟨1534655, by rfl⟩ : syracuseStep 2046207 = 3069311) B3069311
theorem B3069317 : Blo 2045435 3069317 := bbase (se 4 (by rfl) ⟨287748, by rfl⟩ : syracuseStep 3069317 = 575497) (by norm_num)
theorem B2046211 : Blo 2045435 2046211 := bstep (se 1 (by rfl) ⟨1534658, by rfl⟩ : syracuseStep 2046211 = 3069317) B3069317
theorem B3452989 : Blo 2045435 3452989 := bbase (se 3 (by rfl) ⟨647435, by rfl⟩ : syracuseStep 3452989 = 1294871) (by norm_num)
theorem B4603985 : Blo 2045435 4603985 := bstep (se 2 (by rfl) ⟨1726494, by rfl⟩ : syracuseStep 4603985 = 3452989) B3452989
theorem B3069323 : Blo 2045435 3069323 := bstep (se 1 (by rfl) ⟨2301992, by rfl⟩ : syracuseStep 3069323 = 4603985) B4603985
theorem B2046215 : Blo 2045435 2046215 := bstep (se 1 (by rfl) ⟨1534661, by rfl⟩ : syracuseStep 2046215 = 3069323) B3069323
theorem B2301997 : Blo 2045435 2301997 := bbase (se 3 (by rfl) ⟨431624, by rfl⟩ : syracuseStep 2301997 = 863249) (by norm_num)
theorem B3069329 : Blo 2045435 3069329 := bstep (se 2 (by rfl) ⟨1150998, by rfl⟩ : syracuseStep 3069329 = 2301997) B2301997
theorem B2046219 : Blo 2045435 2046219 := bstep (se 1 (by rfl) ⟨1534664, by rfl⟩ : syracuseStep 2046219 = 3069329) B3069329
theorem B6906005 : Blo 2045435 6906005 := bbase (se 6 (by rfl) ⟨161859, by rfl⟩ : syracuseStep 6906005 = 323719) (by norm_num)
theorem B4604003 : Blo 2045435 4604003 := bstep (se 1 (by rfl) ⟨3453002, by rfl⟩ : syracuseStep 4604003 = 6906005) B6906005
theorem B3069335 : Blo 2045435 3069335 := bstep (se 1 (by rfl) ⟨2302001, by rfl⟩ : syracuseStep 3069335 = 4604003) B4604003
theorem B2046223 : Blo 2045435 2046223 := bstep (se 1 (by rfl) ⟨1534667, by rfl⟩ : syracuseStep 2046223 = 3069335) B3069335
theorem B3069341 : Blo 2045435 3069341 := bbase (se 3 (by rfl) ⟨575501, by rfl⟩ : syracuseStep 3069341 = 1151003) (by norm_num)
theorem B2046227 : Blo 2045435 2046227 := bstep (se 1 (by rfl) ⟨1534670, by rfl⟩ : syracuseStep 2046227 = 3069341) B3069341
theorem B4604021 : Blo 2045435 4604021 := bbase (se 5 (by rfl) ⟨215813, by rfl⟩ : syracuseStep 4604021 = 431627) (by norm_num)
theorem B3069347 : Blo 2045435 3069347 := bstep (se 1 (by rfl) ⟨2302010, by rfl⟩ : syracuseStep 3069347 = 4604021) B4604021
theorem B2046231 : Blo 2045435 2046231 := bstep (se 1 (by rfl) ⟨1534673, by rfl⟩ : syracuseStep 2046231 = 3069347) B3069347
theorem B4148309 : Blo 2045435 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B2765539 : Blo 2045435 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B3687385 : Blo 2045435 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B4916513 : Blo 2045435 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B3277675 : Blo 2045435 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B17480933 : Blo 2045435 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B11653955 : Blo 2045435 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B7769303 : Blo 2045435 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B5179535 : Blo 2045435 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B3453023 : Blo 2045435 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B2302015 : Blo 2045435 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B3069353 : Blo 2045435 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B2046235 : Blo 2045435 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B7769317 : Blo 2045435 7769317 := bbase (se 4 (by rfl) ⟨728373, by rfl⟩ : syracuseStep 7769317 = 1456747) (by norm_num)
theorem B10359089 : Blo 2045435 10359089 := bstep (se 2 (by rfl) ⟨3884658, by rfl⟩ : syracuseStep 10359089 = 7769317) B7769317
theorem B6906059 : Blo 2045435 6906059 := bstep (se 1 (by rfl) ⟨5179544, by rfl⟩ : syracuseStep 6906059 = 10359089) B10359089
theorem B4604039 : Blo 2045435 4604039 := bstep (se 1 (by rfl) ⟨3453029, by rfl⟩ : syracuseStep 4604039 = 6906059) B6906059
theorem B3069359 : Blo 2045435 3069359 := bstep (se 1 (by rfl) ⟨2302019, by rfl⟩ : syracuseStep 3069359 = 4604039) B4604039
theorem B2046239 : Blo 2045435 2046239 := bstep (se 1 (by rfl) ⟨1534679, by rfl⟩ : syracuseStep 2046239 = 3069359) B3069359
theorem B3069365 : Blo 2045435 3069365 := bbase (se 5 (by rfl) ⟨143876, by rfl⟩ : syracuseStep 3069365 = 287753) (by norm_num)
theorem B2046243 : Blo 2045435 2046243 := bstep (se 1 (by rfl) ⟨1534682, by rfl⟩ : syracuseStep 2046243 = 3069365) B3069365
theorem B5179565 : Blo 2045435 5179565 := bbase (se 3 (by rfl) ⟨971168, by rfl⟩ : syracuseStep 5179565 = 1942337) (by norm_num)
theorem B3453043 : Blo 2045435 3453043 := bstep (se 1 (by rfl) ⟨2589782, by rfl⟩ : syracuseStep 3453043 = 5179565) B5179565
theorem B4604057 : Blo 2045435 4604057 := bstep (se 2 (by rfl) ⟨1726521, by rfl⟩ : syracuseStep 4604057 = 3453043) B3453043
theorem B3069371 : Blo 2045435 3069371 := bstep (se 1 (by rfl) ⟨2302028, by rfl⟩ : syracuseStep 3069371 = 4604057) B4604057
theorem B2046247 : Blo 2045435 2046247 := bstep (se 1 (by rfl) ⟨1534685, by rfl⟩ : syracuseStep 2046247 = 3069371) B3069371
theorem B2302033 : Blo 2045435 2302033 := bbase (se 2 (by rfl) ⟨863262, by rfl⟩ : syracuseStep 2302033 = 1726525) (by norm_num)
theorem B3069377 : Blo 2045435 3069377 := bstep (se 2 (by rfl) ⟨1151016, by rfl⟩ : syracuseStep 3069377 = 2302033) B2302033
theorem B2046251 : Blo 2045435 2046251 := bstep (se 1 (by rfl) ⟨1534688, by rfl⟩ : syracuseStep 2046251 = 3069377) B3069377
theorem B2913517 : Blo 2045435 2913517 := bbase (se 3 (by rfl) ⟨546284, by rfl⟩ : syracuseStep 2913517 = 1092569) (by norm_num)
theorem B3884689 : Blo 2045435 3884689 := bstep (se 2 (by rfl) ⟨1456758, by rfl⟩ : syracuseStep 3884689 = 2913517) B2913517
theorem B5179585 : Blo 2045435 5179585 := bstep (se 2 (by rfl) ⟨1942344, by rfl⟩ : syracuseStep 5179585 = 3884689) B3884689
theorem B6906113 : Blo 2045435 6906113 := bstep (se 2 (by rfl) ⟨2589792, by rfl⟩ : syracuseStep 6906113 = 5179585) B5179585
theorem B4604075 : Blo 2045435 4604075 := bstep (se 1 (by rfl) ⟨3453056, by rfl⟩ : syracuseStep 4604075 = 6906113) B6906113
theorem B3069383 : Blo 2045435 3069383 := bstep (se 1 (by rfl) ⟨2302037, by rfl⟩ : syracuseStep 3069383 = 4604075) B4604075
theorem B2046255 : Blo 2045435 2046255 := bstep (se 1 (by rfl) ⟨1534691, by rfl⟩ : syracuseStep 2046255 = 3069383) B3069383
theorem B3069389 : Blo 2045435 3069389 := bbase (se 3 (by rfl) ⟨575510, by rfl⟩ : syracuseStep 3069389 = 1151021) (by norm_num)
theorem B2046259 : Blo 2045435 2046259 := bstep (se 1 (by rfl) ⟨1534694, by rfl⟩ : syracuseStep 2046259 = 3069389) B3069389
theorem B4604093 : Blo 2045435 4604093 := bbase (se 3 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 4604093 = 1726535) (by norm_num)
theorem B3069395 : Blo 2045435 3069395 := bstep (se 1 (by rfl) ⟨2302046, by rfl⟩ : syracuseStep 3069395 = 4604093) B4604093
theorem B2046263 : Blo 2045435 2046263 := bstep (se 1 (by rfl) ⟨1534697, by rfl⟩ : syracuseStep 2046263 = 3069395) B3069395
theorem B3453077 : Blo 2045435 3453077 := bbase (se 6 (by rfl) ⟨80931, by rfl⟩ : syracuseStep 3453077 = 161863) (by norm_num)
theorem B2302051 : Blo 2045435 2302051 := bstep (se 1 (by rfl) ⟨1726538, by rfl⟩ : syracuseStep 2302051 = 3453077) B3453077
theorem B3069401 : Blo 2045435 3069401 := bstep (se 2 (by rfl) ⟨1151025, by rfl⟩ : syracuseStep 3069401 = 2302051) B2302051
theorem B2046267 : Blo 2045435 2046267 := bstep (se 1 (by rfl) ⟨1534700, by rfl⟩ : syracuseStep 2046267 = 3069401) B3069401
theorem B4148381 : Blo 2045435 4148381 := bbase (se 3 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 4148381 = 1555643) (by norm_num)
theorem B2765587 : Blo 2045435 2765587 := bstep (se 1 (by rfl) ⟨2074190, by rfl⟩ : syracuseStep 2765587 = 4148381) B4148381
theorem B3687449 : Blo 2045435 3687449 := bstep (se 2 (by rfl) ⟨1382793, by rfl⟩ : syracuseStep 3687449 = 2765587) B2765587
theorem B9833197 : Blo 2045435 9833197 := bstep (se 3 (by rfl) ⟨1843724, by rfl⟩ : syracuseStep 9833197 = 3687449) B3687449
theorem B13110929 : Blo 2045435 13110929 := bstep (se 2 (by rfl) ⟨4916598, by rfl⟩ : syracuseStep 13110929 = 9833197) B9833197
theorem B8740619 : Blo 2045435 8740619 := bstep (se 1 (by rfl) ⟨6555464, by rfl⟩ : syracuseStep 8740619 = 13110929) B13110929
theorem B5827079 : Blo 2045435 5827079 := bstep (se 1 (by rfl) ⟨4370309, by rfl⟩ : syracuseStep 5827079 = 8740619) B8740619
theorem B15538877 : Blo 2045435 15538877 := bstep (se 3 (by rfl) ⟨2913539, by rfl⟩ : syracuseStep 15538877 = 5827079) B5827079
theorem B10359251 : Blo 2045435 10359251 := bstep (se 1 (by rfl) ⟨7769438, by rfl⟩ : syracuseStep 10359251 = 15538877) B15538877
theorem B6906167 : Blo 2045435 6906167 := bstep (se 1 (by rfl) ⟨5179625, by rfl⟩ : syracuseStep 6906167 = 10359251) B10359251
theorem B4604111 : Blo 2045435 4604111 := bstep (se 1 (by rfl) ⟨3453083, by rfl⟩ : syracuseStep 4604111 = 6906167) B6906167
theorem B3069407 : Blo 2045435 3069407 := bstep (se 1 (by rfl) ⟨2302055, by rfl⟩ : syracuseStep 3069407 = 4604111) B4604111
theorem B2046271 : Blo 2045435 2046271 := bstep (se 1 (by rfl) ⟨1534703, by rfl⟩ : syracuseStep 2046271 = 3069407) B3069407
theorem B3069413 : Blo 2045435 3069413 := bbase (se 4 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 3069413 = 575515) (by norm_num)
theorem B2046275 : Blo 2045435 2046275 := bstep (se 1 (by rfl) ⟨1534706, by rfl⟩ : syracuseStep 2046275 = 3069413) B3069413
theorem B16593589 : Blo 2045435 16593589 := bbase (se 5 (by rfl) ⟨777824, by rfl⟩ : syracuseStep 16593589 = 1555649) (by norm_num)
theorem B22124785 : Blo 2045435 22124785 := bstep (se 2 (by rfl) ⟨8296794, by rfl⟩ : syracuseStep 22124785 = 16593589) B16593589
theorem B29499713 : Blo 2045435 29499713 := bstep (se 2 (by rfl) ⟨11062392, by rfl⟩ : syracuseStep 29499713 = 22124785) B22124785
theorem B19666475 : Blo 2045435 19666475 := bstep (se 1 (by rfl) ⟨14749856, by rfl⟩ : syracuseStep 19666475 = 29499713) B29499713
theorem B13110983 : Blo 2045435 13110983 := bstep (se 1 (by rfl) ⟨9833237, by rfl⟩ : syracuseStep 13110983 = 19666475) B19666475
theorem B8740655 : Blo 2045435 8740655 := bstep (se 1 (by rfl) ⟨6555491, by rfl⟩ : syracuseStep 8740655 = 13110983) B13110983
theorem B5827103 : Blo 2045435 5827103 := bstep (se 1 (by rfl) ⟨4370327, by rfl⟩ : syracuseStep 5827103 = 8740655) B8740655
theorem B3884735 : Blo 2045435 3884735 := bstep (se 1 (by rfl) ⟨2913551, by rfl⟩ : syracuseStep 3884735 = 5827103) B5827103
theorem B2589823 : Blo 2045435 2589823 := bstep (se 1 (by rfl) ⟨1942367, by rfl⟩ : syracuseStep 2589823 = 3884735) B3884735
theorem B3453097 : Blo 2045435 3453097 := bstep (se 2 (by rfl) ⟨1294911, by rfl⟩ : syracuseStep 3453097 = 2589823) B2589823
theorem B4604129 : Blo 2045435 4604129 := bstep (se 2 (by rfl) ⟨1726548, by rfl⟩ : syracuseStep 4604129 = 3453097) B3453097
theorem B3069419 : Blo 2045435 3069419 := bstep (se 1 (by rfl) ⟨2302064, by rfl⟩ : syracuseStep 3069419 = 4604129) B4604129
theorem B2046279 : Blo 2045435 2046279 := bstep (se 1 (by rfl) ⟨1534709, by rfl⟩ : syracuseStep 2046279 = 3069419) B3069419
theorem B2302069 : Blo 2045435 2302069 := bbase (se 5 (by rfl) ⟨107909, by rfl⟩ : syracuseStep 2302069 = 215819) (by norm_num)
theorem B3069425 : Blo 2045435 3069425 := bstep (se 2 (by rfl) ⟨1151034, by rfl⟩ : syracuseStep 3069425 = 2302069) B2302069
theorem B2046283 : Blo 2045435 2046283 := bstep (se 1 (by rfl) ⟨1534712, by rfl⟩ : syracuseStep 2046283 = 3069425) B3069425
theorem B2589833 : Blo 2045435 2589833 := bbase (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) (by norm_num)
theorem B6906221 : Blo 2045435 6906221 := bstep (se 3 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 6906221 = 2589833) B2589833
theorem B4604147 : Blo 2045435 4604147 := bstep (se 1 (by rfl) ⟨3453110, by rfl⟩ : syracuseStep 4604147 = 6906221) B6906221
theorem B3069431 : Blo 2045435 3069431 := bstep (se 1 (by rfl) ⟨2302073, by rfl⟩ : syracuseStep 3069431 = 4604147) B4604147
theorem B2046287 : Blo 2045435 2046287 := bstep (se 1 (by rfl) ⟨1534715, by rfl⟩ : syracuseStep 2046287 = 3069431) B3069431
theorem B3069437 : Blo 2045435 3069437 := bbase (se 3 (by rfl) ⟨575519, by rfl⟩ : syracuseStep 3069437 = 1151039) (by norm_num)
theorem B2046291 : Blo 2045435 2046291 := bstep (se 1 (by rfl) ⟨1534718, by rfl⟩ : syracuseStep 2046291 = 3069437) B3069437
theorem B4604165 : Blo 2045435 4604165 := bbase (se 4 (by rfl) ⟨431640, by rfl⟩ : syracuseStep 4604165 = 863281) (by norm_num)
theorem B3069443 : Blo 2045435 3069443 := bstep (se 1 (by rfl) ⟨2302082, by rfl⟩ : syracuseStep 3069443 = 4604165) B4604165
theorem B2046295 : Blo 2045435 2046295 := bstep (se 1 (by rfl) ⟨1534721, by rfl⟩ : syracuseStep 2046295 = 3069443) B3069443
theorem B3884773 : Blo 2045435 3884773 := bbase (se 4 (by rfl) ⟨364197, by rfl⟩ : syracuseStep 3884773 = 728395) (by norm_num)
theorem B5179697 : Blo 2045435 5179697 := bstep (se 2 (by rfl) ⟨1942386, by rfl⟩ : syracuseStep 5179697 = 3884773) B3884773
theorem B3453131 : Blo 2045435 3453131 := bstep (se 1 (by rfl) ⟨2589848, by rfl⟩ : syracuseStep 3453131 = 5179697) B5179697
theorem B2302087 : Blo 2045435 2302087 := bstep (se 1 (by rfl) ⟨1726565, by rfl⟩ : syracuseStep 2302087 = 3453131) B3453131
theorem B3069449 : Blo 2045435 3069449 := bstep (se 2 (by rfl) ⟨1151043, by rfl⟩ : syracuseStep 3069449 = 2302087) B2302087
theorem B2046299 : Blo 2045435 2046299 := bstep (se 1 (by rfl) ⟨1534724, by rfl⟩ : syracuseStep 2046299 = 3069449) B3069449
theorem B10359413 : Blo 2045435 10359413 := bbase (se 5 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 10359413 = 971195) (by norm_num)
theorem B6906275 : Blo 2045435 6906275 := bstep (se 1 (by rfl) ⟨5179706, by rfl⟩ : syracuseStep 6906275 = 10359413) B10359413
theorem B4604183 : Blo 2045435 4604183 := bstep (se 1 (by rfl) ⟨3453137, by rfl⟩ : syracuseStep 4604183 = 6906275) B6906275
theorem B3069455 : Blo 2045435 3069455 := bstep (se 1 (by rfl) ⟨2302091, by rfl⟩ : syracuseStep 3069455 = 4604183) B4604183
theorem B2046303 : Blo 2045435 2046303 := bstep (se 1 (by rfl) ⟨1534727, by rfl⟩ : syracuseStep 2046303 = 3069455) B3069455
theorem B3069461 : Blo 2045435 3069461 := bbase (se 6 (by rfl) ⟨71940, by rfl⟩ : syracuseStep 3069461 = 143881) (by norm_num)
theorem B2046307 : Blo 2045435 2046307 := bstep (se 1 (by rfl) ⟨1534730, by rfl⟩ : syracuseStep 2046307 = 3069461) B3069461
theorem B4667021 : Blo 2045435 4667021 := bbase (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) (by norm_num)
theorem B3111347 : Blo 2045435 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B2074231 : Blo 2045435 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B11062565 : Blo 2045435 11062565 := bstep (se 4 (by rfl) ⟨1037115, by rfl⟩ : syracuseStep 11062565 = 2074231) B2074231
theorem B7375043 : Blo 2045435 7375043 := bstep (se 1 (by rfl) ⟨5531282, by rfl⟩ : syracuseStep 7375043 = 11062565) B11062565
theorem B4916695 : Blo 2045435 4916695 := bstep (se 1 (by rfl) ⟨3687521, by rfl⟩ : syracuseStep 4916695 = 7375043) B7375043
theorem B6555593 : Blo 2045435 6555593 := bstep (se 2 (by rfl) ⟨2458347, by rfl⟩ : syracuseStep 6555593 = 4916695) B4916695
theorem B17481581 : Blo 2045435 17481581 := bstep (se 3 (by rfl) ⟨3277796, by rfl⟩ : syracuseStep 17481581 = 6555593) B6555593
theorem B11654387 : Blo 2045435 11654387 := bstep (se 1 (by rfl) ⟨8740790, by rfl⟩ : syracuseStep 11654387 = 17481581) B17481581
theorem B7769591 : Blo 2045435 7769591 := bstep (se 1 (by rfl) ⟨5827193, by rfl⟩ : syracuseStep 7769591 = 11654387) B11654387
theorem B5179727 : Blo 2045435 5179727 := bstep (se 1 (by rfl) ⟨3884795, by rfl⟩ : syracuseStep 5179727 = 7769591) B7769591
theorem B3453151 : Blo 2045435 3453151 := bstep (se 1 (by rfl) ⟨2589863, by rfl⟩ : syracuseStep 3453151 = 5179727) B5179727
theorem B4604201 : Blo 2045435 4604201 := bstep (se 2 (by rfl) ⟨1726575, by rfl⟩ : syracuseStep 4604201 = 3453151) B3453151
theorem B3069467 : Blo 2045435 3069467 := bstep (se 1 (by rfl) ⟨2302100, by rfl⟩ : syracuseStep 3069467 = 4604201) B4604201
theorem B2046311 : Blo 2045435 2046311 := bstep (se 1 (by rfl) ⟨1534733, by rfl⟩ : syracuseStep 2046311 = 3069467) B3069467
theorem B2302105 : Blo 2045435 2302105 := bbase (se 2 (by rfl) ⟨863289, by rfl⟩ : syracuseStep 2302105 = 1726579) (by norm_num)
theorem B3069473 : Blo 2045435 3069473 := bstep (se 2 (by rfl) ⟨1151052, by rfl⟩ : syracuseStep 3069473 = 2302105) B2302105
theorem B2046315 : Blo 2045435 2046315 := bstep (se 1 (by rfl) ⟨1534736, by rfl⟩ : syracuseStep 2046315 = 3069473) B3069473
theorem B7769621 : Blo 2045435 7769621 := bbase (se 6 (by rfl) ⟨182100, by rfl⟩ : syracuseStep 7769621 = 364201) (by norm_num)
theorem B5179747 : Blo 2045435 5179747 := bstep (se 1 (by rfl) ⟨3884810, by rfl⟩ : syracuseStep 5179747 = 7769621) B7769621
theorem B6906329 : Blo 2045435 6906329 := bstep (se 2 (by rfl) ⟨2589873, by rfl⟩ : syracuseStep 6906329 = 5179747) B5179747
theorem B4604219 : Blo 2045435 4604219 := bstep (se 1 (by rfl) ⟨3453164, by rfl⟩ : syracuseStep 4604219 = 6906329) B6906329
theorem B3069479 : Blo 2045435 3069479 := bstep (se 1 (by rfl) ⟨2302109, by rfl⟩ : syracuseStep 3069479 = 4604219) B4604219
theorem B2046319 : Blo 2045435 2046319 := bstep (se 1 (by rfl) ⟨1534739, by rfl⟩ : syracuseStep 2046319 = 3069479) B3069479
theorem B3069485 : Blo 2045435 3069485 := bbase (se 3 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 3069485 = 1151057) (by norm_num)
theorem B2046323 : Blo 2045435 2046323 := bstep (se 1 (by rfl) ⟨1534742, by rfl⟩ : syracuseStep 2046323 = 3069485) B3069485
theorem B4604237 : Blo 2045435 4604237 := bbase (se 3 (by rfl) ⟨863294, by rfl⟩ : syracuseStep 4604237 = 1726589) (by norm_num)
theorem B3069491 : Blo 2045435 3069491 := bstep (se 1 (by rfl) ⟨2302118, by rfl⟩ : syracuseStep 3069491 = 4604237) B4604237
theorem B2046327 : Blo 2045435 2046327 := bstep (se 1 (by rfl) ⟨1534745, by rfl⟩ : syracuseStep 2046327 = 3069491) B3069491
theorem B2589889 : Blo 2045435 2589889 := bbase (se 2 (by rfl) ⟨971208, by rfl⟩ : syracuseStep 2589889 = 1942417) (by norm_num)
theorem B3453185 : Blo 2045435 3453185 := bstep (se 2 (by rfl) ⟨1294944, by rfl⟩ : syracuseStep 3453185 = 2589889) B2589889
theorem B2302123 : Blo 2045435 2302123 := bstep (se 1 (by rfl) ⟨1726592, by rfl⟩ : syracuseStep 2302123 = 3453185) B3453185
theorem B3069497 : Blo 2045435 3069497 := bstep (se 2 (by rfl) ⟨1151061, by rfl⟩ : syracuseStep 3069497 = 2302123) B2302123
theorem B2046331 : Blo 2045435 2046331 := bstep (se 1 (by rfl) ⟨1534748, by rfl⟩ : syracuseStep 2046331 = 3069497) B3069497
theorem B3687565 : Blo 2045435 3687565 := bbase (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) (by norm_num)
theorem B4916753 : Blo 2045435 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B3277835 : Blo 2045435 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B2185223 : Blo 2045435 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B23309045 : Blo 2045435 23309045 := bstep (se 5 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 23309045 = 2185223) B2185223
theorem B15539363 : Blo 2045435 15539363 := bstep (se 1 (by rfl) ⟨11654522, by rfl⟩ : syracuseStep 15539363 = 23309045) B23309045
theorem B10359575 : Blo 2045435 10359575 := bstep (se 1 (by rfl) ⟨7769681, by rfl⟩ : syracuseStep 10359575 = 15539363) B15539363
theorem B6906383 : Blo 2045435 6906383 := bstep (se 1 (by rfl) ⟨5179787, by rfl⟩ : syracuseStep 6906383 = 10359575) B10359575
theorem B4604255 : Blo 2045435 4604255 := bstep (se 1 (by rfl) ⟨3453191, by rfl⟩ : syracuseStep 4604255 = 6906383) B6906383
theorem B3069503 : Blo 2045435 3069503 := bstep (se 1 (by rfl) ⟨2302127, by rfl⟩ : syracuseStep 3069503 = 4604255) B4604255
theorem B2046335 : Blo 2045435 2046335 := bstep (se 1 (by rfl) ⟨1534751, by rfl⟩ : syracuseStep 2046335 = 3069503) B3069503
theorem B3069509 : Blo 2045435 3069509 := bbase (se 4 (by rfl) ⟨287766, by rfl⟩ : syracuseStep 3069509 = 575533) (by norm_num)
theorem B2046339 : Blo 2045435 2046339 := bstep (se 1 (by rfl) ⟨1534754, by rfl⟩ : syracuseStep 2046339 = 3069509) B3069509
theorem B3453205 : Blo 2045435 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B4604273 : Blo 2045435 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B3069515 : Blo 2045435 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B2046343 : Blo 2045435 2046343 := bstep (se 1 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 2046343 = 3069515) B3069515
theorem B2302141 : Blo 2045435 2302141 := bbase (se 3 (by rfl) ⟨431651, by rfl⟩ : syracuseStep 2302141 = 863303) (by norm_num)
theorem B3069521 : Blo 2045435 3069521 := bstep (se 2 (by rfl) ⟨1151070, by rfl⟩ : syracuseStep 3069521 = 2302141) B2302141
theorem B2046347 : Blo 2045435 2046347 := bstep (se 1 (by rfl) ⟨1534760, by rfl⟩ : syracuseStep 2046347 = 3069521) B3069521
theorem B6906437 : Blo 2045435 6906437 := bbase (se 4 (by rfl) ⟨647478, by rfl⟩ : syracuseStep 6906437 = 1294957) (by norm_num)
theorem B4604291 : Blo 2045435 4604291 := bstep (se 1 (by rfl) ⟨3453218, by rfl⟩ : syracuseStep 4604291 = 6906437) B6906437
theorem B3069527 : Blo 2045435 3069527 := bstep (se 1 (by rfl) ⟨2302145, by rfl⟩ : syracuseStep 3069527 = 4604291) B4604291
theorem B2046351 : Blo 2045435 2046351 := bstep (se 1 (by rfl) ⟨1534763, by rfl⟩ : syracuseStep 2046351 = 3069527) B3069527
theorem B3069533 : Blo 2045435 3069533 := bbase (se 3 (by rfl) ⟨575537, by rfl⟩ : syracuseStep 3069533 = 1151075) (by norm_num)
theorem B2046355 : Blo 2045435 2046355 := bstep (se 1 (by rfl) ⟨1534766, by rfl⟩ : syracuseStep 2046355 = 3069533) B3069533
theorem B4604309 : Blo 2045435 4604309 := bbase (se 6 (by rfl) ⟨107913, by rfl⟩ : syracuseStep 4604309 = 215827) (by norm_num)
theorem B3069539 : Blo 2045435 3069539 := bstep (se 1 (by rfl) ⟨2302154, by rfl⟩ : syracuseStep 3069539 = 4604309) B4604309
theorem B2046359 : Blo 2045435 2046359 := bstep (se 1 (by rfl) ⟨1534769, by rfl⟩ : syracuseStep 2046359 = 3069539) B3069539
theorem B4916821 : Blo 2045435 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B6555761 : Blo 2045435 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B4370507 : Blo 2045435 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B2913671 : Blo 2045435 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B7769789 : Blo 2045435 7769789 := bstep (se 3 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 7769789 = 2913671) B2913671
theorem B5179859 : Blo 2045435 5179859 := bstep (se 1 (by rfl) ⟨3884894, by rfl⟩ : syracuseStep 5179859 = 7769789) B7769789
theorem B3453239 : Blo 2045435 3453239 := bstep (se 1 (by rfl) ⟨2589929, by rfl⟩ : syracuseStep 3453239 = 5179859) B5179859
theorem B2302159 : Blo 2045435 2302159 := bstep (se 1 (by rfl) ⟨1726619, by rfl⟩ : syracuseStep 2302159 = 3453239) B3453239
theorem B3069545 : Blo 2045435 3069545 := bstep (se 2 (by rfl) ⟨1151079, by rfl⟩ : syracuseStep 3069545 = 2302159) B2302159
theorem B2046363 : Blo 2045435 2046363 := bstep (se 1 (by rfl) ⟨1534772, by rfl⟩ : syracuseStep 2046363 = 3069545) B3069545
theorem B8741029 : Blo 2045435 8741029 := bbase (se 4 (by rfl) ⟨819471, by rfl⟩ : syracuseStep 8741029 = 1638943) (by norm_num)
theorem B11654705 : Blo 2045435 11654705 := bstep (se 2 (by rfl) ⟨4370514, by rfl⟩ : syracuseStep 11654705 = 8741029) B8741029
theorem B7769803 : Blo 2045435 7769803 := bstep (se 1 (by rfl) ⟨5827352, by rfl⟩ : syracuseStep 7769803 = 11654705) B11654705
theorem B10359737 : Blo 2045435 10359737 := bstep (se 2 (by rfl) ⟨3884901, by rfl⟩ : syracuseStep 10359737 = 7769803) B7769803
theorem B6906491 : Blo 2045435 6906491 := bstep (se 1 (by rfl) ⟨5179868, by rfl⟩ : syracuseStep 6906491 = 10359737) B10359737
theorem B4604327 : Blo 2045435 4604327 := bstep (se 1 (by rfl) ⟨3453245, by rfl⟩ : syracuseStep 4604327 = 6906491) B6906491
theorem B3069551 : Blo 2045435 3069551 := bstep (se 1 (by rfl) ⟨2302163, by rfl⟩ : syracuseStep 3069551 = 4604327) B4604327
theorem B2046367 : Blo 2045435 2046367 := bstep (se 1 (by rfl) ⟨1534775, by rfl⟩ : syracuseStep 2046367 = 3069551) B3069551
theorem B3069557 : Blo 2045435 3069557 := bbase (se 5 (by rfl) ⟨143885, by rfl⟩ : syracuseStep 3069557 = 287771) (by norm_num)
theorem B2046371 : Blo 2045435 2046371 := bstep (se 1 (by rfl) ⟨1534778, by rfl⟩ : syracuseStep 2046371 = 3069557) B3069557
theorem B3884917 : Blo 2045435 3884917 := bbase (se 5 (by rfl) ⟨182105, by rfl⟩ : syracuseStep 3884917 = 364211) (by norm_num)
theorem B5179889 : Blo 2045435 5179889 := bstep (se 2 (by rfl) ⟨1942458, by rfl⟩ : syracuseStep 5179889 = 3884917) B3884917
theorem B3453259 : Blo 2045435 3453259 := bstep (se 1 (by rfl) ⟨2589944, by rfl⟩ : syracuseStep 3453259 = 5179889) B5179889
theorem B4604345 : Blo 2045435 4604345 := bstep (se 2 (by rfl) ⟨1726629, by rfl⟩ : syracuseStep 4604345 = 3453259) B3453259
theorem B3069563 : Blo 2045435 3069563 := bstep (se 1 (by rfl) ⟨2302172, by rfl⟩ : syracuseStep 3069563 = 4604345) B4604345
theorem B2046375 : Blo 2045435 2046375 := bstep (se 1 (by rfl) ⟨1534781, by rfl⟩ : syracuseStep 2046375 = 3069563) B3069563
theorem B2302177 : Blo 2045435 2302177 := bbase (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) (by norm_num)
theorem B3069569 : Blo 2045435 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B2046379 : Blo 2045435 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B5179909 : Blo 2045435 5179909 := bbase (se 4 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 5179909 = 971233) (by norm_num)
theorem B6906545 : Blo 2045435 6906545 := bstep (se 2 (by rfl) ⟨2589954, by rfl⟩ : syracuseStep 6906545 = 5179909) B5179909
theorem B4604363 : Blo 2045435 4604363 := bstep (se 1 (by rfl) ⟨3453272, by rfl⟩ : syracuseStep 4604363 = 6906545) B6906545
theorem B3069575 : Blo 2045435 3069575 := bstep (se 1 (by rfl) ⟨2302181, by rfl⟩ : syracuseStep 3069575 = 4604363) B4604363
theorem B2046383 : Blo 2045435 2046383 := bstep (se 1 (by rfl) ⟨1534787, by rfl⟩ : syracuseStep 2046383 = 3069575) B3069575
theorem B3069581 : Blo 2045435 3069581 := bbase (se 3 (by rfl) ⟨575546, by rfl⟩ : syracuseStep 3069581 = 1151093) (by norm_num)
theorem B2046387 : Blo 2045435 2046387 := bstep (se 1 (by rfl) ⟨1534790, by rfl⟩ : syracuseStep 2046387 = 3069581) B3069581
theorem B4604381 : Blo 2045435 4604381 := bbase (se 3 (by rfl) ⟨863321, by rfl⟩ : syracuseStep 4604381 = 1726643) (by norm_num)
theorem B3069587 : Blo 2045435 3069587 := bstep (se 1 (by rfl) ⟨2302190, by rfl⟩ : syracuseStep 3069587 = 4604381) B4604381
theorem B2046391 : Blo 2045435 2046391 := bstep (se 1 (by rfl) ⟨1534793, by rfl⟩ : syracuseStep 2046391 = 3069587) B3069587
theorem B3453293 : Blo 2045435 3453293 := bbase (se 3 (by rfl) ⟨647492, by rfl⟩ : syracuseStep 3453293 = 1294985) (by norm_num)
theorem B2302195 : Blo 2045435 2302195 := bstep (se 1 (by rfl) ⟨1726646, by rfl⟩ : syracuseStep 2302195 = 3453293) B3453293
theorem B3069593 : Blo 2045435 3069593 := bstep (se 2 (by rfl) ⟨1151097, by rfl⟩ : syracuseStep 3069593 = 2302195) B2302195
theorem B2046395 : Blo 2045435 2046395 := bstep (se 1 (by rfl) ⟨1534796, by rfl⟩ : syracuseStep 2046395 = 3069593) B3069593
theorem B15966773 : Blo 2045435 15966773 := bbase (se 5 (by rfl) ⟨748442, by rfl⟩ : syracuseStep 15966773 = 1496885) (by norm_num)
theorem B681248981 : Blo 2045435 681248981 := bstep (se 7 (by rfl) ⟨7983386, by rfl⟩ : syracuseStep 681248981 = 15966773) B15966773
theorem B454165987 : Blo 2045435 454165987 := bstep (se 1 (by rfl) ⟨340624490, by rfl⟩ : syracuseStep 454165987 = 681248981) B681248981
theorem B605554649 : Blo 2045435 605554649 := bstep (se 2 (by rfl) ⟨227082993, by rfl⟩ : syracuseStep 605554649 = 454165987) B454165987
theorem B403703099 : Blo 2045435 403703099 := bstep (se 1 (by rfl) ⟨302777324, by rfl⟩ : syracuseStep 403703099 = 605554649) B605554649
theorem B269135399 : Blo 2045435 269135399 := bstep (se 1 (by rfl) ⟨201851549, by rfl⟩ : syracuseStep 269135399 = 403703099) B403703099
theorem B179423599 : Blo 2045435 179423599 := bstep (se 1 (by rfl) ⟨134567699, by rfl⟩ : syracuseStep 179423599 = 269135399) B269135399
theorem B239231465 : Blo 2045435 239231465 := bstep (se 2 (by rfl) ⟨89711799, by rfl⟩ : syracuseStep 239231465 = 179423599) B179423599
theorem B159487643 : Blo 2045435 159487643 := bstep (se 1 (by rfl) ⟨119615732, by rfl⟩ : syracuseStep 159487643 = 239231465) B239231465
theorem B106325095 : Blo 2045435 106325095 := bstep (se 1 (by rfl) ⟨79743821, by rfl⟩ : syracuseStep 106325095 = 159487643) B159487643
theorem B141766793 : Blo 2045435 141766793 := bstep (se 2 (by rfl) ⟨53162547, by rfl⟩ : syracuseStep 141766793 = 106325095) B106325095
theorem B94511195 : Blo 2045435 94511195 := bstep (se 1 (by rfl) ⟨70883396, by rfl⟩ : syracuseStep 94511195 = 141766793) B141766793
theorem B63007463 : Blo 2045435 63007463 := bstep (se 1 (by rfl) ⟨47255597, by rfl⟩ : syracuseStep 63007463 = 94511195) B94511195
theorem B42004975 : Blo 2045435 42004975 := bstep (se 1 (by rfl) ⟨31503731, by rfl⟩ : syracuseStep 42004975 = 63007463) B63007463
theorem B56006633 : Blo 2045435 56006633 := bstep (se 2 (by rfl) ⟨21002487, by rfl⟩ : syracuseStep 56006633 = 42004975) B42004975
theorem B37337755 : Blo 2045435 37337755 := bstep (se 1 (by rfl) ⟨28003316, by rfl⟩ : syracuseStep 37337755 = 56006633) B56006633
theorem B49783673 : Blo 2045435 49783673 := bstep (se 2 (by rfl) ⟨18668877, by rfl⟩ : syracuseStep 49783673 = 37337755) B37337755
theorem B33189115 : Blo 2045435 33189115 := bstep (se 1 (by rfl) ⟨24891836, by rfl⟩ : syracuseStep 33189115 = 49783673) B49783673
theorem B44252153 : Blo 2045435 44252153 := bstep (se 2 (by rfl) ⟨16594557, by rfl⟩ : syracuseStep 44252153 = 33189115) B33189115
theorem B29501435 : Blo 2045435 29501435 := bstep (se 1 (by rfl) ⟨22126076, by rfl⟩ : syracuseStep 29501435 = 44252153) B44252153
theorem B19667623 : Blo 2045435 19667623 := bstep (se 1 (by rfl) ⟨14750717, by rfl⟩ : syracuseStep 19667623 = 29501435) B29501435
theorem B26223497 : Blo 2045435 26223497 := bstep (se 2 (by rfl) ⟨9833811, by rfl⟩ : syracuseStep 26223497 = 19667623) B19667623
theorem B17482331 : Blo 2045435 17482331 := bstep (se 1 (by rfl) ⟨13111748, by rfl⟩ : syracuseStep 17482331 = 26223497) B26223497
theorem B11654887 : Blo 2045435 11654887 := bstep (se 1 (by rfl) ⟨8741165, by rfl⟩ : syracuseStep 11654887 = 17482331) B17482331
theorem B15539849 : Blo 2045435 15539849 := bstep (se 2 (by rfl) ⟨5827443, by rfl⟩ : syracuseStep 15539849 = 11654887) B11654887
theorem B10359899 : Blo 2045435 10359899 := bstep (se 1 (by rfl) ⟨7769924, by rfl⟩ : syracuseStep 10359899 = 15539849) B15539849
theorem B6906599 : Blo 2045435 6906599 := bstep (se 1 (by rfl) ⟨5179949, by rfl⟩ : syracuseStep 6906599 = 10359899) B10359899
theorem B4604399 : Blo 2045435 4604399 := bstep (se 1 (by rfl) ⟨3453299, by rfl⟩ : syracuseStep 4604399 = 6906599) B6906599
theorem B3069599 : Blo 2045435 3069599 := bstep (se 1 (by rfl) ⟨2302199, by rfl⟩ : syracuseStep 3069599 = 4604399) B4604399
theorem B2046399 : Blo 2045435 2046399 := bstep (se 1 (by rfl) ⟨1534799, by rfl⟩ : syracuseStep 2046399 = 3069599) B3069599
theorem B3069605 : Blo 2045435 3069605 := bbase (se 4 (by rfl) ⟨287775, by rfl⟩ : syracuseStep 3069605 = 575551) (by norm_num)
theorem B2046403 : Blo 2045435 2046403 := bstep (se 1 (by rfl) ⟨1534802, by rfl⟩ : syracuseStep 2046403 = 3069605) B3069605
theorem B2589985 : Blo 2045435 2589985 := bbase (se 2 (by rfl) ⟨971244, by rfl⟩ : syracuseStep 2589985 = 1942489) (by norm_num)
theorem B3453313 : Blo 2045435 3453313 := bstep (se 2 (by rfl) ⟨1294992, by rfl⟩ : syracuseStep 3453313 = 2589985) B2589985
theorem B4604417 : Blo 2045435 4604417 := bstep (se 2 (by rfl) ⟨1726656, by rfl⟩ : syracuseStep 4604417 = 3453313) B3453313
theorem B3069611 : Blo 2045435 3069611 := bstep (se 1 (by rfl) ⟨2302208, by rfl⟩ : syracuseStep 3069611 = 4604417) B4604417
theorem B2046407 : Blo 2045435 2046407 := bstep (se 1 (by rfl) ⟨1534805, by rfl⟩ : syracuseStep 2046407 = 3069611) B3069611
theorem B2302213 : Blo 2045435 2302213 := bbase (se 4 (by rfl) ⟨215832, by rfl⟩ : syracuseStep 2302213 = 431665) (by norm_num)
theorem B3069617 : Blo 2045435 3069617 := bstep (se 2 (by rfl) ⟨1151106, by rfl⟩ : syracuseStep 3069617 = 2302213) B2302213
theorem B2046411 : Blo 2045435 2046411 := bstep (se 1 (by rfl) ⟨1534808, by rfl⟩ : syracuseStep 2046411 = 3069617) B3069617
theorem B2185309 : Blo 2045435 2185309 := bbase (se 3 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 2185309 = 819491) (by norm_num)
theorem B2913745 : Blo 2045435 2913745 := bstep (se 2 (by rfl) ⟨1092654, by rfl⟩ : syracuseStep 2913745 = 2185309) B2185309
theorem B3884993 : Blo 2045435 3884993 := bstep (se 2 (by rfl) ⟨1456872, by rfl⟩ : syracuseStep 3884993 = 2913745) B2913745
theorem B2589995 : Blo 2045435 2589995 := bstep (se 1 (by rfl) ⟨1942496, by rfl⟩ : syracuseStep 2589995 = 3884993) B3884993
theorem B6906653 : Blo 2045435 6906653 := bstep (se 3 (by rfl) ⟨1294997, by rfl⟩ : syracuseStep 6906653 = 2589995) B2589995
theorem B4604435 : Blo 2045435 4604435 := bstep (se 1 (by rfl) ⟨3453326, by rfl⟩ : syracuseStep 4604435 = 6906653) B6906653
theorem B3069623 : Blo 2045435 3069623 := bstep (se 1 (by rfl) ⟨2302217, by rfl⟩ : syracuseStep 3069623 = 4604435) B4604435
theorem B2046415 : Blo 2045435 2046415 := bstep (se 1 (by rfl) ⟨1534811, by rfl⟩ : syracuseStep 2046415 = 3069623) B3069623
theorem B3069629 : Blo 2045435 3069629 := bbase (se 3 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 3069629 = 1151111) (by norm_num)
theorem B2046419 : Blo 2045435 2046419 := bstep (se 1 (by rfl) ⟨1534814, by rfl⟩ : syracuseStep 2046419 = 3069629) B3069629
theorem B4604453 : Blo 2045435 4604453 := bbase (se 4 (by rfl) ⟨431667, by rfl⟩ : syracuseStep 4604453 = 863335) (by norm_num)
theorem B3069635 : Blo 2045435 3069635 := bstep (se 1 (by rfl) ⟨2302226, by rfl⟩ : syracuseStep 3069635 = 4604453) B4604453
theorem B2046423 : Blo 2045435 2046423 := bstep (se 1 (by rfl) ⟨1534817, by rfl⟩ : syracuseStep 2046423 = 3069635) B3069635
theorem B5180021 : Blo 2045435 5180021 := bbase (se 5 (by rfl) ⟨242813, by rfl⟩ : syracuseStep 5180021 = 485627) (by norm_num)
theorem B3453347 : Blo 2045435 3453347 := bstep (se 1 (by rfl) ⟨2590010, by rfl⟩ : syracuseStep 3453347 = 5180021) B5180021
theorem B2302231 : Blo 2045435 2302231 := bstep (se 1 (by rfl) ⟨1726673, by rfl⟩ : syracuseStep 2302231 = 3453347) B3453347
theorem B3069641 : Blo 2045435 3069641 := bstep (se 2 (by rfl) ⟨1151115, by rfl⟩ : syracuseStep 3069641 = 2302231) B2302231
theorem B2046427 : Blo 2045435 2046427 := bstep (se 1 (by rfl) ⟨1534820, by rfl⟩ : syracuseStep 2046427 = 3069641) B3069641
theorem B4430285 : Blo 2045435 4430285 := bbase (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) (by norm_num)
theorem B2953523 : Blo 2045435 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B7876061 : Blo 2045435 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B5250707 : Blo 2045435 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B3500471 : Blo 2045435 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B2333647 : Blo 2045435 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B3111529 : Blo 2045435 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B4148705 : Blo 2045435 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B11063213 : Blo 2045435 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B7375475 : Blo 2045435 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B19667933 : Blo 2045435 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B13111955 : Blo 2045435 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B8741303 : Blo 2045435 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B5827535 : Blo 2045435 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B3885023 : Blo 2045435 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B10360061 : Blo 2045435 10360061 := bstep (se 3 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 10360061 = 3885023) B3885023
theorem B6906707 : Blo 2045435 6906707 := bstep (se 1 (by rfl) ⟨5180030, by rfl⟩ : syracuseStep 6906707 = 10360061) B10360061
theorem B4604471 : Blo 2045435 4604471 := bstep (se 1 (by rfl) ⟨3453353, by rfl⟩ : syracuseStep 4604471 = 6906707) B6906707
theorem B3069647 : Blo 2045435 3069647 := bstep (se 1 (by rfl) ⟨2302235, by rfl⟩ : syracuseStep 3069647 = 4604471) B4604471
theorem B2046431 : Blo 2045435 2046431 := bstep (se 1 (by rfl) ⟨1534823, by rfl⟩ : syracuseStep 2046431 = 3069647) B3069647
theorem B3069653 : Blo 2045435 3069653 := bbase (se 7 (by rfl) ⟨35972, by rfl⟩ : syracuseStep 3069653 = 71945) (by norm_num)
theorem B2046435 : Blo 2045435 2046435 := bstep (se 1 (by rfl) ⟨1534826, by rfl⟩ : syracuseStep 2046435 = 3069653) B3069653
theorem B4370669 : Blo 2045435 4370669 := bbase (se 3 (by rfl) ⟨819500, by rfl⟩ : syracuseStep 4370669 = 1639001) (by norm_num)
theorem B2913779 : Blo 2045435 2913779 := bstep (se 1 (by rfl) ⟨2185334, by rfl⟩ : syracuseStep 2913779 = 4370669) B4370669
theorem B7770077 : Blo 2045435 7770077 := bstep (se 3 (by rfl) ⟨1456889, by rfl⟩ : syracuseStep 7770077 = 2913779) B2913779
theorem B5180051 : Blo 2045435 5180051 := bstep (se 1 (by rfl) ⟨3885038, by rfl⟩ : syracuseStep 5180051 = 7770077) B7770077
theorem B3453367 : Blo 2045435 3453367 := bstep (se 1 (by rfl) ⟨2590025, by rfl⟩ : syracuseStep 3453367 = 5180051) B5180051
theorem B4604489 : Blo 2045435 4604489 := bstep (se 2 (by rfl) ⟨1726683, by rfl⟩ : syracuseStep 4604489 = 3453367) B3453367
theorem B3069659 : Blo 2045435 3069659 := bstep (se 1 (by rfl) ⟨2302244, by rfl⟩ : syracuseStep 3069659 = 4604489) B4604489
theorem B2046439 : Blo 2045435 2046439 := bstep (se 1 (by rfl) ⟨1534829, by rfl⟩ : syracuseStep 2046439 = 3069659) B3069659
theorem B2302249 : Blo 2045435 2302249 := bbase (se 2 (by rfl) ⟨863343, by rfl⟩ : syracuseStep 2302249 = 1726687) (by norm_num)
theorem B3069665 : Blo 2045435 3069665 := bstep (se 2 (by rfl) ⟨1151124, by rfl⟩ : syracuseStep 3069665 = 2302249) B2302249
theorem B2046443 : Blo 2045435 2046443 := bstep (se 1 (by rfl) ⟨1534832, by rfl⟩ : syracuseStep 2046443 = 3069665) B3069665
theorem B2333665 : Blo 2045435 2333665 := bbase (se 2 (by rfl) ⟨875124, by rfl⟩ : syracuseStep 2333665 = 1750249) (by norm_num)
theorem B3111553 : Blo 2045435 3111553 := bstep (se 2 (by rfl) ⟨1166832, by rfl⟩ : syracuseStep 3111553 = 2333665) B2333665
theorem B16594949 : Blo 2045435 16594949 := bstep (se 4 (by rfl) ⟨1555776, by rfl⟩ : syracuseStep 16594949 = 3111553) B3111553
theorem B11063299 : Blo 2045435 11063299 := bstep (se 1 (by rfl) ⟨8297474, by rfl⟩ : syracuseStep 11063299 = 16594949) B16594949
theorem B14751065 : Blo 2045435 14751065 := bstep (se 2 (by rfl) ⟨5531649, by rfl⟩ : syracuseStep 14751065 = 11063299) B11063299
theorem B9834043 : Blo 2045435 9834043 := bstep (se 1 (by rfl) ⟨7375532, by rfl⟩ : syracuseStep 9834043 = 14751065) B14751065
theorem B13112057 : Blo 2045435 13112057 := bstep (se 2 (by rfl) ⟨4917021, by rfl⟩ : syracuseStep 13112057 = 9834043) B9834043
theorem B8741371 : Blo 2045435 8741371 := bstep (se 1 (by rfl) ⟨6556028, by rfl⟩ : syracuseStep 8741371 = 13112057) B13112057
theorem B11655161 : Blo 2045435 11655161 := bstep (se 2 (by rfl) ⟨4370685, by rfl⟩ : syracuseStep 11655161 = 8741371) B8741371
theorem B7770107 : Blo 2045435 7770107 := bstep (se 1 (by rfl) ⟨5827580, by rfl⟩ : syracuseStep 7770107 = 11655161) B11655161
theorem B5180071 : Blo 2045435 5180071 := bstep (se 1 (by rfl) ⟨3885053, by rfl⟩ : syracuseStep 5180071 = 7770107) B7770107
theorem B6906761 : Blo 2045435 6906761 := bstep (se 2 (by rfl) ⟨2590035, by rfl⟩ : syracuseStep 6906761 = 5180071) B5180071
theorem B4604507 : Blo 2045435 4604507 := bstep (se 1 (by rfl) ⟨3453380, by rfl⟩ : syracuseStep 4604507 = 6906761) B6906761
theorem B3069671 : Blo 2045435 3069671 := bstep (se 1 (by rfl) ⟨2302253, by rfl⟩ : syracuseStep 3069671 = 4604507) B4604507
theorem B2046447 : Blo 2045435 2046447 := bstep (se 1 (by rfl) ⟨1534835, by rfl⟩ : syracuseStep 2046447 = 3069671) B3069671
theorem B3069677 : Blo 2045435 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B2046451 : Blo 2045435 2046451 := bstep (se 1 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 2046451 = 3069677) B3069677
theorem B4604525 : Blo 2045435 4604525 := bbase (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) (by norm_num)
theorem B3069683 : Blo 2045435 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B2046455 : Blo 2045435 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B3885077 : Blo 2045435 3885077 := bbase (se 6 (by rfl) ⟨91056, by rfl⟩ : syracuseStep 3885077 = 182113) (by norm_num)
theorem B2590051 : Blo 2045435 2590051 := bstep (se 1 (by rfl) ⟨1942538, by rfl⟩ : syracuseStep 2590051 = 3885077) B3885077
theorem B3453401 : Blo 2045435 3453401 := bstep (se 2 (by rfl) ⟨1295025, by rfl⟩ : syracuseStep 3453401 = 2590051) B2590051
theorem B2302267 : Blo 2045435 2302267 := bstep (se 1 (by rfl) ⟨1726700, by rfl⟩ : syracuseStep 2302267 = 3453401) B3453401
theorem B3069689 : Blo 2045435 3069689 := bstep (se 2 (by rfl) ⟨1151133, by rfl⟩ : syracuseStep 3069689 = 2302267) B2302267
theorem B2046459 : Blo 2045435 2046459 := bstep (se 1 (by rfl) ⟨1534844, by rfl⟩ : syracuseStep 2046459 = 3069689) B3069689
theorem B3738109 : Blo 2045435 3738109 := bbase (se 3 (by rfl) ⟨700895, by rfl⟩ : syracuseStep 3738109 = 1401791) (by norm_num)
theorem B4984145 : Blo 2045435 4984145 := bstep (se 2 (by rfl) ⟨1869054, by rfl⟩ : syracuseStep 4984145 = 3738109) B3738109
theorem B3322763 : Blo 2045435 3322763 := bstep (se 1 (by rfl) ⟨2492072, by rfl⟩ : syracuseStep 3322763 = 4984145) B4984145
theorem B35442805 : Blo 2045435 35442805 := bstep (se 5 (by rfl) ⟨1661381, by rfl⟩ : syracuseStep 35442805 = 3322763) B3322763
theorem B47257073 : Blo 2045435 47257073 := bstep (se 2 (by rfl) ⟨17721402, by rfl⟩ : syracuseStep 47257073 = 35442805) B35442805
theorem B31504715 : Blo 2045435 31504715 := bstep (se 1 (by rfl) ⟨23628536, by rfl⟩ : syracuseStep 31504715 = 47257073) B47257073
theorem B21003143 : Blo 2045435 21003143 := bstep (se 1 (by rfl) ⟨15752357, by rfl⟩ : syracuseStep 21003143 = 31504715) B31504715
theorem B224033525 : Blo 2045435 224033525 := bstep (se 5 (by rfl) ⟨10501571, by rfl⟩ : syracuseStep 224033525 = 21003143) B21003143
theorem B149355683 : Blo 2045435 149355683 := bstep (se 1 (by rfl) ⟨112016762, by rfl⟩ : syracuseStep 149355683 = 224033525) B224033525
theorem B99570455 : Blo 2045435 99570455 := bstep (se 1 (by rfl) ⟨74677841, by rfl⟩ : syracuseStep 99570455 = 149355683) B149355683
theorem B66380303 : Blo 2045435 66380303 := bstep (se 1 (by rfl) ⟨49785227, by rfl⟩ : syracuseStep 66380303 = 99570455) B99570455
theorem B44253535 : Blo 2045435 44253535 := bstep (se 1 (by rfl) ⟨33190151, by rfl⟩ : syracuseStep 44253535 = 66380303) B66380303
theorem B59004713 : Blo 2045435 59004713 := bstep (se 2 (by rfl) ⟨22126767, by rfl⟩ : syracuseStep 59004713 = 44253535) B44253535
theorem B39336475 : Blo 2045435 39336475 := bstep (se 1 (by rfl) ⟨29502356, by rfl⟩ : syracuseStep 39336475 = 59004713) B59004713
theorem B52448633 : Blo 2045435 52448633 := bstep (se 2 (by rfl) ⟨19668237, by rfl⟩ : syracuseStep 52448633 = 39336475) B39336475
theorem B34965755 : Blo 2045435 34965755 := bstep (se 1 (by rfl) ⟨26224316, by rfl⟩ : syracuseStep 34965755 = 52448633) B52448633
theorem B23310503 : Blo 2045435 23310503 := bstep (se 1 (by rfl) ⟨17482877, by rfl⟩ : syracuseStep 23310503 = 34965755) B34965755
theorem B15540335 : Blo 2045435 15540335 := bstep (se 1 (by rfl) ⟨11655251, by rfl⟩ : syracuseStep 15540335 = 23310503) B23310503
theorem B10360223 : Blo 2045435 10360223 := bstep (se 1 (by rfl) ⟨7770167, by rfl⟩ : syracuseStep 10360223 = 15540335) B15540335
theorem B6906815 : Blo 2045435 6906815 := bstep (se 1 (by rfl) ⟨5180111, by rfl⟩ : syracuseStep 6906815 = 10360223) B10360223
theorem B4604543 : Blo 2045435 4604543 := bstep (se 1 (by rfl) ⟨3453407, by rfl⟩ : syracuseStep 4604543 = 6906815) B6906815
theorem B3069695 : Blo 2045435 3069695 := bstep (se 1 (by rfl) ⟨2302271, by rfl⟩ : syracuseStep 3069695 = 4604543) B4604543
theorem B2046463 : Blo 2045435 2046463 := bstep (se 1 (by rfl) ⟨1534847, by rfl⟩ : syracuseStep 2046463 = 3069695) B3069695
theorem B3069701 : Blo 2045435 3069701 := bbase (se 4 (by rfl) ⟨287784, by rfl⟩ : syracuseStep 3069701 = 575569) (by norm_num)
theorem B2046467 : Blo 2045435 2046467 := bstep (se 1 (by rfl) ⟨1534850, by rfl⟩ : syracuseStep 2046467 = 3069701) B3069701
theorem B3453421 : Blo 2045435 3453421 := bbase (se 3 (by rfl) ⟨647516, by rfl⟩ : syracuseStep 3453421 = 1295033) (by norm_num)
theorem B4604561 : Blo 2045435 4604561 := bstep (se 2 (by rfl) ⟨1726710, by rfl⟩ : syracuseStep 4604561 = 3453421) B3453421
theorem B3069707 : Blo 2045435 3069707 := bstep (se 1 (by rfl) ⟨2302280, by rfl⟩ : syracuseStep 3069707 = 4604561) B4604561
theorem B2046471 : Blo 2045435 2046471 := bstep (se 1 (by rfl) ⟨1534853, by rfl⟩ : syracuseStep 2046471 = 3069707) B3069707
theorem B2302285 : Blo 2045435 2302285 := bbase (se 3 (by rfl) ⟨431678, by rfl⟩ : syracuseStep 2302285 = 863357) (by norm_num)
theorem B3069713 : Blo 2045435 3069713 := bstep (se 2 (by rfl) ⟨1151142, by rfl⟩ : syracuseStep 3069713 = 2302285) B2302285
theorem B2046475 : Blo 2045435 2046475 := bstep (se 1 (by rfl) ⟨1534856, by rfl⟩ : syracuseStep 2046475 = 3069713) B3069713
theorem B6906869 : Blo 2045435 6906869 := bbase (se 5 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 6906869 = 647519) (by norm_num)
theorem B4604579 : Blo 2045435 4604579 := bstep (se 1 (by rfl) ⟨3453434, by rfl⟩ : syracuseStep 4604579 = 6906869) B6906869
theorem B3069719 : Blo 2045435 3069719 := bstep (se 1 (by rfl) ⟨2302289, by rfl⟩ : syracuseStep 3069719 = 4604579) B4604579
theorem B2046479 : Blo 2045435 2046479 := bstep (se 1 (by rfl) ⟨1534859, by rfl⟩ : syracuseStep 2046479 = 3069719) B3069719
theorem B3069725 : Blo 2045435 3069725 := bbase (se 3 (by rfl) ⟨575573, by rfl⟩ : syracuseStep 3069725 = 1151147) (by norm_num)
theorem B2046483 : Blo 2045435 2046483 := bstep (se 1 (by rfl) ⟨1534862, by rfl⟩ : syracuseStep 2046483 = 3069725) B3069725
theorem B4604597 : Blo 2045435 4604597 := bbase (se 5 (by rfl) ⟨215840, by rfl⟩ : syracuseStep 4604597 = 431681) (by norm_num)
theorem B3069731 : Blo 2045435 3069731 := bstep (se 1 (by rfl) ⟨2302298, by rfl⟩ : syracuseStep 3069731 = 4604597) B4604597
theorem B2046487 : Blo 2045435 2046487 := bstep (se 1 (by rfl) ⟨1534865, by rfl⟩ : syracuseStep 2046487 = 3069731) B3069731
theorem B11655413 : Blo 2045435 11655413 := bbase (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) (by norm_num)
theorem B7770275 : Blo 2045435 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B5180183 : Blo 2045435 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B3453455 : Blo 2045435 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B2302303 : Blo 2045435 2302303 := bstep (se 1 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 2302303 = 3453455) B3453455
theorem B3069737 : Blo 2045435 3069737 := bstep (se 2 (by rfl) ⟨1151151, by rfl⟩ : syracuseStep 3069737 = 2302303) B2302303
theorem B2046491 : Blo 2045435 2046491 := bstep (se 1 (by rfl) ⟨1534868, by rfl⟩ : syracuseStep 2046491 = 3069737) B3069737
theorem B5827717 : Blo 2045435 5827717 := bbase (se 4 (by rfl) ⟨546348, by rfl⟩ : syracuseStep 5827717 = 1092697) (by norm_num)
theorem B7770289 : Blo 2045435 7770289 := bstep (se 2 (by rfl) ⟨2913858, by rfl⟩ : syracuseStep 7770289 = 5827717) B5827717
theorem B10360385 : Blo 2045435 10360385 := bstep (se 2 (by rfl) ⟨3885144, by rfl⟩ : syracuseStep 10360385 = 7770289) B7770289
theorem B6906923 : Blo 2045435 6906923 := bstep (se 1 (by rfl) ⟨5180192, by rfl⟩ : syracuseStep 6906923 = 10360385) B10360385
theorem B4604615 : Blo 2045435 4604615 := bstep (se 1 (by rfl) ⟨3453461, by rfl⟩ : syracuseStep 4604615 = 6906923) B6906923
theorem B3069743 : Blo 2045435 3069743 := bstep (se 1 (by rfl) ⟨2302307, by rfl⟩ : syracuseStep 3069743 = 4604615) B4604615
theorem B2046495 : Blo 2045435 2046495 := bstep (se 1 (by rfl) ⟨1534871, by rfl⟩ : syracuseStep 2046495 = 3069743) B3069743
theorem B3069749 : Blo 2045435 3069749 := bbase (se 5 (by rfl) ⟨143894, by rfl⟩ : syracuseStep 3069749 = 287789) (by norm_num)
theorem B2046499 : Blo 2045435 2046499 := bstep (se 1 (by rfl) ⟨1534874, by rfl⟩ : syracuseStep 2046499 = 3069749) B3069749
theorem B5180213 : Blo 2045435 5180213 := bbase (se 5 (by rfl) ⟨242822, by rfl⟩ : syracuseStep 5180213 = 485645) (by norm_num)
theorem B3453475 : Blo 2045435 3453475 := bstep (se 1 (by rfl) ⟨2590106, by rfl⟩ : syracuseStep 3453475 = 5180213) B5180213
theorem B4604633 : Blo 2045435 4604633 := bstep (se 2 (by rfl) ⟨1726737, by rfl⟩ : syracuseStep 4604633 = 3453475) B3453475
theorem B3069755 : Blo 2045435 3069755 := bstep (se 1 (by rfl) ⟨2302316, by rfl⟩ : syracuseStep 3069755 = 4604633) B4604633
theorem B2046503 : Blo 2045435 2046503 := bstep (se 1 (by rfl) ⟨1534877, by rfl⟩ : syracuseStep 2046503 = 3069755) B3069755
theorem B2302321 : Blo 2045435 2302321 := bbase (se 2 (by rfl) ⟨863370, by rfl⟩ : syracuseStep 2302321 = 1726741) (by norm_num)
theorem B3069761 : Blo 2045435 3069761 := bstep (se 2 (by rfl) ⟨1151160, by rfl⟩ : syracuseStep 3069761 = 2302321) B2302321
theorem B2046507 : Blo 2045435 2046507 := bstep (se 1 (by rfl) ⟨1534880, by rfl⟩ : syracuseStep 2046507 = 3069761) B3069761
theorem B3278117 : Blo 2045435 3278117 := bbase (se 4 (by rfl) ⟨307323, by rfl⟩ : syracuseStep 3278117 = 614647) (by norm_num)
theorem B8741645 : Blo 2045435 8741645 := bstep (se 3 (by rfl) ⟨1639058, by rfl⟩ : syracuseStep 8741645 = 3278117) B3278117
theorem B5827763 : Blo 2045435 5827763 := bstep (se 1 (by rfl) ⟨4370822, by rfl⟩ : syracuseStep 5827763 = 8741645) B8741645
theorem B3885175 : Blo 2045435 3885175 := bstep (se 1 (by rfl) ⟨2913881, by rfl⟩ : syracuseStep 3885175 = 5827763) B5827763
theorem B5180233 : Blo 2045435 5180233 := bstep (se 2 (by rfl) ⟨1942587, by rfl⟩ : syracuseStep 5180233 = 3885175) B3885175
theorem B6906977 : Blo 2045435 6906977 := bstep (se 2 (by rfl) ⟨2590116, by rfl⟩ : syracuseStep 6906977 = 5180233) B5180233
theorem B4604651 : Blo 2045435 4604651 := bstep (se 1 (by rfl) ⟨3453488, by rfl⟩ : syracuseStep 4604651 = 6906977) B6906977
theorem B3069767 : Blo 2045435 3069767 := bstep (se 1 (by rfl) ⟨2302325, by rfl⟩ : syracuseStep 3069767 = 4604651) B4604651
theorem B2046511 : Blo 2045435 2046511 := bstep (se 1 (by rfl) ⟨1534883, by rfl⟩ : syracuseStep 2046511 = 3069767) B3069767
theorem B3069773 : Blo 2045435 3069773 := bbase (se 3 (by rfl) ⟨575582, by rfl⟩ : syracuseStep 3069773 = 1151165) (by norm_num)
theorem B2046515 : Blo 2045435 2046515 := bstep (se 1 (by rfl) ⟨1534886, by rfl⟩ : syracuseStep 2046515 = 3069773) B3069773
theorem B4604669 : Blo 2045435 4604669 := bbase (se 3 (by rfl) ⟨863375, by rfl⟩ : syracuseStep 4604669 = 1726751) (by norm_num)
theorem B3069779 : Blo 2045435 3069779 := bstep (se 1 (by rfl) ⟨2302334, by rfl⟩ : syracuseStep 3069779 = 4604669) B4604669
theorem B2046519 : Blo 2045435 2046519 := bstep (se 1 (by rfl) ⟨1534889, by rfl⟩ : syracuseStep 2046519 = 3069779) B3069779
theorem B3453509 : Blo 2045435 3453509 := bbase (se 4 (by rfl) ⟨323766, by rfl⟩ : syracuseStep 3453509 = 647533) (by norm_num)
theorem B2302339 : Blo 2045435 2302339 := bstep (se 1 (by rfl) ⟨1726754, by rfl⟩ : syracuseStep 2302339 = 3453509) B3453509
theorem B3069785 : Blo 2045435 3069785 := bstep (se 2 (by rfl) ⟨1151169, by rfl⟩ : syracuseStep 3069785 = 2302339) B2302339
theorem B2046523 : Blo 2045435 2046523 := bstep (se 1 (by rfl) ⟨1534892, by rfl⟩ : syracuseStep 2046523 = 3069785) B3069785
theorem B15540821 : Blo 2045435 15540821 := bbase (se 8 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 15540821 = 182119) (by norm_num)
theorem B10360547 : Blo 2045435 10360547 := bstep (se 1 (by rfl) ⟨7770410, by rfl⟩ : syracuseStep 10360547 = 15540821) B15540821
theorem B6907031 : Blo 2045435 6907031 := bstep (se 1 (by rfl) ⟨5180273, by rfl⟩ : syracuseStep 6907031 = 10360547) B10360547
theorem B4604687 : Blo 2045435 4604687 := bstep (se 1 (by rfl) ⟨3453515, by rfl⟩ : syracuseStep 4604687 = 6907031) B6907031
theorem B3069791 : Blo 2045435 3069791 := bstep (se 1 (by rfl) ⟨2302343, by rfl⟩ : syracuseStep 3069791 = 4604687) B4604687
theorem B2046527 : Blo 2045435 2046527 := bstep (se 1 (by rfl) ⟨1534895, by rfl⟩ : syracuseStep 2046527 = 3069791) B3069791
theorem B3069797 : Blo 2045435 3069797 := bbase (se 4 (by rfl) ⟨287793, by rfl⟩ : syracuseStep 3069797 = 575587) (by norm_num)
theorem B2046531 : Blo 2045435 2046531 := bstep (se 1 (by rfl) ⟨1534898, by rfl⟩ : syracuseStep 2046531 = 3069797) B3069797
theorem B3885221 : Blo 2045435 3885221 := bbase (se 4 (by rfl) ⟨364239, by rfl⟩ : syracuseStep 3885221 = 728479) (by norm_num)
theorem B2590147 : Blo 2045435 2590147 := bstep (se 1 (by rfl) ⟨1942610, by rfl⟩ : syracuseStep 2590147 = 3885221) B3885221
theorem B3453529 : Blo 2045435 3453529 := bstep (se 2 (by rfl) ⟨1295073, by rfl⟩ : syracuseStep 3453529 = 2590147) B2590147
theorem B4604705 : Blo 2045435 4604705 := bstep (se 2 (by rfl) ⟨1726764, by rfl⟩ : syracuseStep 4604705 = 3453529) B3453529
theorem B3069803 : Blo 2045435 3069803 := bstep (se 1 (by rfl) ⟨2302352, by rfl⟩ : syracuseStep 3069803 = 4604705) B4604705
theorem B2046535 : Blo 2045435 2046535 := bstep (se 1 (by rfl) ⟨1534901, by rfl⟩ : syracuseStep 2046535 = 3069803) B3069803
theorem B2302357 : Blo 2045435 2302357 := bbase (se 6 (by rfl) ⟨53961, by rfl⟩ : syracuseStep 2302357 = 107923) (by norm_num)
theorem B3069809 : Blo 2045435 3069809 := bstep (se 2 (by rfl) ⟨1151178, by rfl⟩ : syracuseStep 3069809 = 2302357) B2302357
theorem B2046539 : Blo 2045435 2046539 := bstep (se 1 (by rfl) ⟨1534904, by rfl⟩ : syracuseStep 2046539 = 3069809) B3069809
theorem B2590157 : Blo 2045435 2590157 := bbase (se 3 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 2590157 = 971309) (by norm_num)
theorem B6907085 : Blo 2045435 6907085 := bstep (se 3 (by rfl) ⟨1295078, by rfl⟩ : syracuseStep 6907085 = 2590157) B2590157
theorem B4604723 : Blo 2045435 4604723 := bstep (se 1 (by rfl) ⟨3453542, by rfl⟩ : syracuseStep 4604723 = 6907085) B6907085
theorem B3069815 : Blo 2045435 3069815 := bstep (se 1 (by rfl) ⟨2302361, by rfl⟩ : syracuseStep 3069815 = 4604723) B4604723
theorem B2046543 : Blo 2045435 2046543 := bstep (se 1 (by rfl) ⟨1534907, by rfl⟩ : syracuseStep 2046543 = 3069815) B3069815
theorem B3069821 : Blo 2045435 3069821 := bbase (se 3 (by rfl) ⟨575591, by rfl⟩ : syracuseStep 3069821 = 1151183) (by norm_num)
theorem B2046547 : Blo 2045435 2046547 := bstep (se 1 (by rfl) ⟨1534910, by rfl⟩ : syracuseStep 2046547 = 3069821) B3069821
theorem B4604741 : Blo 2045435 4604741 := bbase (se 4 (by rfl) ⟨431694, by rfl⟩ : syracuseStep 4604741 = 863389) (by norm_num)
theorem B3069827 : Blo 2045435 3069827 := bstep (se 1 (by rfl) ⟨2302370, by rfl⟩ : syracuseStep 3069827 = 4604741) B4604741
theorem B2046551 : Blo 2045435 2046551 := bstep (se 1 (by rfl) ⟨1534913, by rfl⟩ : syracuseStep 2046551 = 3069827) B3069827
theorem B4370917 : Blo 2045435 4370917 := bbase (se 4 (by rfl) ⟨409773, by rfl⟩ : syracuseStep 4370917 = 819547) (by norm_num)
theorem B5827889 : Blo 2045435 5827889 := bstep (se 2 (by rfl) ⟨2185458, by rfl⟩ : syracuseStep 5827889 = 4370917) B4370917
theorem B3885259 : Blo 2045435 3885259 := bstep (se 1 (by rfl) ⟨2913944, by rfl⟩ : syracuseStep 3885259 = 5827889) B5827889
theorem B5180345 : Blo 2045435 5180345 := bstep (se 2 (by rfl) ⟨1942629, by rfl⟩ : syracuseStep 5180345 = 3885259) B3885259
theorem B3453563 : Blo 2045435 3453563 := bstep (se 1 (by rfl) ⟨2590172, by rfl⟩ : syracuseStep 3453563 = 5180345) B5180345
theorem B2302375 : Blo 2045435 2302375 := bstep (se 1 (by rfl) ⟨1726781, by rfl⟩ : syracuseStep 2302375 = 3453563) B3453563
theorem B3069833 : Blo 2045435 3069833 := bstep (se 2 (by rfl) ⟨1151187, by rfl⟩ : syracuseStep 3069833 = 2302375) B2302375
theorem B2046555 : Blo 2045435 2046555 := bstep (se 1 (by rfl) ⟨1534916, by rfl⟩ : syracuseStep 2046555 = 3069833) B3069833
theorem B10360709 : Blo 2045435 10360709 := bbase (se 4 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 10360709 = 1942633) (by norm_num)
theorem B6907139 : Blo 2045435 6907139 := bstep (se 1 (by rfl) ⟨5180354, by rfl⟩ : syracuseStep 6907139 = 10360709) B10360709
theorem B4604759 : Blo 2045435 4604759 := bstep (se 1 (by rfl) ⟨3453569, by rfl⟩ : syracuseStep 4604759 = 6907139) B6907139
theorem B3069839 : Blo 2045435 3069839 := bstep (se 1 (by rfl) ⟨2302379, by rfl⟩ : syracuseStep 3069839 = 4604759) B4604759
theorem B2046559 : Blo 2045435 2046559 := bstep (se 1 (by rfl) ⟨1534919, by rfl⟩ : syracuseStep 2046559 = 3069839) B3069839
theorem B3069845 : Blo 2045435 3069845 := bbase (se 6 (by rfl) ⟨71949, by rfl⟩ : syracuseStep 3069845 = 143899) (by norm_num)
theorem B2046563 : Blo 2045435 2046563 := bstep (se 1 (by rfl) ⟨1534922, by rfl⟩ : syracuseStep 2046563 = 3069845) B3069845
theorem B2697661 : Blo 2045435 2697661 := bbase (se 3 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 2697661 = 1011623) (by norm_num)
theorem B3596881 : Blo 2045435 3596881 := bstep (se 2 (by rfl) ⟨1348830, by rfl⟩ : syracuseStep 3596881 = 2697661) B2697661
theorem B4795841 : Blo 2045435 4795841 := bstep (se 2 (by rfl) ⟨1798440, by rfl⟩ : syracuseStep 4795841 = 3596881) B3596881
theorem B3197227 : Blo 2045435 3197227 := bstep (se 1 (by rfl) ⟨2397920, by rfl⟩ : syracuseStep 3197227 = 4795841) B4795841
theorem B4262969 : Blo 2045435 4262969 := bstep (se 2 (by rfl) ⟨1598613, by rfl⟩ : syracuseStep 4262969 = 3197227) B3197227
theorem B2841979 : Blo 2045435 2841979 := bstep (se 1 (by rfl) ⟨2131484, by rfl⟩ : syracuseStep 2841979 = 4262969) B4262969
theorem B3789305 : Blo 2045435 3789305 := bstep (se 2 (by rfl) ⟨1420989, by rfl⟩ : syracuseStep 3789305 = 2841979) B2841979
theorem B2526203 : Blo 2045435 2526203 := bstep (se 1 (by rfl) ⟨1894652, by rfl⟩ : syracuseStep 2526203 = 3789305) B3789305
theorem B6736541 : Blo 2045435 6736541 := bstep (se 3 (by rfl) ⟨1263101, by rfl⟩ : syracuseStep 6736541 = 2526203) B2526203
theorem B17964109 : Blo 2045435 17964109 := bstep (se 3 (by rfl) ⟨3368270, by rfl⟩ : syracuseStep 17964109 = 6736541) B6736541
theorem B23952145 : Blo 2045435 23952145 := bstep (se 2 (by rfl) ⟨8982054, by rfl⟩ : syracuseStep 23952145 = 17964109) B17964109
theorem B31936193 : Blo 2045435 31936193 := bstep (se 2 (by rfl) ⟨11976072, by rfl⟩ : syracuseStep 31936193 = 23952145) B23952145
theorem B21290795 : Blo 2045435 21290795 := bstep (se 1 (by rfl) ⟨15968096, by rfl⟩ : syracuseStep 21290795 = 31936193) B31936193
theorem B14193863 : Blo 2045435 14193863 := bstep (se 1 (by rfl) ⟨10645397, by rfl⟩ : syracuseStep 14193863 = 21290795) B21290795
theorem B9462575 : Blo 2045435 9462575 := bstep (se 1 (by rfl) ⟨7096931, by rfl⟩ : syracuseStep 9462575 = 14193863) B14193863
theorem B6308383 : Blo 2045435 6308383 := bstep (se 1 (by rfl) ⟨4731287, by rfl⟩ : syracuseStep 6308383 = 9462575) B9462575
theorem B8411177 : Blo 2045435 8411177 := bstep (se 2 (by rfl) ⟨3154191, by rfl⟩ : syracuseStep 8411177 = 6308383) B6308383
theorem B5607451 : Blo 2045435 5607451 := bstep (se 1 (by rfl) ⟨4205588, by rfl⟩ : syracuseStep 5607451 = 8411177) B8411177
theorem B29906405 : Blo 2045435 29906405 := bstep (se 4 (by rfl) ⟨2803725, by rfl⟩ : syracuseStep 29906405 = 5607451) B5607451
theorem B19937603 : Blo 2045435 19937603 := bstep (se 1 (by rfl) ⟨14953202, by rfl⟩ : syracuseStep 19937603 = 29906405) B29906405
theorem B53166941 : Blo 2045435 53166941 := bstep (se 3 (by rfl) ⟨9968801, by rfl⟩ : syracuseStep 53166941 = 19937603) B19937603
theorem B35444627 : Blo 2045435 35444627 := bstep (se 1 (by rfl) ⟨26583470, by rfl⟩ : syracuseStep 35444627 = 53166941) B53166941
theorem B23629751 : Blo 2045435 23629751 := bstep (se 1 (by rfl) ⟨17722313, by rfl⟩ : syracuseStep 23629751 = 35444627) B35444627
theorem B15753167 : Blo 2045435 15753167 := bstep (se 1 (by rfl) ⟨11814875, by rfl⟩ : syracuseStep 15753167 = 23629751) B23629751
theorem B10502111 : Blo 2045435 10502111 := bstep (se 1 (by rfl) ⟨7876583, by rfl⟩ : syracuseStep 10502111 = 15753167) B15753167
theorem B7001407 : Blo 2045435 7001407 := bstep (se 1 (by rfl) ⟨5251055, by rfl⟩ : syracuseStep 7001407 = 10502111) B10502111
theorem B37340837 : Blo 2045435 37340837 := bstep (se 4 (by rfl) ⟨3500703, by rfl⟩ : syracuseStep 37340837 = 7001407) B7001407
theorem B24893891 : Blo 2045435 24893891 := bstep (se 1 (by rfl) ⟨18670418, by rfl⟩ : syracuseStep 24893891 = 37340837) B37340837
theorem B16595927 : Blo 2045435 16595927 := bstep (se 1 (by rfl) ⟨12446945, by rfl⟩ : syracuseStep 16595927 = 24893891) B24893891
theorem B11063951 : Blo 2045435 11063951 := bstep (se 1 (by rfl) ⟨8297963, by rfl⟩ : syracuseStep 11063951 = 16595927) B16595927
theorem B7375967 : Blo 2045435 7375967 := bstep (se 1 (by rfl) ⟨5531975, by rfl⟩ : syracuseStep 7375967 = 11063951) B11063951
theorem B4917311 : Blo 2045435 4917311 := bstep (se 1 (by rfl) ⟨3687983, by rfl⟩ : syracuseStep 4917311 = 7375967) B7375967
theorem B3278207 : Blo 2045435 3278207 := bstep (se 1 (by rfl) ⟨2458655, by rfl⟩ : syracuseStep 3278207 = 4917311) B4917311
theorem B2185471 : Blo 2045435 2185471 := bstep (se 1 (by rfl) ⟨1639103, by rfl⟩ : syracuseStep 2185471 = 3278207) B3278207
theorem B11655845 : Blo 2045435 11655845 := bstep (se 4 (by rfl) ⟨1092735, by rfl⟩ : syracuseStep 11655845 = 2185471) B2185471
theorem B7770563 : Blo 2045435 7770563 := bstep (se 1 (by rfl) ⟨5827922, by rfl⟩ : syracuseStep 7770563 = 11655845) B11655845
theorem B5180375 : Blo 2045435 5180375 := bstep (se 1 (by rfl) ⟨3885281, by rfl⟩ : syracuseStep 5180375 = 7770563) B7770563
theorem B3453583 : Blo 2045435 3453583 := bstep (se 1 (by rfl) ⟨2590187, by rfl⟩ : syracuseStep 3453583 = 5180375) B5180375
theorem B4604777 : Blo 2045435 4604777 := bstep (se 2 (by rfl) ⟨1726791, by rfl⟩ : syracuseStep 4604777 = 3453583) B3453583
theorem B3069851 : Blo 2045435 3069851 := bstep (se 1 (by rfl) ⟨2302388, by rfl⟩ : syracuseStep 3069851 = 4604777) B4604777
theorem B2046567 : Blo 2045435 2046567 := bstep (se 1 (by rfl) ⟨1534925, by rfl⟩ : syracuseStep 2046567 = 3069851) B3069851
theorem B2302393 : Blo 2045435 2302393 := bbase (se 2 (by rfl) ⟨863397, by rfl⟩ : syracuseStep 2302393 = 1726795) (by norm_num)
theorem B3069857 : Blo 2045435 3069857 := bstep (se 2 (by rfl) ⟨1151196, by rfl⟩ : syracuseStep 3069857 = 2302393) B2302393
theorem B2046571 : Blo 2045435 2046571 := bstep (se 1 (by rfl) ⟨1534928, by rfl⟩ : syracuseStep 2046571 = 3069857) B3069857
theorem B14751989 : Blo 2045435 14751989 := bbase (se 5 (by rfl) ⟨691499, by rfl⟩ : syracuseStep 14751989 = 1382999) (by norm_num)
theorem B9834659 : Blo 2045435 9834659 := bstep (se 1 (by rfl) ⟨7375994, by rfl⟩ : syracuseStep 9834659 = 14751989) B14751989
theorem B6556439 : Blo 2045435 6556439 := bstep (se 1 (by rfl) ⟨4917329, by rfl⟩ : syracuseStep 6556439 = 9834659) B9834659
theorem B4370959 : Blo 2045435 4370959 := bstep (se 1 (by rfl) ⟨3278219, by rfl⟩ : syracuseStep 4370959 = 6556439) B6556439
theorem B5827945 : Blo 2045435 5827945 := bstep (se 2 (by rfl) ⟨2185479, by rfl⟩ : syracuseStep 5827945 = 4370959) B4370959
theorem B7770593 : Blo 2045435 7770593 := bstep (se 2 (by rfl) ⟨2913972, by rfl⟩ : syracuseStep 7770593 = 5827945) B5827945
theorem B5180395 : Blo 2045435 5180395 := bstep (se 1 (by rfl) ⟨3885296, by rfl⟩ : syracuseStep 5180395 = 7770593) B7770593
theorem B6907193 : Blo 2045435 6907193 := bstep (se 2 (by rfl) ⟨2590197, by rfl⟩ : syracuseStep 6907193 = 5180395) B5180395
theorem B4604795 : Blo 2045435 4604795 := bstep (se 1 (by rfl) ⟨3453596, by rfl⟩ : syracuseStep 4604795 = 6907193) B6907193
theorem B3069863 : Blo 2045435 3069863 := bstep (se 1 (by rfl) ⟨2302397, by rfl⟩ : syracuseStep 3069863 = 4604795) B4604795
theorem B2046575 : Blo 2045435 2046575 := bstep (se 1 (by rfl) ⟨1534931, by rfl⟩ : syracuseStep 2046575 = 3069863) B3069863
theorem B3069869 : Blo 2045435 3069869 := bbase (se 3 (by rfl) ⟨575600, by rfl⟩ : syracuseStep 3069869 = 1151201) (by norm_num)
theorem B2046579 : Blo 2045435 2046579 := bstep (se 1 (by rfl) ⟨1534934, by rfl⟩ : syracuseStep 2046579 = 3069869) B3069869
theorem B4604813 : Blo 2045435 4604813 := bbase (se 3 (by rfl) ⟨863402, by rfl⟩ : syracuseStep 4604813 = 1726805) (by norm_num)
theorem B3069875 : Blo 2045435 3069875 := bstep (se 1 (by rfl) ⟨2302406, by rfl⟩ : syracuseStep 3069875 = 4604813) B4604813
theorem B2046583 : Blo 2045435 2046583 := bstep (se 1 (by rfl) ⟨1534937, by rfl⟩ : syracuseStep 2046583 = 3069875) B3069875
theorem B2590213 : Blo 2045435 2590213 := bbase (se 4 (by rfl) ⟨242832, by rfl⟩ : syracuseStep 2590213 = 485665) (by norm_num)
theorem B3453617 : Blo 2045435 3453617 := bstep (se 2 (by rfl) ⟨1295106, by rfl⟩ : syracuseStep 3453617 = 2590213) B2590213
theorem B2302411 : Blo 2045435 2302411 := bstep (se 1 (by rfl) ⟨1726808, by rfl⟩ : syracuseStep 2302411 = 3453617) B3453617
theorem B3069881 : Blo 2045435 3069881 := bstep (se 2 (by rfl) ⟨1151205, by rfl⟩ : syracuseStep 3069881 = 2302411) B2302411
theorem B2046587 : Blo 2045435 2046587 := bstep (se 1 (by rfl) ⟨1534940, by rfl⟩ : syracuseStep 2046587 = 3069881) B3069881
theorem B4149029 : Blo 2045435 4149029 := bbase (se 4 (by rfl) ⟨388971, by rfl⟩ : syracuseStep 4149029 = 777943) (by norm_num)
theorem B11064077 : Blo 2045435 11064077 := bstep (se 3 (by rfl) ⟨2074514, by rfl⟩ : syracuseStep 11064077 = 4149029) B4149029
theorem B7376051 : Blo 2045435 7376051 := bstep (se 1 (by rfl) ⟨5532038, by rfl⟩ : syracuseStep 7376051 = 11064077) B11064077
theorem B4917367 : Blo 2045435 4917367 := bstep (se 1 (by rfl) ⟨3688025, by rfl⟩ : syracuseStep 4917367 = 7376051) B7376051
theorem B26225957 : Blo 2045435 26225957 := bstep (se 4 (by rfl) ⟨2458683, by rfl⟩ : syracuseStep 26225957 = 4917367) B4917367
theorem B17483971 : Blo 2045435 17483971 := bstep (se 1 (by rfl) ⟨13112978, by rfl⟩ : syracuseStep 17483971 = 26225957) B26225957
theorem B23311961 : Blo 2045435 23311961 := bstep (se 2 (by rfl) ⟨8741985, by rfl⟩ : syracuseStep 23311961 = 17483971) B17483971
theorem B15541307 : Blo 2045435 15541307 := bstep (se 1 (by rfl) ⟨11655980, by rfl⟩ : syracuseStep 15541307 = 23311961) B23311961
theorem B10360871 : Blo 2045435 10360871 := bstep (se 1 (by rfl) ⟨7770653, by rfl⟩ : syracuseStep 10360871 = 15541307) B15541307
theorem B6907247 : Blo 2045435 6907247 := bstep (se 1 (by rfl) ⟨5180435, by rfl⟩ : syracuseStep 6907247 = 10360871) B10360871
theorem B4604831 : Blo 2045435 4604831 := bstep (se 1 (by rfl) ⟨3453623, by rfl⟩ : syracuseStep 4604831 = 6907247) B6907247
theorem B3069887 : Blo 2045435 3069887 := bstep (se 1 (by rfl) ⟨2302415, by rfl⟩ : syracuseStep 3069887 = 4604831) B4604831
theorem B2046591 : Blo 2045435 2046591 := bstep (se 1 (by rfl) ⟨1534943, by rfl⟩ : syracuseStep 2046591 = 3069887) B3069887
theorem B3069893 : Blo 2045435 3069893 := bbase (se 4 (by rfl) ⟨287802, by rfl⟩ : syracuseStep 3069893 = 575605) (by norm_num)
theorem B2046595 : Blo 2045435 2046595 := bstep (se 1 (by rfl) ⟨1534946, by rfl⟩ : syracuseStep 2046595 = 3069893) B3069893
theorem B3453637 : Blo 2045435 3453637 := bbase (se 4 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 3453637 = 647557) (by norm_num)
theorem B4604849 : Blo 2045435 4604849 := bstep (se 2 (by rfl) ⟨1726818, by rfl⟩ : syracuseStep 4604849 = 3453637) B3453637
theorem B3069899 : Blo 2045435 3069899 := bstep (se 1 (by rfl) ⟨2302424, by rfl⟩ : syracuseStep 3069899 = 4604849) B4604849
theorem B2046599 : Blo 2045435 2046599 := bstep (se 1 (by rfl) ⟨1534949, by rfl⟩ : syracuseStep 2046599 = 3069899) B3069899
theorem B2302429 : Blo 2045435 2302429 := bbase (se 3 (by rfl) ⟨431705, by rfl⟩ : syracuseStep 2302429 = 863411) (by norm_num)
theorem B3069905 : Blo 2045435 3069905 := bstep (se 2 (by rfl) ⟨1151214, by rfl⟩ : syracuseStep 3069905 = 2302429) B2302429
theorem B2046603 : Blo 2045435 2046603 := bstep (se 1 (by rfl) ⟨1534952, by rfl⟩ : syracuseStep 2046603 = 3069905) B3069905
theorem B6907301 : Blo 2045435 6907301 := bbase (se 4 (by rfl) ⟨647559, by rfl⟩ : syracuseStep 6907301 = 1295119) (by norm_num)
theorem B4604867 : Blo 2045435 4604867 := bstep (se 1 (by rfl) ⟨3453650, by rfl⟩ : syracuseStep 4604867 = 6907301) B6907301
theorem B3069911 : Blo 2045435 3069911 := bstep (se 1 (by rfl) ⟨2302433, by rfl⟩ : syracuseStep 3069911 = 4604867) B4604867
theorem B2046607 : Blo 2045435 2046607 := bstep (se 1 (by rfl) ⟨1534955, by rfl⟩ : syracuseStep 2046607 = 3069911) B3069911
theorem B3069917 : Blo 2045435 3069917 := bbase (se 3 (by rfl) ⟨575609, by rfl⟩ : syracuseStep 3069917 = 1151219) (by norm_num)
theorem B2046611 : Blo 2045435 2046611 := bstep (se 1 (by rfl) ⟨1534958, by rfl⟩ : syracuseStep 2046611 = 3069917) B3069917
theorem B4604885 : Blo 2045435 4604885 := bbase (se 7 (by rfl) ⟨53963, by rfl⟩ : syracuseStep 4604885 = 107927) (by norm_num)
theorem B3069923 : Blo 2045435 3069923 := bstep (se 1 (by rfl) ⟨2302442, by rfl⟩ : syracuseStep 3069923 = 4604885) B4604885
theorem B2046615 : Blo 2045435 2046615 := bstep (se 1 (by rfl) ⟨1534961, by rfl⟩ : syracuseStep 2046615 = 3069923) B3069923
theorem B5251189 : Blo 2045435 5251189 := bbase (se 5 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 5251189 = 492299) (by norm_num)
theorem B7001585 : Blo 2045435 7001585 := bstep (se 2 (by rfl) ⟨2625594, by rfl⟩ : syracuseStep 7001585 = 5251189) B5251189
theorem B4667723 : Blo 2045435 4667723 := bstep (se 1 (by rfl) ⟨3500792, by rfl⟩ : syracuseStep 4667723 = 7001585) B7001585
theorem B3111815 : Blo 2045435 3111815 := bstep (se 1 (by rfl) ⟨2333861, by rfl⟩ : syracuseStep 3111815 = 4667723) B4667723
theorem B8298173 : Blo 2045435 8298173 := bstep (se 3 (by rfl) ⟨1555907, by rfl⟩ : syracuseStep 8298173 = 3111815) B3111815
theorem B22128461 : Blo 2045435 22128461 := bstep (se 3 (by rfl) ⟨4149086, by rfl⟩ : syracuseStep 22128461 = 8298173) B8298173
theorem B14752307 : Blo 2045435 14752307 := bstep (se 1 (by rfl) ⟨11064230, by rfl⟩ : syracuseStep 14752307 = 22128461) B22128461
theorem B9834871 : Blo 2045435 9834871 := bstep (se 1 (by rfl) ⟨7376153, by rfl⟩ : syracuseStep 9834871 = 14752307) B14752307
theorem B13113161 : Blo 2045435 13113161 := bstep (se 2 (by rfl) ⟨4917435, by rfl⟩ : syracuseStep 13113161 = 9834871) B9834871
theorem B8742107 : Blo 2045435 8742107 := bstep (se 1 (by rfl) ⟨6556580, by rfl⟩ : syracuseStep 8742107 = 13113161) B13113161
theorem B5828071 : Blo 2045435 5828071 := bstep (se 1 (by rfl) ⟨4371053, by rfl⟩ : syracuseStep 5828071 = 8742107) B8742107
theorem B7770761 : Blo 2045435 7770761 := bstep (se 2 (by rfl) ⟨2914035, by rfl⟩ : syracuseStep 7770761 = 5828071) B5828071
theorem B5180507 : Blo 2045435 5180507 := bstep (se 1 (by rfl) ⟨3885380, by rfl⟩ : syracuseStep 5180507 = 7770761) B7770761
theorem B3453671 : Blo 2045435 3453671 := bstep (se 1 (by rfl) ⟨2590253, by rfl⟩ : syracuseStep 3453671 = 5180507) B5180507
theorem B2302447 : Blo 2045435 2302447 := bstep (se 1 (by rfl) ⟨1726835, by rfl⟩ : syracuseStep 2302447 = 3453671) B3453671
theorem B3069929 : Blo 2045435 3069929 := bstep (se 2 (by rfl) ⟨1151223, by rfl⟩ : syracuseStep 3069929 = 2302447) B2302447
theorem B2046619 : Blo 2045435 2046619 := bstep (se 1 (by rfl) ⟨1534964, by rfl⟩ : syracuseStep 2046619 = 3069929) B3069929
theorem B17484245 : Blo 2045435 17484245 := bbase (se 7 (by rfl) ⟨204893, by rfl⟩ : syracuseStep 17484245 = 409787) (by norm_num)
theorem B11656163 : Blo 2045435 11656163 := bstep (se 1 (by rfl) ⟨8742122, by rfl⟩ : syracuseStep 11656163 = 17484245) B17484245
theorem B7770775 : Blo 2045435 7770775 := bstep (se 1 (by rfl) ⟨5828081, by rfl⟩ : syracuseStep 7770775 = 11656163) B11656163
theorem B10361033 : Blo 2045435 10361033 := bstep (se 2 (by rfl) ⟨3885387, by rfl⟩ : syracuseStep 10361033 = 7770775) B7770775
theorem B6907355 : Blo 2045435 6907355 := bstep (se 1 (by rfl) ⟨5180516, by rfl⟩ : syracuseStep 6907355 = 10361033) B10361033
theorem B4604903 : Blo 2045435 4604903 := bstep (se 1 (by rfl) ⟨3453677, by rfl⟩ : syracuseStep 4604903 = 6907355) B6907355
theorem B3069935 : Blo 2045435 3069935 := bstep (se 1 (by rfl) ⟨2302451, by rfl⟩ : syracuseStep 3069935 = 4604903) B4604903
theorem B2046623 : Blo 2045435 2046623 := bstep (se 1 (by rfl) ⟨1534967, by rfl⟩ : syracuseStep 2046623 = 3069935) B3069935
theorem B3069941 : Blo 2045435 3069941 := bbase (se 5 (by rfl) ⟨143903, by rfl⟩ : syracuseStep 3069941 = 287807) (by norm_num)
theorem B2046627 : Blo 2045435 2046627 := bstep (se 1 (by rfl) ⟨1534970, by rfl⟩ : syracuseStep 2046627 = 3069941) B3069941
theorem B7376197 : Blo 2045435 7376197 := bbase (se 4 (by rfl) ⟨691518, by rfl⟩ : syracuseStep 7376197 = 1383037) (by norm_num)
theorem B9834929 : Blo 2045435 9834929 := bstep (se 2 (by rfl) ⟨3688098, by rfl⟩ : syracuseStep 9834929 = 7376197) B7376197
theorem B6556619 : Blo 2045435 6556619 := bstep (se 1 (by rfl) ⟨4917464, by rfl⟩ : syracuseStep 6556619 = 9834929) B9834929
theorem B4371079 : Blo 2045435 4371079 := bstep (se 1 (by rfl) ⟨3278309, by rfl⟩ : syracuseStep 4371079 = 6556619) B6556619
theorem B5828105 : Blo 2045435 5828105 := bstep (se 2 (by rfl) ⟨2185539, by rfl⟩ : syracuseStep 5828105 = 4371079) B4371079
theorem B3885403 : Blo 2045435 3885403 := bstep (se 1 (by rfl) ⟨2914052, by rfl⟩ : syracuseStep 3885403 = 5828105) B5828105
theorem B5180537 : Blo 2045435 5180537 := bstep (se 2 (by rfl) ⟨1942701, by rfl⟩ : syracuseStep 5180537 = 3885403) B3885403
theorem B3453691 : Blo 2045435 3453691 := bstep (se 1 (by rfl) ⟨2590268, by rfl⟩ : syracuseStep 3453691 = 5180537) B5180537
theorem B4604921 : Blo 2045435 4604921 := bstep (se 2 (by rfl) ⟨1726845, by rfl⟩ : syracuseStep 4604921 = 3453691) B3453691
theorem B3069947 : Blo 2045435 3069947 := bstep (se 1 (by rfl) ⟨2302460, by rfl⟩ : syracuseStep 3069947 = 4604921) B4604921
theorem B2046631 : Blo 2045435 2046631 := bstep (se 1 (by rfl) ⟨1534973, by rfl⟩ : syracuseStep 2046631 = 3069947) B3069947
theorem B2302465 : Blo 2045435 2302465 := bbase (se 2 (by rfl) ⟨863424, by rfl⟩ : syracuseStep 2302465 = 1726849) (by norm_num)
theorem B3069953 : Blo 2045435 3069953 := bstep (se 2 (by rfl) ⟨1151232, by rfl⟩ : syracuseStep 3069953 = 2302465) B2302465
theorem B2046635 : Blo 2045435 2046635 := bstep (se 1 (by rfl) ⟨1534976, by rfl⟩ : syracuseStep 2046635 = 3069953) B3069953
theorem B5180557 : Blo 2045435 5180557 := bbase (se 3 (by rfl) ⟨971354, by rfl⟩ : syracuseStep 5180557 = 1942709) (by norm_num)
theorem B6907409 : Blo 2045435 6907409 := bstep (se 2 (by rfl) ⟨2590278, by rfl⟩ : syracuseStep 6907409 = 5180557) B5180557
theorem B4604939 : Blo 2045435 4604939 := bstep (se 1 (by rfl) ⟨3453704, by rfl⟩ : syracuseStep 4604939 = 6907409) B6907409
theorem B3069959 : Blo 2045435 3069959 := bstep (se 1 (by rfl) ⟨2302469, by rfl⟩ : syracuseStep 3069959 = 4604939) B4604939
theorem B2046639 : Blo 2045435 2046639 := bstep (se 1 (by rfl) ⟨1534979, by rfl⟩ : syracuseStep 2046639 = 3069959) B3069959
theorem B3069965 : Blo 2045435 3069965 := bbase (se 3 (by rfl) ⟨575618, by rfl⟩ : syracuseStep 3069965 = 1151237) (by norm_num)
theorem B2046643 : Blo 2045435 2046643 := bstep (se 1 (by rfl) ⟨1534982, by rfl⟩ : syracuseStep 2046643 = 3069965) B3069965
theorem B4604957 : Blo 2045435 4604957 := bbase (se 3 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 4604957 = 1726859) (by norm_num)
theorem B3069971 : Blo 2045435 3069971 := bstep (se 1 (by rfl) ⟨2302478, by rfl⟩ : syracuseStep 3069971 = 4604957) B4604957
theorem B2046647 : Blo 2045435 2046647 := bstep (se 1 (by rfl) ⟨1534985, by rfl⟩ : syracuseStep 2046647 = 3069971) B3069971
theorem B3453725 : Blo 2045435 3453725 := bbase (se 3 (by rfl) ⟨647573, by rfl⟩ : syracuseStep 3453725 = 1295147) (by norm_num)
theorem B2302483 : Blo 2045435 2302483 := bstep (se 1 (by rfl) ⟨1726862, by rfl⟩ : syracuseStep 2302483 = 3453725) B3453725
theorem B3069977 : Blo 2045435 3069977 := bstep (se 2 (by rfl) ⟨1151241, by rfl⟩ : syracuseStep 3069977 = 2302483) B2302483
theorem B2046651 : Blo 2045435 2046651 := bstep (se 1 (by rfl) ⟨1534988, by rfl⟩ : syracuseStep 2046651 = 3069977) B3069977
theorem B3688141 : Blo 2045435 3688141 := bbase (se 3 (by rfl) ⟨691526, by rfl⟩ : syracuseStep 3688141 = 1383053) (by norm_num)
theorem B4917521 : Blo 2045435 4917521 := bstep (se 2 (by rfl) ⟨1844070, by rfl⟩ : syracuseStep 4917521 = 3688141) B3688141
theorem B13113389 : Blo 2045435 13113389 := bstep (se 3 (by rfl) ⟨2458760, by rfl⟩ : syracuseStep 13113389 = 4917521) B4917521
theorem B8742259 : Blo 2045435 8742259 := bstep (se 1 (by rfl) ⟨6556694, by rfl⟩ : syracuseStep 8742259 = 13113389) B13113389
theorem B11656345 : Blo 2045435 11656345 := bstep (se 2 (by rfl) ⟨4371129, by rfl⟩ : syracuseStep 11656345 = 8742259) B8742259
theorem B15541793 : Blo 2045435 15541793 := bstep (se 2 (by rfl) ⟨5828172, by rfl⟩ : syracuseStep 15541793 = 11656345) B11656345
theorem B10361195 : Blo 2045435 10361195 := bstep (se 1 (by rfl) ⟨7770896, by rfl⟩ : syracuseStep 10361195 = 15541793) B15541793
theorem B6907463 : Blo 2045435 6907463 := bstep (se 1 (by rfl) ⟨5180597, by rfl⟩ : syracuseStep 6907463 = 10361195) B10361195
theorem B4604975 : Blo 2045435 4604975 := bstep (se 1 (by rfl) ⟨3453731, by rfl⟩ : syracuseStep 4604975 = 6907463) B6907463
theorem B3069983 : Blo 2045435 3069983 := bstep (se 1 (by rfl) ⟨2302487, by rfl⟩ : syracuseStep 3069983 = 4604975) B4604975
theorem B2046655 : Blo 2045435 2046655 := bstep (se 1 (by rfl) ⟨1534991, by rfl⟩ : syracuseStep 2046655 = 3069983) B3069983
theorem B3069989 : Blo 2045435 3069989 := bbase (se 4 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 3069989 = 575623) (by norm_num)
theorem B2046659 : Blo 2045435 2046659 := bstep (se 1 (by rfl) ⟨1534994, by rfl⟩ : syracuseStep 2046659 = 3069989) B3069989
theorem B2590309 : Blo 2045435 2590309 := bbase (se 4 (by rfl) ⟨242841, by rfl⟩ : syracuseStep 2590309 = 485683) (by norm_num)
theorem B3453745 : Blo 2045435 3453745 := bstep (se 2 (by rfl) ⟨1295154, by rfl⟩ : syracuseStep 3453745 = 2590309) B2590309
theorem B4604993 : Blo 2045435 4604993 := bstep (se 2 (by rfl) ⟨1726872, by rfl⟩ : syracuseStep 4604993 = 3453745) B3453745
theorem B3069995 : Blo 2045435 3069995 := bstep (se 1 (by rfl) ⟨2302496, by rfl⟩ : syracuseStep 3069995 = 4604993) B4604993
theorem B2046663 : Blo 2045435 2046663 := bstep (se 1 (by rfl) ⟨1534997, by rfl⟩ : syracuseStep 2046663 = 3069995) B3069995
theorem B2302501 : Blo 2045435 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B3070001 : Blo 2045435 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B2046667 : Blo 2045435 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B7376341 : Blo 2045435 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B9835121 : Blo 2045435 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B6556747 : Blo 2045435 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B8742329 : Blo 2045435 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B5828219 : Blo 2045435 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B3885479 : Blo 2045435 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B2590319 : Blo 2045435 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B6907517 : Blo 2045435 6907517 := bstep (se 3 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 6907517 = 2590319) B2590319
theorem B4605011 : Blo 2045435 4605011 := bstep (se 1 (by rfl) ⟨3453758, by rfl⟩ : syracuseStep 4605011 = 6907517) B6907517
theorem B3070007 : Blo 2045435 3070007 := bstep (se 1 (by rfl) ⟨2302505, by rfl⟩ : syracuseStep 3070007 = 4605011) B4605011
theorem B2046671 : Blo 2045435 2046671 := bstep (se 1 (by rfl) ⟨1535003, by rfl⟩ : syracuseStep 2046671 = 3070007) B3070007
theorem B3070013 : Blo 2045435 3070013 := bbase (se 3 (by rfl) ⟨575627, by rfl⟩ : syracuseStep 3070013 = 1151255) (by norm_num)
theorem B2046675 : Blo 2045435 2046675 := bstep (se 1 (by rfl) ⟨1535006, by rfl⟩ : syracuseStep 2046675 = 3070013) B3070013
theorem B4605029 : Blo 2045435 4605029 := bbase (se 4 (by rfl) ⟨431721, by rfl⟩ : syracuseStep 4605029 = 863443) (by norm_num)
theorem B3070019 : Blo 2045435 3070019 := bstep (se 1 (by rfl) ⟨2302514, by rfl⟩ : syracuseStep 3070019 = 4605029) B4605029
theorem B2046679 : Blo 2045435 2046679 := bstep (se 1 (by rfl) ⟨1535009, by rfl⟩ : syracuseStep 2046679 = 3070019) B3070019
theorem B5180669 : Blo 2045435 5180669 := bbase (se 3 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 5180669 = 1942751) (by norm_num)
theorem B3453779 : Blo 2045435 3453779 := bstep (se 1 (by rfl) ⟨2590334, by rfl⟩ : syracuseStep 3453779 = 5180669) B5180669
theorem B2302519 : Blo 2045435 2302519 := bstep (se 1 (by rfl) ⟨1726889, by rfl⟩ : syracuseStep 2302519 = 3453779) B3453779
theorem B3070025 : Blo 2045435 3070025 := bstep (se 2 (by rfl) ⟨1151259, by rfl⟩ : syracuseStep 3070025 = 2302519) B2302519
theorem B2046683 : Blo 2045435 2046683 := bstep (se 1 (by rfl) ⟨1535012, by rfl⟩ : syracuseStep 2046683 = 3070025) B3070025
theorem B3885509 : Blo 2045435 3885509 := bbase (se 4 (by rfl) ⟨364266, by rfl⟩ : syracuseStep 3885509 = 728533) (by norm_num)
theorem B10361357 : Blo 2045435 10361357 := bstep (se 3 (by rfl) ⟨1942754, by rfl⟩ : syracuseStep 10361357 = 3885509) B3885509
theorem B6907571 : Blo 2045435 6907571 := bstep (se 1 (by rfl) ⟨5180678, by rfl⟩ : syracuseStep 6907571 = 10361357) B10361357
theorem B4605047 : Blo 2045435 4605047 := bstep (se 1 (by rfl) ⟨3453785, by rfl⟩ : syracuseStep 4605047 = 6907571) B6907571
theorem B3070031 : Blo 2045435 3070031 := bstep (se 1 (by rfl) ⟨2302523, by rfl⟩ : syracuseStep 3070031 = 4605047) B4605047
theorem B2046687 : Blo 2045435 2046687 := bstep (se 1 (by rfl) ⟨1535015, by rfl⟩ : syracuseStep 2046687 = 3070031) B3070031
theorem B3070037 : Blo 2045435 3070037 := bbase (se 8 (by rfl) ⟨17988, by rfl⟩ : syracuseStep 3070037 = 35977) (by norm_num)
theorem B2046691 : Blo 2045435 2046691 := bstep (se 1 (by rfl) ⟨1535018, by rfl⟩ : syracuseStep 2046691 = 3070037) B3070037
theorem B2803901 : Blo 2045435 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B7477069 : Blo 2045435 7477069 := bstep (se 3 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 7477069 = 2803901) B2803901
theorem B9969425 : Blo 2045435 9969425 := bstep (se 2 (by rfl) ⟨3738534, by rfl⟩ : syracuseStep 9969425 = 7477069) B7477069
theorem B6646283 : Blo 2045435 6646283 := bstep (se 1 (by rfl) ⟨4984712, by rfl⟩ : syracuseStep 6646283 = 9969425) B9969425
theorem B4430855 : Blo 2045435 4430855 := bstep (se 1 (by rfl) ⟨3323141, by rfl⟩ : syracuseStep 4430855 = 6646283) B6646283
theorem B2953903 : Blo 2045435 2953903 := bstep (se 1 (by rfl) ⟨2215427, by rfl⟩ : syracuseStep 2953903 = 4430855) B4430855
theorem B3938537 : Blo 2045435 3938537 := bstep (se 2 (by rfl) ⟨1476951, by rfl⟩ : syracuseStep 3938537 = 2953903) B2953903
theorem B10502765 : Blo 2045435 10502765 := bstep (se 3 (by rfl) ⟨1969268, by rfl⟩ : syracuseStep 10502765 = 3938537) B3938537
theorem B7001843 : Blo 2045435 7001843 := bstep (se 1 (by rfl) ⟨5251382, by rfl⟩ : syracuseStep 7001843 = 10502765) B10502765
theorem B18671581 : Blo 2045435 18671581 := bstep (se 3 (by rfl) ⟨3500921, by rfl⟩ : syracuseStep 18671581 = 7001843) B7001843
theorem B24895441 : Blo 2045435 24895441 := bstep (se 2 (by rfl) ⟨9335790, by rfl⟩ : syracuseStep 24895441 = 18671581) B18671581
theorem B33193921 : Blo 2045435 33193921 := bstep (se 2 (by rfl) ⟨12447720, by rfl⟩ : syracuseStep 33193921 = 24895441) B24895441
theorem B44258561 : Blo 2045435 44258561 := bstep (se 2 (by rfl) ⟨16596960, by rfl⟩ : syracuseStep 44258561 = 33193921) B33193921
theorem B29505707 : Blo 2045435 29505707 := bstep (se 1 (by rfl) ⟨22129280, by rfl⟩ : syracuseStep 29505707 = 44258561) B44258561
theorem B19670471 : Blo 2045435 19670471 := bstep (se 1 (by rfl) ⟨14752853, by rfl⟩ : syracuseStep 19670471 = 29505707) B29505707
theorem B13113647 : Blo 2045435 13113647 := bstep (se 1 (by rfl) ⟨9835235, by rfl⟩ : syracuseStep 13113647 = 19670471) B19670471
theorem B8742431 : Blo 2045435 8742431 := bstep (se 1 (by rfl) ⟨6556823, by rfl⟩ : syracuseStep 8742431 = 13113647) B13113647
theorem B5828287 : Blo 2045435 5828287 := bstep (se 1 (by rfl) ⟨4371215, by rfl⟩ : syracuseStep 5828287 = 8742431) B8742431
theorem B7771049 : Blo 2045435 7771049 := bstep (se 2 (by rfl) ⟨2914143, by rfl⟩ : syracuseStep 7771049 = 5828287) B5828287
theorem B5180699 : Blo 2045435 5180699 := bstep (se 1 (by rfl) ⟨3885524, by rfl⟩ : syracuseStep 5180699 = 7771049) B7771049
theorem B3453799 : Blo 2045435 3453799 := bstep (se 1 (by rfl) ⟨2590349, by rfl⟩ : syracuseStep 3453799 = 5180699) B5180699
theorem B4605065 : Blo 2045435 4605065 := bstep (se 2 (by rfl) ⟨1726899, by rfl⟩ : syracuseStep 4605065 = 3453799) B3453799
theorem B3070043 : Blo 2045435 3070043 := bstep (se 1 (by rfl) ⟨2302532, by rfl⟩ : syracuseStep 3070043 = 4605065) B4605065
theorem B2046695 : Blo 2045435 2046695 := bstep (se 1 (by rfl) ⟨1535021, by rfl⟩ : syracuseStep 2046695 = 3070043) B3070043
theorem B2302537 : Blo 2045435 2302537 := bbase (se 2 (by rfl) ⟨863451, by rfl⟩ : syracuseStep 2302537 = 1726903) (by norm_num)
theorem B3070049 : Blo 2045435 3070049 := bstep (se 2 (by rfl) ⟨1151268, by rfl⟩ : syracuseStep 3070049 = 2302537) B2302537
theorem B2046699 : Blo 2045435 2046699 := bstep (se 1 (by rfl) ⟨1535024, by rfl⟩ : syracuseStep 2046699 = 3070049) B3070049
theorem B5907829 : Blo 2045435 5907829 := bbase (se 5 (by rfl) ⟨276929, by rfl⟩ : syracuseStep 5907829 = 553859) (by norm_num)
theorem B7877105 : Blo 2045435 7877105 := bstep (se 2 (by rfl) ⟨2953914, by rfl⟩ : syracuseStep 7877105 = 5907829) B5907829
theorem B5251403 : Blo 2045435 5251403 := bstep (se 1 (by rfl) ⟨3938552, by rfl⟩ : syracuseStep 5251403 = 7877105) B7877105
theorem B14003741 : Blo 2045435 14003741 := bstep (se 3 (by rfl) ⟨2625701, by rfl⟩ : syracuseStep 14003741 = 5251403) B5251403
theorem B9335827 : Blo 2045435 9335827 := bstep (se 1 (by rfl) ⟨7001870, by rfl⟩ : syracuseStep 9335827 = 14003741) B14003741
theorem B12447769 : Blo 2045435 12447769 := bstep (se 2 (by rfl) ⟨4667913, by rfl⟩ : syracuseStep 12447769 = 9335827) B9335827
theorem B16597025 : Blo 2045435 16597025 := bstep (se 2 (by rfl) ⟨6223884, by rfl⟩ : syracuseStep 16597025 = 12447769) B12447769
theorem B11064683 : Blo 2045435 11064683 := bstep (se 1 (by rfl) ⟨8298512, by rfl⟩ : syracuseStep 11064683 = 16597025) B16597025
theorem B7376455 : Blo 2045435 7376455 := bstep (se 1 (by rfl) ⟨5532341, by rfl⟩ : syracuseStep 7376455 = 11064683) B11064683
theorem B9835273 : Blo 2045435 9835273 := bstep (se 2 (by rfl) ⟨3688227, by rfl⟩ : syracuseStep 9835273 = 7376455) B7376455
theorem B13113697 : Blo 2045435 13113697 := bstep (se 2 (by rfl) ⟨4917636, by rfl⟩ : syracuseStep 13113697 = 9835273) B9835273
theorem B17484929 : Blo 2045435 17484929 := bstep (se 2 (by rfl) ⟨6556848, by rfl⟩ : syracuseStep 17484929 = 13113697) B13113697
theorem B11656619 : Blo 2045435 11656619 := bstep (se 1 (by rfl) ⟨8742464, by rfl⟩ : syracuseStep 11656619 = 17484929) B17484929
theorem B7771079 : Blo 2045435 7771079 := bstep (se 1 (by rfl) ⟨5828309, by rfl⟩ : syracuseStep 7771079 = 11656619) B11656619
theorem B5180719 : Blo 2045435 5180719 := bstep (se 1 (by rfl) ⟨3885539, by rfl⟩ : syracuseStep 5180719 = 7771079) B7771079
theorem B6907625 : Blo 2045435 6907625 := bstep (se 2 (by rfl) ⟨2590359, by rfl⟩ : syracuseStep 6907625 = 5180719) B5180719
theorem B4605083 : Blo 2045435 4605083 := bstep (se 1 (by rfl) ⟨3453812, by rfl⟩ : syracuseStep 4605083 = 6907625) B6907625
theorem B3070055 : Blo 2045435 3070055 := bstep (se 1 (by rfl) ⟨2302541, by rfl⟩ : syracuseStep 3070055 = 4605083) B4605083
theorem B2046703 : Blo 2045435 2046703 := bstep (se 1 (by rfl) ⟨1535027, by rfl⟩ : syracuseStep 2046703 = 3070055) B3070055
theorem B3070061 : Blo 2045435 3070061 := bbase (se 3 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 3070061 = 1151273) (by norm_num)
theorem B2046707 : Blo 2045435 2046707 := bstep (se 1 (by rfl) ⟨1535030, by rfl⟩ : syracuseStep 2046707 = 3070061) B3070061
theorem B4605101 : Blo 2045435 4605101 := bbase (se 3 (by rfl) ⟨863456, by rfl⟩ : syracuseStep 4605101 = 1726913) (by norm_num)
theorem B3070067 : Blo 2045435 3070067 := bstep (se 1 (by rfl) ⟨2302550, by rfl⟩ : syracuseStep 3070067 = 4605101) B4605101
theorem B2046711 : Blo 2045435 2046711 := bstep (se 1 (by rfl) ⟨1535033, by rfl⟩ : syracuseStep 2046711 = 3070067) B3070067
theorem B7376501 : Blo 2045435 7376501 := bbase (se 5 (by rfl) ⟨345773, by rfl⟩ : syracuseStep 7376501 = 691547) (by norm_num)
theorem B4917667 : Blo 2045435 4917667 := bstep (se 1 (by rfl) ⟨3688250, by rfl⟩ : syracuseStep 4917667 = 7376501) B7376501
theorem B6556889 : Blo 2045435 6556889 := bstep (se 2 (by rfl) ⟨2458833, by rfl⟩ : syracuseStep 6556889 = 4917667) B4917667
theorem B4371259 : Blo 2045435 4371259 := bstep (se 1 (by rfl) ⟨3278444, by rfl⟩ : syracuseStep 4371259 = 6556889) B6556889
theorem B5828345 : Blo 2045435 5828345 := bstep (se 2 (by rfl) ⟨2185629, by rfl⟩ : syracuseStep 5828345 = 4371259) B4371259
theorem B3885563 : Blo 2045435 3885563 := bstep (se 1 (by rfl) ⟨2914172, by rfl⟩ : syracuseStep 3885563 = 5828345) B5828345
theorem B2590375 : Blo 2045435 2590375 := bstep (se 1 (by rfl) ⟨1942781, by rfl⟩ : syracuseStep 2590375 = 3885563) B3885563
theorem B3453833 : Blo 2045435 3453833 := bstep (se 2 (by rfl) ⟨1295187, by rfl⟩ : syracuseStep 3453833 = 2590375) B2590375
theorem B2302555 : Blo 2045435 2302555 := bstep (se 1 (by rfl) ⟨1726916, by rfl⟩ : syracuseStep 2302555 = 3453833) B3453833
theorem B3070073 : Blo 2045435 3070073 := bstep (se 2 (by rfl) ⟨1151277, by rfl⟩ : syracuseStep 3070073 = 2302555) B2302555
theorem B2046715 : Blo 2045435 2046715 := bstep (se 1 (by rfl) ⟨1535036, by rfl⟩ : syracuseStep 2046715 = 3070073) B3070073
theorem B9835349 : Blo 2045435 9835349 := bbase (se 9 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 9835349 = 57629) (by norm_num)
theorem B26227597 : Blo 2045435 26227597 := bstep (se 3 (by rfl) ⟨4917674, by rfl⟩ : syracuseStep 26227597 = 9835349) B9835349
theorem B34970129 : Blo 2045435 34970129 := bstep (se 2 (by rfl) ⟨13113798, by rfl⟩ : syracuseStep 34970129 = 26227597) B26227597
theorem B23313419 : Blo 2045435 23313419 := bstep (se 1 (by rfl) ⟨17485064, by rfl⟩ : syracuseStep 23313419 = 34970129) B34970129
theorem B15542279 : Blo 2045435 15542279 := bstep (se 1 (by rfl) ⟨11656709, by rfl⟩ : syracuseStep 15542279 = 23313419) B23313419
theorem B10361519 : Blo 2045435 10361519 := bstep (se 1 (by rfl) ⟨7771139, by rfl⟩ : syracuseStep 10361519 = 15542279) B15542279
theorem B6907679 : Blo 2045435 6907679 := bstep (se 1 (by rfl) ⟨5180759, by rfl⟩ : syracuseStep 6907679 = 10361519) B10361519
theorem B4605119 : Blo 2045435 4605119 := bstep (se 1 (by rfl) ⟨3453839, by rfl⟩ : syracuseStep 4605119 = 6907679) B6907679
theorem B3070079 : Blo 2045435 3070079 := bstep (se 1 (by rfl) ⟨2302559, by rfl⟩ : syracuseStep 3070079 = 4605119) B4605119
theorem B2046719 : Blo 2045435 2046719 := bstep (se 1 (by rfl) ⟨1535039, by rfl⟩ : syracuseStep 2046719 = 3070079) B3070079
theorem B3070085 : Blo 2045435 3070085 := bbase (se 4 (by rfl) ⟨287820, by rfl⟩ : syracuseStep 3070085 = 575641) (by norm_num)
theorem B2046723 : Blo 2045435 2046723 := bstep (se 1 (by rfl) ⟨1535042, by rfl⟩ : syracuseStep 2046723 = 3070085) B3070085
theorem B3453853 : Blo 2045435 3453853 := bbase (se 3 (by rfl) ⟨647597, by rfl⟩ : syracuseStep 3453853 = 1295195) (by norm_num)
theorem B4605137 : Blo 2045435 4605137 := bstep (se 2 (by rfl) ⟨1726926, by rfl⟩ : syracuseStep 4605137 = 3453853) B3453853
theorem B3070091 : Blo 2045435 3070091 := bstep (se 1 (by rfl) ⟨2302568, by rfl⟩ : syracuseStep 3070091 = 4605137) B4605137
theorem B2046727 : Blo 2045435 2046727 := bstep (se 1 (by rfl) ⟨1535045, by rfl⟩ : syracuseStep 2046727 = 3070091) B3070091
theorem B2302573 : Blo 2045435 2302573 := bbase (se 3 (by rfl) ⟨431732, by rfl⟩ : syracuseStep 2302573 = 863465) (by norm_num)
theorem B3070097 : Blo 2045435 3070097 := bstep (se 2 (by rfl) ⟨1151286, by rfl⟩ : syracuseStep 3070097 = 2302573) B2302573
theorem B2046731 : Blo 2045435 2046731 := bstep (se 1 (by rfl) ⟨1535048, by rfl⟩ : syracuseStep 2046731 = 3070097) B3070097
theorem B6907733 : Blo 2045435 6907733 := bbase (se 9 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 6907733 = 40475) (by norm_num)
theorem B4605155 : Blo 2045435 4605155 := bstep (se 1 (by rfl) ⟨3453866, by rfl⟩ : syracuseStep 4605155 = 6907733) B6907733
theorem B3070103 : Blo 2045435 3070103 := bstep (se 1 (by rfl) ⟨2302577, by rfl⟩ : syracuseStep 3070103 = 4605155) B4605155
theorem B2046735 : Blo 2045435 2046735 := bstep (se 1 (by rfl) ⟨1535051, by rfl⟩ : syracuseStep 2046735 = 3070103) B3070103
theorem B3070109 : Blo 2045435 3070109 := bbase (se 3 (by rfl) ⟨575645, by rfl⟩ : syracuseStep 3070109 = 1151291) (by norm_num)
theorem B2046739 : Blo 2045435 2046739 := bstep (se 1 (by rfl) ⟨1535054, by rfl⟩ : syracuseStep 2046739 = 3070109) B3070109
theorem B4605173 : Blo 2045435 4605173 := bbase (se 5 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 4605173 = 431735) (by norm_num)
theorem B3070115 : Blo 2045435 3070115 := bstep (se 1 (by rfl) ⟨2302586, by rfl⟩ : syracuseStep 3070115 = 4605173) B4605173
theorem B2046743 : Blo 2045435 2046743 := bstep (se 1 (by rfl) ⟨1535057, by rfl⟩ : syracuseStep 2046743 = 3070115) B3070115
theorem B5251517 : Blo 2045435 5251517 := bbase (se 3 (by rfl) ⟨984659, by rfl⟩ : syracuseStep 5251517 = 1969319) (by norm_num)
theorem B3501011 : Blo 2045435 3501011 := bstep (se 1 (by rfl) ⟨2625758, by rfl⟩ : syracuseStep 3501011 = 5251517) B5251517
theorem B2334007 : Blo 2045435 2334007 := bstep (se 1 (by rfl) ⟨1750505, by rfl⟩ : syracuseStep 2334007 = 3501011) B3501011
theorem B12448037 : Blo 2045435 12448037 := bstep (se 4 (by rfl) ⟨1167003, by rfl⟩ : syracuseStep 12448037 = 2334007) B2334007
theorem B33194765 : Blo 2045435 33194765 := bstep (se 3 (by rfl) ⟨6224018, by rfl⟩ : syracuseStep 33194765 = 12448037) B12448037
theorem B22129843 : Blo 2045435 22129843 := bstep (se 1 (by rfl) ⟨16597382, by rfl⟩ : syracuseStep 22129843 = 33194765) B33194765
theorem B29506457 : Blo 2045435 29506457 := bstep (se 2 (by rfl) ⟨11064921, by rfl⟩ : syracuseStep 29506457 = 22129843) B22129843
theorem B19670971 : Blo 2045435 19670971 := bstep (se 1 (by rfl) ⟨14753228, by rfl⟩ : syracuseStep 19670971 = 29506457) B29506457
theorem B26227961 : Blo 2045435 26227961 := bstep (se 2 (by rfl) ⟨9835485, by rfl⟩ : syracuseStep 26227961 = 19670971) B19670971
theorem B17485307 : Blo 2045435 17485307 := bstep (se 1 (by rfl) ⟨13113980, by rfl⟩ : syracuseStep 17485307 = 26227961) B26227961
theorem B11656871 : Blo 2045435 11656871 := bstep (se 1 (by rfl) ⟨8742653, by rfl⟩ : syracuseStep 11656871 = 17485307) B17485307
theorem B7771247 : Blo 2045435 7771247 := bstep (se 1 (by rfl) ⟨5828435, by rfl⟩ : syracuseStep 7771247 = 11656871) B11656871
theorem B5180831 : Blo 2045435 5180831 := bstep (se 1 (by rfl) ⟨3885623, by rfl⟩ : syracuseStep 5180831 = 7771247) B7771247
theorem B3453887 : Blo 2045435 3453887 := bstep (se 1 (by rfl) ⟨2590415, by rfl⟩ : syracuseStep 3453887 = 5180831) B5180831
theorem B2302591 : Blo 2045435 2302591 := bstep (se 1 (by rfl) ⟨1726943, by rfl⟩ : syracuseStep 2302591 = 3453887) B3453887
theorem B3070121 : Blo 2045435 3070121 := bstep (se 2 (by rfl) ⟨1151295, by rfl⟩ : syracuseStep 3070121 = 2302591) B2302591
theorem B2046747 : Blo 2045435 2046747 := bstep (se 1 (by rfl) ⟨1535060, by rfl⟩ : syracuseStep 2046747 = 3070121) B3070121
theorem B7376629 : Blo 2045435 7376629 := bbase (se 5 (by rfl) ⟨345779, by rfl⟩ : syracuseStep 7376629 = 691559) (by norm_num)
theorem B9835505 : Blo 2045435 9835505 := bstep (se 2 (by rfl) ⟨3688314, by rfl⟩ : syracuseStep 9835505 = 7376629) B7376629
theorem B6557003 : Blo 2045435 6557003 := bstep (se 1 (by rfl) ⟨4917752, by rfl⟩ : syracuseStep 6557003 = 9835505) B9835505
theorem B4371335 : Blo 2045435 4371335 := bstep (se 1 (by rfl) ⟨3278501, by rfl⟩ : syracuseStep 4371335 = 6557003) B6557003
theorem B2914223 : Blo 2045435 2914223 := bstep (se 1 (by rfl) ⟨2185667, by rfl⟩ : syracuseStep 2914223 = 4371335) B4371335
theorem B7771261 : Blo 2045435 7771261 := bstep (se 3 (by rfl) ⟨1457111, by rfl⟩ : syracuseStep 7771261 = 2914223) B2914223
theorem B10361681 : Blo 2045435 10361681 := bstep (se 2 (by rfl) ⟨3885630, by rfl⟩ : syracuseStep 10361681 = 7771261) B7771261
theorem B6907787 : Blo 2045435 6907787 := bstep (se 1 (by rfl) ⟨5180840, by rfl⟩ : syracuseStep 6907787 = 10361681) B10361681
theorem B4605191 : Blo 2045435 4605191 := bstep (se 1 (by rfl) ⟨3453893, by rfl⟩ : syracuseStep 4605191 = 6907787) B6907787
theorem B3070127 : Blo 2045435 3070127 := bstep (se 1 (by rfl) ⟨2302595, by rfl⟩ : syracuseStep 3070127 = 4605191) B4605191
theorem B2046751 : Blo 2045435 2046751 := bstep (se 1 (by rfl) ⟨1535063, by rfl⟩ : syracuseStep 2046751 = 3070127) B3070127
theorem B3070133 : Blo 2045435 3070133 := bbase (se 5 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 3070133 = 287825) (by norm_num)
theorem B2046755 : Blo 2045435 2046755 := bstep (se 1 (by rfl) ⟨1535066, by rfl⟩ : syracuseStep 2046755 = 3070133) B3070133
theorem B5180861 : Blo 2045435 5180861 := bbase (se 3 (by rfl) ⟨971411, by rfl⟩ : syracuseStep 5180861 = 1942823) (by norm_num)
theorem B3453907 : Blo 2045435 3453907 := bstep (se 1 (by rfl) ⟨2590430, by rfl⟩ : syracuseStep 3453907 = 5180861) B5180861
theorem B4605209 : Blo 2045435 4605209 := bstep (se 2 (by rfl) ⟨1726953, by rfl⟩ : syracuseStep 4605209 = 3453907) B3453907
theorem B3070139 : Blo 2045435 3070139 := bstep (se 1 (by rfl) ⟨2302604, by rfl⟩ : syracuseStep 3070139 = 4605209) B4605209
theorem B2046759 : Blo 2045435 2046759 := bstep (se 1 (by rfl) ⟨1535069, by rfl⟩ : syracuseStep 2046759 = 3070139) B3070139
theorem B2302609 : Blo 2045435 2302609 := bbase (se 2 (by rfl) ⟨863478, by rfl⟩ : syracuseStep 2302609 = 1726957) (by norm_num)
theorem B3070145 : Blo 2045435 3070145 := bstep (se 2 (by rfl) ⟨1151304, by rfl⟩ : syracuseStep 3070145 = 2302609) B2302609
theorem B2046763 : Blo 2045435 2046763 := bstep (se 1 (by rfl) ⟨1535072, by rfl⟩ : syracuseStep 2046763 = 3070145) B3070145
theorem B3885661 : Blo 2045435 3885661 := bbase (se 3 (by rfl) ⟨728561, by rfl⟩ : syracuseStep 3885661 = 1457123) (by norm_num)
theorem B5180881 : Blo 2045435 5180881 := bstep (se 2 (by rfl) ⟨1942830, by rfl⟩ : syracuseStep 5180881 = 3885661) B3885661
theorem B6907841 : Blo 2045435 6907841 := bstep (se 2 (by rfl) ⟨2590440, by rfl⟩ : syracuseStep 6907841 = 5180881) B5180881
theorem B4605227 : Blo 2045435 4605227 := bstep (se 1 (by rfl) ⟨3453920, by rfl⟩ : syracuseStep 4605227 = 6907841) B6907841
theorem B3070151 : Blo 2045435 3070151 := bstep (se 1 (by rfl) ⟨2302613, by rfl⟩ : syracuseStep 3070151 = 4605227) B4605227
theorem B2046767 : Blo 2045435 2046767 := bstep (se 1 (by rfl) ⟨1535075, by rfl⟩ : syracuseStep 2046767 = 3070151) B3070151
theorem B3070157 : Blo 2045435 3070157 := bbase (se 3 (by rfl) ⟨575654, by rfl⟩ : syracuseStep 3070157 = 1151309) (by norm_num)
theorem B2046771 : Blo 2045435 2046771 := bstep (se 1 (by rfl) ⟨1535078, by rfl⟩ : syracuseStep 2046771 = 3070157) B3070157
theorem B4605245 : Blo 2045435 4605245 := bbase (se 3 (by rfl) ⟨863483, by rfl⟩ : syracuseStep 4605245 = 1726967) (by norm_num)
theorem B3070163 : Blo 2045435 3070163 := bstep (se 1 (by rfl) ⟨2302622, by rfl⟩ : syracuseStep 3070163 = 4605245) B4605245
theorem B2046775 : Blo 2045435 2046775 := bstep (se 1 (by rfl) ⟨1535081, by rfl⟩ : syracuseStep 2046775 = 3070163) B3070163
theorem B3453941 : Blo 2045435 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B2302627 : Blo 2045435 2302627 := bstep (se 1 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 2302627 = 3453941) B3453941
theorem B3070169 : Blo 2045435 3070169 := bstep (se 2 (by rfl) ⟨1151313, by rfl⟩ : syracuseStep 3070169 = 2302627) B2302627
theorem B2046779 : Blo 2045435 2046779 := bstep (se 1 (by rfl) ⟨1535084, by rfl⟩ : syracuseStep 2046779 = 3070169) B3070169
theorem B4917829 : Blo 2045435 4917829 := bbase (se 4 (by rfl) ⟨461046, by rfl⟩ : syracuseStep 4917829 = 922093) (by norm_num)
theorem B6557105 : Blo 2045435 6557105 := bstep (se 2 (by rfl) ⟨2458914, by rfl⟩ : syracuseStep 6557105 = 4917829) B4917829
theorem B4371403 : Blo 2045435 4371403 := bstep (se 1 (by rfl) ⟨3278552, by rfl⟩ : syracuseStep 4371403 = 6557105) B6557105
theorem B5828537 : Blo 2045435 5828537 := bstep (se 2 (by rfl) ⟨2185701, by rfl⟩ : syracuseStep 5828537 = 4371403) B4371403
theorem B15542765 : Blo 2045435 15542765 := bstep (se 3 (by rfl) ⟨2914268, by rfl⟩ : syracuseStep 15542765 = 5828537) B5828537
theorem B10361843 : Blo 2045435 10361843 := bstep (se 1 (by rfl) ⟨7771382, by rfl⟩ : syracuseStep 10361843 = 15542765) B15542765
theorem B6907895 : Blo 2045435 6907895 := bstep (se 1 (by rfl) ⟨5180921, by rfl⟩ : syracuseStep 6907895 = 10361843) B10361843
theorem B4605263 : Blo 2045435 4605263 := bstep (se 1 (by rfl) ⟨3453947, by rfl⟩ : syracuseStep 4605263 = 6907895) B6907895
theorem B3070175 : Blo 2045435 3070175 := bstep (se 1 (by rfl) ⟨2302631, by rfl⟩ : syracuseStep 3070175 = 4605263) B4605263
theorem B2046783 : Blo 2045435 2046783 := bstep (se 1 (by rfl) ⟨1535087, by rfl⟩ : syracuseStep 2046783 = 3070175) B3070175
theorem B3070181 : Blo 2045435 3070181 := bbase (se 4 (by rfl) ⟨287829, by rfl⟩ : syracuseStep 3070181 = 575659) (by norm_num)
theorem B2046787 : Blo 2045435 2046787 := bstep (se 1 (by rfl) ⟨1535090, by rfl⟩ : syracuseStep 2046787 = 3070181) B3070181
theorem B4371421 : Blo 2045435 4371421 := bbase (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) (by norm_num)
theorem B5828561 : Blo 2045435 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B3885707 : Blo 2045435 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B2590471 : Blo 2045435 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B3453961 : Blo 2045435 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B4605281 : Blo 2045435 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B3070187 : Blo 2045435 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B2046791 : Blo 2045435 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B2302645 : Blo 2045435 2302645 := bbase (se 5 (by rfl) ⟨107936, by rfl⟩ : syracuseStep 2302645 = 215873) (by norm_num)
theorem B3070193 : Blo 2045435 3070193 := bstep (se 2 (by rfl) ⟨1151322, by rfl⟩ : syracuseStep 3070193 = 2302645) B2302645
theorem B2046795 : Blo 2045435 2046795 := bstep (se 1 (by rfl) ⟨1535096, by rfl⟩ : syracuseStep 2046795 = 3070193) B3070193
theorem B2590481 : Blo 2045435 2590481 := bbase (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) (by norm_num)
theorem B6907949 : Blo 2045435 6907949 := bstep (se 3 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 6907949 = 2590481) B2590481
theorem B4605299 : Blo 2045435 4605299 := bstep (se 1 (by rfl) ⟨3453974, by rfl⟩ : syracuseStep 4605299 = 6907949) B6907949
theorem B3070199 : Blo 2045435 3070199 := bstep (se 1 (by rfl) ⟨2302649, by rfl⟩ : syracuseStep 3070199 = 4605299) B4605299
theorem B2046799 : Blo 2045435 2046799 := bstep (se 1 (by rfl) ⟨1535099, by rfl⟩ : syracuseStep 2046799 = 3070199) B3070199
theorem B3070205 : Blo 2045435 3070205 := bbase (se 3 (by rfl) ⟨575663, by rfl⟩ : syracuseStep 3070205 = 1151327) (by norm_num)
theorem B2046803 : Blo 2045435 2046803 := bstep (se 1 (by rfl) ⟨1535102, by rfl⟩ : syracuseStep 2046803 = 3070205) B3070205
theorem B4605317 : Blo 2045435 4605317 := bbase (se 4 (by rfl) ⟨431748, by rfl⟩ : syracuseStep 4605317 = 863497) (by norm_num)
theorem B3070211 : Blo 2045435 3070211 := bstep (se 1 (by rfl) ⟨2302658, by rfl⟩ : syracuseStep 3070211 = 4605317) B4605317
theorem B2046807 : Blo 2045435 2046807 := bstep (se 1 (by rfl) ⟨1535105, by rfl⟩ : syracuseStep 2046807 = 3070211) B3070211
theorem B2914309 : Blo 2045435 2914309 := bbase (se 4 (by rfl) ⟨273216, by rfl⟩ : syracuseStep 2914309 = 546433) (by norm_num)
theorem B3885745 : Blo 2045435 3885745 := bstep (se 2 (by rfl) ⟨1457154, by rfl⟩ : syracuseStep 3885745 = 2914309) B2914309
theorem B5180993 : Blo 2045435 5180993 := bstep (se 2 (by rfl) ⟨1942872, by rfl⟩ : syracuseStep 5180993 = 3885745) B3885745
theorem B3453995 : Blo 2045435 3453995 := bstep (se 1 (by rfl) ⟨2590496, by rfl⟩ : syracuseStep 3453995 = 5180993) B5180993
theorem B2302663 : Blo 2045435 2302663 := bstep (se 1 (by rfl) ⟨1726997, by rfl⟩ : syracuseStep 2302663 = 3453995) B3453995
theorem B3070217 : Blo 2045435 3070217 := bstep (se 2 (by rfl) ⟨1151331, by rfl⟩ : syracuseStep 3070217 = 2302663) B2302663
theorem B2046811 : Blo 2045435 2046811 := bstep (se 1 (by rfl) ⟨1535108, by rfl⟩ : syracuseStep 2046811 = 3070217) B3070217
theorem B10362005 : Blo 2045435 10362005 := bbase (se 6 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 10362005 = 485719) (by norm_num)
theorem B6908003 : Blo 2045435 6908003 := bstep (se 1 (by rfl) ⟨5181002, by rfl⟩ : syracuseStep 6908003 = 10362005) B10362005
theorem B4605335 : Blo 2045435 4605335 := bstep (se 1 (by rfl) ⟨3454001, by rfl⟩ : syracuseStep 4605335 = 6908003) B6908003
theorem B3070223 : Blo 2045435 3070223 := bstep (se 1 (by rfl) ⟨2302667, by rfl⟩ : syracuseStep 3070223 = 4605335) B4605335
theorem B2046815 : Blo 2045435 2046815 := bstep (se 1 (by rfl) ⟨1535111, by rfl⟩ : syracuseStep 2046815 = 3070223) B3070223
theorem B3070229 : Blo 2045435 3070229 := bbase (se 6 (by rfl) ⟨71958, by rfl⟩ : syracuseStep 3070229 = 143917) (by norm_num)
theorem B2046819 : Blo 2045435 2046819 := bstep (se 1 (by rfl) ⟨1535114, by rfl⟩ : syracuseStep 2046819 = 3070229) B3070229
theorem B4917925 : Blo 2045435 4917925 := bbase (se 4 (by rfl) ⟨461055, by rfl⟩ : syracuseStep 4917925 = 922111) (by norm_num)
theorem B26228933 : Blo 2045435 26228933 := bstep (se 4 (by rfl) ⟨2458962, by rfl⟩ : syracuseStep 26228933 = 4917925) B4917925
theorem B17485955 : Blo 2045435 17485955 := bstep (se 1 (by rfl) ⟨13114466, by rfl⟩ : syracuseStep 17485955 = 26228933) B26228933
theorem B11657303 : Blo 2045435 11657303 := bstep (se 1 (by rfl) ⟨8742977, by rfl⟩ : syracuseStep 11657303 = 17485955) B17485955
theorem B7771535 : Blo 2045435 7771535 := bstep (se 1 (by rfl) ⟨5828651, by rfl⟩ : syracuseStep 7771535 = 11657303) B11657303
theorem B5181023 : Blo 2045435 5181023 := bstep (se 1 (by rfl) ⟨3885767, by rfl⟩ : syracuseStep 5181023 = 7771535) B7771535
theorem B3454015 : Blo 2045435 3454015 := bstep (se 1 (by rfl) ⟨2590511, by rfl⟩ : syracuseStep 3454015 = 5181023) B5181023
theorem B4605353 : Blo 2045435 4605353 := bstep (se 2 (by rfl) ⟨1727007, by rfl⟩ : syracuseStep 4605353 = 3454015) B3454015
theorem B3070235 : Blo 2045435 3070235 := bstep (se 1 (by rfl) ⟨2302676, by rfl⟩ : syracuseStep 3070235 = 4605353) B4605353
theorem B2046823 : Blo 2045435 2046823 := bstep (se 1 (by rfl) ⟨1535117, by rfl⟩ : syracuseStep 2046823 = 3070235) B3070235
theorem B2302681 : Blo 2045435 2302681 := bbase (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) (by norm_num)
theorem B3070241 : Blo 2045435 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B2046827 : Blo 2045435 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B2185753 : Blo 2045435 2185753 := bbase (se 2 (by rfl) ⟨819657, by rfl⟩ : syracuseStep 2185753 = 1639315) (by norm_num)
theorem B2914337 : Blo 2045435 2914337 := bstep (se 2 (by rfl) ⟨1092876, by rfl⟩ : syracuseStep 2914337 = 2185753) B2185753
theorem B7771565 : Blo 2045435 7771565 := bstep (se 3 (by rfl) ⟨1457168, by rfl⟩ : syracuseStep 7771565 = 2914337) B2914337
theorem B5181043 : Blo 2045435 5181043 := bstep (se 1 (by rfl) ⟨3885782, by rfl⟩ : syracuseStep 5181043 = 7771565) B7771565
theorem B6908057 : Blo 2045435 6908057 := bstep (se 2 (by rfl) ⟨2590521, by rfl⟩ : syracuseStep 6908057 = 5181043) B5181043
theorem B4605371 : Blo 2045435 4605371 := bstep (se 1 (by rfl) ⟨3454028, by rfl⟩ : syracuseStep 4605371 = 6908057) B6908057
theorem B3070247 : Blo 2045435 3070247 := bstep (se 1 (by rfl) ⟨2302685, by rfl⟩ : syracuseStep 3070247 = 4605371) B4605371
theorem B2046831 : Blo 2045435 2046831 := bstep (se 1 (by rfl) ⟨1535123, by rfl⟩ : syracuseStep 2046831 = 3070247) B3070247
theorem B3070253 : Blo 2045435 3070253 := bbase (se 3 (by rfl) ⟨575672, by rfl⟩ : syracuseStep 3070253 = 1151345) (by norm_num)
theorem B2046835 : Blo 2045435 2046835 := bstep (se 1 (by rfl) ⟨1535126, by rfl⟩ : syracuseStep 2046835 = 3070253) B3070253
theorem B4605389 : Blo 2045435 4605389 := bbase (se 3 (by rfl) ⟨863510, by rfl⟩ : syracuseStep 4605389 = 1727021) (by norm_num)
theorem B3070259 : Blo 2045435 3070259 := bstep (se 1 (by rfl) ⟨2302694, by rfl⟩ : syracuseStep 3070259 = 4605389) B4605389
theorem B2046839 : Blo 2045435 2046839 := bstep (se 1 (by rfl) ⟨1535129, by rfl⟩ : syracuseStep 2046839 = 3070259) B3070259
theorem B2590537 : Blo 2045435 2590537 := bbase (se 2 (by rfl) ⟨971451, by rfl⟩ : syracuseStep 2590537 = 1942903) (by norm_num)
theorem B3454049 : Blo 2045435 3454049 := bstep (se 2 (by rfl) ⟨1295268, by rfl⟩ : syracuseStep 3454049 = 2590537) B2590537
theorem B2302699 : Blo 2045435 2302699 := bstep (se 1 (by rfl) ⟨1727024, by rfl⟩ : syracuseStep 2302699 = 3454049) B3454049
theorem B3070265 : Blo 2045435 3070265 := bstep (se 2 (by rfl) ⟨1151349, by rfl⟩ : syracuseStep 3070265 = 2302699) B2302699
theorem B2046843 : Blo 2045435 2046843 := bstep (se 1 (by rfl) ⟨1535132, by rfl⟩ : syracuseStep 2046843 = 3070265) B3070265
theorem B7985141 : Blo 2045435 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B5323427 : Blo 2045435 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B3548951 : Blo 2045435 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B2365967 : Blo 2045435 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B6309245 : Blo 2045435 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B4206163 : Blo 2045435 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B5608217 : Blo 2045435 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B3738811 : Blo 2045435 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B4985081 : Blo 2045435 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B3323387 : Blo 2045435 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B8862365 : Blo 2045435 8862365 := bstep (se 3 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 8862365 = 3323387) B3323387
theorem B23632973 : Blo 2045435 23632973 := bstep (se 3 (by rfl) ⟨4431182, by rfl⟩ : syracuseStep 23632973 = 8862365) B8862365
theorem B15755315 : Blo 2045435 15755315 := bstep (se 1 (by rfl) ⟨11816486, by rfl⟩ : syracuseStep 15755315 = 23632973) B23632973
theorem B42014173 : Blo 2045435 42014173 := bstep (se 3 (by rfl) ⟨7877657, by rfl⟩ : syracuseStep 42014173 = 15755315) B15755315
theorem B56018897 : Blo 2045435 56018897 := bstep (se 2 (by rfl) ⟨21007086, by rfl⟩ : syracuseStep 56018897 = 42014173) B42014173
theorem B37345931 : Blo 2045435 37345931 := bstep (se 1 (by rfl) ⟨28009448, by rfl⟩ : syracuseStep 37345931 = 56018897) B56018897
theorem B24897287 : Blo 2045435 24897287 := bstep (se 1 (by rfl) ⟨18672965, by rfl⟩ : syracuseStep 24897287 = 37345931) B37345931
theorem B16598191 : Blo 2045435 16598191 := bstep (se 1 (by rfl) ⟨12448643, by rfl⟩ : syracuseStep 16598191 = 24897287) B24897287
theorem B22130921 : Blo 2045435 22130921 := bstep (se 2 (by rfl) ⟨8299095, by rfl⟩ : syracuseStep 22130921 = 16598191) B16598191
theorem B14753947 : Blo 2045435 14753947 := bstep (se 1 (by rfl) ⟨11065460, by rfl⟩ : syracuseStep 14753947 = 22130921) B22130921
theorem B19671929 : Blo 2045435 19671929 := bstep (se 2 (by rfl) ⟨7376973, by rfl⟩ : syracuseStep 19671929 = 14753947) B14753947
theorem B13114619 : Blo 2045435 13114619 := bstep (se 1 (by rfl) ⟨9835964, by rfl⟩ : syracuseStep 13114619 = 19671929) B19671929
theorem B8743079 : Blo 2045435 8743079 := bstep (se 1 (by rfl) ⟨6557309, by rfl⟩ : syracuseStep 8743079 = 13114619) B13114619
theorem B23314877 : Blo 2045435 23314877 := bstep (se 3 (by rfl) ⟨4371539, by rfl⟩ : syracuseStep 23314877 = 8743079) B8743079
theorem B15543251 : Blo 2045435 15543251 := bstep (se 1 (by rfl) ⟨11657438, by rfl⟩ : syracuseStep 15543251 = 23314877) B23314877
theorem B10362167 : Blo 2045435 10362167 := bstep (se 1 (by rfl) ⟨7771625, by rfl⟩ : syracuseStep 10362167 = 15543251) B15543251
theorem B6908111 : Blo 2045435 6908111 := bstep (se 1 (by rfl) ⟨5181083, by rfl⟩ : syracuseStep 6908111 = 10362167) B10362167
theorem B4605407 : Blo 2045435 4605407 := bstep (se 1 (by rfl) ⟨3454055, by rfl⟩ : syracuseStep 4605407 = 6908111) B6908111
theorem B3070271 : Blo 2045435 3070271 := bstep (se 1 (by rfl) ⟨2302703, by rfl⟩ : syracuseStep 3070271 = 4605407) B4605407
theorem B2046847 : Blo 2045435 2046847 := bstep (se 1 (by rfl) ⟨1535135, by rfl⟩ : syracuseStep 2046847 = 3070271) B3070271
theorem B3070277 : Blo 2045435 3070277 := bbase (se 4 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 3070277 = 575677) (by norm_num)
theorem B2046851 : Blo 2045435 2046851 := bstep (se 1 (by rfl) ⟨1535138, by rfl⟩ : syracuseStep 2046851 = 3070277) B3070277
theorem B3454069 : Blo 2045435 3454069 := bbase (se 5 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 3454069 = 323819) (by norm_num)
theorem B4605425 : Blo 2045435 4605425 := bstep (se 2 (by rfl) ⟨1727034, by rfl⟩ : syracuseStep 4605425 = 3454069) B3454069
theorem B3070283 : Blo 2045435 3070283 := bstep (se 1 (by rfl) ⟨2302712, by rfl⟩ : syracuseStep 3070283 = 4605425) B4605425
theorem B2046855 : Blo 2045435 2046855 := bstep (se 1 (by rfl) ⟨1535141, by rfl⟩ : syracuseStep 2046855 = 3070283) B3070283
theorem B2302717 : Blo 2045435 2302717 := bbase (se 3 (by rfl) ⟨431759, by rfl⟩ : syracuseStep 2302717 = 863519) (by norm_num)
theorem B3070289 : Blo 2045435 3070289 := bstep (se 2 (by rfl) ⟨1151358, by rfl⟩ : syracuseStep 3070289 = 2302717) B2302717
theorem B2046859 : Blo 2045435 2046859 := bstep (se 1 (by rfl) ⟨1535144, by rfl⟩ : syracuseStep 2046859 = 3070289) B3070289
theorem B6908165 : Blo 2045435 6908165 := bbase (se 4 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 6908165 = 1295281) (by norm_num)
theorem B4605443 : Blo 2045435 4605443 := bstep (se 1 (by rfl) ⟨3454082, by rfl⟩ : syracuseStep 4605443 = 6908165) B6908165
theorem B3070295 : Blo 2045435 3070295 := bstep (se 1 (by rfl) ⟨2302721, by rfl⟩ : syracuseStep 3070295 = 4605443) B4605443
theorem B2046863 : Blo 2045435 2046863 := bstep (se 1 (by rfl) ⟨1535147, by rfl⟩ : syracuseStep 2046863 = 3070295) B3070295
theorem B3070301 : Blo 2045435 3070301 := bbase (se 3 (by rfl) ⟨575681, by rfl⟩ : syracuseStep 3070301 = 1151363) (by norm_num)
theorem B2046867 : Blo 2045435 2046867 := bstep (se 1 (by rfl) ⟨1535150, by rfl⟩ : syracuseStep 2046867 = 3070301) B3070301
theorem B4605461 : Blo 2045435 4605461 := bbase (se 6 (by rfl) ⟨107940, by rfl⟩ : syracuseStep 4605461 = 215881) (by norm_num)
theorem B3070307 : Blo 2045435 3070307 := bstep (se 1 (by rfl) ⟨2302730, by rfl⟩ : syracuseStep 3070307 = 4605461) B4605461
theorem B2046871 : Blo 2045435 2046871 := bstep (se 1 (by rfl) ⟨1535153, by rfl⟩ : syracuseStep 2046871 = 3070307) B3070307
theorem B7771733 : Blo 2045435 7771733 := bbase (se 8 (by rfl) ⟨45537, by rfl⟩ : syracuseStep 7771733 = 91075) (by norm_num)
theorem B5181155 : Blo 2045435 5181155 := bstep (se 1 (by rfl) ⟨3885866, by rfl⟩ : syracuseStep 5181155 = 7771733) B7771733
theorem B3454103 : Blo 2045435 3454103 := bstep (se 1 (by rfl) ⟨2590577, by rfl⟩ : syracuseStep 3454103 = 5181155) B5181155
theorem B2302735 : Blo 2045435 2302735 := bstep (se 1 (by rfl) ⟨1727051, by rfl⟩ : syracuseStep 2302735 = 3454103) B3454103
theorem B3070313 : Blo 2045435 3070313 := bstep (se 2 (by rfl) ⟨1151367, by rfl⟩ : syracuseStep 3070313 = 2302735) B2302735
theorem B2046875 : Blo 2045435 2046875 := bstep (se 1 (by rfl) ⟨1535156, by rfl⟩ : syracuseStep 2046875 = 3070313) B3070313
theorem B11657621 : Blo 2045435 11657621 := bbase (se 6 (by rfl) ⟨273225, by rfl⟩ : syracuseStep 11657621 = 546451) (by norm_num)
theorem B7771747 : Blo 2045435 7771747 := bstep (se 1 (by rfl) ⟨5828810, by rfl⟩ : syracuseStep 7771747 = 11657621) B11657621
theorem B10362329 : Blo 2045435 10362329 := bstep (se 2 (by rfl) ⟨3885873, by rfl⟩ : syracuseStep 10362329 = 7771747) B7771747
theorem B6908219 : Blo 2045435 6908219 := bstep (se 1 (by rfl) ⟨5181164, by rfl⟩ : syracuseStep 6908219 = 10362329) B10362329
theorem B4605479 : Blo 2045435 4605479 := bstep (se 1 (by rfl) ⟨3454109, by rfl⟩ : syracuseStep 4605479 = 6908219) B6908219
theorem B3070319 : Blo 2045435 3070319 := bstep (se 1 (by rfl) ⟨2302739, by rfl⟩ : syracuseStep 3070319 = 4605479) B4605479
theorem B2046879 : Blo 2045435 2046879 := bstep (se 1 (by rfl) ⟨1535159, by rfl⟩ : syracuseStep 2046879 = 3070319) B3070319
theorem B3070325 : Blo 2045435 3070325 := bbase (se 5 (by rfl) ⟨143921, by rfl⟩ : syracuseStep 3070325 = 287843) (by norm_num)
theorem B2046883 : Blo 2045435 2046883 := bstep (se 1 (by rfl) ⟨1535162, by rfl⟩ : syracuseStep 2046883 = 3070325) B3070325
theorem B2185813 : Blo 2045435 2185813 := bbase (se 8 (by rfl) ⟨12807, by rfl⟩ : syracuseStep 2185813 = 25615) (by norm_num)
theorem B2914417 : Blo 2045435 2914417 := bstep (se 2 (by rfl) ⟨1092906, by rfl⟩ : syracuseStep 2914417 = 2185813) B2185813
theorem B3885889 : Blo 2045435 3885889 := bstep (se 2 (by rfl) ⟨1457208, by rfl⟩ : syracuseStep 3885889 = 2914417) B2914417
theorem B5181185 : Blo 2045435 5181185 := bstep (se 2 (by rfl) ⟨1942944, by rfl⟩ : syracuseStep 5181185 = 3885889) B3885889
theorem B3454123 : Blo 2045435 3454123 := bstep (se 1 (by rfl) ⟨2590592, by rfl⟩ : syracuseStep 3454123 = 5181185) B5181185
theorem B4605497 : Blo 2045435 4605497 := bstep (se 2 (by rfl) ⟨1727061, by rfl⟩ : syracuseStep 4605497 = 3454123) B3454123
theorem B3070331 : Blo 2045435 3070331 := bstep (se 1 (by rfl) ⟨2302748, by rfl⟩ : syracuseStep 3070331 = 4605497) B4605497
theorem B2046887 : Blo 2045435 2046887 := bstep (se 1 (by rfl) ⟨1535165, by rfl⟩ : syracuseStep 2046887 = 3070331) B3070331
theorem B2302753 : Blo 2045435 2302753 := bbase (se 2 (by rfl) ⟨863532, by rfl⟩ : syracuseStep 2302753 = 1727065) (by norm_num)
theorem B3070337 : Blo 2045435 3070337 := bstep (se 2 (by rfl) ⟨1151376, by rfl⟩ : syracuseStep 3070337 = 2302753) B2302753
theorem B2046891 : Blo 2045435 2046891 := bstep (se 1 (by rfl) ⟨1535168, by rfl⟩ : syracuseStep 2046891 = 3070337) B3070337
theorem B5181205 : Blo 2045435 5181205 := bbase (se 6 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 5181205 = 242869) (by norm_num)
theorem B6908273 : Blo 2045435 6908273 := bstep (se 2 (by rfl) ⟨2590602, by rfl⟩ : syracuseStep 6908273 = 5181205) B5181205
theorem B4605515 : Blo 2045435 4605515 := bstep (se 1 (by rfl) ⟨3454136, by rfl⟩ : syracuseStep 4605515 = 6908273) B6908273
theorem B3070343 : Blo 2045435 3070343 := bstep (se 1 (by rfl) ⟨2302757, by rfl⟩ : syracuseStep 3070343 = 4605515) B4605515
theorem B2046895 : Blo 2045435 2046895 := bstep (se 1 (by rfl) ⟨1535171, by rfl⟩ : syracuseStep 2046895 = 3070343) B3070343
theorem B3070349 : Blo 2045435 3070349 := bbase (se 3 (by rfl) ⟨575690, by rfl⟩ : syracuseStep 3070349 = 1151381) (by norm_num)
theorem B2046899 : Blo 2045435 2046899 := bstep (se 1 (by rfl) ⟨1535174, by rfl⟩ : syracuseStep 2046899 = 3070349) B3070349
theorem B4605533 : Blo 2045435 4605533 := bbase (se 3 (by rfl) ⟨863537, by rfl⟩ : syracuseStep 4605533 = 1727075) (by norm_num)
theorem B3070355 : Blo 2045435 3070355 := bstep (se 1 (by rfl) ⟨2302766, by rfl⟩ : syracuseStep 3070355 = 4605533) B4605533
theorem B2046903 : Blo 2045435 2046903 := bstep (se 1 (by rfl) ⟨1535177, by rfl⟩ : syracuseStep 2046903 = 3070355) B3070355
theorem B3454157 : Blo 2045435 3454157 := bbase (se 3 (by rfl) ⟨647654, by rfl⟩ : syracuseStep 3454157 = 1295309) (by norm_num)
theorem B2302771 : Blo 2045435 2302771 := bstep (se 1 (by rfl) ⟨1727078, by rfl⟩ : syracuseStep 2302771 = 3454157) B3454157
theorem B3070361 : Blo 2045435 3070361 := bstep (se 2 (by rfl) ⟨1151385, by rfl⟩ : syracuseStep 3070361 = 2302771) B2302771
theorem B2046907 : Blo 2045435 2046907 := bstep (se 1 (by rfl) ⟨1535180, by rfl⟩ : syracuseStep 2046907 = 3070361) B3070361
theorem B13115029 : Blo 2045435 13115029 := bbase (se 6 (by rfl) ⟨307383, by rfl⟩ : syracuseStep 13115029 = 614767) (by norm_num)
theorem B17486705 : Blo 2045435 17486705 := bstep (se 2 (by rfl) ⟨6557514, by rfl⟩ : syracuseStep 17486705 = 13115029) B13115029
theorem B11657803 : Blo 2045435 11657803 := bstep (se 1 (by rfl) ⟨8743352, by rfl⟩ : syracuseStep 11657803 = 17486705) B17486705
theorem B15543737 : Blo 2045435 15543737 := bstep (se 2 (by rfl) ⟨5828901, by rfl⟩ : syracuseStep 15543737 = 11657803) B11657803
theorem B10362491 : Blo 2045435 10362491 := bstep (se 1 (by rfl) ⟨7771868, by rfl⟩ : syracuseStep 10362491 = 15543737) B15543737
theorem B6908327 : Blo 2045435 6908327 := bstep (se 1 (by rfl) ⟨5181245, by rfl⟩ : syracuseStep 6908327 = 10362491) B10362491
theorem B4605551 : Blo 2045435 4605551 := bstep (se 1 (by rfl) ⟨3454163, by rfl⟩ : syracuseStep 4605551 = 6908327) B6908327
theorem B3070367 : Blo 2045435 3070367 := bstep (se 1 (by rfl) ⟨2302775, by rfl⟩ : syracuseStep 3070367 = 4605551) B4605551
theorem B2046911 : Blo 2045435 2046911 := bstep (se 1 (by rfl) ⟨1535183, by rfl⟩ : syracuseStep 2046911 = 3070367) B3070367
theorem B3070373 : Blo 2045435 3070373 := bbase (se 4 (by rfl) ⟨287847, by rfl⟩ : syracuseStep 3070373 = 575695) (by norm_num)
theorem B2046915 : Blo 2045435 2046915 := bstep (se 1 (by rfl) ⟨1535186, by rfl⟩ : syracuseStep 2046915 = 3070373) B3070373
theorem B2590633 : Blo 2045435 2590633 := bbase (se 2 (by rfl) ⟨971487, by rfl⟩ : syracuseStep 2590633 = 1942975) (by norm_num)
theorem B3454177 : Blo 2045435 3454177 := bstep (se 2 (by rfl) ⟨1295316, by rfl⟩ : syracuseStep 3454177 = 2590633) B2590633
theorem B4605569 : Blo 2045435 4605569 := bstep (se 2 (by rfl) ⟨1727088, by rfl⟩ : syracuseStep 4605569 = 3454177) B3454177
theorem B3070379 : Blo 2045435 3070379 := bstep (se 1 (by rfl) ⟨2302784, by rfl⟩ : syracuseStep 3070379 = 4605569) B4605569
theorem B2046919 : Blo 2045435 2046919 := bstep (se 1 (by rfl) ⟨1535189, by rfl⟩ : syracuseStep 2046919 = 3070379) B3070379
theorem B2302789 : Blo 2045435 2302789 := bbase (se 4 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 2302789 = 431773) (by norm_num)
theorem B3070385 : Blo 2045435 3070385 := bstep (se 2 (by rfl) ⟨1151394, by rfl⟩ : syracuseStep 3070385 = 2302789) B2302789
theorem B2046923 : Blo 2045435 2046923 := bstep (se 1 (by rfl) ⟨1535192, by rfl⟩ : syracuseStep 2046923 = 3070385) B3070385
theorem B3885965 : Blo 2045435 3885965 := bbase (se 3 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 3885965 = 1457237) (by norm_num)
theorem B2590643 : Blo 2045435 2590643 := bstep (se 1 (by rfl) ⟨1942982, by rfl⟩ : syracuseStep 2590643 = 3885965) B3885965
theorem B6908381 : Blo 2045435 6908381 := bstep (se 3 (by rfl) ⟨1295321, by rfl⟩ : syracuseStep 6908381 = 2590643) B2590643
theorem B4605587 : Blo 2045435 4605587 := bstep (se 1 (by rfl) ⟨3454190, by rfl⟩ : syracuseStep 4605587 = 6908381) B6908381
theorem B3070391 : Blo 2045435 3070391 := bstep (se 1 (by rfl) ⟨2302793, by rfl⟩ : syracuseStep 3070391 = 4605587) B4605587
theorem B2046927 : Blo 2045435 2046927 := bstep (se 1 (by rfl) ⟨1535195, by rfl⟩ : syracuseStep 2046927 = 3070391) B3070391
theorem B3070397 : Blo 2045435 3070397 := bbase (se 3 (by rfl) ⟨575699, by rfl⟩ : syracuseStep 3070397 = 1151399) (by norm_num)
theorem B2046931 : Blo 2045435 2046931 := bstep (se 1 (by rfl) ⟨1535198, by rfl⟩ : syracuseStep 2046931 = 3070397) B3070397
theorem B4605605 : Blo 2045435 4605605 := bbase (se 4 (by rfl) ⟨431775, by rfl⟩ : syracuseStep 4605605 = 863551) (by norm_num)
theorem B3070403 : Blo 2045435 3070403 := bstep (se 1 (by rfl) ⟨2302802, by rfl⟩ : syracuseStep 3070403 = 4605605) B4605605
theorem B2046935 : Blo 2045435 2046935 := bstep (se 1 (by rfl) ⟨1535201, by rfl⟩ : syracuseStep 2046935 = 3070403) B3070403
theorem B5181317 : Blo 2045435 5181317 := bbase (se 4 (by rfl) ⟨485748, by rfl⟩ : syracuseStep 5181317 = 971497) (by norm_num)
theorem B3454211 : Blo 2045435 3454211 := bstep (se 1 (by rfl) ⟨2590658, by rfl⟩ : syracuseStep 3454211 = 5181317) B5181317
theorem B2302807 : Blo 2045435 2302807 := bstep (se 1 (by rfl) ⟨1727105, by rfl⟩ : syracuseStep 2302807 = 3454211) B3454211
theorem B3070409 : Blo 2045435 3070409 := bstep (se 2 (by rfl) ⟨1151403, by rfl⟩ : syracuseStep 3070409 = 2302807) B2302807
theorem B2046939 : Blo 2045435 2046939 := bstep (se 1 (by rfl) ⟨1535204, by rfl⟩ : syracuseStep 2046939 = 3070409) B3070409
theorem B3688661 : Blo 2045435 3688661 := bbase (se 7 (by rfl) ⟨43226, by rfl⟩ : syracuseStep 3688661 = 86453) (by norm_num)
theorem B2459107 : Blo 2045435 2459107 := bstep (se 1 (by rfl) ⟨1844330, by rfl⟩ : syracuseStep 2459107 = 3688661) B3688661
theorem B3278809 : Blo 2045435 3278809 := bstep (se 2 (by rfl) ⟨1229553, by rfl⟩ : syracuseStep 3278809 = 2459107) B2459107
theorem B4371745 : Blo 2045435 4371745 := bstep (se 2 (by rfl) ⟨1639404, by rfl⟩ : syracuseStep 4371745 = 3278809) B3278809
theorem B5828993 : Blo 2045435 5828993 := bstep (se 2 (by rfl) ⟨2185872, by rfl⟩ : syracuseStep 5828993 = 4371745) B4371745
theorem B3885995 : Blo 2045435 3885995 := bstep (se 1 (by rfl) ⟨2914496, by rfl⟩ : syracuseStep 3885995 = 5828993) B5828993
theorem B10362653 : Blo 2045435 10362653 := bstep (se 3 (by rfl) ⟨1942997, by rfl⟩ : syracuseStep 10362653 = 3885995) B3885995
theorem B6908435 : Blo 2045435 6908435 := bstep (se 1 (by rfl) ⟨5181326, by rfl⟩ : syracuseStep 6908435 = 10362653) B10362653
theorem B4605623 : Blo 2045435 4605623 := bstep (se 1 (by rfl) ⟨3454217, by rfl⟩ : syracuseStep 4605623 = 6908435) B6908435
theorem B3070415 : Blo 2045435 3070415 := bstep (se 1 (by rfl) ⟨2302811, by rfl⟩ : syracuseStep 3070415 = 4605623) B4605623
theorem B2046943 : Blo 2045435 2046943 := bstep (se 1 (by rfl) ⟨1535207, by rfl⟩ : syracuseStep 2046943 = 3070415) B3070415
theorem B3070421 : Blo 2045435 3070421 := bbase (se 7 (by rfl) ⟨35981, by rfl⟩ : syracuseStep 3070421 = 71963) (by norm_num)
theorem B2046947 : Blo 2045435 2046947 := bstep (se 1 (by rfl) ⟨1535210, by rfl⟩ : syracuseStep 2046947 = 3070421) B3070421
theorem B7772021 : Blo 2045435 7772021 := bbase (se 5 (by rfl) ⟨364313, by rfl⟩ : syracuseStep 7772021 = 728627) (by norm_num)
theorem B5181347 : Blo 2045435 5181347 := bstep (se 1 (by rfl) ⟨3886010, by rfl⟩ : syracuseStep 5181347 = 7772021) B7772021
theorem B3454231 : Blo 2045435 3454231 := bstep (se 1 (by rfl) ⟨2590673, by rfl⟩ : syracuseStep 3454231 = 5181347) B5181347
theorem B4605641 : Blo 2045435 4605641 := bstep (se 2 (by rfl) ⟨1727115, by rfl⟩ : syracuseStep 4605641 = 3454231) B3454231
theorem B3070427 : Blo 2045435 3070427 := bstep (se 1 (by rfl) ⟨2302820, by rfl⟩ : syracuseStep 3070427 = 4605641) B4605641
theorem B2046951 : Blo 2045435 2046951 := bstep (se 1 (by rfl) ⟨1535213, by rfl⟩ : syracuseStep 2046951 = 3070427) B3070427
theorem B2302825 : Blo 2045435 2302825 := bbase (se 2 (by rfl) ⟨863559, by rfl⟩ : syracuseStep 2302825 = 1727119) (by norm_num)
theorem B3070433 : Blo 2045435 3070433 := bstep (se 2 (by rfl) ⟨1151412, by rfl⟩ : syracuseStep 3070433 = 2302825) B2302825
theorem B2046955 : Blo 2045435 2046955 := bstep (se 1 (by rfl) ⟨1535216, by rfl⟩ : syracuseStep 2046955 = 3070433) B3070433
theorem B6557669 : Blo 2045435 6557669 := bbase (se 4 (by rfl) ⟨614781, by rfl⟩ : syracuseStep 6557669 = 1229563) (by norm_num)
theorem B4371779 : Blo 2045435 4371779 := bstep (se 1 (by rfl) ⟨3278834, by rfl⟩ : syracuseStep 4371779 = 6557669) B6557669
theorem B11658077 : Blo 2045435 11658077 := bstep (se 3 (by rfl) ⟨2185889, by rfl⟩ : syracuseStep 11658077 = 4371779) B4371779
theorem B7772051 : Blo 2045435 7772051 := bstep (se 1 (by rfl) ⟨5829038, by rfl⟩ : syracuseStep 7772051 = 11658077) B11658077
theorem B5181367 : Blo 2045435 5181367 := bstep (se 1 (by rfl) ⟨3886025, by rfl⟩ : syracuseStep 5181367 = 7772051) B7772051
theorem B6908489 : Blo 2045435 6908489 := bstep (se 2 (by rfl) ⟨2590683, by rfl⟩ : syracuseStep 6908489 = 5181367) B5181367
theorem B4605659 : Blo 2045435 4605659 := bstep (se 1 (by rfl) ⟨3454244, by rfl⟩ : syracuseStep 4605659 = 6908489) B6908489
theorem B3070439 : Blo 2045435 3070439 := bstep (se 1 (by rfl) ⟨2302829, by rfl⟩ : syracuseStep 3070439 = 4605659) B4605659
theorem B2046959 : Blo 2045435 2046959 := bstep (se 1 (by rfl) ⟨1535219, by rfl⟩ : syracuseStep 2046959 = 3070439) B3070439
theorem B3070445 : Blo 2045435 3070445 := bbase (se 3 (by rfl) ⟨575708, by rfl⟩ : syracuseStep 3070445 = 1151417) (by norm_num)
theorem B2046963 : Blo 2045435 2046963 := bstep (se 1 (by rfl) ⟨1535222, by rfl⟩ : syracuseStep 2046963 = 3070445) B3070445
theorem B4605677 : Blo 2045435 4605677 := bbase (se 3 (by rfl) ⟨863564, by rfl⟩ : syracuseStep 4605677 = 1727129) (by norm_num)
theorem B3070451 : Blo 2045435 3070451 := bstep (se 1 (by rfl) ⟨2302838, by rfl⟩ : syracuseStep 3070451 = 4605677) B4605677
theorem B2046967 : Blo 2045435 2046967 := bstep (se 1 (by rfl) ⟨1535225, by rfl⟩ : syracuseStep 2046967 = 3070451) B3070451
theorem B2074901 : Blo 2045435 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B5533069 : Blo 2045435 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B7377425 : Blo 2045435 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B4918283 : Blo 2045435 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B3278855 : Blo 2045435 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B2185903 : Blo 2045435 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B2914537 : Blo 2045435 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B3886049 : Blo 2045435 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B2590699 : Blo 2045435 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B3454265 : Blo 2045435 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B2302843 : Blo 2045435 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B3070457 : Blo 2045435 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B2046971 : Blo 2045435 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B6647189 : Blo 2045435 6647189 := bbase (se 6 (by rfl) ⟨155793, by rfl⟩ : syracuseStep 6647189 = 311587) (by norm_num)
theorem B17725837 : Blo 2045435 17725837 := bstep (se 3 (by rfl) ⟨3323594, by rfl⟩ : syracuseStep 17725837 = 6647189) B6647189
theorem B23634449 : Blo 2045435 23634449 := bstep (se 2 (by rfl) ⟨8862918, by rfl⟩ : syracuseStep 23634449 = 17725837) B17725837
theorem B15756299 : Blo 2045435 15756299 := bstep (se 1 (by rfl) ⟨11817224, by rfl⟩ : syracuseStep 15756299 = 23634449) B23634449
theorem B10504199 : Blo 2045435 10504199 := bstep (se 1 (by rfl) ⟨7878149, by rfl⟩ : syracuseStep 10504199 = 15756299) B15756299
theorem B28011197 : Blo 2045435 28011197 := bstep (se 3 (by rfl) ⟨5252099, by rfl⟩ : syracuseStep 28011197 = 10504199) B10504199
theorem B74696525 : Blo 2045435 74696525 := bstep (se 3 (by rfl) ⟨14005598, by rfl⟩ : syracuseStep 74696525 = 28011197) B28011197
theorem B49797683 : Blo 2045435 49797683 := bstep (se 1 (by rfl) ⟨37348262, by rfl⟩ : syracuseStep 49797683 = 74696525) B74696525
theorem B33198455 : Blo 2045435 33198455 := bstep (se 1 (by rfl) ⟨24898841, by rfl⟩ : syracuseStep 33198455 = 49797683) B49797683
theorem B88529213 : Blo 2045435 88529213 := bstep (se 3 (by rfl) ⟨16599227, by rfl⟩ : syracuseStep 88529213 = 33198455) B33198455
theorem B59019475 : Blo 2045435 59019475 := bstep (se 1 (by rfl) ⟨44264606, by rfl⟩ : syracuseStep 59019475 = 88529213) B88529213
theorem B78692633 : Blo 2045435 78692633 := bstep (se 2 (by rfl) ⟨29509737, by rfl⟩ : syracuseStep 78692633 = 59019475) B59019475
theorem B52461755 : Blo 2045435 52461755 := bstep (se 1 (by rfl) ⟨39346316, by rfl⟩ : syracuseStep 52461755 = 78692633) B78692633
theorem B34974503 : Blo 2045435 34974503 := bstep (se 1 (by rfl) ⟨26230877, by rfl⟩ : syracuseStep 34974503 = 52461755) B52461755
theorem B23316335 : Blo 2045435 23316335 := bstep (se 1 (by rfl) ⟨17487251, by rfl⟩ : syracuseStep 23316335 = 34974503) B34974503
theorem B15544223 : Blo 2045435 15544223 := bstep (se 1 (by rfl) ⟨11658167, by rfl⟩ : syracuseStep 15544223 = 23316335) B23316335
theorem B10362815 : Blo 2045435 10362815 := bstep (se 1 (by rfl) ⟨7772111, by rfl⟩ : syracuseStep 10362815 = 15544223) B15544223
theorem B6908543 : Blo 2045435 6908543 := bstep (se 1 (by rfl) ⟨5181407, by rfl⟩ : syracuseStep 6908543 = 10362815) B10362815
theorem B4605695 : Blo 2045435 4605695 := bstep (se 1 (by rfl) ⟨3454271, by rfl⟩ : syracuseStep 4605695 = 6908543) B6908543
theorem B3070463 : Blo 2045435 3070463 := bstep (se 1 (by rfl) ⟨2302847, by rfl⟩ : syracuseStep 3070463 = 4605695) B4605695
theorem B2046975 : Blo 2045435 2046975 := bstep (se 1 (by rfl) ⟨1535231, by rfl⟩ : syracuseStep 2046975 = 3070463) B3070463
theorem B3070469 : Blo 2045435 3070469 := bbase (se 4 (by rfl) ⟨287856, by rfl⟩ : syracuseStep 3070469 = 575713) (by norm_num)
theorem B2046979 : Blo 2045435 2046979 := bstep (se 1 (by rfl) ⟨1535234, by rfl⟩ : syracuseStep 2046979 = 3070469) B3070469
theorem B3454285 : Blo 2045435 3454285 := bbase (se 3 (by rfl) ⟨647678, by rfl⟩ : syracuseStep 3454285 = 1295357) (by norm_num)
theorem B4605713 : Blo 2045435 4605713 := bstep (se 2 (by rfl) ⟨1727142, by rfl⟩ : syracuseStep 4605713 = 3454285) B3454285
theorem B3070475 : Blo 2045435 3070475 := bstep (se 1 (by rfl) ⟨2302856, by rfl⟩ : syracuseStep 3070475 = 4605713) B4605713
theorem B2046983 : Blo 2045435 2046983 := bstep (se 1 (by rfl) ⟨1535237, by rfl⟩ : syracuseStep 2046983 = 3070475) B3070475
theorem B2302861 : Blo 2045435 2302861 := bbase (se 3 (by rfl) ⟨431786, by rfl⟩ : syracuseStep 2302861 = 863573) (by norm_num)
theorem B3070481 : Blo 2045435 3070481 := bstep (se 2 (by rfl) ⟨1151430, by rfl⟩ : syracuseStep 3070481 = 2302861) B2302861
theorem B2046987 : Blo 2045435 2046987 := bstep (se 1 (by rfl) ⟨1535240, by rfl⟩ : syracuseStep 2046987 = 3070481) B3070481
theorem B6908597 : Blo 2045435 6908597 := bbase (se 5 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 6908597 = 647681) (by norm_num)
theorem B4605731 : Blo 2045435 4605731 := bstep (se 1 (by rfl) ⟨3454298, by rfl⟩ : syracuseStep 4605731 = 6908597) B6908597
theorem B3070487 : Blo 2045435 3070487 := bstep (se 1 (by rfl) ⟨2302865, by rfl⟩ : syracuseStep 3070487 = 4605731) B4605731
theorem B2046991 : Blo 2045435 2046991 := bstep (se 1 (by rfl) ⟨1535243, by rfl⟩ : syracuseStep 2046991 = 3070487) B3070487
theorem B3070493 : Blo 2045435 3070493 := bbase (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) (by norm_num)
theorem B2046995 : Blo 2045435 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B4605749 : Blo 2045435 4605749 := bbase (se 5 (by rfl) ⟨215894, by rfl⟩ : syracuseStep 4605749 = 431789) (by norm_num)
theorem B3070499 : Blo 2045435 3070499 := bstep (se 1 (by rfl) ⟨2302874, by rfl⟩ : syracuseStep 3070499 = 4605749) B4605749
theorem B2046999 : Blo 2045435 2046999 := bstep (se 1 (by rfl) ⟨1535249, by rfl⟩ : syracuseStep 2046999 = 3070499) B3070499
theorem B2074933 : Blo 2045435 2074933 := bbase (se 5 (by rfl) ⟨97262, by rfl⟩ : syracuseStep 2074933 = 194525) (by norm_num)
theorem B2766577 : Blo 2045435 2766577 := bstep (se 2 (by rfl) ⟨1037466, by rfl⟩ : syracuseStep 2766577 = 2074933) B2074933
theorem B3688769 : Blo 2045435 3688769 := bstep (se 2 (by rfl) ⟨1383288, by rfl⟩ : syracuseStep 3688769 = 2766577) B2766577
theorem B2459179 : Blo 2045435 2459179 := bstep (se 1 (by rfl) ⟨1844384, by rfl⟩ : syracuseStep 2459179 = 3688769) B3688769
theorem B13115621 : Blo 2045435 13115621 := bstep (se 4 (by rfl) ⟨1229589, by rfl⟩ : syracuseStep 13115621 = 2459179) B2459179
theorem B8743747 : Blo 2045435 8743747 := bstep (se 1 (by rfl) ⟨6557810, by rfl⟩ : syracuseStep 8743747 = 13115621) B13115621
theorem B11658329 : Blo 2045435 11658329 := bstep (se 2 (by rfl) ⟨4371873, by rfl⟩ : syracuseStep 11658329 = 8743747) B8743747
theorem B7772219 : Blo 2045435 7772219 := bstep (se 1 (by rfl) ⟨5829164, by rfl⟩ : syracuseStep 7772219 = 11658329) B11658329
theorem B5181479 : Blo 2045435 5181479 := bstep (se 1 (by rfl) ⟨3886109, by rfl⟩ : syracuseStep 5181479 = 7772219) B7772219
theorem B3454319 : Blo 2045435 3454319 := bstep (se 1 (by rfl) ⟨2590739, by rfl⟩ : syracuseStep 3454319 = 5181479) B5181479
theorem B2302879 : Blo 2045435 2302879 := bstep (se 1 (by rfl) ⟨1727159, by rfl⟩ : syracuseStep 2302879 = 3454319) B3454319
theorem B3070505 : Blo 2045435 3070505 := bstep (se 2 (by rfl) ⟨1151439, by rfl⟩ : syracuseStep 3070505 = 2302879) B2302879
theorem B2047003 : Blo 2045435 2047003 := bstep (se 1 (by rfl) ⟨1535252, by rfl⟩ : syracuseStep 2047003 = 3070505) B3070505
theorem B10106981 : Blo 2045435 10106981 := bbase (se 4 (by rfl) ⟨947529, by rfl⟩ : syracuseStep 10106981 = 1895059) (by norm_num)
theorem B6737987 : Blo 2045435 6737987 := bstep (se 1 (by rfl) ⟨5053490, by rfl⟩ : syracuseStep 6737987 = 10106981) B10106981
theorem B17967965 : Blo 2045435 17967965 := bstep (se 3 (by rfl) ⟨3368993, by rfl⟩ : syracuseStep 17967965 = 6737987) B6737987
theorem B47914573 : Blo 2045435 47914573 := bstep (se 3 (by rfl) ⟨8983982, by rfl⟩ : syracuseStep 47914573 = 17967965) B17967965
theorem B63886097 : Blo 2045435 63886097 := bstep (se 2 (by rfl) ⟨23957286, by rfl⟩ : syracuseStep 63886097 = 47914573) B47914573
theorem B170362925 : Blo 2045435 170362925 := bstep (se 3 (by rfl) ⟨31943048, by rfl⟩ : syracuseStep 170362925 = 63886097) B63886097
theorem B113575283 : Blo 2045435 113575283 := bstep (se 1 (by rfl) ⟨85181462, by rfl⟩ : syracuseStep 113575283 = 170362925) B170362925
theorem B75716855 : Blo 2045435 75716855 := bstep (se 1 (by rfl) ⟨56787641, by rfl⟩ : syracuseStep 75716855 = 113575283) B113575283
theorem B50477903 : Blo 2045435 50477903 := bstep (se 1 (by rfl) ⟨37858427, by rfl⟩ : syracuseStep 50477903 = 75716855) B75716855
theorem B33651935 : Blo 2045435 33651935 := bstep (se 1 (by rfl) ⟨25238951, by rfl⟩ : syracuseStep 33651935 = 50477903) B50477903
theorem B22434623 : Blo 2045435 22434623 := bstep (se 1 (by rfl) ⟨16825967, by rfl⟩ : syracuseStep 22434623 = 33651935) B33651935
theorem B14956415 : Blo 2045435 14956415 := bstep (se 1 (by rfl) ⟨11217311, by rfl⟩ : syracuseStep 14956415 = 22434623) B22434623
theorem B9970943 : Blo 2045435 9970943 := bstep (se 1 (by rfl) ⟨7478207, by rfl⟩ : syracuseStep 9970943 = 14956415) B14956415
theorem B26589181 : Blo 2045435 26589181 := bstep (se 3 (by rfl) ⟨4985471, by rfl⟩ : syracuseStep 26589181 = 9970943) B9970943
theorem B35452241 : Blo 2045435 35452241 := bstep (se 2 (by rfl) ⟨13294590, by rfl⟩ : syracuseStep 35452241 = 26589181) B26589181
theorem B23634827 : Blo 2045435 23634827 := bstep (se 1 (by rfl) ⟨17726120, by rfl⟩ : syracuseStep 23634827 = 35452241) B35452241
theorem B15756551 : Blo 2045435 15756551 := bstep (se 1 (by rfl) ⟨11817413, by rfl⟩ : syracuseStep 15756551 = 23634827) B23634827
theorem B10504367 : Blo 2045435 10504367 := bstep (se 1 (by rfl) ⟨7878275, by rfl⟩ : syracuseStep 10504367 = 15756551) B15756551
theorem B7002911 : Blo 2045435 7002911 := bstep (se 1 (by rfl) ⟨5252183, by rfl⟩ : syracuseStep 7002911 = 10504367) B10504367
theorem B4668607 : Blo 2045435 4668607 := bstep (se 1 (by rfl) ⟨3501455, by rfl⟩ : syracuseStep 4668607 = 7002911) B7002911
theorem B24899237 : Blo 2045435 24899237 := bstep (se 4 (by rfl) ⟨2334303, by rfl⟩ : syracuseStep 24899237 = 4668607) B4668607
theorem B16599491 : Blo 2045435 16599491 := bstep (se 1 (by rfl) ⟨12449618, by rfl⟩ : syracuseStep 16599491 = 24899237) B24899237
theorem B11066327 : Blo 2045435 11066327 := bstep (se 1 (by rfl) ⟨8299745, by rfl⟩ : syracuseStep 11066327 = 16599491) B16599491
theorem B7377551 : Blo 2045435 7377551 := bstep (se 1 (by rfl) ⟨5533163, by rfl⟩ : syracuseStep 7377551 = 11066327) B11066327
theorem B4918367 : Blo 2045435 4918367 := bstep (se 1 (by rfl) ⟨3688775, by rfl⟩ : syracuseStep 4918367 = 7377551) B7377551
theorem B13115645 : Blo 2045435 13115645 := bstep (se 3 (by rfl) ⟨2459183, by rfl⟩ : syracuseStep 13115645 = 4918367) B4918367
theorem B8743763 : Blo 2045435 8743763 := bstep (se 1 (by rfl) ⟨6557822, by rfl⟩ : syracuseStep 8743763 = 13115645) B13115645
theorem B5829175 : Blo 2045435 5829175 := bstep (se 1 (by rfl) ⟨4371881, by rfl⟩ : syracuseStep 5829175 = 8743763) B8743763
theorem B7772233 : Blo 2045435 7772233 := bstep (se 2 (by rfl) ⟨2914587, by rfl⟩ : syracuseStep 7772233 = 5829175) B5829175
theorem B10362977 : Blo 2045435 10362977 := bstep (se 2 (by rfl) ⟨3886116, by rfl⟩ : syracuseStep 10362977 = 7772233) B7772233
theorem B6908651 : Blo 2045435 6908651 := bstep (se 1 (by rfl) ⟨5181488, by rfl⟩ : syracuseStep 6908651 = 10362977) B10362977
theorem B4605767 : Blo 2045435 4605767 := bstep (se 1 (by rfl) ⟨3454325, by rfl⟩ : syracuseStep 4605767 = 6908651) B6908651
theorem B3070511 : Blo 2045435 3070511 := bstep (se 1 (by rfl) ⟨2302883, by rfl⟩ : syracuseStep 3070511 = 4605767) B4605767
theorem B2047007 : Blo 2045435 2047007 := bstep (se 1 (by rfl) ⟨1535255, by rfl⟩ : syracuseStep 2047007 = 3070511) B3070511
theorem B3070517 : Blo 2045435 3070517 := bbase (se 5 (by rfl) ⟨143930, by rfl⟩ : syracuseStep 3070517 = 287861) (by norm_num)
theorem B2047011 : Blo 2045435 2047011 := bstep (se 1 (by rfl) ⟨1535258, by rfl⟩ : syracuseStep 2047011 = 3070517) B3070517
theorem B5181509 : Blo 2045435 5181509 := bbase (se 4 (by rfl) ⟨485766, by rfl⟩ : syracuseStep 5181509 = 971533) (by norm_num)
theorem B3454339 : Blo 2045435 3454339 := bstep (se 1 (by rfl) ⟨2590754, by rfl⟩ : syracuseStep 3454339 = 5181509) B5181509
theorem B4605785 : Blo 2045435 4605785 := bstep (se 2 (by rfl) ⟨1727169, by rfl⟩ : syracuseStep 4605785 = 3454339) B3454339
theorem B3070523 : Blo 2045435 3070523 := bstep (se 1 (by rfl) ⟨2302892, by rfl⟩ : syracuseStep 3070523 = 4605785) B4605785
theorem B2047015 : Blo 2045435 2047015 := bstep (se 1 (by rfl) ⟨1535261, by rfl⟩ : syracuseStep 2047015 = 3070523) B3070523
theorem B2302897 : Blo 2045435 2302897 := bbase (se 2 (by rfl) ⟨863586, by rfl⟩ : syracuseStep 2302897 = 1727173) (by norm_num)
theorem B3070529 : Blo 2045435 3070529 := bstep (se 2 (by rfl) ⟨1151448, by rfl⟩ : syracuseStep 3070529 = 2302897) B2302897
theorem B2047019 : Blo 2045435 2047019 := bstep (se 1 (by rfl) ⟨1535264, by rfl⟩ : syracuseStep 2047019 = 3070529) B3070529
theorem B5829221 : Blo 2045435 5829221 := bbase (se 4 (by rfl) ⟨546489, by rfl⟩ : syracuseStep 5829221 = 1092979) (by norm_num)
theorem B3886147 : Blo 2045435 3886147 := bstep (se 1 (by rfl) ⟨2914610, by rfl⟩ : syracuseStep 3886147 = 5829221) B5829221
theorem B5181529 : Blo 2045435 5181529 := bstep (se 2 (by rfl) ⟨1943073, by rfl⟩ : syracuseStep 5181529 = 3886147) B3886147
theorem B6908705 : Blo 2045435 6908705 := bstep (se 2 (by rfl) ⟨2590764, by rfl⟩ : syracuseStep 6908705 = 5181529) B5181529
theorem B4605803 : Blo 2045435 4605803 := bstep (se 1 (by rfl) ⟨3454352, by rfl⟩ : syracuseStep 4605803 = 6908705) B6908705
theorem B3070535 : Blo 2045435 3070535 := bstep (se 1 (by rfl) ⟨2302901, by rfl⟩ : syracuseStep 3070535 = 4605803) B4605803
theorem B2047023 : Blo 2045435 2047023 := bstep (se 1 (by rfl) ⟨1535267, by rfl⟩ : syracuseStep 2047023 = 3070535) B3070535
theorem B3070541 : Blo 2045435 3070541 := bbase (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) (by norm_num)
theorem B2047027 : Blo 2045435 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B4605821 : Blo 2045435 4605821 := bbase (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) (by norm_num)
theorem B3070547 : Blo 2045435 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B2047031 : Blo 2045435 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B3454373 : Blo 2045435 3454373 := bbase (se 4 (by rfl) ⟨323847, by rfl⟩ : syracuseStep 3454373 = 647695) (by norm_num)
theorem B2302915 : Blo 2045435 2302915 := bstep (se 1 (by rfl) ⟨1727186, by rfl⟩ : syracuseStep 2302915 = 3454373) B3454373
theorem B3070553 : Blo 2045435 3070553 := bstep (se 2 (by rfl) ⟨1151457, by rfl⟩ : syracuseStep 3070553 = 2302915) B2302915
theorem B2047035 : Blo 2045435 2047035 := bstep (se 1 (by rfl) ⟨1535276, by rfl⟩ : syracuseStep 2047035 = 3070553) B3070553
theorem B4918445 : Blo 2045435 4918445 := bbase (se 3 (by rfl) ⟨922208, by rfl⟩ : syracuseStep 4918445 = 1844417) (by norm_num)
theorem B3278963 : Blo 2045435 3278963 := bstep (se 1 (by rfl) ⟨2459222, by rfl⟩ : syracuseStep 3278963 = 4918445) B4918445
theorem B2185975 : Blo 2045435 2185975 := bstep (se 1 (by rfl) ⟨1639481, by rfl⟩ : syracuseStep 2185975 = 3278963) B3278963
theorem B2914633 : Blo 2045435 2914633 := bstep (se 2 (by rfl) ⟨1092987, by rfl⟩ : syracuseStep 2914633 = 2185975) B2185975
theorem B15544709 : Blo 2045435 15544709 := bstep (se 4 (by rfl) ⟨1457316, by rfl⟩ : syracuseStep 15544709 = 2914633) B2914633
theorem B10363139 : Blo 2045435 10363139 := bstep (se 1 (by rfl) ⟨7772354, by rfl⟩ : syracuseStep 10363139 = 15544709) B15544709
theorem B6908759 : Blo 2045435 6908759 := bstep (se 1 (by rfl) ⟨5181569, by rfl⟩ : syracuseStep 6908759 = 10363139) B10363139
theorem B4605839 : Blo 2045435 4605839 := bstep (se 1 (by rfl) ⟨3454379, by rfl⟩ : syracuseStep 4605839 = 6908759) B6908759
theorem B3070559 : Blo 2045435 3070559 := bstep (se 1 (by rfl) ⟨2302919, by rfl⟩ : syracuseStep 3070559 = 4605839) B4605839
theorem B2047039 : Blo 2045435 2047039 := bstep (se 1 (by rfl) ⟨1535279, by rfl⟩ : syracuseStep 2047039 = 3070559) B3070559
theorem B3070565 : Blo 2045435 3070565 := bbase (se 4 (by rfl) ⟨287865, by rfl⟩ : syracuseStep 3070565 = 575731) (by norm_num)
theorem B2047043 : Blo 2045435 2047043 := bstep (se 1 (by rfl) ⟨1535282, by rfl⟩ : syracuseStep 2047043 = 3070565) B3070565
theorem B2914645 : Blo 2045435 2914645 := bbase (se 10 (by rfl) ⟨4269, by rfl⟩ : syracuseStep 2914645 = 8539) (by norm_num)
theorem B3886193 : Blo 2045435 3886193 := bstep (se 2 (by rfl) ⟨1457322, by rfl⟩ : syracuseStep 3886193 = 2914645) B2914645
theorem B2590795 : Blo 2045435 2590795 := bstep (se 1 (by rfl) ⟨1943096, by rfl⟩ : syracuseStep 2590795 = 3886193) B3886193
theorem B3454393 : Blo 2045435 3454393 := bstep (se 2 (by rfl) ⟨1295397, by rfl⟩ : syracuseStep 3454393 = 2590795) B2590795
theorem B4605857 : Blo 2045435 4605857 := bstep (se 2 (by rfl) ⟨1727196, by rfl⟩ : syracuseStep 4605857 = 3454393) B3454393
theorem B3070571 : Blo 2045435 3070571 := bstep (se 1 (by rfl) ⟨2302928, by rfl⟩ : syracuseStep 3070571 = 4605857) B4605857
theorem B2047047 : Blo 2045435 2047047 := bstep (se 1 (by rfl) ⟨1535285, by rfl⟩ : syracuseStep 2047047 = 3070571) B3070571
theorem B2302933 : Blo 2045435 2302933 := bbase (se 7 (by rfl) ⟨26987, by rfl⟩ : syracuseStep 2302933 = 53975) (by norm_num)
theorem B3070577 : Blo 2045435 3070577 := bstep (se 2 (by rfl) ⟨1151466, by rfl⟩ : syracuseStep 3070577 = 2302933) B2302933
theorem B2047051 : Blo 2045435 2047051 := bstep (se 1 (by rfl) ⟨1535288, by rfl⟩ : syracuseStep 2047051 = 3070577) B3070577
theorem B2590805 : Blo 2045435 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B6908813 : Blo 2045435 6908813 := bstep (se 3 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 6908813 = 2590805) B2590805
theorem B4605875 : Blo 2045435 4605875 := bstep (se 1 (by rfl) ⟨3454406, by rfl⟩ : syracuseStep 4605875 = 6908813) B6908813
theorem B3070583 : Blo 2045435 3070583 := bstep (se 1 (by rfl) ⟨2302937, by rfl⟩ : syracuseStep 3070583 = 4605875) B4605875
theorem B2047055 : Blo 2045435 2047055 := bstep (se 1 (by rfl) ⟨1535291, by rfl⟩ : syracuseStep 2047055 = 3070583) B3070583
theorem B3070589 : Blo 2045435 3070589 := bbase (se 3 (by rfl) ⟨575735, by rfl⟩ : syracuseStep 3070589 = 1151471) (by norm_num)
theorem B2047059 : Blo 2045435 2047059 := bstep (se 1 (by rfl) ⟨1535294, by rfl⟩ : syracuseStep 2047059 = 3070589) B3070589
theorem B4605893 : Blo 2045435 4605893 := bbase (se 4 (by rfl) ⟨431802, by rfl⟩ : syracuseStep 4605893 = 863605) (by norm_num)
theorem B3070595 : Blo 2045435 3070595 := bstep (se 1 (by rfl) ⟨2302946, by rfl⟩ : syracuseStep 3070595 = 4605893) B4605893
theorem B2047063 : Blo 2045435 2047063 := bstep (se 1 (by rfl) ⟨1535297, by rfl⟩ : syracuseStep 2047063 = 3070595) B3070595
theorem B8744021 : Blo 2045435 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B5829347 : Blo 2045435 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B3886231 : Blo 2045435 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B5181641 : Blo 2045435 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B3454427 : Blo 2045435 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B2302951 : Blo 2045435 2302951 := bstep (se 1 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 2302951 = 3454427) B3454427
theorem B3070601 : Blo 2045435 3070601 := bstep (se 2 (by rfl) ⟨1151475, by rfl⟩ : syracuseStep 3070601 = 2302951) B2302951
theorem B2047067 : Blo 2045435 2047067 := bstep (se 1 (by rfl) ⟨1535300, by rfl⟩ : syracuseStep 2047067 = 3070601) B3070601
theorem B10363301 : Blo 2045435 10363301 := bbase (se 4 (by rfl) ⟨971559, by rfl⟩ : syracuseStep 10363301 = 1943119) (by norm_num)
theorem B6908867 : Blo 2045435 6908867 := bstep (se 1 (by rfl) ⟨5181650, by rfl⟩ : syracuseStep 6908867 = 10363301) B10363301
theorem B4605911 : Blo 2045435 4605911 := bstep (se 1 (by rfl) ⟨3454433, by rfl⟩ : syracuseStep 4605911 = 6908867) B6908867
theorem B3070607 : Blo 2045435 3070607 := bstep (se 1 (by rfl) ⟨2302955, by rfl⟩ : syracuseStep 3070607 = 4605911) B4605911
theorem B2047071 : Blo 2045435 2047071 := bstep (se 1 (by rfl) ⟨1535303, by rfl⟩ : syracuseStep 2047071 = 3070607) B3070607
theorem B3070613 : Blo 2045435 3070613 := bbase (se 6 (by rfl) ⟨71967, by rfl⟩ : syracuseStep 3070613 = 143935) (by norm_num)
theorem B2047075 : Blo 2045435 2047075 := bstep (se 1 (by rfl) ⟨1535306, by rfl⟩ : syracuseStep 2047075 = 3070613) B3070613
theorem B6225029 : Blo 2045435 6225029 := bbase (se 4 (by rfl) ⟨583596, by rfl⟩ : syracuseStep 6225029 = 1167193) (by norm_num)
theorem B4150019 : Blo 2045435 4150019 := bstep (se 1 (by rfl) ⟨3112514, by rfl⟩ : syracuseStep 4150019 = 6225029) B6225029
theorem B2766679 : Blo 2045435 2766679 := bstep (se 1 (by rfl) ⟨2075009, by rfl⟩ : syracuseStep 2766679 = 4150019) B4150019
theorem B14755621 : Blo 2045435 14755621 := bstep (se 4 (by rfl) ⟨1383339, by rfl⟩ : syracuseStep 14755621 = 2766679) B2766679
theorem B19674161 : Blo 2045435 19674161 := bstep (se 2 (by rfl) ⟨7377810, by rfl⟩ : syracuseStep 19674161 = 14755621) B14755621
theorem B13116107 : Blo 2045435 13116107 := bstep (se 1 (by rfl) ⟨9837080, by rfl⟩ : syracuseStep 13116107 = 19674161) B19674161
theorem B8744071 : Blo 2045435 8744071 := bstep (se 1 (by rfl) ⟨6558053, by rfl⟩ : syracuseStep 8744071 = 13116107) B13116107
theorem B11658761 : Blo 2045435 11658761 := bstep (se 2 (by rfl) ⟨4372035, by rfl⟩ : syracuseStep 11658761 = 8744071) B8744071
theorem B7772507 : Blo 2045435 7772507 := bstep (se 1 (by rfl) ⟨5829380, by rfl⟩ : syracuseStep 7772507 = 11658761) B11658761
theorem B5181671 : Blo 2045435 5181671 := bstep (se 1 (by rfl) ⟨3886253, by rfl⟩ : syracuseStep 5181671 = 7772507) B7772507
theorem B3454447 : Blo 2045435 3454447 := bstep (se 1 (by rfl) ⟨2590835, by rfl⟩ : syracuseStep 3454447 = 5181671) B5181671
theorem B4605929 : Blo 2045435 4605929 := bstep (se 2 (by rfl) ⟨1727223, by rfl⟩ : syracuseStep 4605929 = 3454447) B3454447
theorem B3070619 : Blo 2045435 3070619 := bstep (se 1 (by rfl) ⟨2302964, by rfl⟩ : syracuseStep 3070619 = 4605929) B4605929
theorem B2047079 : Blo 2045435 2047079 := bstep (se 1 (by rfl) ⟨1535309, by rfl⟩ : syracuseStep 2047079 = 3070619) B3070619
theorem B2302969 : Blo 2045435 2302969 := bbase (se 2 (by rfl) ⟨863613, by rfl⟩ : syracuseStep 2302969 = 1727227) (by norm_num)
theorem B3070625 : Blo 2045435 3070625 := bstep (se 2 (by rfl) ⟨1151484, by rfl⟩ : syracuseStep 3070625 = 2302969) B2302969
theorem B2047083 : Blo 2045435 2047083 := bstep (se 1 (by rfl) ⟨1535312, by rfl⟩ : syracuseStep 2047083 = 3070625) B3070625
theorem B74700629 : Blo 2045435 74700629 := bbase (se 9 (by rfl) ⟨218849, by rfl⟩ : syracuseStep 74700629 = 437699) (by norm_num)
theorem B49800419 : Blo 2045435 49800419 := bstep (se 1 (by rfl) ⟨37350314, by rfl⟩ : syracuseStep 49800419 = 74700629) B74700629
theorem B33200279 : Blo 2045435 33200279 := bstep (se 1 (by rfl) ⟨24900209, by rfl⟩ : syracuseStep 33200279 = 49800419) B49800419
theorem B22133519 : Blo 2045435 22133519 := bstep (se 1 (by rfl) ⟨16600139, by rfl⟩ : syracuseStep 22133519 = 33200279) B33200279
theorem B14755679 : Blo 2045435 14755679 := bstep (se 1 (by rfl) ⟨11066759, by rfl⟩ : syracuseStep 14755679 = 22133519) B22133519
theorem B9837119 : Blo 2045435 9837119 := bstep (se 1 (by rfl) ⟨7377839, by rfl⟩ : syracuseStep 9837119 = 14755679) B14755679
theorem B6558079 : Blo 2045435 6558079 := bstep (se 1 (by rfl) ⟨4918559, by rfl⟩ : syracuseStep 6558079 = 9837119) B9837119
theorem B8744105 : Blo 2045435 8744105 := bstep (se 2 (by rfl) ⟨3279039, by rfl⟩ : syracuseStep 8744105 = 6558079) B6558079
theorem B5829403 : Blo 2045435 5829403 := bstep (se 1 (by rfl) ⟨4372052, by rfl⟩ : syracuseStep 5829403 = 8744105) B8744105
theorem B7772537 : Blo 2045435 7772537 := bstep (se 2 (by rfl) ⟨2914701, by rfl⟩ : syracuseStep 7772537 = 5829403) B5829403
theorem B5181691 : Blo 2045435 5181691 := bstep (se 1 (by rfl) ⟨3886268, by rfl⟩ : syracuseStep 5181691 = 7772537) B7772537
theorem B6908921 : Blo 2045435 6908921 := bstep (se 2 (by rfl) ⟨2590845, by rfl⟩ : syracuseStep 6908921 = 5181691) B5181691
theorem B4605947 : Blo 2045435 4605947 := bstep (se 1 (by rfl) ⟨3454460, by rfl⟩ : syracuseStep 4605947 = 6908921) B6908921
theorem B3070631 : Blo 2045435 3070631 := bstep (se 1 (by rfl) ⟨2302973, by rfl⟩ : syracuseStep 3070631 = 4605947) B4605947
theorem B2047087 : Blo 2045435 2047087 := bstep (se 1 (by rfl) ⟨1535315, by rfl⟩ : syracuseStep 2047087 = 3070631) B3070631
theorem B3070637 : Blo 2045435 3070637 := bbase (se 3 (by rfl) ⟨575744, by rfl⟩ : syracuseStep 3070637 = 1151489) (by norm_num)
theorem B2047091 : Blo 2045435 2047091 := bstep (se 1 (by rfl) ⟨1535318, by rfl⟩ : syracuseStep 2047091 = 3070637) B3070637
theorem B4605965 : Blo 2045435 4605965 := bbase (se 3 (by rfl) ⟨863618, by rfl⟩ : syracuseStep 4605965 = 1727237) (by norm_num)
theorem B3070643 : Blo 2045435 3070643 := bstep (se 1 (by rfl) ⟨2302982, by rfl⟩ : syracuseStep 3070643 = 4605965) B4605965
theorem B2047095 : Blo 2045435 2047095 := bstep (se 1 (by rfl) ⟨1535321, by rfl⟩ : syracuseStep 2047095 = 3070643) B3070643
theorem B2590861 : Blo 2045435 2590861 := bbase (se 3 (by rfl) ⟨485786, by rfl⟩ : syracuseStep 2590861 = 971573) (by norm_num)
theorem B3454481 : Blo 2045435 3454481 := bstep (se 2 (by rfl) ⟨1295430, by rfl⟩ : syracuseStep 3454481 = 2590861) B2590861
theorem B2302987 : Blo 2045435 2302987 := bstep (se 1 (by rfl) ⟨1727240, by rfl⟩ : syracuseStep 2302987 = 3454481) B3454481
theorem B3070649 : Blo 2045435 3070649 := bstep (se 2 (by rfl) ⟨1151493, by rfl⟩ : syracuseStep 3070649 = 2302987) B2302987
theorem B2047099 : Blo 2045435 2047099 := bstep (se 1 (by rfl) ⟨1535324, by rfl⟩ : syracuseStep 2047099 = 3070649) B3070649
theorem B19674389 : Blo 2045435 19674389 := bbase (se 6 (by rfl) ⟨461118, by rfl⟩ : syracuseStep 19674389 = 922237) (by norm_num)
theorem B13116259 : Blo 2045435 13116259 := bstep (se 1 (by rfl) ⟨9837194, by rfl⟩ : syracuseStep 13116259 = 19674389) B19674389
theorem B17488345 : Blo 2045435 17488345 := bstep (se 2 (by rfl) ⟨6558129, by rfl⟩ : syracuseStep 17488345 = 13116259) B13116259
theorem B23317793 : Blo 2045435 23317793 := bstep (se 2 (by rfl) ⟨8744172, by rfl⟩ : syracuseStep 23317793 = 17488345) B17488345
theorem B15545195 : Blo 2045435 15545195 := bstep (se 1 (by rfl) ⟨11658896, by rfl⟩ : syracuseStep 15545195 = 23317793) B23317793
theorem B10363463 : Blo 2045435 10363463 := bstep (se 1 (by rfl) ⟨7772597, by rfl⟩ : syracuseStep 10363463 = 15545195) B15545195
theorem B6908975 : Blo 2045435 6908975 := bstep (se 1 (by rfl) ⟨5181731, by rfl⟩ : syracuseStep 6908975 = 10363463) B10363463
theorem B4605983 : Blo 2045435 4605983 := bstep (se 1 (by rfl) ⟨3454487, by rfl⟩ : syracuseStep 4605983 = 6908975) B6908975
theorem B3070655 : Blo 2045435 3070655 := bstep (se 1 (by rfl) ⟨2302991, by rfl⟩ : syracuseStep 3070655 = 4605983) B4605983
theorem B2047103 : Blo 2045435 2047103 := bstep (se 1 (by rfl) ⟨1535327, by rfl⟩ : syracuseStep 2047103 = 3070655) B3070655
theorem B3070661 : Blo 2045435 3070661 := bbase (se 4 (by rfl) ⟨287874, by rfl⟩ : syracuseStep 3070661 = 575749) (by norm_num)
theorem B2047107 : Blo 2045435 2047107 := bstep (se 1 (by rfl) ⟨1535330, by rfl⟩ : syracuseStep 2047107 = 3070661) B3070661
theorem B3454501 : Blo 2045435 3454501 := bbase (se 4 (by rfl) ⟨323859, by rfl⟩ : syracuseStep 3454501 = 647719) (by norm_num)
theorem B4606001 : Blo 2045435 4606001 := bstep (se 2 (by rfl) ⟨1727250, by rfl⟩ : syracuseStep 4606001 = 3454501) B3454501
theorem B3070667 : Blo 2045435 3070667 := bstep (se 1 (by rfl) ⟨2303000, by rfl⟩ : syracuseStep 3070667 = 4606001) B4606001
theorem B2047111 : Blo 2045435 2047111 := bstep (se 1 (by rfl) ⟨1535333, by rfl⟩ : syracuseStep 2047111 = 3070667) B3070667
theorem B2303005 : Blo 2045435 2303005 := bbase (se 3 (by rfl) ⟨431813, by rfl⟩ : syracuseStep 2303005 = 863627) (by norm_num)
theorem B3070673 : Blo 2045435 3070673 := bstep (se 2 (by rfl) ⟨1151502, by rfl⟩ : syracuseStep 3070673 = 2303005) B2303005
theorem B2047115 : Blo 2045435 2047115 := bstep (se 1 (by rfl) ⟨1535336, by rfl⟩ : syracuseStep 2047115 = 3070673) B3070673
theorem B6909029 : Blo 2045435 6909029 := bbase (se 4 (by rfl) ⟨647721, by rfl⟩ : syracuseStep 6909029 = 1295443) (by norm_num)
theorem B4606019 : Blo 2045435 4606019 := bstep (se 1 (by rfl) ⟨3454514, by rfl⟩ : syracuseStep 4606019 = 6909029) B6909029
theorem B3070679 : Blo 2045435 3070679 := bstep (se 1 (by rfl) ⟨2303009, by rfl⟩ : syracuseStep 3070679 = 4606019) B4606019
theorem B2047119 : Blo 2045435 2047119 := bstep (se 1 (by rfl) ⟨1535339, by rfl⟩ : syracuseStep 2047119 = 3070679) B3070679
theorem B3070685 : Blo 2045435 3070685 := bbase (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) (by norm_num)
theorem B2047123 : Blo 2045435 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B4606037 : Blo 2045435 4606037 := bbase (se 8 (by rfl) ⟨26988, by rfl⟩ : syracuseStep 4606037 = 53977) (by norm_num)
theorem B3070691 : Blo 2045435 3070691 := bstep (se 1 (by rfl) ⟨2303018, by rfl⟩ : syracuseStep 3070691 = 4606037) B4606037
theorem B2047127 : Blo 2045435 2047127 := bstep (se 1 (by rfl) ⟨1535345, by rfl⟩ : syracuseStep 2047127 = 3070691) B3070691
theorem B2459333 : Blo 2045435 2459333 := bbase (se 4 (by rfl) ⟨230562, by rfl⟩ : syracuseStep 2459333 = 461125) (by norm_num)
theorem B6558221 : Blo 2045435 6558221 := bstep (se 3 (by rfl) ⟨1229666, by rfl⟩ : syracuseStep 6558221 = 2459333) B2459333
theorem B4372147 : Blo 2045435 4372147 := bstep (se 1 (by rfl) ⟨3279110, by rfl⟩ : syracuseStep 4372147 = 6558221) B6558221
theorem B5829529 : Blo 2045435 5829529 := bstep (se 2 (by rfl) ⟨2186073, by rfl⟩ : syracuseStep 5829529 = 4372147) B4372147
theorem B7772705 : Blo 2045435 7772705 := bstep (se 2 (by rfl) ⟨2914764, by rfl⟩ : syracuseStep 7772705 = 5829529) B5829529
theorem B5181803 : Blo 2045435 5181803 := bstep (se 1 (by rfl) ⟨3886352, by rfl⟩ : syracuseStep 5181803 = 7772705) B7772705
theorem B3454535 : Blo 2045435 3454535 := bstep (se 1 (by rfl) ⟨2590901, by rfl⟩ : syracuseStep 3454535 = 5181803) B5181803
theorem B2303023 : Blo 2045435 2303023 := bstep (se 1 (by rfl) ⟨1727267, by rfl⟩ : syracuseStep 2303023 = 3454535) B3454535
theorem B3070697 : Blo 2045435 3070697 := bstep (se 2 (by rfl) ⟨1151511, by rfl⟩ : syracuseStep 3070697 = 2303023) B2303023
theorem B2047131 : Blo 2045435 2047131 := bstep (se 1 (by rfl) ⟨1535348, by rfl⟩ : syracuseStep 2047131 = 3070697) B3070697
theorem B6310133 : Blo 2045435 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B4206755 : Blo 2045435 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B2804503 : Blo 2045435 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B3739337 : Blo 2045435 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B2492891 : Blo 2045435 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B26590837 : Blo 2045435 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B35454449 : Blo 2045435 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B23636299 : Blo 2045435 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B31515065 : Blo 2045435 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B21010043 : Blo 2045435 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B14006695 : Blo 2045435 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B18675593 : Blo 2045435 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B12450395 : Blo 2045435 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B33201053 : Blo 2045435 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B22134035 : Blo 2045435 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B14756023 : Blo 2045435 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B19674697 : Blo 2045435 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B26232929 : Blo 2045435 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B17488619 : Blo 2045435 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B11659079 : Blo 2045435 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B7772719 : Blo 2045435 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B10363625 : Blo 2045435 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B6909083 : Blo 2045435 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B4606055 : Blo 2045435 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B3070703 : Blo 2045435 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B2047135 : Blo 2045435 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B3070709 : Blo 2045435 3070709 := bbase (se 5 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 3070709 = 287879) (by norm_num)
theorem B2047139 : Blo 2045435 2047139 := bstep (se 1 (by rfl) ⟨1535354, by rfl⟩ : syracuseStep 2047139 = 3070709) B3070709
theorem B3689021 : Blo 2045435 3689021 := bbase (se 3 (by rfl) ⟨691691, by rfl⟩ : syracuseStep 3689021 = 1383383) (by norm_num)
theorem B9837389 : Blo 2045435 9837389 := bstep (se 3 (by rfl) ⟨1844510, by rfl⟩ : syracuseStep 9837389 = 3689021) B3689021
theorem B6558259 : Blo 2045435 6558259 := bstep (se 1 (by rfl) ⟨4918694, by rfl⟩ : syracuseStep 6558259 = 9837389) B9837389
theorem B8744345 : Blo 2045435 8744345 := bstep (se 2 (by rfl) ⟨3279129, by rfl⟩ : syracuseStep 8744345 = 6558259) B6558259
theorem B5829563 : Blo 2045435 5829563 := bstep (se 1 (by rfl) ⟨4372172, by rfl⟩ : syracuseStep 5829563 = 8744345) B8744345
theorem B3886375 : Blo 2045435 3886375 := bstep (se 1 (by rfl) ⟨2914781, by rfl⟩ : syracuseStep 3886375 = 5829563) B5829563
theorem B5181833 : Blo 2045435 5181833 := bstep (se 2 (by rfl) ⟨1943187, by rfl⟩ : syracuseStep 5181833 = 3886375) B3886375
theorem B3454555 : Blo 2045435 3454555 := bstep (se 1 (by rfl) ⟨2590916, by rfl⟩ : syracuseStep 3454555 = 5181833) B5181833
theorem B4606073 : Blo 2045435 4606073 := bstep (se 2 (by rfl) ⟨1727277, by rfl⟩ : syracuseStep 4606073 = 3454555) B3454555
theorem B3070715 : Blo 2045435 3070715 := bstep (se 1 (by rfl) ⟨2303036, by rfl⟩ : syracuseStep 3070715 = 4606073) B4606073
theorem B2047143 : Blo 2045435 2047143 := bstep (se 1 (by rfl) ⟨1535357, by rfl⟩ : syracuseStep 2047143 = 3070715) B3070715
theorem B2303041 : Blo 2045435 2303041 := bbase (se 2 (by rfl) ⟨863640, by rfl⟩ : syracuseStep 2303041 = 1727281) (by norm_num)
theorem B3070721 : Blo 2045435 3070721 := bstep (se 2 (by rfl) ⟨1151520, by rfl⟩ : syracuseStep 3070721 = 2303041) B2303041
theorem B2047147 : Blo 2045435 2047147 := bstep (se 1 (by rfl) ⟨1535360, by rfl⟩ : syracuseStep 2047147 = 3070721) B3070721
theorem B5181853 : Blo 2045435 5181853 := bbase (se 3 (by rfl) ⟨971597, by rfl⟩ : syracuseStep 5181853 = 1943195) (by norm_num)
theorem B6909137 : Blo 2045435 6909137 := bstep (se 2 (by rfl) ⟨2590926, by rfl⟩ : syracuseStep 6909137 = 5181853) B5181853
theorem B4606091 : Blo 2045435 4606091 := bstep (se 1 (by rfl) ⟨3454568, by rfl⟩ : syracuseStep 4606091 = 6909137) B6909137
theorem B3070727 : Blo 2045435 3070727 := bstep (se 1 (by rfl) ⟨2303045, by rfl⟩ : syracuseStep 3070727 = 4606091) B4606091
theorem B2047151 : Blo 2045435 2047151 := bstep (se 1 (by rfl) ⟨1535363, by rfl⟩ : syracuseStep 2047151 = 3070727) B3070727
theorem B3070733 : Blo 2045435 3070733 := bbase (se 3 (by rfl) ⟨575762, by rfl⟩ : syracuseStep 3070733 = 1151525) (by norm_num)
theorem B2047155 : Blo 2045435 2047155 := bstep (se 1 (by rfl) ⟨1535366, by rfl⟩ : syracuseStep 2047155 = 3070733) B3070733
theorem B4606109 : Blo 2045435 4606109 := bbase (se 3 (by rfl) ⟨863645, by rfl⟩ : syracuseStep 4606109 = 1727291) (by norm_num)
theorem B3070739 : Blo 2045435 3070739 := bstep (se 1 (by rfl) ⟨2303054, by rfl⟩ : syracuseStep 3070739 = 4606109) B4606109
theorem B2047159 : Blo 2045435 2047159 := bstep (se 1 (by rfl) ⟨1535369, by rfl⟩ : syracuseStep 2047159 = 3070739) B3070739
theorem B3454589 : Blo 2045435 3454589 := bbase (se 3 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 3454589 = 1295471) (by norm_num)
theorem B2303059 : Blo 2045435 2303059 := bstep (se 1 (by rfl) ⟨1727294, by rfl⟩ : syracuseStep 2303059 = 3454589) B3454589
theorem B3070745 : Blo 2045435 3070745 := bstep (se 2 (by rfl) ⟨1151529, by rfl⟩ : syracuseStep 3070745 = 2303059) B2303059
theorem B2047163 : Blo 2045435 2047163 := bstep (se 1 (by rfl) ⟨1535372, by rfl⟩ : syracuseStep 2047163 = 3070745) B3070745
theorem B5609093 : Blo 2045435 5609093 := bbase (se 4 (by rfl) ⟨525852, by rfl⟩ : syracuseStep 5609093 = 1051705) (by norm_num)
theorem B14957581 : Blo 2045435 14957581 := bstep (se 3 (by rfl) ⟨2804546, by rfl⟩ : syracuseStep 14957581 = 5609093) B5609093
theorem B19943441 : Blo 2045435 19943441 := bstep (se 2 (by rfl) ⟨7478790, by rfl⟩ : syracuseStep 19943441 = 14957581) B14957581
theorem B13295627 : Blo 2045435 13295627 := bstep (se 1 (by rfl) ⟨9971720, by rfl⟩ : syracuseStep 13295627 = 19943441) B19943441
theorem B8863751 : Blo 2045435 8863751 := bstep (se 1 (by rfl) ⟨6647813, by rfl⟩ : syracuseStep 8863751 = 13295627) B13295627
theorem B23636669 : Blo 2045435 23636669 := bstep (se 3 (by rfl) ⟨4431875, by rfl⟩ : syracuseStep 23636669 = 8863751) B8863751
theorem B63031117 : Blo 2045435 63031117 := bstep (se 3 (by rfl) ⟨11818334, by rfl⟩ : syracuseStep 63031117 = 23636669) B23636669
theorem B84041489 : Blo 2045435 84041489 := bstep (se 2 (by rfl) ⟨31515558, by rfl⟩ : syracuseStep 84041489 = 63031117) B63031117
theorem B56027659 : Blo 2045435 56027659 := bstep (se 1 (by rfl) ⟨42020744, by rfl⟩ : syracuseStep 56027659 = 84041489) B84041489
theorem B74703545 : Blo 2045435 74703545 := bstep (se 2 (by rfl) ⟨28013829, by rfl⟩ : syracuseStep 74703545 = 56027659) B56027659
theorem B49802363 : Blo 2045435 49802363 := bstep (se 1 (by rfl) ⟨37351772, by rfl⟩ : syracuseStep 49802363 = 74703545) B74703545
theorem B33201575 : Blo 2045435 33201575 := bstep (se 1 (by rfl) ⟨24901181, by rfl⟩ : syracuseStep 33201575 = 49802363) B49802363
theorem B22134383 : Blo 2045435 22134383 := bstep (se 1 (by rfl) ⟨16600787, by rfl⟩ : syracuseStep 22134383 = 33201575) B33201575
theorem B14756255 : Blo 2045435 14756255 := bstep (se 1 (by rfl) ⟨11067191, by rfl⟩ : syracuseStep 14756255 = 22134383) B22134383
theorem B9837503 : Blo 2045435 9837503 := bstep (se 1 (by rfl) ⟨7378127, by rfl⟩ : syracuseStep 9837503 = 14756255) B14756255
theorem B6558335 : Blo 2045435 6558335 := bstep (se 1 (by rfl) ⟨4918751, by rfl⟩ : syracuseStep 6558335 = 9837503) B9837503
theorem B4372223 : Blo 2045435 4372223 := bstep (se 1 (by rfl) ⟨3279167, by rfl⟩ : syracuseStep 4372223 = 6558335) B6558335
theorem B11659261 : Blo 2045435 11659261 := bstep (se 3 (by rfl) ⟨2186111, by rfl⟩ : syracuseStep 11659261 = 4372223) B4372223
theorem B15545681 : Blo 2045435 15545681 := bstep (se 2 (by rfl) ⟨5829630, by rfl⟩ : syracuseStep 15545681 = 11659261) B11659261
theorem B10363787 : Blo 2045435 10363787 := bstep (se 1 (by rfl) ⟨7772840, by rfl⟩ : syracuseStep 10363787 = 15545681) B15545681
theorem B6909191 : Blo 2045435 6909191 := bstep (se 1 (by rfl) ⟨5181893, by rfl⟩ : syracuseStep 6909191 = 10363787) B10363787
theorem B4606127 : Blo 2045435 4606127 := bstep (se 1 (by rfl) ⟨3454595, by rfl⟩ : syracuseStep 4606127 = 6909191) B6909191
theorem B3070751 : Blo 2045435 3070751 := bstep (se 1 (by rfl) ⟨2303063, by rfl⟩ : syracuseStep 3070751 = 4606127) B4606127
theorem B2047167 : Blo 2045435 2047167 := bstep (se 1 (by rfl) ⟨1535375, by rfl⟩ : syracuseStep 2047167 = 3070751) B3070751
theorem B3070757 : Blo 2045435 3070757 := bbase (se 4 (by rfl) ⟨287883, by rfl⟩ : syracuseStep 3070757 = 575767) (by norm_num)
theorem B2047171 : Blo 2045435 2047171 := bstep (se 1 (by rfl) ⟨1535378, by rfl⟩ : syracuseStep 2047171 = 3070757) B3070757
theorem B2590957 : Blo 2045435 2590957 := bbase (se 3 (by rfl) ⟨485804, by rfl⟩ : syracuseStep 2590957 = 971609) (by norm_num)
theorem B3454609 : Blo 2045435 3454609 := bstep (se 2 (by rfl) ⟨1295478, by rfl⟩ : syracuseStep 3454609 = 2590957) B2590957
theorem B4606145 : Blo 2045435 4606145 := bstep (se 2 (by rfl) ⟨1727304, by rfl⟩ : syracuseStep 4606145 = 3454609) B3454609
theorem B3070763 : Blo 2045435 3070763 := bstep (se 1 (by rfl) ⟨2303072, by rfl⟩ : syracuseStep 3070763 = 4606145) B4606145
theorem B2047175 : Blo 2045435 2047175 := bstep (se 1 (by rfl) ⟨1535381, by rfl⟩ : syracuseStep 2047175 = 3070763) B3070763
theorem B2303077 : Blo 2045435 2303077 := bbase (se 4 (by rfl) ⟨215913, by rfl⟩ : syracuseStep 2303077 = 431827) (by norm_num)
theorem B3070769 : Blo 2045435 3070769 := bstep (se 2 (by rfl) ⟨1151538, by rfl⟩ : syracuseStep 3070769 = 2303077) B2303077
theorem B2047179 : Blo 2045435 2047179 := bstep (se 1 (by rfl) ⟨1535384, by rfl⟩ : syracuseStep 2047179 = 3070769) B3070769
theorem B2186129 : Blo 2045435 2186129 := bbase (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) (by norm_num)
theorem B5829677 : Blo 2045435 5829677 := bstep (se 3 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 5829677 = 2186129) B2186129
theorem B3886451 : Blo 2045435 3886451 := bstep (se 1 (by rfl) ⟨2914838, by rfl⟩ : syracuseStep 3886451 = 5829677) B5829677
theorem B2590967 : Blo 2045435 2590967 := bstep (se 1 (by rfl) ⟨1943225, by rfl⟩ : syracuseStep 2590967 = 3886451) B3886451
theorem B6909245 : Blo 2045435 6909245 := bstep (se 3 (by rfl) ⟨1295483, by rfl⟩ : syracuseStep 6909245 = 2590967) B2590967
theorem B4606163 : Blo 2045435 4606163 := bstep (se 1 (by rfl) ⟨3454622, by rfl⟩ : syracuseStep 4606163 = 6909245) B6909245
theorem B3070775 : Blo 2045435 3070775 := bstep (se 1 (by rfl) ⟨2303081, by rfl⟩ : syracuseStep 3070775 = 4606163) B4606163
theorem B2047183 : Blo 2045435 2047183 := bstep (se 1 (by rfl) ⟨1535387, by rfl⟩ : syracuseStep 2047183 = 3070775) B3070775
theorem B3070781 : Blo 2045435 3070781 := bbase (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) (by norm_num)
theorem B2047187 : Blo 2045435 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B4606181 : Blo 2045435 4606181 := bbase (se 4 (by rfl) ⟨431829, by rfl⟩ : syracuseStep 4606181 = 863659) (by norm_num)
theorem B3070787 : Blo 2045435 3070787 := bstep (se 1 (by rfl) ⟨2303090, by rfl⟩ : syracuseStep 3070787 = 4606181) B4606181
theorem B2047191 : Blo 2045435 2047191 := bstep (se 1 (by rfl) ⟨1535393, by rfl⟩ : syracuseStep 2047191 = 3070787) B3070787
theorem B5181965 : Blo 2045435 5181965 := bbase (se 3 (by rfl) ⟨971618, by rfl⟩ : syracuseStep 5181965 = 1943237) (by norm_num)
theorem B3454643 : Blo 2045435 3454643 := bstep (se 1 (by rfl) ⟨2590982, by rfl⟩ : syracuseStep 3454643 = 5181965) B5181965
theorem B2303095 : Blo 2045435 2303095 := bstep (se 1 (by rfl) ⟨1727321, by rfl⟩ : syracuseStep 2303095 = 3454643) B3454643
theorem B3070793 : Blo 2045435 3070793 := bstep (se 2 (by rfl) ⟨1151547, by rfl⟩ : syracuseStep 3070793 = 2303095) B2303095
theorem B2047195 : Blo 2045435 2047195 := bstep (se 1 (by rfl) ⟨1535396, by rfl⟩ : syracuseStep 2047195 = 3070793) B3070793
theorem B2914861 : Blo 2045435 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B3886481 : Blo 2045435 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B10363949 : Blo 2045435 10363949 := bstep (se 3 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 10363949 = 3886481) B3886481
theorem B6909299 : Blo 2045435 6909299 := bstep (se 1 (by rfl) ⟨5181974, by rfl⟩ : syracuseStep 6909299 = 10363949) B10363949
theorem B4606199 : Blo 2045435 4606199 := bstep (se 1 (by rfl) ⟨3454649, by rfl⟩ : syracuseStep 4606199 = 6909299) B6909299
theorem B3070799 : Blo 2045435 3070799 := bstep (se 1 (by rfl) ⟨2303099, by rfl⟩ : syracuseStep 3070799 = 4606199) B4606199
theorem B2047199 : Blo 2045435 2047199 := bstep (se 1 (by rfl) ⟨1535399, by rfl⟩ : syracuseStep 2047199 = 3070799) B3070799
theorem B3070805 : Blo 2045435 3070805 := bbase (se 9 (by rfl) ⟨8996, by rfl⟩ : syracuseStep 3070805 = 17993) (by norm_num)
theorem B2047203 : Blo 2045435 2047203 := bstep (se 1 (by rfl) ⟨1535402, by rfl⟩ : syracuseStep 2047203 = 3070805) B3070805
theorem B4372309 : Blo 2045435 4372309 := bbase (se 9 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 4372309 = 25619) (by norm_num)
theorem B5829745 : Blo 2045435 5829745 := bstep (se 2 (by rfl) ⟨2186154, by rfl⟩ : syracuseStep 5829745 = 4372309) B4372309
theorem B7772993 : Blo 2045435 7772993 := bstep (se 2 (by rfl) ⟨2914872, by rfl⟩ : syracuseStep 7772993 = 5829745) B5829745
theorem B5181995 : Blo 2045435 5181995 := bstep (se 1 (by rfl) ⟨3886496, by rfl⟩ : syracuseStep 5181995 = 7772993) B7772993
theorem B3454663 : Blo 2045435 3454663 := bstep (se 1 (by rfl) ⟨2590997, by rfl⟩ : syracuseStep 3454663 = 5181995) B5181995
theorem B4606217 : Blo 2045435 4606217 := bstep (se 2 (by rfl) ⟨1727331, by rfl⟩ : syracuseStep 4606217 = 3454663) B3454663
theorem B3070811 : Blo 2045435 3070811 := bstep (se 1 (by rfl) ⟨2303108, by rfl⟩ : syracuseStep 3070811 = 4606217) B4606217
theorem B2047207 : Blo 2045435 2047207 := bstep (se 1 (by rfl) ⟨1535405, by rfl⟩ : syracuseStep 2047207 = 3070811) B3070811
theorem B2303113 : Blo 2045435 2303113 := bbase (se 2 (by rfl) ⟨863667, by rfl⟩ : syracuseStep 2303113 = 1727335) (by norm_num)
theorem B3070817 : Blo 2045435 3070817 := bstep (se 2 (by rfl) ⟨1151556, by rfl⟩ : syracuseStep 3070817 = 2303113) B2303113
theorem B2047211 : Blo 2045435 2047211 := bstep (se 1 (by rfl) ⟨1535408, by rfl⟩ : syracuseStep 2047211 = 3070817) B3070817
theorem B39350933 : Blo 2045435 39350933 := bbase (se 6 (by rfl) ⟨922287, by rfl⟩ : syracuseStep 39350933 = 1844575) (by norm_num)
theorem B26233955 : Blo 2045435 26233955 := bstep (se 1 (by rfl) ⟨19675466, by rfl⟩ : syracuseStep 26233955 = 39350933) B39350933
theorem B17489303 : Blo 2045435 17489303 := bstep (se 1 (by rfl) ⟨13116977, by rfl⟩ : syracuseStep 17489303 = 26233955) B26233955
theorem B11659535 : Blo 2045435 11659535 := bstep (se 1 (by rfl) ⟨8744651, by rfl⟩ : syracuseStep 11659535 = 17489303) B17489303
theorem B7773023 : Blo 2045435 7773023 := bstep (se 1 (by rfl) ⟨5829767, by rfl⟩ : syracuseStep 7773023 = 11659535) B11659535
theorem B5182015 : Blo 2045435 5182015 := bstep (se 1 (by rfl) ⟨3886511, by rfl⟩ : syracuseStep 5182015 = 7773023) B7773023
theorem B6909353 : Blo 2045435 6909353 := bstep (se 2 (by rfl) ⟨2591007, by rfl⟩ : syracuseStep 6909353 = 5182015) B5182015
theorem B4606235 : Blo 2045435 4606235 := bstep (se 1 (by rfl) ⟨3454676, by rfl⟩ : syracuseStep 4606235 = 6909353) B6909353
theorem B3070823 : Blo 2045435 3070823 := bstep (se 1 (by rfl) ⟨2303117, by rfl⟩ : syracuseStep 3070823 = 4606235) B4606235
theorem B2047215 : Blo 2045435 2047215 := bstep (se 1 (by rfl) ⟨1535411, by rfl⟩ : syracuseStep 2047215 = 3070823) B3070823
theorem B3070829 : Blo 2045435 3070829 := bbase (se 3 (by rfl) ⟨575780, by rfl⟩ : syracuseStep 3070829 = 1151561) (by norm_num)
theorem B2047219 : Blo 2045435 2047219 := bstep (se 1 (by rfl) ⟨1535414, by rfl⟩ : syracuseStep 2047219 = 3070829) B3070829
theorem B4606253 : Blo 2045435 4606253 := bbase (se 3 (by rfl) ⟨863672, by rfl⟩ : syracuseStep 4606253 = 1727345) (by norm_num)
theorem B3070835 : Blo 2045435 3070835 := bstep (se 1 (by rfl) ⟨2303126, by rfl⟩ : syracuseStep 3070835 = 4606253) B4606253
theorem B2047223 : Blo 2045435 2047223 := bstep (se 1 (by rfl) ⟨1535417, by rfl⟩ : syracuseStep 2047223 = 3070835) B3070835
theorem B3689173 : Blo 2045435 3689173 := bbase (se 7 (by rfl) ⟨43232, by rfl⟩ : syracuseStep 3689173 = 86465) (by norm_num)
theorem B4918897 : Blo 2045435 4918897 := bstep (se 2 (by rfl) ⟨1844586, by rfl⟩ : syracuseStep 4918897 = 3689173) B3689173
theorem B6558529 : Blo 2045435 6558529 := bstep (se 2 (by rfl) ⟨2459448, by rfl⟩ : syracuseStep 6558529 = 4918897) B4918897
theorem B8744705 : Blo 2045435 8744705 := bstep (se 2 (by rfl) ⟨3279264, by rfl⟩ : syracuseStep 8744705 = 6558529) B6558529
theorem B5829803 : Blo 2045435 5829803 := bstep (se 1 (by rfl) ⟨4372352, by rfl⟩ : syracuseStep 5829803 = 8744705) B8744705
theorem B3886535 : Blo 2045435 3886535 := bstep (se 1 (by rfl) ⟨2914901, by rfl⟩ : syracuseStep 3886535 = 5829803) B5829803
theorem B2591023 : Blo 2045435 2591023 := bstep (se 1 (by rfl) ⟨1943267, by rfl⟩ : syracuseStep 2591023 = 3886535) B3886535
theorem B3454697 : Blo 2045435 3454697 := bstep (se 2 (by rfl) ⟨1295511, by rfl⟩ : syracuseStep 3454697 = 2591023) B2591023
theorem B2303131 : Blo 2045435 2303131 := bstep (se 1 (by rfl) ⟨1727348, by rfl⟩ : syracuseStep 2303131 = 3454697) B3454697
theorem B3070841 : Blo 2045435 3070841 := bstep (se 2 (by rfl) ⟨1151565, by rfl⟩ : syracuseStep 3070841 = 2303131) B2303131
theorem B2047227 : Blo 2045435 2047227 := bstep (se 1 (by rfl) ⟨1535420, by rfl⟩ : syracuseStep 2047227 = 3070841) B3070841
theorem B29513429 : Blo 2045435 29513429 := bbase (se 7 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 29513429 = 691721) (by norm_num)
theorem B19675619 : Blo 2045435 19675619 := bstep (se 1 (by rfl) ⟨14756714, by rfl⟩ : syracuseStep 19675619 = 29513429) B29513429
theorem B13117079 : Blo 2045435 13117079 := bstep (se 1 (by rfl) ⟨9837809, by rfl⟩ : syracuseStep 13117079 = 19675619) B19675619
theorem B34978877 : Blo 2045435 34978877 := bstep (se 3 (by rfl) ⟨6558539, by rfl⟩ : syracuseStep 34978877 = 13117079) B13117079
theorem B23319251 : Blo 2045435 23319251 := bstep (se 1 (by rfl) ⟨17489438, by rfl⟩ : syracuseStep 23319251 = 34978877) B34978877
theorem B15546167 : Blo 2045435 15546167 := bstep (se 1 (by rfl) ⟨11659625, by rfl⟩ : syracuseStep 15546167 = 23319251) B23319251
theorem B10364111 : Blo 2045435 10364111 := bstep (se 1 (by rfl) ⟨7773083, by rfl⟩ : syracuseStep 10364111 = 15546167) B15546167
theorem B6909407 : Blo 2045435 6909407 := bstep (se 1 (by rfl) ⟨5182055, by rfl⟩ : syracuseStep 6909407 = 10364111) B10364111
theorem B4606271 : Blo 2045435 4606271 := bstep (se 1 (by rfl) ⟨3454703, by rfl⟩ : syracuseStep 4606271 = 6909407) B6909407
theorem B3070847 : Blo 2045435 3070847 := bstep (se 1 (by rfl) ⟨2303135, by rfl⟩ : syracuseStep 3070847 = 4606271) B4606271
theorem B2047231 : Blo 2045435 2047231 := bstep (se 1 (by rfl) ⟨1535423, by rfl⟩ : syracuseStep 2047231 = 3070847) B3070847
theorem B3070853 : Blo 2045435 3070853 := bbase (se 4 (by rfl) ⟨287892, by rfl⟩ : syracuseStep 3070853 = 575785) (by norm_num)
theorem B2047235 : Blo 2045435 2047235 := bstep (se 1 (by rfl) ⟨1535426, by rfl⟩ : syracuseStep 2047235 = 3070853) B3070853
theorem B3454717 : Blo 2045435 3454717 := bbase (se 3 (by rfl) ⟨647759, by rfl⟩ : syracuseStep 3454717 = 1295519) (by norm_num)
theorem B4606289 : Blo 2045435 4606289 := bstep (se 2 (by rfl) ⟨1727358, by rfl⟩ : syracuseStep 4606289 = 3454717) B3454717
theorem B3070859 : Blo 2045435 3070859 := bstep (se 1 (by rfl) ⟨2303144, by rfl⟩ : syracuseStep 3070859 = 4606289) B4606289
theorem B2047239 : Blo 2045435 2047239 := bstep (se 1 (by rfl) ⟨1535429, by rfl⟩ : syracuseStep 2047239 = 3070859) B3070859
theorem B2303149 : Blo 2045435 2303149 := bbase (se 3 (by rfl) ⟨431840, by rfl⟩ : syracuseStep 2303149 = 863681) (by norm_num)
theorem B3070865 : Blo 2045435 3070865 := bstep (se 2 (by rfl) ⟨1151574, by rfl⟩ : syracuseStep 3070865 = 2303149) B2303149
theorem B2047243 : Blo 2045435 2047243 := bstep (se 1 (by rfl) ⟨1535432, by rfl⟩ : syracuseStep 2047243 = 3070865) B3070865
theorem B6909461 : Blo 2045435 6909461 := bbase (se 6 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 6909461 = 323881) (by norm_num)
theorem B4606307 : Blo 2045435 4606307 := bstep (se 1 (by rfl) ⟨3454730, by rfl⟩ : syracuseStep 4606307 = 6909461) B6909461
theorem B3070871 : Blo 2045435 3070871 := bstep (se 1 (by rfl) ⟨2303153, by rfl⟩ : syracuseStep 3070871 = 4606307) B4606307
theorem B2047247 : Blo 2045435 2047247 := bstep (se 1 (by rfl) ⟨1535435, by rfl⟩ : syracuseStep 2047247 = 3070871) B3070871
theorem B3070877 : Blo 2045435 3070877 := bbase (se 3 (by rfl) ⟨575789, by rfl⟩ : syracuseStep 3070877 = 1151579) (by norm_num)
theorem B2047251 : Blo 2045435 2047251 := bstep (se 1 (by rfl) ⟨1535438, by rfl⟩ : syracuseStep 2047251 = 3070877) B3070877
theorem B4606325 : Blo 2045435 4606325 := bbase (se 5 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 4606325 = 431843) (by norm_num)
theorem B3070883 : Blo 2045435 3070883 := bstep (se 1 (by rfl) ⟨2303162, by rfl⟩ : syracuseStep 3070883 = 4606325) B4606325
theorem B2047255 : Blo 2045435 2047255 := bstep (se 1 (by rfl) ⟨1535441, by rfl⟩ : syracuseStep 2047255 = 3070883) B3070883
theorem B4918973 : Blo 2045435 4918973 := bbase (se 3 (by rfl) ⟨922307, by rfl⟩ : syracuseStep 4918973 = 1844615) (by norm_num)
theorem B13117261 : Blo 2045435 13117261 := bstep (se 3 (by rfl) ⟨2459486, by rfl⟩ : syracuseStep 13117261 = 4918973) B4918973
theorem B17489681 : Blo 2045435 17489681 := bstep (se 2 (by rfl) ⟨6558630, by rfl⟩ : syracuseStep 17489681 = 13117261) B13117261
theorem B11659787 : Blo 2045435 11659787 := bstep (se 1 (by rfl) ⟨8744840, by rfl⟩ : syracuseStep 11659787 = 17489681) B17489681
theorem B7773191 : Blo 2045435 7773191 := bstep (se 1 (by rfl) ⟨5829893, by rfl⟩ : syracuseStep 7773191 = 11659787) B11659787
theorem B5182127 : Blo 2045435 5182127 := bstep (se 1 (by rfl) ⟨3886595, by rfl⟩ : syracuseStep 5182127 = 7773191) B7773191
theorem B3454751 : Blo 2045435 3454751 := bstep (se 1 (by rfl) ⟨2591063, by rfl⟩ : syracuseStep 3454751 = 5182127) B5182127
theorem B2303167 : Blo 2045435 2303167 := bstep (se 1 (by rfl) ⟨1727375, by rfl⟩ : syracuseStep 2303167 = 3454751) B3454751
theorem B3070889 : Blo 2045435 3070889 := bstep (se 2 (by rfl) ⟨1151583, by rfl⟩ : syracuseStep 3070889 = 2303167) B2303167
theorem B2047259 : Blo 2045435 2047259 := bstep (se 1 (by rfl) ⟨1535444, by rfl⟩ : syracuseStep 2047259 = 3070889) B3070889
theorem B7773205 : Blo 2045435 7773205 := bbase (se 6 (by rfl) ⟨182184, by rfl⟩ : syracuseStep 7773205 = 364369) (by norm_num)
theorem B10364273 : Blo 2045435 10364273 := bstep (se 2 (by rfl) ⟨3886602, by rfl⟩ : syracuseStep 10364273 = 7773205) B7773205
theorem B6909515 : Blo 2045435 6909515 := bstep (se 1 (by rfl) ⟨5182136, by rfl⟩ : syracuseStep 6909515 = 10364273) B10364273
theorem B4606343 : Blo 2045435 4606343 := bstep (se 1 (by rfl) ⟨3454757, by rfl⟩ : syracuseStep 4606343 = 6909515) B6909515
theorem B3070895 : Blo 2045435 3070895 := bstep (se 1 (by rfl) ⟨2303171, by rfl⟩ : syracuseStep 3070895 = 4606343) B4606343
theorem B2047263 : Blo 2045435 2047263 := bstep (se 1 (by rfl) ⟨1535447, by rfl⟩ : syracuseStep 2047263 = 3070895) B3070895
theorem B3070901 : Blo 2045435 3070901 := bbase (se 5 (by rfl) ⟨143948, by rfl⟩ : syracuseStep 3070901 = 287897) (by norm_num)
theorem B2047267 : Blo 2045435 2047267 := bstep (se 1 (by rfl) ⟨1535450, by rfl⟩ : syracuseStep 2047267 = 3070901) B3070901
theorem B5182157 : Blo 2045435 5182157 := bbase (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) (by norm_num)
theorem B3454771 : Blo 2045435 3454771 := bstep (se 1 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 3454771 = 5182157) B5182157
theorem B4606361 : Blo 2045435 4606361 := bstep (se 2 (by rfl) ⟨1727385, by rfl⟩ : syracuseStep 4606361 = 3454771) B3454771
theorem B3070907 : Blo 2045435 3070907 := bstep (se 1 (by rfl) ⟨2303180, by rfl⟩ : syracuseStep 3070907 = 4606361) B4606361
theorem B2047271 : Blo 2045435 2047271 := bstep (se 1 (by rfl) ⟨1535453, by rfl⟩ : syracuseStep 2047271 = 3070907) B3070907
theorem B2303185 : Blo 2045435 2303185 := bbase (se 2 (by rfl) ⟨863694, by rfl⟩ : syracuseStep 2303185 = 1727389) (by norm_num)
theorem B3070913 : Blo 2045435 3070913 := bstep (se 2 (by rfl) ⟨1151592, by rfl⟩ : syracuseStep 3070913 = 2303185) B2303185
theorem B2047275 : Blo 2045435 2047275 := bstep (se 1 (by rfl) ⟨1535456, by rfl⟩ : syracuseStep 2047275 = 3070913) B3070913
theorem B24902549 : Blo 2045435 24902549 := bbase (se 6 (by rfl) ⟨583653, by rfl⟩ : syracuseStep 24902549 = 1167307) (by norm_num)
theorem B16601699 : Blo 2045435 16601699 := bstep (se 1 (by rfl) ⟨12451274, by rfl⟩ : syracuseStep 16601699 = 24902549) B24902549
theorem B11067799 : Blo 2045435 11067799 := bstep (se 1 (by rfl) ⟨8300849, by rfl⟩ : syracuseStep 11067799 = 16601699) B16601699
theorem B14757065 : Blo 2045435 14757065 := bstep (se 2 (by rfl) ⟨5533899, by rfl⟩ : syracuseStep 14757065 = 11067799) B11067799
theorem B9838043 : Blo 2045435 9838043 := bstep (se 1 (by rfl) ⟨7378532, by rfl⟩ : syracuseStep 9838043 = 14757065) B14757065
theorem B6558695 : Blo 2045435 6558695 := bstep (se 1 (by rfl) ⟨4919021, by rfl⟩ : syracuseStep 6558695 = 9838043) B9838043
theorem B4372463 : Blo 2045435 4372463 := bstep (se 1 (by rfl) ⟨3279347, by rfl⟩ : syracuseStep 4372463 = 6558695) B6558695
theorem B2914975 : Blo 2045435 2914975 := bstep (se 1 (by rfl) ⟨2186231, by rfl⟩ : syracuseStep 2914975 = 4372463) B4372463
theorem B3886633 : Blo 2045435 3886633 := bstep (se 2 (by rfl) ⟨1457487, by rfl⟩ : syracuseStep 3886633 = 2914975) B2914975
theorem B5182177 : Blo 2045435 5182177 := bstep (se 2 (by rfl) ⟨1943316, by rfl⟩ : syracuseStep 5182177 = 3886633) B3886633
theorem B6909569 : Blo 2045435 6909569 := bstep (se 2 (by rfl) ⟨2591088, by rfl⟩ : syracuseStep 6909569 = 5182177) B5182177
theorem B4606379 : Blo 2045435 4606379 := bstep (se 1 (by rfl) ⟨3454784, by rfl⟩ : syracuseStep 4606379 = 6909569) B6909569
theorem B3070919 : Blo 2045435 3070919 := bstep (se 1 (by rfl) ⟨2303189, by rfl⟩ : syracuseStep 3070919 = 4606379) B4606379
theorem B2047279 : Blo 2045435 2047279 := bstep (se 1 (by rfl) ⟨1535459, by rfl⟩ : syracuseStep 2047279 = 3070919) B3070919
theorem B3070925 : Blo 2045435 3070925 := bbase (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) (by norm_num)
theorem B2047283 : Blo 2045435 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B4606397 : Blo 2045435 4606397 := bbase (se 3 (by rfl) ⟨863699, by rfl⟩ : syracuseStep 4606397 = 1727399) (by norm_num)
theorem B3070931 : Blo 2045435 3070931 := bstep (se 1 (by rfl) ⟨2303198, by rfl⟩ : syracuseStep 3070931 = 4606397) B4606397
theorem B2047287 : Blo 2045435 2047287 := bstep (se 1 (by rfl) ⟨1535465, by rfl⟩ : syracuseStep 2047287 = 3070931) B3070931
theorem B3454805 : Blo 2045435 3454805 := bbase (se 9 (by rfl) ⟨10121, by rfl⟩ : syracuseStep 3454805 = 20243) (by norm_num)
theorem B2303203 : Blo 2045435 2303203 := bstep (se 1 (by rfl) ⟨1727402, by rfl⟩ : syracuseStep 2303203 = 3454805) B3454805
theorem B3070937 : Blo 2045435 3070937 := bstep (se 2 (by rfl) ⟨1151601, by rfl⟩ : syracuseStep 3070937 = 2303203) B2303203
theorem B2047291 : Blo 2045435 2047291 := bstep (se 1 (by rfl) ⟨1535468, by rfl⟩ : syracuseStep 2047291 = 3070937) B3070937
theorem B3501949 : Blo 2045435 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B4669265 : Blo 2045435 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B3112843 : Blo 2045435 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B4150457 : Blo 2045435 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B2766971 : Blo 2045435 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B7378589 : Blo 2045435 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B4919059 : Blo 2045435 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B6558745 : Blo 2045435 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B8744993 : Blo 2045435 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B5829995 : Blo 2045435 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B15546653 : Blo 2045435 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B10364435 : Blo 2045435 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B6909623 : Blo 2045435 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B4606415 : Blo 2045435 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B3070943 : Blo 2045435 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B2047295 : Blo 2045435 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B3070949 : Blo 2045435 3070949 := bbase (se 4 (by rfl) ⟨287901, by rfl⟩ : syracuseStep 3070949 = 575803) (by norm_num)
theorem B2047299 : Blo 2045435 2047299 := bstep (se 1 (by rfl) ⟨1535474, by rfl⟩ : syracuseStep 2047299 = 3070949) B3070949
theorem B8745029 : Blo 2045435 8745029 := bbase (se 4 (by rfl) ⟨819846, by rfl⟩ : syracuseStep 8745029 = 1639693) (by norm_num)
theorem B5830019 : Blo 2045435 5830019 := bstep (se 1 (by rfl) ⟨4372514, by rfl⟩ : syracuseStep 5830019 = 8745029) B8745029
theorem B3886679 : Blo 2045435 3886679 := bstep (se 1 (by rfl) ⟨2915009, by rfl⟩ : syracuseStep 3886679 = 5830019) B5830019
theorem B2591119 : Blo 2045435 2591119 := bstep (se 1 (by rfl) ⟨1943339, by rfl⟩ : syracuseStep 2591119 = 3886679) B3886679
theorem B3454825 : Blo 2045435 3454825 := bstep (se 2 (by rfl) ⟨1295559, by rfl⟩ : syracuseStep 3454825 = 2591119) B2591119
theorem B4606433 : Blo 2045435 4606433 := bstep (se 2 (by rfl) ⟨1727412, by rfl⟩ : syracuseStep 4606433 = 3454825) B3454825
theorem B3070955 : Blo 2045435 3070955 := bstep (se 1 (by rfl) ⟨2303216, by rfl⟩ : syracuseStep 3070955 = 4606433) B4606433
theorem B2047303 : Blo 2045435 2047303 := bstep (se 1 (by rfl) ⟨1535477, by rfl⟩ : syracuseStep 2047303 = 3070955) B3070955
theorem B2303221 : Blo 2045435 2303221 := bbase (se 5 (by rfl) ⟨107963, by rfl⟩ : syracuseStep 2303221 = 215927) (by norm_num)
theorem B3070961 : Blo 2045435 3070961 := bstep (se 2 (by rfl) ⟨1151610, by rfl⟩ : syracuseStep 3070961 = 2303221) B2303221
theorem B2047307 : Blo 2045435 2047307 := bstep (se 1 (by rfl) ⟨1535480, by rfl⟩ : syracuseStep 2047307 = 3070961) B3070961
theorem B2591129 : Blo 2045435 2591129 := bbase (se 2 (by rfl) ⟨971673, by rfl⟩ : syracuseStep 2591129 = 1943347) (by norm_num)
theorem B6909677 : Blo 2045435 6909677 := bstep (se 3 (by rfl) ⟨1295564, by rfl⟩ : syracuseStep 6909677 = 2591129) B2591129
theorem B4606451 : Blo 2045435 4606451 := bstep (se 1 (by rfl) ⟨3454838, by rfl⟩ : syracuseStep 4606451 = 6909677) B6909677
theorem B3070967 : Blo 2045435 3070967 := bstep (se 1 (by rfl) ⟨2303225, by rfl⟩ : syracuseStep 3070967 = 4606451) B4606451
theorem B2047311 : Blo 2045435 2047311 := bstep (se 1 (by rfl) ⟨1535483, by rfl⟩ : syracuseStep 2047311 = 3070967) B3070967
theorem B3070973 : Blo 2045435 3070973 := bbase (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) (by norm_num)
theorem B2047315 : Blo 2045435 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B4606469 : Blo 2045435 4606469 := bbase (se 4 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 4606469 = 863713) (by norm_num)
theorem B3070979 : Blo 2045435 3070979 := bstep (se 1 (by rfl) ⟨2303234, by rfl⟩ : syracuseStep 3070979 = 4606469) B4606469
theorem B2047319 : Blo 2045435 2047319 := bstep (se 1 (by rfl) ⟨1535489, by rfl⟩ : syracuseStep 2047319 = 3070979) B3070979
theorem B3886717 : Blo 2045435 3886717 := bbase (se 3 (by rfl) ⟨728759, by rfl⟩ : syracuseStep 3886717 = 1457519) (by norm_num)
theorem B5182289 : Blo 2045435 5182289 := bstep (se 2 (by rfl) ⟨1943358, by rfl⟩ : syracuseStep 5182289 = 3886717) B3886717
theorem B3454859 : Blo 2045435 3454859 := bstep (se 1 (by rfl) ⟨2591144, by rfl⟩ : syracuseStep 3454859 = 5182289) B5182289
theorem B2303239 : Blo 2045435 2303239 := bstep (se 1 (by rfl) ⟨1727429, by rfl⟩ : syracuseStep 2303239 = 3454859) B3454859
theorem B3070985 : Blo 2045435 3070985 := bstep (se 2 (by rfl) ⟨1151619, by rfl⟩ : syracuseStep 3070985 = 2303239) B2303239
theorem B2047323 : Blo 2045435 2047323 := bstep (se 1 (by rfl) ⟨1535492, by rfl⟩ : syracuseStep 2047323 = 3070985) B3070985
theorem B10364597 : Blo 2045435 10364597 := bbase (se 5 (by rfl) ⟨485840, by rfl⟩ : syracuseStep 10364597 = 971681) (by norm_num)
theorem B6909731 : Blo 2045435 6909731 := bstep (se 1 (by rfl) ⟨5182298, by rfl⟩ : syracuseStep 6909731 = 10364597) B10364597
theorem B4606487 : Blo 2045435 4606487 := bstep (se 1 (by rfl) ⟨3454865, by rfl⟩ : syracuseStep 4606487 = 6909731) B6909731
theorem B3070991 : Blo 2045435 3070991 := bstep (se 1 (by rfl) ⟨2303243, by rfl⟩ : syracuseStep 3070991 = 4606487) B4606487
theorem B2047327 : Blo 2045435 2047327 := bstep (se 1 (by rfl) ⟨1535495, by rfl⟩ : syracuseStep 2047327 = 3070991) B3070991
theorem B3070997 : Blo 2045435 3070997 := bbase (se 6 (by rfl) ⟨71976, by rfl⟩ : syracuseStep 3070997 = 143953) (by norm_num)
theorem B2047331 : Blo 2045435 2047331 := bstep (se 1 (by rfl) ⟨1535498, by rfl⟩ : syracuseStep 2047331 = 3070997) B3070997
theorem B2075269 : Blo 2045435 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B2767025 : Blo 2045435 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B7378733 : Blo 2045435 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B19676621 : Blo 2045435 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B13117747 : Blo 2045435 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B17490329 : Blo 2045435 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B11660219 : Blo 2045435 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B7773479 : Blo 2045435 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B5182319 : Blo 2045435 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B3454879 : Blo 2045435 3454879 := bstep (se 1 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 3454879 = 5182319) B5182319
theorem B4606505 : Blo 2045435 4606505 := bstep (se 2 (by rfl) ⟨1727439, by rfl⟩ : syracuseStep 4606505 = 3454879) B3454879
theorem B3071003 : Blo 2045435 3071003 := bstep (se 1 (by rfl) ⟨2303252, by rfl⟩ : syracuseStep 3071003 = 4606505) B4606505
theorem B2047335 : Blo 2045435 2047335 := bstep (se 1 (by rfl) ⟨1535501, by rfl⟩ : syracuseStep 2047335 = 3071003) B3071003
theorem B2303257 : Blo 2045435 2303257 := bbase (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) (by norm_num)
theorem B3071009 : Blo 2045435 3071009 := bstep (se 2 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 3071009 = 2303257) B2303257
theorem B2047339 : Blo 2045435 2047339 := bstep (se 1 (by rfl) ⟨1535504, by rfl⟩ : syracuseStep 2047339 = 3071009) B3071009
theorem B7773509 : Blo 2045435 7773509 := bbase (se 4 (by rfl) ⟨728766, by rfl⟩ : syracuseStep 7773509 = 1457533) (by norm_num)
theorem B5182339 : Blo 2045435 5182339 := bstep (se 1 (by rfl) ⟨3886754, by rfl⟩ : syracuseStep 5182339 = 7773509) B7773509
theorem B6909785 : Blo 2045435 6909785 := bstep (se 2 (by rfl) ⟨2591169, by rfl⟩ : syracuseStep 6909785 = 5182339) B5182339
theorem B4606523 : Blo 2045435 4606523 := bstep (se 1 (by rfl) ⟨3454892, by rfl⟩ : syracuseStep 4606523 = 6909785) B6909785
theorem B3071015 : Blo 2045435 3071015 := bstep (se 1 (by rfl) ⟨2303261, by rfl⟩ : syracuseStep 3071015 = 4606523) B4606523
theorem B2047343 : Blo 2045435 2047343 := bstep (se 1 (by rfl) ⟨1535507, by rfl⟩ : syracuseStep 2047343 = 3071015) B3071015
theorem B3071021 : Blo 2045435 3071021 := bbase (se 3 (by rfl) ⟨575816, by rfl⟩ : syracuseStep 3071021 = 1151633) (by norm_num)
theorem B2047347 : Blo 2045435 2047347 := bstep (se 1 (by rfl) ⟨1535510, by rfl⟩ : syracuseStep 2047347 = 3071021) B3071021
theorem B4606541 : Blo 2045435 4606541 := bbase (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) (by norm_num)
theorem B3071027 : Blo 2045435 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B2047351 : Blo 2045435 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B2591185 : Blo 2045435 2591185 := bbase (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) (by norm_num)
theorem B3454913 : Blo 2045435 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B2303275 : Blo 2045435 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B3071033 : Blo 2045435 3071033 := bstep (se 2 (by rfl) ⟨1151637, by rfl⟩ : syracuseStep 3071033 = 2303275) B2303275
theorem B2047355 : Blo 2045435 2047355 := bstep (se 1 (by rfl) ⟨1535516, by rfl⟩ : syracuseStep 2047355 = 3071033) B3071033
theorem B4919213 : Blo 2045435 4919213 := bbase (se 3 (by rfl) ⟨922352, by rfl⟩ : syracuseStep 4919213 = 1844705) (by norm_num)
theorem B3279475 : Blo 2045435 3279475 := bstep (se 1 (by rfl) ⟨2459606, by rfl⟩ : syracuseStep 3279475 = 4919213) B4919213
theorem B4372633 : Blo 2045435 4372633 := bstep (se 2 (by rfl) ⟨1639737, by rfl⟩ : syracuseStep 4372633 = 3279475) B3279475
theorem B23320709 : Blo 2045435 23320709 := bstep (se 4 (by rfl) ⟨2186316, by rfl⟩ : syracuseStep 23320709 = 4372633) B4372633
theorem B15547139 : Blo 2045435 15547139 := bstep (se 1 (by rfl) ⟨11660354, by rfl⟩ : syracuseStep 15547139 = 23320709) B23320709
theorem B10364759 : Blo 2045435 10364759 := bstep (se 1 (by rfl) ⟨7773569, by rfl⟩ : syracuseStep 10364759 = 15547139) B15547139
theorem B6909839 : Blo 2045435 6909839 := bstep (se 1 (by rfl) ⟨5182379, by rfl⟩ : syracuseStep 6909839 = 10364759) B10364759
theorem B4606559 : Blo 2045435 4606559 := bstep (se 1 (by rfl) ⟨3454919, by rfl⟩ : syracuseStep 4606559 = 6909839) B6909839
theorem B3071039 : Blo 2045435 3071039 := bstep (se 1 (by rfl) ⟨2303279, by rfl⟩ : syracuseStep 3071039 = 4606559) B4606559
theorem B2047359 : Blo 2045435 2047359 := bstep (se 1 (by rfl) ⟨1535519, by rfl⟩ : syracuseStep 2047359 = 3071039) B3071039
theorem B3071045 : Blo 2045435 3071045 := bbase (se 4 (by rfl) ⟨287910, by rfl⟩ : syracuseStep 3071045 = 575821) (by norm_num)
theorem B2047363 : Blo 2045435 2047363 := bstep (se 1 (by rfl) ⟨1535522, by rfl⟩ : syracuseStep 2047363 = 3071045) B3071045
theorem B3454933 : Blo 2045435 3454933 := bbase (se 7 (by rfl) ⟨40487, by rfl⟩ : syracuseStep 3454933 = 80975) (by norm_num)
theorem B4606577 : Blo 2045435 4606577 := bstep (se 2 (by rfl) ⟨1727466, by rfl⟩ : syracuseStep 4606577 = 3454933) B3454933
theorem B3071051 : Blo 2045435 3071051 := bstep (se 1 (by rfl) ⟨2303288, by rfl⟩ : syracuseStep 3071051 = 4606577) B4606577
theorem B2047367 : Blo 2045435 2047367 := bstep (se 1 (by rfl) ⟨1535525, by rfl⟩ : syracuseStep 2047367 = 3071051) B3071051
theorem B2303293 : Blo 2045435 2303293 := bbase (se 3 (by rfl) ⟨431867, by rfl⟩ : syracuseStep 2303293 = 863735) (by norm_num)
theorem B3071057 : Blo 2045435 3071057 := bstep (se 2 (by rfl) ⟨1151646, by rfl⟩ : syracuseStep 3071057 = 2303293) B2303293
theorem B2047371 : Blo 2045435 2047371 := bstep (se 1 (by rfl) ⟨1535528, by rfl⟩ : syracuseStep 2047371 = 3071057) B3071057
theorem B6909893 : Blo 2045435 6909893 := bbase (se 4 (by rfl) ⟨647802, by rfl⟩ : syracuseStep 6909893 = 1295605) (by norm_num)
theorem B4606595 : Blo 2045435 4606595 := bstep (se 1 (by rfl) ⟨3454946, by rfl⟩ : syracuseStep 4606595 = 6909893) B6909893
theorem B3071063 : Blo 2045435 3071063 := bstep (se 1 (by rfl) ⟨2303297, by rfl⟩ : syracuseStep 3071063 = 4606595) B4606595
theorem B2047375 : Blo 2045435 2047375 := bstep (se 1 (by rfl) ⟨1535531, by rfl⟩ : syracuseStep 2047375 = 3071063) B3071063
theorem B3071069 : Blo 2045435 3071069 := bbase (se 3 (by rfl) ⟨575825, by rfl⟩ : syracuseStep 3071069 = 1151651) (by norm_num)
theorem B2047379 : Blo 2045435 2047379 := bstep (se 1 (by rfl) ⟨1535534, by rfl⟩ : syracuseStep 2047379 = 3071069) B3071069
theorem B4606613 : Blo 2045435 4606613 := bbase (se 6 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 4606613 = 215935) (by norm_num)
theorem B3071075 : Blo 2045435 3071075 := bstep (se 1 (by rfl) ⟨2303306, by rfl⟩ : syracuseStep 3071075 = 4606613) B4606613
theorem B2047383 : Blo 2045435 2047383 := bstep (se 1 (by rfl) ⟨1535537, by rfl⟩ : syracuseStep 2047383 = 3071075) B3071075
theorem B2459641 : Blo 2045435 2459641 := bbase (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) (by norm_num)
theorem B3279521 : Blo 2045435 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B2186347 : Blo 2045435 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B2915129 : Blo 2045435 2915129 := bstep (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) B2186347
theorem B7773677 : Blo 2045435 7773677 := bstep (se 3 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 7773677 = 2915129) B2915129
theorem B5182451 : Blo 2045435 5182451 := bstep (se 1 (by rfl) ⟨3886838, by rfl⟩ : syracuseStep 5182451 = 7773677) B7773677
theorem B3454967 : Blo 2045435 3454967 := bstep (se 1 (by rfl) ⟨2591225, by rfl⟩ : syracuseStep 3454967 = 5182451) B5182451
theorem B2303311 : Blo 2045435 2303311 := bstep (se 1 (by rfl) ⟨1727483, by rfl⟩ : syracuseStep 2303311 = 3454967) B3454967
theorem B3071081 : Blo 2045435 3071081 := bstep (se 2 (by rfl) ⟨1151655, by rfl⟩ : syracuseStep 3071081 = 2303311) B2303311
theorem B2047387 : Blo 2045435 2047387 := bstep (se 1 (by rfl) ⟨1535540, by rfl⟩ : syracuseStep 2047387 = 3071081) B3071081
theorem B3939877 : Blo 2045435 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B5253169 : Blo 2045435 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B7004225 : Blo 2045435 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B4669483 : Blo 2045435 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B6225977 : Blo 2045435 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B4150651 : Blo 2045435 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B5534201 : Blo 2045435 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B14757869 : Blo 2045435 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B9838579 : Blo 2045435 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B13118105 : Blo 2045435 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B8745403 : Blo 2045435 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B11660537 : Blo 2045435 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B7773691 : Blo 2045435 7773691 := bstep (se 1 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 7773691 = 11660537) B11660537
theorem B10364921 : Blo 2045435 10364921 := bstep (se 2 (by rfl) ⟨3886845, by rfl⟩ : syracuseStep 10364921 = 7773691) B7773691
theorem B6909947 : Blo 2045435 6909947 := bstep (se 1 (by rfl) ⟨5182460, by rfl⟩ : syracuseStep 6909947 = 10364921) B10364921
theorem B4606631 : Blo 2045435 4606631 := bstep (se 1 (by rfl) ⟨3454973, by rfl⟩ : syracuseStep 4606631 = 6909947) B6909947
theorem B3071087 : Blo 2045435 3071087 := bstep (se 1 (by rfl) ⟨2303315, by rfl⟩ : syracuseStep 3071087 = 4606631) B4606631
theorem B2047391 : Blo 2045435 2047391 := bstep (se 1 (by rfl) ⟨1535543, by rfl⟩ : syracuseStep 2047391 = 3071087) B3071087
theorem B3071093 : Blo 2045435 3071093 := bbase (se 5 (by rfl) ⟨143957, by rfl⟩ : syracuseStep 3071093 = 287915) (by norm_num)
theorem B2047395 : Blo 2045435 2047395 := bstep (se 1 (by rfl) ⟨1535546, by rfl⟩ : syracuseStep 2047395 = 3071093) B3071093
theorem B3886861 : Blo 2045435 3886861 := bbase (se 3 (by rfl) ⟨728786, by rfl⟩ : syracuseStep 3886861 = 1457573) (by norm_num)
theorem B5182481 : Blo 2045435 5182481 := bstep (se 2 (by rfl) ⟨1943430, by rfl⟩ : syracuseStep 5182481 = 3886861) B3886861
theorem B3454987 : Blo 2045435 3454987 := bstep (se 1 (by rfl) ⟨2591240, by rfl⟩ : syracuseStep 3454987 = 5182481) B5182481
theorem B4606649 : Blo 2045435 4606649 := bstep (se 2 (by rfl) ⟨1727493, by rfl⟩ : syracuseStep 4606649 = 3454987) B3454987
theorem B3071099 : Blo 2045435 3071099 := bstep (se 1 (by rfl) ⟨2303324, by rfl⟩ : syracuseStep 3071099 = 4606649) B4606649
theorem B2047399 : Blo 2045435 2047399 := bstep (se 1 (by rfl) ⟨1535549, by rfl⟩ : syracuseStep 2047399 = 3071099) B3071099
theorem B2303329 : Blo 2045435 2303329 := bbase (se 2 (by rfl) ⟨863748, by rfl⟩ : syracuseStep 2303329 = 1727497) (by norm_num)
theorem B3071105 : Blo 2045435 3071105 := bstep (se 2 (by rfl) ⟨1151664, by rfl⟩ : syracuseStep 3071105 = 2303329) B2303329
theorem B2047403 : Blo 2045435 2047403 := bstep (se 1 (by rfl) ⟨1535552, by rfl⟩ : syracuseStep 2047403 = 3071105) B3071105
theorem B5182501 : Blo 2045435 5182501 := bbase (se 4 (by rfl) ⟨485859, by rfl⟩ : syracuseStep 5182501 = 971719) (by norm_num)
theorem B6910001 : Blo 2045435 6910001 := bstep (se 2 (by rfl) ⟨2591250, by rfl⟩ : syracuseStep 6910001 = 5182501) B5182501
theorem B4606667 : Blo 2045435 4606667 := bstep (se 1 (by rfl) ⟨3455000, by rfl⟩ : syracuseStep 4606667 = 6910001) B6910001
theorem B3071111 : Blo 2045435 3071111 := bstep (se 1 (by rfl) ⟨2303333, by rfl⟩ : syracuseStep 3071111 = 4606667) B4606667
theorem B2047407 : Blo 2045435 2047407 := bstep (se 1 (by rfl) ⟨1535555, by rfl⟩ : syracuseStep 2047407 = 3071111) B3071111
theorem B3071117 : Blo 2045435 3071117 := bbase (se 3 (by rfl) ⟨575834, by rfl⟩ : syracuseStep 3071117 = 1151669) (by norm_num)
theorem B2047411 : Blo 2045435 2047411 := bstep (se 1 (by rfl) ⟨1535558, by rfl⟩ : syracuseStep 2047411 = 3071117) B3071117
theorem B4606685 : Blo 2045435 4606685 := bbase (se 3 (by rfl) ⟨863753, by rfl⟩ : syracuseStep 4606685 = 1727507) (by norm_num)
theorem B3071123 : Blo 2045435 3071123 := bstep (se 1 (by rfl) ⟨2303342, by rfl⟩ : syracuseStep 3071123 = 4606685) B4606685
theorem B2047415 : Blo 2045435 2047415 := bstep (se 1 (by rfl) ⟨1535561, by rfl⟩ : syracuseStep 2047415 = 3071123) B3071123
theorem B3455021 : Blo 2045435 3455021 := bbase (se 3 (by rfl) ⟨647816, by rfl⟩ : syracuseStep 3455021 = 1295633) (by norm_num)
theorem B2303347 : Blo 2045435 2303347 := bstep (se 1 (by rfl) ⟨1727510, by rfl⟩ : syracuseStep 2303347 = 3455021) B3455021
theorem B3071129 : Blo 2045435 3071129 := bstep (se 2 (by rfl) ⟨1151673, by rfl⟩ : syracuseStep 3071129 = 2303347) B2303347
theorem B2047419 : Blo 2045435 2047419 := bstep (se 1 (by rfl) ⟨1535564, by rfl⟩ : syracuseStep 2047419 = 3071129) B3071129
theorem B2626625 : Blo 2045435 2626625 := bbase (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) (by norm_num)
theorem B7004333 : Blo 2045435 7004333 := bstep (se 3 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 7004333 = 2626625) B2626625
theorem B18678221 : Blo 2045435 18678221 := bstep (se 3 (by rfl) ⟨3502166, by rfl⟩ : syracuseStep 18678221 = 7004333) B7004333
theorem B12452147 : Blo 2045435 12452147 := bstep (se 1 (by rfl) ⟨9339110, by rfl⟩ : syracuseStep 12452147 = 18678221) B18678221
theorem B8301431 : Blo 2045435 8301431 := bstep (se 1 (by rfl) ⟨6226073, by rfl⟩ : syracuseStep 8301431 = 12452147) B12452147
theorem B5534287 : Blo 2045435 5534287 := bstep (se 1 (by rfl) ⟨4150715, by rfl⟩ : syracuseStep 5534287 = 8301431) B8301431
theorem B29516197 : Blo 2045435 29516197 := bstep (se 4 (by rfl) ⟨2767143, by rfl⟩ : syracuseStep 29516197 = 5534287) B5534287
theorem B39354929 : Blo 2045435 39354929 := bstep (se 2 (by rfl) ⟨14758098, by rfl⟩ : syracuseStep 39354929 = 29516197) B29516197
theorem B26236619 : Blo 2045435 26236619 := bstep (se 1 (by rfl) ⟨19677464, by rfl⟩ : syracuseStep 26236619 = 39354929) B39354929
theorem B17491079 : Blo 2045435 17491079 := bstep (se 1 (by rfl) ⟨13118309, by rfl⟩ : syracuseStep 17491079 = 26236619) B26236619
theorem B11660719 : Blo 2045435 11660719 := bstep (se 1 (by rfl) ⟨8745539, by rfl⟩ : syracuseStep 11660719 = 17491079) B17491079
theorem B15547625 : Blo 2045435 15547625 := bstep (se 2 (by rfl) ⟨5830359, by rfl⟩ : syracuseStep 15547625 = 11660719) B11660719
theorem B10365083 : Blo 2045435 10365083 := bstep (se 1 (by rfl) ⟨7773812, by rfl⟩ : syracuseStep 10365083 = 15547625) B15547625
theorem B6910055 : Blo 2045435 6910055 := bstep (se 1 (by rfl) ⟨5182541, by rfl⟩ : syracuseStep 6910055 = 10365083) B10365083
theorem B4606703 : Blo 2045435 4606703 := bstep (se 1 (by rfl) ⟨3455027, by rfl⟩ : syracuseStep 4606703 = 6910055) B6910055
theorem B3071135 : Blo 2045435 3071135 := bstep (se 1 (by rfl) ⟨2303351, by rfl⟩ : syracuseStep 3071135 = 4606703) B4606703
theorem B2047423 : Blo 2045435 2047423 := bstep (se 1 (by rfl) ⟨1535567, by rfl⟩ : syracuseStep 2047423 = 3071135) B3071135
theorem B3071141 : Blo 2045435 3071141 := bbase (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) (by norm_num)
theorem B2047427 : Blo 2045435 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B2591281 : Blo 2045435 2591281 := bbase (se 2 (by rfl) ⟨971730, by rfl⟩ : syracuseStep 2591281 = 1943461) (by norm_num)
theorem B3455041 : Blo 2045435 3455041 := bstep (se 2 (by rfl) ⟨1295640, by rfl⟩ : syracuseStep 3455041 = 2591281) B2591281
theorem B4606721 : Blo 2045435 4606721 := bstep (se 2 (by rfl) ⟨1727520, by rfl⟩ : syracuseStep 4606721 = 3455041) B3455041
theorem B3071147 : Blo 2045435 3071147 := bstep (se 1 (by rfl) ⟨2303360, by rfl⟩ : syracuseStep 3071147 = 4606721) B4606721
theorem B2047431 : Blo 2045435 2047431 := bstep (se 1 (by rfl) ⟨1535573, by rfl⟩ : syracuseStep 2047431 = 3071147) B3071147
theorem B2303365 : Blo 2045435 2303365 := bbase (se 4 (by rfl) ⟨215940, by rfl⟩ : syracuseStep 2303365 = 431881) (by norm_num)
theorem B3071153 : Blo 2045435 3071153 := bstep (se 2 (by rfl) ⟨1151682, by rfl⟩ : syracuseStep 3071153 = 2303365) B2303365
theorem B2047435 : Blo 2045435 2047435 := bstep (se 1 (by rfl) ⟨1535576, by rfl⟩ : syracuseStep 2047435 = 3071153) B3071153
theorem C0 (j : ℕ) (h1 : 511358 ≤ j) (h2 : j ≤ 511858) : Blo 2045435 (4 * j + 3) := by
  interval_cases j
  · exact B2045435
  · exact B2045439
  · exact B2045443
  · exact B2045447
  · exact B2045451
  · exact B2045455
  · exact B2045459
  · exact B2045463
  · exact B2045467
  · exact B2045471
  · exact B2045475
  · exact B2045479
  · exact B2045483
  · exact B2045487
  · exact B2045491
  · exact B2045495
  · exact B2045499
  · exact B2045503
  · exact B2045507
  · exact B2045511
  · exact B2045515
  · exact B2045519
  · exact B2045523
  · exact B2045527
  · exact B2045531
  · exact B2045535
  · exact B2045539
  · exact B2045543
  · exact B2045547
  · exact B2045551
  · exact B2045555
  · exact B2045559
  · exact B2045563
  · exact B2045567
  · exact B2045571
  · exact B2045575
  · exact B2045579
  · exact B2045583
  · exact B2045587
  · exact B2045591
  · exact B2045595
  · exact B2045599
  · exact B2045603
  · exact B2045607
  · exact B2045611
  · exact B2045615
  · exact B2045619
  · exact B2045623
  · exact B2045627
  · exact B2045631
  · exact B2045635
  · exact B2045639
  · exact B2045643
  · exact B2045647
  · exact B2045651
  · exact B2045655
  · exact B2045659
  · exact B2045663
  · exact B2045667
  · exact B2045671
  · exact B2045675
  · exact B2045679
  · exact B2045683
  · exact B2045687
  · exact B2045691
  · exact B2045695
  · exact B2045699
  · exact B2045703
  · exact B2045707
  · exact B2045711
  · exact B2045715
  · exact B2045719
  · exact B2045723
  · exact B2045727
  · exact B2045731
  · exact B2045735
  · exact B2045739
  · exact B2045743
  · exact B2045747
  · exact B2045751
  · exact B2045755
  · exact B2045759
  · exact B2045763
  · exact B2045767
  · exact B2045771
  · exact B2045775
  · exact B2045779
  · exact B2045783
  · exact B2045787
  · exact B2045791
  · exact B2045795
  · exact B2045799
  · exact B2045803
  · exact B2045807
  · exact B2045811
  · exact B2045815
  · exact B2045819
  · exact B2045823
  · exact B2045827
  · exact B2045831
  · exact B2045835
  · exact B2045839
  · exact B2045843
  · exact B2045847
  · exact B2045851
  · exact B2045855
  · exact B2045859
  · exact B2045863
  · exact B2045867
  · exact B2045871
  · exact B2045875
  · exact B2045879
  · exact B2045883
  · exact B2045887
  · exact B2045891
  · exact B2045895
  · exact B2045899
  · exact B2045903
  · exact B2045907
  · exact B2045911
  · exact B2045915
  · exact B2045919
  · exact B2045923
  · exact B2045927
  · exact B2045931
  · exact B2045935
  · exact B2045939
  · exact B2045943
  · exact B2045947
  · exact B2045951
  · exact B2045955
  · exact B2045959
  · exact B2045963
  · exact B2045967
  · exact B2045971
  · exact B2045975
  · exact B2045979
  · exact B2045983
  · exact B2045987
  · exact B2045991
  · exact B2045995
  · exact B2045999
  · exact B2046003
  · exact B2046007
  · exact B2046011
  · exact B2046015
  · exact B2046019
  · exact B2046023
  · exact B2046027
  · exact B2046031
  · exact B2046035
  · exact B2046039
  · exact B2046043
  · exact B2046047
  · exact B2046051
  · exact B2046055
  · exact B2046059
  · exact B2046063
  · exact B2046067
  · exact B2046071
  · exact B2046075
  · exact B2046079
  · exact B2046083
  · exact B2046087
  · exact B2046091
  · exact B2046095
  · exact B2046099
  · exact B2046103
  · exact B2046107
  · exact B2046111
  · exact B2046115
  · exact B2046119
  · exact B2046123
  · exact B2046127
  · exact B2046131
  · exact B2046135
  · exact B2046139
  · exact B2046143
  · exact B2046147
  · exact B2046151
  · exact B2046155
  · exact B2046159
  · exact B2046163
  · exact B2046167
  · exact B2046171
  · exact B2046175
  · exact B2046179
  · exact B2046183
  · exact B2046187
  · exact B2046191
  · exact B2046195
  · exact B2046199
  · exact B2046203
  · exact B2046207
  · exact B2046211
  · exact B2046215
  · exact B2046219
  · exact B2046223
  · exact B2046227
  · exact B2046231
  · exact B2046235
  · exact B2046239
  · exact B2046243
  · exact B2046247
  · exact B2046251
  · exact B2046255
  · exact B2046259
  · exact B2046263
  · exact B2046267
  · exact B2046271
  · exact B2046275
  · exact B2046279
  · exact B2046283
  · exact B2046287
  · exact B2046291
  · exact B2046295
  · exact B2046299
  · exact B2046303
  · exact B2046307
  · exact B2046311
  · exact B2046315
  · exact B2046319
  · exact B2046323
  · exact B2046327
  · exact B2046331
  · exact B2046335
  · exact B2046339
  · exact B2046343
  · exact B2046347
  · exact B2046351
  · exact B2046355
  · exact B2046359
  · exact B2046363
  · exact B2046367
  · exact B2046371
  · exact B2046375
  · exact B2046379
  · exact B2046383
  · exact B2046387
  · exact B2046391
  · exact B2046395
  · exact B2046399
  · exact B2046403
  · exact B2046407
  · exact B2046411
  · exact B2046415
  · exact B2046419
  · exact B2046423
  · exact B2046427
  · exact B2046431
  · exact B2046435
  · exact B2046439
  · exact B2046443
  · exact B2046447
  · exact B2046451
  · exact B2046455
  · exact B2046459
  · exact B2046463
  · exact B2046467
  · exact B2046471
  · exact B2046475
  · exact B2046479
  · exact B2046483
  · exact B2046487
  · exact B2046491
  · exact B2046495
  · exact B2046499
  · exact B2046503
  · exact B2046507
  · exact B2046511
  · exact B2046515
  · exact B2046519
  · exact B2046523
  · exact B2046527
  · exact B2046531
  · exact B2046535
  · exact B2046539
  · exact B2046543
  · exact B2046547
  · exact B2046551
  · exact B2046555
  · exact B2046559
  · exact B2046563
  · exact B2046567
  · exact B2046571
  · exact B2046575
  · exact B2046579
  · exact B2046583
  · exact B2046587
  · exact B2046591
  · exact B2046595
  · exact B2046599
  · exact B2046603
  · exact B2046607
  · exact B2046611
  · exact B2046615
  · exact B2046619
  · exact B2046623
  · exact B2046627
  · exact B2046631
  · exact B2046635
  · exact B2046639
  · exact B2046643
  · exact B2046647
  · exact B2046651
  · exact B2046655
  · exact B2046659
  · exact B2046663
  · exact B2046667
  · exact B2046671
  · exact B2046675
  · exact B2046679
  · exact B2046683
  · exact B2046687
  · exact B2046691
  · exact B2046695
  · exact B2046699
  · exact B2046703
  · exact B2046707
  · exact B2046711
  · exact B2046715
  · exact B2046719
  · exact B2046723
  · exact B2046727
  · exact B2046731
  · exact B2046735
  · exact B2046739
  · exact B2046743
  · exact B2046747
  · exact B2046751
  · exact B2046755
  · exact B2046759
  · exact B2046763
  · exact B2046767
  · exact B2046771
  · exact B2046775
  · exact B2046779
  · exact B2046783
  · exact B2046787
  · exact B2046791
  · exact B2046795
  · exact B2046799
  · exact B2046803
  · exact B2046807
  · exact B2046811
  · exact B2046815
  · exact B2046819
  · exact B2046823
  · exact B2046827
  · exact B2046831
  · exact B2046835
  · exact B2046839
  · exact B2046843
  · exact B2046847
  · exact B2046851
  · exact B2046855
  · exact B2046859
  · exact B2046863
  · exact B2046867
  · exact B2046871
  · exact B2046875
  · exact B2046879
  · exact B2046883
  · exact B2046887
  · exact B2046891
  · exact B2046895
  · exact B2046899
  · exact B2046903
  · exact B2046907
  · exact B2046911
  · exact B2046915
  · exact B2046919
  · exact B2046923
  · exact B2046927
  · exact B2046931
  · exact B2046935
  · exact B2046939
  · exact B2046943
  · exact B2046947
  · exact B2046951
  · exact B2046955
  · exact B2046959
  · exact B2046963
  · exact B2046967
  · exact B2046971
  · exact B2046975
  · exact B2046979
  · exact B2046983
  · exact B2046987
  · exact B2046991
  · exact B2046995
  · exact B2046999
  · exact B2047003
  · exact B2047007
  · exact B2047011
  · exact B2047015
  · exact B2047019
  · exact B2047023
  · exact B2047027
  · exact B2047031
  · exact B2047035
  · exact B2047039
  · exact B2047043
  · exact B2047047
  · exact B2047051
  · exact B2047055
  · exact B2047059
  · exact B2047063
  · exact B2047067
  · exact B2047071
  · exact B2047075
  · exact B2047079
  · exact B2047083
  · exact B2047087
  · exact B2047091
  · exact B2047095
  · exact B2047099
  · exact B2047103
  · exact B2047107
  · exact B2047111
  · exact B2047115
  · exact B2047119
  · exact B2047123
  · exact B2047127
  · exact B2047131
  · exact B2047135
  · exact B2047139
  · exact B2047143
  · exact B2047147
  · exact B2047151
  · exact B2047155
  · exact B2047159
  · exact B2047163
  · exact B2047167
  · exact B2047171
  · exact B2047175
  · exact B2047179
  · exact B2047183
  · exact B2047187
  · exact B2047191
  · exact B2047195
  · exact B2047199
  · exact B2047203
  · exact B2047207
  · exact B2047211
  · exact B2047215
  · exact B2047219
  · exact B2047223
  · exact B2047227
  · exact B2047231
  · exact B2047235
  · exact B2047239
  · exact B2047243
  · exact B2047247
  · exact B2047251
  · exact B2047255
  · exact B2047259
  · exact B2047263
  · exact B2047267
  · exact B2047271
  · exact B2047275
  · exact B2047279
  · exact B2047283
  · exact B2047287
  · exact B2047291
  · exact B2047295
  · exact B2047299
  · exact B2047303
  · exact B2047307
  · exact B2047311
  · exact B2047315
  · exact B2047319
  · exact B2047323
  · exact B2047327
  · exact B2047331
  · exact B2047335
  · exact B2047339
  · exact B2047343
  · exact B2047347
  · exact B2047351
  · exact B2047355
  · exact B2047359
  · exact B2047363
  · exact B2047367
  · exact B2047371
  · exact B2047375
  · exact B2047379
  · exact B2047383
  · exact B2047387
  · exact B2047391
  · exact B2047395
  · exact B2047399
  · exact B2047403
  · exact B2047407
  · exact B2047411
  · exact B2047415
  · exact B2047419
  · exact B2047423
  · exact B2047427
  · exact B2047431
  · exact B2047435
theorem solution (m : ℕ) (hlo : 2045435 ≤ m) (hhi : m ≤ 2047435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 511358 ≤ j := by omega
    have hj2 : j ≤ 511858 := by omega
    have hb : Blo 2045435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
