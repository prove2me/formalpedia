-- Prove2me | solution 1 for syracuse_descends_range_455782_459782
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:00.088799+00:00
-- url     : https://prove2.me/submissions/b64fa282-64ad-4686-8dd4-20612f7c3e85

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


theorem B688133 : Blo 455782 688133 := bbase (se 4 (by rfl) ⟨64512, by rfl⟩ : syracuseStep 688133 = 129025) (by norm_num)
theorem B688157 : Blo 455782 688157 := bbase (se 3 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 688157 = 258059) (by norm_num)
theorem B1540133 : Blo 455782 1540133 := bbase (se 4 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 1540133 = 288775) (by norm_num)
theorem B688181 : Blo 455782 688181 := bbase (se 5 (by rfl) ⟨32258, by rfl⟩ : syracuseStep 688181 = 64517) (by norm_num)
theorem B688205 : Blo 455782 688205 := bbase (se 3 (by rfl) ⟨129038, by rfl⟩ : syracuseStep 688205 = 258077) (by norm_num)
theorem B688229 : Blo 455782 688229 := bbase (se 4 (by rfl) ⟨64521, by rfl⟩ : syracuseStep 688229 = 129043) (by norm_num)
theorem B688253 : Blo 455782 688253 := bbase (se 3 (by rfl) ⟨129047, by rfl⟩ : syracuseStep 688253 = 258095) (by norm_num)
theorem B688277 : Blo 455782 688277 := bbase (se 6 (by rfl) ⟨16131, by rfl⟩ : syracuseStep 688277 = 32263) (by norm_num)
theorem B688301 : Blo 455782 688301 := bbase (se 3 (by rfl) ⟨129056, by rfl⟩ : syracuseStep 688301 = 258113) (by norm_num)
theorem B688325 : Blo 455782 688325 := bbase (se 4 (by rfl) ⟨64530, by rfl⟩ : syracuseStep 688325 = 129061) (by norm_num)
theorem B688349 : Blo 455782 688349 := bbase (se 3 (by rfl) ⟨129065, by rfl⟩ : syracuseStep 688349 = 258131) (by norm_num)
theorem B688373 : Blo 455782 688373 := bbase (se 5 (by rfl) ⟨32267, by rfl⟩ : syracuseStep 688373 = 64535) (by norm_num)
theorem B688397 : Blo 455782 688397 := bbase (se 3 (by rfl) ⟨129074, by rfl⟩ : syracuseStep 688397 = 258149) (by norm_num)
theorem B2326805 : Blo 455782 2326805 := bbase (se 6 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 2326805 = 109069) (by norm_num)
theorem B688421 : Blo 455782 688421 := bbase (se 4 (by rfl) ⟨64539, by rfl⟩ : syracuseStep 688421 = 129079) (by norm_num)
theorem B688445 : Blo 455782 688445 := bbase (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) (by norm_num)
theorem B688469 : Blo 455782 688469 := bbase (se 10 (by rfl) ⟨1008, by rfl⟩ : syracuseStep 688469 = 2017) (by norm_num)
theorem B688493 : Blo 455782 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B688517 : Blo 455782 688517 := bbase (se 4 (by rfl) ⟨64548, by rfl⟩ : syracuseStep 688517 = 129097) (by norm_num)
theorem B688541 : Blo 455782 688541 := bbase (se 3 (by rfl) ⟨129101, by rfl⟩ : syracuseStep 688541 = 258203) (by norm_num)
theorem B688565 : Blo 455782 688565 := bbase (se 5 (by rfl) ⟨32276, by rfl⟩ : syracuseStep 688565 = 64553) (by norm_num)
theorem B688589 : Blo 455782 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B1540565 : Blo 455782 1540565 := bbase (se 7 (by rfl) ⟨18053, by rfl⟩ : syracuseStep 1540565 = 36107) (by norm_num)
theorem B1671637 : Blo 455782 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B688613 : Blo 455782 688613 := bbase (se 4 (by rfl) ⟨64557, by rfl⟩ : syracuseStep 688613 = 129115) (by norm_num)
theorem B688637 : Blo 455782 688637 := bbase (se 3 (by rfl) ⟨129119, by rfl⟩ : syracuseStep 688637 = 258239) (by norm_num)
theorem B688661 : Blo 455782 688661 := bbase (se 6 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 688661 = 32281) (by norm_num)
theorem B688685 : Blo 455782 688685 := bbase (se 3 (by rfl) ⟨129128, by rfl⟩ : syracuseStep 688685 = 258257) (by norm_num)
theorem B688709 : Blo 455782 688709 := bbase (se 4 (by rfl) ⟨64566, by rfl⟩ : syracuseStep 688709 = 129133) (by norm_num)
theorem B688733 : Blo 455782 688733 := bbase (se 3 (by rfl) ⟨129137, by rfl⟩ : syracuseStep 688733 = 258275) (by norm_num)
theorem B688757 : Blo 455782 688757 := bbase (se 5 (by rfl) ⟨32285, by rfl⟩ : syracuseStep 688757 = 64571) (by norm_num)
theorem B688781 : Blo 455782 688781 := bbase (se 3 (by rfl) ⟨129146, by rfl⟩ : syracuseStep 688781 = 258293) (by norm_num)
theorem B688805 : Blo 455782 688805 := bbase (se 4 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 688805 = 129151) (by norm_num)
theorem B688829 : Blo 455782 688829 := bbase (se 3 (by rfl) ⟨129155, by rfl⟩ : syracuseStep 688829 = 258311) (by norm_num)
theorem B688853 : Blo 455782 688853 := bbase (se 7 (by rfl) ⟨8072, by rfl⟩ : syracuseStep 688853 = 16145) (by norm_num)
theorem B688877 : Blo 455782 688877 := bbase (se 3 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 688877 = 258329) (by norm_num)
theorem B688901 : Blo 455782 688901 := bbase (se 4 (by rfl) ⟨64584, by rfl⟩ : syracuseStep 688901 = 129169) (by norm_num)
theorem B688925 : Blo 455782 688925 := bbase (se 3 (by rfl) ⟨129173, by rfl⟩ : syracuseStep 688925 = 258347) (by norm_num)
theorem B688949 : Blo 455782 688949 := bbase (se 5 (by rfl) ⟨32294, by rfl⟩ : syracuseStep 688949 = 64589) (by norm_num)
theorem B688973 : Blo 455782 688973 := bbase (se 3 (by rfl) ⟨129182, by rfl⟩ : syracuseStep 688973 = 258365) (by norm_num)
theorem B1737557 : Blo 455782 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B688997 : Blo 455782 688997 := bbase (se 4 (by rfl) ⟨64593, by rfl⟩ : syracuseStep 688997 = 129187) (by norm_num)
theorem B689021 : Blo 455782 689021 := bbase (se 3 (by rfl) ⟨129191, by rfl⟩ : syracuseStep 689021 = 258383) (by norm_num)
theorem B1540997 : Blo 455782 1540997 := bbase (se 4 (by rfl) ⟨144468, by rfl⟩ : syracuseStep 1540997 = 288937) (by norm_num)
theorem B689045 : Blo 455782 689045 := bbase (se 6 (by rfl) ⟨16149, by rfl⟩ : syracuseStep 689045 = 32299) (by norm_num)
theorem B689069 : Blo 455782 689069 := bbase (se 3 (by rfl) ⟨129200, by rfl⟩ : syracuseStep 689069 = 258401) (by norm_num)
theorem B689093 : Blo 455782 689093 := bbase (se 4 (by rfl) ⟨64602, by rfl⟩ : syracuseStep 689093 = 129205) (by norm_num)
theorem B689117 : Blo 455782 689117 := bbase (se 3 (by rfl) ⟨129209, by rfl⟩ : syracuseStep 689117 = 258419) (by norm_num)
theorem B689141 : Blo 455782 689141 := bbase (se 5 (by rfl) ⟨32303, by rfl⟩ : syracuseStep 689141 = 64607) (by norm_num)
theorem B689165 : Blo 455782 689165 := bbase (se 3 (by rfl) ⟨129218, by rfl⟩ : syracuseStep 689165 = 258437) (by norm_num)
theorem B689189 : Blo 455782 689189 := bbase (se 4 (by rfl) ⟨64611, by rfl⟩ : syracuseStep 689189 = 129223) (by norm_num)
theorem B689213 : Blo 455782 689213 := bbase (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) (by norm_num)
theorem B689237 : Blo 455782 689237 := bbase (se 8 (by rfl) ⟨4038, by rfl⟩ : syracuseStep 689237 = 8077) (by norm_num)
theorem B689261 : Blo 455782 689261 := bbase (se 3 (by rfl) ⟨129236, by rfl⟩ : syracuseStep 689261 = 258473) (by norm_num)
theorem B1737845 : Blo 455782 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B689285 : Blo 455782 689285 := bbase (se 4 (by rfl) ⟨64620, by rfl⟩ : syracuseStep 689285 = 129241) (by norm_num)
theorem B5276821 : Blo 455782 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B689309 : Blo 455782 689309 := bbase (se 3 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 689309 = 258491) (by norm_num)
theorem B689333 : Blo 455782 689333 := bbase (se 5 (by rfl) ⟨32312, by rfl⟩ : syracuseStep 689333 = 64625) (by norm_num)
theorem B689357 : Blo 455782 689357 := bbase (se 3 (by rfl) ⟨129254, by rfl⟩ : syracuseStep 689357 = 258509) (by norm_num)
theorem B689381 : Blo 455782 689381 := bbase (se 4 (by rfl) ⟨64629, by rfl⟩ : syracuseStep 689381 = 129259) (by norm_num)
theorem B558313 : Blo 455782 558313 := bbase (se 2 (by rfl) ⟨209367, by rfl⟩ : syracuseStep 558313 = 418735) (by norm_num)
theorem B689405 : Blo 455782 689405 := bbase (se 3 (by rfl) ⟨129263, by rfl⟩ : syracuseStep 689405 = 258527) (by norm_num)
theorem B689429 : Blo 455782 689429 := bbase (se 6 (by rfl) ⟨16158, by rfl⟩ : syracuseStep 689429 = 32317) (by norm_num)
theorem B689453 : Blo 455782 689453 := bbase (se 3 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 689453 = 258545) (by norm_num)
theorem B1541429 : Blo 455782 1541429 := bbase (se 5 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 1541429 = 144509) (by norm_num)
theorem B689477 : Blo 455782 689477 := bbase (se 4 (by rfl) ⟨64638, by rfl⟩ : syracuseStep 689477 = 129277) (by norm_num)
theorem B689501 : Blo 455782 689501 := bbase (se 3 (by rfl) ⟨129281, by rfl⟩ : syracuseStep 689501 = 258563) (by norm_num)
theorem B689525 : Blo 455782 689525 := bbase (se 5 (by rfl) ⟨32321, by rfl⟩ : syracuseStep 689525 = 64643) (by norm_num)
theorem B689549 : Blo 455782 689549 := bbase (se 3 (by rfl) ⟨129290, by rfl⟩ : syracuseStep 689549 = 258581) (by norm_num)
theorem B689573 : Blo 455782 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B689597 : Blo 455782 689597 := bbase (se 3 (by rfl) ⟨129299, by rfl⟩ : syracuseStep 689597 = 258599) (by norm_num)
theorem B689621 : Blo 455782 689621 := bbase (se 7 (by rfl) ⟨8081, by rfl⟩ : syracuseStep 689621 = 16163) (by norm_num)
theorem B689645 : Blo 455782 689645 := bbase (se 3 (by rfl) ⟨129308, by rfl⟩ : syracuseStep 689645 = 258617) (by norm_num)
theorem B689669 : Blo 455782 689669 := bbase (se 4 (by rfl) ⟨64656, by rfl⟩ : syracuseStep 689669 = 129313) (by norm_num)
theorem B1541861 : Blo 455782 1541861 := bbase (se 4 (by rfl) ⟨144549, by rfl⟩ : syracuseStep 1541861 = 289099) (by norm_num)
theorem B558937 : Blo 455782 558937 := bbase (se 2 (by rfl) ⟨209601, by rfl⟩ : syracuseStep 558937 = 419203) (by norm_num)
theorem B624485 : Blo 455782 624485 := bbase (se 4 (by rfl) ⟨58545, by rfl⟩ : syracuseStep 624485 = 117091) (by norm_num)
theorem B2820149 : Blo 455782 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B821381 : Blo 455782 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B1542293 : Blo 455782 1542293 := bbase (se 6 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 1542293 = 72295) (by norm_num)
theorem B1739029 : Blo 455782 1739029 := bbase (se 6 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 1739029 = 81517) (by norm_num)
theorem B3705173 : Blo 455782 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B1116509 : Blo 455782 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B2197925 : Blo 455782 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B559561 : Blo 455782 559561 := bbase (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) (by norm_num)
theorem B1542725 : Blo 455782 1542725 := bbase (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) (by norm_num)
theorem B1739333 : Blo 455782 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B2198117 : Blo 455782 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B822125 : Blo 455782 822125 := bbase (se 3 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 822125 = 308297) (by norm_num)
theorem B2198501 : Blo 455782 2198501 := bbase (se 4 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 2198501 = 412219) (by norm_num)
theorem B1543157 : Blo 455782 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B462133 : Blo 455782 462133 := bbase (se 5 (by rfl) ⟨21662, by rfl⟩ : syracuseStep 462133 = 43325) (by norm_num)
theorem B1543589 : Blo 455782 1543589 := bbase (se 4 (by rfl) ⟨144711, by rfl⟩ : syracuseStep 1543589 = 289423) (by norm_num)
theorem B1544021 : Blo 455782 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B25431893 : Blo 455782 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1118069 : Blo 455782 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B1544453 : Blo 455782 1544453 := bbase (se 4 (by rfl) ⟨144792, by rfl⟩ : syracuseStep 1544453 = 289585) (by norm_num)
theorem B823645 : Blo 455782 823645 := bbase (se 3 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 823645 = 308867) (by norm_num)
theorem B463325 : Blo 455782 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B823861 : Blo 455782 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B1741445 : Blo 455782 1741445 := bbase (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) (by norm_num)
theorem B1544885 : Blo 455782 1544885 := bbase (se 5 (by rfl) ⟨72416, by rfl⟩ : syracuseStep 1544885 = 144833) (by norm_num)
theorem B1119005 : Blo 455782 1119005 := bbase (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) (by norm_num)
theorem B463649 : Blo 455782 463649 := bbase (se 2 (by rfl) ⟨173868, by rfl⟩ : syracuseStep 463649 = 347737) (by norm_num)
theorem B824149 : Blo 455782 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B1741733 : Blo 455782 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B988157 : Blo 455782 988157 := bbase (se 3 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 988157 = 370559) (by norm_num)
theorem B1545317 : Blo 455782 1545317 := bbase (se 4 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 1545317 = 289747) (by norm_num)
theorem B824813 : Blo 455782 824813 := bbase (se 3 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 824813 = 309305) (by norm_num)
theorem B1545749 : Blo 455782 1545749 := bbase (se 6 (by rfl) ⟨36228, by rfl⟩ : syracuseStep 1545749 = 72457) (by norm_num)
theorem B530101 : Blo 455782 530101 := bbase (se 5 (by rfl) ⟨24848, by rfl⟩ : syracuseStep 530101 = 49697) (by norm_num)
theorem B1054637 : Blo 455782 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B1546181 : Blo 455782 1546181 := bbase (se 4 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 1546181 = 289909) (by norm_num)
theorem B1742917 : Blo 455782 1742917 := bbase (se 4 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 1742917 = 326797) (by norm_num)
theorem B792749 : Blo 455782 792749 := bbase (se 3 (by rfl) ⟨148640, by rfl⟩ : syracuseStep 792749 = 297281) (by norm_num)
theorem B465085 : Blo 455782 465085 := bbase (se 3 (by rfl) ⟨87203, by rfl⟩ : syracuseStep 465085 = 174407) (by norm_num)
theorem B628925 : Blo 455782 628925 := bbase (se 3 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 628925 = 235847) (by norm_num)
theorem B1546613 : Blo 455782 1546613 := bbase (se 5 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 1546613 = 144995) (by norm_num)
theorem B1743221 : Blo 455782 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B3480245 : Blo 455782 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B1481509 : Blo 455782 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B1547045 : Blo 455782 1547045 := bbase (se 4 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 1547045 = 290071) (by norm_num)
theorem B924461 : Blo 455782 924461 := bbase (se 3 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 924461 = 346673) (by norm_num)
theorem B1153885 : Blo 455782 1153885 := bbase (se 3 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 1153885 = 432707) (by norm_num)
theorem B1153997 : Blo 455782 1153997 := bbase (se 3 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 1153997 = 432749) (by norm_num)
theorem B695341 : Blo 455782 695341 := bbase (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) (by norm_num)
theorem B466049 : Blo 455782 466049 := bbase (se 2 (by rfl) ⟨174768, by rfl⟩ : syracuseStep 466049 = 349537) (by norm_num)
theorem B1154189 : Blo 455782 1154189 := bbase (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) (by norm_num)
theorem B2202805 : Blo 455782 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1252565 : Blo 455782 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1547477 : Blo 455782 1547477 := bbase (se 7 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 1547477 = 36269) (by norm_num)
theorem B38083925 : Blo 455782 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B466273 : Blo 455782 466273 := bbase (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) (by norm_num)
theorem B1154533 : Blo 455782 1154533 := bbase (se 4 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 1154533 = 216475) (by norm_num)
theorem B826853 : Blo 455782 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B1154645 : Blo 455782 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B1547909 : Blo 455782 1547909 := bbase (se 4 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 1547909 = 290233) (by norm_num)
theorem B1154837 : Blo 455782 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B3907349 : Blo 455782 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1646453 : Blo 455782 1646453 := bbase (se 5 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 1646453 = 154355) (by norm_num)
theorem B663437 : Blo 455782 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B991205 : Blo 455782 991205 := bbase (se 4 (by rfl) ⟨92925, by rfl⟩ : syracuseStep 991205 = 185851) (by norm_num)
theorem B696325 : Blo 455782 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B696349 : Blo 455782 696349 := bbase (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) (by norm_num)
theorem B1548341 : Blo 455782 1548341 := bbase (se 5 (by rfl) ⟨72578, by rfl⟩ : syracuseStep 1548341 = 145157) (by norm_num)
theorem B7610453 : Blo 455782 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1155181 : Blo 455782 1155181 := bbase (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) (by norm_num)
theorem B1155293 : Blo 455782 1155293 := bbase (se 3 (by rfl) ⟨216617, by rfl⟩ : syracuseStep 1155293 = 433235) (by norm_num)
theorem B1155485 : Blo 455782 1155485 := bbase (se 3 (by rfl) ⟨216653, by rfl⟩ : syracuseStep 1155485 = 433307) (by norm_num)
theorem B1745333 : Blo 455782 1745333 := bbase (se 5 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 1745333 = 163625) (by norm_num)
theorem B1548773 : Blo 455782 1548773 := bbase (se 4 (by rfl) ⟨145197, by rfl⟩ : syracuseStep 1548773 = 290395) (by norm_num)
theorem B926357 : Blo 455782 926357 := bbase (se 6 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 926357 = 43423) (by norm_num)
theorem B1745621 : Blo 455782 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B1155829 : Blo 455782 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B795413 : Blo 455782 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B1155941 : Blo 455782 1155941 := bbase (se 4 (by rfl) ⟨108369, by rfl⟩ : syracuseStep 1155941 = 216739) (by norm_num)
theorem B828301 : Blo 455782 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B1549205 : Blo 455782 1549205 := bbase (se 6 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 1549205 = 72619) (by norm_num)
theorem B1156133 : Blo 455782 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B730181 : Blo 455782 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B1549637 : Blo 455782 1549637 := bbase (se 4 (by rfl) ⟨145278, by rfl⟩ : syracuseStep 1549637 = 290557) (by norm_num)
theorem B1156477 : Blo 455782 1156477 := bbase (se 3 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 1156477 = 433679) (by norm_num)
theorem B1156589 : Blo 455782 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B1025549 : Blo 455782 1025549 := bbase (se 3 (by rfl) ⟨192290, by rfl⟩ : syracuseStep 1025549 = 384581) (by norm_num)
theorem B1058333 : Blo 455782 1058333 := bbase (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) (by norm_num)
theorem B697901 : Blo 455782 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B1025621 : Blo 455782 1025621 := bbase (se 8 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 1025621 = 12019) (by norm_num)
theorem B1025693 : Blo 455782 1025693 := bbase (se 3 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 1025693 = 384635) (by norm_num)
theorem B1156781 : Blo 455782 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B1025765 : Blo 455782 1025765 := bbase (se 4 (by rfl) ⟨96165, by rfl⟩ : syracuseStep 1025765 = 192331) (by norm_num)
theorem B1550069 : Blo 455782 1550069 := bbase (se 5 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 1550069 = 145319) (by norm_num)
theorem B927485 : Blo 455782 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B1025837 : Blo 455782 1025837 := bbase (se 3 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 1025837 = 384689) (by norm_num)
theorem B1025909 : Blo 455782 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B1025981 : Blo 455782 1025981 := bbase (se 3 (by rfl) ⟨192371, by rfl⟩ : syracuseStep 1025981 = 384743) (by norm_num)
theorem B1026053 : Blo 455782 1026053 := bbase (se 4 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 1026053 = 192385) (by norm_num)
theorem B1157125 : Blo 455782 1157125 := bbase (se 4 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 1157125 = 216961) (by norm_num)
theorem B1026125 : Blo 455782 1026125 := bbase (se 3 (by rfl) ⟨192398, by rfl⟩ : syracuseStep 1026125 = 384797) (by norm_num)
theorem B1157237 : Blo 455782 1157237 := bbase (se 5 (by rfl) ⟨54245, by rfl⟩ : syracuseStep 1157237 = 108491) (by norm_num)
theorem B1026197 : Blo 455782 1026197 := bbase (se 6 (by rfl) ⟨24051, by rfl⟩ : syracuseStep 1026197 = 48103) (by norm_num)
theorem B1550501 : Blo 455782 1550501 := bbase (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) (by norm_num)
theorem B698533 : Blo 455782 698533 := bbase (se 4 (by rfl) ⟨65487, by rfl⟩ : syracuseStep 698533 = 130975) (by norm_num)
theorem B1026269 : Blo 455782 1026269 := bbase (se 3 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 1026269 = 384851) (by norm_num)
theorem B4466933 : Blo 455782 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B1026341 : Blo 455782 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B1157429 : Blo 455782 1157429 := bbase (se 5 (by rfl) ⟨54254, by rfl⟩ : syracuseStep 1157429 = 108509) (by norm_num)
theorem B1026413 : Blo 455782 1026413 := bbase (se 3 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 1026413 = 384905) (by norm_num)
theorem B731501 : Blo 455782 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B1026485 : Blo 455782 1026485 := bbase (se 5 (by rfl) ⟨48116, by rfl⟩ : syracuseStep 1026485 = 96233) (by norm_num)
theorem B731597 : Blo 455782 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B731629 : Blo 455782 731629 := bbase (se 3 (by rfl) ⟨137180, by rfl⟩ : syracuseStep 731629 = 274361) (by norm_num)
theorem B1026557 : Blo 455782 1026557 := bbase (se 3 (by rfl) ⟨192479, by rfl⟩ : syracuseStep 1026557 = 384959) (by norm_num)
theorem B1026629 : Blo 455782 1026629 := bbase (se 4 (by rfl) ⟨96246, by rfl⟩ : syracuseStep 1026629 = 192493) (by norm_num)
theorem B1550933 : Blo 455782 1550933 := bbase (se 8 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 1550933 = 18175) (by norm_num)
theorem B2108005 : Blo 455782 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B1026701 : Blo 455782 1026701 := bbase (se 3 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 1026701 = 385013) (by norm_num)
theorem B1157773 : Blo 455782 1157773 := bbase (se 3 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 1157773 = 434165) (by norm_num)
theorem B2927285 : Blo 455782 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B1026773 : Blo 455782 1026773 := bbase (se 7 (by rfl) ⟨12032, by rfl⟩ : syracuseStep 1026773 = 24065) (by norm_num)
theorem B1157885 : Blo 455782 1157885 := bbase (se 3 (by rfl) ⟨217103, by rfl⟩ : syracuseStep 1157885 = 434207) (by norm_num)
theorem B7842581 : Blo 455782 7842581 := bbase (se 6 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 7842581 = 367621) (by norm_num)
theorem B1026845 : Blo 455782 1026845 := bbase (se 3 (by rfl) ⟨192533, by rfl⟩ : syracuseStep 1026845 = 385067) (by norm_num)
theorem B1026917 : Blo 455782 1026917 := bbase (se 4 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 1026917 = 192547) (by norm_num)
theorem B1026989 : Blo 455782 1026989 := bbase (se 3 (by rfl) ⟨192560, by rfl⟩ : syracuseStep 1026989 = 385121) (by norm_num)
theorem B1158077 : Blo 455782 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B1027061 : Blo 455782 1027061 := bbase (se 5 (by rfl) ⟨48143, by rfl⟩ : syracuseStep 1027061 = 96287) (by norm_num)
theorem B1551365 : Blo 455782 1551365 := bbase (se 4 (by rfl) ⟨145440, by rfl⟩ : syracuseStep 1551365 = 290881) (by norm_num)
theorem B1027133 : Blo 455782 1027133 := bbase (se 3 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 1027133 = 385175) (by norm_num)
theorem B1027205 : Blo 455782 1027205 := bbase (se 4 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 1027205 = 192601) (by norm_num)
theorem B601241 : Blo 455782 601241 := bbase (se 2 (by rfl) ⟨225465, by rfl⟩ : syracuseStep 601241 = 450931) (by norm_num)
theorem B1027277 : Blo 455782 1027277 := bbase (se 3 (by rfl) ⟨192614, by rfl⟩ : syracuseStep 1027277 = 385229) (by norm_num)
theorem B1027349 : Blo 455782 1027349 := bbase (se 6 (by rfl) ⟨24078, by rfl⟩ : syracuseStep 1027349 = 48157) (by norm_num)
theorem B1158421 : Blo 455782 1158421 := bbase (se 6 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 1158421 = 54301) (by norm_num)
theorem B1027421 : Blo 455782 1027421 := bbase (se 3 (by rfl) ⟨192641, by rfl⟩ : syracuseStep 1027421 = 385283) (by norm_num)
theorem B1158533 : Blo 455782 1158533 := bbase (se 4 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 1158533 = 217225) (by norm_num)
theorem B1027493 : Blo 455782 1027493 := bbase (se 4 (by rfl) ⟨96327, by rfl⟩ : syracuseStep 1027493 = 192655) (by norm_num)
theorem B4402613 : Blo 455782 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B2207189 : Blo 455782 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B1027565 : Blo 455782 1027565 := bbase (se 3 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 1027565 = 385337) (by norm_num)
theorem B1027637 : Blo 455782 1027637 := bbase (se 5 (by rfl) ⟨48170, by rfl⟩ : syracuseStep 1027637 = 96341) (by norm_num)
theorem B1158725 : Blo 455782 1158725 := bbase (se 4 (by rfl) ⟨108630, by rfl⟩ : syracuseStep 1158725 = 217261) (by norm_num)
theorem B1027709 : Blo 455782 1027709 := bbase (se 3 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 1027709 = 385391) (by norm_num)
theorem B1027781 : Blo 455782 1027781 := bbase (se 4 (by rfl) ⟨96354, by rfl⟩ : syracuseStep 1027781 = 192709) (by norm_num)
theorem B1027853 : Blo 455782 1027853 := bbase (se 3 (by rfl) ⟨192722, by rfl⟩ : syracuseStep 1027853 = 385445) (by norm_num)
theorem B1027925 : Blo 455782 1027925 := bbase (se 9 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 1027925 = 6023) (by norm_num)
theorem B1027997 : Blo 455782 1027997 := bbase (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) (by norm_num)
theorem B1159069 : Blo 455782 1159069 := bbase (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) (by norm_num)
theorem B733141 : Blo 455782 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B1028069 : Blo 455782 1028069 := bbase (se 4 (by rfl) ⟨96381, by rfl⟩ : syracuseStep 1028069 = 192763) (by norm_num)
theorem B1159181 : Blo 455782 1159181 := bbase (se 3 (by rfl) ⟨217346, by rfl⟩ : syracuseStep 1159181 = 434693) (by norm_num)
theorem B2600981 : Blo 455782 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B1028141 : Blo 455782 1028141 := bbase (se 3 (by rfl) ⟨192776, by rfl⟩ : syracuseStep 1028141 = 385553) (by norm_num)
theorem B929893 : Blo 455782 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B1028213 : Blo 455782 1028213 := bbase (se 5 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 1028213 = 96395) (by norm_num)
theorem B1028285 : Blo 455782 1028285 := bbase (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) (by norm_num)
theorem B1159373 : Blo 455782 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1028357 : Blo 455782 1028357 := bbase (se 4 (by rfl) ⟨96408, by rfl⟩ : syracuseStep 1028357 = 192817) (by norm_num)
theorem B1323317 : Blo 455782 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1028429 : Blo 455782 1028429 := bbase (se 3 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 1028429 = 385661) (by norm_num)
theorem B1028501 : Blo 455782 1028501 := bbase (se 6 (by rfl) ⟨24105, by rfl⟩ : syracuseStep 1028501 = 48211) (by norm_num)
theorem B1028573 : Blo 455782 1028573 := bbase (se 3 (by rfl) ⟨192857, by rfl⟩ : syracuseStep 1028573 = 385715) (by norm_num)
theorem B930341 : Blo 455782 930341 := bbase (se 4 (by rfl) ⟨87219, by rfl⟩ : syracuseStep 930341 = 174439) (by norm_num)
theorem B1028645 : Blo 455782 1028645 := bbase (se 4 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 1028645 = 192871) (by norm_num)
theorem B1159717 : Blo 455782 1159717 := bbase (se 4 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 1159717 = 217447) (by norm_num)
theorem B1028717 : Blo 455782 1028717 := bbase (se 3 (by rfl) ⟨192884, by rfl⟩ : syracuseStep 1028717 = 385769) (by norm_num)
theorem B1159829 : Blo 455782 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B733853 : Blo 455782 733853 := bbase (se 3 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 733853 = 275195) (by norm_num)
theorem B1028789 : Blo 455782 1028789 := bbase (se 5 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 1028789 = 96449) (by norm_num)
theorem B1028861 : Blo 455782 1028861 := bbase (se 3 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 1028861 = 385823) (by norm_num)
theorem B1028933 : Blo 455782 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B1160021 : Blo 455782 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1029005 : Blo 455782 1029005 := bbase (se 3 (by rfl) ⟨192938, by rfl⟩ : syracuseStep 1029005 = 385877) (by norm_num)
theorem B1029077 : Blo 455782 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B1029149 : Blo 455782 1029149 := bbase (se 3 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 1029149 = 385931) (by norm_num)
theorem B1029221 : Blo 455782 1029221 := bbase (se 4 (by rfl) ⟨96489, by rfl⟩ : syracuseStep 1029221 = 192979) (by norm_num)
theorem B1029293 : Blo 455782 1029293 := bbase (se 3 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 1029293 = 385985) (by norm_num)
theorem B1160365 : Blo 455782 1160365 := bbase (se 3 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 1160365 = 435137) (by norm_num)
theorem B2602165 : Blo 455782 2602165 := bbase (se 5 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 2602165 = 243953) (by norm_num)
theorem B1029365 : Blo 455782 1029365 := bbase (se 5 (by rfl) ⟨48251, by rfl⟩ : syracuseStep 1029365 = 96503) (by norm_num)
theorem B1160477 : Blo 455782 1160477 := bbase (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) (by norm_num)
theorem B1029437 : Blo 455782 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B734525 : Blo 455782 734525 := bbase (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) (by norm_num)
theorem B1029509 : Blo 455782 1029509 := bbase (se 4 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 1029509 = 193033) (by norm_num)
theorem B865741 : Blo 455782 865741 := bbase (se 3 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 865741 = 324653) (by norm_num)
theorem B1029581 : Blo 455782 1029581 := bbase (se 3 (by rfl) ⟨193046, by rfl⟩ : syracuseStep 1029581 = 386093) (by norm_num)
theorem B1160669 : Blo 455782 1160669 := bbase (se 3 (by rfl) ⟨217625, by rfl⟩ : syracuseStep 1160669 = 435251) (by norm_num)
theorem B2635253 : Blo 455782 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B1029653 : Blo 455782 1029653 := bbase (se 6 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 1029653 = 48265) (by norm_num)
theorem B865885 : Blo 455782 865885 := bbase (se 3 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 865885 = 324707) (by norm_num)
theorem B1029725 : Blo 455782 1029725 := bbase (se 3 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 1029725 = 386147) (by norm_num)
theorem B1029797 : Blo 455782 1029797 := bbase (se 4 (by rfl) ⟨96543, by rfl⟩ : syracuseStep 1029797 = 193087) (by norm_num)
theorem B1029869 : Blo 455782 1029869 := bbase (se 3 (by rfl) ⟨193100, by rfl⟩ : syracuseStep 1029869 = 386201) (by norm_num)
theorem B866045 : Blo 455782 866045 := bbase (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) (by norm_num)
theorem B3127061 : Blo 455782 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1029941 : Blo 455782 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B1161013 : Blo 455782 1161013 := bbase (se 5 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 1161013 = 108845) (by norm_num)
theorem B931637 : Blo 455782 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B735037 : Blo 455782 735037 := bbase (se 3 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 735037 = 275639) (by norm_num)
theorem B1947509 : Blo 455782 1947509 := bbase (se 5 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 1947509 = 182579) (by norm_num)
theorem B1030013 : Blo 455782 1030013 := bbase (se 3 (by rfl) ⟨193127, by rfl⟩ : syracuseStep 1030013 = 386255) (by norm_num)
theorem B866189 : Blo 455782 866189 := bbase (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) (by norm_num)
theorem B1161125 : Blo 455782 1161125 := bbase (se 4 (by rfl) ⟨108855, by rfl⟩ : syracuseStep 1161125 = 217711) (by norm_num)
theorem B1030085 : Blo 455782 1030085 := bbase (se 4 (by rfl) ⟨96570, by rfl⟩ : syracuseStep 1030085 = 193141) (by norm_num)
theorem B1030157 : Blo 455782 1030157 := bbase (se 3 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 1030157 = 386309) (by norm_num)
theorem B1030229 : Blo 455782 1030229 := bbase (se 8 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 1030229 = 12073) (by norm_num)
theorem B1161317 : Blo 455782 1161317 := bbase (se 4 (by rfl) ⟨108873, by rfl⟩ : syracuseStep 1161317 = 217747) (by norm_num)
theorem B1947797 : Blo 455782 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B1030301 : Blo 455782 1030301 := bbase (se 3 (by rfl) ⟨193181, by rfl⟩ : syracuseStep 1030301 = 386363) (by norm_num)
theorem B866477 : Blo 455782 866477 := bbase (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) (by norm_num)
theorem B1030373 : Blo 455782 1030373 := bbase (se 4 (by rfl) ⟨96597, by rfl⟩ : syracuseStep 1030373 = 193195) (by norm_num)
theorem B1128701 : Blo 455782 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B735493 : Blo 455782 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B3488021 : Blo 455782 3488021 := bbase (se 6 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 3488021 = 163501) (by norm_num)
theorem B1030445 : Blo 455782 1030445 := bbase (se 3 (by rfl) ⟨193208, by rfl⟩ : syracuseStep 1030445 = 386417) (by norm_num)
theorem B866629 : Blo 455782 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B1096021 : Blo 455782 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B1030517 : Blo 455782 1030517 := bbase (se 5 (by rfl) ⟨48305, by rfl⟩ : syracuseStep 1030517 = 96611) (by norm_num)
theorem B1030589 : Blo 455782 1030589 := bbase (se 3 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 1030589 = 386471) (by norm_num)
theorem B1161661 : Blo 455782 1161661 := bbase (se 3 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 1161661 = 435623) (by norm_num)
theorem B1030661 : Blo 455782 1030661 := bbase (se 4 (by rfl) ⟨96624, by rfl⟩ : syracuseStep 1030661 = 193249) (by norm_num)
theorem B1391141 : Blo 455782 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B1325605 : Blo 455782 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B1161773 : Blo 455782 1161773 := bbase (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) (by norm_num)
theorem B2308661 : Blo 455782 2308661 := bbase (se 5 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 2308661 = 216437) (by norm_num)
theorem B1653317 : Blo 455782 1653317 := bbase (se 4 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 1653317 = 309997) (by norm_num)
theorem B1030733 : Blo 455782 1030733 := bbase (se 3 (by rfl) ⟨193262, by rfl⟩ : syracuseStep 1030733 = 386525) (by norm_num)
theorem B866933 : Blo 455782 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B1030805 : Blo 455782 1030805 := bbase (se 6 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 1030805 = 48319) (by norm_num)
theorem B1030877 : Blo 455782 1030877 := bbase (se 3 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 1030877 = 386579) (by norm_num)
theorem B1161965 : Blo 455782 1161965 := bbase (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) (by norm_num)
theorem B1030949 : Blo 455782 1030949 := bbase (se 4 (by rfl) ⟨96651, by rfl⟩ : syracuseStep 1030949 = 193303) (by norm_num)
theorem B22362965 : Blo 455782 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B1653605 : Blo 455782 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1031021 : Blo 455782 1031021 := bbase (se 3 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 1031021 = 386633) (by norm_num)
theorem B1948549 : Blo 455782 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B736165 : Blo 455782 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B1031093 : Blo 455782 1031093 := bbase (se 5 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 1031093 = 96665) (by norm_num)
theorem B1653749 : Blo 455782 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1031165 : Blo 455782 1031165 := bbase (se 3 (by rfl) ⟨193343, by rfl⟩ : syracuseStep 1031165 = 386687) (by norm_num)
theorem B1031237 : Blo 455782 1031237 := bbase (se 4 (by rfl) ⟨96678, by rfl⟩ : syracuseStep 1031237 = 193357) (by norm_num)
theorem B1162309 : Blo 455782 1162309 := bbase (se 4 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 1162309 = 217933) (by norm_num)
theorem B2604149 : Blo 455782 2604149 := bbase (se 5 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 2604149 = 244139) (by norm_num)
theorem B1031309 : Blo 455782 1031309 := bbase (se 3 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 1031309 = 386741) (by norm_num)
theorem B769189 : Blo 455782 769189 := bbase (se 4 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 769189 = 144223) (by norm_num)
theorem B1162421 : Blo 455782 1162421 := bbase (se 5 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 1162421 = 108977) (by norm_num)
theorem B1031381 : Blo 455782 1031381 := bbase (se 7 (by rfl) ⟨12086, by rfl⟩ : syracuseStep 1031381 = 24173) (by norm_num)
theorem B769277 : Blo 455782 769277 := bbase (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) (by norm_num)
theorem B1031453 : Blo 455782 1031453 := bbase (se 3 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 1031453 = 386795) (by norm_num)
theorem B867685 : Blo 455782 867685 := bbase (se 4 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 867685 = 162691) (by norm_num)
theorem B1031525 : Blo 455782 1031525 := bbase (se 4 (by rfl) ⟨96705, by rfl⟩ : syracuseStep 1031525 = 193411) (by norm_num)
theorem B1162613 : Blo 455782 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B769405 : Blo 455782 769405 := bbase (se 3 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 769405 = 288527) (by norm_num)
theorem B1031597 : Blo 455782 1031597 := bbase (se 3 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 1031597 = 386849) (by norm_num)
theorem B2080181 : Blo 455782 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B769493 : Blo 455782 769493 := bbase (se 7 (by rfl) ⟨9017, by rfl⟩ : syracuseStep 769493 = 18035) (by norm_num)
theorem B867829 : Blo 455782 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B1031669 : Blo 455782 1031669 := bbase (se 5 (by rfl) ⟨48359, by rfl⟩ : syracuseStep 1031669 = 96719) (by norm_num)
theorem B1031741 : Blo 455782 1031741 := bbase (se 3 (by rfl) ⟨193451, by rfl⟩ : syracuseStep 1031741 = 386903) (by norm_num)
theorem B769621 : Blo 455782 769621 := bbase (se 8 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 769621 = 9019) (by norm_num)
theorem B1949285 : Blo 455782 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B1031813 : Blo 455782 1031813 := bbase (se 4 (by rfl) ⟨96732, by rfl⟩ : syracuseStep 1031813 = 193465) (by norm_num)
theorem B867989 : Blo 455782 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B769709 : Blo 455782 769709 := bbase (se 3 (by rfl) ⟨144320, by rfl⟩ : syracuseStep 769709 = 288641) (by norm_num)
theorem B1097405 : Blo 455782 1097405 := bbase (se 3 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 1097405 = 411527) (by norm_num)
theorem B1031885 : Blo 455782 1031885 := bbase (se 3 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 1031885 = 386957) (by norm_num)
theorem B1162957 : Blo 455782 1162957 := bbase (se 3 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 1162957 = 436109) (by norm_num)
theorem B1031957 : Blo 455782 1031957 := bbase (se 6 (by rfl) ⟨24186, by rfl⟩ : syracuseStep 1031957 = 48373) (by norm_num)
theorem B868133 : Blo 455782 868133 := bbase (se 4 (by rfl) ⟨81387, by rfl⟩ : syracuseStep 868133 = 162775) (by norm_num)
theorem B769837 : Blo 455782 769837 := bbase (se 3 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 769837 = 288689) (by norm_num)
theorem B1163069 : Blo 455782 1163069 := bbase (se 3 (by rfl) ⟨218075, by rfl⟩ : syracuseStep 1163069 = 436151) (by norm_num)
theorem B2309957 : Blo 455782 2309957 := bbase (se 4 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 2309957 = 433117) (by norm_num)
theorem B1032029 : Blo 455782 1032029 := bbase (se 3 (by rfl) ⟨193505, by rfl⟩ : syracuseStep 1032029 = 387011) (by norm_num)
theorem B1097597 : Blo 455782 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B769925 : Blo 455782 769925 := bbase (se 4 (by rfl) ⟨72180, by rfl⟩ : syracuseStep 769925 = 144361) (by norm_num)
theorem B1032101 : Blo 455782 1032101 := bbase (se 4 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 1032101 = 193519) (by norm_num)
theorem B1032173 : Blo 455782 1032173 := bbase (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) (by norm_num)
theorem B1163261 : Blo 455782 1163261 := bbase (se 3 (by rfl) ⟨218111, by rfl⟩ : syracuseStep 1163261 = 436223) (by norm_num)
theorem B770053 : Blo 455782 770053 := bbase (se 4 (by rfl) ⟨72192, by rfl⟩ : syracuseStep 770053 = 144385) (by norm_num)
theorem B1032245 : Blo 455782 1032245 := bbase (se 5 (by rfl) ⟨48386, by rfl⟩ : syracuseStep 1032245 = 96773) (by norm_num)
theorem B868421 : Blo 455782 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B770141 : Blo 455782 770141 := bbase (se 3 (by rfl) ⟨144401, by rfl⟩ : syracuseStep 770141 = 288803) (by norm_num)
theorem B1032317 : Blo 455782 1032317 := bbase (se 3 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 1032317 = 387119) (by norm_num)
theorem B1032389 : Blo 455782 1032389 := bbase (se 4 (by rfl) ⟨96786, by rfl⟩ : syracuseStep 1032389 = 193573) (by norm_num)
theorem B2932949 : Blo 455782 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B770269 : Blo 455782 770269 := bbase (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) (by norm_num)
theorem B868573 : Blo 455782 868573 := bbase (se 3 (by rfl) ⟨162857, by rfl⟩ : syracuseStep 868573 = 325715) (by norm_num)
theorem B1032461 : Blo 455782 1032461 := bbase (se 3 (by rfl) ⟨193586, by rfl⟩ : syracuseStep 1032461 = 387173) (by norm_num)
theorem B770357 : Blo 455782 770357 := bbase (se 5 (by rfl) ⟨36110, by rfl⟩ : syracuseStep 770357 = 72221) (by norm_num)
theorem B1032533 : Blo 455782 1032533 := bbase (se 10 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 1032533 = 3025) (by norm_num)
theorem B1163605 : Blo 455782 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B1032605 : Blo 455782 1032605 := bbase (se 3 (by rfl) ⟨193613, by rfl⟩ : syracuseStep 1032605 = 387227) (by norm_num)
theorem B770485 : Blo 455782 770485 := bbase (se 5 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 770485 = 72233) (by norm_num)
theorem B1163717 : Blo 455782 1163717 := bbase (se 4 (by rfl) ⟨109098, by rfl⟩ : syracuseStep 1163717 = 218197) (by norm_num)
theorem B1032677 : Blo 455782 1032677 := bbase (se 4 (by rfl) ⟨96813, by rfl⟩ : syracuseStep 1032677 = 193627) (by norm_num)
theorem B770573 : Blo 455782 770573 := bbase (se 3 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 770573 = 288965) (by norm_num)
theorem B868877 : Blo 455782 868877 := bbase (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) (by norm_num)
theorem B1032749 : Blo 455782 1032749 := bbase (se 3 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 1032749 = 387281) (by norm_num)
theorem B1032821 : Blo 455782 1032821 := bbase (se 5 (by rfl) ⟨48413, by rfl⟩ : syracuseStep 1032821 = 96827) (by norm_num)
theorem B770701 : Blo 455782 770701 := bbase (se 3 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 770701 = 289013) (by norm_num)
theorem B1032893 : Blo 455782 1032893 := bbase (se 3 (by rfl) ⟨193667, by rfl⟩ : syracuseStep 1032893 = 387335) (by norm_num)
theorem B770789 : Blo 455782 770789 := bbase (se 4 (by rfl) ⟨72261, by rfl⟩ : syracuseStep 770789 = 144523) (by norm_num)
theorem B1032965 : Blo 455782 1032965 := bbase (se 4 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 1032965 = 193681) (by norm_num)
theorem B1033037 : Blo 455782 1033037 := bbase (se 3 (by rfl) ⟨193694, by rfl⟩ : syracuseStep 1033037 = 387389) (by norm_num)
theorem B770917 : Blo 455782 770917 := bbase (se 4 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 770917 = 144547) (by norm_num)
theorem B1033109 : Blo 455782 1033109 := bbase (se 6 (by rfl) ⟨24213, by rfl⟩ : syracuseStep 1033109 = 48427) (by norm_num)
theorem B771005 : Blo 455782 771005 := bbase (se 3 (by rfl) ⟨144563, by rfl⟩ : syracuseStep 771005 = 289127) (by norm_num)
theorem B1033181 : Blo 455782 1033181 := bbase (se 3 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 1033181 = 387443) (by norm_num)
theorem B1033253 : Blo 455782 1033253 := bbase (se 4 (by rfl) ⟨96867, by rfl⟩ : syracuseStep 1033253 = 193735) (by norm_num)
theorem B771133 : Blo 455782 771133 := bbase (se 3 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 771133 = 289175) (by norm_num)
theorem B2311253 : Blo 455782 2311253 := bbase (se 8 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 2311253 = 27085) (by norm_num)
theorem B1033325 : Blo 455782 1033325 := bbase (se 3 (by rfl) ⟨193748, by rfl⟩ : syracuseStep 1033325 = 387497) (by norm_num)
theorem B771221 : Blo 455782 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B1033397 : Blo 455782 1033397 := bbase (se 5 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 1033397 = 96881) (by norm_num)
theorem B869629 : Blo 455782 869629 := bbase (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) (by norm_num)
theorem B1033469 : Blo 455782 1033469 := bbase (se 3 (by rfl) ⟨193775, by rfl⟩ : syracuseStep 1033469 = 387551) (by norm_num)
theorem B771349 : Blo 455782 771349 := bbase (se 6 (by rfl) ⟨18078, by rfl⟩ : syracuseStep 771349 = 36157) (by norm_num)
theorem B2606357 : Blo 455782 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B1983797 : Blo 455782 1983797 := bbase (se 5 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 1983797 = 185981) (by norm_num)
theorem B1033541 : Blo 455782 1033541 := bbase (se 4 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 1033541 = 193789) (by norm_num)
theorem B771437 : Blo 455782 771437 := bbase (se 3 (by rfl) ⟨144644, by rfl⟩ : syracuseStep 771437 = 289289) (by norm_num)
theorem B705925 : Blo 455782 705925 := bbase (se 4 (by rfl) ⟨66180, by rfl⟩ : syracuseStep 705925 = 132361) (by norm_num)
theorem B869773 : Blo 455782 869773 := bbase (se 3 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 869773 = 326165) (by norm_num)
theorem B1033613 : Blo 455782 1033613 := bbase (se 3 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 1033613 = 387605) (by norm_num)
theorem B1099165 : Blo 455782 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B1033685 : Blo 455782 1033685 := bbase (se 7 (by rfl) ⟨12113, by rfl⟩ : syracuseStep 1033685 = 24227) (by norm_num)
theorem B771565 : Blo 455782 771565 := bbase (se 3 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 771565 = 289337) (by norm_num)
theorem B1033757 : Blo 455782 1033757 := bbase (se 3 (by rfl) ⟨193829, by rfl⟩ : syracuseStep 1033757 = 387659) (by norm_num)
theorem B1590821 : Blo 455782 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B869933 : Blo 455782 869933 := bbase (se 3 (by rfl) ⟨163112, by rfl⟩ : syracuseStep 869933 = 326225) (by norm_num)
theorem B771653 : Blo 455782 771653 := bbase (se 4 (by rfl) ⟨72342, by rfl⟩ : syracuseStep 771653 = 144685) (by norm_num)
theorem B1033829 : Blo 455782 1033829 := bbase (se 4 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 1033829 = 193843) (by norm_num)
theorem B1033901 : Blo 455782 1033901 := bbase (se 3 (by rfl) ⟨193856, by rfl⟩ : syracuseStep 1033901 = 387713) (by norm_num)
theorem B870077 : Blo 455782 870077 := bbase (se 3 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 870077 = 326279) (by norm_num)
theorem B771781 : Blo 455782 771781 := bbase (se 4 (by rfl) ⟨72354, by rfl⟩ : syracuseStep 771781 = 144709) (by norm_num)
theorem B1033973 : Blo 455782 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B771869 : Blo 455782 771869 := bbase (se 3 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 771869 = 289451) (by norm_num)
theorem B1034045 : Blo 455782 1034045 := bbase (se 3 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 1034045 = 387767) (by norm_num)
theorem B1034117 : Blo 455782 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B771997 : Blo 455782 771997 := bbase (se 3 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 771997 = 289499) (by norm_num)
theorem B1034189 : Blo 455782 1034189 := bbase (se 3 (by rfl) ⟨193910, by rfl⟩ : syracuseStep 1034189 = 387821) (by norm_num)
theorem B870365 : Blo 455782 870365 := bbase (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) (by norm_num)
theorem B772085 : Blo 455782 772085 := bbase (se 5 (by rfl) ⟨36191, by rfl⟩ : syracuseStep 772085 = 72383) (by norm_num)
theorem B1099781 : Blo 455782 1099781 := bbase (se 4 (by rfl) ⟨103104, by rfl⟩ : syracuseStep 1099781 = 206209) (by norm_num)
theorem B4769813 : Blo 455782 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034261 : Blo 455782 1034261 := bbase (se 6 (by rfl) ⟨24240, by rfl⟩ : syracuseStep 1034261 = 48481) (by norm_num)
theorem B1001501 : Blo 455782 1001501 := bbase (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) (by norm_num)
theorem B1034333 : Blo 455782 1034333 := bbase (se 3 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 1034333 = 387875) (by norm_num)
theorem B772213 : Blo 455782 772213 := bbase (se 5 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 772213 = 72395) (by norm_num)
theorem B870517 : Blo 455782 870517 := bbase (se 5 (by rfl) ⟨40805, by rfl⟩ : syracuseStep 870517 = 81611) (by norm_num)
theorem B1656949 : Blo 455782 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1034405 : Blo 455782 1034405 := bbase (se 4 (by rfl) ⟨96975, by rfl⟩ : syracuseStep 1034405 = 193951) (by norm_num)
theorem B772301 : Blo 455782 772301 := bbase (se 3 (by rfl) ⟨144806, by rfl⟩ : syracuseStep 772301 = 289613) (by norm_num)
theorem B1034477 : Blo 455782 1034477 := bbase (se 3 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 1034477 = 387929) (by norm_num)
theorem B772429 : Blo 455782 772429 := bbase (se 3 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 772429 = 289661) (by norm_num)
theorem B2312549 : Blo 455782 2312549 := bbase (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) (by norm_num)
theorem B903565 : Blo 455782 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B772517 : Blo 455782 772517 := bbase (se 4 (by rfl) ⟨72423, by rfl⟩ : syracuseStep 772517 = 144847) (by norm_num)
theorem B870821 : Blo 455782 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B772645 : Blo 455782 772645 := bbase (se 4 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 772645 = 144871) (by norm_num)
theorem B772733 : Blo 455782 772733 := bbase (se 3 (by rfl) ⟨144887, by rfl⟩ : syracuseStep 772733 = 289775) (by norm_num)
theorem B3721909 : Blo 455782 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B9358037 : Blo 455782 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B772861 : Blo 455782 772861 := bbase (se 3 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 772861 = 289823) (by norm_num)
theorem B1100557 : Blo 455782 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B1952581 : Blo 455782 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B772949 : Blo 455782 772949 := bbase (se 9 (by rfl) ⟨2264, by rfl⟩ : syracuseStep 772949 = 4529) (by norm_num)
theorem B773077 : Blo 455782 773077 := bbase (se 7 (by rfl) ⟨9059, by rfl⟩ : syracuseStep 773077 = 18119) (by norm_num)
theorem B773165 : Blo 455782 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B3132533 : Blo 455782 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B871573 : Blo 455782 871573 := bbase (se 6 (by rfl) ⟨20427, by rfl⟩ : syracuseStep 871573 = 40855) (by norm_num)
theorem B773293 : Blo 455782 773293 := bbase (se 3 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 773293 = 289985) (by norm_num)
theorem B773381 : Blo 455782 773381 := bbase (se 4 (by rfl) ⟨72504, by rfl⟩ : syracuseStep 773381 = 145009) (by norm_num)
theorem B5229845 : Blo 455782 5229845 := bbase (se 6 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 5229845 = 245149) (by norm_num)
theorem B871717 : Blo 455782 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B576877 : Blo 455782 576877 := bbase (se 3 (by rfl) ⟨108164, by rfl⟩ : syracuseStep 576877 = 216329) (by norm_num)
theorem B773509 : Blo 455782 773509 := bbase (se 4 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 773509 = 145033) (by norm_num)
theorem B871877 : Blo 455782 871877 := bbase (se 4 (by rfl) ⟨81738, by rfl⟩ : syracuseStep 871877 = 163477) (by norm_num)
theorem B576973 : Blo 455782 576973 := bbase (se 3 (by rfl) ⟨108182, by rfl⟩ : syracuseStep 576973 = 216365) (by norm_num)
theorem B1101269 : Blo 455782 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B773597 : Blo 455782 773597 := bbase (se 3 (by rfl) ⟨145049, by rfl⟩ : syracuseStep 773597 = 290099) (by norm_num)
theorem B3132917 : Blo 455782 3132917 := bbase (se 5 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 3132917 = 293711) (by norm_num)
theorem B1461797 : Blo 455782 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B872021 : Blo 455782 872021 := bbase (se 8 (by rfl) ⟨5109, by rfl⟩ : syracuseStep 872021 = 10219) (by norm_num)
theorem B773725 : Blo 455782 773725 := bbase (se 3 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 773725 = 290147) (by norm_num)
theorem B2313845 : Blo 455782 2313845 := bbase (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) (by norm_num)
theorem B577145 : Blo 455782 577145 := bbase (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) (by norm_num)
theorem B577201 : Blo 455782 577201 := bbase (se 2 (by rfl) ⟨216450, by rfl⟩ : syracuseStep 577201 = 432901) (by norm_num)
theorem B773813 : Blo 455782 773813 := bbase (se 5 (by rfl) ⟨36272, by rfl⟩ : syracuseStep 773813 = 72545) (by norm_num)
theorem B577297 : Blo 455782 577297 := bbase (se 2 (by rfl) ⟨216486, by rfl⟩ : syracuseStep 577297 = 432973) (by norm_num)
theorem B1298213 : Blo 455782 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B773941 : Blo 455782 773941 := bbase (se 5 (by rfl) ⟨36278, by rfl⟩ : syracuseStep 773941 = 72557) (by norm_num)
theorem B872309 : Blo 455782 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B774029 : Blo 455782 774029 := bbase (se 3 (by rfl) ⟨145130, by rfl⟩ : syracuseStep 774029 = 290261) (by norm_num)
theorem B577469 : Blo 455782 577469 := bbase (se 3 (by rfl) ⟨108275, by rfl⟩ : syracuseStep 577469 = 216551) (by norm_num)
theorem B577525 : Blo 455782 577525 := bbase (se 5 (by rfl) ⟨27071, by rfl⟩ : syracuseStep 577525 = 54143) (by norm_num)
theorem B970741 : Blo 455782 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B774157 : Blo 455782 774157 := bbase (se 3 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 774157 = 290309) (by norm_num)
theorem B872461 : Blo 455782 872461 := bbase (se 3 (by rfl) ⟨163586, by rfl⟩ : syracuseStep 872461 = 327173) (by norm_num)
theorem B577621 : Blo 455782 577621 := bbase (se 8 (by rfl) ⟨3384, by rfl⟩ : syracuseStep 577621 = 6769) (by norm_num)
theorem B774245 : Blo 455782 774245 := bbase (se 4 (by rfl) ⟨72585, by rfl⟩ : syracuseStep 774245 = 145171) (by norm_num)
theorem B1101941 : Blo 455782 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B774373 : Blo 455782 774373 := bbase (se 4 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 774373 = 145195) (by norm_num)
theorem B2773237 : Blo 455782 2773237 := bbase (se 5 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 2773237 = 259991) (by norm_num)
theorem B577793 : Blo 455782 577793 := bbase (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) (by norm_num)
theorem B1069325 : Blo 455782 1069325 := bbase (se 3 (by rfl) ⟨200498, by rfl⟩ : syracuseStep 1069325 = 400997) (by norm_num)
theorem B577849 : Blo 455782 577849 := bbase (se 2 (by rfl) ⟨216693, by rfl⟩ : syracuseStep 577849 = 433387) (by norm_num)
theorem B774461 : Blo 455782 774461 := bbase (se 3 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 774461 = 290423) (by norm_num)
theorem B872765 : Blo 455782 872765 := bbase (se 3 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 872765 = 327287) (by norm_num)
theorem B577945 : Blo 455782 577945 := bbase (se 2 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 577945 = 433459) (by norm_num)
theorem B1462693 : Blo 455782 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B2347429 : Blo 455782 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B774589 : Blo 455782 774589 := bbase (se 3 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 774589 = 290471) (by norm_num)
theorem B2118149 : Blo 455782 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B774677 : Blo 455782 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B578117 : Blo 455782 578117 := bbase (se 4 (by rfl) ⟨54198, by rfl⟩ : syracuseStep 578117 = 108397) (by norm_num)
theorem B578173 : Blo 455782 578173 := bbase (se 3 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 578173 = 216815) (by norm_num)
theorem B774805 : Blo 455782 774805 := bbase (se 6 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 774805 = 36319) (by norm_num)
theorem B938693 : Blo 455782 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B578269 : Blo 455782 578269 := bbase (se 3 (by rfl) ⟨108425, by rfl⟩ : syracuseStep 578269 = 216851) (by norm_num)
theorem B774893 : Blo 455782 774893 := bbase (se 3 (by rfl) ⟨145292, by rfl⟩ : syracuseStep 774893 = 290585) (by norm_num)
theorem B512761 : Blo 455782 512761 := bbase (se 2 (by rfl) ⟨192285, by rfl⟩ : syracuseStep 512761 = 384571) (by norm_num)
theorem B512797 : Blo 455782 512797 := bbase (se 3 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 512797 = 192299) (by norm_num)
theorem B1463093 : Blo 455782 1463093 := bbase (se 5 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 1463093 = 137165) (by norm_num)
theorem B512833 : Blo 455782 512833 := bbase (se 2 (by rfl) ⟨192312, by rfl⟩ : syracuseStep 512833 = 384625) (by norm_num)
theorem B512869 : Blo 455782 512869 := bbase (se 4 (by rfl) ⟨48081, by rfl⟩ : syracuseStep 512869 = 96163) (by norm_num)
theorem B775021 : Blo 455782 775021 := bbase (se 3 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 775021 = 290633) (by norm_num)
theorem B2315141 : Blo 455782 2315141 := bbase (se 4 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 2315141 = 434089) (by norm_num)
theorem B512905 : Blo 455782 512905 := bbase (se 2 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 512905 = 384679) (by norm_num)
theorem B578441 : Blo 455782 578441 := bbase (se 2 (by rfl) ⟨216915, by rfl⟩ : syracuseStep 578441 = 433831) (by norm_num)
theorem B512941 : Blo 455782 512941 := bbase (se 3 (by rfl) ⟨96176, by rfl⟩ : syracuseStep 512941 = 192353) (by norm_num)
theorem B578497 : Blo 455782 578497 := bbase (se 2 (by rfl) ⟨216936, by rfl⟩ : syracuseStep 578497 = 433873) (by norm_num)
theorem B1299397 : Blo 455782 1299397 := bbase (se 4 (by rfl) ⟨121818, by rfl⟩ : syracuseStep 1299397 = 243637) (by norm_num)
theorem B775109 : Blo 455782 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B512977 : Blo 455782 512977 := bbase (se 2 (by rfl) ⟨192366, by rfl⟩ : syracuseStep 512977 = 384733) (by norm_num)
theorem B513013 : Blo 455782 513013 := bbase (se 5 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 513013 = 48095) (by norm_num)
theorem B513049 : Blo 455782 513049 := bbase (se 2 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 513049 = 384787) (by norm_num)
theorem B578593 : Blo 455782 578593 := bbase (se 2 (by rfl) ⟨216972, by rfl⟩ : syracuseStep 578593 = 433945) (by norm_num)
theorem B513085 : Blo 455782 513085 := bbase (se 3 (by rfl) ⟨96203, by rfl⟩ : syracuseStep 513085 = 192407) (by norm_num)
theorem B775237 : Blo 455782 775237 := bbase (se 4 (by rfl) ⟨72678, by rfl⟩ : syracuseStep 775237 = 145357) (by norm_num)
theorem B513121 : Blo 455782 513121 := bbase (se 2 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 513121 = 384841) (by norm_num)
theorem B1299557 : Blo 455782 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B513157 : Blo 455782 513157 := bbase (se 4 (by rfl) ⟨48108, by rfl⟩ : syracuseStep 513157 = 96217) (by norm_num)
theorem B775325 : Blo 455782 775325 := bbase (se 3 (by rfl) ⟨145373, by rfl⟩ : syracuseStep 775325 = 290747) (by norm_num)
theorem B513193 : Blo 455782 513193 := bbase (se 2 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 513193 = 384895) (by norm_num)
theorem B513229 : Blo 455782 513229 := bbase (se 3 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 513229 = 192461) (by norm_num)
theorem B578765 : Blo 455782 578765 := bbase (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) (by norm_num)
theorem B513265 : Blo 455782 513265 := bbase (se 2 (by rfl) ⟨192474, by rfl⟩ : syracuseStep 513265 = 384949) (by norm_num)
theorem B578821 : Blo 455782 578821 := bbase (se 4 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 578821 = 108529) (by norm_num)
theorem B513301 : Blo 455782 513301 := bbase (se 6 (by rfl) ⟨12030, by rfl⟩ : syracuseStep 513301 = 24061) (by norm_num)
theorem B775453 : Blo 455782 775453 := bbase (se 3 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 775453 = 290795) (by norm_num)
theorem B513337 : Blo 455782 513337 := bbase (se 2 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 513337 = 385003) (by norm_num)
theorem B1299797 : Blo 455782 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B513373 : Blo 455782 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B578917 : Blo 455782 578917 := bbase (se 4 (by rfl) ⟨54273, by rfl⟩ : syracuseStep 578917 = 108547) (by norm_num)
theorem B775541 : Blo 455782 775541 := bbase (se 5 (by rfl) ⟨36353, by rfl⟩ : syracuseStep 775541 = 72707) (by norm_num)
theorem B513409 : Blo 455782 513409 := bbase (se 2 (by rfl) ⟨192528, by rfl⟩ : syracuseStep 513409 = 385057) (by norm_num)
theorem B513445 : Blo 455782 513445 := bbase (se 4 (by rfl) ⟨48135, by rfl⟩ : syracuseStep 513445 = 96271) (by norm_num)
theorem B513481 : Blo 455782 513481 := bbase (se 2 (by rfl) ⟨192555, by rfl⟩ : syracuseStep 513481 = 385111) (by norm_num)
theorem B513517 : Blo 455782 513517 := bbase (se 3 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 513517 = 192569) (by norm_num)
theorem B775669 : Blo 455782 775669 := bbase (se 5 (by rfl) ⟨36359, by rfl⟩ : syracuseStep 775669 = 72719) (by norm_num)
theorem B513553 : Blo 455782 513553 := bbase (se 2 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 513553 = 385165) (by norm_num)
theorem B579089 : Blo 455782 579089 := bbase (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) (by norm_num)
theorem B1299989 : Blo 455782 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B513589 : Blo 455782 513589 := bbase (se 5 (by rfl) ⟨24074, by rfl⟩ : syracuseStep 513589 = 48149) (by norm_num)
theorem B579145 : Blo 455782 579145 := bbase (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) (by norm_num)
theorem B775757 : Blo 455782 775757 := bbase (se 3 (by rfl) ⟨145454, by rfl⟩ : syracuseStep 775757 = 290909) (by norm_num)
theorem B513625 : Blo 455782 513625 := bbase (se 2 (by rfl) ⟨192609, by rfl⟩ : syracuseStep 513625 = 385219) (by norm_num)
theorem B513661 : Blo 455782 513661 := bbase (se 3 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 513661 = 192623) (by norm_num)
theorem B513697 : Blo 455782 513697 := bbase (se 2 (by rfl) ⟨192636, by rfl⟩ : syracuseStep 513697 = 385273) (by norm_num)
theorem B579241 : Blo 455782 579241 := bbase (se 2 (by rfl) ⟨217215, by rfl⟩ : syracuseStep 579241 = 434431) (by norm_num)
theorem B513733 : Blo 455782 513733 := bbase (se 4 (by rfl) ⟨48162, by rfl⟩ : syracuseStep 513733 = 96325) (by norm_num)
theorem B513769 : Blo 455782 513769 := bbase (se 2 (by rfl) ⟨192663, by rfl⟩ : syracuseStep 513769 = 385327) (by norm_num)
theorem B1955573 : Blo 455782 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B513805 : Blo 455782 513805 := bbase (se 3 (by rfl) ⟨96338, by rfl⟩ : syracuseStep 513805 = 192677) (by norm_num)
theorem B513841 : Blo 455782 513841 := bbase (se 2 (by rfl) ⟨192690, by rfl⟩ : syracuseStep 513841 = 385381) (by norm_num)
theorem B513877 : Blo 455782 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B579413 : Blo 455782 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B1103701 : Blo 455782 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B513913 : Blo 455782 513913 := bbase (se 2 (by rfl) ⟨192717, by rfl⟩ : syracuseStep 513913 = 385435) (by norm_num)
theorem B579469 : Blo 455782 579469 := bbase (se 3 (by rfl) ⟨108650, by rfl⟩ : syracuseStep 579469 = 217301) (by norm_num)
theorem B513949 : Blo 455782 513949 := bbase (se 3 (by rfl) ⟨96365, by rfl⟩ : syracuseStep 513949 = 192731) (by norm_num)
theorem B513985 : Blo 455782 513985 := bbase (se 2 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 513985 = 385489) (by norm_num)
theorem B514021 : Blo 455782 514021 := bbase (se 4 (by rfl) ⟨48189, by rfl⟩ : syracuseStep 514021 = 96379) (by norm_num)
theorem B579565 : Blo 455782 579565 := bbase (se 3 (by rfl) ⟨108668, by rfl⟩ : syracuseStep 579565 = 217337) (by norm_num)
theorem B514057 : Blo 455782 514057 := bbase (se 2 (by rfl) ⟨192771, by rfl⟩ : syracuseStep 514057 = 385543) (by norm_num)
theorem B514093 : Blo 455782 514093 := bbase (se 3 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 514093 = 192785) (by norm_num)
theorem B514129 : Blo 455782 514129 := bbase (se 2 (by rfl) ⟨192798, by rfl⟩ : syracuseStep 514129 = 385597) (by norm_num)
theorem B2480213 : Blo 455782 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B514165 : Blo 455782 514165 := bbase (se 5 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 514165 = 48203) (by norm_num)
theorem B2316437 : Blo 455782 2316437 := bbase (se 6 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 2316437 = 108583) (by norm_num)
theorem B514201 : Blo 455782 514201 := bbase (se 2 (by rfl) ⟨192825, by rfl⟩ : syracuseStep 514201 = 385651) (by norm_num)
theorem B579737 : Blo 455782 579737 := bbase (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) (by norm_num)
theorem B514237 : Blo 455782 514237 := bbase (se 3 (by rfl) ⟨96419, by rfl⟩ : syracuseStep 514237 = 192839) (by norm_num)
theorem B579793 : Blo 455782 579793 := bbase (se 2 (by rfl) ⟨217422, by rfl⟩ : syracuseStep 579793 = 434845) (by norm_num)
theorem B514273 : Blo 455782 514273 := bbase (se 2 (by rfl) ⟨192852, by rfl⟩ : syracuseStep 514273 = 385705) (by norm_num)
theorem B514309 : Blo 455782 514309 := bbase (se 4 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 514309 = 96433) (by norm_num)
theorem B514345 : Blo 455782 514345 := bbase (se 2 (by rfl) ⟨192879, by rfl⟩ : syracuseStep 514345 = 385759) (by norm_num)
theorem B579889 : Blo 455782 579889 := bbase (se 2 (by rfl) ⟨217458, by rfl⟩ : syracuseStep 579889 = 434917) (by norm_num)
theorem B514381 : Blo 455782 514381 := bbase (se 3 (by rfl) ⟨96446, by rfl⟩ : syracuseStep 514381 = 192893) (by norm_num)
theorem B514417 : Blo 455782 514417 := bbase (se 2 (by rfl) ⟨192906, by rfl⟩ : syracuseStep 514417 = 385813) (by norm_num)
theorem B514453 : Blo 455782 514453 := bbase (se 6 (by rfl) ⟨12057, by rfl⟩ : syracuseStep 514453 = 24115) (by norm_num)
theorem B514489 : Blo 455782 514489 := bbase (se 2 (by rfl) ⟨192933, by rfl⟩ : syracuseStep 514489 = 385867) (by norm_num)
theorem B1104317 : Blo 455782 1104317 := bbase (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) (by norm_num)
theorem B514525 : Blo 455782 514525 := bbase (se 3 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 514525 = 192947) (by norm_num)
theorem B580061 : Blo 455782 580061 := bbase (se 3 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 580061 = 217523) (by norm_num)
theorem B1300981 : Blo 455782 1300981 := bbase (se 5 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 1300981 = 121967) (by norm_num)
theorem B514561 : Blo 455782 514561 := bbase (se 2 (by rfl) ⟨192960, by rfl⟩ : syracuseStep 514561 = 385921) (by norm_num)
theorem B580117 : Blo 455782 580117 := bbase (se 6 (by rfl) ⟨13596, by rfl⟩ : syracuseStep 580117 = 27193) (by norm_num)
theorem B514597 : Blo 455782 514597 := bbase (se 4 (by rfl) ⟨48243, by rfl⟩ : syracuseStep 514597 = 96487) (by norm_num)
theorem B1858085 : Blo 455782 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B514633 : Blo 455782 514633 := bbase (se 2 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 514633 = 385975) (by norm_num)
theorem B514669 : Blo 455782 514669 := bbase (se 3 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 514669 = 193001) (by norm_num)
theorem B580213 : Blo 455782 580213 := bbase (se 5 (by rfl) ⟨27197, by rfl⟩ : syracuseStep 580213 = 54395) (by norm_num)
theorem B514705 : Blo 455782 514705 := bbase (se 2 (by rfl) ⟨193014, by rfl⟩ : syracuseStep 514705 = 386029) (by norm_num)
theorem B514741 : Blo 455782 514741 := bbase (se 5 (by rfl) ⟨24128, by rfl⟩ : syracuseStep 514741 = 48257) (by norm_num)
theorem B514777 : Blo 455782 514777 := bbase (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) (by norm_num)
theorem B1956581 : Blo 455782 1956581 := bbase (se 4 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 1956581 = 366859) (by norm_num)
theorem B973549 : Blo 455782 973549 := bbase (se 3 (by rfl) ⟨182540, by rfl⟩ : syracuseStep 973549 = 365081) (by norm_num)
theorem B514813 : Blo 455782 514813 := bbase (se 3 (by rfl) ⟨96527, by rfl⟩ : syracuseStep 514813 = 193055) (by norm_num)
theorem B514849 : Blo 455782 514849 := bbase (se 2 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 514849 = 386137) (by norm_num)
theorem B580385 : Blo 455782 580385 := bbase (se 2 (by rfl) ⟨217644, by rfl⟩ : syracuseStep 580385 = 435289) (by norm_num)
theorem B1170245 : Blo 455782 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B514885 : Blo 455782 514885 := bbase (se 4 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 514885 = 96541) (by norm_num)
theorem B580441 : Blo 455782 580441 := bbase (se 2 (by rfl) ⟨217665, by rfl⟩ : syracuseStep 580441 = 435331) (by norm_num)
theorem B514921 : Blo 455782 514921 := bbase (se 2 (by rfl) ⟨193095, by rfl⟩ : syracuseStep 514921 = 386191) (by norm_num)
theorem B514957 : Blo 455782 514957 := bbase (se 3 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 514957 = 193109) (by norm_num)
theorem B547741 : Blo 455782 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B514993 : Blo 455782 514993 := bbase (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) (by norm_num)
theorem B580537 : Blo 455782 580537 := bbase (se 2 (by rfl) ⟨217701, by rfl⟩ : syracuseStep 580537 = 435403) (by norm_num)
theorem B515029 : Blo 455782 515029 := bbase (se 7 (by rfl) ⟨6035, by rfl⟩ : syracuseStep 515029 = 12071) (by norm_num)
theorem B515065 : Blo 455782 515065 := bbase (se 2 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 515065 = 386299) (by norm_num)
theorem B515101 : Blo 455782 515101 := bbase (se 3 (by rfl) ⟨96581, by rfl⟩ : syracuseStep 515101 = 193163) (by norm_num)
theorem B515137 : Blo 455782 515137 := bbase (se 2 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 515137 = 386353) (by norm_num)
theorem B515173 : Blo 455782 515173 := bbase (se 4 (by rfl) ⟨48297, by rfl⟩ : syracuseStep 515173 = 96595) (by norm_num)
theorem B580709 : Blo 455782 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B515209 : Blo 455782 515209 := bbase (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) (by norm_num)
theorem B580765 : Blo 455782 580765 := bbase (se 3 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 580765 = 217787) (by norm_num)
theorem B515245 : Blo 455782 515245 := bbase (se 3 (by rfl) ⟨96608, by rfl⟩ : syracuseStep 515245 = 193217) (by norm_num)
theorem B515281 : Blo 455782 515281 := bbase (se 2 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 515281 = 386461) (by norm_num)
theorem B515317 : Blo 455782 515317 := bbase (se 5 (by rfl) ⟨24155, by rfl⟩ : syracuseStep 515317 = 48311) (by norm_num)
theorem B580861 : Blo 455782 580861 := bbase (se 3 (by rfl) ⟨108911, by rfl⟩ : syracuseStep 580861 = 217823) (by norm_num)
theorem B515353 : Blo 455782 515353 := bbase (se 2 (by rfl) ⟨193257, by rfl⟩ : syracuseStep 515353 = 386515) (by norm_num)
theorem B515389 : Blo 455782 515389 := bbase (se 3 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 515389 = 193271) (by norm_num)
theorem B1039709 : Blo 455782 1039709 := bbase (se 3 (by rfl) ⟨194945, by rfl⟩ : syracuseStep 1039709 = 389891) (by norm_num)
theorem B515425 : Blo 455782 515425 := bbase (se 2 (by rfl) ⟨193284, by rfl⟩ : syracuseStep 515425 = 386569) (by norm_num)
theorem B515461 : Blo 455782 515461 := bbase (se 4 (by rfl) ⟨48324, by rfl⟩ : syracuseStep 515461 = 96649) (by norm_num)
theorem B2317733 : Blo 455782 2317733 := bbase (se 4 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 2317733 = 434575) (by norm_num)
theorem B515497 : Blo 455782 515497 := bbase (se 2 (by rfl) ⟨193311, by rfl⟩ : syracuseStep 515497 = 386623) (by norm_num)
theorem B581033 : Blo 455782 581033 := bbase (se 2 (by rfl) ⟨217887, by rfl⟩ : syracuseStep 581033 = 435775) (by norm_num)
theorem B515533 : Blo 455782 515533 := bbase (se 3 (by rfl) ⟨96662, by rfl⟩ : syracuseStep 515533 = 193325) (by norm_num)
theorem B581089 : Blo 455782 581089 := bbase (se 2 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 581089 = 435817) (by norm_num)
theorem B515569 : Blo 455782 515569 := bbase (se 2 (by rfl) ⟨193338, by rfl⟩ : syracuseStep 515569 = 386677) (by norm_num)
theorem B3464693 : Blo 455782 3464693 := bbase (se 5 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 3464693 = 324815) (by norm_num)
theorem B515605 : Blo 455782 515605 := bbase (se 6 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 515605 = 24169) (by norm_num)
theorem B515641 : Blo 455782 515641 := bbase (se 2 (by rfl) ⟨193365, by rfl⟩ : syracuseStep 515641 = 386731) (by norm_num)
theorem B581185 : Blo 455782 581185 := bbase (se 2 (by rfl) ⟨217944, by rfl⟩ : syracuseStep 581185 = 435889) (by norm_num)
theorem B1302085 : Blo 455782 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B515677 : Blo 455782 515677 := bbase (se 3 (by rfl) ⟨96689, by rfl⟩ : syracuseStep 515677 = 193379) (by norm_num)
theorem B515713 : Blo 455782 515713 := bbase (se 2 (by rfl) ⟨193392, by rfl⟩ : syracuseStep 515713 = 386785) (by norm_num)
theorem B515749 : Blo 455782 515749 := bbase (se 4 (by rfl) ⟨48351, by rfl⟩ : syracuseStep 515749 = 96703) (by norm_num)
theorem B515785 : Blo 455782 515785 := bbase (se 2 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 515785 = 386839) (by norm_num)
theorem B515821 : Blo 455782 515821 := bbase (se 3 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 515821 = 193433) (by norm_num)
theorem B581357 : Blo 455782 581357 := bbase (se 3 (by rfl) ⟨109004, by rfl⟩ : syracuseStep 581357 = 218009) (by norm_num)
theorem B515857 : Blo 455782 515857 := bbase (se 2 (by rfl) ⟨193446, by rfl⟩ : syracuseStep 515857 = 386893) (by norm_num)
theorem B581413 : Blo 455782 581413 := bbase (se 4 (by rfl) ⟨54507, by rfl⟩ : syracuseStep 581413 = 109015) (by norm_num)
theorem B515893 : Blo 455782 515893 := bbase (se 5 (by rfl) ⟨24182, by rfl⟩ : syracuseStep 515893 = 48365) (by norm_num)
theorem B515929 : Blo 455782 515929 := bbase (se 2 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 515929 = 386947) (by norm_num)
theorem B515965 : Blo 455782 515965 := bbase (se 3 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 515965 = 193487) (by norm_num)
theorem B548741 : Blo 455782 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B581509 : Blo 455782 581509 := bbase (se 4 (by rfl) ⟨54516, by rfl⟩ : syracuseStep 581509 = 109033) (by norm_num)
theorem B516001 : Blo 455782 516001 := bbase (se 2 (by rfl) ⟨193500, by rfl⟩ : syracuseStep 516001 = 387001) (by norm_num)
theorem B548789 : Blo 455782 548789 := bbase (se 5 (by rfl) ⟨25724, by rfl⟩ : syracuseStep 548789 = 51449) (by norm_num)
theorem B516037 : Blo 455782 516037 := bbase (se 4 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 516037 = 96757) (by norm_num)
theorem B516073 : Blo 455782 516073 := bbase (se 2 (by rfl) ⟨193527, by rfl⟩ : syracuseStep 516073 = 387055) (by norm_num)
theorem B516109 : Blo 455782 516109 := bbase (se 3 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 516109 = 193541) (by norm_num)
theorem B516145 : Blo 455782 516145 := bbase (se 2 (by rfl) ⟨193554, by rfl⟩ : syracuseStep 516145 = 387109) (by norm_num)
theorem B581681 : Blo 455782 581681 := bbase (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) (by norm_num)
theorem B516181 : Blo 455782 516181 := bbase (se 8 (by rfl) ⟨3024, by rfl⟩ : syracuseStep 516181 = 6049) (by norm_num)
theorem B581737 : Blo 455782 581737 := bbase (se 2 (by rfl) ⟨218151, by rfl⟩ : syracuseStep 581737 = 436303) (by norm_num)
theorem B516217 : Blo 455782 516217 := bbase (se 2 (by rfl) ⟨193581, by rfl⟩ : syracuseStep 516217 = 387163) (by norm_num)
theorem B516253 : Blo 455782 516253 := bbase (se 3 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 516253 = 193595) (by norm_num)
theorem B516289 : Blo 455782 516289 := bbase (se 2 (by rfl) ⟨193608, by rfl⟩ : syracuseStep 516289 = 387217) (by norm_num)
theorem B581833 : Blo 455782 581833 := bbase (se 2 (by rfl) ⟨218187, by rfl⟩ : syracuseStep 581833 = 436375) (by norm_num)
theorem B975053 : Blo 455782 975053 := bbase (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) (by norm_num)
theorem B516325 : Blo 455782 516325 := bbase (se 4 (by rfl) ⟨48405, by rfl⟩ : syracuseStep 516325 = 96811) (by norm_num)
theorem B516361 : Blo 455782 516361 := bbase (se 2 (by rfl) ⟨193635, by rfl⟩ : syracuseStep 516361 = 387271) (by norm_num)
theorem B516397 : Blo 455782 516397 := bbase (se 3 (by rfl) ⟨96824, by rfl⟩ : syracuseStep 516397 = 193649) (by norm_num)
theorem B516433 : Blo 455782 516433 := bbase (se 2 (by rfl) ⟨193662, by rfl⟩ : syracuseStep 516433 = 387325) (by norm_num)
theorem B975197 : Blo 455782 975197 := bbase (se 3 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 975197 = 365699) (by norm_num)
theorem B1237349 : Blo 455782 1237349 := bbase (se 4 (by rfl) ⟨116001, by rfl⟩ : syracuseStep 1237349 = 232003) (by norm_num)
theorem B516469 : Blo 455782 516469 := bbase (se 5 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 516469 = 48419) (by norm_num)
theorem B516505 : Blo 455782 516505 := bbase (se 2 (by rfl) ⟨193689, by rfl⟩ : syracuseStep 516505 = 387379) (by norm_num)
theorem B516541 : Blo 455782 516541 := bbase (se 3 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 516541 = 193703) (by norm_num)
theorem B1958357 : Blo 455782 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B549337 : Blo 455782 549337 := bbase (se 2 (by rfl) ⟨206001, by rfl⟩ : syracuseStep 549337 = 412003) (by norm_num)
theorem B516577 : Blo 455782 516577 := bbase (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) (by norm_num)
theorem B1466885 : Blo 455782 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B516613 : Blo 455782 516613 := bbase (se 4 (by rfl) ⟨48432, by rfl⟩ : syracuseStep 516613 = 96865) (by norm_num)
theorem B516649 : Blo 455782 516649 := bbase (se 2 (by rfl) ⟨193743, by rfl⟩ : syracuseStep 516649 = 387487) (by norm_num)
theorem B2482741 : Blo 455782 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B516685 : Blo 455782 516685 := bbase (se 3 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 516685 = 193757) (by norm_num)
theorem B516721 : Blo 455782 516721 := bbase (se 2 (by rfl) ⟨193770, by rfl⟩ : syracuseStep 516721 = 387541) (by norm_num)
theorem B516757 : Blo 455782 516757 := bbase (se 6 (by rfl) ⟨12111, by rfl⟩ : syracuseStep 516757 = 24223) (by norm_num)
theorem B2319029 : Blo 455782 2319029 := bbase (se 5 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 2319029 = 217409) (by norm_num)
theorem B516793 : Blo 455782 516793 := bbase (se 2 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 516793 = 387595) (by norm_num)
theorem B975557 : Blo 455782 975557 := bbase (se 4 (by rfl) ⟨91458, by rfl⟩ : syracuseStep 975557 = 182917) (by norm_num)
theorem B1237717 : Blo 455782 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B516829 : Blo 455782 516829 := bbase (se 3 (by rfl) ⟨96905, by rfl⟩ : syracuseStep 516829 = 193811) (by norm_num)
theorem B516865 : Blo 455782 516865 := bbase (se 2 (by rfl) ⟨193824, by rfl⟩ : syracuseStep 516865 = 387649) (by norm_num)
theorem B1237781 : Blo 455782 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B516901 : Blo 455782 516901 := bbase (se 4 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 516901 = 96919) (by norm_num)
theorem B516937 : Blo 455782 516937 := bbase (se 2 (by rfl) ⟨193851, by rfl⟩ : syracuseStep 516937 = 387703) (by norm_num)
theorem B516973 : Blo 455782 516973 := bbase (se 3 (by rfl) ⟨96932, by rfl⟩ : syracuseStep 516973 = 193865) (by norm_num)
theorem B4416373 : Blo 455782 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B517009 : Blo 455782 517009 := bbase (se 2 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 517009 = 387757) (by norm_num)
theorem B517045 : Blo 455782 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B549817 : Blo 455782 549817 := bbase (se 2 (by rfl) ⟨206181, by rfl⟩ : syracuseStep 549817 = 412363) (by norm_num)
theorem B517081 : Blo 455782 517081 := bbase (se 2 (by rfl) ⟨193905, by rfl⟩ : syracuseStep 517081 = 387811) (by norm_num)
theorem B517117 : Blo 455782 517117 := bbase (se 3 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 517117 = 193919) (by norm_num)
theorem B517153 : Blo 455782 517153 := bbase (se 2 (by rfl) ⟨193932, by rfl⟩ : syracuseStep 517153 = 387865) (by norm_num)
theorem B1303589 : Blo 455782 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B1041461 : Blo 455782 1041461 := bbase (se 5 (by rfl) ⟨48818, by rfl⟩ : syracuseStep 1041461 = 97637) (by norm_num)
theorem B517189 : Blo 455782 517189 := bbase (se 4 (by rfl) ⟨48486, by rfl⟩ : syracuseStep 517189 = 96973) (by norm_num)
theorem B517225 : Blo 455782 517225 := bbase (se 2 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 517225 = 387919) (by norm_num)
theorem B8316053 : Blo 455782 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B779645 : Blo 455782 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B976445 : Blo 455782 976445 := bbase (se 3 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 976445 = 366167) (by norm_num)
theorem B1467973 : Blo 455782 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B550697 : Blo 455782 550697 := bbase (se 2 (by rfl) ⟨206511, by rfl⟩ : syracuseStep 550697 = 413023) (by norm_num)
theorem B976693 : Blo 455782 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B550813 : Blo 455782 550813 := bbase (se 3 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 550813 = 206555) (by norm_num)
theorem B2320325 : Blo 455782 2320325 := bbase (se 4 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 2320325 = 435061) (by norm_num)
theorem B8775701 : Blo 455782 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B4384853 : Blo 455782 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B551009 : Blo 455782 551009 := bbase (se 2 (by rfl) ⟨206628, by rfl⟩ : syracuseStep 551009 = 413257) (by norm_num)
theorem B649397 : Blo 455782 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B1861861 : Blo 455782 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B977197 : Blo 455782 977197 := bbase (se 3 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 977197 = 366449) (by norm_num)
theorem B616837 : Blo 455782 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1173941 : Blo 455782 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B1305173 : Blo 455782 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B617053 : Blo 455782 617053 := bbase (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) (by norm_num)
theorem B1567333 : Blo 455782 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B551557 : Blo 455782 551557 := bbase (se 4 (by rfl) ⟨51708, by rfl⟩ : syracuseStep 551557 = 103417) (by norm_num)
theorem B1731253 : Blo 455782 1731253 := bbase (se 5 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 1731253 = 162305) (by norm_num)
theorem B1469141 : Blo 455782 1469141 := bbase (se 7 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 1469141 = 34433) (by norm_num)
theorem B649949 : Blo 455782 649949 := bbase (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) (by norm_num)
theorem B879341 : Blo 455782 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B879349 : Blo 455782 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B551701 : Blo 455782 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B2616245 : Blo 455782 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B1731557 : Blo 455782 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B1567829 : Blo 455782 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B978085 : Blo 455782 978085 := bbase (se 4 (by rfl) ⟨91695, by rfl⟩ : syracuseStep 978085 = 183391) (by norm_num)
theorem B2321621 : Blo 455782 2321621 := bbase (se 7 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 2321621 = 54413) (by norm_num)
theorem B1305845 : Blo 455782 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B781589 : Blo 455782 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B650701 : Blo 455782 650701 := bbase (se 3 (by rfl) ⟨122006, by rfl⟩ : syracuseStep 650701 = 244013) (by norm_num)
theorem B585185 : Blo 455782 585185 := bbase (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) (by norm_num)
theorem B880141 : Blo 455782 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B978581 : Blo 455782 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B1306277 : Blo 455782 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B683693 : Blo 455782 683693 := bbase (se 3 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 683693 = 256385) (by norm_num)
theorem B1044149 : Blo 455782 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B683717 : Blo 455782 683717 := bbase (se 4 (by rfl) ⟨64098, by rfl⟩ : syracuseStep 683717 = 128197) (by norm_num)
theorem B487129 : Blo 455782 487129 := bbase (se 2 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 487129 = 365347) (by norm_num)
theorem B683741 : Blo 455782 683741 := bbase (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) (by norm_num)
theorem B1044197 : Blo 455782 1044197 := bbase (se 4 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 1044197 = 195787) (by norm_num)
theorem B683765 : Blo 455782 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B683789 : Blo 455782 683789 := bbase (se 3 (by rfl) ⟨128210, by rfl⟩ : syracuseStep 683789 = 256421) (by norm_num)
theorem B683813 : Blo 455782 683813 := bbase (se 4 (by rfl) ⟨64107, by rfl⟩ : syracuseStep 683813 = 128215) (by norm_num)
theorem B683837 : Blo 455782 683837 := bbase (se 3 (by rfl) ⟨128219, by rfl⟩ : syracuseStep 683837 = 256439) (by norm_num)
theorem B683861 : Blo 455782 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B487253 : Blo 455782 487253 := bbase (se 9 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 487253 = 2855) (by norm_num)
theorem B683885 : Blo 455782 683885 := bbase (se 3 (by rfl) ⟨128228, by rfl⟩ : syracuseStep 683885 = 256457) (by norm_num)
theorem B683909 : Blo 455782 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B683933 : Blo 455782 683933 := bbase (se 3 (by rfl) ⟨128237, by rfl⟩ : syracuseStep 683933 = 256475) (by norm_num)
theorem B683957 : Blo 455782 683957 := bbase (se 5 (by rfl) ⟨32060, by rfl⟩ : syracuseStep 683957 = 64121) (by norm_num)
theorem B683981 : Blo 455782 683981 := bbase (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) (by norm_num)
theorem B684005 : Blo 455782 684005 := bbase (se 4 (by rfl) ⟨64125, by rfl⟩ : syracuseStep 684005 = 128251) (by norm_num)
theorem B684029 : Blo 455782 684029 := bbase (se 3 (by rfl) ⟨128255, by rfl⟩ : syracuseStep 684029 = 256511) (by norm_num)
theorem B684053 : Blo 455782 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B1044517 : Blo 455782 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B684077 : Blo 455782 684077 := bbase (se 3 (by rfl) ⟨128264, by rfl⟩ : syracuseStep 684077 = 256529) (by norm_num)
theorem B684101 : Blo 455782 684101 := bbase (se 4 (by rfl) ⟨64134, by rfl⟩ : syracuseStep 684101 = 128269) (by norm_num)
theorem B487505 : Blo 455782 487505 := bbase (se 2 (by rfl) ⟨182814, by rfl⟩ : syracuseStep 487505 = 365629) (by norm_num)
theorem B684125 : Blo 455782 684125 := bbase (se 3 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 684125 = 256547) (by norm_num)
theorem B1044589 : Blo 455782 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B684149 : Blo 455782 684149 := bbase (se 5 (by rfl) ⟨32069, by rfl⟩ : syracuseStep 684149 = 64139) (by norm_num)
theorem B684173 : Blo 455782 684173 := bbase (se 3 (by rfl) ⟨128282, by rfl⟩ : syracuseStep 684173 = 256565) (by norm_num)
theorem B684197 : Blo 455782 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B684221 : Blo 455782 684221 := bbase (se 3 (by rfl) ⟨128291, by rfl⟩ : syracuseStep 684221 = 256583) (by norm_num)
theorem B684245 : Blo 455782 684245 := bbase (se 7 (by rfl) ⟨8018, by rfl⟩ : syracuseStep 684245 = 16037) (by norm_num)
theorem B651493 : Blo 455782 651493 := bbase (se 4 (by rfl) ⟨61077, by rfl⟩ : syracuseStep 651493 = 122155) (by norm_num)
theorem B684269 : Blo 455782 684269 := bbase (se 3 (by rfl) ⟨128300, by rfl⟩ : syracuseStep 684269 = 256601) (by norm_num)
theorem B684293 : Blo 455782 684293 := bbase (se 4 (by rfl) ⟨64152, by rfl⟩ : syracuseStep 684293 = 128305) (by norm_num)
theorem B684317 : Blo 455782 684317 := bbase (se 3 (by rfl) ⟨128309, by rfl⟩ : syracuseStep 684317 = 256619) (by norm_num)
theorem B684341 : Blo 455782 684341 := bbase (se 5 (by rfl) ⟨32078, by rfl⟩ : syracuseStep 684341 = 64157) (by norm_num)
theorem B4714805 : Blo 455782 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B1241413 : Blo 455782 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B684365 : Blo 455782 684365 := bbase (se 3 (by rfl) ⟨128318, by rfl⟩ : syracuseStep 684365 = 256637) (by norm_num)
theorem B684389 : Blo 455782 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B1667429 : Blo 455782 1667429 := bbase (se 4 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 1667429 = 312643) (by norm_num)
theorem B684413 : Blo 455782 684413 := bbase (se 3 (by rfl) ⟨128327, by rfl⟩ : syracuseStep 684413 = 256655) (by norm_num)
theorem B684437 : Blo 455782 684437 := bbase (se 6 (by rfl) ⟨16041, by rfl⟩ : syracuseStep 684437 = 32083) (by norm_num)
theorem B1307029 : Blo 455782 1307029 := bbase (se 6 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 1307029 = 61267) (by norm_num)
theorem B684461 : Blo 455782 684461 := bbase (se 3 (by rfl) ⟨128336, by rfl⟩ : syracuseStep 684461 = 256673) (by norm_num)
theorem B684485 : Blo 455782 684485 := bbase (se 4 (by rfl) ⟨64170, by rfl⟩ : syracuseStep 684485 = 128341) (by norm_num)
theorem B684509 : Blo 455782 684509 := bbase (se 3 (by rfl) ⟨128345, by rfl⟩ : syracuseStep 684509 = 256691) (by norm_num)
theorem B2322917 : Blo 455782 2322917 := bbase (se 4 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 2322917 = 435547) (by norm_num)
theorem B684533 : Blo 455782 684533 := bbase (se 5 (by rfl) ⟨32087, by rfl⟩ : syracuseStep 684533 = 64175) (by norm_num)
theorem B684557 : Blo 455782 684557 := bbase (se 3 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 684557 = 256709) (by norm_num)
theorem B487949 : Blo 455782 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B979469 : Blo 455782 979469 := bbase (se 3 (by rfl) ⟨183650, by rfl⟩ : syracuseStep 979469 = 367301) (by norm_num)
theorem B1470997 : Blo 455782 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B684581 : Blo 455782 684581 := bbase (se 4 (by rfl) ⟨64179, by rfl⟩ : syracuseStep 684581 = 128359) (by norm_num)
theorem B1045037 : Blo 455782 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B651829 : Blo 455782 651829 := bbase (se 5 (by rfl) ⟨30554, by rfl⟩ : syracuseStep 651829 = 61109) (by norm_num)
theorem B684605 : Blo 455782 684605 := bbase (se 3 (by rfl) ⟨128363, by rfl⟩ : syracuseStep 684605 = 256727) (by norm_num)
theorem B684629 : Blo 455782 684629 := bbase (se 8 (by rfl) ⟨4011, by rfl⟩ : syracuseStep 684629 = 8023) (by norm_num)
theorem B684653 : Blo 455782 684653 := bbase (se 3 (by rfl) ⟨128372, by rfl⟩ : syracuseStep 684653 = 256745) (by norm_num)
theorem B684677 : Blo 455782 684677 := bbase (se 4 (by rfl) ⟨64188, by rfl⟩ : syracuseStep 684677 = 128377) (by norm_num)
theorem B979589 : Blo 455782 979589 := bbase (se 4 (by rfl) ⟨91836, by rfl⟩ : syracuseStep 979589 = 183673) (by norm_num)
theorem B1962629 : Blo 455782 1962629 := bbase (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) (by norm_num)
theorem B684701 : Blo 455782 684701 := bbase (se 3 (by rfl) ⟨128381, by rfl⟩ : syracuseStep 684701 = 256763) (by norm_num)
theorem B684725 : Blo 455782 684725 := bbase (se 5 (by rfl) ⟨32096, by rfl⟩ : syracuseStep 684725 = 64193) (by norm_num)
theorem B1045181 : Blo 455782 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B684749 : Blo 455782 684749 := bbase (se 3 (by rfl) ⟨128390, by rfl⟩ : syracuseStep 684749 = 256781) (by norm_num)
theorem B7533269 : Blo 455782 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B684773 : Blo 455782 684773 := bbase (se 4 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 684773 = 128395) (by norm_num)
theorem B684797 : Blo 455782 684797 := bbase (se 3 (by rfl) ⟨128399, by rfl⟩ : syracuseStep 684797 = 256799) (by norm_num)
theorem B488197 : Blo 455782 488197 := bbase (se 4 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 488197 = 91537) (by norm_num)
theorem B652045 : Blo 455782 652045 := bbase (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) (by norm_num)
theorem B684821 : Blo 455782 684821 := bbase (se 6 (by rfl) ⟨16050, by rfl⟩ : syracuseStep 684821 = 32101) (by norm_num)
theorem B684845 : Blo 455782 684845 := bbase (se 3 (by rfl) ⟨128408, by rfl⟩ : syracuseStep 684845 = 256817) (by norm_num)
theorem B684869 : Blo 455782 684869 := bbase (se 4 (by rfl) ⟨64206, by rfl⟩ : syracuseStep 684869 = 128413) (by norm_num)
theorem B4944725 : Blo 455782 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B684893 : Blo 455782 684893 := bbase (se 3 (by rfl) ⟨128417, by rfl⟩ : syracuseStep 684893 = 256835) (by norm_num)
theorem B684917 : Blo 455782 684917 := bbase (se 5 (by rfl) ⟨32105, by rfl⟩ : syracuseStep 684917 = 64211) (by norm_num)
theorem B684941 : Blo 455782 684941 := bbase (se 3 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 684941 = 256853) (by norm_num)
theorem B684965 : Blo 455782 684965 := bbase (se 4 (by rfl) ⟨64215, by rfl⟩ : syracuseStep 684965 = 128431) (by norm_num)
theorem B684989 : Blo 455782 684989 := bbase (se 3 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 684989 = 256871) (by norm_num)
theorem B685013 : Blo 455782 685013 := bbase (se 7 (by rfl) ⟨8027, by rfl⟩ : syracuseStep 685013 = 16055) (by norm_num)
theorem B685037 : Blo 455782 685037 := bbase (se 3 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 685037 = 256889) (by norm_num)
theorem B685061 : Blo 455782 685061 := bbase (se 4 (by rfl) ⟨64224, by rfl⟩ : syracuseStep 685061 = 128449) (by norm_num)
theorem B1569797 : Blo 455782 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B685085 : Blo 455782 685085 := bbase (se 3 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 685085 = 256907) (by norm_num)
theorem B1733669 : Blo 455782 1733669 := bbase (se 4 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 1733669 = 325063) (by norm_num)
theorem B685109 : Blo 455782 685109 := bbase (se 5 (by rfl) ⟨32114, by rfl⟩ : syracuseStep 685109 = 64229) (by norm_num)
theorem B521273 : Blo 455782 521273 := bbase (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) (by norm_num)
theorem B685133 : Blo 455782 685133 := bbase (se 3 (by rfl) ⟨128462, by rfl⟩ : syracuseStep 685133 = 256925) (by norm_num)
theorem B685157 : Blo 455782 685157 := bbase (se 4 (by rfl) ⟨64233, by rfl⟩ : syracuseStep 685157 = 128467) (by norm_num)
theorem B685181 : Blo 455782 685181 := bbase (se 3 (by rfl) ⟨128471, by rfl⟩ : syracuseStep 685181 = 256943) (by norm_num)
theorem B652421 : Blo 455782 652421 := bbase (se 4 (by rfl) ⟨61164, by rfl⟩ : syracuseStep 652421 = 122329) (by norm_num)
theorem B685205 : Blo 455782 685205 := bbase (se 6 (by rfl) ⟨16059, by rfl⟩ : syracuseStep 685205 = 32119) (by norm_num)
theorem B685229 : Blo 455782 685229 := bbase (se 3 (by rfl) ⟨128480, by rfl⟩ : syracuseStep 685229 = 256961) (by norm_num)
theorem B488641 : Blo 455782 488641 := bbase (se 2 (by rfl) ⟨183240, by rfl⟩ : syracuseStep 488641 = 366481) (by norm_num)
theorem B685253 : Blo 455782 685253 := bbase (se 4 (by rfl) ⟨64242, by rfl⟩ : syracuseStep 685253 = 128485) (by norm_num)
theorem B1569989 : Blo 455782 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B685277 : Blo 455782 685277 := bbase (se 3 (by rfl) ⟨128489, by rfl⟩ : syracuseStep 685277 = 256979) (by norm_num)
theorem B685301 : Blo 455782 685301 := bbase (se 5 (by rfl) ⟨32123, by rfl⟩ : syracuseStep 685301 = 64247) (by norm_num)
theorem B488701 : Blo 455782 488701 := bbase (se 3 (by rfl) ⟨91631, by rfl⟩ : syracuseStep 488701 = 183263) (by norm_num)
theorem B980221 : Blo 455782 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B685325 : Blo 455782 685325 := bbase (se 3 (by rfl) ⟨128498, by rfl⟩ : syracuseStep 685325 = 256997) (by norm_num)
theorem B685349 : Blo 455782 685349 := bbase (se 4 (by rfl) ⟨64251, by rfl⟩ : syracuseStep 685349 = 128503) (by norm_num)
theorem B685373 : Blo 455782 685373 := bbase (se 3 (by rfl) ⟨128507, by rfl⟩ : syracuseStep 685373 = 257015) (by norm_num)
theorem B1733957 : Blo 455782 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B685397 : Blo 455782 685397 := bbase (se 13 (by rfl) ⟨125, by rfl⟩ : syracuseStep 685397 = 251) (by norm_num)
theorem B685421 : Blo 455782 685421 := bbase (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) (by norm_num)
theorem B685445 : Blo 455782 685445 := bbase (se 4 (by rfl) ⟨64260, by rfl⟩ : syracuseStep 685445 = 128521) (by norm_num)
theorem B1111445 : Blo 455782 1111445 := bbase (se 6 (by rfl) ⟨26049, by rfl⟩ : syracuseStep 1111445 = 52099) (by norm_num)
theorem B685469 : Blo 455782 685469 := bbase (se 3 (by rfl) ⟨128525, by rfl⟩ : syracuseStep 685469 = 257051) (by norm_num)
theorem B685493 : Blo 455782 685493 := bbase (se 5 (by rfl) ⟨32132, by rfl⟩ : syracuseStep 685493 = 64265) (by norm_num)
theorem B685517 : Blo 455782 685517 := bbase (se 3 (by rfl) ⟨128534, by rfl⟩ : syracuseStep 685517 = 257069) (by norm_num)
theorem B685541 : Blo 455782 685541 := bbase (se 4 (by rfl) ⟨64269, by rfl⟩ : syracuseStep 685541 = 128539) (by norm_num)
theorem B685565 : Blo 455782 685565 := bbase (se 3 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 685565 = 257087) (by norm_num)
theorem B685589 : Blo 455782 685589 := bbase (se 6 (by rfl) ⟨16068, by rfl⟩ : syracuseStep 685589 = 32137) (by norm_num)
theorem B685613 : Blo 455782 685613 := bbase (se 3 (by rfl) ⟨128552, by rfl⟩ : syracuseStep 685613 = 257105) (by norm_num)
theorem B489017 : Blo 455782 489017 := bbase (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) (by norm_num)
theorem B685637 : Blo 455782 685637 := bbase (se 4 (by rfl) ⟨64278, by rfl⟩ : syracuseStep 685637 = 128557) (by norm_num)
theorem B685661 : Blo 455782 685661 := bbase (se 3 (by rfl) ⟨128561, by rfl⟩ : syracuseStep 685661 = 257123) (by norm_num)
theorem B685685 : Blo 455782 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B685709 : Blo 455782 685709 := bbase (se 3 (by rfl) ⟨128570, by rfl⟩ : syracuseStep 685709 = 257141) (by norm_num)
theorem B685733 : Blo 455782 685733 := bbase (se 4 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 685733 = 128575) (by norm_num)
theorem B685757 : Blo 455782 685757 := bbase (se 3 (by rfl) ⟨128579, by rfl⟩ : syracuseStep 685757 = 257159) (by norm_num)
theorem B685781 : Blo 455782 685781 := bbase (se 7 (by rfl) ⟨8036, by rfl⟩ : syracuseStep 685781 = 16073) (by norm_num)
theorem B685805 : Blo 455782 685805 := bbase (se 3 (by rfl) ⟨128588, by rfl⟩ : syracuseStep 685805 = 257177) (by norm_num)
theorem B2324213 : Blo 455782 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B685829 : Blo 455782 685829 := bbase (se 4 (by rfl) ⟨64296, by rfl⟩ : syracuseStep 685829 = 128593) (by norm_num)
theorem B685853 : Blo 455782 685853 := bbase (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) (by norm_num)
theorem B685877 : Blo 455782 685877 := bbase (se 5 (by rfl) ⟨32150, by rfl⟩ : syracuseStep 685877 = 64301) (by norm_num)
theorem B685901 : Blo 455782 685901 := bbase (se 3 (by rfl) ⟨128606, by rfl⟩ : syracuseStep 685901 = 257213) (by norm_num)
theorem B685925 : Blo 455782 685925 := bbase (se 4 (by rfl) ⟨64305, by rfl⟩ : syracuseStep 685925 = 128611) (by norm_num)
theorem B1472357 : Blo 455782 1472357 := bbase (se 4 (by rfl) ⟨138033, by rfl⟩ : syracuseStep 1472357 = 276067) (by norm_num)
theorem B685949 : Blo 455782 685949 := bbase (se 3 (by rfl) ⟨128615, by rfl⟩ : syracuseStep 685949 = 257231) (by norm_num)
theorem B685973 : Blo 455782 685973 := bbase (se 6 (by rfl) ⟨16077, by rfl⟩ : syracuseStep 685973 = 32155) (by norm_num)
theorem B685997 : Blo 455782 685997 := bbase (se 3 (by rfl) ⟨128624, by rfl⟩ : syracuseStep 685997 = 257249) (by norm_num)
theorem B686021 : Blo 455782 686021 := bbase (se 4 (by rfl) ⟨64314, by rfl⟩ : syracuseStep 686021 = 128629) (by norm_num)
theorem B686045 : Blo 455782 686045 := bbase (se 3 (by rfl) ⟨128633, by rfl⟩ : syracuseStep 686045 = 257267) (by norm_num)
theorem B686069 : Blo 455782 686069 := bbase (se 5 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 686069 = 64319) (by norm_num)
theorem B489461 : Blo 455782 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B686093 : Blo 455782 686093 := bbase (se 3 (by rfl) ⟨128642, by rfl⟩ : syracuseStep 686093 = 257285) (by norm_num)
theorem B686117 : Blo 455782 686117 := bbase (se 4 (by rfl) ⟨64323, by rfl⟩ : syracuseStep 686117 = 128647) (by norm_num)
theorem B489521 : Blo 455782 489521 := bbase (se 2 (by rfl) ⟨183570, by rfl⟩ : syracuseStep 489521 = 367141) (by norm_num)
theorem B686141 : Blo 455782 686141 := bbase (se 3 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 686141 = 257303) (by norm_num)
theorem B686165 : Blo 455782 686165 := bbase (se 8 (by rfl) ⟨4020, by rfl⟩ : syracuseStep 686165 = 8041) (by norm_num)
theorem B686189 : Blo 455782 686189 := bbase (se 3 (by rfl) ⟨128660, by rfl⟩ : syracuseStep 686189 = 257321) (by norm_num)
theorem B981109 : Blo 455782 981109 := bbase (se 5 (by rfl) ⟨45989, by rfl⟩ : syracuseStep 981109 = 91979) (by norm_num)
theorem B686213 : Blo 455782 686213 := bbase (se 4 (by rfl) ⟨64332, by rfl⟩ : syracuseStep 686213 = 128665) (by norm_num)
theorem B8485013 : Blo 455782 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B686237 : Blo 455782 686237 := bbase (se 3 (by rfl) ⟨128669, by rfl⟩ : syracuseStep 686237 = 257339) (by norm_num)
theorem B489649 : Blo 455782 489649 := bbase (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) (by norm_num)
theorem B4159669 : Blo 455782 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B686261 : Blo 455782 686261 := bbase (se 5 (by rfl) ⟨32168, by rfl⟩ : syracuseStep 686261 = 64337) (by norm_num)
theorem B686285 : Blo 455782 686285 := bbase (se 3 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 686285 = 257357) (by norm_num)
theorem B686309 : Blo 455782 686309 := bbase (se 4 (by rfl) ⟨64341, by rfl⟩ : syracuseStep 686309 = 128683) (by norm_num)
theorem B981229 : Blo 455782 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B686333 : Blo 455782 686333 := bbase (se 3 (by rfl) ⟨128687, by rfl⟩ : syracuseStep 686333 = 257375) (by norm_num)
theorem B686357 : Blo 455782 686357 := bbase (se 6 (by rfl) ⟨16086, by rfl⟩ : syracuseStep 686357 = 32173) (by norm_num)
theorem B686381 : Blo 455782 686381 := bbase (se 3 (by rfl) ⟨128696, by rfl⟩ : syracuseStep 686381 = 257393) (by norm_num)
theorem B686405 : Blo 455782 686405 := bbase (se 4 (by rfl) ⟨64350, by rfl⟩ : syracuseStep 686405 = 128701) (by norm_num)
theorem B686429 : Blo 455782 686429 := bbase (se 3 (by rfl) ⟨128705, by rfl⟩ : syracuseStep 686429 = 257411) (by norm_num)
theorem B1538405 : Blo 455782 1538405 := bbase (se 4 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 1538405 = 288451) (by norm_num)
theorem B555373 : Blo 455782 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B686453 : Blo 455782 686453 := bbase (se 5 (by rfl) ⟨32177, by rfl⟩ : syracuseStep 686453 = 64355) (by norm_num)
theorem B686477 : Blo 455782 686477 := bbase (se 3 (by rfl) ⟨128714, by rfl⟩ : syracuseStep 686477 = 257429) (by norm_num)
theorem B686501 : Blo 455782 686501 := bbase (se 4 (by rfl) ⟨64359, by rfl⟩ : syracuseStep 686501 = 128719) (by norm_num)
theorem B686525 : Blo 455782 686525 := bbase (se 3 (by rfl) ⟨128723, by rfl⟩ : syracuseStep 686525 = 257447) (by norm_num)
theorem B686549 : Blo 455782 686549 := bbase (se 7 (by rfl) ⟨8045, by rfl⟩ : syracuseStep 686549 = 16091) (by norm_num)
theorem B1735141 : Blo 455782 1735141 := bbase (se 4 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 1735141 = 325339) (by norm_num)
theorem B686573 : Blo 455782 686573 := bbase (se 3 (by rfl) ⟨128732, by rfl⟩ : syracuseStep 686573 = 257465) (by norm_num)
theorem B981485 : Blo 455782 981485 := bbase (se 3 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 981485 = 368057) (by norm_num)
theorem B686597 : Blo 455782 686597 := bbase (se 4 (by rfl) ⟨64368, by rfl⟩ : syracuseStep 686597 = 128737) (by norm_num)
theorem B653845 : Blo 455782 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B686621 : Blo 455782 686621 := bbase (se 3 (by rfl) ⟨128741, by rfl⟩ : syracuseStep 686621 = 257483) (by norm_num)
theorem B686645 : Blo 455782 686645 := bbase (se 5 (by rfl) ⟨32186, by rfl⟩ : syracuseStep 686645 = 64373) (by norm_num)
theorem B686669 : Blo 455782 686669 := bbase (se 3 (by rfl) ⟨128750, by rfl⟩ : syracuseStep 686669 = 257501) (by norm_num)
theorem B784981 : Blo 455782 784981 := bbase (se 8 (by rfl) ⟨4599, by rfl⟩ : syracuseStep 784981 = 9199) (by norm_num)
theorem B686693 : Blo 455782 686693 := bbase (se 4 (by rfl) ⟨64377, by rfl⟩ : syracuseStep 686693 = 128755) (by norm_num)
theorem B490093 : Blo 455782 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B686717 : Blo 455782 686717 := bbase (se 3 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 686717 = 257519) (by norm_num)
theorem B686741 : Blo 455782 686741 := bbase (se 6 (by rfl) ⟨16095, by rfl⟩ : syracuseStep 686741 = 32191) (by norm_num)
theorem B686765 : Blo 455782 686765 := bbase (se 3 (by rfl) ⟨128768, by rfl⟩ : syracuseStep 686765 = 257537) (by norm_num)
theorem B686789 : Blo 455782 686789 := bbase (se 4 (by rfl) ⟨64386, by rfl⟩ : syracuseStep 686789 = 128773) (by norm_num)
theorem B686813 : Blo 455782 686813 := bbase (se 3 (by rfl) ⟨128777, by rfl⟩ : syracuseStep 686813 = 257555) (by norm_num)
theorem B490213 : Blo 455782 490213 := bbase (se 4 (by rfl) ⟨45957, by rfl⟩ : syracuseStep 490213 = 91915) (by norm_num)
theorem B686837 : Blo 455782 686837 := bbase (se 5 (by rfl) ⟨32195, by rfl⟩ : syracuseStep 686837 = 64391) (by norm_num)
theorem B686861 : Blo 455782 686861 := bbase (se 3 (by rfl) ⟨128786, by rfl⟩ : syracuseStep 686861 = 257573) (by norm_num)
theorem B1538837 : Blo 455782 1538837 := bbase (se 6 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 1538837 = 72133) (by norm_num)
theorem B1735445 : Blo 455782 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B686885 : Blo 455782 686885 := bbase (se 4 (by rfl) ⟨64395, by rfl⟩ : syracuseStep 686885 = 128791) (by norm_num)
theorem B686909 : Blo 455782 686909 := bbase (se 3 (by rfl) ⟨128795, by rfl⟩ : syracuseStep 686909 = 257591) (by norm_num)
theorem B686933 : Blo 455782 686933 := bbase (se 9 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 686933 = 4025) (by norm_num)
theorem B686957 : Blo 455782 686957 := bbase (se 3 (by rfl) ⟨128804, by rfl⟩ : syracuseStep 686957 = 257609) (by norm_num)
theorem B686981 : Blo 455782 686981 := bbase (se 4 (by rfl) ⟨64404, by rfl⟩ : syracuseStep 686981 = 128809) (by norm_num)
theorem B687005 : Blo 455782 687005 := bbase (se 3 (by rfl) ⟨128813, by rfl⟩ : syracuseStep 687005 = 257627) (by norm_num)
theorem B687029 : Blo 455782 687029 := bbase (se 5 (by rfl) ⟨32204, by rfl⟩ : syracuseStep 687029 = 64409) (by norm_num)
theorem B523193 : Blo 455782 523193 := bbase (se 2 (by rfl) ⟨196197, by rfl⟩ : syracuseStep 523193 = 392395) (by norm_num)
theorem B687053 : Blo 455782 687053 := bbase (se 3 (by rfl) ⟨128822, by rfl⟩ : syracuseStep 687053 = 257645) (by norm_num)
theorem B490465 : Blo 455782 490465 := bbase (se 2 (by rfl) ⟨183924, by rfl⟩ : syracuseStep 490465 = 367849) (by norm_num)
theorem B687077 : Blo 455782 687077 := bbase (se 4 (by rfl) ⟨64413, by rfl⟩ : syracuseStep 687077 = 128827) (by norm_num)
theorem B490469 : Blo 455782 490469 := bbase (se 4 (by rfl) ⟨45981, by rfl⟩ : syracuseStep 490469 = 91963) (by norm_num)
theorem B687101 : Blo 455782 687101 := bbase (se 3 (by rfl) ⟨128831, by rfl⟩ : syracuseStep 687101 = 257663) (by norm_num)
theorem B2325509 : Blo 455782 2325509 := bbase (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) (by norm_num)
theorem B687125 : Blo 455782 687125 := bbase (se 6 (by rfl) ⟨16104, by rfl⟩ : syracuseStep 687125 = 32209) (by norm_num)
theorem B687149 : Blo 455782 687149 := bbase (se 3 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 687149 = 257681) (by norm_num)
theorem B687173 : Blo 455782 687173 := bbase (se 4 (by rfl) ⟨64422, by rfl⟩ : syracuseStep 687173 = 128845) (by norm_num)
theorem B3472469 : Blo 455782 3472469 := bbase (se 8 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 3472469 = 40693) (by norm_num)
theorem B687197 : Blo 455782 687197 := bbase (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) (by norm_num)
theorem B654437 : Blo 455782 654437 := bbase (se 4 (by rfl) ⟨61353, by rfl⟩ : syracuseStep 654437 = 122707) (by norm_num)
theorem B687221 : Blo 455782 687221 := bbase (se 5 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 687221 = 64427) (by norm_num)
theorem B687245 : Blo 455782 687245 := bbase (se 3 (by rfl) ⟨128858, by rfl⟩ : syracuseStep 687245 = 257717) (by norm_num)
theorem B687269 : Blo 455782 687269 := bbase (se 4 (by rfl) ⟨64431, by rfl⟩ : syracuseStep 687269 = 128863) (by norm_num)
theorem B654517 : Blo 455782 654517 := bbase (se 5 (by rfl) ⟨30680, by rfl⟩ : syracuseStep 654517 = 61361) (by norm_num)
theorem B687293 : Blo 455782 687293 := bbase (se 3 (by rfl) ⟨128867, by rfl⟩ : syracuseStep 687293 = 257735) (by norm_num)
theorem B1539269 : Blo 455782 1539269 := bbase (se 4 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 1539269 = 288613) (by norm_num)
theorem B687317 : Blo 455782 687317 := bbase (se 7 (by rfl) ⟨8054, by rfl⟩ : syracuseStep 687317 = 16109) (by norm_num)
theorem B687341 : Blo 455782 687341 := bbase (se 3 (by rfl) ⟨128876, by rfl⟩ : syracuseStep 687341 = 257753) (by norm_num)
theorem B687365 : Blo 455782 687365 := bbase (se 4 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 687365 = 128881) (by norm_num)
theorem B687389 : Blo 455782 687389 := bbase (se 3 (by rfl) ⟨128885, by rfl⟩ : syracuseStep 687389 = 257771) (by norm_num)
theorem B654637 : Blo 455782 654637 := bbase (se 3 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 654637 = 245489) (by norm_num)
theorem B687413 : Blo 455782 687413 := bbase (se 5 (by rfl) ⟨32222, by rfl⟩ : syracuseStep 687413 = 64445) (by norm_num)
theorem B687437 : Blo 455782 687437 := bbase (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) (by norm_num)
theorem B7142741 : Blo 455782 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B687461 : Blo 455782 687461 := bbase (se 4 (by rfl) ⟨64449, by rfl⟩ : syracuseStep 687461 = 128899) (by norm_num)
theorem B687485 : Blo 455782 687485 := bbase (se 3 (by rfl) ⟨128903, by rfl⟩ : syracuseStep 687485 = 257807) (by norm_num)
theorem B687509 : Blo 455782 687509 := bbase (se 6 (by rfl) ⟨16113, by rfl⟩ : syracuseStep 687509 = 32227) (by norm_num)
theorem B1047973 : Blo 455782 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B687533 : Blo 455782 687533 := bbase (se 3 (by rfl) ⟨128912, by rfl⟩ : syracuseStep 687533 = 257825) (by norm_num)
theorem B687557 : Blo 455782 687557 := bbase (se 4 (by rfl) ⟨64458, by rfl⟩ : syracuseStep 687557 = 128917) (by norm_num)
theorem B687581 : Blo 455782 687581 := bbase (se 3 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 687581 = 257843) (by norm_num)
theorem B687605 : Blo 455782 687605 := bbase (se 5 (by rfl) ⟨32231, by rfl⟩ : syracuseStep 687605 = 64463) (by norm_num)
theorem B687629 : Blo 455782 687629 := bbase (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) (by norm_num)
theorem B687653 : Blo 455782 687653 := bbase (se 4 (by rfl) ⟨64467, by rfl⟩ : syracuseStep 687653 = 128935) (by norm_num)
theorem B687677 : Blo 455782 687677 := bbase (se 3 (by rfl) ⟨128939, by rfl⟩ : syracuseStep 687677 = 257879) (by norm_num)
theorem B589393 : Blo 455782 589393 := bbase (se 2 (by rfl) ⟨221022, by rfl⟩ : syracuseStep 589393 = 442045) (by norm_num)
theorem B687701 : Blo 455782 687701 := bbase (se 8 (by rfl) ⟨4029, by rfl⟩ : syracuseStep 687701 = 8059) (by norm_num)
theorem B687725 : Blo 455782 687725 := bbase (se 3 (by rfl) ⟨128948, by rfl⟩ : syracuseStep 687725 = 257897) (by norm_num)
theorem B1539701 : Blo 455782 1539701 := bbase (se 5 (by rfl) ⟨72173, by rfl⟩ : syracuseStep 1539701 = 144347) (by norm_num)
theorem B687749 : Blo 455782 687749 := bbase (se 4 (by rfl) ⟨64476, by rfl⟩ : syracuseStep 687749 = 128953) (by norm_num)
theorem B687773 : Blo 455782 687773 := bbase (se 3 (by rfl) ⟨128957, by rfl⟩ : syracuseStep 687773 = 257915) (by norm_num)
theorem B687797 : Blo 455782 687797 := bbase (se 5 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 687797 = 64481) (by norm_num)
theorem B589513 : Blo 455782 589513 := bbase (se 2 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 589513 = 442135) (by norm_num)
theorem B687821 : Blo 455782 687821 := bbase (se 3 (by rfl) ⟨128966, by rfl⟩ : syracuseStep 687821 = 257933) (by norm_num)
theorem B687845 : Blo 455782 687845 := bbase (se 4 (by rfl) ⟨64485, by rfl⟩ : syracuseStep 687845 = 128971) (by norm_num)
theorem B687869 : Blo 455782 687869 := bbase (se 3 (by rfl) ⟨128975, by rfl⟩ : syracuseStep 687869 = 257951) (by norm_num)
theorem B687893 : Blo 455782 687893 := bbase (se 6 (by rfl) ⟨16122, by rfl⟩ : syracuseStep 687893 = 32245) (by norm_num)
theorem B687917 : Blo 455782 687917 := bbase (se 3 (by rfl) ⟨128984, by rfl⟩ : syracuseStep 687917 = 257969) (by norm_num)
theorem B687941 : Blo 455782 687941 := bbase (se 4 (by rfl) ⟨64494, by rfl⟩ : syracuseStep 687941 = 128989) (by norm_num)
theorem B1769285 : Blo 455782 1769285 := bbase (se 4 (by rfl) ⟨165870, by rfl⟩ : syracuseStep 1769285 = 331741) (by norm_num)
theorem B687965 : Blo 455782 687965 := bbase (se 3 (by rfl) ⟨128993, by rfl⟩ : syracuseStep 687965 = 257987) (by norm_num)
theorem B687989 : Blo 455782 687989 := bbase (se 5 (by rfl) ⟨32249, by rfl⟩ : syracuseStep 687989 = 64499) (by norm_num)
theorem B688013 : Blo 455782 688013 := bbase (se 3 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 688013 = 258005) (by norm_num)
theorem B3899285 : Blo 455782 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B688037 : Blo 455782 688037 := bbase (se 4 (by rfl) ⟨64503, by rfl⟩ : syracuseStep 688037 = 129007) (by norm_num)
theorem B688061 : Blo 455782 688061 := bbase (se 3 (by rfl) ⟨129011, by rfl⟩ : syracuseStep 688061 = 258023) (by norm_num)
theorem B688085 : Blo 455782 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B688109 : Blo 455782 688109 := bbase (se 3 (by rfl) ⟨129020, by rfl⟩ : syracuseStep 688109 = 258041) (by norm_num)
theorem B3702773 : Blo 455782 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B458755 : Blo 455782 458755 := bstep (se 1 (by rfl) ⟨344066, by rfl⟩ : syracuseStep 458755 = 688133) B688133
theorem B688145 : Blo 455782 688145 := bstep (se 2 (by rfl) ⟨258054, by rfl⟩ : syracuseStep 688145 = 516109) B516109
theorem B458771 : Blo 455782 458771 := bstep (se 1 (by rfl) ⟨344078, by rfl⟩ : syracuseStep 458771 = 688157) B688157
theorem B688163 : Blo 455782 688163 := bstep (se 1 (by rfl) ⟨516122, by rfl⟩ : syracuseStep 688163 = 1032245) B1032245
theorem B458787 : Blo 455782 458787 := bstep (se 1 (by rfl) ⟨344090, by rfl⟩ : syracuseStep 458787 = 688181) B688181
theorem B458803 : Blo 455782 458803 := bstep (se 1 (by rfl) ⟨344102, by rfl⟩ : syracuseStep 458803 = 688205) B688205
theorem B688193 : Blo 455782 688193 := bstep (se 2 (by rfl) ⟨258072, by rfl⟩ : syracuseStep 688193 = 516145) B516145
theorem B458819 : Blo 455782 458819 := bstep (se 1 (by rfl) ⟨344114, by rfl⟩ : syracuseStep 458819 = 688229) B688229
theorem B688211 : Blo 455782 688211 := bstep (se 1 (by rfl) ⟨516158, by rfl⟩ : syracuseStep 688211 = 1032317) B1032317
theorem B458835 : Blo 455782 458835 := bstep (se 1 (by rfl) ⟨344126, by rfl⟩ : syracuseStep 458835 = 688253) B688253
theorem B458851 : Blo 455782 458851 := bstep (se 1 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 458851 = 688277) B688277
theorem B688241 : Blo 455782 688241 := bstep (se 2 (by rfl) ⟨258090, by rfl⟩ : syracuseStep 688241 = 516181) B516181
theorem B458867 : Blo 455782 458867 := bstep (se 1 (by rfl) ⟨344150, by rfl⟩ : syracuseStep 458867 = 688301) B688301
theorem B688259 : Blo 455782 688259 := bstep (se 1 (by rfl) ⟨516194, by rfl⟩ : syracuseStep 688259 = 1032389) B1032389
theorem B458883 : Blo 455782 458883 := bstep (se 1 (by rfl) ⟨344162, by rfl⟩ : syracuseStep 458883 = 688325) B688325
theorem B1540241 : Blo 455782 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B458899 : Blo 455782 458899 := bstep (se 1 (by rfl) ⟨344174, by rfl⟩ : syracuseStep 458899 = 688349) B688349
theorem B688289 : Blo 455782 688289 := bstep (se 2 (by rfl) ⟨258108, by rfl⟩ : syracuseStep 688289 = 516217) B516217
theorem B458915 : Blo 455782 458915 := bstep (se 1 (by rfl) ⟨344186, by rfl⟩ : syracuseStep 458915 = 688373) B688373
theorem B688307 : Blo 455782 688307 := bstep (se 1 (by rfl) ⟨516230, by rfl⟩ : syracuseStep 688307 = 1032461) B1032461
theorem B458931 : Blo 455782 458931 := bstep (se 1 (by rfl) ⟨344198, by rfl⟩ : syracuseStep 458931 = 688397) B688397
theorem B458947 : Blo 455782 458947 := bstep (se 1 (by rfl) ⟨344210, by rfl⟩ : syracuseStep 458947 = 688421) B688421
theorem B688337 : Blo 455782 688337 := bstep (se 2 (by rfl) ⟨258126, by rfl⟩ : syracuseStep 688337 = 516253) B516253
theorem B458963 : Blo 455782 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B688355 : Blo 455782 688355 := bstep (se 1 (by rfl) ⟨516266, by rfl⟩ : syracuseStep 688355 = 1032533) B1032533
theorem B458979 : Blo 455782 458979 := bstep (se 1 (by rfl) ⟨344234, by rfl⟩ : syracuseStep 458979 = 688469) B688469
theorem B458995 : Blo 455782 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B688385 : Blo 455782 688385 := bstep (se 2 (by rfl) ⟨258144, by rfl⟩ : syracuseStep 688385 = 516289) B516289
theorem B459011 : Blo 455782 459011 := bstep (se 1 (by rfl) ⟨344258, by rfl⟩ : syracuseStep 459011 = 688517) B688517
theorem B688403 : Blo 455782 688403 := bstep (se 1 (by rfl) ⟨516302, by rfl⟩ : syracuseStep 688403 = 1032605) B1032605
theorem B459027 : Blo 455782 459027 := bstep (se 1 (by rfl) ⟨344270, by rfl⟩ : syracuseStep 459027 = 688541) B688541
theorem B459043 : Blo 455782 459043 := bstep (se 1 (by rfl) ⟨344282, by rfl⟩ : syracuseStep 459043 = 688565) B688565
theorem B688433 : Blo 455782 688433 := bstep (se 2 (by rfl) ⟨258162, by rfl⟩ : syracuseStep 688433 = 516325) B516325
theorem B459059 : Blo 455782 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B688451 : Blo 455782 688451 := bstep (se 1 (by rfl) ⟨516338, by rfl⟩ : syracuseStep 688451 = 1032677) B1032677
theorem B459075 : Blo 455782 459075 := bstep (se 1 (by rfl) ⟨344306, by rfl⟩ : syracuseStep 459075 = 688613) B688613
theorem B459091 : Blo 455782 459091 := bstep (se 1 (by rfl) ⟨344318, by rfl⟩ : syracuseStep 459091 = 688637) B688637
theorem B688481 : Blo 455782 688481 := bstep (se 2 (by rfl) ⟨258180, by rfl⟩ : syracuseStep 688481 = 516361) B516361
theorem B459107 : Blo 455782 459107 := bstep (se 1 (by rfl) ⟨344330, by rfl⟩ : syracuseStep 459107 = 688661) B688661
theorem B688499 : Blo 455782 688499 := bstep (se 1 (by rfl) ⟨516374, by rfl⟩ : syracuseStep 688499 = 1032749) B1032749
theorem B459123 : Blo 455782 459123 := bstep (se 1 (by rfl) ⟨344342, by rfl⟩ : syracuseStep 459123 = 688685) B688685
theorem B459139 : Blo 455782 459139 := bstep (se 1 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 459139 = 688709) B688709
theorem B688529 : Blo 455782 688529 := bstep (se 2 (by rfl) ⟨258198, by rfl⟩ : syracuseStep 688529 = 516397) B516397
theorem B459155 : Blo 455782 459155 := bstep (se 1 (by rfl) ⟨344366, by rfl⟩ : syracuseStep 459155 = 688733) B688733
theorem B688547 : Blo 455782 688547 := bstep (se 1 (by rfl) ⟨516410, by rfl⟩ : syracuseStep 688547 = 1032821) B1032821
theorem B459171 : Blo 455782 459171 := bstep (se 1 (by rfl) ⟨344378, by rfl⟩ : syracuseStep 459171 = 688757) B688757
theorem B459187 : Blo 455782 459187 := bstep (se 1 (by rfl) ⟨344390, by rfl⟩ : syracuseStep 459187 = 688781) B688781
theorem B688577 : Blo 455782 688577 := bstep (se 2 (by rfl) ⟨258216, by rfl⟩ : syracuseStep 688577 = 516433) B516433
theorem B459203 : Blo 455782 459203 := bstep (se 1 (by rfl) ⟨344402, by rfl⟩ : syracuseStep 459203 = 688805) B688805
theorem B688595 : Blo 455782 688595 := bstep (se 1 (by rfl) ⟨516446, by rfl⟩ : syracuseStep 688595 = 1032893) B1032893
theorem B459219 : Blo 455782 459219 := bstep (se 1 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 459219 = 688829) B688829
theorem B459235 : Blo 455782 459235 := bstep (se 1 (by rfl) ⟨344426, by rfl⟩ : syracuseStep 459235 = 688853) B688853
theorem B688625 : Blo 455782 688625 := bstep (se 2 (by rfl) ⟨258234, by rfl⟩ : syracuseStep 688625 = 516469) B516469
theorem B459251 : Blo 455782 459251 := bstep (se 1 (by rfl) ⟨344438, by rfl⟩ : syracuseStep 459251 = 688877) B688877
theorem B688643 : Blo 455782 688643 := bstep (se 1 (by rfl) ⟨516482, by rfl⟩ : syracuseStep 688643 = 1032965) B1032965
theorem B459267 : Blo 455782 459267 := bstep (se 1 (by rfl) ⟨344450, by rfl⟩ : syracuseStep 459267 = 688901) B688901
theorem B459283 : Blo 455782 459283 := bstep (se 1 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 459283 = 688925) B688925
theorem B688673 : Blo 455782 688673 := bstep (se 2 (by rfl) ⟨258252, by rfl⟩ : syracuseStep 688673 = 516505) B516505
theorem B459299 : Blo 455782 459299 := bstep (se 1 (by rfl) ⟨344474, by rfl⟩ : syracuseStep 459299 = 688949) B688949
theorem B688691 : Blo 455782 688691 := bstep (se 1 (by rfl) ⟨516518, by rfl⟩ : syracuseStep 688691 = 1033037) B1033037
theorem B459315 : Blo 455782 459315 := bstep (se 1 (by rfl) ⟨344486, by rfl⟩ : syracuseStep 459315 = 688973) B688973
theorem B459331 : Blo 455782 459331 := bstep (se 1 (by rfl) ⟨344498, by rfl⟩ : syracuseStep 459331 = 688997) B688997
theorem B688721 : Blo 455782 688721 := bstep (se 2 (by rfl) ⟨258270, by rfl⟩ : syracuseStep 688721 = 516541) B516541
theorem B459347 : Blo 455782 459347 := bstep (se 1 (by rfl) ⟨344510, by rfl⟩ : syracuseStep 459347 = 689021) B689021
theorem B688739 : Blo 455782 688739 := bstep (se 1 (by rfl) ⟨516554, by rfl⟩ : syracuseStep 688739 = 1033109) B1033109
theorem B459363 : Blo 455782 459363 := bstep (se 1 (by rfl) ⟨344522, by rfl⟩ : syracuseStep 459363 = 689045) B689045
theorem B2228849 : Blo 455782 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B459379 : Blo 455782 459379 := bstep (se 1 (by rfl) ⟨344534, by rfl⟩ : syracuseStep 459379 = 689069) B689069
theorem B688769 : Blo 455782 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B459395 : Blo 455782 459395 := bstep (se 1 (by rfl) ⟨344546, by rfl⟩ : syracuseStep 459395 = 689093) B689093
theorem B688787 : Blo 455782 688787 := bstep (se 1 (by rfl) ⟨516590, by rfl⟩ : syracuseStep 688787 = 1033181) B1033181
theorem B459411 : Blo 455782 459411 := bstep (se 1 (by rfl) ⟨344558, by rfl⟩ : syracuseStep 459411 = 689117) B689117
theorem B459427 : Blo 455782 459427 := bstep (se 1 (by rfl) ⟨344570, by rfl⟩ : syracuseStep 459427 = 689141) B689141
theorem B1540781 : Blo 455782 1540781 := bstep (se 3 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 1540781 = 577793) B577793
theorem B688817 : Blo 455782 688817 := bstep (se 2 (by rfl) ⟨258306, by rfl⟩ : syracuseStep 688817 = 516613) B516613
theorem B459443 : Blo 455782 459443 := bstep (se 1 (by rfl) ⟨344582, by rfl⟩ : syracuseStep 459443 = 689165) B689165
theorem B688835 : Blo 455782 688835 := bstep (se 1 (by rfl) ⟨516626, by rfl⟩ : syracuseStep 688835 = 1033253) B1033253
theorem B459459 : Blo 455782 459459 := bstep (se 1 (by rfl) ⟨344594, by rfl⟩ : syracuseStep 459459 = 689189) B689189
theorem B459475 : Blo 455782 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B688865 : Blo 455782 688865 := bstep (se 2 (by rfl) ⟨258324, by rfl⟩ : syracuseStep 688865 = 516649) B516649
theorem B1540835 : Blo 455782 1540835 := bstep (se 1 (by rfl) ⟨1155626, by rfl⟩ : syracuseStep 1540835 = 2311253) B2311253
theorem B459491 : Blo 455782 459491 := bstep (se 1 (by rfl) ⟨344618, by rfl⟩ : syracuseStep 459491 = 689237) B689237
theorem B3310321 : Blo 455782 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B688883 : Blo 455782 688883 := bstep (se 1 (by rfl) ⟨516662, by rfl⟩ : syracuseStep 688883 = 1033325) B1033325
theorem B459507 : Blo 455782 459507 := bstep (se 1 (by rfl) ⟨344630, by rfl⟩ : syracuseStep 459507 = 689261) B689261
theorem B459523 : Blo 455782 459523 := bstep (se 1 (by rfl) ⟨344642, by rfl⟩ : syracuseStep 459523 = 689285) B689285
theorem B688913 : Blo 455782 688913 := bstep (se 2 (by rfl) ⟨258342, by rfl⟩ : syracuseStep 688913 = 516685) B516685
theorem B459539 : Blo 455782 459539 := bstep (se 1 (by rfl) ⟨344654, by rfl⟩ : syracuseStep 459539 = 689309) B689309
theorem B688931 : Blo 455782 688931 := bstep (se 1 (by rfl) ⟨516698, by rfl⟩ : syracuseStep 688931 = 1033397) B1033397
theorem B459555 : Blo 455782 459555 := bstep (se 1 (by rfl) ⟨344666, by rfl⟩ : syracuseStep 459555 = 689333) B689333
theorem B459571 : Blo 455782 459571 := bstep (se 1 (by rfl) ⟨344678, by rfl⟩ : syracuseStep 459571 = 689357) B689357
theorem B688961 : Blo 455782 688961 := bstep (se 2 (by rfl) ⟨258360, by rfl⟩ : syracuseStep 688961 = 516721) B516721
theorem B459587 : Blo 455782 459587 := bstep (se 1 (by rfl) ⟨344690, by rfl⟩ : syracuseStep 459587 = 689381) B689381
theorem B688979 : Blo 455782 688979 := bstep (se 1 (by rfl) ⟨516734, by rfl⟩ : syracuseStep 688979 = 1033469) B1033469
theorem B459603 : Blo 455782 459603 := bstep (se 1 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 459603 = 689405) B689405
theorem B1737571 : Blo 455782 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B459619 : Blo 455782 459619 := bstep (se 1 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 459619 = 689429) B689429
theorem B689009 : Blo 455782 689009 := bstep (se 2 (by rfl) ⟨258378, by rfl⟩ : syracuseStep 689009 = 516757) B516757
theorem B459635 : Blo 455782 459635 := bstep (se 1 (by rfl) ⟨344726, by rfl⟩ : syracuseStep 459635 = 689453) B689453
theorem B689027 : Blo 455782 689027 := bstep (se 1 (by rfl) ⟨516770, by rfl⟩ : syracuseStep 689027 = 1033541) B1033541
theorem B459651 : Blo 455782 459651 := bstep (se 1 (by rfl) ⟨344738, by rfl⟩ : syracuseStep 459651 = 689477) B689477
theorem B459667 : Blo 455782 459667 := bstep (se 1 (by rfl) ⟨344750, by rfl⟩ : syracuseStep 459667 = 689501) B689501
theorem B689057 : Blo 455782 689057 := bstep (se 2 (by rfl) ⟨258396, by rfl⟩ : syracuseStep 689057 = 516793) B516793
theorem B459683 : Blo 455782 459683 := bstep (se 1 (by rfl) ⟨344762, by rfl⟩ : syracuseStep 459683 = 689525) B689525
theorem B689075 : Blo 455782 689075 := bstep (se 1 (by rfl) ⟨516806, by rfl⟩ : syracuseStep 689075 = 1033613) B1033613
theorem B459699 : Blo 455782 459699 := bstep (se 1 (by rfl) ⟨344774, by rfl⟩ : syracuseStep 459699 = 689549) B689549
theorem B459715 : Blo 455782 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B689105 : Blo 455782 689105 := bstep (se 2 (by rfl) ⟨258414, by rfl⟩ : syracuseStep 689105 = 516829) B516829
theorem B459731 : Blo 455782 459731 := bstep (se 1 (by rfl) ⟨344798, by rfl⟩ : syracuseStep 459731 = 689597) B689597
theorem B689123 : Blo 455782 689123 := bstep (se 1 (by rfl) ⟨516842, by rfl⟩ : syracuseStep 689123 = 1033685) B1033685
theorem B459747 : Blo 455782 459747 := bstep (se 1 (by rfl) ⟨344810, by rfl⟩ : syracuseStep 459747 = 689621) B689621
theorem B1541105 : Blo 455782 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B459763 : Blo 455782 459763 := bstep (se 1 (by rfl) ⟨344822, by rfl⟩ : syracuseStep 459763 = 689645) B689645
theorem B689153 : Blo 455782 689153 := bstep (se 2 (by rfl) ⟨258432, by rfl⟩ : syracuseStep 689153 = 516865) B516865
theorem B459779 : Blo 455782 459779 := bstep (se 1 (by rfl) ⟨344834, by rfl⟩ : syracuseStep 459779 = 689669) B689669
theorem B689171 : Blo 455782 689171 := bstep (se 1 (by rfl) ⟨516878, by rfl⟩ : syracuseStep 689171 = 1033757) B1033757
theorem B689201 : Blo 455782 689201 := bstep (se 2 (by rfl) ⟨258450, by rfl⟩ : syracuseStep 689201 = 516901) B516901
theorem B689219 : Blo 455782 689219 := bstep (se 1 (by rfl) ⟨516914, by rfl⟩ : syracuseStep 689219 = 1033829) B1033829
theorem B689249 : Blo 455782 689249 := bstep (se 2 (by rfl) ⟨258468, by rfl⟩ : syracuseStep 689249 = 516937) B516937
theorem B689267 : Blo 455782 689267 := bstep (se 1 (by rfl) ⟨516950, by rfl⟩ : syracuseStep 689267 = 1033901) B1033901
theorem B689297 : Blo 455782 689297 := bstep (se 2 (by rfl) ⟨258486, by rfl⟩ : syracuseStep 689297 = 516973) B516973
theorem B689315 : Blo 455782 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B689345 : Blo 455782 689345 := bstep (se 2 (by rfl) ⟨258504, by rfl⟩ : syracuseStep 689345 = 517009) B517009
theorem B689363 : Blo 455782 689363 := bstep (se 1 (by rfl) ⟨517022, by rfl⟩ : syracuseStep 689363 = 1034045) B1034045
theorem B689393 : Blo 455782 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B689411 : Blo 455782 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B689441 : Blo 455782 689441 := bstep (se 2 (by rfl) ⟨258540, by rfl⟩ : syracuseStep 689441 = 517081) B517081
theorem B689459 : Blo 455782 689459 := bstep (se 1 (by rfl) ⟨517094, by rfl⟩ : syracuseStep 689459 = 1034189) B1034189
theorem B689489 : Blo 455782 689489 := bstep (se 2 (by rfl) ⟨258558, by rfl⟩ : syracuseStep 689489 = 517117) B517117
theorem B689507 : Blo 455782 689507 := bstep (se 1 (by rfl) ⟨517130, by rfl⟩ : syracuseStep 689507 = 1034261) B1034261
theorem B689537 : Blo 455782 689537 := bstep (se 2 (by rfl) ⟨258576, by rfl⟩ : syracuseStep 689537 = 517153) B517153
theorem B689555 : Blo 455782 689555 := bstep (se 1 (by rfl) ⟨517166, by rfl⟩ : syracuseStep 689555 = 1034333) B1034333
theorem B689585 : Blo 455782 689585 := bstep (se 2 (by rfl) ⟨258594, by rfl⟩ : syracuseStep 689585 = 517189) B517189
theorem B689603 : Blo 455782 689603 := bstep (se 1 (by rfl) ⟨517202, by rfl⟩ : syracuseStep 689603 = 1034405) B1034405
theorem B689633 : Blo 455782 689633 := bstep (se 2 (by rfl) ⟨258612, by rfl⟩ : syracuseStep 689633 = 517225) B517225
theorem B689651 : Blo 455782 689651 := bstep (se 1 (by rfl) ⟨517238, by rfl⟩ : syracuseStep 689651 = 1034477) B1034477
theorem B1541645 : Blo 455782 1541645 := bstep (se 3 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 1541645 = 578117) B578117
theorem B1541699 : Blo 455782 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B6620869 : Blo 455782 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B2787149 : Blo 455782 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B1541969 : Blo 455782 1541969 := bstep (se 2 (by rfl) ⟨578238, by rfl⟩ : syracuseStep 1541969 = 1156477) B1156477
theorem B1542509 : Blo 455782 1542509 := bstep (se 3 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 1542509 = 578441) B578441
theorem B1542563 : Blo 455782 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B1542833 : Blo 455782 1542833 := bstep (se 2 (by rfl) ⟨578562, by rfl⟩ : syracuseStep 1542833 = 1157125) B1157125
theorem B4393925 : Blo 455782 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B1412099 : Blo 455782 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B1739789 : Blo 455782 1739789 := bstep (se 3 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 1739789 = 652421) B652421
theorem B822449 : Blo 455782 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B8359109 : Blo 455782 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B1543373 : Blo 455782 1543373 := bstep (se 3 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 1543373 = 578765) B578765
theorem B1543427 : Blo 455782 1543427 := bstep (se 1 (by rfl) ⟨1157570, by rfl⟩ : syracuseStep 1543427 = 2315141) B2315141
theorem B822737 : Blo 455782 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B1543697 : Blo 455782 1543697 := bstep (se 2 (by rfl) ⟨578886, by rfl⟩ : syracuseStep 1543697 = 1157773) B1157773
theorem B1544237 : Blo 455782 1544237 := bstep (se 3 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 1544237 = 579089) B579089
theorem B2822221 : Blo 455782 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B1544291 : Blo 455782 1544291 := bstep (se 1 (by rfl) ⟨1158218, by rfl⟩ : syracuseStep 1544291 = 2316437) B2316437
theorem B7901381 : Blo 455782 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B1544561 : Blo 455782 1544561 := bstep (se 2 (by rfl) ⟨579210, by rfl⟩ : syracuseStep 1544561 = 1158421) B1158421
theorem B2921285 : Blo 455782 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B1545101 : Blo 455782 1545101 := bstep (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) B579413
theorem B693139 : Blo 455782 693139 := bstep (se 1 (by rfl) ⟨519854, by rfl⟩ : syracuseStep 693139 = 1039709) B1039709
theorem B1545155 : Blo 455782 1545155 := bstep (se 1 (by rfl) ⟨1158866, by rfl⟩ : syracuseStep 1545155 = 2317733) B2317733
theorem B1545425 : Blo 455782 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B660803 : Blo 455782 660803 := bstep (se 1 (by rfl) ⟨495602, by rfl⟩ : syracuseStep 660803 = 991205) B991205
theorem B12719501 : Blo 455782 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B824899 : Blo 455782 824899 := bstep (se 1 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 824899 = 1237349) B1237349
theorem B1545965 : Blo 455782 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B1546019 : Blo 455782 1546019 := bstep (se 1 (by rfl) ⟨1159514, by rfl⟩ : syracuseStep 1546019 = 2319029) B2319029
theorem B1677133 : Blo 455782 1677133 := bstep (se 3 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 1677133 = 628925) B628925
theorem B530275 : Blo 455782 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B1742705 : Blo 455782 1742705 := bstep (se 2 (by rfl) ⟨653514, by rfl⟩ : syracuseStep 1742705 = 1307029) B1307029
theorem B694307 : Blo 455782 694307 := bstep (se 1 (by rfl) ⟨520730, by rfl⟩ : syracuseStep 694307 = 1041461) B1041461
theorem B1546289 : Blo 455782 1546289 := bstep (se 2 (by rfl) ⟨579858, by rfl⟩ : syracuseStep 1546289 = 1159717) B1159717
theorem B5544035 : Blo 455782 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B1546829 : Blo 455782 1546829 := bstep (se 3 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 1546829 = 580061) B580061
theorem B1546883 : Blo 455782 1546883 := bstep (se 1 (by rfl) ⟨1160162, by rfl⟩ : syracuseStep 1546883 = 2320325) B2320325
theorem B2923235 : Blo 455782 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B3709709 : Blo 455782 3709709 := bstep (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) B1391141
theorem B1547153 : Blo 455782 1547153 := bstep (se 2 (by rfl) ⟨580182, by rfl⟩ : syracuseStep 1547153 = 1160365) B1160365
theorem B1154321 : Blo 455782 1154321 := bstep (se 2 (by rfl) ⟨432870, by rfl⟩ : syracuseStep 1154321 = 865741) B865741
theorem B1744163 : Blo 455782 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B1154371 : Blo 455782 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B1547693 : Blo 455782 1547693 := bstep (se 3 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 1547693 = 580385) B580385
theorem B1154513 : Blo 455782 1154513 := bstep (se 2 (by rfl) ⟨432942, by rfl⟩ : syracuseStep 1154513 = 865885) B865885
theorem B1547747 : Blo 455782 1547747 := bstep (se 1 (by rfl) ⟨1160810, by rfl⟩ : syracuseStep 1547747 = 2321621) B2321621
theorem B3120653 : Blo 455782 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B1548017 : Blo 455782 1548017 := bstep (se 2 (by rfl) ⟨580506, by rfl⟩ : syracuseStep 1548017 = 1161013) B1161013
theorem B696131 : Blo 455782 696131 := bstep (se 1 (by rfl) ⟨522098, by rfl⟩ : syracuseStep 696131 = 1044197) B1044197
theorem B5546225 : Blo 455782 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B1548557 : Blo 455782 1548557 := bstep (se 3 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 1548557 = 580709) B580709
theorem B1745165 : Blo 455782 1745165 := bstep (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) B654437
theorem B1548611 : Blo 455782 1548611 := bstep (se 1 (by rfl) ⟨1161458, by rfl⟩ : syracuseStep 1548611 = 2322917) B2322917
theorem B696691 : Blo 455782 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B1155505 : Blo 455782 1155505 := bstep (se 2 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 1155505 = 866629) B866629
theorem B5022179 : Blo 455782 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B1548881 : Blo 455782 1548881 := bstep (se 2 (by rfl) ⟨580830, by rfl⟩ : syracuseStep 1548881 = 1161661) B1161661
theorem B1155779 : Blo 455782 1155779 := bstep (se 1 (by rfl) ⟨866834, by rfl⟩ : syracuseStep 1155779 = 1733669) B1733669
theorem B1155971 : Blo 455782 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B1549421 : Blo 455782 1549421 := bstep (se 3 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 1549421 = 581033) B581033
theorem B5547149 : Blo 455782 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B1549475 : Blo 455782 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B2598065 : Blo 455782 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B2204941 : Blo 455782 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B927121 : Blo 455782 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B1549745 : Blo 455782 1549745 := bstep (se 2 (by rfl) ⟨581154, by rfl⟩ : syracuseStep 1549745 = 1162309) B1162309
theorem B1025585 : Blo 455782 1025585 := bstep (se 2 (by rfl) ⟨384594, by rfl⟩ : syracuseStep 1025585 = 769189) B769189
theorem B1025603 : Blo 455782 1025603 := bstep (se 1 (by rfl) ⟨769202, by rfl⟩ : syracuseStep 1025603 = 1538405) B1538405
theorem B1156913 : Blo 455782 1156913 := bstep (se 2 (by rfl) ⟨433842, by rfl⟩ : syracuseStep 1156913 = 867685) B867685
theorem B1025873 : Blo 455782 1025873 := bstep (se 2 (by rfl) ⟨384702, by rfl⟩ : syracuseStep 1025873 = 769405) B769405
theorem B1025891 : Blo 455782 1025891 := bstep (se 1 (by rfl) ⟨769418, by rfl⟩ : syracuseStep 1025891 = 1538837) B1538837
theorem B1156963 : Blo 455782 1156963 := bstep (se 1 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 1156963 = 1735445) B1735445
theorem B1550285 : Blo 455782 1550285 := bstep (se 3 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 1550285 = 581357) B581357
theorem B1157105 : Blo 455782 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B1550339 : Blo 455782 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B1026161 : Blo 455782 1026161 := bstep (se 2 (by rfl) ⟨384810, by rfl⟩ : syracuseStep 1026161 = 769621) B769621
theorem B1026179 : Blo 455782 1026179 := bstep (se 1 (by rfl) ⟨769634, by rfl⟩ : syracuseStep 1026179 = 1539269) B1539269
theorem B4761827 : Blo 455782 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B1550609 : Blo 455782 1550609 := bstep (se 2 (by rfl) ⟨581478, by rfl⟩ : syracuseStep 1550609 = 1162957) B1162957
theorem B2926925 : Blo 455782 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B1026449 : Blo 455782 1026449 := bstep (se 2 (by rfl) ⟨384918, by rfl⟩ : syracuseStep 1026449 = 769837) B769837
theorem B1026467 : Blo 455782 1026467 := bstep (se 1 (by rfl) ⟨769850, by rfl⟩ : syracuseStep 1026467 = 1539701) B1539701
theorem B731603 : Blo 455782 731603 := bstep (se 1 (by rfl) ⟨548702, by rfl⟩ : syracuseStep 731603 = 1097405) B1097405
theorem B2599523 : Blo 455782 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B2468515 : Blo 455782 2468515 := bstep (se 1 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 2468515 = 3702773) B3702773
theorem B1026737 : Blo 455782 1026737 := bstep (se 2 (by rfl) ⟨385026, by rfl⟩ : syracuseStep 1026737 = 770053) B770053
theorem B928433 : Blo 455782 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B1026755 : Blo 455782 1026755 := bstep (se 1 (by rfl) ⟨770066, by rfl⟩ : syracuseStep 1026755 = 1540133) B1540133
theorem B928465 : Blo 455782 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B1551149 : Blo 455782 1551149 := bstep (se 3 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 1551149 = 581681) B581681
theorem B1551203 : Blo 455782 1551203 := bstep (se 1 (by rfl) ⟨1163402, by rfl⟩ : syracuseStep 1551203 = 2326805) B2326805
theorem B1027025 : Blo 455782 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B1158097 : Blo 455782 1158097 := bstep (se 2 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 1158097 = 868573) B868573
theorem B1027043 : Blo 455782 1027043 := bstep (se 1 (by rfl) ⟨770282, by rfl⟩ : syracuseStep 1027043 = 1540565) B1540565
theorem B1551473 : Blo 455782 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B1158371 : Blo 455782 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B1027313 : Blo 455782 1027313 := bstep (se 2 (by rfl) ⟨385242, by rfl⟩ : syracuseStep 1027313 = 770485) B770485
theorem B1027331 : Blo 455782 1027331 := bstep (se 1 (by rfl) ⟨770498, by rfl⟩ : syracuseStep 1027331 = 1540997) B1540997
theorem B732449 : Blo 455782 732449 := bstep (se 2 (by rfl) ⟨274668, by rfl⟩ : syracuseStep 732449 = 549337) B549337
theorem B1158563 : Blo 455782 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B1027601 : Blo 455782 1027601 := bstep (se 2 (by rfl) ⟨385350, by rfl⟩ : syracuseStep 1027601 = 770701) B770701
theorem B1027619 : Blo 455782 1027619 := bstep (se 1 (by rfl) ⟨770714, by rfl⟩ : syracuseStep 1027619 = 1541429) B1541429
theorem B1322531 : Blo 455782 1322531 := bstep (se 1 (by rfl) ⟨991898, by rfl⟩ : syracuseStep 1322531 = 1983797) B1983797
theorem B2600525 : Blo 455782 2600525 := bstep (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) B975197
theorem B1650289 : Blo 455782 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B1060547 : Blo 455782 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B1027889 : Blo 455782 1027889 := bstep (se 2 (by rfl) ⟨385458, by rfl⟩ : syracuseStep 1027889 = 770917) B770917
theorem B1027907 : Blo 455782 1027907 := bstep (se 1 (by rfl) ⟨770930, by rfl⟩ : syracuseStep 1027907 = 1541861) B1541861
theorem B733187 : Blo 455782 733187 := bstep (se 1 (by rfl) ⟨549890, by rfl⟩ : syracuseStep 733187 = 1099781) B1099781
theorem B667667 : Blo 455782 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B1880099 : Blo 455782 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B1028177 : Blo 455782 1028177 := bstep (se 2 (by rfl) ⟨385566, by rfl⟩ : syracuseStep 1028177 = 771133) B771133
theorem B1028195 : Blo 455782 1028195 := bstep (se 1 (by rfl) ⟨771146, by rfl⟩ : syracuseStep 1028195 = 1542293) B1542293
theorem B2470115 : Blo 455782 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B1159505 : Blo 455782 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B1028465 : Blo 455782 1028465 := bstep (se 2 (by rfl) ⟨385674, by rfl⟩ : syracuseStep 1028465 = 771349) B771349
theorem B1028483 : Blo 455782 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B1159555 : Blo 455782 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B2470285 : Blo 455782 2470285 := bstep (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) B926357
theorem B6238691 : Blo 455782 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B2503181 : Blo 455782 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B1159697 : Blo 455782 1159697 := bstep (se 2 (by rfl) ⟨434886, by rfl⟩ : syracuseStep 1159697 = 869773) B869773
theorem B1028753 : Blo 455782 1028753 := bstep (se 2 (by rfl) ⟨385782, by rfl⟩ : syracuseStep 1028753 = 771565) B771565
theorem B1028771 : Blo 455782 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B44970773 : Blo 455782 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B3486563 : Blo 455782 3486563 := bstep (se 1 (by rfl) ⟨2614922, by rfl⟩ : syracuseStep 3486563 = 5229845) B5229845
theorem B1029041 : Blo 455782 1029041 := bstep (se 2 (by rfl) ⟨385890, by rfl⟩ : syracuseStep 1029041 = 771781) B771781
theorem B1029059 : Blo 455782 1029059 := bstep (se 1 (by rfl) ⟨771794, by rfl⟩ : syracuseStep 1029059 = 1543589) B1543589
theorem B734179 : Blo 455782 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B865475 : Blo 455782 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B1029329 : Blo 455782 1029329 := bstep (se 2 (by rfl) ⟨385998, by rfl⟩ : syracuseStep 1029329 = 771997) B771997
theorem B734417 : Blo 455782 734417 := bstep (se 2 (by rfl) ⟨275406, by rfl⟩ : syracuseStep 734417 = 550813) B550813
theorem B1029347 : Blo 455782 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B16954595 : Blo 455782 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B2635085 : Blo 455782 2635085 := bstep (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) B988157
theorem B734627 : Blo 455782 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B1390061 : Blo 455782 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B1029617 : Blo 455782 1029617 := bstep (se 2 (by rfl) ⟨386106, by rfl⟩ : syracuseStep 1029617 = 772213) B772213
theorem B1160689 : Blo 455782 1160689 := bstep (se 2 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 1160689 = 870517) B870517
theorem B2209265 : Blo 455782 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B1029635 : Blo 455782 1029635 := bstep (se 1 (by rfl) ⟨772226, by rfl⟩ : syracuseStep 1029635 = 1544453) B1544453
theorem B1947149 : Blo 455782 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B1160963 : Blo 455782 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1029905 : Blo 455782 1029905 := bstep (se 2 (by rfl) ⟨386214, by rfl⟩ : syracuseStep 1029905 = 772429) B772429
theorem B1029923 : Blo 455782 1029923 := bstep (se 1 (by rfl) ⟨772442, by rfl⟩ : syracuseStep 1029923 = 1544885) B1544885
theorem B1161155 : Blo 455782 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B1030193 : Blo 455782 1030193 := bstep (se 2 (by rfl) ⟨386322, by rfl⟩ : syracuseStep 1030193 = 772645) B772645
theorem B866371 : Blo 455782 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B1030211 : Blo 455782 1030211 := bstep (se 1 (by rfl) ⟨772658, by rfl⟩ : syracuseStep 1030211 = 1545317) B1545317
theorem B735409 : Blo 455782 735409 := bstep (se 2 (by rfl) ⟨275778, by rfl⟩ : syracuseStep 735409 = 551557) B551557
theorem B866531 : Blo 455782 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B2308337 : Blo 455782 2308337 := bstep (se 2 (by rfl) ⟨865626, by rfl⟩ : syracuseStep 2308337 = 1731253) B1731253
theorem B4962545 : Blo 455782 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B2079053 : Blo 455782 2079053 := bstep (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) B779645
theorem B1030481 : Blo 455782 1030481 := bstep (se 2 (by rfl) ⟨386430, by rfl⟩ : syracuseStep 1030481 = 772861) B772861
theorem B1030499 : Blo 455782 1030499 := bstep (se 1 (by rfl) ⟨772874, by rfl⟩ : syracuseStep 1030499 = 1545749) B1545749
theorem B2603441 : Blo 455782 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B1030769 : Blo 455782 1030769 := bstep (se 2 (by rfl) ⟨386538, by rfl⟩ : syracuseStep 1030769 = 773077) B773077
theorem B703091 : Blo 455782 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B1030787 : Blo 455782 1030787 := bstep (se 1 (by rfl) ⟨773090, by rfl⟩ : syracuseStep 1030787 = 1546181) B1546181
theorem B1653475 : Blo 455782 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B1162097 : Blo 455782 1162097 := bstep (se 2 (by rfl) ⟨435786, by rfl⟩ : syracuseStep 1162097 = 871573) B871573
theorem B1031057 : Blo 455782 1031057 := bstep (se 2 (by rfl) ⟨386646, by rfl⟩ : syracuseStep 1031057 = 773293) B773293
theorem B1031075 : Blo 455782 1031075 := bstep (se 1 (by rfl) ⟨773306, by rfl⟩ : syracuseStep 1031075 = 1546613) B1546613
theorem B1162147 : Blo 455782 1162147 := bstep (se 1 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 1162147 = 1743221) B1743221
theorem B736211 : Blo 455782 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B1162289 : Blo 455782 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B769169 : Blo 455782 769169 := bstep (se 2 (by rfl) ⟨288438, by rfl⟩ : syracuseStep 769169 = 576877) B576877
theorem B1031345 : Blo 455782 1031345 := bstep (se 2 (by rfl) ⟨386754, by rfl⟩ : syracuseStep 1031345 = 773509) B773509
theorem B1031363 : Blo 455782 1031363 := bstep (se 1 (by rfl) ⟨773522, by rfl⟩ : syracuseStep 1031363 = 1547045) B1547045
theorem B769297 : Blo 455782 769297 := bstep (se 2 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 769297 = 576973) B576973
theorem B867601 : Blo 455782 867601 := bstep (se 2 (by rfl) ⟨325350, by rfl⟩ : syracuseStep 867601 = 650701) B650701
theorem B769331 : Blo 455782 769331 := bstep (se 1 (by rfl) ⟨576998, by rfl⟩ : syracuseStep 769331 = 1153997) B1153997
theorem B769459 : Blo 455782 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B1031633 : Blo 455782 1031633 := bstep (se 2 (by rfl) ⟨386862, by rfl⟩ : syracuseStep 1031633 = 773725) B773725
theorem B835043 : Blo 455782 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B1031651 : Blo 455782 1031651 := bstep (se 1 (by rfl) ⟨773738, by rfl⟩ : syracuseStep 1031651 = 1547477) B1547477
theorem B769601 : Blo 455782 769601 := bstep (se 2 (by rfl) ⟨288600, by rfl⟩ : syracuseStep 769601 = 577201) B577201
theorem B2932357 : Blo 455782 2932357 := bstep (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) B549817
theorem B2309795 : Blo 455782 2309795 := bstep (se 1 (by rfl) ⟨1732346, by rfl⟩ : syracuseStep 2309795 = 3464693) B3464693
theorem B769729 : Blo 455782 769729 := bstep (se 2 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 769729 = 577297) B577297
theorem B769763 : Blo 455782 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B1031921 : Blo 455782 1031921 := bstep (se 2 (by rfl) ⟨386970, by rfl⟩ : syracuseStep 1031921 = 773941) B773941
theorem B1031939 : Blo 455782 1031939 := bstep (se 1 (by rfl) ⟨773954, by rfl⟩ : syracuseStep 1031939 = 1547909) B1547909
theorem B769891 : Blo 455782 769891 := bstep (se 1 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 769891 = 1154837) B1154837
theorem B2604899 : Blo 455782 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B1097635 : Blo 455782 1097635 := bstep (se 1 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 1097635 = 1646453) B1646453
theorem B770033 : Blo 455782 770033 := bstep (se 2 (by rfl) ⟨288762, by rfl⟩ : syracuseStep 770033 = 577525) B577525
theorem B1294321 : Blo 455782 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B1032209 : Blo 455782 1032209 := bstep (se 2 (by rfl) ⟨387078, by rfl⟩ : syracuseStep 1032209 = 774157) B774157
theorem B1163281 : Blo 455782 1163281 := bstep (se 2 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 1163281 = 872461) B872461
theorem B1032227 : Blo 455782 1032227 := bstep (se 1 (by rfl) ⟨774170, by rfl⟩ : syracuseStep 1032227 = 1548341) B1548341
theorem B1392689 : Blo 455782 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B770161 : Blo 455782 770161 := bstep (se 2 (by rfl) ⟨288810, by rfl⟩ : syracuseStep 770161 = 577621) B577621
theorem B1392785 : Blo 455782 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B770195 : Blo 455782 770195 := bstep (se 1 (by rfl) ⟨577646, by rfl⟩ : syracuseStep 770195 = 1155293) B1155293
theorem B770323 : Blo 455782 770323 := bstep (se 1 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 770323 = 1155485) B1155485
theorem B1163555 : Blo 455782 1163555 := bstep (se 1 (by rfl) ⟨872666, by rfl⟩ : syracuseStep 1163555 = 1745333) B1745333
theorem B868657 : Blo 455782 868657 := bstep (se 2 (by rfl) ⟨325746, by rfl⟩ : syracuseStep 868657 = 651493) B651493
theorem B1032497 : Blo 455782 1032497 := bstep (se 2 (by rfl) ⟨387186, by rfl⟩ : syracuseStep 1032497 = 774373) B774373
theorem B1032515 : Blo 455782 1032515 := bstep (se 1 (by rfl) ⟨774386, by rfl⟩ : syracuseStep 1032515 = 1548773) B1548773
theorem B770465 : Blo 455782 770465 := bstep (se 2 (by rfl) ⟨288924, by rfl⟩ : syracuseStep 770465 = 577849) B577849
theorem B2310605 : Blo 455782 2310605 := bstep (se 3 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 2310605 = 866477) B866477
theorem B2113997 : Blo 455782 2113997 := bstep (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) B792749
theorem B1098193 : Blo 455782 1098193 := bstep (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) B823645
theorem B1163747 : Blo 455782 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B770593 : Blo 455782 770593 := bstep (se 2 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 770593 = 577945) B577945
theorem B1950257 : Blo 455782 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B3129905 : Blo 455782 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B770627 : Blo 455782 770627 := bstep (se 1 (by rfl) ⟨577970, by rfl⟩ : syracuseStep 770627 = 1155941) B1155941
theorem B1032785 : Blo 455782 1032785 := bstep (se 2 (by rfl) ⟨387294, by rfl⟩ : syracuseStep 1032785 = 774589) B774589
theorem B1032803 : Blo 455782 1032803 := bstep (se 1 (by rfl) ⟨774602, by rfl⟩ : syracuseStep 1032803 = 1549205) B1549205
theorem B770755 : Blo 455782 770755 := bstep (se 1 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 770755 = 1156133) B1156133
theorem B869059 : Blo 455782 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B869105 : Blo 455782 869105 := bstep (se 2 (by rfl) ⟨325914, by rfl⟩ : syracuseStep 869105 = 651829) B651829
theorem B770897 : Blo 455782 770897 := bstep (se 2 (by rfl) ⟨289086, by rfl⟩ : syracuseStep 770897 = 578173) B578173
theorem B1033073 : Blo 455782 1033073 := bstep (se 2 (by rfl) ⟨387402, by rfl⟩ : syracuseStep 1033073 = 774805) B774805
theorem B1033091 : Blo 455782 1033091 := bstep (se 1 (by rfl) ⟨774818, by rfl⟩ : syracuseStep 1033091 = 1549637) B1549637
theorem B771025 : Blo 455782 771025 := bstep (se 2 (by rfl) ⟨289134, by rfl⟩ : syracuseStep 771025 = 578269) B578269
theorem B771059 : Blo 455782 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B869393 : Blo 455782 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B1098865 : Blo 455782 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B771187 : Blo 455782 771187 := bstep (se 1 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 771187 = 1156781) B1156781
theorem B1033361 : Blo 455782 1033361 := bstep (se 2 (by rfl) ⟨387510, by rfl⟩ : syracuseStep 1033361 = 775021) B775021
theorem B1033379 : Blo 455782 1033379 := bstep (se 1 (by rfl) ⟨775034, by rfl⟩ : syracuseStep 1033379 = 1550069) B1550069
theorem B1950925 : Blo 455782 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B771329 : Blo 455782 771329 := bstep (se 2 (by rfl) ⟨289248, by rfl⟩ : syracuseStep 771329 = 578497) B578497
theorem B5850467 : Blo 455782 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B771457 : Blo 455782 771457 := bstep (se 2 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 771457 = 578593) B578593
theorem B771491 : Blo 455782 771491 := bstep (se 1 (by rfl) ⟨578618, by rfl⟩ : syracuseStep 771491 = 1157237) B1157237
theorem B1033649 : Blo 455782 1033649 := bstep (se 2 (by rfl) ⟨387618, by rfl⟩ : syracuseStep 1033649 = 775237) B775237
theorem B1033667 : Blo 455782 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B771619 : Blo 455782 771619 := bstep (se 1 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 771619 = 1157429) B1157429
theorem B771761 : Blo 455782 771761 := bstep (se 2 (by rfl) ⟨289410, by rfl⟩ : syracuseStep 771761 = 578821) B578821
theorem B1033937 : Blo 455782 1033937 := bstep (se 2 (by rfl) ⟨387726, by rfl⟩ : syracuseStep 1033937 = 775453) B775453
theorem B870115 : Blo 455782 870115 := bstep (se 1 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 870115 = 1305173) B1305173
theorem B1033955 : Blo 455782 1033955 := bstep (se 1 (by rfl) ⟨775466, by rfl⟩ : syracuseStep 1033955 = 1550933) B1550933
theorem B1951523 : Blo 455782 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B771889 : Blo 455782 771889 := bstep (se 2 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 771889 = 578917) B578917
theorem B771923 : Blo 455782 771923 := bstep (se 1 (by rfl) ⟨578942, by rfl⟩ : syracuseStep 771923 = 1157885) B1157885
theorem B5228387 : Blo 455782 5228387 := bstep (se 1 (by rfl) ⟨3921290, by rfl⟩ : syracuseStep 5228387 = 7842581) B7842581
theorem B2344909 : Blo 455782 2344909 := bstep (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) B879341
theorem B772051 : Blo 455782 772051 := bstep (se 1 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 772051 = 1158077) B1158077
theorem B1034225 : Blo 455782 1034225 := bstep (se 2 (by rfl) ⟨387834, by rfl⟩ : syracuseStep 1034225 = 775669) B775669
theorem B1034243 : Blo 455782 1034243 := bstep (se 1 (by rfl) ⟨775682, by rfl⟩ : syracuseStep 1034243 = 1551365) B1551365
theorem B772193 : Blo 455782 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B870563 : Blo 455782 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B772321 : Blo 455782 772321 := bstep (se 2 (by rfl) ⟨289620, by rfl⟩ : syracuseStep 772321 = 579241) B579241
theorem B706801 : Blo 455782 706801 := bstep (se 2 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 706801 = 530101) B530101
theorem B772355 : Blo 455782 772355 := bstep (se 1 (by rfl) ⟨579266, by rfl⟩ : syracuseStep 772355 = 1158533) B1158533
theorem B2935075 : Blo 455782 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B772483 : Blo 455782 772483 := bstep (se 1 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 772483 = 1158725) B1158725
theorem B870851 : Blo 455782 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B1395181 : Blo 455782 1395181 := bstep (se 3 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 1395181 = 523193) B523193
theorem B772625 : Blo 455782 772625 := bstep (se 2 (by rfl) ⟨289734, by rfl⟩ : syracuseStep 772625 = 579469) B579469
theorem B772753 : Blo 455782 772753 := bstep (se 2 (by rfl) ⟨289782, by rfl⟩ : syracuseStep 772753 = 579565) B579565
theorem B772787 : Blo 455782 772787 := bstep (se 1 (by rfl) ⟨579590, by rfl⟩ : syracuseStep 772787 = 1159181) B1159181
theorem B772915 : Blo 455782 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B773057 : Blo 455782 773057 := bstep (se 2 (by rfl) ⟨289896, by rfl⟩ : syracuseStep 773057 = 579793) B579793
theorem B773185 : Blo 455782 773185 := bstep (se 2 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 773185 = 579889) B579889
theorem B773219 : Blo 455782 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B1461361 : Blo 455782 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B740497 : Blo 455782 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B3296483 : Blo 455782 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B773347 : Blo 455782 773347 := bstep (se 1 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 773347 = 1160021) B1160021
theorem B2313521 : Blo 455782 2313521 := bstep (se 2 (by rfl) ⟨867570, by rfl⟩ : syracuseStep 2313521 = 1735141) B1735141
theorem B773489 : Blo 455782 773489 := bstep (se 2 (by rfl) ⟨290058, by rfl⟩ : syracuseStep 773489 = 580117) B580117
theorem B871793 : Blo 455782 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B773617 : Blo 455782 773617 := bstep (se 2 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 773617 = 580213) B580213
theorem B773651 : Blo 455782 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B740963 : Blo 455782 740963 := bstep (se 1 (by rfl) ⟨555722, by rfl⟩ : syracuseStep 740963 = 1111445) B1111445
theorem B1298065 : Blo 455782 1298065 := bstep (se 2 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 1298065 = 973549) B973549
theorem B773779 : Blo 455782 773779 := bstep (se 1 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 773779 = 1160669) B1160669
theorem B1756835 : Blo 455782 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B773921 : Blo 455782 773921 := bstep (se 2 (by rfl) ⟨290220, by rfl⟩ : syracuseStep 773921 = 580441) B580441
theorem B577363 : Blo 455782 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B2084707 : Blo 455782 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B774049 : Blo 455782 774049 := bstep (se 2 (by rfl) ⟨290268, by rfl⟩ : syracuseStep 774049 = 580537) B580537
theorem B1298339 : Blo 455782 1298339 := bstep (se 1 (by rfl) ⟨973754, by rfl⟩ : syracuseStep 1298339 = 1947509) B1947509
theorem B1560493 : Blo 455782 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B577459 : Blo 455782 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B774083 : Blo 455782 774083 := bstep (se 1 (by rfl) ⟨580562, by rfl⟩ : syracuseStep 774083 = 1161125) B1161125
theorem B774211 : Blo 455782 774211 := bstep (se 1 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 774211 = 1161317) B1161317
theorem B1298531 : Blo 455782 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B5656675 : Blo 455782 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B774353 : Blo 455782 774353 := bstep (se 2 (by rfl) ⟨290382, by rfl⟩ : syracuseStep 774353 = 580765) B580765
theorem B2937073 : Blo 455782 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B872689 : Blo 455782 872689 := bstep (se 2 (by rfl) ⟨327258, by rfl⟩ : syracuseStep 872689 = 654517) B654517
theorem B3920197 : Blo 455782 3920197 := bstep (se 4 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 3920197 = 735037) B735037
theorem B774481 : Blo 455782 774481 := bstep (se 2 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 774481 = 580861) B580861
theorem B774515 : Blo 455782 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B1102211 : Blo 455782 1102211 := bstep (se 1 (by rfl) ⟨826658, by rfl⟩ : syracuseStep 1102211 = 1653317) B1653317
theorem B872849 : Blo 455782 872849 := bstep (se 2 (by rfl) ⟨327318, by rfl⟩ : syracuseStep 872849 = 654637) B654637
theorem B577955 : Blo 455782 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B774643 : Blo 455782 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B1397297 : Blo 455782 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B1102403 : Blo 455782 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B774785 : Blo 455782 774785 := bstep (se 2 (by rfl) ⟨290544, by rfl⟩ : syracuseStep 774785 = 581089) B581089
theorem B1102499 : Blo 455782 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B2314979 : Blo 455782 2314979 := bstep (se 1 (by rfl) ⟨1736234, by rfl⟩ : syracuseStep 2314979 = 3472469) B3472469
theorem B774913 : Blo 455782 774913 := bstep (se 2 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 774913 = 581185) B581185
theorem B774947 : Blo 455782 774947 := bstep (se 1 (by rfl) ⟨581210, by rfl⟩ : syracuseStep 774947 = 1162421) B1162421
theorem B512851 : Blo 455782 512851 := bstep (se 1 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 512851 = 769277) B769277
theorem B1299341 : Blo 455782 1299341 := bstep (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) B487253
theorem B775075 : Blo 455782 775075 := bstep (se 1 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 775075 = 1162613) B1162613
theorem B512995 : Blo 455782 512995 := bstep (se 1 (by rfl) ⟨384746, by rfl⟩ : syracuseStep 512995 = 769493) B769493
theorem B1463309 : Blo 455782 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B775217 : Blo 455782 775217 := bstep (se 2 (by rfl) ⟨290706, by rfl⟩ : syracuseStep 775217 = 581413) B581413
theorem B1299523 : Blo 455782 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B578659 : Blo 455782 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B513139 : Blo 455782 513139 := bstep (se 1 (by rfl) ⟨384854, by rfl⟩ : syracuseStep 513139 = 769709) B769709
theorem B1463437 : Blo 455782 1463437 := bstep (se 3 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 1463437 = 548789) B548789
theorem B775345 : Blo 455782 775345 := bstep (se 2 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 775345 = 581509) B581509
theorem B578755 : Blo 455782 578755 := bstep (se 1 (by rfl) ⟨434066, by rfl⟩ : syracuseStep 578755 = 868133) B868133
theorem B775379 : Blo 455782 775379 := bstep (se 1 (by rfl) ⟨581534, by rfl⟩ : syracuseStep 775379 = 1163069) B1163069
theorem B513283 : Blo 455782 513283 := bstep (se 1 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 513283 = 769925) B769925
theorem B775507 : Blo 455782 775507 := bstep (se 1 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 775507 = 1163261) B1163261
theorem B513427 : Blo 455782 513427 := bstep (se 1 (by rfl) ⟨385070, by rfl⟩ : syracuseStep 513427 = 770141) B770141
theorem B775649 : Blo 455782 775649 := bstep (se 2 (by rfl) ⟨290868, by rfl⟩ : syracuseStep 775649 = 581737) B581737
theorem B1955299 : Blo 455782 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B2315789 : Blo 455782 2315789 := bstep (se 3 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 2315789 = 868421) B868421
theorem B513571 : Blo 455782 513571 := bstep (se 1 (by rfl) ⟨385178, by rfl⟩ : syracuseStep 513571 = 770357) B770357
theorem B1300013 : Blo 455782 1300013 := bstep (se 3 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 1300013 = 487505) B487505
theorem B775777 : Blo 455782 775777 := bstep (se 2 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 775777 = 581833) B581833
theorem B775811 : Blo 455782 775811 := bstep (se 1 (by rfl) ⟨581858, by rfl⟩ : syracuseStep 775811 = 1163717) B1163717
theorem B513715 : Blo 455782 513715 := bstep (se 1 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 513715 = 770573) B770573
theorem B579251 : Blo 455782 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B513859 : Blo 455782 513859 := bstep (se 1 (by rfl) ⟨385394, by rfl⟩ : syracuseStep 513859 = 770789) B770789
theorem B514003 : Blo 455782 514003 := bstep (se 1 (by rfl) ⟨385502, by rfl⟩ : syracuseStep 514003 = 771005) B771005
theorem B514147 : Blo 455782 514147 := bstep (se 1 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 514147 = 771221) B771221
theorem B3528845 : Blo 455782 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B12572813 : Blo 455782 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B3725509 : Blo 455782 3725509 := bstep (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) B698533
theorem B514291 : Blo 455782 514291 := bstep (se 1 (by rfl) ⟨385718, by rfl⟩ : syracuseStep 514291 = 771437) B771437
theorem B2480453 : Blo 455782 2480453 := bstep (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) B465085
theorem B579955 : Blo 455782 579955 := bstep (se 1 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 579955 = 869933) B869933
theorem B514435 : Blo 455782 514435 := bstep (se 1 (by rfl) ⟨385826, by rfl⟩ : syracuseStep 514435 = 771653) B771653
theorem B580051 : Blo 455782 580051 := bstep (se 1 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 580051 = 870077) B870077
theorem B5888497 : Blo 455782 5888497 := bstep (se 2 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 5888497 = 4416373) B4416373
theorem B1104401 : Blo 455782 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B514579 : Blo 455782 514579 := bstep (se 1 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 514579 = 771869) B771869
theorem B1235533 : Blo 455782 1235533 := bstep (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) B463325
theorem B514723 : Blo 455782 514723 := bstep (se 1 (by rfl) ⟨386042, by rfl⟩ : syracuseStep 514723 = 772085) B772085
theorem B1301197 : Blo 455782 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B514867 : Blo 455782 514867 := bstep (se 1 (by rfl) ⟨386150, by rfl⟩ : syracuseStep 514867 = 772301) B772301
theorem B7035761 : Blo 455782 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1465283 : Blo 455782 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B515011 : Blo 455782 515011 := bstep (se 1 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 515011 = 772517) B772517
theorem B580547 : Blo 455782 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B1465411 : Blo 455782 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B515155 : Blo 455782 515155 := bstep (se 1 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 515155 = 772733) B772733
theorem B1465553 : Blo 455782 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B515299 : Blo 455782 515299 := bstep (se 1 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 515299 = 772949) B772949
theorem B548083 : Blo 455782 548083 := bstep (se 1 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 548083 = 822125) B822125
theorem B1465667 : Blo 455782 1465667 := bstep (se 1 (by rfl) ⟨1099250, by rfl⟩ : syracuseStep 1465667 = 2198501) B2198501
theorem B515443 : Blo 455782 515443 := bstep (se 1 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 515443 = 773165) B773165
theorem B3300749 : Blo 455782 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B2088355 : Blo 455782 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1236397 : Blo 455782 1236397 := bstep (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) B463649
theorem B1957297 : Blo 455782 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B515587 : Blo 455782 515587 := bstep (se 1 (by rfl) ⟨386690, by rfl⟩ : syracuseStep 515587 = 773381) B773381
theorem B581251 : Blo 455782 581251 := bstep (se 1 (by rfl) ⟨435938, by rfl⟩ : syracuseStep 581251 = 871877) B871877
theorem B515731 : Blo 455782 515731 := bstep (se 1 (by rfl) ⟨386798, by rfl⟩ : syracuseStep 515731 = 773597) B773597
theorem B2088611 : Blo 455782 2088611 := bstep (se 1 (by rfl) ⟨1566458, by rfl⟩ : syracuseStep 2088611 = 3132917) B3132917
theorem B974531 : Blo 455782 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B581347 : Blo 455782 581347 := bstep (se 1 (by rfl) ⟨436010, by rfl⟩ : syracuseStep 581347 = 872021) B872021
theorem B1302257 : Blo 455782 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B745249 : Blo 455782 745249 := bstep (se 2 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 745249 = 558937) B558937
theorem B515875 : Blo 455782 515875 := bstep (se 1 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 515875 = 773813) B773813
theorem B745379 : Blo 455782 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B516019 : Blo 455782 516019 := bstep (se 1 (by rfl) ⟨387014, by rfl⟩ : syracuseStep 516019 = 774029) B774029
theorem B516163 : Blo 455782 516163 := bstep (se 1 (by rfl) ⟨387122, by rfl⟩ : syracuseStep 516163 = 774245) B774245
theorem B712883 : Blo 455782 712883 := bstep (se 1 (by rfl) ⟨534662, by rfl⟩ : syracuseStep 712883 = 1069325) B1069325
theorem B516307 : Blo 455782 516307 := bstep (se 1 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 516307 = 774461) B774461
theorem B581843 : Blo 455782 581843 := bstep (se 1 (by rfl) ⟨436382, by rfl⟩ : syracuseStep 581843 = 872765) B872765
theorem B2482481 : Blo 455782 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B516451 : Blo 455782 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B2318705 : Blo 455782 2318705 := bstep (se 2 (by rfl) ⟨869514, by rfl⟩ : syracuseStep 2318705 = 1739029) B1739029
theorem B1302929 : Blo 455782 1302929 := bstep (se 2 (by rfl) ⟨488598, by rfl⟩ : syracuseStep 1302929 = 977197) B977197
theorem B516595 : Blo 455782 516595 := bstep (se 1 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 516595 = 774893) B774893
theorem B4186637 : Blo 455782 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B1204753 : Blo 455782 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B746003 : Blo 455782 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B975395 : Blo 455782 975395 := bstep (se 1 (by rfl) ⟨731546, by rfl⟩ : syracuseStep 975395 = 1463093) B1463093
theorem B2613829 : Blo 455782 2613829 := bstep (se 4 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 2613829 = 490093) B490093
theorem B746081 : Blo 455782 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B516739 : Blo 455782 516739 := bstep (se 1 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 516739 = 775109) B775109
theorem B975505 : Blo 455782 975505 := bstep (se 2 (by rfl) ⟨365814, by rfl⟩ : syracuseStep 975505 = 731629) B731629
theorem B516883 : Blo 455782 516883 := bstep (se 1 (by rfl) ⟨387662, by rfl⟩ : syracuseStep 516883 = 775325) B775325
theorem B517027 : Blo 455782 517027 := bstep (se 1 (by rfl) ⟨387770, by rfl⟩ : syracuseStep 517027 = 775541) B775541
theorem B1172465 : Blo 455782 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B549875 : Blo 455782 549875 := bstep (se 1 (by rfl) ⟨412406, by rfl⟩ : syracuseStep 549875 = 824813) B824813
theorem B1467409 : Blo 455782 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B517171 : Blo 455782 517171 := bstep (se 1 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 517171 = 775757) B775757
theorem B1303715 : Blo 455782 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B3466637 : Blo 455782 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B2942405 : Blo 455782 2942405 := bstep (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) B551701
theorem B1861069 : Blo 455782 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B1304045 : Blo 455782 1304045 := bstep (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) B489017
theorem B1304113 : Blo 455782 1304113 := bstep (se 2 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 1304113 = 978085) B978085
theorem B1238723 : Blo 455782 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B616177 : Blo 455782 616177 := bstep (se 2 (by rfl) ⟨231066, by rfl⟩ : syracuseStep 616177 = 462133) B462133
theorem B2320163 : Blo 455782 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B1304387 : Blo 455782 1304387 := bstep (se 1 (by rfl) ⟨978290, by rfl⟩ : syracuseStep 1304387 = 1956581) B1956581
theorem B616307 : Blo 455782 616307 := bstep (se 1 (by rfl) ⟨462230, by rfl⟩ : syracuseStep 616307 = 924461) B924461
theorem B1173521 : Blo 455782 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B1468525 : Blo 455782 1468525 := bstep (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) B550697
theorem B25389283 : Blo 455782 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B1665293 : Blo 455782 1665293 := bstep (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) B624485
theorem B649505 : Blo 455782 649505 := bstep (se 2 (by rfl) ⟨243564, by rfl⟩ : syracuseStep 649505 = 487129) B487129
theorem B2615813 : Blo 455782 2615813 := bstep (se 4 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 2615813 = 490465) B490465
theorem B2320973 : Blo 455782 2320973 := bstep (se 3 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 2320973 = 870365) B870365
theorem B977521 : Blo 455782 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B1305229 : Blo 455782 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B5073635 : Blo 455782 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1305389 : Blo 455782 1305389 := bstep (se 3 (by rfl) ⟨244760, by rfl⟩ : syracuseStep 1305389 = 489521) B489521
theorem B1239857 : Blo 455782 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B650035 : Blo 455782 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B1469357 : Blo 455782 1469357 := bstep (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) B551009
theorem B1305571 : Blo 455782 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B3697649 : Blo 455782 3697649 := bstep (se 2 (by rfl) ⟨1386618, by rfl⟩ : syracuseStep 3697649 = 2773237) B2773237
theorem B977923 : Blo 455782 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B2190349 : Blo 455782 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B650371 : Blo 455782 650371 := bstep (se 1 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 650371 = 975557) B975557
theorem B1731725 : Blo 455782 1731725 := bstep (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) B649397
theorem B3009869 : Blo 455782 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B1961329 : Blo 455782 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B2977357 : Blo 455782 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B683681 : Blo 455782 683681 := bstep (se 2 (by rfl) ⟨256380, by rfl⟩ : syracuseStep 683681 = 512761) B512761
theorem B650929 : Blo 455782 650929 := bstep (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) B488197
theorem B683699 : Blo 455782 683699 := bstep (se 1 (by rfl) ⟨512774, by rfl⟩ : syracuseStep 683699 = 1025549) B1025549
theorem B683729 : Blo 455782 683729 := bstep (se 2 (by rfl) ⟨256398, by rfl⟩ : syracuseStep 683729 = 512797) B512797
theorem B650963 : Blo 455782 650963 := bstep (se 1 (by rfl) ⟨488222, by rfl⟩ : syracuseStep 650963 = 976445) B976445
theorem B683747 : Blo 455782 683747 := bstep (se 1 (by rfl) ⟨512810, by rfl⟩ : syracuseStep 683747 = 1025621) B1025621
theorem B683777 : Blo 455782 683777 := bstep (se 2 (by rfl) ⟨256416, by rfl⟩ : syracuseStep 683777 = 512833) B512833
theorem B683795 : Blo 455782 683795 := bstep (se 1 (by rfl) ⟨512846, by rfl⟩ : syracuseStep 683795 = 1025693) B1025693
theorem B683825 : Blo 455782 683825 := bstep (se 2 (by rfl) ⟨256434, by rfl⟩ : syracuseStep 683825 = 512869) B512869
theorem B683843 : Blo 455782 683843 := bstep (se 1 (by rfl) ⟨512882, by rfl⟩ : syracuseStep 683843 = 1025765) B1025765
theorem B618323 : Blo 455782 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B683873 : Blo 455782 683873 := bstep (se 2 (by rfl) ⟨256452, by rfl⟩ : syracuseStep 683873 = 512905) B512905
theorem B683891 : Blo 455782 683891 := bstep (se 1 (by rfl) ⟨512918, by rfl⟩ : syracuseStep 683891 = 1025837) B1025837
theorem B2977669 : Blo 455782 2977669 := bstep (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) B558313
theorem B683921 : Blo 455782 683921 := bstep (se 2 (by rfl) ⟨256470, by rfl⟩ : syracuseStep 683921 = 512941) B512941
theorem B683939 : Blo 455782 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B1732529 : Blo 455782 1732529 := bstep (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) B1299397
theorem B683969 : Blo 455782 683969 := bstep (se 2 (by rfl) ⟨256488, by rfl⟩ : syracuseStep 683969 = 512977) B512977
theorem B683987 : Blo 455782 683987 := bstep (se 1 (by rfl) ⟨512990, by rfl⟩ : syracuseStep 683987 = 1025981) B1025981
theorem B684017 : Blo 455782 684017 := bstep (se 2 (by rfl) ⟨256506, by rfl⟩ : syracuseStep 684017 = 513013) B513013
theorem B684035 : Blo 455782 684035 := bstep (se 1 (by rfl) ⟨513026, by rfl⟩ : syracuseStep 684035 = 1026053) B1026053
theorem B684065 : Blo 455782 684065 := bstep (se 2 (by rfl) ⟨256524, by rfl⟩ : syracuseStep 684065 = 513049) B513049
theorem B684083 : Blo 455782 684083 := bstep (se 1 (by rfl) ⟨513062, by rfl⟩ : syracuseStep 684083 = 1026125) B1026125
theorem B684113 : Blo 455782 684113 := bstep (se 2 (by rfl) ⟨256542, by rfl⟩ : syracuseStep 684113 = 513085) B513085
theorem B684131 : Blo 455782 684131 := bstep (se 1 (by rfl) ⟨513098, by rfl⟩ : syracuseStep 684131 = 1026197) B1026197
theorem B684161 : Blo 455782 684161 := bstep (se 2 (by rfl) ⟨256560, by rfl⟩ : syracuseStep 684161 = 513121) B513121
theorem B684179 : Blo 455782 684179 := bstep (se 1 (by rfl) ⟨513134, by rfl⟩ : syracuseStep 684179 = 1026269) B1026269
theorem B2977955 : Blo 455782 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B684209 : Blo 455782 684209 := bstep (se 2 (by rfl) ⟨256578, by rfl⟩ : syracuseStep 684209 = 513157) B513157
theorem B684227 : Blo 455782 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B684257 : Blo 455782 684257 := bstep (se 2 (by rfl) ⟨256596, by rfl⟩ : syracuseStep 684257 = 513193) B513193
theorem B3469553 : Blo 455782 3469553 := bstep (se 2 (by rfl) ⟨1301082, by rfl⟩ : syracuseStep 3469553 = 2602165) B2602165
theorem B684275 : Blo 455782 684275 := bstep (se 1 (by rfl) ⟨513206, by rfl⟩ : syracuseStep 684275 = 1026413) B1026413
theorem B487667 : Blo 455782 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B651521 : Blo 455782 651521 := bstep (se 2 (by rfl) ⟨244320, by rfl⟩ : syracuseStep 651521 = 488641) B488641
theorem B684305 : Blo 455782 684305 := bstep (se 2 (by rfl) ⟨256614, by rfl⟩ : syracuseStep 684305 = 513229) B513229
theorem B684323 : Blo 455782 684323 := bstep (se 1 (by rfl) ⟨513242, by rfl⟩ : syracuseStep 684323 = 1026485) B1026485
theorem B782627 : Blo 455782 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B684353 : Blo 455782 684353 := bstep (se 2 (by rfl) ⟨256632, by rfl⟩ : syracuseStep 684353 = 513265) B513265
theorem B651601 : Blo 455782 651601 := bstep (se 2 (by rfl) ⟨244350, by rfl⟩ : syracuseStep 651601 = 488701) B488701
theorem B1306961 : Blo 455782 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B684371 : Blo 455782 684371 := bstep (se 1 (by rfl) ⟨513278, by rfl⟩ : syracuseStep 684371 = 1026557) B1026557
theorem B684401 : Blo 455782 684401 := bstep (se 2 (by rfl) ⟨256650, by rfl⟩ : syracuseStep 684401 = 513301) B513301
theorem B684419 : Blo 455782 684419 := bstep (se 1 (by rfl) ⟨513314, by rfl⟩ : syracuseStep 684419 = 1026629) B1026629
theorem B684449 : Blo 455782 684449 := bstep (se 2 (by rfl) ⟨256668, by rfl⟩ : syracuseStep 684449 = 513337) B513337
theorem B684467 : Blo 455782 684467 := bstep (se 1 (by rfl) ⟨513350, by rfl⟩ : syracuseStep 684467 = 1026701) B1026701
theorem B684497 : Blo 455782 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B684515 : Blo 455782 684515 := bstep (se 1 (by rfl) ⟨513386, by rfl⟩ : syracuseStep 684515 = 1026773) B1026773
theorem B979427 : Blo 455782 979427 := bstep (se 1 (by rfl) ⟨734570, by rfl⟩ : syracuseStep 979427 = 1469141) B1469141
theorem B684545 : Blo 455782 684545 := bstep (se 2 (by rfl) ⟨256704, by rfl⟩ : syracuseStep 684545 = 513409) B513409
theorem B684563 : Blo 455782 684563 := bstep (se 1 (by rfl) ⟨513422, by rfl⟩ : syracuseStep 684563 = 1026845) B1026845
theorem B684593 : Blo 455782 684593 := bstep (se 2 (by rfl) ⟨256722, by rfl⟩ : syracuseStep 684593 = 513445) B513445
theorem B684611 : Blo 455782 684611 := bstep (se 1 (by rfl) ⟨513458, by rfl⟩ : syracuseStep 684611 = 1026917) B1026917
theorem B1733197 : Blo 455782 1733197 := bstep (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) B649949
theorem B684641 : Blo 455782 684641 := bstep (se 2 (by rfl) ⟨256740, by rfl⟩ : syracuseStep 684641 = 513481) B513481
theorem B684659 : Blo 455782 684659 := bstep (se 1 (by rfl) ⟨513494, by rfl⟩ : syracuseStep 684659 = 1026989) B1026989
theorem B684689 : Blo 455782 684689 := bstep (se 2 (by rfl) ⟨256758, by rfl⟩ : syracuseStep 684689 = 513517) B513517
theorem B684707 : Blo 455782 684707 := bstep (se 1 (by rfl) ⟨513530, by rfl⟩ : syracuseStep 684707 = 1027061) B1027061
theorem B684737 : Blo 455782 684737 := bstep (se 2 (by rfl) ⟨256776, by rfl⟩ : syracuseStep 684737 = 513553) B513553
theorem B3764933 : Blo 455782 3764933 := bstep (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) B705925
theorem B684755 : Blo 455782 684755 := bstep (se 1 (by rfl) ⟨513566, by rfl⟩ : syracuseStep 684755 = 1027133) B1027133
theorem B1045219 : Blo 455782 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B684785 : Blo 455782 684785 := bstep (se 2 (by rfl) ⟨256794, by rfl⟩ : syracuseStep 684785 = 513589) B513589
theorem B684803 : Blo 455782 684803 := bstep (se 1 (by rfl) ⟨513602, by rfl⟩ : syracuseStep 684803 = 1027205) B1027205
theorem B684833 : Blo 455782 684833 := bstep (se 2 (by rfl) ⟨256812, by rfl⟩ : syracuseStep 684833 = 513625) B513625
theorem B684851 : Blo 455782 684851 := bstep (se 1 (by rfl) ⟨513638, by rfl⟩ : syracuseStep 684851 = 1027277) B1027277
theorem B684881 : Blo 455782 684881 := bstep (se 2 (by rfl) ⟨256830, by rfl⟩ : syracuseStep 684881 = 513661) B513661
theorem B684899 : Blo 455782 684899 := bstep (se 1 (by rfl) ⟨513674, by rfl⟩ : syracuseStep 684899 = 1027349) B1027349
theorem B521059 : Blo 455782 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B684929 : Blo 455782 684929 := bstep (se 2 (by rfl) ⟨256848, by rfl⟩ : syracuseStep 684929 = 513697) B513697
theorem B684947 : Blo 455782 684947 := bstep (se 1 (by rfl) ⟨513710, by rfl⟩ : syracuseStep 684947 = 1027421) B1027421
theorem B684977 : Blo 455782 684977 := bstep (se 2 (by rfl) ⟨256866, by rfl⟩ : syracuseStep 684977 = 513733) B513733
theorem B684995 : Blo 455782 684995 := bstep (se 1 (by rfl) ⟨513746, by rfl⟩ : syracuseStep 684995 = 1027493) B1027493
theorem B685025 : Blo 455782 685025 := bstep (se 2 (by rfl) ⟨256884, by rfl⟩ : syracuseStep 685025 = 513769) B513769
theorem B1471459 : Blo 455782 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B685043 : Blo 455782 685043 := bstep (se 1 (by rfl) ⟨513782, by rfl⟩ : syracuseStep 685043 = 1027565) B1027565
theorem B685073 : Blo 455782 685073 := bstep (se 2 (by rfl) ⟨256902, by rfl⟩ : syracuseStep 685073 = 513805) B513805
theorem B685091 : Blo 455782 685091 := bstep (se 1 (by rfl) ⟨513818, by rfl⟩ : syracuseStep 685091 = 1027637) B1027637
theorem B685121 : Blo 455782 685121 := bstep (se 2 (by rfl) ⟨256920, by rfl⟩ : syracuseStep 685121 = 513841) B513841
theorem B685139 : Blo 455782 685139 := bstep (se 1 (by rfl) ⟨513854, by rfl⟩ : syracuseStep 685139 = 1027709) B1027709
theorem B652387 : Blo 455782 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B685169 : Blo 455782 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B1471601 : Blo 455782 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B455795 : Blo 455782 455795 := bstep (se 1 (by rfl) ⟨341846, by rfl⟩ : syracuseStep 455795 = 683693) B683693
theorem B455811 : Blo 455782 455811 := bstep (se 1 (by rfl) ⟨341858, by rfl⟩ : syracuseStep 455811 = 683717) B683717
theorem B685187 : Blo 455782 685187 := bstep (se 1 (by rfl) ⟨513890, by rfl⟩ : syracuseStep 685187 = 1027781) B1027781
theorem B455827 : Blo 455782 455827 := bstep (se 1 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 455827 = 683741) B683741
theorem B685217 : Blo 455782 685217 := bstep (se 2 (by rfl) ⟨256956, by rfl⟩ : syracuseStep 685217 = 513913) B513913
theorem B455843 : Blo 455782 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B455859 : Blo 455782 455859 := bstep (se 1 (by rfl) ⟨341894, by rfl⟩ : syracuseStep 455859 = 683789) B683789
theorem B685235 : Blo 455782 685235 := bstep (se 1 (by rfl) ⟨513926, by rfl⟩ : syracuseStep 685235 = 1027853) B1027853
theorem B455875 : Blo 455782 455875 := bstep (se 1 (by rfl) ⟨341906, by rfl⟩ : syracuseStep 455875 = 683813) B683813
theorem B685265 : Blo 455782 685265 := bstep (se 2 (by rfl) ⟨256974, by rfl⟩ : syracuseStep 685265 = 513949) B513949
theorem B455891 : Blo 455782 455891 := bstep (se 1 (by rfl) ⟨341918, by rfl⟩ : syracuseStep 455891 = 683837) B683837
theorem B455907 : Blo 455782 455907 := bstep (se 1 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 455907 = 683861) B683861
theorem B685283 : Blo 455782 685283 := bstep (se 1 (by rfl) ⟨513962, by rfl⟩ : syracuseStep 685283 = 1027925) B1027925
theorem B455923 : Blo 455782 455923 := bstep (se 1 (by rfl) ⟨341942, by rfl⟩ : syracuseStep 455923 = 683885) B683885
theorem B685313 : Blo 455782 685313 := bstep (se 2 (by rfl) ⟨256992, by rfl⟩ : syracuseStep 685313 = 513985) B513985
theorem B455939 : Blo 455782 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B1307917 : Blo 455782 1307917 := bstep (se 3 (by rfl) ⟨245234, by rfl⟩ : syracuseStep 1307917 = 490469) B490469
theorem B455955 : Blo 455782 455955 := bstep (se 1 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 455955 = 683933) B683933
theorem B685331 : Blo 455782 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B455971 : Blo 455782 455971 := bstep (se 1 (by rfl) ⟨341978, by rfl⟩ : syracuseStep 455971 = 683957) B683957
theorem B685361 : Blo 455782 685361 := bstep (se 2 (by rfl) ⟨257010, by rfl⟩ : syracuseStep 685361 = 514021) B514021
theorem B455987 : Blo 455782 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B456003 : Blo 455782 456003 := bstep (se 1 (by rfl) ⟨342002, by rfl⟩ : syracuseStep 456003 = 684005) B684005
theorem B685379 : Blo 455782 685379 := bstep (se 1 (by rfl) ⟨514034, by rfl⟩ : syracuseStep 685379 = 1028069) B1028069
theorem B456019 : Blo 455782 456019 := bstep (se 1 (by rfl) ⟨342014, by rfl⟩ : syracuseStep 456019 = 684029) B684029
theorem B685409 : Blo 455782 685409 := bstep (se 2 (by rfl) ⟨257028, by rfl⟩ : syracuseStep 685409 = 514057) B514057
theorem B456035 : Blo 455782 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B1733987 : Blo 455782 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B456051 : Blo 455782 456051 := bstep (se 1 (by rfl) ⟨342038, by rfl⟩ : syracuseStep 456051 = 684077) B684077
theorem B685427 : Blo 455782 685427 := bstep (se 1 (by rfl) ⟨514070, by rfl⟩ : syracuseStep 685427 = 1028141) B1028141
theorem B456067 : Blo 455782 456067 := bstep (se 1 (by rfl) ⟨342050, by rfl⟩ : syracuseStep 456067 = 684101) B684101
theorem B685457 : Blo 455782 685457 := bstep (se 2 (by rfl) ⟨257046, by rfl⟩ : syracuseStep 685457 = 514093) B514093
theorem B456083 : Blo 455782 456083 := bstep (se 1 (by rfl) ⟨342062, by rfl⟩ : syracuseStep 456083 = 684125) B684125
theorem B456099 : Blo 455782 456099 := bstep (se 1 (by rfl) ⟨342074, by rfl⟩ : syracuseStep 456099 = 684149) B684149
theorem B685475 : Blo 455782 685475 := bstep (se 1 (by rfl) ⟨514106, by rfl⟩ : syracuseStep 685475 = 1028213) B1028213
theorem B2323889 : Blo 455782 2323889 := bstep (se 2 (by rfl) ⟨871458, by rfl⟩ : syracuseStep 2323889 = 1742917) B1742917
theorem B456115 : Blo 455782 456115 := bstep (se 1 (by rfl) ⟨342086, by rfl⟩ : syracuseStep 456115 = 684173) B684173
theorem B685505 : Blo 455782 685505 := bstep (se 2 (by rfl) ⟨257064, by rfl⟩ : syracuseStep 685505 = 514129) B514129
theorem B456131 : Blo 455782 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B456147 : Blo 455782 456147 := bstep (se 1 (by rfl) ⟨342110, by rfl⟩ : syracuseStep 456147 = 684221) B684221
theorem B685523 : Blo 455782 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B456163 : Blo 455782 456163 := bstep (se 1 (by rfl) ⟨342122, by rfl⟩ : syracuseStep 456163 = 684245) B684245
theorem B685553 : Blo 455782 685553 := bstep (se 2 (by rfl) ⟨257082, by rfl⟩ : syracuseStep 685553 = 514165) B514165
theorem B1308145 : Blo 455782 1308145 := bstep (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) B981109
theorem B456179 : Blo 455782 456179 := bstep (se 1 (by rfl) ⟨342134, by rfl⟩ : syracuseStep 456179 = 684269) B684269
theorem B456195 : Blo 455782 456195 := bstep (se 1 (by rfl) ⟨342146, by rfl⟩ : syracuseStep 456195 = 684293) B684293
theorem B685571 : Blo 455782 685571 := bstep (se 1 (by rfl) ⟨514178, by rfl⟩ : syracuseStep 685571 = 1028357) B1028357
theorem B456211 : Blo 455782 456211 := bstep (se 1 (by rfl) ⟨342158, by rfl⟩ : syracuseStep 456211 = 684317) B684317
theorem B685601 : Blo 455782 685601 := bstep (se 2 (by rfl) ⟨257100, by rfl⟩ : syracuseStep 685601 = 514201) B514201
theorem B456227 : Blo 455782 456227 := bstep (se 1 (by rfl) ⟨342170, by rfl⟩ : syracuseStep 456227 = 684341) B684341
theorem B456243 : Blo 455782 456243 := bstep (se 1 (by rfl) ⟨342182, by rfl⟩ : syracuseStep 456243 = 684365) B684365
theorem B685619 : Blo 455782 685619 := bstep (se 1 (by rfl) ⟨514214, by rfl⟩ : syracuseStep 685619 = 1028429) B1028429
theorem B652865 : Blo 455782 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B456259 : Blo 455782 456259 := bstep (se 1 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 456259 = 684389) B684389
theorem B1111619 : Blo 455782 1111619 := bstep (se 1 (by rfl) ⟨833714, by rfl⟩ : syracuseStep 1111619 = 1667429) B1667429
theorem B685649 : Blo 455782 685649 := bstep (se 2 (by rfl) ⟨257118, by rfl⟩ : syracuseStep 685649 = 514237) B514237
theorem B456275 : Blo 455782 456275 := bstep (se 1 (by rfl) ⟨342206, by rfl⟩ : syracuseStep 456275 = 684413) B684413
theorem B456291 : Blo 455782 456291 := bstep (se 1 (by rfl) ⟨342218, by rfl⟩ : syracuseStep 456291 = 684437) B684437
theorem B685667 : Blo 455782 685667 := bstep (se 1 (by rfl) ⟨514250, by rfl⟩ : syracuseStep 685667 = 1028501) B1028501
theorem B456307 : Blo 455782 456307 := bstep (se 1 (by rfl) ⟨342230, by rfl⟩ : syracuseStep 456307 = 684461) B684461
theorem B685697 : Blo 455782 685697 := bstep (se 2 (by rfl) ⟨257136, by rfl⟩ : syracuseStep 685697 = 514273) B514273
theorem B456323 : Blo 455782 456323 := bstep (se 1 (by rfl) ⟨342242, by rfl⟩ : syracuseStep 456323 = 684485) B684485
theorem B1308305 : Blo 455782 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B456339 : Blo 455782 456339 := bstep (se 1 (by rfl) ⟨342254, by rfl⟩ : syracuseStep 456339 = 684509) B684509
theorem B685715 : Blo 455782 685715 := bstep (se 1 (by rfl) ⟨514286, by rfl⟩ : syracuseStep 685715 = 1028573) B1028573
theorem B456355 : Blo 455782 456355 := bstep (se 1 (by rfl) ⟨342266, by rfl⟩ : syracuseStep 456355 = 684533) B684533
theorem B1242797 : Blo 455782 1242797 := bstep (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) B466049
theorem B685745 : Blo 455782 685745 := bstep (se 2 (by rfl) ⟨257154, by rfl⟩ : syracuseStep 685745 = 514309) B514309
theorem B980657 : Blo 455782 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B456371 : Blo 455782 456371 := bstep (se 1 (by rfl) ⟨342278, by rfl⟩ : syracuseStep 456371 = 684557) B684557
theorem B652979 : Blo 455782 652979 := bstep (se 1 (by rfl) ⟨489734, by rfl⟩ : syracuseStep 652979 = 979469) B979469
theorem B456387 : Blo 455782 456387 := bstep (se 1 (by rfl) ⟨342290, by rfl⟩ : syracuseStep 456387 = 684581) B684581
theorem B685763 : Blo 455782 685763 := bstep (se 1 (by rfl) ⟨514322, by rfl⟩ : syracuseStep 685763 = 1028645) B1028645
theorem B620227 : Blo 455782 620227 := bstep (se 1 (by rfl) ⟨465170, by rfl⟩ : syracuseStep 620227 = 930341) B930341
theorem B456403 : Blo 455782 456403 := bstep (se 1 (by rfl) ⟨342302, by rfl⟩ : syracuseStep 456403 = 684605) B684605
theorem B685793 : Blo 455782 685793 := bstep (se 2 (by rfl) ⟨257172, by rfl⟩ : syracuseStep 685793 = 514345) B514345
theorem B456419 : Blo 455782 456419 := bstep (se 1 (by rfl) ⟨342314, by rfl⟩ : syracuseStep 456419 = 684629) B684629
theorem B1603309 : Blo 455782 1603309 := bstep (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) B601241
theorem B456435 : Blo 455782 456435 := bstep (se 1 (by rfl) ⟨342326, by rfl⟩ : syracuseStep 456435 = 684653) B684653
theorem B685811 : Blo 455782 685811 := bstep (se 1 (by rfl) ⟨514358, by rfl⟩ : syracuseStep 685811 = 1028717) B1028717
theorem B456451 : Blo 455782 456451 := bstep (se 1 (by rfl) ⟨342338, by rfl⟩ : syracuseStep 456451 = 684677) B684677
theorem B653059 : Blo 455782 653059 := bstep (se 1 (by rfl) ⟨489794, by rfl⟩ : syracuseStep 653059 = 979589) B979589
theorem B1308419 : Blo 455782 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B685841 : Blo 455782 685841 := bstep (se 2 (by rfl) ⟨257190, by rfl⟩ : syracuseStep 685841 = 514381) B514381
theorem B456467 : Blo 455782 456467 := bstep (se 1 (by rfl) ⟨342350, by rfl⟩ : syracuseStep 456467 = 684701) B684701
theorem B489235 : Blo 455782 489235 := bstep (se 1 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 489235 = 733853) B733853
theorem B456483 : Blo 455782 456483 := bstep (se 1 (by rfl) ⟨342362, by rfl⟩ : syracuseStep 456483 = 684725) B684725
theorem B685859 : Blo 455782 685859 := bstep (se 1 (by rfl) ⟨514394, by rfl⟩ : syracuseStep 685859 = 1028789) B1028789
theorem B456499 : Blo 455782 456499 := bstep (se 1 (by rfl) ⟨342374, by rfl⟩ : syracuseStep 456499 = 684749) B684749
theorem B685889 : Blo 455782 685889 := bstep (se 2 (by rfl) ⟨257208, by rfl⟩ : syracuseStep 685889 = 514417) B514417
theorem B456515 : Blo 455782 456515 := bstep (se 1 (by rfl) ⟨342386, by rfl⟩ : syracuseStep 456515 = 684773) B684773
theorem B456531 : Blo 455782 456531 := bstep (se 1 (by rfl) ⟨342398, by rfl⟩ : syracuseStep 456531 = 684797) B684797
theorem B685907 : Blo 455782 685907 := bstep (se 1 (by rfl) ⟨514430, by rfl⟩ : syracuseStep 685907 = 1028861) B1028861
theorem B456547 : Blo 455782 456547 := bstep (se 1 (by rfl) ⟨342410, by rfl⟩ : syracuseStep 456547 = 684821) B684821
theorem B685937 : Blo 455782 685937 := bstep (se 2 (by rfl) ⟨257226, by rfl⟩ : syracuseStep 685937 = 514453) B514453
theorem B456563 : Blo 455782 456563 := bstep (se 1 (by rfl) ⟨342422, by rfl⟩ : syracuseStep 456563 = 684845) B684845
theorem B456579 : Blo 455782 456579 := bstep (se 1 (by rfl) ⟨342434, by rfl⟩ : syracuseStep 456579 = 684869) B684869
theorem B685955 : Blo 455782 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B456595 : Blo 455782 456595 := bstep (se 1 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 456595 = 684893) B684893
theorem B685985 : Blo 455782 685985 := bstep (se 2 (by rfl) ⟨257244, by rfl⟩ : syracuseStep 685985 = 514489) B514489
theorem B456611 : Blo 455782 456611 := bstep (se 1 (by rfl) ⟨342458, by rfl⟩ : syracuseStep 456611 = 684917) B684917
theorem B456627 : Blo 455782 456627 := bstep (se 1 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 456627 = 684941) B684941
theorem B686003 : Blo 455782 686003 := bstep (se 1 (by rfl) ⟨514502, by rfl⟩ : syracuseStep 686003 = 1029005) B1029005
theorem B456643 : Blo 455782 456643 := bstep (se 1 (by rfl) ⟨342482, by rfl⟩ : syracuseStep 456643 = 684965) B684965
theorem B686033 : Blo 455782 686033 := bstep (se 2 (by rfl) ⟨257262, by rfl⟩ : syracuseStep 686033 = 514525) B514525
theorem B456659 : Blo 455782 456659 := bstep (se 1 (by rfl) ⟨342494, by rfl⟩ : syracuseStep 456659 = 684989) B684989
theorem B456675 : Blo 455782 456675 := bstep (se 1 (by rfl) ⟨342506, by rfl⟩ : syracuseStep 456675 = 685013) B685013
theorem B686051 : Blo 455782 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B1734641 : Blo 455782 1734641 := bstep (se 2 (by rfl) ⟨650490, by rfl⟩ : syracuseStep 1734641 = 1300981) B1300981
theorem B456691 : Blo 455782 456691 := bstep (se 1 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 456691 = 685037) B685037
theorem B686081 : Blo 455782 686081 := bstep (se 2 (by rfl) ⟨257280, by rfl⟩ : syracuseStep 686081 = 514561) B514561
theorem B456707 : Blo 455782 456707 := bstep (se 1 (by rfl) ⟨342530, by rfl⟩ : syracuseStep 456707 = 685061) B685061
theorem B1046531 : Blo 455782 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B456723 : Blo 455782 456723 := bstep (se 1 (by rfl) ⟨342542, by rfl⟩ : syracuseStep 456723 = 685085) B685085
theorem B686099 : Blo 455782 686099 := bstep (se 1 (by rfl) ⟨514574, by rfl⟩ : syracuseStep 686099 = 1029149) B1029149
theorem B456739 : Blo 455782 456739 := bstep (se 1 (by rfl) ⟨342554, by rfl⟩ : syracuseStep 456739 = 685109) B685109
theorem B686129 : Blo 455782 686129 := bstep (se 2 (by rfl) ⟨257298, by rfl⟩ : syracuseStep 686129 = 514597) B514597
theorem B456755 : Blo 455782 456755 := bstep (se 1 (by rfl) ⟨342566, by rfl⟩ : syracuseStep 456755 = 685133) B685133
theorem B1767473 : Blo 455782 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B456771 : Blo 455782 456771 := bstep (se 1 (by rfl) ⟨342578, by rfl⟩ : syracuseStep 456771 = 685157) B685157
theorem B686147 : Blo 455782 686147 := bstep (se 1 (by rfl) ⟨514610, by rfl⟩ : syracuseStep 686147 = 1029221) B1029221
theorem B456787 : Blo 455782 456787 := bstep (se 1 (by rfl) ⟨342590, by rfl⟩ : syracuseStep 456787 = 685181) B685181
theorem B686177 : Blo 455782 686177 := bstep (se 2 (by rfl) ⟨257316, by rfl⟩ : syracuseStep 686177 = 514633) B514633
theorem B456803 : Blo 455782 456803 := bstep (se 1 (by rfl) ⟨342602, by rfl⟩ : syracuseStep 456803 = 685205) B685205
theorem B1046641 : Blo 455782 1046641 := bstep (se 2 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 1046641 = 784981) B784981
theorem B456819 : Blo 455782 456819 := bstep (se 1 (by rfl) ⟨342614, by rfl⟩ : syracuseStep 456819 = 685229) B685229
theorem B686195 : Blo 455782 686195 := bstep (se 1 (by rfl) ⟨514646, by rfl⟩ : syracuseStep 686195 = 1029293) B1029293
theorem B456835 : Blo 455782 456835 := bstep (se 1 (by rfl) ⟨342626, by rfl⟩ : syracuseStep 456835 = 685253) B685253
theorem B686225 : Blo 455782 686225 := bstep (se 2 (by rfl) ⟨257334, by rfl⟩ : syracuseStep 686225 = 514669) B514669
theorem B456851 : Blo 455782 456851 := bstep (se 1 (by rfl) ⟨342638, by rfl⟩ : syracuseStep 456851 = 685277) B685277
theorem B456867 : Blo 455782 456867 := bstep (se 1 (by rfl) ⟨342650, by rfl⟩ : syracuseStep 456867 = 685301) B685301
theorem B686243 : Blo 455782 686243 := bstep (se 1 (by rfl) ⟨514682, by rfl⟩ : syracuseStep 686243 = 1029365) B1029365
theorem B456883 : Blo 455782 456883 := bstep (se 1 (by rfl) ⟨342662, by rfl⟩ : syracuseStep 456883 = 685325) B685325
theorem B686273 : Blo 455782 686273 := bstep (se 2 (by rfl) ⟨257352, by rfl⟩ : syracuseStep 686273 = 514705) B514705
theorem B456899 : Blo 455782 456899 := bstep (se 1 (by rfl) ⟨342674, by rfl⟩ : syracuseStep 456899 = 685349) B685349
theorem B489683 : Blo 455782 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B456915 : Blo 455782 456915 := bstep (se 1 (by rfl) ⟨342686, by rfl⟩ : syracuseStep 456915 = 685373) B685373
theorem B686291 : Blo 455782 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B456931 : Blo 455782 456931 := bstep (se 1 (by rfl) ⟨342698, by rfl⟩ : syracuseStep 456931 = 685397) B685397
theorem B686321 : Blo 455782 686321 := bstep (se 2 (by rfl) ⟨257370, by rfl⟩ : syracuseStep 686321 = 514741) B514741
theorem B456947 : Blo 455782 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B456963 : Blo 455782 456963 := bstep (se 1 (by rfl) ⟨342722, by rfl⟩ : syracuseStep 456963 = 685445) B685445
theorem B686339 : Blo 455782 686339 := bstep (se 1 (by rfl) ⟨514754, by rfl⟩ : syracuseStep 686339 = 1029509) B1029509
theorem B456979 : Blo 455782 456979 := bstep (se 1 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 456979 = 685469) B685469
theorem B686369 : Blo 455782 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B456995 : Blo 455782 456995 := bstep (se 1 (by rfl) ⟨342746, by rfl⟩ : syracuseStep 456995 = 685493) B685493
theorem B653617 : Blo 455782 653617 := bstep (se 2 (by rfl) ⟨245106, by rfl⟩ : syracuseStep 653617 = 490213) B490213
theorem B457011 : Blo 455782 457011 := bstep (se 1 (by rfl) ⟨342758, by rfl⟩ : syracuseStep 457011 = 685517) B685517
theorem B686387 : Blo 455782 686387 := bstep (se 1 (by rfl) ⟨514790, by rfl⟩ : syracuseStep 686387 = 1029581) B1029581
theorem B457027 : Blo 455782 457027 := bstep (se 1 (by rfl) ⟨342770, by rfl⟩ : syracuseStep 457027 = 685541) B685541
theorem B686417 : Blo 455782 686417 := bstep (se 2 (by rfl) ⟨257406, by rfl⟩ : syracuseStep 686417 = 514813) B514813
theorem B457043 : Blo 455782 457043 := bstep (se 1 (by rfl) ⟨342782, by rfl⟩ : syracuseStep 457043 = 685565) B685565
theorem B457059 : Blo 455782 457059 := bstep (se 1 (by rfl) ⟨342794, by rfl⟩ : syracuseStep 457059 = 685589) B685589
theorem B686435 : Blo 455782 686435 := bstep (se 1 (by rfl) ⟨514826, by rfl⟩ : syracuseStep 686435 = 1029653) B1029653
theorem B457075 : Blo 455782 457075 := bstep (se 1 (by rfl) ⟨342806, by rfl⟩ : syracuseStep 457075 = 685613) B685613
theorem B686465 : Blo 455782 686465 := bstep (se 2 (by rfl) ⟨257424, by rfl⟩ : syracuseStep 686465 = 514849) B514849
theorem B457091 : Blo 455782 457091 := bstep (se 1 (by rfl) ⟨342818, by rfl⟩ : syracuseStep 457091 = 685637) B685637
theorem B457107 : Blo 455782 457107 := bstep (se 1 (by rfl) ⟨342830, by rfl⟩ : syracuseStep 457107 = 685661) B685661
theorem B686483 : Blo 455782 686483 := bstep (se 1 (by rfl) ⟨514862, by rfl⟩ : syracuseStep 686483 = 1029725) B1029725
theorem B457123 : Blo 455782 457123 := bstep (se 1 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 457123 = 685685) B685685
theorem B686513 : Blo 455782 686513 := bstep (se 2 (by rfl) ⟨257442, by rfl⟩ : syracuseStep 686513 = 514885) B514885
theorem B457139 : Blo 455782 457139 := bstep (se 1 (by rfl) ⟨342854, by rfl⟩ : syracuseStep 457139 = 685709) B685709
theorem B457155 : Blo 455782 457155 := bstep (se 1 (by rfl) ⟨342866, by rfl⟩ : syracuseStep 457155 = 685733) B685733
theorem B686531 : Blo 455782 686531 := bstep (se 1 (by rfl) ⟨514898, by rfl⟩ : syracuseStep 686531 = 1029797) B1029797
theorem B1538513 : Blo 455782 1538513 := bstep (se 2 (by rfl) ⟨576942, by rfl⟩ : syracuseStep 1538513 = 1153885) B1153885
theorem B457171 : Blo 455782 457171 := bstep (se 1 (by rfl) ⟨342878, by rfl⟩ : syracuseStep 457171 = 685757) B685757
theorem B686561 : Blo 455782 686561 := bstep (se 2 (by rfl) ⟨257460, by rfl⟩ : syracuseStep 686561 = 514921) B514921
theorem B457187 : Blo 455782 457187 := bstep (se 1 (by rfl) ⟨342890, by rfl⟩ : syracuseStep 457187 = 685781) B685781
theorem B457203 : Blo 455782 457203 := bstep (se 1 (by rfl) ⟨342902, by rfl⟩ : syracuseStep 457203 = 685805) B685805
theorem B686579 : Blo 455782 686579 := bstep (se 1 (by rfl) ⟨514934, by rfl⟩ : syracuseStep 686579 = 1029869) B1029869
theorem B457219 : Blo 455782 457219 := bstep (se 1 (by rfl) ⟨342914, by rfl⟩ : syracuseStep 457219 = 685829) B685829
theorem B686609 : Blo 455782 686609 := bstep (se 2 (by rfl) ⟨257478, by rfl⟩ : syracuseStep 686609 = 514957) B514957
theorem B457235 : Blo 455782 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B457251 : Blo 455782 457251 := bstep (se 1 (by rfl) ⟨342938, by rfl⟩ : syracuseStep 457251 = 685877) B685877
theorem B686627 : Blo 455782 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B621091 : Blo 455782 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B457267 : Blo 455782 457267 := bstep (se 1 (by rfl) ⟨342950, by rfl⟩ : syracuseStep 457267 = 685901) B685901
theorem B981553 : Blo 455782 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B686657 : Blo 455782 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B457283 : Blo 455782 457283 := bstep (se 1 (by rfl) ⟨342962, by rfl⟩ : syracuseStep 457283 = 685925) B685925
theorem B981571 : Blo 455782 981571 := bstep (se 1 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 981571 = 1472357) B1472357
theorem B457299 : Blo 455782 457299 := bstep (se 1 (by rfl) ⟨342974, by rfl⟩ : syracuseStep 457299 = 685949) B685949
theorem B686675 : Blo 455782 686675 := bstep (se 1 (by rfl) ⟨515006, by rfl⟩ : syracuseStep 686675 = 1030013) B1030013
theorem B457315 : Blo 455782 457315 := bstep (se 1 (by rfl) ⟨342986, by rfl⟩ : syracuseStep 457315 = 685973) B685973
theorem B686705 : Blo 455782 686705 := bstep (se 2 (by rfl) ⟨257514, by rfl⟩ : syracuseStep 686705 = 515029) B515029
theorem B457331 : Blo 455782 457331 := bstep (se 1 (by rfl) ⟨342998, by rfl⟩ : syracuseStep 457331 = 685997) B685997
theorem B457347 : Blo 455782 457347 := bstep (se 1 (by rfl) ⟨343010, by rfl⟩ : syracuseStep 457347 = 686021) B686021
theorem B686723 : Blo 455782 686723 := bstep (se 1 (by rfl) ⟨515042, by rfl⟩ : syracuseStep 686723 = 1030085) B1030085
theorem B457363 : Blo 455782 457363 := bstep (se 1 (by rfl) ⟨343022, by rfl⟩ : syracuseStep 457363 = 686045) B686045
theorem B686753 : Blo 455782 686753 := bstep (se 2 (by rfl) ⟨257532, by rfl⟩ : syracuseStep 686753 = 515065) B515065
theorem B457379 : Blo 455782 457379 := bstep (se 1 (by rfl) ⟨343034, by rfl⟩ : syracuseStep 457379 = 686069) B686069
theorem B457395 : Blo 455782 457395 := bstep (se 1 (by rfl) ⟨343046, by rfl⟩ : syracuseStep 457395 = 686093) B686093
theorem B686771 : Blo 455782 686771 := bstep (se 1 (by rfl) ⟨515078, by rfl⟩ : syracuseStep 686771 = 1030157) B1030157
theorem B457411 : Blo 455782 457411 := bstep (se 1 (by rfl) ⟨343058, by rfl⟩ : syracuseStep 457411 = 686117) B686117
theorem B686801 : Blo 455782 686801 := bstep (se 2 (by rfl) ⟨257550, by rfl⟩ : syracuseStep 686801 = 515101) B515101
theorem B457427 : Blo 455782 457427 := bstep (se 1 (by rfl) ⟨343070, by rfl⟩ : syracuseStep 457427 = 686141) B686141
theorem B457443 : Blo 455782 457443 := bstep (se 1 (by rfl) ⟨343082, by rfl⟩ : syracuseStep 457443 = 686165) B686165
theorem B686819 : Blo 455782 686819 := bstep (se 1 (by rfl) ⟨515114, by rfl⟩ : syracuseStep 686819 = 1030229) B1030229
theorem B457459 : Blo 455782 457459 := bstep (se 1 (by rfl) ⟨343094, by rfl⟩ : syracuseStep 457459 = 686189) B686189
theorem B686849 : Blo 455782 686849 := bstep (se 2 (by rfl) ⟨257568, by rfl⟩ : syracuseStep 686849 = 515137) B515137
theorem B457475 : Blo 455782 457475 := bstep (se 1 (by rfl) ⟨343106, by rfl⟩ : syracuseStep 457475 = 686213) B686213
theorem B457491 : Blo 455782 457491 := bstep (se 1 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 457491 = 686237) B686237
theorem B686867 : Blo 455782 686867 := bstep (se 1 (by rfl) ⟨515150, by rfl⟩ : syracuseStep 686867 = 1030301) B1030301
theorem B457507 : Blo 455782 457507 := bstep (se 1 (by rfl) ⟨343130, by rfl⟩ : syracuseStep 457507 = 686261) B686261
theorem B686897 : Blo 455782 686897 := bstep (se 2 (by rfl) ⟨257586, by rfl⟩ : syracuseStep 686897 = 515173) B515173
theorem B457523 : Blo 455782 457523 := bstep (se 1 (by rfl) ⟨343142, by rfl⟩ : syracuseStep 457523 = 686285) B686285
theorem B457539 : Blo 455782 457539 := bstep (se 1 (by rfl) ⟨343154, by rfl⟩ : syracuseStep 457539 = 686309) B686309
theorem B686915 : Blo 455782 686915 := bstep (se 1 (by rfl) ⟨515186, by rfl⟩ : syracuseStep 686915 = 1030373) B1030373
theorem B457555 : Blo 455782 457555 := bstep (se 1 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 457555 = 686333) B686333
theorem B686945 : Blo 455782 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B457571 : Blo 455782 457571 := bstep (se 1 (by rfl) ⟨343178, by rfl⟩ : syracuseStep 457571 = 686357) B686357
theorem B2325347 : Blo 455782 2325347 := bstep (se 1 (by rfl) ⟨1744010, by rfl⟩ : syracuseStep 2325347 = 3488021) B3488021
theorem B457587 : Blo 455782 457587 := bstep (se 1 (by rfl) ⟨343190, by rfl⟩ : syracuseStep 457587 = 686381) B686381
theorem B686963 : Blo 455782 686963 := bstep (se 1 (by rfl) ⟨515222, by rfl⟩ : syracuseStep 686963 = 1030445) B1030445
theorem B457603 : Blo 455782 457603 := bstep (se 1 (by rfl) ⟨343202, by rfl⟩ : syracuseStep 457603 = 686405) B686405
theorem B686993 : Blo 455782 686993 := bstep (se 2 (by rfl) ⟨257622, by rfl⟩ : syracuseStep 686993 = 515245) B515245
theorem B457619 : Blo 455782 457619 := bstep (se 1 (by rfl) ⟨343214, by rfl⟩ : syracuseStep 457619 = 686429) B686429
theorem B457635 : Blo 455782 457635 := bstep (se 1 (by rfl) ⟨343226, by rfl⟩ : syracuseStep 457635 = 686453) B686453
theorem B687011 : Blo 455782 687011 := bstep (se 1 (by rfl) ⟨515258, by rfl⟩ : syracuseStep 687011 = 1030517) B1030517
theorem B457651 : Blo 455782 457651 := bstep (se 1 (by rfl) ⟨343238, by rfl⟩ : syracuseStep 457651 = 686477) B686477
theorem B687041 : Blo 455782 687041 := bstep (se 2 (by rfl) ⟨257640, by rfl⟩ : syracuseStep 687041 = 515281) B515281
theorem B457667 : Blo 455782 457667 := bstep (se 1 (by rfl) ⟨343250, by rfl⟩ : syracuseStep 457667 = 686501) B686501
theorem B457683 : Blo 455782 457683 := bstep (se 1 (by rfl) ⟨343262, by rfl⟩ : syracuseStep 457683 = 686525) B686525
theorem B687059 : Blo 455782 687059 := bstep (se 1 (by rfl) ⟨515294, by rfl⟩ : syracuseStep 687059 = 1030589) B1030589
theorem B457699 : Blo 455782 457699 := bstep (se 1 (by rfl) ⟨343274, by rfl⟩ : syracuseStep 457699 = 686549) B686549
theorem B1539053 : Blo 455782 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B687089 : Blo 455782 687089 := bstep (se 2 (by rfl) ⟨257658, by rfl⟩ : syracuseStep 687089 = 515317) B515317
theorem B457715 : Blo 455782 457715 := bstep (se 1 (by rfl) ⟨343286, by rfl⟩ : syracuseStep 457715 = 686573) B686573
theorem B654323 : Blo 455782 654323 := bstep (se 1 (by rfl) ⟨490742, by rfl⟩ : syracuseStep 654323 = 981485) B981485
theorem B457731 : Blo 455782 457731 := bstep (se 1 (by rfl) ⟨343298, by rfl⟩ : syracuseStep 457731 = 686597) B686597
theorem B687107 : Blo 455782 687107 := bstep (se 1 (by rfl) ⟨515330, by rfl⟩ : syracuseStep 687107 = 1030661) B1030661
theorem B457747 : Blo 455782 457747 := bstep (se 1 (by rfl) ⟨343310, by rfl⟩ : syracuseStep 457747 = 686621) B686621
theorem B687137 : Blo 455782 687137 := bstep (se 2 (by rfl) ⟨257676, by rfl⟩ : syracuseStep 687137 = 515353) B515353
theorem B1539107 : Blo 455782 1539107 := bstep (se 1 (by rfl) ⟨1154330, by rfl⟩ : syracuseStep 1539107 = 2308661) B2308661
theorem B457763 : Blo 455782 457763 := bstep (se 1 (by rfl) ⟨343322, by rfl⟩ : syracuseStep 457763 = 686645) B686645
theorem B457779 : Blo 455782 457779 := bstep (se 1 (by rfl) ⟨343334, by rfl⟩ : syracuseStep 457779 = 686669) B686669
theorem B687155 : Blo 455782 687155 := bstep (se 1 (by rfl) ⟨515366, by rfl⟩ : syracuseStep 687155 = 1030733) B1030733
theorem B457795 : Blo 455782 457795 := bstep (se 1 (by rfl) ⟨343346, by rfl⟩ : syracuseStep 457795 = 686693) B686693
theorem B687185 : Blo 455782 687185 := bstep (se 2 (by rfl) ⟨257694, by rfl⟩ : syracuseStep 687185 = 515389) B515389
theorem B457811 : Blo 455782 457811 := bstep (se 1 (by rfl) ⟨343358, by rfl⟩ : syracuseStep 457811 = 686717) B686717
theorem B457827 : Blo 455782 457827 := bstep (se 1 (by rfl) ⟨343370, by rfl⟩ : syracuseStep 457827 = 686741) B686741
theorem B687203 : Blo 455782 687203 := bstep (se 1 (by rfl) ⟨515402, by rfl⟩ : syracuseStep 687203 = 1030805) B1030805
theorem B457843 : Blo 455782 457843 := bstep (se 1 (by rfl) ⟨343382, by rfl⟩ : syracuseStep 457843 = 686765) B686765
theorem B687233 : Blo 455782 687233 := bstep (se 2 (by rfl) ⟨257712, by rfl⟩ : syracuseStep 687233 = 515425) B515425
theorem B621697 : Blo 455782 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B457859 : Blo 455782 457859 := bstep (se 1 (by rfl) ⟨343394, by rfl⟩ : syracuseStep 457859 = 686789) B686789
theorem B2784397 : Blo 455782 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B457875 : Blo 455782 457875 := bstep (se 1 (by rfl) ⟨343406, by rfl⟩ : syracuseStep 457875 = 686813) B686813
theorem B687251 : Blo 455782 687251 := bstep (se 1 (by rfl) ⟨515438, by rfl⟩ : syracuseStep 687251 = 1030877) B1030877
theorem B457891 : Blo 455782 457891 := bstep (se 1 (by rfl) ⟨343418, by rfl⟩ : syracuseStep 457891 = 686837) B686837
theorem B687281 : Blo 455782 687281 := bstep (se 2 (by rfl) ⟨257730, by rfl⟩ : syracuseStep 687281 = 515461) B515461
theorem B457907 : Blo 455782 457907 := bstep (se 1 (by rfl) ⟨343430, by rfl⟩ : syracuseStep 457907 = 686861) B686861
theorem B457923 : Blo 455782 457923 := bstep (se 1 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 457923 = 686885) B686885
theorem B687299 : Blo 455782 687299 := bstep (se 1 (by rfl) ⟨515474, by rfl⟩ : syracuseStep 687299 = 1030949) B1030949
theorem B457939 : Blo 455782 457939 := bstep (se 1 (by rfl) ⟨343454, by rfl⟩ : syracuseStep 457939 = 686909) B686909
theorem B687329 : Blo 455782 687329 := bstep (se 2 (by rfl) ⟨257748, by rfl⟩ : syracuseStep 687329 = 515497) B515497
theorem B457955 : Blo 455782 457955 := bstep (se 1 (by rfl) ⟨343466, by rfl⟩ : syracuseStep 457955 = 686933) B686933
theorem B14908643 : Blo 455782 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B457971 : Blo 455782 457971 := bstep (se 1 (by rfl) ⟨343478, by rfl⟩ : syracuseStep 457971 = 686957) B686957
theorem B687347 : Blo 455782 687347 := bstep (se 1 (by rfl) ⟨515510, by rfl⟩ : syracuseStep 687347 = 1031021) B1031021
theorem B457987 : Blo 455782 457987 := bstep (se 1 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 457987 = 686981) B686981
theorem B687377 : Blo 455782 687377 := bstep (se 2 (by rfl) ⟨257766, by rfl⟩ : syracuseStep 687377 = 515533) B515533
theorem B458003 : Blo 455782 458003 := bstep (se 1 (by rfl) ⟨343502, by rfl⟩ : syracuseStep 458003 = 687005) B687005
theorem B458019 : Blo 455782 458019 := bstep (se 1 (by rfl) ⟨343514, by rfl⟩ : syracuseStep 458019 = 687029) B687029
theorem B687395 : Blo 455782 687395 := bstep (se 1 (by rfl) ⟨515546, by rfl⟩ : syracuseStep 687395 = 1031093) B1031093
theorem B1539377 : Blo 455782 1539377 := bstep (se 2 (by rfl) ⟨577266, by rfl⟩ : syracuseStep 1539377 = 1154533) B1154533
theorem B458035 : Blo 455782 458035 := bstep (se 1 (by rfl) ⟨343526, by rfl⟩ : syracuseStep 458035 = 687053) B687053
theorem B687425 : Blo 455782 687425 := bstep (se 2 (by rfl) ⟨257784, by rfl⟩ : syracuseStep 687425 = 515569) B515569
theorem B458051 : Blo 455782 458051 := bstep (se 1 (by rfl) ⟨343538, by rfl⟩ : syracuseStep 458051 = 687077) B687077
theorem B458067 : Blo 455782 458067 := bstep (se 1 (by rfl) ⟨343550, by rfl⟩ : syracuseStep 458067 = 687101) B687101
theorem B687443 : Blo 455782 687443 := bstep (se 1 (by rfl) ⟨515582, by rfl⟩ : syracuseStep 687443 = 1031165) B1031165
theorem B458083 : Blo 455782 458083 := bstep (se 1 (by rfl) ⟨343562, by rfl⟩ : syracuseStep 458083 = 687125) B687125
theorem B687473 : Blo 455782 687473 := bstep (se 2 (by rfl) ⟨257802, by rfl⟩ : syracuseStep 687473 = 515605) B515605
theorem B458099 : Blo 455782 458099 := bstep (se 1 (by rfl) ⟨343574, by rfl⟩ : syracuseStep 458099 = 687149) B687149
theorem B458115 : Blo 455782 458115 := bstep (se 1 (by rfl) ⟨343586, by rfl⟩ : syracuseStep 458115 = 687173) B687173
theorem B687491 : Blo 455782 687491 := bstep (se 1 (by rfl) ⟨515618, by rfl⟩ : syracuseStep 687491 = 1031237) B1031237
theorem B458131 : Blo 455782 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B687521 : Blo 455782 687521 := bstep (se 2 (by rfl) ⟨257820, by rfl⟩ : syracuseStep 687521 = 515641) B515641
theorem B1736099 : Blo 455782 1736099 := bstep (se 1 (by rfl) ⟨1302074, by rfl⟩ : syracuseStep 1736099 = 2604149) B2604149
theorem B458147 : Blo 455782 458147 := bstep (se 1 (by rfl) ⟨343610, by rfl⟩ : syracuseStep 458147 = 687221) B687221
theorem B1736113 : Blo 455782 1736113 := bstep (se 2 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 1736113 = 1302085) B1302085
theorem B458163 : Blo 455782 458163 := bstep (se 1 (by rfl) ⟨343622, by rfl⟩ : syracuseStep 458163 = 687245) B687245
theorem B687539 : Blo 455782 687539 := bstep (se 1 (by rfl) ⟨515654, by rfl⟩ : syracuseStep 687539 = 1031309) B1031309
theorem B785857 : Blo 455782 785857 := bstep (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) B589393
theorem B458179 : Blo 455782 458179 := bstep (se 1 (by rfl) ⟨343634, by rfl⟩ : syracuseStep 458179 = 687269) B687269
theorem B687569 : Blo 455782 687569 := bstep (se 2 (by rfl) ⟨257838, by rfl⟩ : syracuseStep 687569 = 515677) B515677
theorem B458195 : Blo 455782 458195 := bstep (se 1 (by rfl) ⟨343646, by rfl⟩ : syracuseStep 458195 = 687293) B687293
theorem B458211 : Blo 455782 458211 := bstep (se 1 (by rfl) ⟨343658, by rfl⟩ : syracuseStep 458211 = 687317) B687317
theorem B687587 : Blo 455782 687587 := bstep (se 1 (by rfl) ⟨515690, by rfl⟩ : syracuseStep 687587 = 1031381) B1031381
theorem B458227 : Blo 455782 458227 := bstep (se 1 (by rfl) ⟨343670, by rfl⟩ : syracuseStep 458227 = 687341) B687341
theorem B687617 : Blo 455782 687617 := bstep (se 2 (by rfl) ⟨257856, by rfl⟩ : syracuseStep 687617 = 515713) B515713
theorem B458243 : Blo 455782 458243 := bstep (se 1 (by rfl) ⟨343682, by rfl⟩ : syracuseStep 458243 = 687365) B687365
theorem B458259 : Blo 455782 458259 := bstep (se 1 (by rfl) ⟨343694, by rfl⟩ : syracuseStep 458259 = 687389) B687389
theorem B687635 : Blo 455782 687635 := bstep (se 1 (by rfl) ⟨515726, by rfl⟩ : syracuseStep 687635 = 1031453) B1031453
theorem B458275 : Blo 455782 458275 := bstep (se 1 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 458275 = 687413) B687413
theorem B687665 : Blo 455782 687665 := bstep (se 2 (by rfl) ⟨257874, by rfl⟩ : syracuseStep 687665 = 515749) B515749
theorem B458291 : Blo 455782 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B458307 : Blo 455782 458307 := bstep (se 1 (by rfl) ⟨343730, by rfl⟩ : syracuseStep 458307 = 687461) B687461
theorem B687683 : Blo 455782 687683 := bstep (se 1 (by rfl) ⟨515762, by rfl⟩ : syracuseStep 687683 = 1031525) B1031525
theorem B458323 : Blo 455782 458323 := bstep (se 1 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 458323 = 687485) B687485
theorem B687713 : Blo 455782 687713 := bstep (se 2 (by rfl) ⟨257892, by rfl⟩ : syracuseStep 687713 = 515785) B515785
theorem B786017 : Blo 455782 786017 := bstep (se 2 (by rfl) ⟨294756, by rfl⟩ : syracuseStep 786017 = 589513) B589513
theorem B458339 : Blo 455782 458339 := bstep (se 1 (by rfl) ⟨343754, by rfl⟩ : syracuseStep 458339 = 687509) B687509
theorem B687731 : Blo 455782 687731 := bstep (se 1 (by rfl) ⟨515798, by rfl⟩ : syracuseStep 687731 = 1031597) B1031597
theorem B458355 : Blo 455782 458355 := bstep (se 1 (by rfl) ⟨343766, by rfl⟩ : syracuseStep 458355 = 687533) B687533
theorem B458371 : Blo 455782 458371 := bstep (se 1 (by rfl) ⟨343778, by rfl⟩ : syracuseStep 458371 = 687557) B687557
theorem B2326157 : Blo 455782 2326157 := bstep (se 3 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 2326157 = 872309) B872309
theorem B687761 : Blo 455782 687761 := bstep (se 2 (by rfl) ⟨257910, by rfl⟩ : syracuseStep 687761 = 515821) B515821
theorem B458387 : Blo 455782 458387 := bstep (se 1 (by rfl) ⟨343790, by rfl⟩ : syracuseStep 458387 = 687581) B687581
theorem B458403 : Blo 455782 458403 := bstep (se 1 (by rfl) ⟨343802, by rfl⟩ : syracuseStep 458403 = 687605) B687605
theorem B687779 : Blo 455782 687779 := bstep (se 1 (by rfl) ⟨515834, by rfl⟩ : syracuseStep 687779 = 1031669) B1031669
theorem B458419 : Blo 455782 458419 := bstep (se 1 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 458419 = 687629) B687629
theorem B687809 : Blo 455782 687809 := bstep (se 2 (by rfl) ⟨257928, by rfl⟩ : syracuseStep 687809 = 515857) B515857
theorem B458435 : Blo 455782 458435 := bstep (se 1 (by rfl) ⟨343826, by rfl⟩ : syracuseStep 458435 = 687653) B687653
theorem B1769165 : Blo 455782 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B458451 : Blo 455782 458451 := bstep (se 1 (by rfl) ⟨343838, by rfl⟩ : syracuseStep 458451 = 687677) B687677
theorem B687827 : Blo 455782 687827 := bstep (se 1 (by rfl) ⟨515870, by rfl⟩ : syracuseStep 687827 = 1031741) B1031741
theorem B458467 : Blo 455782 458467 := bstep (se 1 (by rfl) ⟨343850, by rfl⟩ : syracuseStep 458467 = 687701) B687701
theorem B687857 : Blo 455782 687857 := bstep (se 2 (by rfl) ⟨257946, by rfl⟩ : syracuseStep 687857 = 515893) B515893
theorem B458483 : Blo 455782 458483 := bstep (se 1 (by rfl) ⟨343862, by rfl⟩ : syracuseStep 458483 = 687725) B687725
theorem B458499 : Blo 455782 458499 := bstep (se 1 (by rfl) ⟨343874, by rfl⟩ : syracuseStep 458499 = 687749) B687749
theorem B687875 : Blo 455782 687875 := bstep (se 1 (by rfl) ⟨515906, by rfl⟩ : syracuseStep 687875 = 1031813) B1031813
theorem B458515 : Blo 455782 458515 := bstep (se 1 (by rfl) ⟨343886, by rfl⟩ : syracuseStep 458515 = 687773) B687773
theorem B687905 : Blo 455782 687905 := bstep (se 2 (by rfl) ⟨257964, by rfl⟩ : syracuseStep 687905 = 515929) B515929
theorem B458531 : Blo 455782 458531 := bstep (se 1 (by rfl) ⟨343898, by rfl⟩ : syracuseStep 458531 = 687797) B687797
theorem B458547 : Blo 455782 458547 := bstep (se 1 (by rfl) ⟨343910, by rfl⟩ : syracuseStep 458547 = 687821) B687821
theorem B687923 : Blo 455782 687923 := bstep (se 1 (by rfl) ⟨515942, by rfl⟩ : syracuseStep 687923 = 1031885) B1031885
theorem B458563 : Blo 455782 458563 := bstep (se 1 (by rfl) ⟨343922, by rfl⟩ : syracuseStep 458563 = 687845) B687845
theorem B1539917 : Blo 455782 1539917 := bstep (se 3 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 1539917 = 577469) B577469
theorem B687953 : Blo 455782 687953 := bstep (se 2 (by rfl) ⟨257982, by rfl⟩ : syracuseStep 687953 = 515965) B515965
theorem B458579 : Blo 455782 458579 := bstep (se 1 (by rfl) ⟨343934, by rfl⟩ : syracuseStep 458579 = 687869) B687869
theorem B458595 : Blo 455782 458595 := bstep (se 1 (by rfl) ⟨343946, by rfl⟩ : syracuseStep 458595 = 687893) B687893
theorem B687971 : Blo 455782 687971 := bstep (se 1 (by rfl) ⟨515978, by rfl⟩ : syracuseStep 687971 = 1031957) B1031957
theorem B458611 : Blo 455782 458611 := bstep (se 1 (by rfl) ⟨343958, by rfl⟩ : syracuseStep 458611 = 687917) B687917
theorem B688001 : Blo 455782 688001 := bstep (se 2 (by rfl) ⟨258000, by rfl⟩ : syracuseStep 688001 = 516001) B516001
theorem B1539971 : Blo 455782 1539971 := bstep (se 1 (by rfl) ⟨1154978, by rfl⟩ : syracuseStep 1539971 = 2309957) B2309957
theorem B458627 : Blo 455782 458627 := bstep (se 1 (by rfl) ⟨343970, by rfl⟩ : syracuseStep 458627 = 687941) B687941
theorem B1179523 : Blo 455782 1179523 := bstep (se 1 (by rfl) ⟨884642, by rfl⟩ : syracuseStep 1179523 = 1769285) B1769285
theorem B458643 : Blo 455782 458643 := bstep (se 1 (by rfl) ⟨343982, by rfl⟩ : syracuseStep 458643 = 687965) B687965
theorem B688019 : Blo 455782 688019 := bstep (se 1 (by rfl) ⟨516014, by rfl⟩ : syracuseStep 688019 = 1032029) B1032029
theorem B458659 : Blo 455782 458659 := bstep (se 1 (by rfl) ⟨343994, by rfl⟩ : syracuseStep 458659 = 687989) B687989
theorem B688049 : Blo 455782 688049 := bstep (se 2 (by rfl) ⟨258018, by rfl⟩ : syracuseStep 688049 = 516037) B516037
theorem B458675 : Blo 455782 458675 := bstep (se 1 (by rfl) ⟨344006, by rfl⟩ : syracuseStep 458675 = 688013) B688013
theorem B458691 : Blo 455782 458691 := bstep (se 1 (by rfl) ⟨344018, by rfl⟩ : syracuseStep 458691 = 688037) B688037
theorem B688067 : Blo 455782 688067 := bstep (se 1 (by rfl) ⟨516050, by rfl⟩ : syracuseStep 688067 = 1032101) B1032101
theorem B458707 : Blo 455782 458707 := bstep (se 1 (by rfl) ⟨344030, by rfl⟩ : syracuseStep 458707 = 688061) B688061
theorem B688097 : Blo 455782 688097 := bstep (se 2 (by rfl) ⟨258036, by rfl⟩ : syracuseStep 688097 = 516073) B516073
theorem B458723 : Blo 455782 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B458739 : Blo 455782 458739 := bstep (se 1 (by rfl) ⟨344054, by rfl⟩ : syracuseStep 458739 = 688109) B688109
theorem B688115 : Blo 455782 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B688139 : Blo 455782 688139 := bstep (se 1 (by rfl) ⟨516104, by rfl⟩ : syracuseStep 688139 = 1032209) B1032209
theorem B458763 : Blo 455782 458763 := bstep (se 1 (by rfl) ⟨344072, by rfl⟩ : syracuseStep 458763 = 688145) B688145
theorem B688151 : Blo 455782 688151 := bstep (se 1 (by rfl) ⟨516113, by rfl⟩ : syracuseStep 688151 = 1032227) B1032227
theorem B458775 : Blo 455782 458775 := bstep (se 1 (by rfl) ⟨344081, by rfl⟩ : syracuseStep 458775 = 688163) B688163
theorem B458795 : Blo 455782 458795 := bstep (se 1 (by rfl) ⟨344096, by rfl⟩ : syracuseStep 458795 = 688193) B688193
theorem B458807 : Blo 455782 458807 := bstep (se 1 (by rfl) ⟨344105, by rfl⟩ : syracuseStep 458807 = 688211) B688211
theorem B458827 : Blo 455782 458827 := bstep (se 1 (by rfl) ⟨344120, by rfl⟩ : syracuseStep 458827 = 688241) B688241
theorem B458839 : Blo 455782 458839 := bstep (se 1 (by rfl) ⟨344129, by rfl⟩ : syracuseStep 458839 = 688259) B688259
theorem B688217 : Blo 455782 688217 := bstep (se 2 (by rfl) ⟨258081, by rfl⟩ : syracuseStep 688217 = 516163) B516163
theorem B458859 : Blo 455782 458859 := bstep (se 1 (by rfl) ⟨344144, by rfl⟩ : syracuseStep 458859 = 688289) B688289
theorem B458871 : Blo 455782 458871 := bstep (se 1 (by rfl) ⟨344153, by rfl⟩ : syracuseStep 458871 = 688307) B688307
theorem B458891 : Blo 455782 458891 := bstep (se 1 (by rfl) ⟨344168, by rfl⟩ : syracuseStep 458891 = 688337) B688337
theorem B458903 : Blo 455782 458903 := bstep (se 1 (by rfl) ⟨344177, by rfl⟩ : syracuseStep 458903 = 688355) B688355
theorem B458923 : Blo 455782 458923 := bstep (se 1 (by rfl) ⟨344192, by rfl⟩ : syracuseStep 458923 = 688385) B688385
theorem B458935 : Blo 455782 458935 := bstep (se 1 (by rfl) ⟨344201, by rfl⟩ : syracuseStep 458935 = 688403) B688403
theorem B688331 : Blo 455782 688331 := bstep (se 1 (by rfl) ⟨516248, by rfl⟩ : syracuseStep 688331 = 1032497) B1032497
theorem B458955 : Blo 455782 458955 := bstep (se 1 (by rfl) ⟨344216, by rfl⟩ : syracuseStep 458955 = 688433) B688433
theorem B688343 : Blo 455782 688343 := bstep (se 1 (by rfl) ⟨516257, by rfl⟩ : syracuseStep 688343 = 1032515) B1032515
theorem B458967 : Blo 455782 458967 := bstep (se 1 (by rfl) ⟨344225, by rfl⟩ : syracuseStep 458967 = 688451) B688451
theorem B458987 : Blo 455782 458987 := bstep (se 1 (by rfl) ⟨344240, by rfl⟩ : syracuseStep 458987 = 688481) B688481
theorem B458999 : Blo 455782 458999 := bstep (se 1 (by rfl) ⟨344249, by rfl⟩ : syracuseStep 458999 = 688499) B688499
theorem B459019 : Blo 455782 459019 := bstep (se 1 (by rfl) ⟨344264, by rfl⟩ : syracuseStep 459019 = 688529) B688529
theorem B459031 : Blo 455782 459031 := bstep (se 1 (by rfl) ⟨344273, by rfl⟩ : syracuseStep 459031 = 688547) B688547
theorem B688409 : Blo 455782 688409 := bstep (se 2 (by rfl) ⟨258153, by rfl⟩ : syracuseStep 688409 = 516307) B516307
theorem B459051 : Blo 455782 459051 := bstep (se 1 (by rfl) ⟨344288, by rfl⟩ : syracuseStep 459051 = 688577) B688577
theorem B1540403 : Blo 455782 1540403 := bstep (se 1 (by rfl) ⟨1155302, by rfl⟩ : syracuseStep 1540403 = 2310605) B2310605
theorem B459063 : Blo 455782 459063 := bstep (se 1 (by rfl) ⟨344297, by rfl⟩ : syracuseStep 459063 = 688595) B688595
theorem B459083 : Blo 455782 459083 := bstep (se 1 (by rfl) ⟨344312, by rfl⟩ : syracuseStep 459083 = 688625) B688625
theorem B459095 : Blo 455782 459095 := bstep (se 1 (by rfl) ⟨344321, by rfl⟩ : syracuseStep 459095 = 688643) B688643
theorem B459115 : Blo 455782 459115 := bstep (se 1 (by rfl) ⟨344336, by rfl⟩ : syracuseStep 459115 = 688673) B688673
theorem B459127 : Blo 455782 459127 := bstep (se 1 (by rfl) ⟨344345, by rfl⟩ : syracuseStep 459127 = 688691) B688691
theorem B688523 : Blo 455782 688523 := bstep (se 1 (by rfl) ⟨516392, by rfl⟩ : syracuseStep 688523 = 1032785) B1032785
theorem B459147 : Blo 455782 459147 := bstep (se 1 (by rfl) ⟨344360, by rfl⟩ : syracuseStep 459147 = 688721) B688721
theorem B688535 : Blo 455782 688535 := bstep (se 1 (by rfl) ⟨516401, by rfl⟩ : syracuseStep 688535 = 1032803) B1032803
theorem B459159 : Blo 455782 459159 := bstep (se 1 (by rfl) ⟨344369, by rfl⟩ : syracuseStep 459159 = 688739) B688739
theorem B459179 : Blo 455782 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B459191 : Blo 455782 459191 := bstep (se 1 (by rfl) ⟨344393, by rfl⟩ : syracuseStep 459191 = 688787) B688787
theorem B459211 : Blo 455782 459211 := bstep (se 1 (by rfl) ⟨344408, by rfl⟩ : syracuseStep 459211 = 688817) B688817
theorem B459223 : Blo 455782 459223 := bstep (se 1 (by rfl) ⟨344417, by rfl⟩ : syracuseStep 459223 = 688835) B688835
theorem B688601 : Blo 455782 688601 := bstep (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) B516451
theorem B459243 : Blo 455782 459243 := bstep (se 1 (by rfl) ⟨344432, by rfl⟩ : syracuseStep 459243 = 688865) B688865
theorem B459255 : Blo 455782 459255 := bstep (se 1 (by rfl) ⟨344441, by rfl⟩ : syracuseStep 459255 = 688883) B688883
theorem B459275 : Blo 455782 459275 := bstep (se 1 (by rfl) ⟨344456, by rfl⟩ : syracuseStep 459275 = 688913) B688913
theorem B459287 : Blo 455782 459287 := bstep (se 1 (by rfl) ⟨344465, by rfl⟩ : syracuseStep 459287 = 688931) B688931
theorem B459307 : Blo 455782 459307 := bstep (se 1 (by rfl) ⟨344480, by rfl⟩ : syracuseStep 459307 = 688961) B688961
theorem B459319 : Blo 455782 459319 := bstep (se 1 (by rfl) ⟨344489, by rfl⟩ : syracuseStep 459319 = 688979) B688979
theorem B1540673 : Blo 455782 1540673 := bstep (se 2 (by rfl) ⟨577752, by rfl⟩ : syracuseStep 1540673 = 1155505) B1155505
theorem B688715 : Blo 455782 688715 := bstep (se 1 (by rfl) ⟨516536, by rfl⟩ : syracuseStep 688715 = 1033073) B1033073
theorem B459339 : Blo 455782 459339 := bstep (se 1 (by rfl) ⟨344504, by rfl⟩ : syracuseStep 459339 = 689009) B689009
theorem B688727 : Blo 455782 688727 := bstep (se 1 (by rfl) ⟨516545, by rfl⟩ : syracuseStep 688727 = 1033091) B1033091
theorem B459351 : Blo 455782 459351 := bstep (se 1 (by rfl) ⟨344513, by rfl⟩ : syracuseStep 459351 = 689027) B689027
theorem B459371 : Blo 455782 459371 := bstep (se 1 (by rfl) ⟨344528, by rfl⟩ : syracuseStep 459371 = 689057) B689057
theorem B459383 : Blo 455782 459383 := bstep (se 1 (by rfl) ⟨344537, by rfl⟩ : syracuseStep 459383 = 689075) B689075
theorem B459403 : Blo 455782 459403 := bstep (se 1 (by rfl) ⟨344552, by rfl⟩ : syracuseStep 459403 = 689105) B689105
theorem B459415 : Blo 455782 459415 := bstep (se 1 (by rfl) ⟨344561, by rfl⟩ : syracuseStep 459415 = 689123) B689123
theorem B688793 : Blo 455782 688793 := bstep (se 2 (by rfl) ⟨258297, by rfl⟩ : syracuseStep 688793 = 516595) B516595
theorem B459435 : Blo 455782 459435 := bstep (se 1 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 459435 = 689153) B689153
theorem B1737389 : Blo 455782 1737389 := bstep (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) B651521
theorem B459447 : Blo 455782 459447 := bstep (se 1 (by rfl) ⟨344585, by rfl⟩ : syracuseStep 459447 = 689171) B689171
theorem B1606337 : Blo 455782 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B459467 : Blo 455782 459467 := bstep (se 1 (by rfl) ⟨344600, by rfl⟩ : syracuseStep 459467 = 689201) B689201
theorem B459479 : Blo 455782 459479 := bstep (se 1 (by rfl) ⟨344609, by rfl⟩ : syracuseStep 459479 = 689219) B689219
theorem B459499 : Blo 455782 459499 := bstep (se 1 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 459499 = 689249) B689249
theorem B459511 : Blo 455782 459511 := bstep (se 1 (by rfl) ⟨344633, by rfl⟩ : syracuseStep 459511 = 689267) B689267
theorem B688907 : Blo 455782 688907 := bstep (se 1 (by rfl) ⟨516680, by rfl⟩ : syracuseStep 688907 = 1033361) B1033361
theorem B459531 : Blo 455782 459531 := bstep (se 1 (by rfl) ⟨344648, by rfl⟩ : syracuseStep 459531 = 689297) B689297
theorem B688919 : Blo 455782 688919 := bstep (se 1 (by rfl) ⟨516689, by rfl⟩ : syracuseStep 688919 = 1033379) B1033379
theorem B459543 : Blo 455782 459543 := bstep (se 1 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 459543 = 689315) B689315
theorem B459563 : Blo 455782 459563 := bstep (se 1 (by rfl) ⟨344672, by rfl⟩ : syracuseStep 459563 = 689345) B689345
theorem B459575 : Blo 455782 459575 := bstep (se 1 (by rfl) ⟨344681, by rfl⟩ : syracuseStep 459575 = 689363) B689363
theorem B459595 : Blo 455782 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B459607 : Blo 455782 459607 := bstep (se 1 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 459607 = 689411) B689411
theorem B688985 : Blo 455782 688985 := bstep (se 2 (by rfl) ⟨258369, by rfl⟩ : syracuseStep 688985 = 516739) B516739
theorem B459627 : Blo 455782 459627 := bstep (se 1 (by rfl) ⟨344720, by rfl⟩ : syracuseStep 459627 = 689441) B689441
theorem B459639 : Blo 455782 459639 := bstep (se 1 (by rfl) ⟨344729, by rfl⟩ : syracuseStep 459639 = 689459) B689459
theorem B459659 : Blo 455782 459659 := bstep (se 1 (by rfl) ⟨344744, by rfl⟩ : syracuseStep 459659 = 689489) B689489
theorem B3900311 : Blo 455782 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B459671 : Blo 455782 459671 := bstep (se 1 (by rfl) ⟨344753, by rfl⟩ : syracuseStep 459671 = 689507) B689507
theorem B459691 : Blo 455782 459691 := bstep (se 1 (by rfl) ⟨344768, by rfl⟩ : syracuseStep 459691 = 689537) B689537
theorem B459703 : Blo 455782 459703 := bstep (se 1 (by rfl) ⟨344777, by rfl⟩ : syracuseStep 459703 = 689555) B689555
theorem B689099 : Blo 455782 689099 := bstep (se 1 (by rfl) ⟨516824, by rfl⟩ : syracuseStep 689099 = 1033649) B1033649
theorem B459723 : Blo 455782 459723 := bstep (se 1 (by rfl) ⟨344792, by rfl⟩ : syracuseStep 459723 = 689585) B689585
theorem B689111 : Blo 455782 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B459735 : Blo 455782 459735 := bstep (se 1 (by rfl) ⟨344801, by rfl⟩ : syracuseStep 459735 = 689603) B689603
theorem B459755 : Blo 455782 459755 := bstep (se 1 (by rfl) ⟨344816, by rfl⟩ : syracuseStep 459755 = 689633) B689633
theorem B459767 : Blo 455782 459767 := bstep (se 1 (by rfl) ⟨344825, by rfl⟩ : syracuseStep 459767 = 689651) B689651
theorem B689177 : Blo 455782 689177 := bstep (se 2 (by rfl) ⟨258441, by rfl⟩ : syracuseStep 689177 = 516883) B516883
theorem B1541213 : Blo 455782 1541213 := bstep (se 3 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 1541213 = 577955) B577955
theorem B689291 : Blo 455782 689291 := bstep (se 1 (by rfl) ⟨516968, by rfl⟩ : syracuseStep 689291 = 1033937) B1033937
theorem B689303 : Blo 455782 689303 := bstep (se 1 (by rfl) ⟨516977, by rfl⟩ : syracuseStep 689303 = 1033955) B1033955
theorem B5637325 : Blo 455782 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B689369 : Blo 455782 689369 := bstep (se 2 (by rfl) ⟨258513, by rfl⟩ : syracuseStep 689369 = 517027) B517027
theorem B689483 : Blo 455782 689483 := bstep (se 1 (by rfl) ⟨517112, by rfl⟩ : syracuseStep 689483 = 1034225) B1034225
theorem B689495 : Blo 455782 689495 := bstep (se 1 (by rfl) ⟨517121, by rfl⟩ : syracuseStep 689495 = 1034243) B1034243
theorem B689561 : Blo 455782 689561 := bstep (se 2 (by rfl) ⟨258585, by rfl⟩ : syracuseStep 689561 = 517171) B517171
theorem B1738817 : Blo 455782 1738817 := bstep (se 2 (by rfl) ⟨652056, by rfl⟩ : syracuseStep 1738817 = 1304113) B1304113
theorem B5572739 : Blo 455782 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B2197655 : Blo 455782 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B1542347 : Blo 455782 1542347 := bstep (se 1 (by rfl) ⟨1156760, by rfl⟩ : syracuseStep 1542347 = 2313521) B2313521
theorem B493975 : Blo 455782 493975 := bstep (se 1 (by rfl) ⟨370481, by rfl⟩ : syracuseStep 493975 = 740963) B740963
theorem B1542617 : Blo 455782 1542617 := bstep (se 2 (by rfl) ⟨578481, by rfl⟩ : syracuseStep 1542617 = 1156963) B1156963
theorem B3312485 : Blo 455782 3312485 := bstep (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) B621091
theorem B33852377 : Blo 455782 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B1543319 : Blo 455782 1543319 := bstep (se 1 (by rfl) ⟨1157489, by rfl⟩ : syracuseStep 1543319 = 2314979) B2314979
theorem B7048565 : Blo 455782 7048565 := bstep (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) B660803
theorem B1740305 : Blo 455782 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B1543859 : Blo 455782 1543859 := bstep (se 1 (by rfl) ⟨1157894, by rfl⟩ : syracuseStep 1543859 = 2315789) B2315789
theorem B4951813 : Blo 455782 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B1544129 : Blo 455782 1544129 := bstep (se 2 (by rfl) ⟨579048, by rfl⟩ : syracuseStep 1544129 = 1158097) B1158097
theorem B3706829 : Blo 455782 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B1740761 : Blo 455782 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B2920465 : Blo 455782 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B462871 : Blo 455782 462871 := bstep (se 1 (by rfl) ⟨347153, by rfl⟩ : syracuseStep 462871 = 694307) B694307
theorem B1740973 : Blo 455782 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B987329 : Blo 455782 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B3314125 : Blo 455782 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B1544669 : Blo 455782 1544669 := bstep (se 3 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 1544669 = 579251) B579251
theorem B1741277 : Blo 455782 1741277 := bstep (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) B652979
theorem B4690507 : Blo 455782 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B3969809 : Blo 455782 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B2200385 : Blo 455782 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B2200499 : Blo 455782 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B1643485 : Blo 455782 1643485 := bstep (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) B616307
theorem B3970225 : Blo 455782 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B464087 : Blo 455782 464087 := bstep (se 1 (by rfl) ⟨348065, by rfl⟩ : syracuseStep 464087 = 696131) B696131
theorem B496919 : Blo 455782 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B2790749 : Blo 455782 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B7542233 : Blo 455782 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B1545803 : Blo 455782 1545803 := bstep (se 1 (by rfl) ⟨1159352, by rfl⟩ : syracuseStep 1545803 = 2318705) B2318705
theorem B3348119 : Blo 455782 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2791091 : Blo 455782 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B497335 : Blo 455782 497335 := bstep (se 1 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 497335 = 746003) B746003
theorem B497387 : Blo 455782 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B1546073 : Blo 455782 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B825815 : Blo 455782 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B694745 : Blo 455782 694745 := bstep (se 2 (by rfl) ⟨260529, by rfl⟩ : syracuseStep 694745 = 521059) B521059
theorem B1546775 : Blo 455782 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B924185 : Blo 455782 924185 := bstep (se 2 (by rfl) ⟨346569, by rfl⟩ : syracuseStep 924185 = 693139) B693139
theorem B1874909 : Blo 455782 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B1743875 : Blo 455782 1743875 := bstep (se 1 (by rfl) ⟨1307906, by rfl⟩ : syracuseStep 1743875 = 2615813) B2615813
theorem B1743889 : Blo 455782 1743889 := bstep (se 2 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 1743889 = 1307917) B1307917
theorem B1547315 : Blo 455782 1547315 := bstep (se 1 (by rfl) ⟨1160486, by rfl⟩ : syracuseStep 1547315 = 2320973) B2320973
theorem B826571 : Blo 455782 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B1547585 : Blo 455782 1547585 := bstep (se 2 (by rfl) ⟨580344, by rfl⟩ : syracuseStep 1547585 = 1160689) B1160689
theorem B1744193 : Blo 455782 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B2465099 : Blo 455782 2465099 := bstep (se 1 (by rfl) ⟨1848824, by rfl⟩ : syracuseStep 2465099 = 3697649) B3697649
theorem B1154483 : Blo 455782 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B2006579 : Blo 455782 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B826969 : Blo 455782 826969 := bstep (se 2 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 826969 = 620227) B620227
theorem B2137745 : Blo 455782 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B2236177 : Blo 455782 2236177 := bstep (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) B1677133
theorem B1548125 : Blo 455782 1548125 := bstep (se 3 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 1548125 = 580547) B580547
theorem B1155019 : Blo 455782 1155019 := bstep (se 1 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 1155019 = 1732529) B1732529
theorem B1744861 : Blo 455782 1744861 := bstep (se 3 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 1744861 = 654323) B654323
theorem B1253399 : Blo 455782 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B1155161 : Blo 455782 1155161 := bstep (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) B866371
theorem B1646743 : Blo 455782 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B1647377 : Blo 455782 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B6595445 : Blo 455782 6595445 := bstep (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) B618323
theorem B1155991 : Blo 455782 1155991 := bstep (se 1 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 1155991 = 1733987) B1733987
theorem B1549259 : Blo 455782 1549259 := bstep (se 1 (by rfl) ⟨1161944, by rfl⟩ : syracuseStep 1549259 = 2323889) B2323889
theorem B2204633 : Blo 455782 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B1549529 : Blo 455782 1549529 := bstep (se 2 (by rfl) ⟨581073, by rfl⟩ : syracuseStep 1549529 = 1162147) B1162147
theorem B3286277 : Blo 455782 3286277 := bstep (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) B616177
theorem B1156427 : Blo 455782 1156427 := bstep (se 1 (by rfl) ⟨867320, by rfl⟩ : syracuseStep 1156427 = 1734641) B1734641
theorem B828929 : Blo 455782 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B3712529 : Blo 455782 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B1386035 : Blo 455782 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B1025675 : Blo 455782 1025675 := bstep (se 1 (by rfl) ⟨769256, by rfl⟩ : syracuseStep 1025675 = 1538513) B1538513
theorem B730777 : Blo 455782 730777 := bstep (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) B548083
theorem B1025729 : Blo 455782 1025729 := bstep (se 2 (by rfl) ⟨384648, by rfl⟩ : syracuseStep 1025729 = 769297) B769297
theorem B1156801 : Blo 455782 1156801 := bstep (se 2 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 1156801 = 867601) B867601
theorem B2598749 : Blo 455782 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B2828125 : Blo 455782 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B1648529 : Blo 455782 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B1550231 : Blo 455782 1550231 := bstep (se 1 (by rfl) ⟨1162673, by rfl⟩ : syracuseStep 1550231 = 2325347) B2325347
theorem B1025945 : Blo 455782 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B1026035 : Blo 455782 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B1026071 : Blo 455782 1026071 := bstep (se 1 (by rfl) ⟨769553, by rfl⟩ : syracuseStep 1026071 = 1539107) B1539107
theorem B9939095 : Blo 455782 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B3909809 : Blo 455782 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B1026251 : Blo 455782 1026251 := bstep (se 1 (by rfl) ⟨769688, by rfl⟩ : syracuseStep 1026251 = 1539377) B1539377
theorem B1026305 : Blo 455782 1026305 := bstep (se 2 (by rfl) ⟨384864, by rfl⟩ : syracuseStep 1026305 = 769729) B769729
theorem B1157399 : Blo 455782 1157399 := bstep (se 1 (by rfl) ⟨868049, by rfl⟩ : syracuseStep 1157399 = 1736099) B1736099
theorem B993665 : Blo 455782 993665 := bstep (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) B745249
theorem B1550771 : Blo 455782 1550771 := bstep (se 1 (by rfl) ⟨1163078, by rfl⟩ : syracuseStep 1550771 = 2326157) B2326157
theorem B1026521 : Blo 455782 1026521 := bstep (se 2 (by rfl) ⟨384945, by rfl⟩ : syracuseStep 1026521 = 769891) B769891
theorem B1026611 : Blo 455782 1026611 := bstep (se 1 (by rfl) ⟨769958, by rfl⟩ : syracuseStep 1026611 = 1539917) B1539917
theorem B1026647 : Blo 455782 1026647 := bstep (se 1 (by rfl) ⟨769985, by rfl⟩ : syracuseStep 1026647 = 1539971) B1539971
theorem B1551041 : Blo 455782 1551041 := bstep (se 2 (by rfl) ⟨581640, by rfl⟩ : syracuseStep 1551041 = 1163281) B1163281
theorem B928459 : Blo 455782 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B1780445 : Blo 455782 1780445 := bstep (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) B667667
theorem B1026827 : Blo 455782 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B928523 : Blo 455782 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B1026881 : Blo 455782 1026881 := bstep (se 2 (by rfl) ⟨385080, by rfl⟩ : syracuseStep 1026881 = 770161) B770161
theorem B1027097 : Blo 455782 1027097 := bstep (se 2 (by rfl) ⟨385161, by rfl⟩ : syracuseStep 1027097 = 770323) B770323
theorem B1158209 : Blo 455782 1158209 := bstep (se 2 (by rfl) ⟨434328, by rfl⟩ : syracuseStep 1158209 = 868657) B868657
theorem B15051845 : Blo 455782 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B1485899 : Blo 455782 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1027187 : Blo 455782 1027187 := bstep (se 1 (by rfl) ⟨770390, by rfl⟩ : syracuseStep 1027187 = 1540781) B1540781
theorem B1027223 : Blo 455782 1027223 := bstep (se 1 (by rfl) ⟨770417, by rfl⟩ : syracuseStep 1027223 = 1540835) B1540835
theorem B928921 : Blo 455782 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B1551581 : Blo 455782 1551581 := bstep (se 3 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 1551581 = 581843) B581843
theorem B1027403 : Blo 455782 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B1027457 : Blo 455782 1027457 := bstep (se 2 (by rfl) ⟨385296, by rfl⟩ : syracuseStep 1027457 = 770593) B770593
theorem B3485105 : Blo 455782 3485105 := bstep (se 2 (by rfl) ⟨1306914, by rfl⟩ : syracuseStep 3485105 = 2613829) B2613829
theorem B1027673 : Blo 455782 1027673 := bstep (se 2 (by rfl) ⟨385377, by rfl⟩ : syracuseStep 1027673 = 770755) B770755
theorem B1158745 : Blo 455782 1158745 := bstep (se 2 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 1158745 = 869059) B869059
theorem B1027763 : Blo 455782 1027763 := bstep (se 1 (by rfl) ⟨770822, by rfl⟩ : syracuseStep 1027763 = 1541645) B1541645
theorem B1027799 : Blo 455782 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B1027979 : Blo 455782 1027979 := bstep (se 1 (by rfl) ⟨770984, by rfl⟩ : syracuseStep 1027979 = 1541969) B1541969
theorem B3485591 : Blo 455782 3485591 := bstep (se 1 (by rfl) ⟨2614193, by rfl⟩ : syracuseStep 3485591 = 5228387) B5228387
theorem B1028033 : Blo 455782 1028033 := bstep (se 2 (by rfl) ⟨385512, by rfl⟩ : syracuseStep 1028033 = 771025) B771025
theorem B1028249 : Blo 455782 1028249 := bstep (se 2 (by rfl) ⟨385593, by rfl⟩ : syracuseStep 1028249 = 771187) B771187
theorem B1028339 : Blo 455782 1028339 := bstep (se 1 (by rfl) ⟨771254, by rfl⟩ : syracuseStep 1028339 = 1542509) B1542509
theorem B2601233 : Blo 455782 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B1028375 : Blo 455782 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B1028555 : Blo 455782 1028555 := bstep (se 1 (by rfl) ⟨771416, by rfl⟩ : syracuseStep 1028555 = 1542833) B1542833
theorem B1028609 : Blo 455782 1028609 := bstep (se 2 (by rfl) ⟨385728, by rfl⟩ : syracuseStep 1028609 = 771457) B771457
theorem B2929283 : Blo 455782 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B1159859 : Blo 455782 1159859 := bstep (se 1 (by rfl) ⟨869894, by rfl⟩ : syracuseStep 1159859 = 1739789) B1739789
theorem B1028825 : Blo 455782 1028825 := bstep (se 2 (by rfl) ⟨385809, by rfl⟩ : syracuseStep 1028825 = 771619) B771619
theorem B1028915 : Blo 455782 1028915 := bstep (se 1 (by rfl) ⟨771686, by rfl⟩ : syracuseStep 1028915 = 1543373) B1543373
theorem B1028951 : Blo 455782 1028951 := bstep (se 1 (by rfl) ⟨771713, by rfl⟩ : syracuseStep 1028951 = 1543427) B1543427
theorem B8827825 : Blo 455782 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B1160153 : Blo 455782 1160153 := bstep (se 2 (by rfl) ⟨435057, by rfl⟩ : syracuseStep 1160153 = 870115) B870115
theorem B1029131 : Blo 455782 1029131 := bstep (se 1 (by rfl) ⟨771848, by rfl⟩ : syracuseStep 1029131 = 1543697) B1543697
theorem B1029185 : Blo 455782 1029185 := bstep (se 2 (by rfl) ⟨385944, by rfl⟩ : syracuseStep 1029185 = 771889) B771889
theorem B3126545 : Blo 455782 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B865559 : Blo 455782 865559 := bstep (se 1 (by rfl) ⟨649169, by rfl⟩ : syracuseStep 865559 = 1298339) B1298339
theorem B1029401 : Blo 455782 1029401 := bstep (se 2 (by rfl) ⟨386025, by rfl⟩ : syracuseStep 1029401 = 772051) B772051
theorem B1029491 : Blo 455782 1029491 := bstep (se 1 (by rfl) ⟨772118, by rfl⟩ : syracuseStep 1029491 = 1544237) B1544237
theorem B1029527 : Blo 455782 1029527 := bstep (se 1 (by rfl) ⟨772145, by rfl⟩ : syracuseStep 1029527 = 1544291) B1544291
theorem B1029707 : Blo 455782 1029707 := bstep (se 1 (by rfl) ⟨772280, by rfl⟩ : syracuseStep 1029707 = 1544561) B1544561
theorem B734807 : Blo 455782 734807 := bstep (se 1 (by rfl) ⟨551105, by rfl⟩ : syracuseStep 734807 = 1102211) B1102211
theorem B1029761 : Blo 455782 1029761 := bstep (se 2 (by rfl) ⟨386160, by rfl⟩ : syracuseStep 1029761 = 772321) B772321
theorem B734935 : Blo 455782 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B3913433 : Blo 455782 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B734999 : Blo 455782 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B1029977 : Blo 455782 1029977 := bstep (se 2 (by rfl) ⟨386241, by rfl⟩ : syracuseStep 1029977 = 772483) B772483
theorem B866227 : Blo 455782 866227 := bstep (se 1 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 866227 = 1299341) B1299341
theorem B1030067 : Blo 455782 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B1030103 : Blo 455782 1030103 := bstep (se 1 (by rfl) ⟨772577, by rfl⟩ : syracuseStep 1030103 = 1545155) B1545155
theorem B1030283 : Blo 455782 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B1030337 : Blo 455782 1030337 := bstep (se 2 (by rfl) ⟨386376, by rfl⟩ : syracuseStep 1030337 = 772753) B772753
theorem B3291353 : Blo 455782 3291353 := bstep (se 2 (by rfl) ⟨1234257, by rfl⟩ : syracuseStep 3291353 = 2468515) B2468515
theorem B866675 : Blo 455782 866675 := bstep (se 1 (by rfl) ⟨650006, by rfl⟩ : syracuseStep 866675 = 1300013) B1300013
theorem B866713 : Blo 455782 866713 := bstep (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) B650035
theorem B1030553 : Blo 455782 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B1030643 : Blo 455782 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B1030679 : Blo 455782 1030679 := bstep (se 1 (by rfl) ⟨773009, by rfl⟩ : syracuseStep 1030679 = 1546019) B1546019
theorem B1161803 : Blo 455782 1161803 := bstep (se 1 (by rfl) ⟨871352, by rfl⟩ : syracuseStep 1161803 = 1742705) B1742705
theorem B1030859 : Blo 455782 1030859 := bstep (se 1 (by rfl) ⟨773144, by rfl⟩ : syracuseStep 1030859 = 1546289) B1546289
theorem B1030913 : Blo 455782 1030913 := bstep (se 2 (by rfl) ⟨386592, by rfl⟩ : syracuseStep 1030913 = 773185) B773185
theorem B1948481 : Blo 455782 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B867161 : Blo 455782 867161 := bstep (se 2 (by rfl) ⟨325185, by rfl⟩ : syracuseStep 867161 = 650371) B650371
theorem B1653635 : Blo 455782 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B1031129 : Blo 455782 1031129 := bstep (se 2 (by rfl) ⟨386673, by rfl⟩ : syracuseStep 1031129 = 773347) B773347
theorem B1031219 : Blo 455782 1031219 := bstep (se 1 (by rfl) ⟨773414, by rfl⟩ : syracuseStep 1031219 = 1546829) B1546829
theorem B1031255 : Blo 455782 1031255 := bstep (se 1 (by rfl) ⟨773441, by rfl⟩ : syracuseStep 1031255 = 1546883) B1546883
theorem B1948823 : Blo 455782 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B2473139 : Blo 455782 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B1031435 : Blo 455782 1031435 := bstep (se 1 (by rfl) ⟨773576, by rfl⟩ : syracuseStep 1031435 = 1547153) B1547153
theorem B1031489 : Blo 455782 1031489 := bstep (se 2 (by rfl) ⟨386808, by rfl⟩ : syracuseStep 1031489 = 773617) B773617
theorem B769547 : Blo 455782 769547 := bstep (se 1 (by rfl) ⟨577160, by rfl⟩ : syracuseStep 769547 = 1154321) B1154321
theorem B1162775 : Blo 455782 1162775 := bstep (se 1 (by rfl) ⟨872081, by rfl⟩ : syracuseStep 1162775 = 1744163) B1744163
theorem B1031705 : Blo 455782 1031705 := bstep (se 2 (by rfl) ⟨386889, by rfl⟩ : syracuseStep 1031705 = 773779) B773779
theorem B867905 : Blo 455782 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B1031795 : Blo 455782 1031795 := bstep (se 1 (by rfl) ⟨773846, by rfl⟩ : syracuseStep 1031795 = 1547693) B1547693
theorem B769675 : Blo 455782 769675 := bstep (se 1 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 769675 = 1154513) B1154513
theorem B1031831 : Blo 455782 1031831 := bstep (se 1 (by rfl) ⟨773873, by rfl⟩ : syracuseStep 1031831 = 1547747) B1547747
theorem B1392407 : Blo 455782 1392407 := bstep (se 1 (by rfl) ⟨1044305, by rfl⟩ : syracuseStep 1392407 = 2088611) B2088611
theorem B769817 : Blo 455782 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B868171 : Blo 455782 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B1032011 : Blo 455782 1032011 := bstep (se 1 (by rfl) ⟨774008, by rfl⟩ : syracuseStep 1032011 = 1548017) B1548017
theorem B1032065 : Blo 455782 1032065 := bstep (se 2 (by rfl) ⟨387024, by rfl⟩ : syracuseStep 1032065 = 774049) B774049
theorem B2080657 : Blo 455782 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B769945 : Blo 455782 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B1032281 : Blo 455782 1032281 := bstep (se 2 (by rfl) ⟨387105, by rfl⟩ : syracuseStep 1032281 = 774211) B774211
theorem B475255 : Blo 455782 475255 := bstep (se 1 (by rfl) ⟨356441, by rfl⟩ : syracuseStep 475255 = 712883) B712883
theorem B1032371 : Blo 455782 1032371 := bstep (se 1 (by rfl) ⟨774278, by rfl⟩ : syracuseStep 1032371 = 1548557) B1548557
theorem B1163443 : Blo 455782 1163443 := bstep (se 1 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 1163443 = 1745165) B1745165
theorem B1654987 : Blo 455782 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B1032407 : Blo 455782 1032407 := bstep (se 1 (by rfl) ⟨774305, by rfl⟩ : syracuseStep 1032407 = 1548611) B1548611
theorem B868619 : Blo 455782 868619 := bstep (se 1 (by rfl) ⟨651464, by rfl⟩ : syracuseStep 868619 = 1302929) B1302929
theorem B3916097 : Blo 455782 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B1163585 : Blo 455782 1163585 := bstep (se 2 (by rfl) ⟨436344, by rfl⟩ : syracuseStep 1163585 = 872689) B872689
theorem B1032587 : Blo 455782 1032587 := bstep (se 1 (by rfl) ⟨774440, by rfl⟩ : syracuseStep 1032587 = 1548881) B1548881
theorem B5226929 : Blo 455782 5226929 := bstep (se 2 (by rfl) ⟨1960098, by rfl⟩ : syracuseStep 5226929 = 3920197) B3920197
theorem B868801 : Blo 455782 868801 := bstep (se 2 (by rfl) ⟨325800, by rfl⟩ : syracuseStep 868801 = 651601) B651601
theorem B1032641 : Blo 455782 1032641 := bstep (se 2 (by rfl) ⟨387240, by rfl⟩ : syracuseStep 1032641 = 774481) B774481
theorem B770519 : Blo 455782 770519 := bstep (se 1 (by rfl) ⟨577889, by rfl⟩ : syracuseStep 770519 = 1155779) B1155779
theorem B3293713 : Blo 455782 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B770647 : Blo 455782 770647 := bstep (se 1 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 770647 = 1155971) B1155971
theorem B1032857 : Blo 455782 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B4440781 : Blo 455782 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B1032947 : Blo 455782 1032947 := bstep (se 1 (by rfl) ⟨774710, by rfl⟩ : syracuseStep 1032947 = 1549421) B1549421
theorem B2310929 : Blo 455782 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B869143 : Blo 455782 869143 := bstep (se 1 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 869143 = 1303715) B1303715
theorem B1032983 : Blo 455782 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B2311091 : Blo 455782 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B1033163 : Blo 455782 1033163 := bstep (se 1 (by rfl) ⟨774872, by rfl⟩ : syracuseStep 1033163 = 1549745) B1549745
theorem B1393625 : Blo 455782 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B869363 : Blo 455782 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B1033217 : Blo 455782 1033217 := bstep (se 2 (by rfl) ⟨387456, by rfl⟩ : syracuseStep 1033217 = 774913) B774913
theorem B771275 : Blo 455782 771275 := bstep (se 1 (by rfl) ⟨578456, by rfl⟩ : syracuseStep 771275 = 1156913) B1156913
theorem B869591 : Blo 455782 869591 := bstep (se 1 (by rfl) ⟨652193, by rfl⟩ : syracuseStep 869591 = 1304387) B1304387
theorem B1033433 : Blo 455782 1033433 := bstep (se 2 (by rfl) ⟨387537, by rfl⟩ : syracuseStep 1033433 = 775075) B775075
theorem B1950941 : Blo 455782 1950941 := bstep (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) B731603
theorem B1033523 : Blo 455782 1033523 := bstep (se 1 (by rfl) ⟨775142, by rfl⟩ : syracuseStep 1033523 = 1550285) B1550285
theorem B771403 : Blo 455782 771403 := bstep (se 1 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 771403 = 1157105) B1157105
theorem B1033559 : Blo 455782 1033559 := bstep (se 1 (by rfl) ⟨775169, by rfl⟩ : syracuseStep 1033559 = 1550339) B1550339
theorem B771545 : Blo 455782 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B869849 : Blo 455782 869849 := bstep (se 2 (by rfl) ⟨326193, by rfl⟩ : syracuseStep 869849 = 652387) B652387
theorem B1033739 : Blo 455782 1033739 := bstep (se 1 (by rfl) ⟨775304, by rfl⟩ : syracuseStep 1033739 = 1550609) B1550609
theorem B1951249 : Blo 455782 1951249 := bstep (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) B1463437
theorem B1951283 : Blo 455782 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B1033793 : Blo 455782 1033793 := bstep (se 2 (by rfl) ⟨387672, by rfl⟩ : syracuseStep 1033793 = 775345) B775345
theorem B771673 : Blo 455782 771673 := bstep (se 2 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 771673 = 578755) B578755
theorem B1034009 : Blo 455782 1034009 := bstep (se 2 (by rfl) ⟨387753, by rfl⟩ : syracuseStep 1034009 = 775507) B775507
theorem B2475821 : Blo 455782 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B870259 : Blo 455782 870259 := bstep (se 1 (by rfl) ⟨652694, by rfl⟩ : syracuseStep 870259 = 1305389) B1305389
theorem B1034099 : Blo 455782 1034099 := bstep (se 1 (by rfl) ⟨775574, by rfl⟩ : syracuseStep 1034099 = 1551149) B1551149
theorem B1034135 : Blo 455782 1034135 := bstep (se 1 (by rfl) ⟨775601, by rfl⟩ : syracuseStep 1034135 = 1551203) B1551203
theorem B2607065 : Blo 455782 2607065 := bstep (se 2 (by rfl) ⟨977649, by rfl⟩ : syracuseStep 2607065 = 1955299) B1955299
theorem B1034315 : Blo 455782 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B1099865 : Blo 455782 1099865 := bstep (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) B824899
theorem B1034369 : Blo 455782 1034369 := bstep (se 2 (by rfl) ⟨387888, by rfl⟩ : syracuseStep 1034369 = 775777) B775777
theorem B772247 : Blo 455782 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B772375 : Blo 455782 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B870745 : Blo 455782 870745 := bstep (se 2 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 870745 = 653059) B653059
theorem B707033 : Blo 455782 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1985303 : Blo 455782 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B1395521 : Blo 455782 1395521 := bstep (se 2 (by rfl) ⟨523320, by rfl⟩ : syracuseStep 1395521 = 1046641) B1046641
theorem B2313035 : Blo 455782 2313035 := bstep (se 1 (by rfl) ⟨1734776, by rfl⟩ : syracuseStep 2313035 = 3469553) B3469553
theorem B773003 : Blo 455782 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B871307 : Blo 455782 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B4967345 : Blo 455782 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B773131 : Blo 455782 773131 := bstep (se 1 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 773131 = 1159697) B1159697
theorem B871489 : Blo 455782 871489 := bstep (se 2 (by rfl) ⟨326808, by rfl⟩ : syracuseStep 871489 = 653617) B653617
theorem B2509955 : Blo 455782 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B773273 : Blo 455782 773273 := bstep (se 2 (by rfl) ⟨289977, by rfl⟩ : syracuseStep 773273 = 579955) B579955
theorem B773401 : Blo 455782 773401 := bstep (se 2 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 773401 = 580051) B580051
theorem B7851329 : Blo 455782 7851329 := bstep (se 2 (by rfl) ⟨2944248, by rfl⟩ : syracuseStep 7851329 = 5888497) B5888497
theorem B1953197 : Blo 455782 1953197 := bstep (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) B732449
theorem B576983 : Blo 455782 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B1756723 : Blo 455782 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B1298099 : Blo 455782 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B741079 : Blo 455782 741079 := bstep (se 1 (by rfl) ⟨555809, by rfl⟩ : syracuseStep 741079 = 1111619) B1111619
theorem B872203 : Blo 455782 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B773975 : Blo 455782 773975 := bstep (se 1 (by rfl) ⟨580481, by rfl⟩ : syracuseStep 773975 = 1160963) B1160963
theorem B872279 : Blo 455782 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B774103 : Blo 455782 774103 := bstep (se 1 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 774103 = 1161155) B1161155
theorem B1953881 : Blo 455782 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B577687 : Blo 455782 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B2314817 : Blo 455782 2314817 := bstep (se 2 (by rfl) ⟨868056, by rfl⟩ : syracuseStep 2314817 = 1736113) B1736113
theorem B2609729 : Blo 455782 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B774731 : Blo 455782 774731 := bstep (se 1 (by rfl) ⟨581048, by rfl⟩ : syracuseStep 774731 = 1162097) B1162097
theorem B774859 : Blo 455782 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B512779 : Blo 455782 512779 := bstep (se 1 (by rfl) ⟨384584, by rfl⟩ : syracuseStep 512779 = 769169) B769169
theorem B775001 : Blo 455782 775001 := bstep (se 2 (by rfl) ⟨290625, by rfl⟩ : syracuseStep 775001 = 581251) B581251
theorem B512887 : Blo 455782 512887 := bstep (se 1 (by rfl) ⟨384665, by rfl⟩ : syracuseStep 512887 = 769331) B769331
theorem B775129 : Blo 455782 775129 := bstep (se 2 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 775129 = 581347) B581347
theorem B513067 : Blo 455782 513067 := bstep (se 1 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 513067 = 769601) B769601
theorem B513175 : Blo 455782 513175 := bstep (se 1 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 513175 = 769763) B769763
theorem B1463513 : Blo 455782 1463513 := bstep (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) B1097635
theorem B1725761 : Blo 455782 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B513355 : Blo 455782 513355 := bstep (se 1 (by rfl) ⟨385016, by rfl⟩ : syracuseStep 513355 = 770033) B770033
theorem B513463 : Blo 455782 513463 := bstep (se 1 (by rfl) ⟨385097, by rfl⟩ : syracuseStep 513463 = 770195) B770195
theorem B775703 : Blo 455782 775703 := bstep (se 1 (by rfl) ⟨581777, by rfl⟩ : syracuseStep 775703 = 1163555) B1163555
theorem B3462749 : Blo 455782 3462749 := bstep (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) B1298531
theorem B513643 : Blo 455782 513643 := bstep (se 1 (by rfl) ⟨385232, by rfl⟩ : syracuseStep 513643 = 770465) B770465
theorem B775831 : Blo 455782 775831 := bstep (se 1 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 775831 = 1163747) B1163747
theorem B2086603 : Blo 455782 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B513751 : Blo 455782 513751 := bstep (se 1 (by rfl) ⟨385313, by rfl⟩ : syracuseStep 513751 = 770627) B770627
theorem B579403 : Blo 455782 579403 := bstep (se 1 (by rfl) ⟨434552, by rfl⟩ : syracuseStep 579403 = 869105) B869105
theorem B513931 : Blo 455782 513931 := bstep (se 1 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 513931 = 770897) B770897
theorem B1464257 : Blo 455782 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B1300445 : Blo 455782 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B514039 : Blo 455782 514039 := bstep (se 1 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 514039 = 771059) B771059
theorem B514219 : Blo 455782 514219 := bstep (se 1 (by rfl) ⟨385664, by rfl⟩ : syracuseStep 514219 = 771329) B771329
theorem B1300673 : Blo 455782 1300673 := bstep (se 2 (by rfl) ⟨487752, by rfl⟩ : syracuseStep 1300673 = 975505) B975505
theorem B3922181 : Blo 455782 3922181 := bstep (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) B735409
theorem B514327 : Blo 455782 514327 := bstep (se 1 (by rfl) ⟨385745, by rfl⟩ : syracuseStep 514327 = 771491) B771491
theorem B4413761 : Blo 455782 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B514507 : Blo 455782 514507 := bstep (se 1 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 514507 = 771761) B771761
theorem B2316761 : Blo 455782 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B1301015 : Blo 455782 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B514615 : Blo 455782 514615 := bstep (se 1 (by rfl) ⟨385961, by rfl⟩ : syracuseStep 514615 = 771923) B771923
theorem B1956545 : Blo 455782 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B6675149 : Blo 455782 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B514795 : Blo 455782 514795 := bstep (se 1 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 514795 = 772193) B772193
theorem B580375 : Blo 455782 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B5200685 : Blo 455782 5200685 := bstep (se 3 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 5200685 = 1950257) B1950257
theorem B3726125 : Blo 455782 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B514903 : Blo 455782 514903 := bstep (se 1 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 514903 = 772355) B772355
theorem B515083 : Blo 455782 515083 := bstep (se 1 (by rfl) ⟨386312, by rfl⟩ : syracuseStep 515083 = 772625) B772625
theorem B2939921 : Blo 455782 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B515191 : Blo 455782 515191 := bstep (se 1 (by rfl) ⟨386393, by rfl⟩ : syracuseStep 515191 = 772787) B772787
theorem B1236161 : Blo 455782 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B2481425 : Blo 455782 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B515371 : Blo 455782 515371 := bstep (se 1 (by rfl) ⟨386528, by rfl⟩ : syracuseStep 515371 = 773057) B773057
theorem B941399 : Blo 455782 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B119922061 : Blo 455782 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B515479 : Blo 455782 515479 := bstep (se 1 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 515479 = 773219) B773219
theorem B548299 : Blo 455782 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B7790093 : Blo 455782 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B515659 : Blo 455782 515659 := bstep (se 1 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 515659 = 773489) B773489
theorem B581195 : Blo 455782 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B515767 : Blo 455782 515767 := bstep (se 1 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 515767 = 773651) B773651
theorem B1171223 : Blo 455782 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B515947 : Blo 455782 515947 := bstep (se 1 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 515947 = 773921) B773921
theorem B516055 : Blo 455782 516055 := bstep (se 1 (by rfl) ⟨387041, by rfl⟩ : syracuseStep 516055 = 774083) B774083
theorem B1466333 : Blo 455782 1466333 := bstep (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) B549875
theorem B2318381 : Blo 455782 2318381 := bstep (se 3 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 2318381 = 869393) B869393
theorem B5267587 : Blo 455782 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B516235 : Blo 455782 516235 := bstep (se 1 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 516235 = 774353) B774353
theorem B1958033 : Blo 455782 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B516343 : Blo 455782 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B581899 : Blo 455782 581899 := bstep (se 1 (by rfl) ⟨436424, by rfl⟩ : syracuseStep 581899 = 872849) B872849
theorem B942401 : Blo 455782 942401 := bstep (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) B706801
theorem B8348021 : Blo 455782 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B516523 : Blo 455782 516523 := bstep (se 1 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 516523 = 774785) B774785
theorem B516631 : Blo 455782 516631 := bstep (se 1 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 516631 = 774947) B774947
theorem B1860241 : Blo 455782 1860241 := bstep (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) B1395181
theorem B975539 : Blo 455782 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B516811 : Blo 455782 516811 := bstep (se 1 (by rfl) ⟨387608, by rfl⟩ : syracuseStep 516811 = 775217) B775217
theorem B516919 : Blo 455782 516919 := bstep (se 1 (by rfl) ⟨387689, by rfl⟩ : syracuseStep 516919 = 775379) B775379
theorem B1303361 : Blo 455782 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B8479667 : Blo 455782 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B517099 : Blo 455782 517099 := bstep (se 1 (by rfl) ⟨387824, by rfl⟩ : syracuseStep 517099 = 775649) B775649
theorem B517207 : Blo 455782 517207 := bstep (se 1 (by rfl) ⟨387905, by rfl⟩ : syracuseStep 517207 = 775811) B775811
theorem B1959005 : Blo 455782 1959005 := bstep (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) B734627
theorem B1303897 : Blo 455782 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B3696023 : Blo 455782 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B2352563 : Blo 455782 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B8381875 : Blo 455782 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B2615105 : Blo 455782 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B976855 : Blo 455782 976855 := bstep (se 1 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 976855 = 1465283) B1465283
theorem B977035 : Blo 455782 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B1730753 : Blo 455782 1730753 := bstep (se 2 (by rfl) ⟨649032, by rfl⟩ : syracuseStep 1730753 = 1298065) B1298065
theorem B7432397 : Blo 455782 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B977111 : Blo 455782 977111 := bstep (se 1 (by rfl) ⟨732833, by rfl⟩ : syracuseStep 977111 = 1465667) B1465667
theorem B2779609 : Blo 455782 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B3697483 : Blo 455782 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B650263 : Blo 455782 650263 := bstep (se 1 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 650263 = 975395) B975395
theorem B1305821 : Blo 455782 1305821 := bstep (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) B489683
theorem B5860613 : Blo 455782 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B781643 : Blo 455782 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B1732013 : Blo 455782 1732013 := bstep (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) B649505
theorem B3698099 : Blo 455782 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B1732043 : Blo 455782 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B1961603 : Blo 455782 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B683723 : Blo 455782 683723 := bstep (se 1 (by rfl) ⟨512792, by rfl⟩ : syracuseStep 683723 = 1025585) B1025585
theorem B683735 : Blo 455782 683735 := bstep (se 1 (by rfl) ⟨512801, by rfl⟩ : syracuseStep 683735 = 1025603) B1025603
theorem B683801 : Blo 455782 683801 := bstep (se 2 (by rfl) ⟨256425, by rfl⟩ : syracuseStep 683801 = 512851) B512851
theorem B2322269 : Blo 455782 2322269 := bstep (se 3 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 2322269 = 870851) B870851
theorem B683915 : Blo 455782 683915 := bstep (se 1 (by rfl) ⟨512936, by rfl⟩ : syracuseStep 683915 = 1025873) B1025873
theorem B683927 : Blo 455782 683927 := bstep (se 1 (by rfl) ⟨512945, by rfl⟩ : syracuseStep 683927 = 1025891) B1025891
theorem B683993 : Blo 455782 683993 := bstep (se 2 (by rfl) ⟨256497, by rfl⟩ : syracuseStep 683993 = 512995) B512995
theorem B978905 : Blo 455782 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B1961945 : Blo 455782 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B782347 : Blo 455782 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B2945069 : Blo 455782 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B684107 : Blo 455782 684107 := bstep (se 1 (by rfl) ⟨513080, by rfl⟩ : syracuseStep 684107 = 1026161) B1026161
theorem B684119 : Blo 455782 684119 := bstep (se 1 (by rfl) ⟨513089, by rfl⟩ : syracuseStep 684119 = 1026179) B1026179
theorem B1732697 : Blo 455782 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B3174551 : Blo 455782 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B684185 : Blo 455782 684185 := bstep (se 2 (by rfl) ⟨256569, by rfl⟩ : syracuseStep 684185 = 513139) B513139
theorem B684299 : Blo 455782 684299 := bstep (se 1 (by rfl) ⟨513224, by rfl⟩ : syracuseStep 684299 = 1026449) B1026449
theorem B684311 : Blo 455782 684311 := bstep (se 1 (by rfl) ⟨513233, by rfl⟩ : syracuseStep 684311 = 1026467) B1026467
theorem B684377 : Blo 455782 684377 := bstep (se 2 (by rfl) ⟨256641, by rfl⟩ : syracuseStep 684377 = 513283) B513283
theorem B1733015 : Blo 455782 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B684491 : Blo 455782 684491 := bstep (se 1 (by rfl) ⟨513368, by rfl⟩ : syracuseStep 684491 = 1026737) B1026737
theorem B684503 : Blo 455782 684503 := bstep (se 1 (by rfl) ⟨513377, by rfl⟩ : syracuseStep 684503 = 1026755) B1026755
theorem B684569 : Blo 455782 684569 := bstep (se 2 (by rfl) ⟨256713, by rfl⟩ : syracuseStep 684569 = 513427) B513427
theorem B13529693 : Blo 455782 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B979571 : Blo 455782 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B684683 : Blo 455782 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B684695 : Blo 455782 684695 := bstep (se 1 (by rfl) ⟨513521, by rfl⟩ : syracuseStep 684695 = 1027043) B1027043
theorem B684761 : Blo 455782 684761 := bstep (se 2 (by rfl) ⟨256785, by rfl⟩ : syracuseStep 684761 = 513571) B513571
theorem B684875 : Blo 455782 684875 := bstep (se 1 (by rfl) ⟨513656, by rfl⟩ : syracuseStep 684875 = 1027313) B1027313
theorem B684887 : Blo 455782 684887 := bstep (se 1 (by rfl) ⟨513665, by rfl⟩ : syracuseStep 684887 = 1027331) B1027331
theorem B684953 : Blo 455782 684953 := bstep (se 2 (by rfl) ⟨256857, by rfl⟩ : syracuseStep 684953 = 513715) B513715
theorem B685067 : Blo 455782 685067 := bstep (se 1 (by rfl) ⟨513800, by rfl⟩ : syracuseStep 685067 = 1027601) B1027601
theorem B685079 : Blo 455782 685079 := bstep (se 1 (by rfl) ⟨513809, by rfl⟩ : syracuseStep 685079 = 1027619) B1027619
theorem B881687 : Blo 455782 881687 := bstep (se 1 (by rfl) ⟨661265, by rfl⟩ : syracuseStep 881687 = 1322531) B1322531
theorem B652313 : Blo 455782 652313 := bstep (se 2 (by rfl) ⟨244617, by rfl⟩ : syracuseStep 652313 = 489235) B489235
theorem B1733683 : Blo 455782 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B685145 : Blo 455782 685145 := bstep (se 2 (by rfl) ⟨256929, by rfl⟩ : syracuseStep 685145 = 513859) B513859
theorem B455787 : Blo 455782 455787 := bstep (se 1 (by rfl) ⟨341840, by rfl⟩ : syracuseStep 455787 = 683681) B683681
theorem B455799 : Blo 455782 455799 := bstep (se 1 (by rfl) ⟨341849, by rfl⟩ : syracuseStep 455799 = 683699) B683699
theorem B455819 : Blo 455782 455819 := bstep (se 1 (by rfl) ⟨341864, by rfl⟩ : syracuseStep 455819 = 683729) B683729
theorem B455831 : Blo 455782 455831 := bstep (se 1 (by rfl) ⟨341873, by rfl⟩ : syracuseStep 455831 = 683747) B683747
theorem B455851 : Blo 455782 455851 := bstep (se 1 (by rfl) ⟨341888, by rfl⟩ : syracuseStep 455851 = 683777) B683777
theorem B455863 : Blo 455782 455863 := bstep (se 1 (by rfl) ⟨341897, by rfl⟩ : syracuseStep 455863 = 683795) B683795
theorem B455883 : Blo 455782 455883 := bstep (se 1 (by rfl) ⟨341912, by rfl⟩ : syracuseStep 455883 = 683825) B683825
theorem B685259 : Blo 455782 685259 := bstep (se 1 (by rfl) ⟨513944, by rfl⟩ : syracuseStep 685259 = 1027889) B1027889
theorem B455895 : Blo 455782 455895 := bstep (se 1 (by rfl) ⟨341921, by rfl⟩ : syracuseStep 455895 = 683843) B683843
theorem B685271 : Blo 455782 685271 := bstep (se 1 (by rfl) ⟨513953, by rfl⟩ : syracuseStep 685271 = 1027907) B1027907
theorem B455915 : Blo 455782 455915 := bstep (se 1 (by rfl) ⟨341936, by rfl⟩ : syracuseStep 455915 = 683873) B683873
theorem B455927 : Blo 455782 455927 := bstep (se 1 (by rfl) ⟨341945, by rfl⟩ : syracuseStep 455927 = 683891) B683891
theorem B455947 : Blo 455782 455947 := bstep (se 1 (by rfl) ⟨341960, by rfl⟩ : syracuseStep 455947 = 683921) B683921
theorem B455959 : Blo 455782 455959 := bstep (se 1 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 455959 = 683939) B683939
theorem B685337 : Blo 455782 685337 := bstep (se 2 (by rfl) ⟨257001, by rfl⟩ : syracuseStep 685337 = 514003) B514003
theorem B455979 : Blo 455782 455979 := bstep (se 1 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 455979 = 683969) B683969
theorem B455991 : Blo 455782 455991 := bstep (se 1 (by rfl) ⟨341993, by rfl⟩ : syracuseStep 455991 = 683987) B683987
theorem B456011 : Blo 455782 456011 := bstep (se 1 (by rfl) ⟨342008, by rfl⟩ : syracuseStep 456011 = 684017) B684017
theorem B456023 : Blo 455782 456023 := bstep (se 1 (by rfl) ⟨342017, by rfl⟩ : syracuseStep 456023 = 684035) B684035
theorem B488791 : Blo 455782 488791 := bstep (se 1 (by rfl) ⟨366593, by rfl⟩ : syracuseStep 488791 = 733187) B733187
theorem B456043 : Blo 455782 456043 := bstep (se 1 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 456043 = 684065) B684065
theorem B456055 : Blo 455782 456055 := bstep (se 1 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 456055 = 684083) B684083
theorem B456075 : Blo 455782 456075 := bstep (se 1 (by rfl) ⟨342056, by rfl⟩ : syracuseStep 456075 = 684113) B684113
theorem B685451 : Blo 455782 685451 := bstep (se 1 (by rfl) ⟨514088, by rfl⟩ : syracuseStep 685451 = 1028177) B1028177
theorem B456087 : Blo 455782 456087 := bstep (se 1 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 456087 = 684131) B684131
theorem B685463 : Blo 455782 685463 := bstep (se 1 (by rfl) ⟨514097, by rfl⟩ : syracuseStep 685463 = 1028195) B1028195
theorem B456107 : Blo 455782 456107 := bstep (se 1 (by rfl) ⟨342080, by rfl⟩ : syracuseStep 456107 = 684161) B684161
theorem B456119 : Blo 455782 456119 := bstep (se 1 (by rfl) ⟨342089, by rfl⟩ : syracuseStep 456119 = 684179) B684179
theorem B456139 : Blo 455782 456139 := bstep (se 1 (by rfl) ⟨342104, by rfl⟩ : syracuseStep 456139 = 684209) B684209
theorem B456151 : Blo 455782 456151 := bstep (se 1 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 456151 = 684227) B684227
theorem B685529 : Blo 455782 685529 := bstep (se 2 (by rfl) ⟨257073, by rfl⟩ : syracuseStep 685529 = 514147) B514147
theorem B456171 : Blo 455782 456171 := bstep (se 1 (by rfl) ⟨342128, by rfl⟩ : syracuseStep 456171 = 684257) B684257
theorem B456183 : Blo 455782 456183 := bstep (se 1 (by rfl) ⟨342137, by rfl⟩ : syracuseStep 456183 = 684275) B684275
theorem B456203 : Blo 455782 456203 := bstep (se 1 (by rfl) ⟨342152, by rfl⟩ : syracuseStep 456203 = 684305) B684305
theorem B456215 : Blo 455782 456215 := bstep (se 1 (by rfl) ⟨342161, by rfl⟩ : syracuseStep 456215 = 684323) B684323
theorem B456235 : Blo 455782 456235 := bstep (se 1 (by rfl) ⟨342176, by rfl⟩ : syracuseStep 456235 = 684353) B684353
theorem B456247 : Blo 455782 456247 := bstep (se 1 (by rfl) ⟨342185, by rfl⟩ : syracuseStep 456247 = 684371) B684371
theorem B456267 : Blo 455782 456267 := bstep (se 1 (by rfl) ⟨342200, by rfl⟩ : syracuseStep 456267 = 684401) B684401
theorem B685643 : Blo 455782 685643 := bstep (se 1 (by rfl) ⟨514232, by rfl⟩ : syracuseStep 685643 = 1028465) B1028465
theorem B456279 : Blo 455782 456279 := bstep (se 1 (by rfl) ⟨342209, by rfl⟩ : syracuseStep 456279 = 684419) B684419
theorem B685655 : Blo 455782 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B456299 : Blo 455782 456299 := bstep (se 1 (by rfl) ⟨342224, by rfl⟩ : syracuseStep 456299 = 684449) B684449
theorem B456311 : Blo 455782 456311 := bstep (se 1 (by rfl) ⟨342233, by rfl⟩ : syracuseStep 456311 = 684467) B684467
theorem B456331 : Blo 455782 456331 := bstep (se 1 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 456331 = 684497) B684497
theorem B4159127 : Blo 455782 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B456343 : Blo 455782 456343 := bstep (se 1 (by rfl) ⟨342257, by rfl⟩ : syracuseStep 456343 = 684515) B684515
theorem B685721 : Blo 455782 685721 := bstep (se 2 (by rfl) ⟨257145, by rfl⟩ : syracuseStep 685721 = 514291) B514291
theorem B652951 : Blo 455782 652951 := bstep (se 1 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 652951 = 979427) B979427
theorem B456363 : Blo 455782 456363 := bstep (se 1 (by rfl) ⟨342272, by rfl⟩ : syracuseStep 456363 = 684545) B684545
theorem B456375 : Blo 455782 456375 := bstep (se 1 (by rfl) ⟨342281, by rfl⟩ : syracuseStep 456375 = 684563) B684563
theorem B456395 : Blo 455782 456395 := bstep (se 1 (by rfl) ⟨342296, by rfl⟩ : syracuseStep 456395 = 684593) B684593
theorem B456407 : Blo 455782 456407 := bstep (se 1 (by rfl) ⟨342305, by rfl⟩ : syracuseStep 456407 = 684611) B684611
theorem B456427 : Blo 455782 456427 := bstep (se 1 (by rfl) ⟨342320, by rfl⟩ : syracuseStep 456427 = 684641) B684641
theorem B456439 : Blo 455782 456439 := bstep (se 1 (by rfl) ⟨342329, by rfl⟩ : syracuseStep 456439 = 684659) B684659
theorem B456459 : Blo 455782 456459 := bstep (se 1 (by rfl) ⟨342344, by rfl⟩ : syracuseStep 456459 = 684689) B684689
theorem B685835 : Blo 455782 685835 := bstep (se 1 (by rfl) ⟨514376, by rfl⟩ : syracuseStep 685835 = 1028753) B1028753
theorem B456471 : Blo 455782 456471 := bstep (se 1 (by rfl) ⟨342353, by rfl⟩ : syracuseStep 456471 = 684707) B684707
theorem B685847 : Blo 455782 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B456491 : Blo 455782 456491 := bstep (se 1 (by rfl) ⟨342368, by rfl⟩ : syracuseStep 456491 = 684737) B684737
theorem B456503 : Blo 455782 456503 := bstep (se 1 (by rfl) ⟨342377, by rfl⟩ : syracuseStep 456503 = 684755) B684755
theorem B456523 : Blo 455782 456523 := bstep (se 1 (by rfl) ⟨342392, by rfl⟩ : syracuseStep 456523 = 684785) B684785
theorem B456535 : Blo 455782 456535 := bstep (se 1 (by rfl) ⟨342401, by rfl⟩ : syracuseStep 456535 = 684803) B684803
theorem B685913 : Blo 455782 685913 := bstep (se 2 (by rfl) ⟨257217, by rfl⟩ : syracuseStep 685913 = 514435) B514435
theorem B456555 : Blo 455782 456555 := bstep (se 1 (by rfl) ⟨342416, by rfl⟩ : syracuseStep 456555 = 684833) B684833
theorem B456567 : Blo 455782 456567 := bstep (se 1 (by rfl) ⟨342425, by rfl⟩ : syracuseStep 456567 = 684851) B684851
theorem B456587 : Blo 455782 456587 := bstep (se 1 (by rfl) ⟨342440, by rfl⟩ : syracuseStep 456587 = 684881) B684881
theorem B456599 : Blo 455782 456599 := bstep (se 1 (by rfl) ⟨342449, by rfl⟩ : syracuseStep 456599 = 684899) B684899
theorem B2324375 : Blo 455782 2324375 := bstep (se 1 (by rfl) ⟨1743281, by rfl⟩ : syracuseStep 2324375 = 3486563) B3486563
theorem B456619 : Blo 455782 456619 := bstep (se 1 (by rfl) ⟨342464, by rfl⟩ : syracuseStep 456619 = 684929) B684929
theorem B456631 : Blo 455782 456631 := bstep (se 1 (by rfl) ⟨342473, by rfl⟩ : syracuseStep 456631 = 684947) B684947
theorem B456651 : Blo 455782 456651 := bstep (se 1 (by rfl) ⟨342488, by rfl⟩ : syracuseStep 456651 = 684977) B684977
theorem B686027 : Blo 455782 686027 := bstep (se 1 (by rfl) ⟨514520, by rfl⟩ : syracuseStep 686027 = 1029041) B1029041
theorem B456663 : Blo 455782 456663 := bstep (se 1 (by rfl) ⟨342497, by rfl⟩ : syracuseStep 456663 = 684995) B684995
theorem B686039 : Blo 455782 686039 := bstep (se 1 (by rfl) ⟨514529, by rfl⟩ : syracuseStep 686039 = 1029059) B1029059
theorem B456683 : Blo 455782 456683 := bstep (se 1 (by rfl) ⟨342512, by rfl⟩ : syracuseStep 456683 = 685025) B685025
theorem B456695 : Blo 455782 456695 := bstep (se 1 (by rfl) ⟨342521, by rfl⟩ : syracuseStep 456695 = 685043) B685043
theorem B456715 : Blo 455782 456715 := bstep (se 1 (by rfl) ⟨342536, by rfl⟩ : syracuseStep 456715 = 685073) B685073
theorem B456727 : Blo 455782 456727 := bstep (se 1 (by rfl) ⟨342545, by rfl⟩ : syracuseStep 456727 = 685091) B685091
theorem B686105 : Blo 455782 686105 := bstep (se 2 (by rfl) ⟨257289, by rfl⟩ : syracuseStep 686105 = 514579) B514579
theorem B456747 : Blo 455782 456747 := bstep (se 1 (by rfl) ⟨342560, by rfl⟩ : syracuseStep 456747 = 685121) B685121
theorem B456759 : Blo 455782 456759 := bstep (se 1 (by rfl) ⟨342569, by rfl⟩ : syracuseStep 456759 = 685139) B685139
theorem B1308737 : Blo 455782 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B456779 : Blo 455782 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B981067 : Blo 455782 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B456791 : Blo 455782 456791 := bstep (se 1 (by rfl) ⟨342593, by rfl⟩ : syracuseStep 456791 = 685187) B685187
theorem B1308761 : Blo 455782 1308761 := bstep (se 2 (by rfl) ⟨490785, by rfl⟩ : syracuseStep 1308761 = 981571) B981571
theorem B456811 : Blo 455782 456811 := bstep (se 1 (by rfl) ⟨342608, by rfl⟩ : syracuseStep 456811 = 685217) B685217
theorem B456823 : Blo 455782 456823 := bstep (se 1 (by rfl) ⟨342617, by rfl⟩ : syracuseStep 456823 = 685235) B685235
theorem B489611 : Blo 455782 489611 := bstep (se 1 (by rfl) ⟨367208, by rfl⟩ : syracuseStep 489611 = 734417) B734417
theorem B456843 : Blo 455782 456843 := bstep (se 1 (by rfl) ⟨342632, by rfl⟩ : syracuseStep 456843 = 685265) B685265
theorem B686219 : Blo 455782 686219 := bstep (se 1 (by rfl) ⟨514664, by rfl⟩ : syracuseStep 686219 = 1029329) B1029329
theorem B456855 : Blo 455782 456855 := bstep (se 1 (by rfl) ⟨342641, by rfl⟩ : syracuseStep 456855 = 685283) B685283
theorem B686231 : Blo 455782 686231 := bstep (se 1 (by rfl) ⟨514673, by rfl⟩ : syracuseStep 686231 = 1029347) B1029347
theorem B11303063 : Blo 455782 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B456875 : Blo 455782 456875 := bstep (se 1 (by rfl) ⟨342656, by rfl⟩ : syracuseStep 456875 = 685313) B685313
theorem B456887 : Blo 455782 456887 := bstep (se 1 (by rfl) ⟨342665, by rfl⟩ : syracuseStep 456887 = 685331) B685331
theorem B456907 : Blo 455782 456907 := bstep (se 1 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 456907 = 685361) B685361
theorem B456919 : Blo 455782 456919 := bstep (se 1 (by rfl) ⟨342689, by rfl⟩ : syracuseStep 456919 = 685379) B685379
theorem B686297 : Blo 455782 686297 := bstep (se 2 (by rfl) ⟨257361, by rfl⟩ : syracuseStep 686297 = 514723) B514723
theorem B456939 : Blo 455782 456939 := bstep (se 1 (by rfl) ⟨342704, by rfl⟩ : syracuseStep 456939 = 685409) B685409
theorem B456951 : Blo 455782 456951 := bstep (se 1 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 456951 = 685427) B685427
theorem B456971 : Blo 455782 456971 := bstep (se 1 (by rfl) ⟨342728, by rfl⟩ : syracuseStep 456971 = 685457) B685457
theorem B1734929 : Blo 455782 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B456983 : Blo 455782 456983 := bstep (se 1 (by rfl) ⟨342737, by rfl⟩ : syracuseStep 456983 = 685475) B685475
theorem B457003 : Blo 455782 457003 := bstep (se 1 (by rfl) ⟨342752, by rfl⟩ : syracuseStep 457003 = 685505) B685505
theorem B457015 : Blo 455782 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B457035 : Blo 455782 457035 := bstep (se 1 (by rfl) ⟨342776, by rfl⟩ : syracuseStep 457035 = 685553) B685553
theorem B686411 : Blo 455782 686411 := bstep (se 1 (by rfl) ⟨514808, by rfl⟩ : syracuseStep 686411 = 1029617) B1029617
theorem B1472843 : Blo 455782 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B457047 : Blo 455782 457047 := bstep (se 1 (by rfl) ⟨342785, by rfl⟩ : syracuseStep 457047 = 685571) B685571
theorem B686423 : Blo 455782 686423 := bstep (se 1 (by rfl) ⟨514817, by rfl⟩ : syracuseStep 686423 = 1029635) B1029635
theorem B457067 : Blo 455782 457067 := bstep (se 1 (by rfl) ⟨342800, by rfl⟩ : syracuseStep 457067 = 685601) B685601
theorem B457079 : Blo 455782 457079 := bstep (se 1 (by rfl) ⟨342809, by rfl⟩ : syracuseStep 457079 = 685619) B685619
theorem B457099 : Blo 455782 457099 := bstep (se 1 (by rfl) ⟨342824, by rfl⟩ : syracuseStep 457099 = 685649) B685649
theorem B457111 : Blo 455782 457111 := bstep (se 1 (by rfl) ⟨342833, by rfl⟩ : syracuseStep 457111 = 685667) B685667
theorem B686489 : Blo 455782 686489 := bstep (se 2 (by rfl) ⟨257433, by rfl⟩ : syracuseStep 686489 = 514867) B514867
theorem B457131 : Blo 455782 457131 := bstep (se 1 (by rfl) ⟨342848, by rfl⟩ : syracuseStep 457131 = 685697) B685697
theorem B457143 : Blo 455782 457143 := bstep (se 1 (by rfl) ⟨342857, by rfl⟩ : syracuseStep 457143 = 685715) B685715
theorem B457163 : Blo 455782 457163 := bstep (se 1 (by rfl) ⟨342872, by rfl⟩ : syracuseStep 457163 = 685745) B685745
theorem B653771 : Blo 455782 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B457175 : Blo 455782 457175 := bstep (se 1 (by rfl) ⟨342881, by rfl⟩ : syracuseStep 457175 = 685763) B685763
theorem B457195 : Blo 455782 457195 := bstep (se 1 (by rfl) ⟨342896, by rfl⟩ : syracuseStep 457195 = 685793) B685793
theorem B457207 : Blo 455782 457207 := bstep (se 1 (by rfl) ⟨342905, by rfl⟩ : syracuseStep 457207 = 685811) B685811
theorem B457227 : Blo 455782 457227 := bstep (se 1 (by rfl) ⟨342920, by rfl⟩ : syracuseStep 457227 = 685841) B685841
theorem B686603 : Blo 455782 686603 := bstep (se 1 (by rfl) ⟨514952, by rfl⟩ : syracuseStep 686603 = 1029905) B1029905
theorem B457239 : Blo 455782 457239 := bstep (se 1 (by rfl) ⟨342929, by rfl⟩ : syracuseStep 457239 = 685859) B685859
theorem B686615 : Blo 455782 686615 := bstep (se 1 (by rfl) ⟨514961, by rfl⟩ : syracuseStep 686615 = 1029923) B1029923
theorem B457259 : Blo 455782 457259 := bstep (se 1 (by rfl) ⟨342944, by rfl⟩ : syracuseStep 457259 = 685889) B685889
theorem B2193965 : Blo 455782 2193965 := bstep (se 3 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 2193965 = 822737) B822737
theorem B457271 : Blo 455782 457271 := bstep (se 1 (by rfl) ⟨342953, by rfl⟩ : syracuseStep 457271 = 685907) B685907
theorem B457291 : Blo 455782 457291 := bstep (se 1 (by rfl) ⟨342968, by rfl⟩ : syracuseStep 457291 = 685937) B685937
theorem B457303 : Blo 455782 457303 := bstep (se 1 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 457303 = 685955) B685955
theorem B686681 : Blo 455782 686681 := bstep (se 2 (by rfl) ⟨257505, by rfl⟩ : syracuseStep 686681 = 515011) B515011
theorem B2226781 : Blo 455782 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B457323 : Blo 455782 457323 := bstep (se 1 (by rfl) ⟨342992, by rfl⟩ : syracuseStep 457323 = 685985) B685985
theorem B457335 : Blo 455782 457335 := bstep (se 1 (by rfl) ⟨343001, by rfl⟩ : syracuseStep 457335 = 686003) B686003
theorem B457355 : Blo 455782 457355 := bstep (se 1 (by rfl) ⟨343016, by rfl⟩ : syracuseStep 457355 = 686033) B686033
theorem B457367 : Blo 455782 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B457387 : Blo 455782 457387 := bstep (se 1 (by rfl) ⟨343040, by rfl⟩ : syracuseStep 457387 = 686081) B686081
theorem B457399 : Blo 455782 457399 := bstep (se 1 (by rfl) ⟨343049, by rfl⟩ : syracuseStep 457399 = 686099) B686099
theorem B457419 : Blo 455782 457419 := bstep (se 1 (by rfl) ⟨343064, by rfl⟩ : syracuseStep 457419 = 686129) B686129
theorem B686795 : Blo 455782 686795 := bstep (se 1 (by rfl) ⟨515096, by rfl⟩ : syracuseStep 686795 = 1030193) B1030193
theorem B8321741 : Blo 455782 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B1178315 : Blo 455782 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B457431 : Blo 455782 457431 := bstep (se 1 (by rfl) ⟨343073, by rfl⟩ : syracuseStep 457431 = 686147) B686147
theorem B686807 : Blo 455782 686807 := bstep (se 1 (by rfl) ⟨515105, by rfl⟩ : syracuseStep 686807 = 1030211) B1030211
theorem B457451 : Blo 455782 457451 := bstep (se 1 (by rfl) ⟨343088, by rfl⟩ : syracuseStep 457451 = 686177) B686177
theorem B457463 : Blo 455782 457463 := bstep (se 1 (by rfl) ⟨343097, by rfl⟩ : syracuseStep 457463 = 686195) B686195
theorem B457483 : Blo 455782 457483 := bstep (se 1 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 457483 = 686225) B686225
theorem B457495 : Blo 455782 457495 := bstep (se 1 (by rfl) ⟨343121, by rfl⟩ : syracuseStep 457495 = 686243) B686243
theorem B686873 : Blo 455782 686873 := bstep (se 2 (by rfl) ⟨257577, by rfl⟩ : syracuseStep 686873 = 515155) B515155
theorem B457515 : Blo 455782 457515 := bstep (se 1 (by rfl) ⟨343136, by rfl⟩ : syracuseStep 457515 = 686273) B686273
theorem B457527 : Blo 455782 457527 := bstep (se 1 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 457527 = 686291) B686291
theorem B1538891 : Blo 455782 1538891 := bstep (se 1 (by rfl) ⟨1154168, by rfl⟩ : syracuseStep 1538891 = 2308337) B2308337
theorem B457547 : Blo 455782 457547 := bstep (se 1 (by rfl) ⟨343160, by rfl⟩ : syracuseStep 457547 = 686321) B686321
theorem B3308363 : Blo 455782 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B457559 : Blo 455782 457559 := bstep (se 1 (by rfl) ⟨343169, by rfl⟩ : syracuseStep 457559 = 686339) B686339
theorem B457579 : Blo 455782 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B457591 : Blo 455782 457591 := bstep (se 1 (by rfl) ⟨343193, by rfl⟩ : syracuseStep 457591 = 686387) B686387
theorem B457611 : Blo 455782 457611 := bstep (se 1 (by rfl) ⟨343208, by rfl⟩ : syracuseStep 457611 = 686417) B686417
theorem B686987 : Blo 455782 686987 := bstep (se 1 (by rfl) ⟨515240, by rfl⟩ : syracuseStep 686987 = 1030481) B1030481
theorem B457623 : Blo 455782 457623 := bstep (se 1 (by rfl) ⟨343217, by rfl⟩ : syracuseStep 457623 = 686435) B686435
theorem B686999 : Blo 455782 686999 := bstep (se 1 (by rfl) ⟨515249, by rfl⟩ : syracuseStep 686999 = 1030499) B1030499
theorem B457643 : Blo 455782 457643 := bstep (se 1 (by rfl) ⟨343232, by rfl⟩ : syracuseStep 457643 = 686465) B686465
theorem B457655 : Blo 455782 457655 := bstep (se 1 (by rfl) ⟨343241, by rfl⟩ : syracuseStep 457655 = 686483) B686483
theorem B1735627 : Blo 455782 1735627 := bstep (se 1 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 1735627 = 2603441) B2603441
theorem B457675 : Blo 455782 457675 := bstep (se 1 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 457675 = 686513) B686513
theorem B457687 : Blo 455782 457687 := bstep (se 1 (by rfl) ⟨343265, by rfl⟩ : syracuseStep 457687 = 686531) B686531
theorem B687065 : Blo 455782 687065 := bstep (se 2 (by rfl) ⟨257649, by rfl⟩ : syracuseStep 687065 = 515299) B515299
theorem B457707 : Blo 455782 457707 := bstep (se 1 (by rfl) ⟨343280, by rfl⟩ : syracuseStep 457707 = 686561) B686561
theorem B457719 : Blo 455782 457719 := bstep (se 1 (by rfl) ⟨343289, by rfl⟩ : syracuseStep 457719 = 686579) B686579
theorem B457739 : Blo 455782 457739 := bstep (se 1 (by rfl) ⟨343304, by rfl⟩ : syracuseStep 457739 = 686609) B686609
theorem B457751 : Blo 455782 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B457771 : Blo 455782 457771 := bstep (se 1 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 457771 = 686657) B686657
theorem B457783 : Blo 455782 457783 := bstep (se 1 (by rfl) ⟨343337, by rfl⟩ : syracuseStep 457783 = 686675) B686675
theorem B457803 : Blo 455782 457803 := bstep (se 1 (by rfl) ⟨343352, by rfl⟩ : syracuseStep 457803 = 686705) B686705
theorem B687179 : Blo 455782 687179 := bstep (se 1 (by rfl) ⟨515384, by rfl⟩ : syracuseStep 687179 = 1030769) B1030769
theorem B457815 : Blo 455782 457815 := bstep (se 1 (by rfl) ⟨343361, by rfl⟩ : syracuseStep 457815 = 686723) B686723
theorem B687191 : Blo 455782 687191 := bstep (se 1 (by rfl) ⟨515393, by rfl⟩ : syracuseStep 687191 = 1030787) B1030787
theorem B1539161 : Blo 455782 1539161 := bstep (se 2 (by rfl) ⟨577185, by rfl⟩ : syracuseStep 1539161 = 1154371) B1154371
theorem B457835 : Blo 455782 457835 := bstep (se 1 (by rfl) ⟨343376, by rfl⟩ : syracuseStep 457835 = 686753) B686753
theorem B457847 : Blo 455782 457847 := bstep (se 1 (by rfl) ⟨343385, by rfl⟩ : syracuseStep 457847 = 686771) B686771
theorem B457867 : Blo 455782 457867 := bstep (se 1 (by rfl) ⟨343400, by rfl⟩ : syracuseStep 457867 = 686801) B686801
theorem B457879 : Blo 455782 457879 := bstep (se 1 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 457879 = 686819) B686819
theorem B687257 : Blo 455782 687257 := bstep (se 2 (by rfl) ⟨257721, by rfl⟩ : syracuseStep 687257 = 515443) B515443
theorem B457899 : Blo 455782 457899 := bstep (se 1 (by rfl) ⟨343424, by rfl⟩ : syracuseStep 457899 = 686849) B686849
theorem B457911 : Blo 455782 457911 := bstep (se 1 (by rfl) ⟨343433, by rfl⟩ : syracuseStep 457911 = 686867) B686867
theorem B457931 : Blo 455782 457931 := bstep (se 1 (by rfl) ⟨343448, by rfl⟩ : syracuseStep 457931 = 686897) B686897
theorem B457943 : Blo 455782 457943 := bstep (se 1 (by rfl) ⟨343457, by rfl⟩ : syracuseStep 457943 = 686915) B686915
theorem B2784473 : Blo 455782 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1735901 : Blo 455782 1735901 := bstep (se 3 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 1735901 = 650963) B650963
theorem B457963 : Blo 455782 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B457975 : Blo 455782 457975 := bstep (se 1 (by rfl) ⟨343481, by rfl⟩ : syracuseStep 457975 = 686963) B686963
theorem B1047809 : Blo 455782 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B457995 : Blo 455782 457995 := bstep (se 1 (by rfl) ⟨343496, by rfl⟩ : syracuseStep 457995 = 686993) B686993
theorem B687371 : Blo 455782 687371 := bstep (se 1 (by rfl) ⟨515528, by rfl⟩ : syracuseStep 687371 = 1031057) B1031057
theorem B458007 : Blo 455782 458007 := bstep (se 1 (by rfl) ⟨343505, by rfl⟩ : syracuseStep 458007 = 687011) B687011
theorem B687383 : Blo 455782 687383 := bstep (se 1 (by rfl) ⟨515537, by rfl⟩ : syracuseStep 687383 = 1031075) B1031075
theorem B458027 : Blo 455782 458027 := bstep (se 1 (by rfl) ⟨343520, by rfl⟩ : syracuseStep 458027 = 687041) B687041
theorem B458039 : Blo 455782 458039 := bstep (se 1 (by rfl) ⟨343529, by rfl⟩ : syracuseStep 458039 = 687059) B687059
theorem B490807 : Blo 455782 490807 := bstep (se 1 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 490807 = 736211) B736211
theorem B458059 : Blo 455782 458059 := bstep (se 1 (by rfl) ⟨343544, by rfl⟩ : syracuseStep 458059 = 687089) B687089
theorem B458071 : Blo 455782 458071 := bstep (se 1 (by rfl) ⟨343553, by rfl⟩ : syracuseStep 458071 = 687107) B687107
theorem B687449 : Blo 455782 687449 := bstep (se 2 (by rfl) ⟨257793, by rfl⟩ : syracuseStep 687449 = 515587) B515587
theorem B458091 : Blo 455782 458091 := bstep (se 1 (by rfl) ⟨343568, by rfl⟩ : syracuseStep 458091 = 687137) B687137
theorem B458103 : Blo 455782 458103 := bstep (se 1 (by rfl) ⟨343577, by rfl⟩ : syracuseStep 458103 = 687155) B687155
theorem B458123 : Blo 455782 458123 := bstep (se 1 (by rfl) ⟨343592, by rfl⟩ : syracuseStep 458123 = 687185) B687185
theorem B458135 : Blo 455782 458135 := bstep (se 1 (by rfl) ⟨343601, by rfl⟩ : syracuseStep 458135 = 687203) B687203
theorem B458155 : Blo 455782 458155 := bstep (se 1 (by rfl) ⟨343616, by rfl⟩ : syracuseStep 458155 = 687233) B687233
theorem B458167 : Blo 455782 458167 := bstep (se 1 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 458167 = 687251) B687251
theorem B458187 : Blo 455782 458187 := bstep (se 1 (by rfl) ⟨343640, by rfl⟩ : syracuseStep 458187 = 687281) B687281
theorem B687563 : Blo 455782 687563 := bstep (se 1 (by rfl) ⟨515672, by rfl⟩ : syracuseStep 687563 = 1031345) B1031345
theorem B458199 : Blo 455782 458199 := bstep (se 1 (by rfl) ⟨343649, by rfl⟩ : syracuseStep 458199 = 687299) B687299
theorem B687575 : Blo 455782 687575 := bstep (se 1 (by rfl) ⟨515681, by rfl⟩ : syracuseStep 687575 = 1031363) B1031363
theorem B458219 : Blo 455782 458219 := bstep (se 1 (by rfl) ⟨343664, by rfl⟩ : syracuseStep 458219 = 687329) B687329
theorem B458231 : Blo 455782 458231 := bstep (se 1 (by rfl) ⟨343673, by rfl⟩ : syracuseStep 458231 = 687347) B687347
theorem B458251 : Blo 455782 458251 := bstep (se 1 (by rfl) ⟨343688, by rfl⟩ : syracuseStep 458251 = 687377) B687377
theorem B458263 : Blo 455782 458263 := bstep (se 1 (by rfl) ⟨343697, by rfl⟩ : syracuseStep 458263 = 687395) B687395
theorem B687641 : Blo 455782 687641 := bstep (se 2 (by rfl) ⟨257865, by rfl⟩ : syracuseStep 687641 = 515731) B515731
theorem B458283 : Blo 455782 458283 := bstep (se 1 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 458283 = 687425) B687425
theorem B458295 : Blo 455782 458295 := bstep (se 1 (by rfl) ⟨343721, by rfl⟩ : syracuseStep 458295 = 687443) B687443
theorem B458315 : Blo 455782 458315 := bstep (se 1 (by rfl) ⟨343736, by rfl⟩ : syracuseStep 458315 = 687473) B687473
theorem B458327 : Blo 455782 458327 := bstep (se 1 (by rfl) ⟨343745, by rfl⟩ : syracuseStep 458327 = 687491) B687491
theorem B458347 : Blo 455782 458347 := bstep (se 1 (by rfl) ⟨343760, by rfl⟩ : syracuseStep 458347 = 687521) B687521
theorem B458359 : Blo 455782 458359 := bstep (se 1 (by rfl) ⟨343769, by rfl⟩ : syracuseStep 458359 = 687539) B687539
theorem B458379 : Blo 455782 458379 := bstep (se 1 (by rfl) ⟨343784, by rfl⟩ : syracuseStep 458379 = 687569) B687569
theorem B687755 : Blo 455782 687755 := bstep (se 1 (by rfl) ⟨515816, by rfl⟩ : syracuseStep 687755 = 1031633) B1031633
theorem B458391 : Blo 455782 458391 := bstep (se 1 (by rfl) ⟨343793, by rfl⟩ : syracuseStep 458391 = 687587) B687587
theorem B687767 : Blo 455782 687767 := bstep (se 1 (by rfl) ⟨515825, by rfl⟩ : syracuseStep 687767 = 1031651) B1031651
theorem B458411 : Blo 455782 458411 := bstep (se 1 (by rfl) ⟨343808, by rfl⟩ : syracuseStep 458411 = 687617) B687617
theorem B458423 : Blo 455782 458423 := bstep (se 1 (by rfl) ⟨343817, by rfl⟩ : syracuseStep 458423 = 687635) B687635
theorem B458443 : Blo 455782 458443 := bstep (se 1 (by rfl) ⟨343832, by rfl⟩ : syracuseStep 458443 = 687665) B687665
theorem B458455 : Blo 455782 458455 := bstep (se 1 (by rfl) ⟨343841, by rfl⟩ : syracuseStep 458455 = 687683) B687683
theorem B687833 : Blo 455782 687833 := bstep (se 2 (by rfl) ⟨257937, by rfl⟩ : syracuseStep 687833 = 515875) B515875
theorem B458475 : Blo 455782 458475 := bstep (se 1 (by rfl) ⟨343856, by rfl⟩ : syracuseStep 458475 = 687713) B687713
theorem B524011 : Blo 455782 524011 := bstep (se 1 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 524011 = 786017) B786017
theorem B458487 : Blo 455782 458487 := bstep (se 1 (by rfl) ⟨343865, by rfl⟩ : syracuseStep 458487 = 687731) B687731
theorem B458507 : Blo 455782 458507 := bstep (se 1 (by rfl) ⟨343880, by rfl⟩ : syracuseStep 458507 = 687761) B687761
theorem B1539863 : Blo 455782 1539863 := bstep (se 1 (by rfl) ⟨1154897, by rfl⟩ : syracuseStep 1539863 = 2309795) B2309795
theorem B458519 : Blo 455782 458519 := bstep (se 1 (by rfl) ⟨343889, by rfl⟩ : syracuseStep 458519 = 687779) B687779
theorem B458539 : Blo 455782 458539 := bstep (se 1 (by rfl) ⟨343904, by rfl⟩ : syracuseStep 458539 = 687809) B687809
theorem B1179443 : Blo 455782 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B458551 : Blo 455782 458551 := bstep (se 1 (by rfl) ⟨343913, by rfl⟩ : syracuseStep 458551 = 687827) B687827
theorem B458571 : Blo 455782 458571 := bstep (se 1 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 458571 = 687857) B687857
theorem B687947 : Blo 455782 687947 := bstep (se 1 (by rfl) ⟨515960, by rfl⟩ : syracuseStep 687947 = 1031921) B1031921
theorem B458583 : Blo 455782 458583 := bstep (se 1 (by rfl) ⟨343937, by rfl⟩ : syracuseStep 458583 = 687875) B687875
theorem B687959 : Blo 455782 687959 := bstep (se 1 (by rfl) ⟨515969, by rfl⟩ : syracuseStep 687959 = 1031939) B1031939
theorem B1572697 : Blo 455782 1572697 := bstep (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) B1179523
theorem B458603 : Blo 455782 458603 := bstep (se 1 (by rfl) ⟨343952, by rfl⟩ : syracuseStep 458603 = 687905) B687905
theorem B458615 : Blo 455782 458615 := bstep (se 1 (by rfl) ⟨343961, by rfl⟩ : syracuseStep 458615 = 687923) B687923
theorem B458635 : Blo 455782 458635 := bstep (se 1 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 458635 = 687953) B687953
theorem B1736599 : Blo 455782 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B458647 : Blo 455782 458647 := bstep (se 1 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 458647 = 687971) B687971
theorem B688025 : Blo 455782 688025 := bstep (se 2 (by rfl) ⟨258009, by rfl⟩ : syracuseStep 688025 = 516019) B516019
theorem B458667 : Blo 455782 458667 := bstep (se 1 (by rfl) ⟨344000, by rfl⟩ : syracuseStep 458667 = 688001) B688001
theorem B458679 : Blo 455782 458679 := bstep (se 1 (by rfl) ⟨344009, by rfl⟩ : syracuseStep 458679 = 688019) B688019
theorem B458699 : Blo 455782 458699 := bstep (se 1 (by rfl) ⟨344024, by rfl⟩ : syracuseStep 458699 = 688049) B688049
theorem B458711 : Blo 455782 458711 := bstep (se 1 (by rfl) ⟨344033, by rfl⟩ : syracuseStep 458711 = 688067) B688067
theorem B458731 : Blo 455782 458731 := bstep (se 1 (by rfl) ⟨344048, by rfl⟩ : syracuseStep 458731 = 688097) B688097
theorem B458743 : Blo 455782 458743 := bstep (se 1 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 458743 = 688115) B688115
theorem B458759 : Blo 455782 458759 := bstep (se 1 (by rfl) ⟨344069, by rfl⟩ : syracuseStep 458759 = 688139) B688139
theorem B458767 : Blo 455782 458767 := bstep (se 1 (by rfl) ⟨344075, by rfl⟩ : syracuseStep 458767 = 688151) B688151
theorem B688187 : Blo 455782 688187 := bstep (se 1 (by rfl) ⟨516140, by rfl⟩ : syracuseStep 688187 = 1032281) B1032281
theorem B458811 : Blo 455782 458811 := bstep (se 1 (by rfl) ⟨344108, by rfl⟩ : syracuseStep 458811 = 688217) B688217
theorem B3342397 : Blo 455782 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B688247 : Blo 455782 688247 := bstep (se 1 (by rfl) ⟨516185, by rfl⟩ : syracuseStep 688247 = 1032371) B1032371
theorem B458887 : Blo 455782 458887 := bstep (se 1 (by rfl) ⟨344165, by rfl⟩ : syracuseStep 458887 = 688331) B688331
theorem B688271 : Blo 455782 688271 := bstep (se 1 (by rfl) ⟨516203, by rfl⟩ : syracuseStep 688271 = 1032407) B1032407
theorem B458895 : Blo 455782 458895 := bstep (se 1 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 458895 = 688343) B688343
theorem B688313 : Blo 455782 688313 := bstep (se 2 (by rfl) ⟨258117, by rfl⟩ : syracuseStep 688313 = 516235) B516235
theorem B458939 : Blo 455782 458939 := bstep (se 1 (by rfl) ⟨344204, by rfl⟩ : syracuseStep 458939 = 688409) B688409
theorem B2195657 : Blo 455782 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B688391 : Blo 455782 688391 := bstep (se 1 (by rfl) ⟨516293, by rfl⟩ : syracuseStep 688391 = 1032587) B1032587
theorem B459015 : Blo 455782 459015 := bstep (se 1 (by rfl) ⟨344261, by rfl⟩ : syracuseStep 459015 = 688523) B688523
theorem B459023 : Blo 455782 459023 := bstep (se 1 (by rfl) ⟨344267, by rfl⟩ : syracuseStep 459023 = 688535) B688535
theorem B688427 : Blo 455782 688427 := bstep (se 1 (by rfl) ⟨516320, by rfl⟩ : syracuseStep 688427 = 1032641) B1032641
theorem B459067 : Blo 455782 459067 := bstep (se 1 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 459067 = 688601) B688601
theorem B688457 : Blo 455782 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B459143 : Blo 455782 459143 := bstep (se 1 (by rfl) ⟨344357, by rfl⟩ : syracuseStep 459143 = 688715) B688715
theorem B459151 : Blo 455782 459151 := bstep (se 1 (by rfl) ⟨344363, by rfl⟩ : syracuseStep 459151 = 688727) B688727
theorem B688571 : Blo 455782 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B459195 : Blo 455782 459195 := bstep (se 1 (by rfl) ⟨344396, by rfl⟩ : syracuseStep 459195 = 688793) B688793
theorem B688631 : Blo 455782 688631 := bstep (se 1 (by rfl) ⟨516473, by rfl⟩ : syracuseStep 688631 = 1032947) B1032947
theorem B459271 : Blo 455782 459271 := bstep (se 1 (by rfl) ⟨344453, by rfl⟩ : syracuseStep 459271 = 688907) B688907
theorem B1540619 : Blo 455782 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B688655 : Blo 455782 688655 := bstep (se 1 (by rfl) ⟨516491, by rfl⟩ : syracuseStep 688655 = 1032983) B1032983
theorem B459279 : Blo 455782 459279 := bstep (se 1 (by rfl) ⟨344459, by rfl⟩ : syracuseStep 459279 = 688919) B688919
theorem B688697 : Blo 455782 688697 := bstep (se 2 (by rfl) ⟨258261, by rfl⟩ : syracuseStep 688697 = 516523) B516523
theorem B459323 : Blo 455782 459323 := bstep (se 1 (by rfl) ⟨344492, by rfl⟩ : syracuseStep 459323 = 688985) B688985
theorem B1540727 : Blo 455782 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B688775 : Blo 455782 688775 := bstep (se 1 (by rfl) ⟨516581, by rfl⟩ : syracuseStep 688775 = 1033163) B1033163
theorem B459399 : Blo 455782 459399 := bstep (se 1 (by rfl) ⟨344549, by rfl⟩ : syracuseStep 459399 = 689099) B689099
theorem B459407 : Blo 455782 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B688811 : Blo 455782 688811 := bstep (se 1 (by rfl) ⟨516608, by rfl⟩ : syracuseStep 688811 = 1033217) B1033217
theorem B459451 : Blo 455782 459451 := bstep (se 1 (by rfl) ⟨344588, by rfl⟩ : syracuseStep 459451 = 689177) B689177
theorem B4391617 : Blo 455782 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B688841 : Blo 455782 688841 := bstep (se 2 (by rfl) ⟨258315, by rfl⟩ : syracuseStep 688841 = 516631) B516631
theorem B459527 : Blo 455782 459527 := bstep (se 1 (by rfl) ⟨344645, by rfl⟩ : syracuseStep 459527 = 689291) B689291
theorem B459535 : Blo 455782 459535 := bstep (se 1 (by rfl) ⟨344651, by rfl⟩ : syracuseStep 459535 = 689303) B689303
theorem B688955 : Blo 455782 688955 := bstep (se 1 (by rfl) ⟨516716, by rfl⟩ : syracuseStep 688955 = 1033433) B1033433
theorem B459579 : Blo 455782 459579 := bstep (se 1 (by rfl) ⟨344684, by rfl⟩ : syracuseStep 459579 = 689369) B689369
theorem B689015 : Blo 455782 689015 := bstep (se 1 (by rfl) ⟨516761, by rfl⟩ : syracuseStep 689015 = 1033523) B1033523
theorem B459655 : Blo 455782 459655 := bstep (se 1 (by rfl) ⟨344741, by rfl⟩ : syracuseStep 459655 = 689483) B689483
theorem B689039 : Blo 455782 689039 := bstep (se 1 (by rfl) ⟨516779, by rfl⟩ : syracuseStep 689039 = 1033559) B1033559
theorem B459663 : Blo 455782 459663 := bstep (se 1 (by rfl) ⟨344747, by rfl⟩ : syracuseStep 459663 = 689495) B689495
theorem B689081 : Blo 455782 689081 := bstep (se 2 (by rfl) ⟨258405, by rfl⟩ : syracuseStep 689081 = 516811) B516811
theorem B459707 : Blo 455782 459707 := bstep (se 1 (by rfl) ⟨344780, by rfl⟩ : syracuseStep 459707 = 689561) B689561
theorem B689159 : Blo 455782 689159 := bstep (se 1 (by rfl) ⟨516869, by rfl⟩ : syracuseStep 689159 = 1033739) B1033739
theorem B689195 : Blo 455782 689195 := bstep (se 1 (by rfl) ⟨516896, by rfl⟩ : syracuseStep 689195 = 1033793) B1033793
theorem B689225 : Blo 455782 689225 := bstep (se 2 (by rfl) ⟨258459, by rfl⟩ : syracuseStep 689225 = 516919) B516919
theorem B689339 : Blo 455782 689339 := bstep (se 1 (by rfl) ⟨517004, by rfl⟩ : syracuseStep 689339 = 1034009) B1034009
theorem B1541321 : Blo 455782 1541321 := bstep (se 2 (by rfl) ⟨577995, by rfl⟩ : syracuseStep 1541321 = 1155991) B1155991
theorem B689399 : Blo 455782 689399 := bstep (se 1 (by rfl) ⟨517049, by rfl⟩ : syracuseStep 689399 = 1034099) B1034099
theorem B689423 : Blo 455782 689423 := bstep (se 1 (by rfl) ⟨517067, by rfl⟩ : syracuseStep 689423 = 1034135) B1034135
theorem B689465 : Blo 455782 689465 := bstep (se 2 (by rfl) ⟨258549, by rfl⟩ : syracuseStep 689465 = 517099) B517099
theorem B1738043 : Blo 455782 1738043 := bstep (se 1 (by rfl) ⟨1303532, by rfl⟩ : syracuseStep 1738043 = 2607065) B2607065
theorem B689543 : Blo 455782 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B689579 : Blo 455782 689579 := bstep (se 1 (by rfl) ⟨517184, by rfl⟩ : syracuseStep 689579 = 1034369) B1034369
theorem B689609 : Blo 455782 689609 := bstep (se 2 (by rfl) ⟨258603, by rfl⟩ : syracuseStep 689609 = 517207) B517207
theorem B36079181 : Blo 455782 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B1738529 : Blo 455782 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B1542023 : Blo 455782 1542023 := bstep (se 1 (by rfl) ⟨1156517, by rfl⟩ : syracuseStep 1542023 = 2313035) B2313035
theorem B11175833 : Blo 455782 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B3311563 : Blo 455782 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B1673303 : Blo 455782 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1542401 : Blo 455782 1542401 := bstep (se 2 (by rfl) ⟨578400, by rfl⟩ : syracuseStep 1542401 = 1156801) B1156801
theorem B3770833 : Blo 455782 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1739501 : Blo 455782 1739501 := bstep (se 3 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 1739501 = 652313) B652313
theorem B658219 : Blo 455782 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B1543211 : Blo 455782 1543211 := bstep (se 1 (by rfl) ⟨1157408, by rfl⟩ : syracuseStep 1543211 = 2314817) B2314817
theorem B1739819 : Blo 455782 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B658633 : Blo 455782 658633 := bstep (se 2 (by rfl) ⟨246987, by rfl⟩ : syracuseStep 658633 = 493975) B493975
theorem B3902701 : Blo 455782 3902701 := bstep (se 3 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 3902701 = 1463513) B1463513
theorem B3706145 : Blo 455782 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B1150507 : Blo 455782 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B463163 : Blo 455782 463163 := bstep (se 1 (by rfl) ⟨347372, by rfl⟩ : syracuseStep 463163 = 694745) B694745
theorem B1544507 : Blo 455782 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B1249939 : Blo 455782 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1544993 : Blo 455782 1544993 := bstep (se 2 (by rfl) ⟨579372, by rfl⟩ : syracuseStep 1544993 = 1158745) B1158745
theorem B824107 : Blo 455782 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B1643399 : Blo 455782 1643399 := bstep (se 1 (by rfl) ⟨1232549, by rfl⟩ : syracuseStep 1643399 = 2465099) B2465099
theorem B627599 : Blo 455782 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B3904685 : Blo 455782 3904685 := bstep (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) B1464257
theorem B1545587 : Blo 455782 1545587 := bstep (se 1 (by rfl) ⟨1159190, by rfl⟩ : syracuseStep 1545587 = 2318381) B2318381
theorem B4396963 : Blo 455782 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B21174533 : Blo 455782 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B2464015 : Blo 455782 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B924023 : Blo 455782 924023 := bstep (se 1 (by rfl) ⟨693017, by rfl⟩ : syracuseStep 924023 = 1386035) B1386035
theorem B1743389 : Blo 455782 1743389 := bstep (se 3 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 1743389 = 653771) B653771
theorem B1743403 : Blo 455782 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B2202173 : Blo 455782 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B11770433 : Blo 455782 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B6626063 : Blo 455782 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B1153835 : Blo 455782 1153835 := bstep (se 1 (by rfl) ⟨865376, by rfl⟩ : syracuseStep 1153835 = 1730753) B1730753
theorem B4954931 : Blo 455782 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B1186963 : Blo 455782 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B990599 : Blo 455782 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B3907075 : Blo 455782 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B663113 : Blo 455782 663113 := bstep (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) B497335
theorem B1154675 : Blo 455782 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B2465399 : Blo 455782 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1154695 : Blo 455782 1154695 := bstep (se 1 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 1154695 = 1732043) B1732043
theorem B2924261 : Blo 455782 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B1548179 : Blo 455782 1548179 := bstep (se 1 (by rfl) ⟨1161134, by rfl⟩ : syracuseStep 1548179 = 2322269) B2322269
theorem B1154969 : Blo 455782 1154969 := bstep (se 2 (by rfl) ⟨433113, by rfl⟩ : syracuseStep 1154969 = 866227) B866227
theorem B1155131 : Blo 455782 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B1155343 : Blo 455782 1155343 := bstep (se 1 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 1155343 = 1733015) B1733015
theorem B2204189 : Blo 455782 2204189 := bstep (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) B826571
theorem B1155617 : Blo 455782 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B3482189 : Blo 455782 3482189 := bstep (se 3 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 3482189 = 1305821) B1305821
theorem B1549583 : Blo 455782 1549583 := bstep (se 1 (by rfl) ⟨1162187, by rfl⟩ : syracuseStep 1549583 = 2324375) B2324375
theorem B1156619 : Blo 455782 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B1549853 : Blo 455782 1549853 := bstep (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) B581195
theorem B5547827 : Blo 455782 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B1025927 : Blo 455782 1025927 := bstep (se 1 (by rfl) ⟨769445, by rfl⟩ : syracuseStep 1025927 = 1538891) B1538891
theorem B2205575 : Blo 455782 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B1026107 : Blo 455782 1026107 := bstep (se 1 (by rfl) ⟨769580, by rfl⟩ : syracuseStep 1026107 = 1539161) B1539161
theorem B1648759 : Blo 455782 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B1157267 : Blo 455782 1157267 := bstep (se 1 (by rfl) ⟨867950, by rfl⟩ : syracuseStep 1157267 = 1735901) B1735901
theorem B698539 : Blo 455782 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B1026233 : Blo 455782 1026233 := bstep (se 2 (by rfl) ⟨384837, by rfl⟩ : syracuseStep 1026233 = 769675) B769675
theorem B698681 : Blo 455782 698681 := bstep (se 2 (by rfl) ⟨262005, by rfl⟩ : syracuseStep 698681 = 524011) B524011
theorem B1157561 : Blo 455782 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B1026575 : Blo 455782 1026575 := bstep (se 1 (by rfl) ⟨769931, by rfl⟩ : syracuseStep 1026575 = 1539863) B1539863
theorem B928271 : Blo 455782 928271 := bstep (se 1 (by rfl) ⟨696203, by rfl⟩ : syracuseStep 928271 = 1392407) B1392407
theorem B1026593 : Blo 455782 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B633673 : Blo 455782 633673 := bstep (se 2 (by rfl) ⟨237627, by rfl⟩ : syracuseStep 633673 = 475255) B475255
theorem B7023449 : Blo 455782 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B1026935 : Blo 455782 1026935 := bstep (se 1 (by rfl) ⟨770201, by rfl⟩ : syracuseStep 1026935 = 1540403) B1540403
theorem B1551257 : Blo 455782 1551257 := bstep (se 2 (by rfl) ⟨581721, by rfl⟩ : syracuseStep 1551257 = 1163443) B1163443
theorem B2206649 : Blo 455782 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B3484619 : Blo 455782 3484619 := bstep (se 1 (by rfl) ⟨2613464, by rfl⟩ : syracuseStep 3484619 = 5226929) B5226929
theorem B1027115 : Blo 455782 1027115 := bstep (se 1 (by rfl) ⟨770336, by rfl⟩ : syracuseStep 1027115 = 1540673) B1540673
theorem B1158259 : Blo 455782 1158259 := bstep (se 1 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 1158259 = 1737389) B1737389
theorem B1158401 : Blo 455782 1158401 := bstep (se 2 (by rfl) ⟨434400, by rfl⟩ : syracuseStep 1158401 = 868801) B868801
theorem B2600207 : Blo 455782 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B929083 : Blo 455782 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B1027475 : Blo 455782 1027475 := bstep (se 1 (by rfl) ⟨770606, by rfl⟩ : syracuseStep 1027475 = 1541213) B1541213
theorem B1027529 : Blo 455782 1027529 := bstep (se 2 (by rfl) ⟨385323, by rfl⟩ : syracuseStep 1027529 = 770647) B770647
theorem B1158857 : Blo 455782 1158857 := bstep (se 2 (by rfl) ⟨434571, by rfl⟩ : syracuseStep 1158857 = 869143) B869143
theorem B1650547 : Blo 455782 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1159211 : Blo 455782 1159211 := bstep (se 1 (by rfl) ⟨869408, by rfl⟩ : syracuseStep 1159211 = 1738817) B1738817
theorem B3715159 : Blo 455782 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B1028231 : Blo 455782 1028231 := bstep (se 1 (by rfl) ⟨771173, by rfl⟩ : syracuseStep 1028231 = 1542347) B1542347
theorem B7516433 : Blo 455782 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B1028411 : Blo 455782 1028411 := bstep (se 1 (by rfl) ⟨771308, by rfl⟩ : syracuseStep 1028411 = 1542617) B1542617
theorem B1028537 : Blo 455782 1028537 := bstep (se 2 (by rfl) ⟨385701, by rfl⟩ : syracuseStep 1028537 = 771403) B771403
theorem B1323535 : Blo 455782 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B930347 : Blo 455782 930347 := bstep (se 1 (by rfl) ⟨697760, by rfl⟩ : syracuseStep 930347 = 1395521) B1395521
theorem B2208323 : Blo 455782 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B2601665 : Blo 455782 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1028879 : Blo 455782 1028879 := bstep (se 1 (by rfl) ⟨771659, by rfl⟩ : syracuseStep 1028879 = 1543319) B1543319
theorem B1028897 : Blo 455782 1028897 := bstep (se 2 (by rfl) ⟨385836, by rfl⟩ : syracuseStep 1028897 = 771673) B771673
theorem B4699043 : Blo 455782 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1160203 : Blo 455782 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B17675333 : Blo 455782 17675333 := bstep (se 4 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 17675333 = 3314125) B3314125
theorem B865399 : Blo 455782 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B1029239 : Blo 455782 1029239 := bstep (se 1 (by rfl) ⟨771929, by rfl⟩ : syracuseStep 1029239 = 1543859) B1543859
theorem B1160345 : Blo 455782 1160345 := bstep (se 2 (by rfl) ⟨435129, by rfl⟩ : syracuseStep 1160345 = 870259) B870259
theorem B1029419 : Blo 455782 1029419 := bstep (se 1 (by rfl) ⟨772064, by rfl⟩ : syracuseStep 1029419 = 1544129) B1544129
theorem B2471219 : Blo 455782 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B1160507 : Blo 455782 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B5224013 : Blo 455782 5224013 := bstep (se 3 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 5224013 = 1959005) B1959005
theorem B1029779 : Blo 455782 1029779 := bstep (se 1 (by rfl) ⟨772334, by rfl⟩ : syracuseStep 1029779 = 1544669) B1544669
theorem B1160851 : Blo 455782 1160851 := bstep (se 1 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 1160851 = 1741277) B1741277
theorem B1029833 : Blo 455782 1029833 := bstep (se 2 (by rfl) ⟨386187, by rfl⟩ : syracuseStep 1029833 = 772375) B772375
theorem B1160993 : Blo 455782 1160993 := bstep (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) B870745
theorem B1325117 : Blo 455782 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B5028155 : Blo 455782 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B1030535 : Blo 455782 1030535 := bstep (se 1 (by rfl) ⟨772901, by rfl⟩ : syracuseStep 1030535 = 1545803) B1545803
theorem B2308499 : Blo 455782 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B4929977 : Blo 455782 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B1030715 : Blo 455782 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B866963 : Blo 455782 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B1030841 : Blo 455782 1030841 := bstep (se 2 (by rfl) ⟨386565, by rfl⟩ : syracuseStep 1030841 = 773131) B773131
theorem B867017 : Blo 455782 867017 := bstep (se 2 (by rfl) ⟨325131, by rfl⟩ : syracuseStep 867017 = 650263) B650263
theorem B1161985 : Blo 455782 1161985 := bstep (se 2 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 1161985 = 871489) B871489
theorem B867115 : Blo 455782 867115 := bstep (se 1 (by rfl) ⟨650336, by rfl⟩ : syracuseStep 867115 = 1300673) B1300673
theorem B867343 : Blo 455782 867343 := bstep (se 1 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 867343 = 1301015) B1301015
theorem B1031183 : Blo 455782 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B1031201 : Blo 455782 1031201 := bstep (se 2 (by rfl) ⟨386700, by rfl⟩ : syracuseStep 1031201 = 773401) B773401
theorem B8928317 : Blo 455782 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B1326365 : Blo 455782 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B1162583 : Blo 455782 1162583 := bstep (se 1 (by rfl) ⟨871937, by rfl⟩ : syracuseStep 1162583 = 1743875) B1743875
theorem B1031543 : Blo 455782 1031543 := bstep (se 1 (by rfl) ⟨773657, by rfl⟩ : syracuseStep 1031543 = 1547315) B1547315
theorem B2342297 : Blo 455782 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B1654283 : Blo 455782 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1031723 : Blo 455782 1031723 := bstep (se 1 (by rfl) ⟨773792, by rfl⟩ : syracuseStep 1031723 = 1547585) B1547585
theorem B1162795 : Blo 455782 1162795 := bstep (se 1 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 1162795 = 1744193) B1744193
theorem B769655 : Blo 455782 769655 := bstep (se 1 (by rfl) ⟨577241, by rfl⟩ : syracuseStep 769655 = 1154483) B1154483
theorem B6602417 : Blo 455782 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B5193395 : Blo 455782 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B1162937 : Blo 455782 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B1425163 : Blo 455782 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B1032083 : Blo 455782 1032083 := bstep (se 1 (by rfl) ⟨774062, by rfl⟩ : syracuseStep 1032083 = 1548125) B1548125
theorem B1032137 : Blo 455782 1032137 := bstep (se 2 (by rfl) ⟨387051, by rfl⟩ : syracuseStep 1032137 = 774103) B774103
theorem B770107 : Blo 455782 770107 := bstep (se 1 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 770107 = 1155161) B1155161
theorem B3489965 : Blo 455782 3489965 := bstep (se 3 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 3489965 = 1308737) B1308737
theorem B770249 : Blo 455782 770249 := bstep (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) B577687
theorem B2932973 : Blo 455782 2932973 := bstep (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) B1099865
theorem B1098251 : Blo 455782 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B868907 : Blo 455782 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B5653111 : Blo 455782 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B1032839 : Blo 455782 1032839 := bstep (se 1 (by rfl) ⟨774629, by rfl⟩ : syracuseStep 1032839 = 1549259) B1549259
theorem B1033019 : Blo 455782 1033019 := bstep (se 1 (by rfl) ⟨774764, by rfl⟩ : syracuseStep 1033019 = 1549529) B1549529
theorem B770951 : Blo 455782 770951 := bstep (se 1 (by rfl) ⟨578213, by rfl⟩ : syracuseStep 770951 = 1156427) B1156427
theorem B1033145 : Blo 455782 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B2475019 : Blo 455782 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B1885421 : Blo 455782 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B1099019 : Blo 455782 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B1033487 : Blo 455782 1033487 := bstep (se 1 (by rfl) ⟨775115, by rfl⟩ : syracuseStep 1033487 = 1550231) B1550231
theorem B1033505 : Blo 455782 1033505 := bstep (se 2 (by rfl) ⟨387564, by rfl⟩ : syracuseStep 1033505 = 775129) B775129
theorem B2311577 : Blo 455782 2311577 := bstep (se 2 (by rfl) ⟨866841, by rfl⟩ : syracuseStep 2311577 = 1733683) B1733683
theorem B2606539 : Blo 455782 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B771599 : Blo 455782 771599 := bstep (se 1 (by rfl) ⟨578699, by rfl⟩ : syracuseStep 771599 = 1157399) B1157399
theorem B1033847 : Blo 455782 1033847 := bstep (se 1 (by rfl) ⟨775385, by rfl⟩ : syracuseStep 1033847 = 1550771) B1550771
theorem B1034027 : Blo 455782 1034027 := bstep (se 1 (by rfl) ⟨775520, by rfl⟩ : syracuseStep 1034027 = 1551041) B1551041
theorem B2476061 : Blo 455782 2476061 := bstep (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) B928523
theorem B772139 : Blo 455782 772139 := bstep (se 1 (by rfl) ⟨579104, by rfl⟩ : syracuseStep 772139 = 1158209) B1158209
theorem B1034387 : Blo 455782 1034387 := bstep (se 1 (by rfl) ⟨775790, by rfl⟩ : syracuseStep 1034387 = 1551581) B1551581
theorem B870601 : Blo 455782 870601 := bstep (se 2 (by rfl) ⟨326475, by rfl⟩ : syracuseStep 870601 = 652951) B652951
theorem B1034441 : Blo 455782 1034441 := bstep (se 2 (by rfl) ⟨387915, by rfl⟩ : syracuseStep 1034441 = 775831) B775831
theorem B772537 : Blo 455782 772537 := bstep (se 2 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 772537 = 579403) B579403
theorem B2116367 : Blo 455782 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B1952855 : Blo 455782 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B773239 : Blo 455782 773239 := bstep (se 1 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 773239 = 1159859) B1159859
theorem B773435 : Blo 455782 773435 := bstep (se 1 (by rfl) ⟨580076, by rfl⟩ : syracuseStep 773435 = 1160153) B1160153
theorem B2969041 : Blo 455782 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B2084363 : Blo 455782 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B577039 : Blo 455782 577039 := bstep (se 1 (by rfl) ⟨432779, by rfl⟩ : syracuseStep 577039 = 865559) B865559
theorem B773833 : Blo 455782 773833 := bstep (se 2 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 773833 = 580375) B580375
theorem B11128549 : Blo 455782 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B2772751 : Blo 455782 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B3952421 : Blo 455782 3952421 := bstep (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) B741079
theorem B2608955 : Blo 455782 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B2314169 : Blo 455782 2314169 := bstep (se 2 (by rfl) ⟨867813, by rfl⟩ : syracuseStep 2314169 = 1735627) B1735627
theorem B872507 : Blo 455782 872507 := bstep (se 1 (by rfl) ⟨654380, by rfl⟩ : syracuseStep 872507 = 1308761) B1308761
theorem B577783 : Blo 455782 577783 := bstep (se 1 (by rfl) ⟨433337, by rfl⟩ : syracuseStep 577783 = 866675) B866675
theorem B1462643 : Blo 455782 1462643 := bstep (se 1 (by rfl) ⟨1096982, by rfl⟩ : syracuseStep 1462643 = 2193965) B2193965
theorem B774535 : Blo 455782 774535 := bstep (se 1 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 774535 = 1161803) B1161803
theorem B159896081 : Blo 455782 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B1298987 : Blo 455782 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B578107 : Blo 455782 578107 := bstep (se 1 (by rfl) ⟨433580, by rfl⟩ : syracuseStep 578107 = 867161) B867161
theorem B1102423 : Blo 455782 1102423 := bstep (se 1 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 1102423 = 1653635) B1653635
theorem B11096837 : Blo 455782 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B1299215 : Blo 455782 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B1102625 : Blo 455782 1102625 := bstep (se 2 (by rfl) ⟨413484, by rfl⟩ : syracuseStep 1102625 = 826969) B826969
theorem B1856315 : Blo 455782 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B513031 : Blo 455782 513031 := bstep (se 1 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 513031 = 769547) B769547
theorem B775183 : Blo 455782 775183 := bstep (se 1 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 775183 = 1162775) B1162775
theorem B578603 : Blo 455782 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B513211 : Blo 455782 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B2315465 : Blo 455782 2315465 := bstep (se 2 (by rfl) ⟨868299, by rfl⟩ : syracuseStep 2315465 = 1736599) B1736599
theorem B2610413 : Blo 455782 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B579079 : Blo 455782 579079 := bstep (se 1 (by rfl) ⟨434309, by rfl⟩ : syracuseStep 579079 = 868619) B868619
theorem B2610731 : Blo 455782 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B775723 : Blo 455782 775723 := bstep (se 1 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 775723 = 1163585) B1163585
theorem B513679 : Blo 455782 513679 := bstep (se 1 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 513679 = 770519) B770519
theorem B775865 : Blo 455782 775865 := bstep (se 2 (by rfl) ⟨290949, by rfl⟩ : syracuseStep 775865 = 581899) B581899
theorem B1070891 : Blo 455782 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B579575 : Blo 455782 579575 := bstep (se 1 (by rfl) ⟨434681, by rfl⟩ : syracuseStep 579575 = 869363) B869363
theorem B514183 : Blo 455782 514183 := bstep (se 1 (by rfl) ⟨385637, by rfl⟩ : syracuseStep 514183 = 771275) B771275
theorem B579727 : Blo 455782 579727 := bstep (se 1 (by rfl) ⟨434795, by rfl⟩ : syracuseStep 579727 = 869591) B869591
theorem B1300627 : Blo 455782 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B2513069 : Blo 455782 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B2480321 : Blo 455782 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B5921041 : Blo 455782 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B514363 : Blo 455782 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B579899 : Blo 455782 579899 := bstep (se 1 (by rfl) ⟨434924, by rfl⟩ : syracuseStep 579899 = 869849) B869849
theorem B1300855 : Blo 455782 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B1465103 : Blo 455782 1465103 := bstep (se 1 (by rfl) ⟨1098827, by rfl⟩ : syracuseStep 1465103 = 2197655) B2197655
theorem B514831 : Blo 455782 514831 := bstep (se 1 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 514831 = 772247) B772247
theorem B2612189 : Blo 455782 2612189 := bstep (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) B979571
theorem B515335 : Blo 455782 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B580871 : Blo 455782 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B515515 : Blo 455782 515515 := bstep (se 1 (by rfl) ⟨386636, by rfl⟩ : syracuseStep 515515 = 773273) B773273
theorem B974369 : Blo 455782 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B5234219 : Blo 455782 5234219 := bstep (se 1 (by rfl) ⟨3925664, by rfl⟩ : syracuseStep 5234219 = 7851329) B7851329
theorem B1302131 : Blo 455782 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B515983 : Blo 455782 515983 := bstep (se 1 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 515983 = 773975) B773975
theorem B581519 : Blo 455782 581519 := bstep (se 1 (by rfl) ⟨436139, by rfl⟩ : syracuseStep 581519 = 872279) B872279
theorem B1302473 : Blo 455782 1302473 := bstep (se 2 (by rfl) ⟨488427, by rfl⟩ : syracuseStep 1302473 = 976855) B976855
theorem B1302587 : Blo 455782 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B1302713 : Blo 455782 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B516487 : Blo 455782 516487 := bstep (se 1 (by rfl) ⟨387365, by rfl⟩ : syracuseStep 516487 = 774731) B774731
theorem B2646539 : Blo 455782 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B1466923 : Blo 455782 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B516667 : Blo 455782 516667 := bstep (se 1 (by rfl) ⟨387500, by rfl⟩ : syracuseStep 516667 = 775001) B775001
theorem B1237565 : Blo 455782 1237565 := bstep (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) B464087
theorem B1466999 : Blo 455782 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1860499 : Blo 455782 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B1237945 : Blo 455782 1237945 := bstep (se 2 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 1237945 = 928459) B928459
theorem B517135 : Blo 455782 517135 := bstep (se 1 (by rfl) ⟨387851, by rfl⟩ : syracuseStep 517135 = 775703) B775703
theorem B1860727 : Blo 455782 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B2614787 : Blo 455782 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B1238561 : Blo 455782 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B2942507 : Blo 455782 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B616123 : Blo 455782 616123 := bstep (se 1 (by rfl) ⟨462092, by rfl⟩ : syracuseStep 616123 = 924185) B924185
theorem B1304363 : Blo 455782 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B4450099 : Blo 455782 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B3467123 : Blo 455782 3467123 := bstep (se 1 (by rfl) ⟨2600342, by rfl⟩ : syracuseStep 3467123 = 5200685) B5200685
theorem B2484083 : Blo 455782 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B1959947 : Blo 455782 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B1959997 : Blo 455782 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B1337719 : Blo 455782 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B780815 : Blo 455782 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B977555 : Blo 455782 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B1043129 : Blo 455782 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B3893953 : Blo 455782 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B617161 : Blo 455782 617161 := bstep (se 2 (by rfl) ⟨231435, by rfl⟩ : syracuseStep 617161 = 462871) B462871
theorem B1305355 : Blo 455782 1305355 := bstep (se 1 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 1305355 = 1958033) B1958033
theorem B2321297 : Blo 455782 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B5565347 : Blo 455782 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B1305629 : Blo 455782 1305629 := bstep (se 3 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 1305629 = 489611) B489611
theorem B650359 : Blo 455782 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B1469755 : Blo 455782 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B6254009 : Blo 455782 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B2190851 : Blo 455782 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B1568375 : Blo 455782 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B552619 : Blo 455782 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B2649773 : Blo 455782 2649773 := bstep (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) B993665
theorem B683705 : Blo 455782 683705 := bstep (se 2 (by rfl) ⟨256389, by rfl⟩ : syracuseStep 683705 = 512779) B512779
theorem B683783 : Blo 455782 683783 := bstep (se 1 (by rfl) ⟨512837, by rfl⟩ : syracuseStep 683783 = 1025675) B1025675
theorem B683819 : Blo 455782 683819 := bstep (se 1 (by rfl) ⟨512864, by rfl⟩ : syracuseStep 683819 = 1025729) B1025729
theorem B683849 : Blo 455782 683849 := bstep (se 2 (by rfl) ⟨256443, by rfl⟩ : syracuseStep 683849 = 512887) B512887
theorem B1732499 : Blo 455782 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B683963 : Blo 455782 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B2191313 : Blo 455782 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B684023 : Blo 455782 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B684047 : Blo 455782 684047 := bstep (se 1 (by rfl) ⟨513035, by rfl⟩ : syracuseStep 684047 = 1026071) B1026071
theorem B684089 : Blo 455782 684089 := bstep (se 2 (by rfl) ⟨256533, by rfl⟩ : syracuseStep 684089 = 513067) B513067
theorem B684167 : Blo 455782 684167 := bstep (se 1 (by rfl) ⟨513125, by rfl⟩ : syracuseStep 684167 = 1026251) B1026251
theorem B651407 : Blo 455782 651407 := bstep (se 1 (by rfl) ⟨488555, by rfl⟩ : syracuseStep 651407 = 977111) B977111
theorem B684203 : Blo 455782 684203 := bstep (se 1 (by rfl) ⟨513152, by rfl⟩ : syracuseStep 684203 = 1026305) B1026305
theorem B684233 : Blo 455782 684233 := bstep (se 2 (by rfl) ⟨256587, by rfl⟩ : syracuseStep 684233 = 513175) B513175
theorem B684347 : Blo 455782 684347 := bstep (se 1 (by rfl) ⟨513260, by rfl⟩ : syracuseStep 684347 = 1026521) B1026521
theorem B684407 : Blo 455782 684407 := bstep (se 1 (by rfl) ⟨513305, by rfl⟩ : syracuseStep 684407 = 1026611) B1026611
theorem B684431 : Blo 455782 684431 := bstep (se 1 (by rfl) ⟨513323, by rfl⟩ : syracuseStep 684431 = 1026647) B1026647
theorem B684473 : Blo 455782 684473 := bstep (se 2 (by rfl) ⟨256677, by rfl⟩ : syracuseStep 684473 = 513355) B513355
theorem B651721 : Blo 455782 651721 := bstep (se 2 (by rfl) ⟨244395, by rfl⟩ : syracuseStep 651721 = 488791) B488791
theorem B684551 : Blo 455782 684551 := bstep (se 1 (by rfl) ⟨513413, by rfl⟩ : syracuseStep 684551 = 1026827) B1026827
theorem B684587 : Blo 455782 684587 := bstep (se 1 (by rfl) ⟨513440, by rfl⟩ : syracuseStep 684587 = 1026881) B1026881
theorem B684617 : Blo 455782 684617 := bstep (se 2 (by rfl) ⟨256731, by rfl⟩ : syracuseStep 684617 = 513463) B513463
theorem B684731 : Blo 455782 684731 := bstep (se 1 (by rfl) ⟨513548, by rfl⟩ : syracuseStep 684731 = 1027097) B1027097
theorem B684791 : Blo 455782 684791 := bstep (se 1 (by rfl) ⟨513593, by rfl⟩ : syracuseStep 684791 = 1027187) B1027187
theorem B684815 : Blo 455782 684815 := bstep (se 1 (by rfl) ⟨513611, by rfl⟩ : syracuseStep 684815 = 1027223) B1027223
theorem B684857 : Blo 455782 684857 := bstep (se 2 (by rfl) ⟨256821, by rfl⟩ : syracuseStep 684857 = 513643) B513643
theorem B684935 : Blo 455782 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B521095 : Blo 455782 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B684971 : Blo 455782 684971 := bstep (se 1 (by rfl) ⟨513728, by rfl⟩ : syracuseStep 684971 = 1027457) B1027457
theorem B685001 : Blo 455782 685001 := bstep (se 2 (by rfl) ⟨256875, by rfl⟩ : syracuseStep 685001 = 513751) B513751
theorem B979913 : Blo 455782 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B2323403 : Blo 455782 2323403 := bstep (se 1 (by rfl) ⟨1742552, by rfl⟩ : syracuseStep 2323403 = 3485105) B3485105
theorem B685115 : Blo 455782 685115 := bstep (se 1 (by rfl) ⟨513836, by rfl⟩ : syracuseStep 685115 = 1027673) B1027673
theorem B1307735 : Blo 455782 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B685175 : Blo 455782 685175 := bstep (se 1 (by rfl) ⟨513881, by rfl⟩ : syracuseStep 685175 = 1027763) B1027763
theorem B455815 : Blo 455782 455815 := bstep (se 1 (by rfl) ⟨341861, by rfl⟩ : syracuseStep 455815 = 683723) B683723
theorem B455823 : Blo 455782 455823 := bstep (se 1 (by rfl) ⟨341867, by rfl⟩ : syracuseStep 455823 = 683735) B683735
theorem B685199 : Blo 455782 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B685241 : Blo 455782 685241 := bstep (se 2 (by rfl) ⟨256965, by rfl⟩ : syracuseStep 685241 = 513931) B513931
theorem B455867 : Blo 455782 455867 := bstep (se 1 (by rfl) ⟨341900, by rfl⟩ : syracuseStep 455867 = 683801) B683801
theorem B90273005 : Blo 455782 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B455943 : Blo 455782 455943 := bstep (se 1 (by rfl) ⟨341957, by rfl⟩ : syracuseStep 455943 = 683915) B683915
theorem B685319 : Blo 455782 685319 := bstep (se 1 (by rfl) ⟨513989, by rfl⟩ : syracuseStep 685319 = 1027979) B1027979
theorem B455951 : Blo 455782 455951 := bstep (se 1 (by rfl) ⟨341963, by rfl⟩ : syracuseStep 455951 = 683927) B683927
theorem B2323727 : Blo 455782 2323727 := bstep (se 1 (by rfl) ⟨1742795, by rfl⟩ : syracuseStep 2323727 = 3485591) B3485591
theorem B685355 : Blo 455782 685355 := bstep (se 1 (by rfl) ⟨514016, by rfl⟩ : syracuseStep 685355 = 1028033) B1028033
theorem B455995 : Blo 455782 455995 := bstep (se 1 (by rfl) ⟨341996, by rfl⟩ : syracuseStep 455995 = 683993) B683993
theorem B1307963 : Blo 455782 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B685385 : Blo 455782 685385 := bstep (se 2 (by rfl) ⟨257019, by rfl⟩ : syracuseStep 685385 = 514039) B514039
theorem B1963379 : Blo 455782 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B456071 : Blo 455782 456071 := bstep (se 1 (by rfl) ⟨342053, by rfl⟩ : syracuseStep 456071 = 684107) B684107
theorem B456079 : Blo 455782 456079 := bstep (se 1 (by rfl) ⟨342059, by rfl⟩ : syracuseStep 456079 = 684119) B684119
theorem B1308089 : Blo 455782 1308089 := bstep (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) B981067
theorem B456123 : Blo 455782 456123 := bstep (se 1 (by rfl) ⟨342092, by rfl⟩ : syracuseStep 456123 = 684185) B684185
theorem B685499 : Blo 455782 685499 := bstep (se 1 (by rfl) ⟨514124, by rfl⟩ : syracuseStep 685499 = 1028249) B1028249
theorem B685559 : Blo 455782 685559 := bstep (se 1 (by rfl) ⟨514169, by rfl⟩ : syracuseStep 685559 = 1028339) B1028339
theorem B456199 : Blo 455782 456199 := bstep (se 1 (by rfl) ⟨342149, by rfl⟩ : syracuseStep 456199 = 684299) B684299
theorem B1734155 : Blo 455782 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B40138253 : Blo 455782 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B456207 : Blo 455782 456207 := bstep (se 1 (by rfl) ⟨342155, by rfl⟩ : syracuseStep 456207 = 684311) B684311
theorem B685583 : Blo 455782 685583 := bstep (se 1 (by rfl) ⟨514187, by rfl⟩ : syracuseStep 685583 = 1028375) B1028375
theorem B685625 : Blo 455782 685625 := bstep (se 2 (by rfl) ⟨257109, by rfl⟩ : syracuseStep 685625 = 514219) B514219
theorem B456251 : Blo 455782 456251 := bstep (se 1 (by rfl) ⟨342188, by rfl⟩ : syracuseStep 456251 = 684377) B684377
theorem B456327 : Blo 455782 456327 := bstep (se 1 (by rfl) ⟨342245, by rfl⟩ : syracuseStep 456327 = 684491) B684491
theorem B685703 : Blo 455782 685703 := bstep (se 1 (by rfl) ⟨514277, by rfl⟩ : syracuseStep 685703 = 1028555) B1028555
theorem B456335 : Blo 455782 456335 := bstep (se 1 (by rfl) ⟨342251, by rfl⟩ : syracuseStep 456335 = 684503) B684503
theorem B685739 : Blo 455782 685739 := bstep (se 1 (by rfl) ⟨514304, by rfl⟩ : syracuseStep 685739 = 1028609) B1028609
theorem B456379 : Blo 455782 456379 := bstep (se 1 (by rfl) ⟨342284, by rfl⟩ : syracuseStep 456379 = 684569) B684569
theorem B685769 : Blo 455782 685769 := bstep (se 2 (by rfl) ⟨257163, by rfl⟩ : syracuseStep 685769 = 514327) B514327
theorem B456455 : Blo 455782 456455 := bstep (se 1 (by rfl) ⟨342341, by rfl⟩ : syracuseStep 456455 = 684683) B684683
theorem B456463 : Blo 455782 456463 := bstep (se 1 (by rfl) ⟨342347, by rfl⟩ : syracuseStep 456463 = 684695) B684695
theorem B456507 : Blo 455782 456507 := bstep (se 1 (by rfl) ⟨342380, by rfl⟩ : syracuseStep 456507 = 684761) B684761
theorem B685883 : Blo 455782 685883 := bstep (se 1 (by rfl) ⟨514412, by rfl⟩ : syracuseStep 685883 = 1028825) B1028825
theorem B685943 : Blo 455782 685943 := bstep (se 1 (by rfl) ⟨514457, by rfl⟩ : syracuseStep 685943 = 1028915) B1028915
theorem B456583 : Blo 455782 456583 := bstep (se 1 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 456583 = 684875) B684875
theorem B456591 : Blo 455782 456591 := bstep (se 1 (by rfl) ⟨342443, by rfl⟩ : syracuseStep 456591 = 684887) B684887
theorem B685967 : Blo 455782 685967 := bstep (se 1 (by rfl) ⟨514475, by rfl⟩ : syracuseStep 685967 = 1028951) B1028951
theorem B686009 : Blo 455782 686009 := bstep (se 2 (by rfl) ⟨257253, by rfl⟩ : syracuseStep 686009 = 514507) B514507
theorem B456635 : Blo 455782 456635 := bstep (se 1 (by rfl) ⟨342476, by rfl⟩ : syracuseStep 456635 = 684953) B684953
theorem B456711 : Blo 455782 456711 := bstep (se 1 (by rfl) ⟨342533, by rfl⟩ : syracuseStep 456711 = 685067) B685067
theorem B686087 : Blo 455782 686087 := bstep (se 1 (by rfl) ⟨514565, by rfl⟩ : syracuseStep 686087 = 1029131) B1029131
theorem B456719 : Blo 455782 456719 := bstep (se 1 (by rfl) ⟨342539, by rfl⟩ : syracuseStep 456719 = 685079) B685079
theorem B587791 : Blo 455782 587791 := bstep (se 1 (by rfl) ⟨440843, by rfl⟩ : syracuseStep 587791 = 881687) B881687
theorem B686123 : Blo 455782 686123 := bstep (se 1 (by rfl) ⟨514592, by rfl⟩ : syracuseStep 686123 = 1029185) B1029185
theorem B456763 : Blo 455782 456763 := bstep (se 1 (by rfl) ⟨342572, by rfl⟩ : syracuseStep 456763 = 685145) B685145
theorem B686153 : Blo 455782 686153 := bstep (se 2 (by rfl) ⟨257307, by rfl⟩ : syracuseStep 686153 = 514615) B514615
theorem B456839 : Blo 455782 456839 := bstep (se 1 (by rfl) ⟨342629, by rfl⟩ : syracuseStep 456839 = 685259) B685259
theorem B456847 : Blo 455782 456847 := bstep (se 1 (by rfl) ⟨342635, by rfl⟩ : syracuseStep 456847 = 685271) B685271
theorem B456891 : Blo 455782 456891 := bstep (se 1 (by rfl) ⟨342668, by rfl⟩ : syracuseStep 456891 = 685337) B685337
theorem B686267 : Blo 455782 686267 := bstep (se 1 (by rfl) ⟨514700, by rfl⟩ : syracuseStep 686267 = 1029401) B1029401
theorem B686327 : Blo 455782 686327 := bstep (se 1 (by rfl) ⟨514745, by rfl⟩ : syracuseStep 686327 = 1029491) B1029491
theorem B456967 : Blo 455782 456967 := bstep (se 1 (by rfl) ⟨342725, by rfl⟩ : syracuseStep 456967 = 685451) B685451
theorem B456975 : Blo 455782 456975 := bstep (se 1 (by rfl) ⟨342731, by rfl⟩ : syracuseStep 456975 = 685463) B685463
theorem B686351 : Blo 455782 686351 := bstep (se 1 (by rfl) ⟨514763, by rfl⟩ : syracuseStep 686351 = 1029527) B1029527
theorem B686393 : Blo 455782 686393 := bstep (se 2 (by rfl) ⟨257397, by rfl⟩ : syracuseStep 686393 = 514795) B514795
theorem B457019 : Blo 455782 457019 := bstep (se 1 (by rfl) ⟨342764, by rfl⟩ : syracuseStep 457019 = 685529) B685529
theorem B457095 : Blo 455782 457095 := bstep (se 1 (by rfl) ⟨342821, by rfl⟩ : syracuseStep 457095 = 685643) B685643
theorem B686471 : Blo 455782 686471 := bstep (se 1 (by rfl) ⟨514853, by rfl⟩ : syracuseStep 686471 = 1029707) B1029707
theorem B457103 : Blo 455782 457103 := bstep (se 1 (by rfl) ⟨342827, by rfl⟩ : syracuseStep 457103 = 685655) B685655
theorem B489871 : Blo 455782 489871 := bstep (se 1 (by rfl) ⟨367403, by rfl⟩ : syracuseStep 489871 = 734807) B734807
theorem B686507 : Blo 455782 686507 := bstep (se 1 (by rfl) ⟨514880, by rfl⟩ : syracuseStep 686507 = 1029761) B1029761
theorem B457147 : Blo 455782 457147 := bstep (se 1 (by rfl) ⟨342860, by rfl⟩ : syracuseStep 457147 = 685721) B685721
theorem B686537 : Blo 455782 686537 := bstep (se 2 (by rfl) ⟨257451, by rfl⟩ : syracuseStep 686537 = 514903) B514903
theorem B457223 : Blo 455782 457223 := bstep (se 1 (by rfl) ⟨342917, by rfl⟩ : syracuseStep 457223 = 685835) B685835
theorem B457231 : Blo 455782 457231 := bstep (se 1 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 457231 = 685847) B685847
theorem B457275 : Blo 455782 457275 := bstep (se 1 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 457275 = 685913) B685913
theorem B686651 : Blo 455782 686651 := bstep (se 1 (by rfl) ⟨514988, by rfl⟩ : syracuseStep 686651 = 1029977) B1029977
theorem B1538621 : Blo 455782 1538621 := bstep (se 3 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 1538621 = 576983) B576983
theorem B686711 : Blo 455782 686711 := bstep (se 1 (by rfl) ⟨515033, by rfl⟩ : syracuseStep 686711 = 1030067) B1030067
theorem B457351 : Blo 455782 457351 := bstep (se 1 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 457351 = 686027) B686027
theorem B457359 : Blo 455782 457359 := bstep (se 1 (by rfl) ⟨343019, by rfl⟩ : syracuseStep 457359 = 686039) B686039
theorem B686735 : Blo 455782 686735 := bstep (se 1 (by rfl) ⟨515051, by rfl⟩ : syracuseStep 686735 = 1030103) B1030103
theorem B686777 : Blo 455782 686777 := bstep (se 2 (by rfl) ⟨257541, by rfl⟩ : syracuseStep 686777 = 515083) B515083
theorem B457403 : Blo 455782 457403 := bstep (se 1 (by rfl) ⟨343052, by rfl⟩ : syracuseStep 457403 = 686105) B686105
theorem B2325185 : Blo 455782 2325185 := bstep (se 2 (by rfl) ⟨871944, by rfl⟩ : syracuseStep 2325185 = 1743889) B1743889
theorem B457479 : Blo 455782 457479 := bstep (se 1 (by rfl) ⟨343109, by rfl⟩ : syracuseStep 457479 = 686219) B686219
theorem B686855 : Blo 455782 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B457487 : Blo 455782 457487 := bstep (se 1 (by rfl) ⟨343115, by rfl⟩ : syracuseStep 457487 = 686231) B686231
theorem B7535375 : Blo 455782 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B686891 : Blo 455782 686891 := bstep (se 1 (by rfl) ⟨515168, by rfl⟩ : syracuseStep 686891 = 1030337) B1030337
theorem B2194235 : Blo 455782 2194235 := bstep (se 1 (by rfl) ⟨1645676, by rfl⟩ : syracuseStep 2194235 = 3291353) B3291353
theorem B457531 : Blo 455782 457531 := bstep (se 1 (by rfl) ⟨343148, by rfl⟩ : syracuseStep 457531 = 686297) B686297
theorem B686921 : Blo 455782 686921 := bstep (se 2 (by rfl) ⟨257595, by rfl⟩ : syracuseStep 686921 = 515191) B515191
theorem B457607 : Blo 455782 457607 := bstep (se 1 (by rfl) ⟨343205, by rfl⟩ : syracuseStep 457607 = 686411) B686411
theorem B981895 : Blo 455782 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B457615 : Blo 455782 457615 := bstep (se 1 (by rfl) ⟨343211, by rfl⟩ : syracuseStep 457615 = 686423) B686423
theorem B457659 : Blo 455782 457659 := bstep (se 1 (by rfl) ⟨343244, by rfl⟩ : syracuseStep 457659 = 686489) B686489
theorem B687035 : Blo 455782 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B687095 : Blo 455782 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B457735 : Blo 455782 457735 := bstep (se 1 (by rfl) ⟨343301, by rfl⟩ : syracuseStep 457735 = 686603) B686603
theorem B457743 : Blo 455782 457743 := bstep (se 1 (by rfl) ⟨343307, by rfl⟩ : syracuseStep 457743 = 686615) B686615
theorem B687119 : Blo 455782 687119 := bstep (se 1 (by rfl) ⟨515339, by rfl⟩ : syracuseStep 687119 = 1030679) B1030679
theorem B687161 : Blo 455782 687161 := bstep (se 2 (by rfl) ⟨257685, by rfl⟩ : syracuseStep 687161 = 515371) B515371
theorem B457787 : Blo 455782 457787 := bstep (se 1 (by rfl) ⟨343340, by rfl⟩ : syracuseStep 457787 = 686681) B686681
theorem B654409 : Blo 455782 654409 := bstep (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) B490807
theorem B457863 : Blo 455782 457863 := bstep (se 1 (by rfl) ⟨343397, by rfl⟩ : syracuseStep 457863 = 686795) B686795
theorem B687239 : Blo 455782 687239 := bstep (se 1 (by rfl) ⟨515429, by rfl⟩ : syracuseStep 687239 = 1030859) B1030859
theorem B785543 : Blo 455782 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B457871 : Blo 455782 457871 := bstep (se 1 (by rfl) ⟨343403, by rfl⟩ : syracuseStep 457871 = 686807) B686807
theorem B687275 : Blo 455782 687275 := bstep (se 1 (by rfl) ⟨515456, by rfl⟩ : syracuseStep 687275 = 1030913) B1030913
theorem B457915 : Blo 455782 457915 := bstep (se 1 (by rfl) ⟨343436, by rfl⟩ : syracuseStep 457915 = 686873) B686873
theorem B687305 : Blo 455782 687305 := bstep (se 2 (by rfl) ⟨257739, by rfl⟩ : syracuseStep 687305 = 515479) B515479
theorem B457991 : Blo 455782 457991 := bstep (se 1 (by rfl) ⟨343493, by rfl⟩ : syracuseStep 457991 = 686987) B686987
theorem B457999 : Blo 455782 457999 := bstep (se 1 (by rfl) ⟨343499, by rfl⟩ : syracuseStep 457999 = 686999) B686999
theorem B458043 : Blo 455782 458043 := bstep (se 1 (by rfl) ⟨343532, by rfl⟩ : syracuseStep 458043 = 687065) B687065
theorem B687419 : Blo 455782 687419 := bstep (se 1 (by rfl) ⟨515564, by rfl⟩ : syracuseStep 687419 = 1031129) B1031129
theorem B687479 : Blo 455782 687479 := bstep (se 1 (by rfl) ⟨515609, by rfl⟩ : syracuseStep 687479 = 1031219) B1031219
theorem B458119 : Blo 455782 458119 := bstep (se 1 (by rfl) ⟨343589, by rfl⟩ : syracuseStep 458119 = 687179) B687179
theorem B458127 : Blo 455782 458127 := bstep (se 1 (by rfl) ⟨343595, by rfl⟩ : syracuseStep 458127 = 687191) B687191
theorem B687503 : Blo 455782 687503 := bstep (se 1 (by rfl) ⟨515627, by rfl⟩ : syracuseStep 687503 = 1031255) B1031255
theorem B687545 : Blo 455782 687545 := bstep (se 2 (by rfl) ⟨257829, by rfl⟩ : syracuseStep 687545 = 515659) B515659
theorem B458171 : Blo 455782 458171 := bstep (se 1 (by rfl) ⟨343628, by rfl⟩ : syracuseStep 458171 = 687257) B687257
theorem B458247 : Blo 455782 458247 := bstep (se 1 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 458247 = 687371) B687371
theorem B687623 : Blo 455782 687623 := bstep (se 1 (by rfl) ⟨515717, by rfl⟩ : syracuseStep 687623 = 1031435) B1031435
theorem B458255 : Blo 455782 458255 := bstep (se 1 (by rfl) ⟨343691, by rfl⟩ : syracuseStep 458255 = 687383) B687383
theorem B687659 : Blo 455782 687659 := bstep (se 1 (by rfl) ⟨515744, by rfl⟩ : syracuseStep 687659 = 1031489) B1031489
theorem B458299 : Blo 455782 458299 := bstep (se 1 (by rfl) ⟨343724, by rfl⟩ : syracuseStep 458299 = 687449) B687449
theorem B687689 : Blo 455782 687689 := bstep (se 2 (by rfl) ⟨257883, by rfl⟩ : syracuseStep 687689 = 515767) B515767
theorem B458375 : Blo 455782 458375 := bstep (se 1 (by rfl) ⟨343781, by rfl⟩ : syracuseStep 458375 = 687563) B687563
theorem B458383 : Blo 455782 458383 := bstep (se 1 (by rfl) ⟨343787, by rfl⟩ : syracuseStep 458383 = 687575) B687575
theorem B458427 : Blo 455782 458427 := bstep (se 1 (by rfl) ⟨343820, by rfl⟩ : syracuseStep 458427 = 687641) B687641
theorem B687803 : Blo 455782 687803 := bstep (se 1 (by rfl) ⟨515852, by rfl⟩ : syracuseStep 687803 = 1031705) B1031705
theorem B2981569 : Blo 455782 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B687863 : Blo 455782 687863 := bstep (se 1 (by rfl) ⟨515897, by rfl⟩ : syracuseStep 687863 = 1031795) B1031795
theorem B458503 : Blo 455782 458503 := bstep (se 1 (by rfl) ⟨343877, by rfl⟩ : syracuseStep 458503 = 687755) B687755
theorem B458511 : Blo 455782 458511 := bstep (se 1 (by rfl) ⟨343883, by rfl⟩ : syracuseStep 458511 = 687767) B687767
theorem B687887 : Blo 455782 687887 := bstep (se 1 (by rfl) ⟨515915, by rfl⟩ : syracuseStep 687887 = 1031831) B1031831
theorem B2096929 : Blo 455782 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B687929 : Blo 455782 687929 := bstep (se 2 (by rfl) ⟨257973, by rfl⟩ : syracuseStep 687929 = 515947) B515947
theorem B458555 : Blo 455782 458555 := bstep (se 1 (by rfl) ⟨343916, by rfl⟩ : syracuseStep 458555 = 687833) B687833
theorem B786295 : Blo 455782 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B458631 : Blo 455782 458631 := bstep (se 1 (by rfl) ⟨343973, by rfl⟩ : syracuseStep 458631 = 687947) B687947
theorem B688007 : Blo 455782 688007 := bstep (se 1 (by rfl) ⟨516005, by rfl⟩ : syracuseStep 688007 = 1032011) B1032011
theorem B458639 : Blo 455782 458639 := bstep (se 1 (by rfl) ⟨343979, by rfl⟩ : syracuseStep 458639 = 687959) B687959
theorem B688043 : Blo 455782 688043 := bstep (se 1 (by rfl) ⟨516032, by rfl⟩ : syracuseStep 688043 = 1032065) B1032065
theorem B1540025 : Blo 455782 1540025 := bstep (se 2 (by rfl) ⟨577509, by rfl⟩ : syracuseStep 1540025 = 1155019) B1155019
theorem B458683 : Blo 455782 458683 := bstep (se 1 (by rfl) ⟨344012, by rfl⟩ : syracuseStep 458683 = 688025) B688025
theorem B688073 : Blo 455782 688073 := bstep (se 2 (by rfl) ⟨258027, by rfl⟩ : syracuseStep 688073 = 516055) B516055
theorem B2326481 : Blo 455782 2326481 := bstep (se 2 (by rfl) ⟨872430, by rfl⟩ : syracuseStep 2326481 = 1744861) B1744861
theorem B458791 : Blo 455782 458791 := bstep (se 1 (by rfl) ⟨344093, by rfl⟩ : syracuseStep 458791 = 688187) B688187
theorem B458831 : Blo 455782 458831 := bstep (se 1 (by rfl) ⟨344123, by rfl⟩ : syracuseStep 458831 = 688247) B688247
theorem B4456529 : Blo 455782 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B458847 : Blo 455782 458847 := bstep (se 1 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 458847 = 688271) B688271
theorem B2326643 : Blo 455782 2326643 := bstep (se 1 (by rfl) ⟨1744982, by rfl⟩ : syracuseStep 2326643 = 3489965) B3489965
theorem B458875 : Blo 455782 458875 := bstep (se 1 (by rfl) ⟨344156, by rfl⟩ : syracuseStep 458875 = 688313) B688313
theorem B458927 : Blo 455782 458927 := bstep (se 1 (by rfl) ⟨344195, by rfl⟩ : syracuseStep 458927 = 688391) B688391
theorem B458951 : Blo 455782 458951 := bstep (se 1 (by rfl) ⟨344213, by rfl⟩ : syracuseStep 458951 = 688427) B688427
theorem B458971 : Blo 455782 458971 := bstep (se 1 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 458971 = 688457) B688457
theorem B459047 : Blo 455782 459047 := bstep (se 1 (by rfl) ⟨344285, by rfl⟩ : syracuseStep 459047 = 688571) B688571
theorem B459087 : Blo 455782 459087 := bstep (se 1 (by rfl) ⟨344315, by rfl⟩ : syracuseStep 459087 = 688631) B688631
theorem B459103 : Blo 455782 459103 := bstep (se 1 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 459103 = 688655) B688655
theorem B1540457 : Blo 455782 1540457 := bstep (se 2 (by rfl) ⟨577671, by rfl⟩ : syracuseStep 1540457 = 1155343) B1155343
theorem B459131 : Blo 455782 459131 := bstep (se 1 (by rfl) ⟨344348, by rfl⟩ : syracuseStep 459131 = 688697) B688697
theorem B1737085 : Blo 455782 1737085 := bstep (se 3 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 1737085 = 651407) B651407
theorem B688559 : Blo 455782 688559 := bstep (se 1 (by rfl) ⟨516419, by rfl⟩ : syracuseStep 688559 = 1032839) B1032839
theorem B459183 : Blo 455782 459183 := bstep (se 1 (by rfl) ⟨344387, by rfl⟩ : syracuseStep 459183 = 688775) B688775
theorem B459207 : Blo 455782 459207 := bstep (se 1 (by rfl) ⟨344405, by rfl⟩ : syracuseStep 459207 = 688811) B688811
theorem B459227 : Blo 455782 459227 := bstep (se 1 (by rfl) ⟨344420, by rfl⟩ : syracuseStep 459227 = 688841) B688841
theorem B688649 : Blo 455782 688649 := bstep (se 2 (by rfl) ⟨258243, by rfl⟩ : syracuseStep 688649 = 516487) B516487
theorem B688679 : Blo 455782 688679 := bstep (se 1 (by rfl) ⟨516509, by rfl⟩ : syracuseStep 688679 = 1033019) B1033019
theorem B459303 : Blo 455782 459303 := bstep (se 1 (by rfl) ⟨344477, by rfl⟩ : syracuseStep 459303 = 688955) B688955
theorem B459343 : Blo 455782 459343 := bstep (se 1 (by rfl) ⟨344507, by rfl⟩ : syracuseStep 459343 = 689015) B689015
theorem B459359 : Blo 455782 459359 := bstep (se 1 (by rfl) ⟨344519, by rfl⟩ : syracuseStep 459359 = 689039) B689039
theorem B688763 : Blo 455782 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B459387 : Blo 455782 459387 := bstep (se 1 (by rfl) ⟨344540, by rfl⟩ : syracuseStep 459387 = 689081) B689081
theorem B459439 : Blo 455782 459439 := bstep (se 1 (by rfl) ⟨344579, by rfl⟩ : syracuseStep 459439 = 689159) B689159
theorem B459463 : Blo 455782 459463 := bstep (se 1 (by rfl) ⟨344597, by rfl⟩ : syracuseStep 459463 = 689195) B689195
theorem B459483 : Blo 455782 459483 := bstep (se 1 (by rfl) ⟨344612, by rfl⟩ : syracuseStep 459483 = 689225) B689225
theorem B688889 : Blo 455782 688889 := bstep (se 2 (by rfl) ⟨258333, by rfl⟩ : syracuseStep 688889 = 516667) B516667
theorem B459559 : Blo 455782 459559 := bstep (se 1 (by rfl) ⟨344669, by rfl⟩ : syracuseStep 459559 = 689339) B689339
theorem B7537481 : Blo 455782 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B459599 : Blo 455782 459599 := bstep (se 1 (by rfl) ⟨344699, by rfl⟩ : syracuseStep 459599 = 689399) B689399
theorem B688991 : Blo 455782 688991 := bstep (se 1 (by rfl) ⟨516743, by rfl⟩ : syracuseStep 688991 = 1033487) B1033487
theorem B459615 : Blo 455782 459615 := bstep (se 1 (by rfl) ⟨344711, by rfl⟩ : syracuseStep 459615 = 689423) B689423
theorem B689003 : Blo 455782 689003 := bstep (se 1 (by rfl) ⟨516752, by rfl⟩ : syracuseStep 689003 = 1033505) B1033505
theorem B459643 : Blo 455782 459643 := bstep (se 1 (by rfl) ⟨344732, by rfl⟩ : syracuseStep 459643 = 689465) B689465
theorem B459695 : Blo 455782 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B1541051 : Blo 455782 1541051 := bstep (se 1 (by rfl) ⟨1155788, by rfl⟩ : syracuseStep 1541051 = 2311577) B2311577
theorem B459719 : Blo 455782 459719 := bstep (se 1 (by rfl) ⟨344789, by rfl⟩ : syracuseStep 459719 = 689579) B689579
theorem B459739 : Blo 455782 459739 := bstep (se 1 (by rfl) ⟨344804, by rfl⟩ : syracuseStep 459739 = 689609) B689609
theorem B24052787 : Blo 455782 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B689231 : Blo 455782 689231 := bstep (se 1 (by rfl) ⟨516923, by rfl⟩ : syracuseStep 689231 = 1033847) B1033847
theorem B689351 : Blo 455782 689351 := bstep (se 1 (by rfl) ⟨517013, by rfl⟩ : syracuseStep 689351 = 1034027) B1034027
theorem B689513 : Blo 455782 689513 := bstep (se 2 (by rfl) ⟨258567, by rfl⟩ : syracuseStep 689513 = 517135) B517135
theorem B689591 : Blo 455782 689591 := bstep (se 1 (by rfl) ⟨517193, by rfl⟩ : syracuseStep 689591 = 1034387) B1034387
theorem B689627 : Blo 455782 689627 := bstep (se 1 (by rfl) ⟨517220, by rfl⟩ : syracuseStep 689627 = 1034441) B1034441
theorem B1410911 : Blo 455782 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B3475385 : Blo 455782 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B4950173 : Blo 455782 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B821497 : Blo 455782 821497 := bstep (se 2 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 821497 = 616123) B616123
theorem B1673597 : Blo 455782 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B5933465 : Blo 455782 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B1739303 : Blo 455782 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B1542779 : Blo 455782 1542779 := bstep (se 1 (by rfl) ⟨1157084, by rfl⟩ : syracuseStep 1542779 = 2314169) B2314169
theorem B1542941 : Blo 455782 1542941 := bstep (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) B578603
theorem B2198345 : Blo 455782 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B106597387 : Blo 455782 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B1543643 : Blo 455782 1543643 := bstep (se 1 (by rfl) ⟨1157732, by rfl⟩ : syracuseStep 1543643 = 2315465) B2315465
theorem B1740275 : Blo 455782 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B822881 : Blo 455782 822881 := bstep (se 2 (by rfl) ⟨308580, by rfl⟩ : syracuseStep 822881 = 617161) B617161
theorem B1740473 : Blo 455782 1740473 := bstep (se 2 (by rfl) ⟨652677, by rfl⟩ : syracuseStep 1740473 = 1305355) B1305355
theorem B1740487 : Blo 455782 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B1675379 : Blo 455782 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1544345 : Blo 455782 1544345 := bstep (se 2 (by rfl) ⟨579129, by rfl⟩ : syracuseStep 1544345 = 1158259) B1158259
theorem B3379589 : Blo 455782 3379589 := bstep (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) B633673
theorem B1741459 : Blo 455782 1741459 := bstep (se 1 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 1741459 = 2612189) B2612189
theorem B3478301 : Blo 455782 3478301 := bstep (se 3 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 3478301 = 1304363) B1304363
theorem B1643599 : Blo 455782 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B1545533 : Blo 455782 1545533 := bstep (se 3 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 1545533 = 579575) B579575
theorem B4953545 : Blo 455782 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B4462141 : Blo 455782 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B6330469 : Blo 455782 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B1546397 : Blo 455782 1546397 := bstep (se 3 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 1546397 = 579899) B579899
theorem B1743191 : Blo 455782 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B825707 : Blo 455782 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B694793 : Blo 455782 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B1546937 : Blo 455782 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B1153865 : Blo 455782 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B465787 : Blo 455782 465787 := bstep (se 1 (by rfl) ⟨349340, by rfl⟩ : syracuseStep 465787 = 698681) B698681
theorem B1547531 : Blo 455782 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B3710231 : Blo 455782 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B1547801 : Blo 455782 1547801 := bstep (se 2 (by rfl) ⟨580425, by rfl⟩ : syracuseStep 1547801 = 1160851) B1160851
theorem B4169339 : Blo 455782 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B1154999 : Blo 455782 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B3285353 : Blo 455782 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B1548935 : Blo 455782 1548935 := bstep (se 1 (by rfl) ⟨1161701, by rfl⟩ : syracuseStep 1548935 = 2323403) B2323403
theorem B1548989 : Blo 455782 1548989 := bstep (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) B580871
theorem B1549151 : Blo 455782 1549151 := bstep (se 1 (by rfl) ⟨1161863, by rfl⟩ : syracuseStep 1549151 = 2323727) B2323727
theorem B1647479 : Blo 455782 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B1549313 : Blo 455782 1549313 := bstep (se 2 (by rfl) ⟨580992, by rfl⟩ : syracuseStep 1549313 = 1161985) B1161985
theorem B1156103 : Blo 455782 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B3482675 : Blo 455782 3482675 := bstep (se 1 (by rfl) ⟨2612006, by rfl⟩ : syracuseStep 3482675 = 5224013) B5224013
theorem B1156153 : Blo 455782 1156153 := bstep (se 2 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 1156153 = 867115) B867115
theorem B1156457 : Blo 455782 1156457 := bstep (se 2 (by rfl) ⟨433671, by rfl⟩ : syracuseStep 1156457 = 867343) B867343
theorem B2598317 : Blo 455782 2598317 := bstep (se 3 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 2598317 = 974369) B974369
theorem B3352103 : Blo 455782 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B3286651 : Blo 455782 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B1025747 : Blo 455782 1025747 := bstep (se 1 (by rfl) ⟨769310, by rfl⟩ : syracuseStep 1025747 = 1538621) B1538621
theorem B1550123 : Blo 455782 1550123 := bstep (se 1 (by rfl) ⟨1162592, by rfl⟩ : syracuseStep 1550123 = 2325185) B2325185
theorem B5023583 : Blo 455782 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B1550393 : Blo 455782 1550393 := bstep (se 2 (by rfl) ⟨581397, by rfl⟩ : syracuseStep 1550393 = 1162795) B1162795
theorem B3975425 : Blo 455782 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B1550717 : Blo 455782 1550717 := bstep (se 3 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 1550717 = 581519) B581519
theorem B2795905 : Blo 455782 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B4401611 : Blo 455782 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B1026683 : Blo 455782 1026683 := bstep (se 1 (by rfl) ⟨770012, by rfl⟩ : syracuseStep 1026683 = 1540025) B1540025
theorem B1550987 : Blo 455782 1550987 := bstep (se 1 (by rfl) ⟨1163240, by rfl⟩ : syracuseStep 1550987 = 2326481) B2326481
theorem B1026809 : Blo 455782 1026809 := bstep (se 2 (by rfl) ⟨385053, by rfl⟩ : syracuseStep 1026809 = 770107) B770107
theorem B1027079 : Blo 455782 1027079 := bstep (se 1 (by rfl) ⟨770309, by rfl⟩ : syracuseStep 1027079 = 1540619) B1540619
theorem B732167 : Blo 455782 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B1027151 : Blo 455782 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B1027547 : Blo 455782 1027547 := bstep (se 1 (by rfl) ⟨770660, by rfl⟩ : syracuseStep 1027547 = 1541321) B1541321
theorem B1158695 : Blo 455782 1158695 := bstep (se 1 (by rfl) ⟨869021, by rfl⟩ : syracuseStep 1158695 = 1738043) B1738043
theorem B1159019 : Blo 455782 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B1650593 : Blo 455782 1650593 := bstep (se 2 (by rfl) ⟨618972, by rfl⟩ : syracuseStep 1650593 = 1237945) B1237945
theorem B1028015 : Blo 455782 1028015 := bstep (se 1 (by rfl) ⟨771011, by rfl⟩ : syracuseStep 1028015 = 1542023) B1542023
theorem B7450555 : Blo 455782 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B1650707 : Blo 455782 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B1028267 : Blo 455782 1028267 := bstep (se 1 (by rfl) ⟨771200, by rfl⟩ : syracuseStep 1028267 = 1542401) B1542401
theorem B1159667 : Blo 455782 1159667 := bstep (se 1 (by rfl) ⟨869750, by rfl⟩ : syracuseStep 1159667 = 1739501) B1739501
theorem B1028807 : Blo 455782 1028807 := bstep (se 1 (by rfl) ⟨771605, by rfl⟩ : syracuseStep 1028807 = 1543211) B1543211
theorem B1159879 : Blo 455782 1159879 := bstep (se 1 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 1159879 = 1739819) B1739819
theorem B2470763 : Blo 455782 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B1389575 : Blo 455782 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B2634947 : Blo 455782 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B1029671 : Blo 455782 1029671 := bstep (se 1 (by rfl) ⟨772253, by rfl⟩ : syracuseStep 1029671 = 1544507) B1544507
theorem B931385 : Blo 455782 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B1160801 : Blo 455782 1160801 := bstep (se 2 (by rfl) ⟨435300, by rfl⟩ : syracuseStep 1160801 = 870601) B870601
theorem B865991 : Blo 455782 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B1783625 : Blo 455782 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B866143 : Blo 455782 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B1029995 : Blo 455782 1029995 := bstep (se 1 (by rfl) ⟨772496, by rfl⟩ : syracuseStep 1029995 = 1544993) B1544993
theorem B735083 : Blo 455782 735083 := bstep (se 1 (by rfl) ⟨551312, by rfl⟩ : syracuseStep 735083 = 1102625) B1102625
theorem B1030049 : Blo 455782 1030049 := bstep (se 2 (by rfl) ⟨386268, by rfl⟩ : syracuseStep 1030049 = 772537) B772537
theorem B1095599 : Blo 455782 1095599 := bstep (se 1 (by rfl) ⟨821699, by rfl⟩ : syracuseStep 1095599 = 1643399) B1643399
theorem B5027777 : Blo 455782 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B5027789 : Blo 455782 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2930717 : Blo 455782 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B2603123 : Blo 455782 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B1030391 : Blo 455782 1030391 := bstep (se 1 (by rfl) ⟨772793, by rfl⟩ : syracuseStep 1030391 = 1545587) B1545587
theorem B5191937 : Blo 455782 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B188627285 : Blo 455782 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B10566389 : Blo 455782 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B1653547 : Blo 455782 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B1030985 : Blo 455782 1030985 := bstep (se 2 (by rfl) ⟨386619, by rfl⟩ : syracuseStep 1030985 = 773239) B773239
theorem B1162259 : Blo 455782 1162259 := bstep (se 1 (by rfl) ⟨871694, by rfl⟩ : syracuseStep 1162259 = 1743389) B1743389
theorem B7846955 : Blo 455782 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B769223 : Blo 455782 769223 := bstep (se 1 (by rfl) ⟨576917, by rfl⟩ : syracuseStep 769223 = 1153835) B1153835
theorem B769385 : Blo 455782 769385 := bstep (se 2 (by rfl) ⟨288519, by rfl⟩ : syracuseStep 769385 = 577039) B577039
theorem B1031777 : Blo 455782 1031777 := bstep (se 2 (by rfl) ⟨386916, by rfl⟩ : syracuseStep 1031777 = 773833) B773833
theorem B3489479 : Blo 455782 3489479 := bstep (se 1 (by rfl) ⟨2617109, by rfl⟩ : syracuseStep 3489479 = 5234219) B5234219
theorem B769783 : Blo 455782 769783 := bstep (se 1 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 769783 = 1154675) B1154675
theorem B868087 : Blo 455782 868087 := bstep (se 1 (by rfl) ⟨651065, by rfl⟩ : syracuseStep 868087 = 1302131) B1302131
theorem B1949507 : Blo 455782 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B1032119 : Blo 455782 1032119 := bstep (se 1 (by rfl) ⟨774089, by rfl⟩ : syracuseStep 1032119 = 1548179) B1548179
theorem B769979 : Blo 455782 769979 := bstep (se 1 (by rfl) ⟨577484, by rfl⟩ : syracuseStep 769979 = 1154969) B1154969
theorem B868315 : Blo 455782 868315 := bstep (se 1 (by rfl) ⟨651236, by rfl⟩ : syracuseStep 868315 = 1302473) B1302473
theorem B770087 : Blo 455782 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B868391 : Blo 455782 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B868475 : Blo 455782 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B770377 : Blo 455782 770377 := bstep (se 2 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 770377 = 577783) B577783
theorem B770411 : Blo 455782 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B1032713 : Blo 455782 1032713 := bstep (se 2 (by rfl) ⟨387267, by rfl⟩ : syracuseStep 1032713 = 774535) B774535
theorem B868961 : Blo 455782 868961 := bstep (se 2 (by rfl) ⟨325860, by rfl⟩ : syracuseStep 868961 = 651721) B651721
theorem B770809 : Blo 455782 770809 := bstep (se 2 (by rfl) ⟨289053, by rfl⟩ : syracuseStep 770809 = 578107) B578107
theorem B1033055 : Blo 455782 1033055 := bstep (se 1 (by rfl) ⟨774791, by rfl⟩ : syracuseStep 1033055 = 1549583) B1549583
theorem B771079 : Blo 455782 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B1033235 : Blo 455782 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B1098809 : Blo 455782 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B2311415 : Blo 455782 2311415 := bstep (se 1 (by rfl) ⟨1733561, by rfl⟩ : syracuseStep 2311415 = 3467123) B3467123
theorem B1656055 : Blo 455782 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1033577 : Blo 455782 1033577 := bstep (se 2 (by rfl) ⟨387591, by rfl⟩ : syracuseStep 1033577 = 775183) B775183
theorem B771511 : Blo 455782 771511 := bstep (se 1 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 771511 = 1157267) B1157267
theorem B771707 : Blo 455782 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B2311901 : Blo 455782 2311901 := bstep (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) B866963
theorem B2606813 : Blo 455782 2606813 := bstep (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) B977555
theorem B1034171 : Blo 455782 1034171 := bstep (se 1 (by rfl) ⟨775628, by rfl⟩ : syracuseStep 1034171 = 1551257) B1551257
theorem B772105 : Blo 455782 772105 := bstep (se 2 (by rfl) ⟨289539, by rfl⟩ : syracuseStep 772105 = 579079) B579079
theorem B870419 : Blo 455782 870419 := bstep (se 1 (by rfl) ⟨652814, by rfl⟩ : syracuseStep 870419 = 1305629) B1305629
theorem B1034297 : Blo 455782 1034297 := bstep (se 2 (by rfl) ⟨387861, by rfl⟩ : syracuseStep 1034297 = 775723) B775723
theorem B772267 : Blo 455782 772267 := bstep (se 1 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 772267 = 1158401) B1158401
theorem B1460567 : Blo 455782 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B772571 : Blo 455782 772571 := bstep (se 1 (by rfl) ⟨579428, by rfl⟩ : syracuseStep 772571 = 1158857) B1158857
theorem B5884397 : Blo 455782 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B1460875 : Blo 455782 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B772807 : Blo 455782 772807 := bstep (se 1 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 772807 = 1159211) B1159211
theorem B772969 : Blo 455782 772969 := bstep (se 2 (by rfl) ⟨289863, by rfl⟩ : syracuseStep 772969 = 579727) B579727
theorem B3132695 : Blo 455782 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B11783555 : Blo 455782 11783555 := bstep (se 1 (by rfl) ⟨8837666, by rfl⟩ : syracuseStep 11783555 = 17675333) B17675333
theorem B871823 : Blo 455782 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B773563 : Blo 455782 773563 := bstep (se 1 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 773563 = 1160345) B1160345
theorem B60182003 : Blo 455782 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B773671 : Blo 455782 773671 := bstep (se 1 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 773671 = 1160507) B1160507
theorem B871975 : Blo 455782 871975 := bstep (se 1 (by rfl) ⟨653981, by rfl⟩ : syracuseStep 871975 = 1307963) B1307963
theorem B872059 : Blo 455782 872059 := bstep (se 1 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 872059 = 1308089) B1308089
theorem B26758835 : Blo 455782 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B773995 : Blo 455782 773995 := bstep (se 1 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 773995 = 1160993) B1160993
theorem B4411421 : Blo 455782 4411421 := bstep (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) B1654283
theorem B872545 : Blo 455782 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B7066061 : Blo 455782 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B578011 : Blo 455782 578011 := bstep (se 1 (by rfl) ⟨433508, by rfl⟩ : syracuseStep 578011 = 867017) B867017
theorem B1462823 : Blo 455782 1462823 := bstep (se 1 (by rfl) ⟨1097117, by rfl⟩ : syracuseStep 1462823 = 2194235) B2194235
theorem B8802917 : Blo 455782 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B5952211 : Blo 455782 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B775055 : Blo 455782 775055 := bstep (se 1 (by rfl) ⟨581291, by rfl⟩ : syracuseStep 775055 = 1162583) B1162583
theorem B1561531 : Blo 455782 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B513103 : Blo 455782 513103 := bstep (se 1 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 513103 = 769655) B769655
theorem B3462263 : Blo 455782 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B775291 : Blo 455782 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B513499 : Blo 455782 513499 := bstep (se 1 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 513499 = 770249) B770249
theorem B1463771 : Blo 455782 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B1955315 : Blo 455782 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B513967 : Blo 455782 513967 := bstep (se 1 (by rfl) ⟨385475, by rfl⟩ : syracuseStep 513967 = 770951) B770951
theorem B20043821 : Blo 455782 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B1955897 : Blo 455782 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B1235101 : Blo 455782 1235101 := bstep (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) B463163
theorem B5855489 : Blo 455782 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B514399 : Blo 455782 514399 := bstep (se 1 (by rfl) ⟨385799, by rfl⟩ : syracuseStep 514399 = 771599) B771599
theorem B514759 : Blo 455782 514759 := bstep (se 1 (by rfl) ⟨386069, by rfl⟩ : syracuseStep 514759 = 772139) B772139
theorem B2317085 : Blo 455782 2317085 := bstep (se 3 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 2317085 = 868907) B868907
theorem B2480969 : Blo 455782 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B3300173 : Blo 455782 3300173 := bstep (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) B1237565
theorem B5888861 : Blo 455782 5888861 := bstep (se 3 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 5888861 = 2208323) B2208323
theorem B1301903 : Blo 455782 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B2612645 : Blo 455782 2612645 := bstep (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) B489871
theorem B515623 : Blo 455782 515623 := bstep (se 1 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 515623 = 773435) B773435
theorem B4415417 : Blo 455782 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B581671 : Blo 455782 581671 := bstep (se 1 (by rfl) ⟨436253, by rfl⟩ : syracuseStep 581671 = 872507) B872507
theorem B2613329 : Blo 455782 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B975095 : Blo 455782 975095 := bstep (se 1 (by rfl) ⟨731321, by rfl⟩ : syracuseStep 975095 = 1462643) B1462643
theorem B7397891 : Blo 455782 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B5235677 : Blo 455782 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B877625 : Blo 455782 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B517243 : Blo 455782 517243 := bstep (se 1 (by rfl) ⟨387932, by rfl⟩ : syracuseStep 517243 = 775865) B775865
theorem B713927 : Blo 455782 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B14116355 : Blo 455782 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B616015 : Blo 455782 616015 := bstep (se 1 (by rfl) ⟨462011, by rfl⟩ : syracuseStep 616015 = 924023) B924023
theorem B878177 : Blo 455782 878177 := bstep (se 2 (by rfl) ⟨329316, by rfl⟩ : syracuseStep 878177 = 658633) B658633
theorem B5203601 : Blo 455782 5203601 := bstep (se 2 (by rfl) ⟨1951350, by rfl⟩ : syracuseStep 5203601 = 3902701) B3902701
theorem B1468115 : Blo 455782 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1238777 : Blo 455782 1238777 := bstep (se 2 (by rfl) ⟨464541, by rfl⟩ : syracuseStep 1238777 = 929083) B929083
theorem B1959673 : Blo 455782 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B976735 : Blo 455782 976735 := bstep (se 1 (by rfl) ⟨732551, by rfl⟩ : syracuseStep 976735 = 1465103) B1465103
theorem B4417375 : Blo 455782 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B3303287 : Blo 455782 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B3958721 : Blo 455782 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1534009 : Blo 455782 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B9922661 : Blo 455782 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B14838065 : Blo 455782 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B3697001 : Blo 455782 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B13200101 : Blo 455782 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B3533645 : Blo 455782 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B1764359 : Blo 455782 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B1469459 : Blo 455782 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B2321459 : Blo 455782 2321459 := bstep (se 1 (by rfl) ⟨1741094, by rfl⟩ : syracuseStep 2321459 = 3482189) B3482189
theorem B977999 : Blo 455782 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B3468581 : Blo 455782 3468581 := bstep (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) B650359
theorem B1764713 : Blo 455782 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1469897 : Blo 455782 1469897 := bstep (se 2 (by rfl) ⟨551211, by rfl⟩ : syracuseStep 1469897 = 1102423) B1102423
theorem B1666585 : Blo 455782 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B1961671 : Blo 455782 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B3698551 : Blo 455782 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B683951 : Blo 455782 683951 := bstep (se 1 (by rfl) ⟨512963, by rfl⟩ : syracuseStep 683951 = 1025927) B1025927
theorem B1470383 : Blo 455782 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B1306631 : Blo 455782 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B684041 : Blo 455782 684041 := bstep (se 2 (by rfl) ⟨256515, by rfl⟩ : syracuseStep 684041 = 513031) B513031
theorem B684071 : Blo 455782 684071 := bstep (se 1 (by rfl) ⟨513053, by rfl⟩ : syracuseStep 684071 = 1026107) B1026107
theorem B684155 : Blo 455782 684155 := bstep (se 1 (by rfl) ⟨513116, by rfl⟩ : syracuseStep 684155 = 1026233) B1026233
theorem B684281 : Blo 455782 684281 := bstep (se 2 (by rfl) ⟨256605, by rfl⟩ : syracuseStep 684281 = 513211) B513211
theorem B684383 : Blo 455782 684383 := bstep (se 1 (by rfl) ⟨513287, by rfl⟩ : syracuseStep 684383 = 1026575) B1026575
theorem B520543 : Blo 455782 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B618847 : Blo 455782 618847 := bstep (se 1 (by rfl) ⟨464135, by rfl⟩ : syracuseStep 618847 = 928271) B928271
theorem B684395 : Blo 455782 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B2781677 : Blo 455782 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B4682299 : Blo 455782 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B684623 : Blo 455782 684623 := bstep (se 1 (by rfl) ⟨513467, by rfl⟩ : syracuseStep 684623 = 1026935) B1026935
theorem B2323079 : Blo 455782 2323079 := bstep (se 1 (by rfl) ⟨1742309, by rfl⟩ : syracuseStep 2323079 = 3484619) B3484619
theorem B684743 : Blo 455782 684743 := bstep (se 1 (by rfl) ⟨513557, by rfl⟩ : syracuseStep 684743 = 1027115) B1027115
theorem B1733471 : Blo 455782 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B684905 : Blo 455782 684905 := bstep (se 2 (by rfl) ⟨256839, by rfl⟩ : syracuseStep 684905 = 513679) B513679
theorem B684983 : Blo 455782 684983 := bstep (se 1 (by rfl) ⟨513737, by rfl⟩ : syracuseStep 684983 = 1027475) B1027475
theorem B685019 : Blo 455782 685019 := bstep (se 1 (by rfl) ⟨513764, by rfl⟩ : syracuseStep 685019 = 1027529) B1027529
theorem B1045583 : Blo 455782 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B455803 : Blo 455782 455803 := bstep (se 1 (by rfl) ⟨341852, by rfl⟩ : syracuseStep 455803 = 683705) B683705
theorem B455855 : Blo 455782 455855 := bstep (se 1 (by rfl) ⟨341891, by rfl⟩ : syracuseStep 455855 = 683783) B683783
theorem B455879 : Blo 455782 455879 := bstep (se 1 (by rfl) ⟨341909, by rfl⟩ : syracuseStep 455879 = 683819) B683819
theorem B5862617 : Blo 455782 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B455899 : Blo 455782 455899 := bstep (se 1 (by rfl) ⟨341924, by rfl⟩ : syracuseStep 455899 = 683849) B683849
theorem B455975 : Blo 455782 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B456015 : Blo 455782 456015 := bstep (se 1 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 456015 = 684023) B684023
theorem B456031 : Blo 455782 456031 := bstep (se 1 (by rfl) ⟨342023, by rfl⟩ : syracuseStep 456031 = 684047) B684047
theorem B783721 : Blo 455782 783721 := bstep (se 2 (by rfl) ⟨293895, by rfl⟩ : syracuseStep 783721 = 587791) B587791
theorem B456059 : Blo 455782 456059 := bstep (se 1 (by rfl) ⟨342044, by rfl⟩ : syracuseStep 456059 = 684089) B684089
theorem B456111 : Blo 455782 456111 := bstep (se 1 (by rfl) ⟨342083, by rfl⟩ : syracuseStep 456111 = 684167) B684167
theorem B685487 : Blo 455782 685487 := bstep (se 1 (by rfl) ⟨514115, by rfl⟩ : syracuseStep 685487 = 1028231) B1028231
theorem B456135 : Blo 455782 456135 := bstep (se 1 (by rfl) ⟨342101, by rfl⟩ : syracuseStep 456135 = 684203) B684203
theorem B456155 : Blo 455782 456155 := bstep (se 1 (by rfl) ⟨342116, by rfl⟩ : syracuseStep 456155 = 684233) B684233
theorem B685577 : Blo 455782 685577 := bstep (se 2 (by rfl) ⟨257091, by rfl⟩ : syracuseStep 685577 = 514183) B514183
theorem B1734169 : Blo 455782 1734169 := bstep (se 2 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 1734169 = 1300627) B1300627
theorem B456231 : Blo 455782 456231 := bstep (se 1 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 456231 = 684347) B684347
theorem B685607 : Blo 455782 685607 := bstep (se 1 (by rfl) ⟨514205, by rfl⟩ : syracuseStep 685607 = 1028411) B1028411
theorem B456271 : Blo 455782 456271 := bstep (se 1 (by rfl) ⟨342203, by rfl⟩ : syracuseStep 456271 = 684407) B684407
theorem B456287 : Blo 455782 456287 := bstep (se 1 (by rfl) ⟨342215, by rfl⟩ : syracuseStep 456287 = 684431) B684431
theorem B456315 : Blo 455782 456315 := bstep (se 1 (by rfl) ⟨342236, by rfl⟩ : syracuseStep 456315 = 684473) B684473
theorem B685691 : Blo 455782 685691 := bstep (se 1 (by rfl) ⟨514268, by rfl⟩ : syracuseStep 685691 = 1028537) B1028537
theorem B456367 : Blo 455782 456367 := bstep (se 1 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 456367 = 684551) B684551
theorem B2094781 : Blo 455782 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B7894721 : Blo 455782 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B456391 : Blo 455782 456391 := bstep (se 1 (by rfl) ⟨342293, by rfl⟩ : syracuseStep 456391 = 684587) B684587
theorem B620231 : Blo 455782 620231 := bstep (se 1 (by rfl) ⟨465173, by rfl⟩ : syracuseStep 620231 = 930347) B930347
theorem B456411 : Blo 455782 456411 := bstep (se 1 (by rfl) ⟨342308, by rfl⟩ : syracuseStep 456411 = 684617) B684617
theorem B685817 : Blo 455782 685817 := bstep (se 2 (by rfl) ⟨257181, by rfl⟩ : syracuseStep 685817 = 514363) B514363
theorem B456487 : Blo 455782 456487 := bstep (se 1 (by rfl) ⟨342365, by rfl⟩ : syracuseStep 456487 = 684731) B684731
theorem B1734443 : Blo 455782 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B1734473 : Blo 455782 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B456527 : Blo 455782 456527 := bstep (se 1 (by rfl) ⟨342395, by rfl⟩ : syracuseStep 456527 = 684791) B684791
theorem B456543 : Blo 455782 456543 := bstep (se 1 (by rfl) ⟨342407, by rfl⟩ : syracuseStep 456543 = 684815) B684815
theorem B685919 : Blo 455782 685919 := bstep (se 1 (by rfl) ⟨514439, by rfl⟩ : syracuseStep 685919 = 1028879) B1028879
theorem B685931 : Blo 455782 685931 := bstep (se 1 (by rfl) ⟨514448, by rfl⟩ : syracuseStep 685931 = 1028897) B1028897
theorem B456571 : Blo 455782 456571 := bstep (se 1 (by rfl) ⟨342428, by rfl⟩ : syracuseStep 456571 = 684857) B684857
theorem B456623 : Blo 455782 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B456647 : Blo 455782 456647 := bstep (se 1 (by rfl) ⟨342485, by rfl⟩ : syracuseStep 456647 = 684971) B684971
theorem B456667 : Blo 455782 456667 := bstep (se 1 (by rfl) ⟨342500, by rfl⟩ : syracuseStep 456667 = 685001) B685001
theorem B653275 : Blo 455782 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B456743 : Blo 455782 456743 := bstep (se 1 (by rfl) ⟨342557, by rfl⟩ : syracuseStep 456743 = 685115) B685115
theorem B2324537 : Blo 455782 2324537 := bstep (se 2 (by rfl) ⟨871701, by rfl⟩ : syracuseStep 2324537 = 1743403) B1743403
theorem B456783 : Blo 455782 456783 := bstep (se 1 (by rfl) ⟨342587, by rfl⟩ : syracuseStep 456783 = 685175) B685175
theorem B686159 : Blo 455782 686159 := bstep (se 1 (by rfl) ⟨514619, by rfl⟩ : syracuseStep 686159 = 1029239) B1029239
theorem B456799 : Blo 455782 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B456827 : Blo 455782 456827 := bstep (se 1 (by rfl) ⟨342620, by rfl⟩ : syracuseStep 456827 = 685241) B685241
theorem B456879 : Blo 455782 456879 := bstep (se 1 (by rfl) ⟨342659, by rfl⟩ : syracuseStep 456879 = 685319) B685319
theorem B456903 : Blo 455782 456903 := bstep (se 1 (by rfl) ⟨342677, by rfl⟩ : syracuseStep 456903 = 685355) B685355
theorem B686279 : Blo 455782 686279 := bstep (se 1 (by rfl) ⟨514709, by rfl⟩ : syracuseStep 686279 = 1029419) B1029419
theorem B456923 : Blo 455782 456923 := bstep (se 1 (by rfl) ⟨342692, by rfl⟩ : syracuseStep 456923 = 685385) B685385
theorem B456999 : Blo 455782 456999 := bstep (se 1 (by rfl) ⟨342749, by rfl⟩ : syracuseStep 456999 = 685499) B685499
theorem B457039 : Blo 455782 457039 := bstep (se 1 (by rfl) ⟨342779, by rfl⟩ : syracuseStep 457039 = 685559) B685559
theorem B457055 : Blo 455782 457055 := bstep (se 1 (by rfl) ⟨342791, by rfl⟩ : syracuseStep 457055 = 685583) B685583
theorem B686441 : Blo 455782 686441 := bstep (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) B514831
theorem B457083 : Blo 455782 457083 := bstep (se 1 (by rfl) ⟨342812, by rfl⟩ : syracuseStep 457083 = 685625) B685625
theorem B457135 : Blo 455782 457135 := bstep (se 1 (by rfl) ⟨342851, by rfl⟩ : syracuseStep 457135 = 685703) B685703
theorem B686519 : Blo 455782 686519 := bstep (se 1 (by rfl) ⟨514889, by rfl⟩ : syracuseStep 686519 = 1029779) B1029779
theorem B457159 : Blo 455782 457159 := bstep (se 1 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 457159 = 685739) B685739
theorem B457179 : Blo 455782 457179 := bstep (se 1 (by rfl) ⟨342884, by rfl⟩ : syracuseStep 457179 = 685769) B685769
theorem B686555 : Blo 455782 686555 := bstep (se 1 (by rfl) ⟨514916, by rfl⟩ : syracuseStep 686555 = 1029833) B1029833
theorem B1309193 : Blo 455782 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B457255 : Blo 455782 457255 := bstep (se 1 (by rfl) ⟨342941, by rfl⟩ : syracuseStep 457255 = 685883) B685883
theorem B457295 : Blo 455782 457295 := bstep (se 1 (by rfl) ⟨342971, by rfl⟩ : syracuseStep 457295 = 685943) B685943
theorem B457311 : Blo 455782 457311 := bstep (se 1 (by rfl) ⟨342983, by rfl⟩ : syracuseStep 457311 = 685967) B685967
theorem B457339 : Blo 455782 457339 := bstep (se 1 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 457339 = 686009) B686009
theorem B457391 : Blo 455782 457391 := bstep (se 1 (by rfl) ⟨343043, by rfl⟩ : syracuseStep 457391 = 686087) B686087
theorem B457415 : Blo 455782 457415 := bstep (se 1 (by rfl) ⟨343061, by rfl⟩ : syracuseStep 457415 = 686123) B686123
theorem B457435 : Blo 455782 457435 := bstep (se 1 (by rfl) ⟨343076, by rfl⟩ : syracuseStep 457435 = 686153) B686153
theorem B457511 : Blo 455782 457511 := bstep (se 1 (by rfl) ⟨343133, by rfl⟩ : syracuseStep 457511 = 686267) B686267
theorem B457551 : Blo 455782 457551 := bstep (se 1 (by rfl) ⟨343163, by rfl⟩ : syracuseStep 457551 = 686327) B686327
theorem B457567 : Blo 455782 457567 := bstep (se 1 (by rfl) ⟨343175, by rfl⟩ : syracuseStep 457567 = 686351) B686351
theorem B1768301 : Blo 455782 1768301 := bstep (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) B663113
theorem B457595 : Blo 455782 457595 := bstep (se 1 (by rfl) ⟨343196, by rfl⟩ : syracuseStep 457595 = 686393) B686393
theorem B457647 : Blo 455782 457647 := bstep (se 1 (by rfl) ⟨343235, by rfl⟩ : syracuseStep 457647 = 686471) B686471
theorem B687023 : Blo 455782 687023 := bstep (se 1 (by rfl) ⟨515267, by rfl⟩ : syracuseStep 687023 = 1030535) B1030535
theorem B1538999 : Blo 455782 1538999 := bstep (se 1 (by rfl) ⟨1154249, by rfl⟩ : syracuseStep 1538999 = 2308499) B2308499
theorem B457671 : Blo 455782 457671 := bstep (se 1 (by rfl) ⟨343253, by rfl⟩ : syracuseStep 457671 = 686507) B686507
theorem B457691 : Blo 455782 457691 := bstep (se 1 (by rfl) ⟨343268, by rfl⟩ : syracuseStep 457691 = 686537) B686537
theorem B687113 : Blo 455782 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B457767 : Blo 455782 457767 := bstep (se 1 (by rfl) ⟨343325, by rfl⟩ : syracuseStep 457767 = 686651) B686651
theorem B687143 : Blo 455782 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B457807 : Blo 455782 457807 := bstep (se 1 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 457807 = 686711) B686711
theorem B457823 : Blo 455782 457823 := bstep (se 1 (by rfl) ⟨343367, by rfl⟩ : syracuseStep 457823 = 686735) B686735
theorem B457851 : Blo 455782 457851 := bstep (se 1 (by rfl) ⟨343388, by rfl⟩ : syracuseStep 457851 = 686777) B686777
theorem B687227 : Blo 455782 687227 := bstep (se 1 (by rfl) ⟨515420, by rfl⟩ : syracuseStep 687227 = 1030841) B1030841
theorem B457903 : Blo 455782 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B457927 : Blo 455782 457927 := bstep (se 1 (by rfl) ⟨343445, by rfl⟩ : syracuseStep 457927 = 686891) B686891
theorem B457947 : Blo 455782 457947 := bstep (se 1 (by rfl) ⟨343460, by rfl⟩ : syracuseStep 457947 = 686921) B686921
theorem B687353 : Blo 455782 687353 := bstep (se 2 (by rfl) ⟨257757, by rfl⟩ : syracuseStep 687353 = 515515) B515515
theorem B458023 : Blo 455782 458023 := bstep (se 1 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 458023 = 687035) B687035
theorem B458063 : Blo 455782 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B5209433 : Blo 455782 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B458079 : Blo 455782 458079 := bstep (se 1 (by rfl) ⟨343559, by rfl⟩ : syracuseStep 458079 = 687119) B687119
theorem B687455 : Blo 455782 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B687467 : Blo 455782 687467 := bstep (se 1 (by rfl) ⟨515600, by rfl⟩ : syracuseStep 687467 = 1031201) B1031201
theorem B458107 : Blo 455782 458107 := bstep (se 1 (by rfl) ⟨343580, by rfl⟩ : syracuseStep 458107 = 687161) B687161
theorem B458159 : Blo 455782 458159 := bstep (se 1 (by rfl) ⟨343619, by rfl⟩ : syracuseStep 458159 = 687239) B687239
theorem B458183 : Blo 455782 458183 := bstep (se 1 (by rfl) ⟨343637, by rfl⟩ : syracuseStep 458183 = 687275) B687275
theorem B458203 : Blo 455782 458203 := bstep (se 1 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 458203 = 687305) B687305
theorem B1539593 : Blo 455782 1539593 := bstep (se 2 (by rfl) ⟨577347, by rfl⟩ : syracuseStep 1539593 = 1154695) B1154695
theorem B884243 : Blo 455782 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B458279 : Blo 455782 458279 := bstep (se 1 (by rfl) ⟨343709, by rfl⟩ : syracuseStep 458279 = 687419) B687419
theorem B458319 : Blo 455782 458319 := bstep (se 1 (by rfl) ⟨343739, by rfl⟩ : syracuseStep 458319 = 687479) B687479
theorem B687695 : Blo 455782 687695 := bstep (se 1 (by rfl) ⟨515771, by rfl⟩ : syracuseStep 687695 = 1031543) B1031543
theorem B458335 : Blo 455782 458335 := bstep (se 1 (by rfl) ⟨343751, by rfl⟩ : syracuseStep 458335 = 687503) B687503
theorem B458363 : Blo 455782 458363 := bstep (se 1 (by rfl) ⟨343772, by rfl⟩ : syracuseStep 458363 = 687545) B687545
theorem B458415 : Blo 455782 458415 := bstep (se 1 (by rfl) ⟨343811, by rfl⟩ : syracuseStep 458415 = 687623) B687623
theorem B1900217 : Blo 455782 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B458439 : Blo 455782 458439 := bstep (se 1 (by rfl) ⟨343829, by rfl⟩ : syracuseStep 458439 = 687659) B687659
theorem B687815 : Blo 455782 687815 := bstep (se 1 (by rfl) ⟨515861, by rfl⟩ : syracuseStep 687815 = 1031723) B1031723
theorem B458459 : Blo 455782 458459 := bstep (se 1 (by rfl) ⟨343844, by rfl⟩ : syracuseStep 458459 = 687689) B687689
theorem B458535 : Blo 455782 458535 := bstep (se 1 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 458535 = 687803) B687803
theorem B1048393 : Blo 455782 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B458575 : Blo 455782 458575 := bstep (se 1 (by rfl) ⟨343931, by rfl⟩ : syracuseStep 458575 = 687863) B687863
theorem B458591 : Blo 455782 458591 := bstep (se 1 (by rfl) ⟨343943, by rfl⟩ : syracuseStep 458591 = 687887) B687887
theorem B687977 : Blo 455782 687977 := bstep (se 2 (by rfl) ⟨257991, by rfl⟩ : syracuseStep 687977 = 515983) B515983
theorem B458619 : Blo 455782 458619 := bstep (se 1 (by rfl) ⟨343964, by rfl⟩ : syracuseStep 458619 = 687929) B687929
theorem B458671 : Blo 455782 458671 := bstep (se 1 (by rfl) ⟨344003, by rfl⟩ : syracuseStep 458671 = 688007) B688007
theorem B688055 : Blo 455782 688055 := bstep (se 1 (by rfl) ⟨516041, by rfl⟩ : syracuseStep 688055 = 1032083) B1032083
theorem B458695 : Blo 455782 458695 := bstep (se 1 (by rfl) ⟨344021, by rfl⟩ : syracuseStep 458695 = 688043) B688043
theorem B458715 : Blo 455782 458715 := bstep (se 1 (by rfl) ⟨344036, by rfl⟩ : syracuseStep 458715 = 688073) B688073
theorem B688091 : Blo 455782 688091 := bstep (se 1 (by rfl) ⟨516068, by rfl⟩ : syracuseStep 688091 = 1032137) B1032137
theorem B459039 : Blo 455782 459039 := bstep (se 1 (by rfl) ⟨344279, by rfl⟩ : syracuseStep 459039 = 688559) B688559
theorem B688475 : Blo 455782 688475 := bstep (se 1 (by rfl) ⟨516356, by rfl⟩ : syracuseStep 688475 = 1032713) B1032713
theorem B459099 : Blo 455782 459099 := bstep (se 1 (by rfl) ⟨344324, by rfl⟩ : syracuseStep 459099 = 688649) B688649
theorem B459119 : Blo 455782 459119 := bstep (se 1 (by rfl) ⟨344339, by rfl⟩ : syracuseStep 459119 = 688679) B688679
theorem B459175 : Blo 455782 459175 := bstep (se 1 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 459175 = 688763) B688763
theorem B459259 : Blo 455782 459259 := bstep (se 1 (by rfl) ⟨344444, by rfl⟩ : syracuseStep 459259 = 688889) B688889
theorem B688703 : Blo 455782 688703 := bstep (se 1 (by rfl) ⟨516527, by rfl⟩ : syracuseStep 688703 = 1033055) B1033055
theorem B459327 : Blo 455782 459327 := bstep (se 1 (by rfl) ⟨344495, by rfl⟩ : syracuseStep 459327 = 688991) B688991
theorem B459335 : Blo 455782 459335 := bstep (se 1 (by rfl) ⟨344501, by rfl⟩ : syracuseStep 459335 = 689003) B689003
theorem B688823 : Blo 455782 688823 := bstep (se 1 (by rfl) ⟨516617, by rfl⟩ : syracuseStep 688823 = 1033235) B1033235
theorem B459487 : Blo 455782 459487 := bstep (se 1 (by rfl) ⟨344615, by rfl⟩ : syracuseStep 459487 = 689231) B689231
theorem B459567 : Blo 455782 459567 := bstep (se 1 (by rfl) ⟨344675, by rfl⟩ : syracuseStep 459567 = 689351) B689351
theorem B1540943 : Blo 455782 1540943 := bstep (se 1 (by rfl) ⟨1155707, by rfl⟩ : syracuseStep 1540943 = 2311415) B2311415
theorem B689051 : Blo 455782 689051 := bstep (se 1 (by rfl) ⟨516788, by rfl⟩ : syracuseStep 689051 = 1033577) B1033577
theorem B459675 : Blo 455782 459675 := bstep (se 1 (by rfl) ⟨344756, by rfl⟩ : syracuseStep 459675 = 689513) B689513
theorem B459727 : Blo 455782 459727 := bstep (se 1 (by rfl) ⟨344795, by rfl⟩ : syracuseStep 459727 = 689591) B689591
theorem B459751 : Blo 455782 459751 := bstep (se 1 (by rfl) ⟨344813, by rfl⟩ : syracuseStep 459751 = 689627) B689627
theorem B1541267 : Blo 455782 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B1737875 : Blo 455782 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B689447 : Blo 455782 689447 := bstep (se 1 (by rfl) ⟨517085, by rfl⟩ : syracuseStep 689447 = 1034171) B1034171
theorem B689531 : Blo 455782 689531 := bstep (se 1 (by rfl) ⟨517148, by rfl⟩ : syracuseStep 689531 = 1034297) B1034297
theorem B1541537 : Blo 455782 1541537 := bstep (se 2 (by rfl) ⟨578076, by rfl⟩ : syracuseStep 1541537 = 1156153) B1156153
theorem B689657 : Blo 455782 689657 := bstep (se 2 (by rfl) ⟨258621, by rfl⟩ : syracuseStep 689657 = 517243) B517243
theorem B1115731 : Blo 455782 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B821353 : Blo 455782 821353 := bstep (se 2 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 821353 = 616015) B616015
theorem B6588701 : Blo 455782 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B1116919 : Blo 455782 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B5868611 : Blo 455782 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B3903659 : Blo 455782 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B463195 : Blo 455782 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B1544723 : Blo 455782 1544723 := bstep (se 1 (by rfl) ⟨1158542, by rfl⟩ : syracuseStep 1544723 = 2317085) B2317085
theorem B2200115 : Blo 455782 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B4756333 : Blo 455782 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1741763 : Blo 455782 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B13407437 : Blo 455782 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B9934073 : Blo 455782 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1742219 : Blo 455782 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B53450189 : Blo 455782 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B694057 : Blo 455782 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B1546505 : Blo 455782 1546505 := bstep (se 2 (by rfl) ⟨579939, by rfl⟩ : syracuseStep 1546505 = 1159879) B1159879
theorem B9410903 : Blo 455782 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B2234735 : Blo 455782 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B825851 : Blo 455782 825851 := bstep (se 1 (by rfl) ⟨619388, by rfl⟩ : syracuseStep 825851 = 1238777) B1238777
theorem B3349055 : Blo 455782 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B2202191 : Blo 455782 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B2464667 : Blo 455782 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B1547639 : Blo 455782 1547639 := bstep (se 1 (by rfl) ⟨1160729, by rfl⟩ : syracuseStep 1547639 = 2321459) B2321459
theorem B2793041 : Blo 455782 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B1154857 : Blo 455782 1154857 := bstep (se 2 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 1154857 = 866143) B866143
theorem B1646801 : Blo 455782 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B1548719 : Blo 455782 1548719 := bstep (se 1 (by rfl) ⟨1161539, by rfl⟩ : syracuseStep 1548719 = 2323079) B2323079
theorem B1155647 : Blo 455782 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B926383 : Blo 455782 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B697055 : Blo 455782 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B3908411 : Blo 455782 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B2204729 : Blo 455782 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B1156295 : Blo 455782 1156295 := bstep (se 1 (by rfl) ⟨867221, by rfl⟩ : syracuseStep 1156295 = 1734443) B1734443
theorem B1156315 : Blo 455782 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B730399 : Blo 455782 730399 := bstep (se 1 (by rfl) ⟨547799, by rfl⟩ : syracuseStep 730399 = 1095599) B1095599
theorem B3351851 : Blo 455782 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B1549691 : Blo 455782 1549691 := bstep (se 1 (by rfl) ⟨1162268, by rfl⟩ : syracuseStep 1549691 = 2324537) B2324537
theorem B1025999 : Blo 455782 1025999 := bstep (se 1 (by rfl) ⟨769499, by rfl⟩ : syracuseStep 1025999 = 1538999) B1538999
theorem B1026377 : Blo 455782 1026377 := bstep (se 2 (by rfl) ⟨384891, by rfl⟩ : syracuseStep 1026377 = 769783) B769783
theorem B1157449 : Blo 455782 1157449 := bstep (se 2 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 1157449 = 868087) B868087
theorem B1026395 : Blo 455782 1026395 := bstep (se 1 (by rfl) ⟨769796, by rfl⟩ : syracuseStep 1026395 = 1539593) B1539593
theorem B3484133 : Blo 455782 3484133 := bstep (se 4 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 3484133 = 653275) B653275
theorem B1157753 : Blo 455782 1157753 := bstep (se 2 (by rfl) ⟨434157, by rfl⟩ : syracuseStep 1157753 = 868315) B868315
theorem B1551095 : Blo 455782 1551095 := bstep (se 1 (by rfl) ⟨1163321, by rfl⟩ : syracuseStep 1551095 = 2326643) B2326643
theorem B1026971 : Blo 455782 1026971 := bstep (se 1 (by rfl) ⟨770228, by rfl⟩ : syracuseStep 1026971 = 1540457) B1540457
theorem B1027169 : Blo 455782 1027169 := bstep (se 2 (by rfl) ⟨385188, by rfl⟩ : syracuseStep 1027169 = 770377) B770377
theorem B5024987 : Blo 455782 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B1027367 : Blo 455782 1027367 := bstep (se 1 (by rfl) ⟨770525, by rfl⟩ : syracuseStep 1027367 = 1541051) B1541051
theorem B16035191 : Blo 455782 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B732539 : Blo 455782 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B1027745 : Blo 455782 1027745 := bstep (se 2 (by rfl) ⟨385404, by rfl⟩ : syracuseStep 1027745 = 770809) B770809
theorem B1028105 : Blo 455782 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B2208073 : Blo 455782 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B1159535 : Blo 455782 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B1028519 : Blo 455782 1028519 := bstep (se 1 (by rfl) ⟨771389, by rfl⟩ : syracuseStep 1028519 = 1542779) B1542779
theorem B1028627 : Blo 455782 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B1028681 : Blo 455782 1028681 := bstep (se 2 (by rfl) ⟨385755, by rfl⟩ : syracuseStep 1028681 = 771511) B771511
theorem B1029095 : Blo 455782 1029095 := bstep (se 1 (by rfl) ⟨771821, by rfl⟩ : syracuseStep 1029095 = 1543643) B1543643
theorem B40121335 : Blo 455782 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B1160183 : Blo 455782 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B17839223 : Blo 455782 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B1160315 : Blo 455782 1160315 := bstep (se 1 (by rfl) ⟨870236, by rfl⟩ : syracuseStep 1160315 = 1740473) B1740473
theorem B1029473 : Blo 455782 1029473 := bstep (se 2 (by rfl) ⟨386052, by rfl⟩ : syracuseStep 1029473 = 772105) B772105
theorem B2045345 : Blo 455782 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B1029563 : Blo 455782 1029563 := bstep (se 1 (by rfl) ⟨772172, by rfl⟩ : syracuseStep 1029563 = 1544345) B1544345
theorem B1029689 : Blo 455782 1029689 := bstep (se 2 (by rfl) ⟨386133, by rfl⟩ : syracuseStep 1029689 = 772267) B772267
theorem B1095329 : Blo 455782 1095329 := bstep (se 2 (by rfl) ⟨410748, by rfl⟩ : syracuseStep 1095329 = 821497) B821497
theorem B2308175 : Blo 455782 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B1947833 : Blo 455782 1947833 := bstep (se 2 (by rfl) ⟨730437, by rfl⟩ : syracuseStep 1947833 = 1460875) B1460875
theorem B1030355 : Blo 455782 1030355 := bstep (se 1 (by rfl) ⟨772766, by rfl⟩ : syracuseStep 1030355 = 1545533) B1545533
theorem B1030409 : Blo 455782 1030409 := bstep (se 2 (by rfl) ⟨386403, by rfl⟩ : syracuseStep 1030409 = 772807) B772807
theorem B1030625 : Blo 455782 1030625 := bstep (se 2 (by rfl) ⟨386484, by rfl⟩ : syracuseStep 1030625 = 772969) B772969
theorem B1030931 : Blo 455782 1030931 := bstep (se 1 (by rfl) ⟨773198, by rfl⟩ : syracuseStep 1030931 = 1546397) B1546397
theorem B1162127 : Blo 455782 1162127 := bstep (se 1 (by rfl) ⟨871595, by rfl⟩ : syracuseStep 1162127 = 1743191) B1743191
theorem B1031291 : Blo 455782 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B2309309 : Blo 455782 2309309 := bstep (se 3 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 2309309 = 865991) B865991
theorem B1653949 : Blo 455782 1653949 := bstep (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) B620231
theorem B769243 : Blo 455782 769243 := bstep (se 1 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 769243 = 1153865) B1153865
theorem B1031417 : Blo 455782 1031417 := bstep (se 2 (by rfl) ⟨386781, by rfl⟩ : syracuseStep 1031417 = 773563) B773563
theorem B1031561 : Blo 455782 1031561 := bstep (se 2 (by rfl) ⟨386835, by rfl⟩ : syracuseStep 1031561 = 773671) B773671
theorem B1162633 : Blo 455782 1162633 := bstep (se 2 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 1162633 = 871975) B871975
theorem B1162745 : Blo 455782 1162745 := bstep (se 2 (by rfl) ⟨436029, by rfl⟩ : syracuseStep 1162745 = 872059) B872059
theorem B1031687 : Blo 455782 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B2473487 : Blo 455782 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B867935 : Blo 455782 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B1031867 : Blo 455782 1031867 := bstep (se 1 (by rfl) ⟨773900, by rfl⟩ : syracuseStep 1031867 = 1547801) B1547801
theorem B1031993 : Blo 455782 1031993 := bstep (se 2 (by rfl) ⟨386997, by rfl⟩ : syracuseStep 1031993 = 773995) B773995
theorem B4931401 : Blo 455782 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B769999 : Blo 455782 769999 := bstep (se 1 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 769999 = 1154999) B1154999
theorem B1163393 : Blo 455782 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B4931927 : Blo 455782 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B1032623 : Blo 455782 1032623 := bstep (se 1 (by rfl) ⟨774467, by rfl⟩ : syracuseStep 1032623 = 1548935) B1548935
theorem B1032659 : Blo 455782 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B1032767 : Blo 455782 1032767 := bstep (se 1 (by rfl) ⟨774575, by rfl⟩ : syracuseStep 1032767 = 1549151) B1549151
theorem B1098319 : Blo 455782 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B770681 : Blo 455782 770681 := bstep (se 2 (by rfl) ⟨289005, by rfl⟩ : syracuseStep 770681 = 578011) B578011
theorem B3490451 : Blo 455782 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B1032875 : Blo 455782 1032875 := bstep (se 1 (by rfl) ⟨774656, by rfl⟩ : syracuseStep 1032875 = 1549313) B1549313
theorem B770735 : Blo 455782 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B6243065 : Blo 455782 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B475951 : Blo 455782 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B770971 : Blo 455782 770971 := bstep (se 1 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 770971 = 1156457) B1156457
theorem B1033415 : Blo 455782 1033415 := bstep (se 1 (by rfl) ⟨775061, by rfl⟩ : syracuseStep 1033415 = 1550123) B1550123
theorem B2082041 : Blo 455782 2082041 := bstep (se 2 (by rfl) ⟨780765, by rfl⟩ : syracuseStep 2082041 = 1561531) B1561531
theorem B2639147 : Blo 455782 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B1033595 : Blo 455782 1033595 := bstep (se 1 (by rfl) ⟨775196, by rfl⟩ : syracuseStep 1033595 = 1550393) B1550393
theorem B1033721 : Blo 455782 1033721 := bstep (se 2 (by rfl) ⟨387645, by rfl⟩ : syracuseStep 1033721 = 775291) B775291
theorem B1033811 : Blo 455782 1033811 := bstep (se 1 (by rfl) ⟨775358, by rfl⟩ : syracuseStep 1033811 = 1550717) B1550717
theorem B2934407 : Blo 455782 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B1033991 : Blo 455782 1033991 := bstep (se 1 (by rfl) ⟨775493, by rfl⟩ : syracuseStep 1033991 = 1550987) B1550987
theorem B8800067 : Blo 455782 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B4179845 : Blo 455782 4179845 := bstep (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) B783721
theorem B2312225 : Blo 455782 2312225 := bstep (se 2 (by rfl) ⟨867084, by rfl⟩ : syracuseStep 2312225 = 1734169) B1734169
theorem B5949521 : Blo 455782 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B2312387 : Blo 455782 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B9423053 : Blo 455782 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B772463 : Blo 455782 772463 := bstep (se 1 (by rfl) ⟨579347, by rfl⟩ : syracuseStep 772463 = 1158695) B1158695
theorem B772679 : Blo 455782 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B1100395 : Blo 455782 1100395 := bstep (se 1 (by rfl) ⟨825296, by rfl⟩ : syracuseStep 1100395 = 1650593) B1650593
theorem B871087 : Blo 455782 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B1100471 : Blo 455782 1100471 := bstep (se 1 (by rfl) ⟨825353, by rfl⟩ : syracuseStep 1100471 = 1650707) B1650707
theorem B3918557 : Blo 455782 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B8440625 : Blo 455782 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B2607997 : Blo 455782 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B1854451 : Blo 455782 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B773111 : Blo 455782 773111 := bstep (se 1 (by rfl) ⟨579833, by rfl⟩ : syracuseStep 773111 = 1159667) B1159667
theorem B1756631 : Blo 455782 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B773867 : Blo 455782 773867 := bstep (se 1 (by rfl) ⟨580400, by rfl⟩ : syracuseStep 773867 = 1160801) B1160801
theorem B5263147 : Blo 455782 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B1953811 : Blo 455782 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B3461291 : Blo 455782 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B125751523 : Blo 455782 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B872795 : Blo 455782 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B5591429 : Blo 455782 5591429 := bstep (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) B1048393
theorem B5067245 : Blo 455782 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B774839 : Blo 455782 774839 := bstep (se 1 (by rfl) ⟨581129, by rfl⟩ : syracuseStep 774839 = 1162259) B1162259
theorem B5231303 : Blo 455782 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B512815 : Blo 455782 512815 := bstep (se 1 (by rfl) ⟨384611, by rfl⟩ : syracuseStep 512815 = 769223) B769223
theorem B512923 : Blo 455782 512923 := bstep (se 1 (by rfl) ⟨384692, by rfl⟩ : syracuseStep 512923 = 769385) B769385
theorem B1299671 : Blo 455782 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B513319 : Blo 455782 513319 := bstep (se 1 (by rfl) ⟨384989, by rfl⟩ : syracuseStep 513319 = 769979) B769979
theorem B513391 : Blo 455782 513391 := bstep (se 1 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 513391 = 770087) B770087
theorem B578927 : Blo 455782 578927 := bstep (se 1 (by rfl) ⟨434195, by rfl⟩ : syracuseStep 578927 = 868391) B868391
theorem B775561 : Blo 455782 775561 := bstep (se 2 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 775561 = 581671) B581671
theorem B2971019 : Blo 455782 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B578983 : Blo 455782 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B513607 : Blo 455782 513607 := bstep (se 1 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 513607 = 770411) B770411
theorem B579307 : Blo 455782 579307 := bstep (se 1 (by rfl) ⟨434480, by rfl⟩ : syracuseStep 579307 = 868961) B868961
theorem B2316113 : Blo 455782 2316113 := bstep (se 2 (by rfl) ⟨868542, by rfl⟩ : syracuseStep 2316113 = 1737085) B1737085
theorem B514471 : Blo 455782 514471 := bstep (se 1 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 514471 = 771707) B771707
theorem B940607 : Blo 455782 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B2316923 : Blo 455782 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B580279 : Blo 455782 580279 := bstep (se 1 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 580279 = 870419) B870419
theorem B3300115 : Blo 455782 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B973711 : Blo 455782 973711 := bstep (se 1 (by rfl) ⟨730283, by rfl⟩ : syracuseStep 973711 = 1460567) B1460567
theorem B3955643 : Blo 455782 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B515047 : Blo 455782 515047 := bstep (se 1 (by rfl) ⟨386285, by rfl⟩ : syracuseStep 515047 = 772571) B772571
theorem B3922931 : Blo 455782 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B3300517 : Blo 455782 3300517 := bstep (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) B618847
theorem B4382201 : Blo 455782 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B7855703 : Blo 455782 7855703 := bstep (se 1 (by rfl) ⟨5891777, by rfl⟩ : syracuseStep 7855703 = 11783555) B11783555
theorem B2612897 : Blo 455782 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B548587 : Blo 455782 548587 := bstep (se 1 (by rfl) ⟨411440, by rfl⟩ : syracuseStep 548587 = 822881) B822881
theorem B1302313 : Blo 455782 1302313 := bstep (se 2 (by rfl) ⟨488367, by rfl⟩ : syracuseStep 1302313 = 976735) B976735
theorem B5889833 : Blo 455782 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B2940947 : Blo 455782 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B2253059 : Blo 455782 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B4710707 : Blo 455782 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B975215 : Blo 455782 975215 := bstep (se 1 (by rfl) ⟨731411, by rfl⟩ : syracuseStep 975215 = 1462823) B1462823
theorem B3727873 : Blo 455782 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B2318867 : Blo 455782 2318867 := bstep (se 1 (by rfl) ⟨1739150, by rfl⟩ : syracuseStep 2318867 = 3478301) B3478301
theorem B516703 : Blo 455782 516703 := bstep (se 1 (by rfl) ⟨387527, by rfl⟩ : syracuseStep 516703 = 775055) B775055
theorem B3302363 : Blo 455782 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B975847 : Blo 455782 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B1303543 : Blo 455782 1303543 := bstep (se 1 (by rfl) ⟨977657, by rfl⟩ : syracuseStep 1303543 = 1955315) B1955315
theorem B31745125 : Blo 455782 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1303931 : Blo 455782 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B2483693 : Blo 455782 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B550471 : Blo 455782 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B3925907 : Blo 455782 3925907 := bstep (se 1 (by rfl) ⟨2944430, by rfl⟩ : syracuseStep 3925907 = 5888861) B5888861
theorem B2222113 : Blo 455782 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B2320649 : Blo 455782 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B2615561 : Blo 455782 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B2779559 : Blo 455782 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B2943611 : Blo 455782 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B568519397 : Blo 455782 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B650063 : Blo 455782 650063 := bstep (se 1 (by rfl) ⟨487547, by rfl⟩ : syracuseStep 650063 = 975095) B975095
theorem B2190235 : Blo 455782 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B2321783 : Blo 455782 2321783 := bstep (se 1 (by rfl) ⟨1741337, by rfl⟩ : syracuseStep 2321783 = 3482675) B3482675
theorem B585083 : Blo 455782 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B2321945 : Blo 455782 2321945 := bstep (se 2 (by rfl) ⟨870729, by rfl⟩ : syracuseStep 2321945 = 1741459) B1741459
theorem B1732211 : Blo 455782 1732211 := bstep (se 1 (by rfl) ⟨1299158, by rfl⟩ : syracuseStep 1732211 = 2598317) B2598317
theorem B585451 : Blo 455782 585451 := bstep (se 1 (by rfl) ⟨439088, by rfl⟩ : syracuseStep 585451 = 878177) B878177
theorem B3469067 : Blo 455782 3469067 := bstep (se 1 (by rfl) ⟨2601800, by rfl⟩ : syracuseStep 3469067 = 5203601) B5203601
theorem B683831 : Blo 455782 683831 := bstep (se 1 (by rfl) ⟨512873, by rfl⟩ : syracuseStep 683831 = 1025747) B1025747
theorem B978743 : Blo 455782 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B6615107 : Blo 455782 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B2191465 : Blo 455782 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B684137 : Blo 455782 684137 := bstep (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) B513103
theorem B2650283 : Blo 455782 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B9892043 : Blo 455782 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B684455 : Blo 455782 684455 := bstep (se 1 (by rfl) ⟨513341, by rfl⟩ : syracuseStep 684455 = 1026683) B1026683
theorem B684539 : Blo 455782 684539 := bstep (se 1 (by rfl) ⟨513404, by rfl⟩ : syracuseStep 684539 = 1026809) B1026809
theorem B684665 : Blo 455782 684665 := bstep (se 2 (by rfl) ⟨256749, by rfl⟩ : syracuseStep 684665 = 513499) B513499
theorem B684719 : Blo 455782 684719 := bstep (se 1 (by rfl) ⟨513539, by rfl⟩ : syracuseStep 684719 = 1027079) B1027079
theorem B488111 : Blo 455782 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B1176239 : Blo 455782 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B684767 : Blo 455782 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B5862253 : Blo 455782 5862253 := bstep (se 3 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 5862253 = 2198345) B2198345
theorem B6615917 : Blo 455782 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B1176475 : Blo 455782 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B979931 : Blo 455782 979931 := bstep (se 1 (by rfl) ⟨734948, by rfl⟩ : syracuseStep 979931 = 1469897) B1469897
theorem B685031 : Blo 455782 685031 := bstep (se 1 (by rfl) ⟨513773, by rfl⟩ : syracuseStep 685031 = 1027547) B1027547
theorem B685289 : Blo 455782 685289 := bstep (se 2 (by rfl) ⟨256983, by rfl⟩ : syracuseStep 685289 = 513967) B513967
theorem B455967 : Blo 455782 455967 := bstep (se 1 (by rfl) ⟨341975, by rfl⟩ : syracuseStep 455967 = 683951) B683951
theorem B685343 : Blo 455782 685343 := bstep (se 1 (by rfl) ⟨514007, by rfl⟩ : syracuseStep 685343 = 1028015) B1028015
theorem B980255 : Blo 455782 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B456027 : Blo 455782 456027 := bstep (se 1 (by rfl) ⟨342020, by rfl⟩ : syracuseStep 456027 = 684041) B684041
theorem B456047 : Blo 455782 456047 := bstep (se 1 (by rfl) ⟨342035, by rfl⟩ : syracuseStep 456047 = 684071) B684071
theorem B456103 : Blo 455782 456103 := bstep (se 1 (by rfl) ⟨342077, by rfl⟩ : syracuseStep 456103 = 684155) B684155
theorem B685511 : Blo 455782 685511 := bstep (se 1 (by rfl) ⟨514133, by rfl⟩ : syracuseStep 685511 = 1028267) B1028267
theorem B456187 : Blo 455782 456187 := bstep (se 1 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 456187 = 684281) B684281
theorem B456255 : Blo 455782 456255 := bstep (se 1 (by rfl) ⟨342191, by rfl⟩ : syracuseStep 456255 = 684383) B684383
theorem B456263 : Blo 455782 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B456415 : Blo 455782 456415 := bstep (se 1 (by rfl) ⟨342311, by rfl⟩ : syracuseStep 456415 = 684623) B684623
theorem B685865 : Blo 455782 685865 := bstep (se 2 (by rfl) ⟨257199, by rfl⟩ : syracuseStep 685865 = 514399) B514399
theorem B456495 : Blo 455782 456495 := bstep (se 1 (by rfl) ⟨342371, by rfl⟩ : syracuseStep 456495 = 684743) B684743
theorem B685871 : Blo 455782 685871 := bstep (se 1 (by rfl) ⟨514403, by rfl⟩ : syracuseStep 685871 = 1028807) B1028807
theorem B456603 : Blo 455782 456603 := bstep (se 1 (by rfl) ⟨342452, by rfl⟩ : syracuseStep 456603 = 684905) B684905
theorem B456655 : Blo 455782 456655 := bstep (se 1 (by rfl) ⟨342491, by rfl⟩ : syracuseStep 456655 = 684983) B684983
theorem B456679 : Blo 455782 456679 := bstep (se 1 (by rfl) ⟨342509, by rfl⟩ : syracuseStep 456679 = 685019) B685019
theorem B8353853 : Blo 455782 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B686345 : Blo 455782 686345 := bstep (se 2 (by rfl) ⟨257379, by rfl⟩ : syracuseStep 686345 = 514759) B514759
theorem B456991 : Blo 455782 456991 := bstep (se 1 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 456991 = 685487) B685487
theorem B457051 : Blo 455782 457051 := bstep (se 1 (by rfl) ⟨342788, by rfl⟩ : syracuseStep 457051 = 685577) B685577
theorem B457071 : Blo 455782 457071 := bstep (se 1 (by rfl) ⟨342803, by rfl⟩ : syracuseStep 457071 = 685607) B685607
theorem B686447 : Blo 455782 686447 := bstep (se 1 (by rfl) ⟨514835, by rfl⟩ : syracuseStep 686447 = 1029671) B1029671
theorem B2324861 : Blo 455782 2324861 := bstep (se 3 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 2324861 = 871823) B871823
theorem B457127 : Blo 455782 457127 := bstep (se 1 (by rfl) ⟨342845, by rfl⟩ : syracuseStep 457127 = 685691) B685691
theorem B621049 : Blo 455782 621049 := bstep (se 2 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 621049 = 465787) B465787
theorem B457211 : Blo 455782 457211 := bstep (se 1 (by rfl) ⟨342908, by rfl⟩ : syracuseStep 457211 = 685817) B685817
theorem B457279 : Blo 455782 457279 := bstep (se 1 (by rfl) ⟨342959, by rfl⟩ : syracuseStep 457279 = 685919) B685919
theorem B457287 : Blo 455782 457287 := bstep (se 1 (by rfl) ⟨342965, by rfl⟩ : syracuseStep 457287 = 685931) B685931
theorem B686663 : Blo 455782 686663 := bstep (se 1 (by rfl) ⟨514997, by rfl⟩ : syracuseStep 686663 = 1029995) B1029995
theorem B490055 : Blo 455782 490055 := bstep (se 1 (by rfl) ⟨367541, by rfl⟩ : syracuseStep 490055 = 735083) B735083
theorem B686699 : Blo 455782 686699 := bstep (se 1 (by rfl) ⟨515024, by rfl⟩ : syracuseStep 686699 = 1030049) B1030049
theorem B2357981 : Blo 455782 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B457439 : Blo 455782 457439 := bstep (se 1 (by rfl) ⟨343079, by rfl⟩ : syracuseStep 457439 = 686159) B686159
theorem B1735415 : Blo 455782 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B457519 : Blo 455782 457519 := bstep (se 1 (by rfl) ⟨343139, by rfl⟩ : syracuseStep 457519 = 686279) B686279
theorem B686927 : Blo 455782 686927 := bstep (se 1 (by rfl) ⟨515195, by rfl⟩ : syracuseStep 686927 = 1030391) B1030391
theorem B457627 : Blo 455782 457627 := bstep (se 1 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 457627 = 686441) B686441
theorem B457679 : Blo 455782 457679 := bstep (se 1 (by rfl) ⟨343259, by rfl⟩ : syracuseStep 457679 = 686519) B686519
theorem B457703 : Blo 455782 457703 := bstep (se 1 (by rfl) ⟨343277, by rfl⟩ : syracuseStep 457703 = 686555) B686555
theorem B7044259 : Blo 455782 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B687323 : Blo 455782 687323 := bstep (se 1 (by rfl) ⟨515492, by rfl⟩ : syracuseStep 687323 = 1030985) B1030985
theorem B1178867 : Blo 455782 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B458015 : Blo 455782 458015 := bstep (se 1 (by rfl) ⟨343511, by rfl⟩ : syracuseStep 458015 = 687023) B687023
theorem B458075 : Blo 455782 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B458095 : Blo 455782 458095 := bstep (se 1 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 458095 = 687143) B687143
theorem B687497 : Blo 455782 687497 := bstep (se 2 (by rfl) ⟨257811, by rfl⟩ : syracuseStep 687497 = 515623) B515623
theorem B458151 : Blo 455782 458151 := bstep (se 1 (by rfl) ⟨343613, by rfl⟩ : syracuseStep 458151 = 687227) B687227
theorem B458235 : Blo 455782 458235 := bstep (se 1 (by rfl) ⟨343676, by rfl⟩ : syracuseStep 458235 = 687353) B687353
theorem B3472955 : Blo 455782 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B458303 : Blo 455782 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B458311 : Blo 455782 458311 := bstep (se 1 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 458311 = 687467) B687467
theorem B458463 : Blo 455782 458463 := bstep (se 1 (by rfl) ⟨343847, by rfl⟩ : syracuseStep 458463 = 687695) B687695
theorem B687851 : Blo 455782 687851 := bstep (se 1 (by rfl) ⟨515888, by rfl⟩ : syracuseStep 687851 = 1031777) B1031777
theorem B458543 : Blo 455782 458543 := bstep (se 1 (by rfl) ⟨343907, by rfl⟩ : syracuseStep 458543 = 687815) B687815
theorem B2326319 : Blo 455782 2326319 := bstep (se 1 (by rfl) ⟨1744739, by rfl⟩ : syracuseStep 2326319 = 3489479) B3489479
theorem B458651 : Blo 455782 458651 := bstep (se 1 (by rfl) ⟨343988, by rfl⟩ : syracuseStep 458651 = 687977) B687977
theorem B458703 : Blo 455782 458703 := bstep (se 1 (by rfl) ⟨344027, by rfl⟩ : syracuseStep 458703 = 688055) B688055
theorem B688079 : Blo 455782 688079 := bstep (se 1 (by rfl) ⟨516059, by rfl⟩ : syracuseStep 688079 = 1032119) B1032119
theorem B458727 : Blo 455782 458727 := bstep (se 1 (by rfl) ⟨344045, by rfl⟩ : syracuseStep 458727 = 688091) B688091
theorem B458983 : Blo 455782 458983 := bstep (se 1 (by rfl) ⟨344237, by rfl⟩ : syracuseStep 458983 = 688475) B688475
theorem B688415 : Blo 455782 688415 := bstep (se 1 (by rfl) ⟨516311, by rfl⟩ : syracuseStep 688415 = 1032623) B1032623
theorem B688439 : Blo 455782 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B688511 : Blo 455782 688511 := bstep (se 1 (by rfl) ⟨516383, by rfl⟩ : syracuseStep 688511 = 1032767) B1032767
theorem B459135 : Blo 455782 459135 := bstep (se 1 (by rfl) ⟨344351, by rfl⟩ : syracuseStep 459135 = 688703) B688703
theorem B2326967 : Blo 455782 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B688583 : Blo 455782 688583 := bstep (se 1 (by rfl) ⟨516437, by rfl⟩ : syracuseStep 688583 = 1032875) B1032875
theorem B459215 : Blo 455782 459215 := bstep (se 1 (by rfl) ⟨344411, by rfl⟩ : syracuseStep 459215 = 688823) B688823
theorem B4162043 : Blo 455782 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B459367 : Blo 455782 459367 := bstep (se 1 (by rfl) ⟨344525, by rfl⟩ : syracuseStep 459367 = 689051) B689051
theorem B688937 : Blo 455782 688937 := bstep (se 2 (by rfl) ⟨258351, by rfl⟩ : syracuseStep 688937 = 516703) B516703
theorem B688943 : Blo 455782 688943 := bstep (se 1 (by rfl) ⟨516707, by rfl⟩ : syracuseStep 688943 = 1033415) B1033415
theorem B459631 : Blo 455782 459631 := bstep (se 1 (by rfl) ⟨344723, by rfl⟩ : syracuseStep 459631 = 689447) B689447
theorem B2327453 : Blo 455782 2327453 := bstep (se 3 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 2327453 = 872795) B872795
theorem B689063 : Blo 455782 689063 := bstep (se 1 (by rfl) ⟨516797, by rfl⟩ : syracuseStep 689063 = 1033595) B1033595
theorem B459687 : Blo 455782 459687 := bstep (se 1 (by rfl) ⟨344765, by rfl⟩ : syracuseStep 459687 = 689531) B689531
theorem B689147 : Blo 455782 689147 := bstep (se 1 (by rfl) ⟨516860, by rfl⟩ : syracuseStep 689147 = 1033721) B1033721
theorem B459771 : Blo 455782 459771 := bstep (se 1 (by rfl) ⟨344828, by rfl⟩ : syracuseStep 459771 = 689657) B689657
theorem B689207 : Blo 455782 689207 := bstep (se 1 (by rfl) ⟨516905, by rfl⟩ : syracuseStep 689207 = 1033811) B1033811
theorem B689327 : Blo 455782 689327 := bstep (se 1 (by rfl) ⟨516995, by rfl⟩ : syracuseStep 689327 = 1033991) B1033991
theorem B5866711 : Blo 455782 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B2786563 : Blo 455782 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B1738057 : Blo 455782 1738057 := bstep (se 2 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 1738057 = 1303543) B1303543
theorem B1541483 : Blo 455782 1541483 := bstep (se 1 (by rfl) ⟨1156112, by rfl⟩ : syracuseStep 1541483 = 2312225) B2312225
theorem B3966347 : Blo 455782 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B1541591 : Blo 455782 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B4392467 : Blo 455782 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B1541753 : Blo 455782 1541753 := bstep (se 2 (by rfl) ⟨578157, by rfl⟩ : syracuseStep 1541753 = 1156315) B1156315
theorem B1543265 : Blo 455782 1543265 := bstep (se 2 (by rfl) ⟨578724, by rfl⟩ : syracuseStep 1543265 = 1157449) B1157449
theorem B6622715 : Blo 455782 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B1543805 : Blo 455782 1543805 := bstep (se 3 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 1543805 = 578927) B578927
theorem B3477329 : Blo 455782 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B2920313 : Blo 455782 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B1544075 : Blo 455782 1544075 := bstep (se 1 (by rfl) ⟨1158056, by rfl⟩ : syracuseStep 1544075 = 2316113) B2316113
theorem B627071 : Blo 455782 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B2232703 : Blo 455782 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B1544615 : Blo 455782 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B1643111 : Blo 455782 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B2921467 : Blo 455782 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B7017529 : Blo 455782 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B1741931 : Blo 455782 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B2921953 : Blo 455782 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B1545911 : Blo 455782 1545911 := bstep (se 1 (by rfl) ⟨1159433, by rfl⟩ : syracuseStep 1545911 = 2318867) B2318867
theorem B2201575 : Blo 455782 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B2234567 : Blo 455782 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B8821061 : Blo 455782 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B1547099 : Blo 455782 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1743707 : Blo 455782 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B3349991 : Blo 455782 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1547855 : Blo 455782 1547855 := bstep (se 1 (by rfl) ⟨1160891, by rfl⟩ : syracuseStep 1547855 = 2321783) B2321783
theorem B10690127 : Blo 455782 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B1547963 : Blo 455782 1547963 := bstep (se 1 (by rfl) ⟨1160972, by rfl⟩ : syracuseStep 1547963 = 2321945) B2321945
theorem B925409 : Blo 455782 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B1154807 : Blo 455782 1154807 := bstep (se 1 (by rfl) ⟨866105, by rfl⟩ : syracuseStep 1154807 = 1732211) B1732211
theorem B6594695 : Blo 455782 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B828065 : Blo 455782 828065 := bstep (se 2 (by rfl) ⟨310524, by rfl⟩ : syracuseStep 828065 = 621049) B621049
theorem B4400153 : Blo 455782 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B730219 : Blo 455782 730219 := bstep (se 1 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 730219 = 1095329) B1095329
theorem B3122405 : Blo 455782 3122405 := bstep (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) B585451
theorem B4400689 : Blo 455782 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B1549907 : Blo 455782 1549907 := bstep (se 1 (by rfl) ⟨1162430, by rfl⟩ : syracuseStep 1549907 = 2324861) B2324861
theorem B1025657 : Blo 455782 1025657 := bstep (se 2 (by rfl) ⟨384621, by rfl⟩ : syracuseStep 1025657 = 769243) B769243
theorem B1156943 : Blo 455782 1156943 := bstep (se 1 (by rfl) ⟨867707, by rfl⟩ : syracuseStep 1156943 = 1735415) B1735415
theorem B1550177 : Blo 455782 1550177 := bstep (se 2 (by rfl) ⟨581316, by rfl⟩ : syracuseStep 1550177 = 1162633) B1162633
theorem B731449 : Blo 455782 731449 := bstep (se 2 (by rfl) ⟨274293, by rfl⟩ : syracuseStep 731449 = 548587) B548587
theorem B1648991 : Blo 455782 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B1550879 : Blo 455782 1550879 := bstep (se 1 (by rfl) ⟨1163159, by rfl⟩ : syracuseStep 1550879 = 2326319) B2326319
theorem B1026665 : Blo 455782 1026665 := bstep (se 2 (by rfl) ⟨384999, by rfl⟩ : syracuseStep 1026665 = 769999) B769999
theorem B3287951 : Blo 455782 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B1027295 : Blo 455782 1027295 := bstep (se 1 (by rfl) ⟨770471, by rfl⟩ : syracuseStep 1027295 = 1540943) B1540943
theorem B1027511 : Blo 455782 1027511 := bstep (se 1 (by rfl) ⟨770633, by rfl⟩ : syracuseStep 1027511 = 1541267) B1541267
theorem B1158583 : Blo 455782 1158583 := bstep (se 1 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 1158583 = 1737875) B1737875
theorem B1388027 : Blo 455782 1388027 := bstep (se 1 (by rfl) ⟨1041020, by rfl⟩ : syracuseStep 1388027 = 2082041) B2082041
theorem B1027691 : Blo 455782 1027691 := bstep (se 1 (by rfl) ⟨770768, by rfl⟩ : syracuseStep 1027691 = 1541537) B1541537
theorem B634601 : Blo 455782 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B1027961 : Blo 455782 1027961 := bstep (se 2 (by rfl) ⟨385485, by rfl⟩ : syracuseStep 1027961 = 770971) B770971
theorem B13512653 : Blo 455782 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B3912407 : Blo 455782 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B733961 : Blo 455782 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1487641 : Blo 455782 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B2962817 : Blo 455782 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B2307527 : Blo 455782 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B2602439 : Blo 455782 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B1095137 : Blo 455782 1095137 := bstep (se 2 (by rfl) ⟨410676, by rfl⟩ : syracuseStep 1095137 = 821353) B821353
theorem B1029815 : Blo 455782 1029815 := bstep (se 1 (by rfl) ⟨772361, by rfl⟩ : syracuseStep 1029815 = 1544723) B1544723
theorem B3487535 : Blo 455782 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B1161175 : Blo 455782 1161175 := bstep (se 1 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 1161175 = 1741763) B1741763
theorem B866447 : Blo 455782 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B1161449 : Blo 455782 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B1161479 : Blo 455782 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B35633459 : Blo 455782 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B1489225 : Blo 455782 1489225 := bstep (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) B1116919
theorem B5454253 : Blo 455782 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B2472601 : Blo 455782 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B1031003 : Blo 455782 1031003 := bstep (se 1 (by rfl) ⟨773252, by rfl⟩ : syracuseStep 1031003 = 1546505) B1546505
theorem B6273935 : Blo 455782 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1489823 : Blo 455782 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B2637095 : Blo 455782 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B1031759 : Blo 455782 1031759 := bstep (se 1 (by rfl) ⟨773819, by rfl⟩ : syracuseStep 1031759 = 1547639) B1547639
theorem B2605081 : Blo 455782 2605081 := bstep (se 2 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 2605081 = 1953811) B1953811
theorem B1097867 : Blo 455782 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B1032479 : Blo 455782 1032479 := bstep (se 1 (by rfl) ⟨774359, by rfl⟩ : syracuseStep 1032479 = 1548719) B1548719
theorem B770431 : Blo 455782 770431 := bstep (se 1 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 770431 = 1155647) B1155647
theorem B2605607 : Blo 455782 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B770863 : Blo 455782 770863 := bstep (se 1 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 770863 = 1156295) B1156295
theorem B869287 : Blo 455782 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B1033127 : Blo 455782 1033127 := bstep (se 1 (by rfl) ⟨774845, by rfl⟩ : syracuseStep 1033127 = 1549691) B1549691
theorem B1655795 : Blo 455782 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B6341777 : Blo 455782 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B7816337 : Blo 455782 7816337 := bstep (se 2 (by rfl) ⟨2931126, by rfl⟩ : syracuseStep 7816337 = 5862253) B5862253
theorem B53495113 : Blo 455782 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B1853039 : Blo 455782 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B771835 : Blo 455782 771835 := bstep (se 1 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 771835 = 1157753) B1157753
theorem B2934589 : Blo 455782 2934589 := bstep (se 3 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 2934589 = 1100471) B1100471
theorem B379012931 : Blo 455782 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B1034063 : Blo 455782 1034063 := bstep (se 1 (by rfl) ⟨775547, by rfl⟩ : syracuseStep 1034063 = 1551095) B1551095
theorem B1034081 : Blo 455782 1034081 := bstep (se 2 (by rfl) ⟨387780, by rfl⟩ : syracuseStep 1034081 = 775561) B775561
theorem B771977 : Blo 455782 771977 := bstep (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) B578983
theorem B772409 : Blo 455782 772409 := bstep (se 2 (by rfl) ⟨289653, by rfl⟩ : syracuseStep 772409 = 579307) B579307
theorem B2312711 : Blo 455782 2312711 := bstep (se 1 (by rfl) ⟨1734533, by rfl⟩ : syracuseStep 2312711 = 3469067) B3469067
theorem B4410071 : Blo 455782 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B773023 : Blo 455782 773023 := bstep (se 1 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 773023 = 1159535) B1159535
theorem B4410611 : Blo 455782 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B773455 : Blo 455782 773455 := bstep (se 1 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 773455 = 1160183) B1160183
theorem B773543 : Blo 455782 773543 := bstep (se 1 (by rfl) ⟨580157, by rfl⟩ : syracuseStep 773543 = 1160315) B1160315
theorem B773705 : Blo 455782 773705 := bstep (se 2 (by rfl) ⟨290139, by rfl⟩ : syracuseStep 773705 = 580279) B580279
theorem B1560221 : Blo 455782 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B1298281 : Blo 455782 1298281 := bstep (se 2 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 1298281 = 973711) B973711
theorem B1298555 : Blo 455782 1298555 := bstep (se 1 (by rfl) ⟨973916, by rfl⟩ : syracuseStep 1298555 = 1947833) B1947833
theorem B9392345 : Blo 455782 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B2314493 : Blo 455782 2314493 := bstep (se 3 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 2314493 = 867935) B867935
theorem B774751 : Blo 455782 774751 := bstep (se 1 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 774751 = 1162127) B1162127
theorem B2609981 : Blo 455782 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B775163 : Blo 455782 775163 := bstep (se 1 (by rfl) ⟨581372, by rfl⟩ : syracuseStep 775163 = 1162745) B1162745
theorem B2315303 : Blo 455782 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B6575201 : Blo 455782 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B775595 : Blo 455782 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B513787 : Blo 455782 513787 := bstep (se 1 (by rfl) ⟨385340, by rfl⟩ : syracuseStep 513787 = 770681) B770681
theorem B513823 : Blo 455782 513823 := bstep (se 1 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 513823 = 770735) B770735
theorem B4970497 : Blo 455782 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B1464425 : Blo 455782 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B1235177 : Blo 455782 1235177 := bstep (se 2 (by rfl) ⟨463191, by rfl⟩ : syracuseStep 1235177 = 926383) B926383
theorem B1301129 : Blo 455782 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B42326833 : Blo 455782 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B6282035 : Blo 455782 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B514975 : Blo 455782 514975 := bstep (se 1 (by rfl) ⟨386231, by rfl⟩ : syracuseStep 514975 = 772463) B772463
theorem B973865 : Blo 455782 973865 := bstep (se 2 (by rfl) ⟨365199, by rfl⟩ : syracuseStep 973865 = 730399) B730399
theorem B515119 : Blo 455782 515119 := bstep (se 1 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 515119 = 772679) B772679
theorem B3136637 : Blo 455782 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B2612371 : Blo 455782 2612371 := bstep (se 1 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 2612371 = 3918557) B3918557
theorem B5627083 : Blo 455782 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B515407 : Blo 455782 515407 := bstep (se 1 (by rfl) ⟨386555, by rfl⟩ : syracuseStep 515407 = 773111) B773111
theorem B515911 : Blo 455782 515911 := bstep (se 1 (by rfl) ⟨386933, by rfl⟩ : syracuseStep 515911 = 773867) B773867
theorem B3727619 : Blo 455782 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B1466743 : Blo 455782 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B516559 : Blo 455782 516559 := bstep (se 1 (by rfl) ⟨387419, by rfl⟩ : syracuseStep 516559 = 774839) B774839
theorem B7037725 : Blo 455782 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B8938291 : Blo 455782 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1467193 : Blo 455782 1467193 := bstep (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) B1100395
theorem B7922717 : Blo 455782 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B550567 : Blo 455782 550567 := bstep (se 1 (by rfl) ⟨412925, by rfl⟩ : syracuseStep 550567 = 825851) B825851
theorem B7825085 : Blo 455782 7825085 := bstep (se 3 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 7825085 = 2934407) B2934407
theorem B1468127 : Blo 455782 1468127 := bstep (se 1 (by rfl) ⟨1101095, by rfl⟩ : syracuseStep 1468127 = 2202191) B2202191
theorem B2615287 : Blo 455782 2615287 := bstep (se 1 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 2615287 = 3922931) B3922931
theorem B1862027 : Blo 455782 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B5237135 : Blo 455782 5237135 := bstep (se 1 (by rfl) ⟨3927851, by rfl⟩ : syracuseStep 5237135 = 7855703) B7855703
theorem B3926555 : Blo 455782 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B1960631 : Blo 455782 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B1502039 : Blo 455782 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B3140471 : Blo 455782 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B650143 : Blo 455782 650143 := bstep (se 1 (by rfl) ⟨487607, by rfl⟩ : syracuseStep 650143 = 975215) B975215
theorem B167668697 : Blo 455782 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B2944097 : Blo 455782 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B617593 : Blo 455782 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B1469819 : Blo 455782 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B683753 : Blo 455782 683753 := bstep (se 2 (by rfl) ⟨256407, by rfl⟩ : syracuseStep 683753 = 512815) B512815
theorem B683897 : Blo 455782 683897 := bstep (se 2 (by rfl) ⟨256461, by rfl⟩ : syracuseStep 683897 = 512923) B512923
theorem B2617271 : Blo 455782 2617271 := bstep (se 1 (by rfl) ⟨1962953, by rfl⟩ : syracuseStep 2617271 = 3925907) B3925907
theorem B683999 : Blo 455782 683999 := bstep (se 1 (by rfl) ⟨512999, by rfl⟩ : syracuseStep 683999 = 1025999) B1025999
theorem B1306813 : Blo 455782 1306813 := bstep (se 3 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 1306813 = 490055) B490055
theorem B684251 : Blo 455782 684251 := bstep (se 1 (by rfl) ⟨513188, by rfl⟩ : syracuseStep 684251 = 1026377) B1026377
theorem B684263 : Blo 455782 684263 := bstep (se 1 (by rfl) ⟨513197, by rfl⟩ : syracuseStep 684263 = 1026395) B1026395
theorem B2322755 : Blo 455782 2322755 := bstep (se 1 (by rfl) ⟨1742066, by rfl⟩ : syracuseStep 2322755 = 3484133) B3484133
theorem B684425 : Blo 455782 684425 := bstep (se 2 (by rfl) ⟨256659, by rfl⟩ : syracuseStep 684425 = 513319) B513319
theorem B1962407 : Blo 455782 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B684521 : Blo 455782 684521 := bstep (se 2 (by rfl) ⟨256695, by rfl⟩ : syracuseStep 684521 = 513391) B513391
theorem B5206517 : Blo 455782 5206517 := bstep (se 5 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 5206517 = 488111) B488111
theorem B684647 : Blo 455782 684647 := bstep (se 1 (by rfl) ⟨513485, by rfl⟩ : syracuseStep 684647 = 1026971) B1026971
theorem B684779 : Blo 455782 684779 := bstep (se 1 (by rfl) ⟨513584, by rfl⟩ : syracuseStep 684779 = 1027169) B1027169
theorem B684809 : Blo 455782 684809 := bstep (se 2 (by rfl) ⟨256803, by rfl⟩ : syracuseStep 684809 = 513607) B513607
theorem B684911 : Blo 455782 684911 := bstep (se 1 (by rfl) ⟨513683, by rfl⟩ : syracuseStep 684911 = 1027367) B1027367
theorem B1733501 : Blo 455782 1733501 := bstep (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) B650063
theorem B488359 : Blo 455782 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B7435253 : Blo 455782 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B685163 : Blo 455782 685163 := bstep (se 1 (by rfl) ⟨513872, by rfl⟩ : syracuseStep 685163 = 1027745) B1027745
theorem B455887 : Blo 455782 455887 := bstep (se 1 (by rfl) ⟨341915, by rfl⟩ : syracuseStep 455887 = 683831) B683831
theorem B685403 : Blo 455782 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B456091 : Blo 455782 456091 := bstep (se 1 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 456091 = 684137) B684137
theorem B1766855 : Blo 455782 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B456303 : Blo 455782 456303 := bstep (se 1 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 456303 = 684455) B684455
theorem B685679 : Blo 455782 685679 := bstep (se 1 (by rfl) ⟨514259, by rfl⟩ : syracuseStep 685679 = 1028519) B1028519
theorem B456359 : Blo 455782 456359 := bstep (se 1 (by rfl) ⟨342269, by rfl⟩ : syracuseStep 456359 = 684539) B684539
theorem B685751 : Blo 455782 685751 := bstep (se 1 (by rfl) ⟨514313, by rfl⟩ : syracuseStep 685751 = 1028627) B1028627
theorem B685787 : Blo 455782 685787 := bstep (se 1 (by rfl) ⟨514340, by rfl⟩ : syracuseStep 685787 = 1028681) B1028681
theorem B456443 : Blo 455782 456443 := bstep (se 1 (by rfl) ⟨342332, by rfl⟩ : syracuseStep 456443 = 684665) B684665
theorem B456479 : Blo 455782 456479 := bstep (se 1 (by rfl) ⟨342359, by rfl⟩ : syracuseStep 456479 = 684719) B684719
theorem B456511 : Blo 455782 456511 := bstep (se 1 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 456511 = 684767) B684767
theorem B685961 : Blo 455782 685961 := bstep (se 2 (by rfl) ⟨257235, by rfl⟩ : syracuseStep 685961 = 514471) B514471
theorem B25098133 : Blo 455782 25098133 := bstep (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) B1176475
theorem B653287 : Blo 455782 653287 := bstep (se 1 (by rfl) ⟨489965, by rfl⟩ : syracuseStep 653287 = 979931) B979931
theorem B456687 : Blo 455782 456687 := bstep (se 1 (by rfl) ⟨342515, by rfl⟩ : syracuseStep 456687 = 685031) B685031
theorem B686063 : Blo 455782 686063 := bstep (se 1 (by rfl) ⟨514547, by rfl⟩ : syracuseStep 686063 = 1029095) B1029095
theorem B11892815 : Blo 455782 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B456859 : Blo 455782 456859 := bstep (se 1 (by rfl) ⟨342644, by rfl⟩ : syracuseStep 456859 = 685289) B685289
theorem B456895 : Blo 455782 456895 := bstep (se 1 (by rfl) ⟨342671, by rfl⟩ : syracuseStep 456895 = 685343) B685343
theorem B653503 : Blo 455782 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B686315 : Blo 455782 686315 := bstep (se 1 (by rfl) ⟨514736, by rfl⟩ : syracuseStep 686315 = 1029473) B1029473
theorem B686375 : Blo 455782 686375 := bstep (se 1 (by rfl) ⟨514781, by rfl⟩ : syracuseStep 686375 = 1029563) B1029563
theorem B457007 : Blo 455782 457007 := bstep (se 1 (by rfl) ⟨342755, by rfl⟩ : syracuseStep 457007 = 685511) B685511
theorem B686459 : Blo 455782 686459 := bstep (se 1 (by rfl) ⟨514844, by rfl⟩ : syracuseStep 686459 = 1029689) B1029689
theorem B457243 : Blo 455782 457243 := bstep (se 1 (by rfl) ⟨342932, by rfl⟩ : syracuseStep 457243 = 685865) B685865
theorem B457247 : Blo 455782 457247 := bstep (se 1 (by rfl) ⟨342935, by rfl⟩ : syracuseStep 457247 = 685871) B685871
theorem B4684349 : Blo 455782 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B686729 : Blo 455782 686729 := bstep (se 2 (by rfl) ⟨257523, by rfl⟩ : syracuseStep 686729 = 515047) B515047
theorem B5569235 : Blo 455782 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B1538783 : Blo 455782 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B686903 : Blo 455782 686903 := bstep (se 1 (by rfl) ⟨515177, by rfl⟩ : syracuseStep 686903 = 1030355) B1030355
theorem B457563 : Blo 455782 457563 := bstep (se 1 (by rfl) ⟨343172, by rfl⟩ : syracuseStep 457563 = 686345) B686345
theorem B686939 : Blo 455782 686939 := bstep (se 1 (by rfl) ⟨515204, by rfl⟩ : syracuseStep 686939 = 1030409) B1030409
theorem B457631 : Blo 455782 457631 := bstep (se 1 (by rfl) ⟨343223, by rfl⟩ : syracuseStep 457631 = 686447) B686447
theorem B687083 : Blo 455782 687083 := bstep (se 1 (by rfl) ⟨515312, by rfl⟩ : syracuseStep 687083 = 1030625) B1030625
theorem B457775 : Blo 455782 457775 := bstep (se 1 (by rfl) ⟨343331, by rfl⟩ : syracuseStep 457775 = 686663) B686663
theorem B457799 : Blo 455782 457799 := bstep (se 1 (by rfl) ⟨343349, by rfl⟩ : syracuseStep 457799 = 686699) B686699
theorem B1571987 : Blo 455782 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B687287 : Blo 455782 687287 := bstep (se 1 (by rfl) ⟨515465, by rfl⟩ : syracuseStep 687287 = 1030931) B1030931
theorem B457951 : Blo 455782 457951 := bstep (se 1 (by rfl) ⟨343463, by rfl⟩ : syracuseStep 457951 = 686927) B686927
theorem B687527 : Blo 455782 687527 := bstep (se 1 (by rfl) ⟨515645, by rfl⟩ : syracuseStep 687527 = 1031291) B1031291
theorem B1539539 : Blo 455782 1539539 := bstep (se 1 (by rfl) ⟨1154654, by rfl⟩ : syracuseStep 1539539 = 2309309) B2309309
theorem B458215 : Blo 455782 458215 := bstep (se 1 (by rfl) ⟨343661, by rfl⟩ : syracuseStep 458215 = 687323) B687323
theorem B785911 : Blo 455782 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B687611 : Blo 455782 687611 := bstep (se 1 (by rfl) ⟨515708, by rfl⟩ : syracuseStep 687611 = 1031417) B1031417
theorem B458331 : Blo 455782 458331 := bstep (se 1 (by rfl) ⟨343748, by rfl⟩ : syracuseStep 458331 = 687497) B687497
theorem B687707 : Blo 455782 687707 := bstep (se 1 (by rfl) ⟨515780, by rfl⟩ : syracuseStep 687707 = 1031561) B1031561
theorem B687791 : Blo 455782 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B1539809 : Blo 455782 1539809 := bstep (se 2 (by rfl) ⟨577428, by rfl⟩ : syracuseStep 1539809 = 1154857) B1154857
theorem B1736417 : Blo 455782 1736417 := bstep (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) B1302313
theorem B687911 : Blo 455782 687911 := bstep (se 1 (by rfl) ⟨515933, by rfl⟩ : syracuseStep 687911 = 1031867) B1031867
theorem B458567 : Blo 455782 458567 := bstep (se 1 (by rfl) ⟨343925, by rfl⟩ : syracuseStep 458567 = 687851) B687851
theorem B687995 : Blo 455782 687995 := bstep (se 1 (by rfl) ⟨515996, by rfl⟩ : syracuseStep 687995 = 1031993) B1031993
theorem B458719 : Blo 455782 458719 := bstep (se 1 (by rfl) ⟨344039, by rfl⟩ : syracuseStep 458719 = 688079) B688079
theorem B3473441 : Blo 455782 3473441 := bstep (se 2 (by rfl) ⟨1302540, by rfl⟩ : syracuseStep 3473441 = 2605081) B2605081
theorem B688319 : Blo 455782 688319 := bstep (se 1 (by rfl) ⟨516239, by rfl⟩ : syracuseStep 688319 = 1032479) B1032479
theorem B458943 : Blo 455782 458943 := bstep (se 1 (by rfl) ⟨344207, by rfl⟩ : syracuseStep 458943 = 688415) B688415
theorem B458959 : Blo 455782 458959 := bstep (se 1 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 458959 = 688439) B688439
theorem B459007 : Blo 455782 459007 := bstep (se 1 (by rfl) ⟨344255, by rfl⟩ : syracuseStep 459007 = 688511) B688511
theorem B459055 : Blo 455782 459055 := bstep (se 1 (by rfl) ⟨344291, by rfl⟩ : syracuseStep 459055 = 688583) B688583
theorem B1737071 : Blo 455782 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B459291 : Blo 455782 459291 := bstep (se 1 (by rfl) ⟨344468, by rfl⟩ : syracuseStep 459291 = 688937) B688937
theorem B459295 : Blo 455782 459295 := bstep (se 1 (by rfl) ⟨344471, by rfl⟩ : syracuseStep 459295 = 688943) B688943
theorem B688745 : Blo 455782 688745 := bstep (se 2 (by rfl) ⟨258279, by rfl⟩ : syracuseStep 688745 = 516559) B516559
theorem B688751 : Blo 455782 688751 := bstep (se 1 (by rfl) ⟨516563, by rfl⟩ : syracuseStep 688751 = 1033127) B1033127
theorem B459375 : Blo 455782 459375 := bstep (se 1 (by rfl) ⟨344531, by rfl⟩ : syracuseStep 459375 = 689063) B689063
theorem B459431 : Blo 455782 459431 := bstep (se 1 (by rfl) ⟨344573, by rfl⟩ : syracuseStep 459431 = 689147) B689147
theorem B459471 : Blo 455782 459471 := bstep (se 1 (by rfl) ⟨344603, by rfl⟩ : syracuseStep 459471 = 689207) B689207
theorem B4227851 : Blo 455782 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B5210891 : Blo 455782 5210891 := bstep (se 1 (by rfl) ⟨3908168, by rfl⟩ : syracuseStep 5210891 = 7816337) B7816337
theorem B459551 : Blo 455782 459551 := bstep (se 1 (by rfl) ⟨344663, by rfl⟩ : syracuseStep 459551 = 689327) B689327
theorem B252675287 : Blo 455782 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B689375 : Blo 455782 689375 := bstep (se 1 (by rfl) ⟨517031, by rfl⟩ : syracuseStep 689375 = 1034063) B1034063
theorem B689387 : Blo 455782 689387 := bstep (se 1 (by rfl) ⟨517040, by rfl⟩ : syracuseStep 689387 = 1034081) B1034081
theorem B3901061 : Blo 455782 3901061 := bstep (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) B731449
theorem B1541807 : Blo 455782 1541807 := bstep (se 1 (by rfl) ⟨1156355, by rfl⟩ : syracuseStep 1541807 = 2312711) B2312711
theorem B5867585 : Blo 455782 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B6261563 : Blo 455782 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1542995 : Blo 455782 1542995 := bstep (se 1 (by rfl) ⟨1157246, by rfl⟩ : syracuseStep 1542995 = 2314493) B2314493
theorem B1739987 : Blo 455782 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B1543535 : Blo 455782 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B6688757 : Blo 455782 6688757 := bstep (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) B627071
theorem B823451 : Blo 455782 823451 := bstep (se 1 (by rfl) ⟨617588, by rfl⟩ : syracuseStep 823451 = 1235177) B1235177
theorem B823457 : Blo 455782 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B1544777 : Blo 455782 1544777 := bstep (se 2 (by rfl) ⟨579291, by rfl⟩ : syracuseStep 1544777 = 1158583) B1158583
theorem B2233327 : Blo 455782 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B4396463 : Blo 455782 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1742417 : Blo 455782 1742417 := bstep (se 2 (by rfl) ⟨653406, by rfl⟩ : syracuseStep 1742417 = 1306813) B1306813
theorem B5281811 : Blo 455782 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B5216723 : Blo 455782 5216723 := bstep (se 1 (by rfl) ⟨3912542, by rfl⟩ : syracuseStep 5216723 = 7825085) B7825085
theorem B12491597 : Blo 455782 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B111779131 : Blo 455782 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B925351 : Blo 455782 925351 := bstep (se 1 (by rfl) ⟨694013, by rfl⟩ : syracuseStep 925351 = 1388027) B1388027
theorem B33464177 : Blo 455782 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B1548233 : Blo 455782 1548233 := bstep (se 2 (by rfl) ⟨580587, by rfl⟩ : syracuseStep 1548233 = 1161175) B1161175
theorem B1744847 : Blo 455782 1744847 := bstep (se 1 (by rfl) ⟨1308635, by rfl⟩ : syracuseStep 1744847 = 2617271) B2617271
theorem B6627329 : Blo 455782 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B1548503 : Blo 455782 1548503 := bstep (se 1 (by rfl) ⟨1161377, by rfl⟩ : syracuseStep 1548503 = 2322755) B2322755
theorem B1155667 : Blo 455782 1155667 := bstep (se 1 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 1155667 = 1733501) B1733501
theorem B4956835 : Blo 455782 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B1975211 : Blo 455782 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B730091 : Blo 455782 730091 := bstep (se 1 (by rfl) ⟨547568, by rfl⟩ : syracuseStep 730091 = 1095137) B1095137
theorem B56435777 : Blo 455782 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B3483161 : Blo 455782 3483161 := bstep (se 2 (by rfl) ⟨1306185, by rfl⟩ : syracuseStep 3483161 = 2612371) B2612371
theorem B3712823 : Blo 455782 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B1025855 : Blo 455782 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B993215 : Blo 455782 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B1026359 : Blo 455782 1026359 := bstep (se 1 (by rfl) ⟨769769, by rfl⟩ : syracuseStep 1026359 = 1539539) B1539539
theorem B1026539 : Blo 455782 1026539 := bstep (se 1 (by rfl) ⟨769904, by rfl⟩ : syracuseStep 1026539 = 1539809) B1539809
theorem B1157611 : Blo 455782 1157611 := bstep (se 1 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 1157611 = 1736417) B1736417
theorem B731911 : Blo 455782 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B1551311 : Blo 455782 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B1027241 : Blo 455782 1027241 := bstep (se 2 (by rfl) ⟨385215, by rfl⟩ : syracuseStep 1027241 = 770431) B770431
theorem B1551635 : Blo 455782 1551635 := bstep (se 1 (by rfl) ⟨1163726, by rfl⟩ : syracuseStep 1551635 = 2327453) B2327453
theorem B1027655 : Blo 455782 1027655 := bstep (se 1 (by rfl) ⟨770741, by rfl⟩ : syracuseStep 1027655 = 1541483) B1541483
theorem B1027727 : Blo 455782 1027727 := bstep (se 1 (by rfl) ⟨770795, by rfl⟩ : syracuseStep 1027727 = 1541591) B1541591
theorem B2928311 : Blo 455782 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B9383633 : Blo 455782 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1027817 : Blo 455782 1027817 := bstep (se 2 (by rfl) ⟨385431, by rfl⟩ : syracuseStep 1027817 = 770863) B770863
theorem B1027835 : Blo 455782 1027835 := bstep (se 1 (by rfl) ⟨770876, by rfl⟩ : syracuseStep 1027835 = 1541753) B1541753
theorem B1159049 : Blo 455782 1159049 := bstep (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) B869287
theorem B3715417 : Blo 455782 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B11907749 : Blo 455782 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B1028843 : Blo 455782 1028843 := bstep (se 1 (by rfl) ⟨771632, by rfl⟩ : syracuseStep 1028843 = 1543265) B1543265
theorem B1029113 : Blo 455782 1029113 := bstep (se 2 (by rfl) ⟨385917, by rfl⟩ : syracuseStep 1029113 = 771835) B771835
theorem B3912785 : Blo 455782 3912785 := bstep (se 2 (by rfl) ⟨1467294, by rfl⟩ : syracuseStep 3912785 = 2934589) B2934589
theorem B1029203 : Blo 455782 1029203 := bstep (se 1 (by rfl) ⟨771902, by rfl⟩ : syracuseStep 1029203 = 1543805) B1543805
theorem B1946875 : Blo 455782 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B1029383 : Blo 455782 1029383 := bstep (se 1 (by rfl) ⟨772037, by rfl⟩ : syracuseStep 1029383 = 1544075) B1544075
theorem B3487049 : Blo 455782 3487049 := bstep (se 2 (by rfl) ⟨1307643, by rfl⟩ : syracuseStep 3487049 = 2615287) B2615287
theorem B865703 : Blo 455782 865703 := bstep (se 1 (by rfl) ⟨649277, by rfl⟩ : syracuseStep 865703 = 1298555) B1298555
theorem B1029743 : Blo 455782 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B1095407 : Blo 455782 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B1161287 : Blo 455782 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B1030607 : Blo 455782 1030607 := bstep (se 1 (by rfl) ⟨772955, by rfl⟩ : syracuseStep 1030607 = 1545911) B1545911
theorem B866857 : Blo 455782 866857 := bstep (se 2 (by rfl) ⟨325071, by rfl⟩ : syracuseStep 866857 = 650143) B650143
theorem B1030697 : Blo 455782 1030697 := bstep (se 2 (by rfl) ⟨386511, by rfl⟩ : syracuseStep 1030697 = 773023) B773023
theorem B5880707 : Blo 455782 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B867419 : Blo 455782 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B1031273 : Blo 455782 1031273 := bstep (se 2 (by rfl) ⟨386727, by rfl⟩ : syracuseStep 1031273 = 773455) B773455
theorem B1031399 : Blo 455782 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1162471 : Blo 455782 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B2604581 : Blo 455782 2604581 := bstep (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) B488359
theorem B1031903 : Blo 455782 1031903 := bstep (se 1 (by rfl) ⟨773927, by rfl⟩ : syracuseStep 1031903 = 1547855) B1547855
theorem B7126751 : Blo 455782 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B1031975 : Blo 455782 1031975 := bstep (se 1 (by rfl) ⟨773981, by rfl⟩ : syracuseStep 1031975 = 1547963) B1547963
theorem B769871 : Blo 455782 769871 := bstep (se 1 (by rfl) ⟨577403, by rfl⟩ : syracuseStep 769871 = 1154807) B1154807
theorem B2933435 : Blo 455782 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B1033001 : Blo 455782 1033001 := bstep (se 2 (by rfl) ⟨387375, by rfl⟩ : syracuseStep 1033001 = 774751) B774751
theorem B2081603 : Blo 455782 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B1983521 : Blo 455782 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B1033271 : Blo 455782 1033271 := bstep (se 1 (by rfl) ⟨774953, by rfl⟩ : syracuseStep 1033271 = 1549907) B1549907
theorem B771295 : Blo 455782 771295 := bstep (se 1 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 771295 = 1156943) B1156943
theorem B1033451 : Blo 455782 1033451 := bstep (se 1 (by rfl) ⟨775088, by rfl⟩ : syracuseStep 1033451 = 1550177) B1550177
theorem B9356705 : Blo 455782 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B1099327 : Blo 455782 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B3491423 : Blo 455782 3491423 := bstep (se 1 (by rfl) ⟨2618567, by rfl⟩ : syracuseStep 3491423 = 5237135) B5237135
theorem B1033919 : Blo 455782 1033919 := bstep (se 1 (by rfl) ⟨775439, by rfl⟩ : syracuseStep 1033919 = 1550879) B1550879
theorem B1001359 : Blo 455782 1001359 := bstep (se 1 (by rfl) ⟨751019, by rfl⟩ : syracuseStep 1001359 = 1502039) B1502039
theorem B2935433 : Blo 455782 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B871049 : Blo 455782 871049 := bstep (se 2 (by rfl) ⟨326643, by rfl⟩ : syracuseStep 871049 = 653287) B653287
theorem B871337 : Blo 455782 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B1985633 : Blo 455782 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B2608271 : Blo 455782 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B7032253 : Blo 455782 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B3296801 : Blo 455782 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2936357 : Blo 455782 2936357 := bstep (se 4 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 2936357 = 550567) B550567
theorem B577631 : Blo 455782 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B774299 : Blo 455782 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B774319 : Blo 455782 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B4182623 : Blo 455782 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B1692269 : Blo 455782 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B2774695 : Blo 455782 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B1955657 : Blo 455782 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B1103863 : Blo 455782 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B11917721 : Blo 455782 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B1235359 : Blo 455782 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B1956257 : Blo 455782 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B514651 : Blo 455782 514651 := bstep (se 1 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 514651 = 771977) B771977
theorem B973625 : Blo 455782 973625 := bstep (se 2 (by rfl) ⟨365109, by rfl⟩ : syracuseStep 973625 = 730219) B730219
theorem B514939 : Blo 455782 514939 := bstep (se 1 (by rfl) ⟨386204, by rfl⟩ : syracuseStep 514939 = 772409) B772409
theorem B71326817 : Blo 455782 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B2317409 : Blo 455782 2317409 := bstep (se 2 (by rfl) ⟨869028, by rfl⟩ : syracuseStep 2317409 = 1738057) B1738057
theorem B2940047 : Blo 455782 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B1957229 : Blo 455782 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B2940407 : Blo 455782 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B515695 : Blo 455782 515695 := bstep (se 1 (by rfl) ⟨386771, by rfl⟩ : syracuseStep 515695 = 773543) B773543
theorem B4415143 : Blo 455782 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B515803 : Blo 455782 515803 := bstep (se 1 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 515803 = 773705) B773705
theorem B1040147 : Blo 455782 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B2318219 : Blo 455782 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B516775 : Blo 455782 516775 := bstep (se 1 (by rfl) ⟨387581, by rfl⟩ : syracuseStep 516775 = 775163) B775163
theorem B4383467 : Blo 455782 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B517063 : Blo 455782 517063 := bstep (se 1 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 517063 = 775595) B775595
theorem B10576925 : Blo 455782 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B976283 : Blo 455782 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B4188023 : Blo 455782 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B649243 : Blo 455782 649243 := bstep (se 1 (by rfl) ⟨486932, by rfl⟩ : syracuseStep 649243 = 973865) B973865
theorem B2091091 : Blo 455782 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B1731041 : Blo 455782 1731041 := bstep (se 2 (by rfl) ⟨649140, by rfl⟩ : syracuseStep 1731041 = 1298281) B1298281
theorem B616939 : Blo 455782 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B2485079 : Blo 455782 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B552043 : Blo 455782 552043 := bstep (se 1 (by rfl) ⟨414032, by rfl⟩ : syracuseStep 552043 = 828065) B828065
theorem B5958845 : Blo 455782 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B683771 : Blo 455782 683771 := bstep (se 1 (by rfl) ⟨512828, by rfl⟩ : syracuseStep 683771 = 1025657) B1025657
theorem B31289125 : Blo 455782 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B978751 : Blo 455782 978751 := bstep (se 1 (by rfl) ⟨734063, by rfl⟩ : syracuseStep 978751 = 1468127) B1468127
theorem B3895289 : Blo 455782 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B1241351 : Blo 455782 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B2617703 : Blo 455782 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B684443 : Blo 455782 684443 := bstep (se 1 (by rfl) ⟨513332, by rfl⟩ : syracuseStep 684443 = 1026665) B1026665
theorem B1307087 : Blo 455782 1307087 := bstep (se 1 (by rfl) ⟨980315, by rfl⟩ : syracuseStep 1307087 = 1960631) B1960631
theorem B2093647 : Blo 455782 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B2191967 : Blo 455782 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B3895937 : Blo 455782 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B1962731 : Blo 455782 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B684863 : Blo 455782 684863 := bstep (se 1 (by rfl) ⟨513647, by rfl⟩ : syracuseStep 684863 = 1027295) B1027295
theorem B979879 : Blo 455782 979879 := bstep (se 1 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 979879 = 1469819) B1469819
theorem B685007 : Blo 455782 685007 := bstep (se 1 (by rfl) ⟨513755, by rfl⟩ : syracuseStep 685007 = 1027511) B1027511
theorem B685049 : Blo 455782 685049 := bstep (se 2 (by rfl) ⟨256893, by rfl⟩ : syracuseStep 685049 = 513787) B513787
theorem B685097 : Blo 455782 685097 := bstep (se 2 (by rfl) ⟨256911, by rfl⟩ : syracuseStep 685097 = 513823) B513823
theorem B685127 : Blo 455782 685127 := bstep (se 1 (by rfl) ⟨513845, by rfl⟩ : syracuseStep 685127 = 1027691) B1027691
theorem B455835 : Blo 455782 455835 := bstep (se 1 (by rfl) ⟨341876, by rfl⟩ : syracuseStep 455835 = 683753) B683753
theorem B455931 : Blo 455782 455931 := bstep (se 1 (by rfl) ⟨341948, by rfl⟩ : syracuseStep 455931 = 683897) B683897
theorem B685307 : Blo 455782 685307 := bstep (se 1 (by rfl) ⟨513980, by rfl⟩ : syracuseStep 685307 = 1027961) B1027961
theorem B9008435 : Blo 455782 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B455999 : Blo 455782 455999 := bstep (se 1 (by rfl) ⟨341999, by rfl⟩ : syracuseStep 455999 = 683999) B683999
theorem B456167 : Blo 455782 456167 := bstep (se 1 (by rfl) ⟨342125, by rfl⟩ : syracuseStep 456167 = 684251) B684251
theorem B456175 : Blo 455782 456175 := bstep (se 1 (by rfl) ⟨342131, by rfl⟩ : syracuseStep 456175 = 684263) B684263
theorem B456283 : Blo 455782 456283 := bstep (se 1 (by rfl) ⟨342212, by rfl⟩ : syracuseStep 456283 = 684425) B684425
theorem B1308271 : Blo 455782 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B456347 : Blo 455782 456347 := bstep (se 1 (by rfl) ⟨342260, by rfl⟩ : syracuseStep 456347 = 684521) B684521
theorem B3471011 : Blo 455782 3471011 := bstep (se 1 (by rfl) ⟨2603258, by rfl⟩ : syracuseStep 3471011 = 5206517) B5206517
theorem B456431 : Blo 455782 456431 := bstep (se 1 (by rfl) ⟨342323, by rfl⟩ : syracuseStep 456431 = 684647) B684647
theorem B456519 : Blo 455782 456519 := bstep (se 1 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 456519 = 684779) B684779
theorem B456539 : Blo 455782 456539 := bstep (se 1 (by rfl) ⟨342404, by rfl⟩ : syracuseStep 456539 = 684809) B684809
theorem B7272337 : Blo 455782 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B456607 : Blo 455782 456607 := bstep (se 1 (by rfl) ⟨342455, by rfl⟩ : syracuseStep 456607 = 684911) B684911
theorem B456775 : Blo 455782 456775 := bstep (se 1 (by rfl) ⟨342581, by rfl⟩ : syracuseStep 456775 = 685163) B685163
theorem B456935 : Blo 455782 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B1538351 : Blo 455782 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B1734959 : Blo 455782 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B1177903 : Blo 455782 1177903 := bstep (se 1 (by rfl) ⟨883427, by rfl⟩ : syracuseStep 1177903 = 1766855) B1766855
theorem B457119 : Blo 455782 457119 := bstep (se 1 (by rfl) ⟨342839, by rfl⟩ : syracuseStep 457119 = 685679) B685679
theorem B457167 : Blo 455782 457167 := bstep (se 1 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 457167 = 685751) B685751
theorem B686543 : Blo 455782 686543 := bstep (se 1 (by rfl) ⟨514907, by rfl⟩ : syracuseStep 686543 = 1029815) B1029815
theorem B457191 : Blo 455782 457191 := bstep (se 1 (by rfl) ⟨342893, by rfl⟩ : syracuseStep 457191 = 685787) B685787
theorem B2325023 : Blo 455782 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B686633 : Blo 455782 686633 := bstep (se 2 (by rfl) ⟨257487, by rfl⟩ : syracuseStep 686633 = 514975) B514975
theorem B457307 : Blo 455782 457307 := bstep (se 1 (by rfl) ⟨342980, by rfl⟩ : syracuseStep 457307 = 685961) B685961
theorem B457375 : Blo 455782 457375 := bstep (se 1 (by rfl) ⟨343031, by rfl⟩ : syracuseStep 457375 = 686063) B686063
theorem B7928543 : Blo 455782 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B686825 : Blo 455782 686825 := bstep (se 2 (by rfl) ⟨257559, by rfl⟩ : syracuseStep 686825 = 515119) B515119
theorem B457543 : Blo 455782 457543 := bstep (se 1 (by rfl) ⟨343157, by rfl⟩ : syracuseStep 457543 = 686315) B686315
theorem B457583 : Blo 455782 457583 := bstep (se 1 (by rfl) ⟨343187, by rfl⟩ : syracuseStep 457583 = 686375) B686375
theorem B23755639 : Blo 455782 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B457639 : Blo 455782 457639 := bstep (se 1 (by rfl) ⟨343229, by rfl⟩ : syracuseStep 457639 = 686459) B686459
theorem B7502777 : Blo 455782 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B457819 : Blo 455782 457819 := bstep (se 1 (by rfl) ⟨343364, by rfl⟩ : syracuseStep 457819 = 686729) B686729
theorem B687209 : Blo 455782 687209 := bstep (se 2 (by rfl) ⟨257703, by rfl⟩ : syracuseStep 687209 = 515407) B515407
theorem B457935 : Blo 455782 457935 := bstep (se 1 (by rfl) ⟨343451, by rfl⟩ : syracuseStep 457935 = 686903) B686903
theorem B457959 : Blo 455782 457959 := bstep (se 1 (by rfl) ⟨343469, by rfl⟩ : syracuseStep 457959 = 686939) B686939
theorem B687335 : Blo 455782 687335 := bstep (se 1 (by rfl) ⟨515501, by rfl⟩ : syracuseStep 687335 = 1031003) B1031003
theorem B458055 : Blo 455782 458055 := bstep (se 1 (by rfl) ⟨343541, by rfl⟩ : syracuseStep 458055 = 687083) B687083
theorem B1047881 : Blo 455782 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B1047991 : Blo 455782 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B458191 : Blo 455782 458191 := bstep (se 1 (by rfl) ⟨343643, by rfl⟩ : syracuseStep 458191 = 687287) B687287
theorem B458351 : Blo 455782 458351 := bstep (se 1 (by rfl) ⟨343763, by rfl⟩ : syracuseStep 458351 = 687527) B687527
theorem B458407 : Blo 455782 458407 := bstep (se 1 (by rfl) ⟨343805, by rfl⟩ : syracuseStep 458407 = 687611) B687611
theorem B687839 : Blo 455782 687839 := bstep (se 1 (by rfl) ⟨515879, by rfl⟩ : syracuseStep 687839 = 1031759) B1031759
theorem B458471 : Blo 455782 458471 := bstep (se 1 (by rfl) ⟨343853, by rfl⟩ : syracuseStep 458471 = 687707) B687707
theorem B687881 : Blo 455782 687881 := bstep (se 2 (by rfl) ⟨257955, by rfl⟩ : syracuseStep 687881 = 515911) B515911
theorem B458527 : Blo 455782 458527 := bstep (se 1 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 458527 = 687791) B687791
theorem B458607 : Blo 455782 458607 := bstep (se 1 (by rfl) ⟨343955, by rfl⟩ : syracuseStep 458607 = 687911) B687911
theorem B458663 : Blo 455782 458663 := bstep (se 1 (by rfl) ⟨343997, by rfl⟩ : syracuseStep 458663 = 687995) B687995
theorem B458879 : Blo 455782 458879 := bstep (se 1 (by rfl) ⟨344159, by rfl⟩ : syracuseStep 458879 = 688319) B688319
theorem B1540349 : Blo 455782 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B459163 : Blo 455782 459163 := bstep (se 1 (by rfl) ⟨344372, by rfl⟩ : syracuseStep 459163 = 688745) B688745
theorem B2195869 : Blo 455782 2195869 := bstep (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) B823451
theorem B459167 : Blo 455782 459167 := bstep (se 1 (by rfl) ⟨344375, by rfl⟩ : syracuseStep 459167 = 688751) B688751
theorem B2195885 : Blo 455782 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B2818567 : Blo 455782 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3473927 : Blo 455782 3473927 := bstep (se 1 (by rfl) ⟨2605445, by rfl⟩ : syracuseStep 3473927 = 5210891) B5210891
theorem B688667 : Blo 455782 688667 := bstep (se 1 (by rfl) ⟨516500, by rfl⟩ : syracuseStep 688667 = 1033001) B1033001
theorem B688847 : Blo 455782 688847 := bstep (se 1 (by rfl) ⟨516635, by rfl⟩ : syracuseStep 688847 = 1033271) B1033271
theorem B1540889 : Blo 455782 1540889 := bstep (se 2 (by rfl) ⟨577833, by rfl⟩ : syracuseStep 1540889 = 1155667) B1155667
theorem B459583 : Blo 455782 459583 := bstep (se 1 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 459583 = 689375) B689375
theorem B688967 : Blo 455782 688967 := bstep (se 1 (by rfl) ⟨516725, by rfl⟩ : syracuseStep 688967 = 1033451) B1033451
theorem B459591 : Blo 455782 459591 := bstep (se 1 (by rfl) ⟨344693, by rfl⟩ : syracuseStep 459591 = 689387) B689387
theorem B689033 : Blo 455782 689033 := bstep (se 2 (by rfl) ⟨258387, by rfl⟩ : syracuseStep 689033 = 516775) B516775
theorem B2327615 : Blo 455782 2327615 := bstep (se 1 (by rfl) ⟨1745711, by rfl⟩ : syracuseStep 2327615 = 3491423) B3491423
theorem B689279 : Blo 455782 689279 := bstep (se 1 (by rfl) ⟨516959, by rfl⟩ : syracuseStep 689279 = 1033919) B1033919
theorem B689417 : Blo 455782 689417 := bstep (se 2 (by rfl) ⟨258531, by rfl⟩ : syracuseStep 689417 = 517063) B517063
theorem B1738847 : Blo 455782 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B2197867 : Blo 455782 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2788121 : Blo 455782 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B2788415 : Blo 455782 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B1543481 : Blo 455782 1543481 := bstep (se 2 (by rfl) ⟨578805, by rfl⟩ : syracuseStep 1543481 = 1157611) B1157611
theorem B3477815 : Blo 455782 3477815 := bstep (se 1 (by rfl) ⟨2608361, by rfl⟩ : syracuseStep 3477815 = 5216723) B5216723
theorem B8327731 : Blo 455782 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B9376337 : Blo 455782 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B47551211 : Blo 455782 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B1544939 : Blo 455782 1544939 := bstep (se 1 (by rfl) ⟨1158704, by rfl⟩ : syracuseStep 1544939 = 2317409) B2317409
theorem B41718833 : Blo 455782 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B693431 : Blo 455782 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B1545479 : Blo 455782 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B4953889 : Blo 455782 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B2922311 : Blo 455782 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B1316807 : Blo 455782 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B7051283 : Blo 455782 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B37623851 : Blo 455782 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B2791529 : Blo 455782 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B2792015 : Blo 455782 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B662143 : Blo 455782 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B1154027 : Blo 455782 1154027 := bstep (se 1 (by rfl) ⟨865520, by rfl⟩ : syracuseStep 1154027 = 1731041) B1731041
theorem B2595833 : Blo 455782 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B3972563 : Blo 455782 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B1744361 : Blo 455782 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B2596333 : Blo 455782 2596333 := bstep (se 3 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 2596333 = 973625) B973625
theorem B2596859 : Blo 455782 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B827567 : Blo 455782 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B1745135 : Blo 455782 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B2597291 : Blo 455782 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B7938499 : Blo 455782 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B1647145 : Blo 455782 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B1155809 : Blo 455782 1155809 := bstep (se 2 (by rfl) ⟨433428, by rfl⟩ : syracuseStep 1155809 = 866857) B866857
theorem B6005623 : Blo 455782 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B730271 : Blo 455782 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B1025567 : Blo 455782 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B1156639 : Blo 455782 1156639 := bstep (se 1 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 1156639 = 1734959) B1734959
theorem B1549961 : Blo 455782 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B1550015 : Blo 455782 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B149038841 : Blo 455782 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B5285695 : Blo 455782 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B698587 : Blo 455782 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B17836685 : Blo 455782 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B1158047 : Blo 455782 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1387735 : Blo 455782 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B1322347 : Blo 455782 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B6237803 : Blo 455782 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B2600707 : Blo 455782 2600707 := bstep (se 1 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 2600707 = 3901061) B3901061
theorem B1027871 : Blo 455782 1027871 := bstep (se 1 (by rfl) ⟨770903, by rfl⟩ : syracuseStep 1027871 = 1541807) B1541807
theorem B3911723 : Blo 455782 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B1028393 : Blo 455782 1028393 := bstep (se 2 (by rfl) ⟨385647, by rfl⟩ : syracuseStep 1028393 = 771295) B771295
theorem B4174375 : Blo 455782 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B1028663 : Blo 455782 1028663 := bstep (se 1 (by rfl) ⟨771497, by rfl⟩ : syracuseStep 1028663 = 1542995) B1542995
theorem B1323755 : Blo 455782 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B1159991 : Blo 455782 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1029023 : Blo 455782 1029023 := bstep (se 1 (by rfl) ⟨771767, by rfl⟩ : syracuseStep 1029023 = 1543535) B1543535
theorem B1946909 : Blo 455782 1946909 := bstep (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) B730091
theorem B865657 : Blo 455782 865657 := bstep (se 2 (by rfl) ⟨324621, by rfl⟩ : syracuseStep 865657 = 649243) B649243
theorem B1029851 : Blo 455782 1029851 := bstep (se 1 (by rfl) ⟨772388, by rfl⟩ : syracuseStep 1029851 = 1544777) B1544777
theorem B1128179 : Blo 455782 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B2930975 : Blo 455782 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B1161611 : Blo 455782 1161611 := bstep (se 1 (by rfl) ⟨871208, by rfl⟩ : syracuseStep 1161611 = 1742417) B1742417
theorem B3521207 : Blo 455782 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B736057 : Blo 455782 736057 := bstep (se 2 (by rfl) ⟨276021, by rfl⟩ : syracuseStep 736057 = 552043) B552043
theorem B7945147 : Blo 455782 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1032155 : Blo 455782 1032155 := bstep (se 1 (by rfl) ⟨774116, by rfl⟩ : syracuseStep 1032155 = 1548233) B1548233
theorem B1163231 : Blo 455782 1163231 := bstep (se 1 (by rfl) ⟨872423, by rfl⟩ : syracuseStep 1163231 = 1744847) B1744847
theorem B1032335 : Blo 455782 1032335 := bstep (se 1 (by rfl) ⟨774251, by rfl⟩ : syracuseStep 1032335 = 1548503) B1548503
theorem B1032425 : Blo 455782 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B2475215 : Blo 455782 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B1656719 : Blo 455782 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B1034207 : Blo 455782 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B1034423 : Blo 455782 1034423 := bstep (se 1 (by rfl) ⟨775817, by rfl⟩ : syracuseStep 1034423 = 1551635) B1551635
theorem B1952207 : Blo 455782 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B772699 : Blo 455782 772699 := bstep (se 1 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 772699 = 1159049) B1159049
theorem B871391 : Blo 455782 871391 := bstep (se 1 (by rfl) ⟨653543, by rfl⟩ : syracuseStep 871391 = 1307087) B1307087
theorem B1461311 : Blo 455782 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B2608523 : Blo 455782 2608523 := bstep (se 1 (by rfl) ⟨1956392, by rfl⟩ : syracuseStep 2608523 = 3912785) B3912785
theorem B4935205 : Blo 455782 4935205 := bstep (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) B925351
theorem B577135 : Blo 455782 577135 := bstep (se 1 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 577135 = 865703) B865703
theorem B2314007 : Blo 455782 2314007 := bstep (se 1 (by rfl) ⟨1735505, by rfl⟩ : syracuseStep 2314007 = 3471011) B3471011
theorem B31674185 : Blo 455782 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B774191 : Blo 455782 774191 := bstep (se 1 (by rfl) ⟨580643, by rfl⟩ : syracuseStep 774191 = 1161287) B1161287
theorem B1397321 : Blo 455782 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B3920471 : Blo 455782 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B5001851 : Blo 455782 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B578279 : Blo 455782 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B5886857 : Blo 455782 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B13161365 : Blo 455782 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B513247 : Blo 455782 513247 := bstep (se 1 (by rfl) ⟨384935, by rfl⟩ : syracuseStep 513247 = 769871) B769871
theorem B2315627 : Blo 455782 2315627 := bstep (se 1 (by rfl) ⟨1736720, by rfl⟩ : syracuseStep 2315627 = 3473441) B3473441
theorem B1955623 : Blo 455782 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B168450191 : Blo 455782 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B6609113 : Blo 455782 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B580699 : Blo 455782 580699 := bstep (se 1 (by rfl) ⟨435524, by rfl⟩ : syracuseStep 580699 = 871049) B871049
theorem B1956955 : Blo 455782 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B1465769 : Blo 455782 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B1957571 : Blo 455782 1957571 := bstep (se 1 (by rfl) ⟨1468178, by rfl⟩ : syracuseStep 1957571 = 2936357) B2936357
theorem B1335145 : Blo 455782 1335145 := bstep (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) B1001359
theorem B516199 : Blo 455782 516199 := bstep (se 1 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 516199 = 774299) B774299
theorem B975881 : Blo 455782 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B1303771 : Blo 455782 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B1304171 : Blo 455782 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B1960031 : Blo 455782 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B1304819 : Blo 455782 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B1960271 : Blo 455782 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B1305001 : Blo 455782 1305001 := bstep (se 2 (by rfl) ⟨489375, by rfl⟩ : syracuseStep 1305001 = 978751) B978751
theorem B22309451 : Blo 455782 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B4418219 : Blo 455782 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B650855 : Blo 455782 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B2322107 : Blo 455782 2322107 := bstep (se 1 (by rfl) ⟨1741580, by rfl⟩ : syracuseStep 2322107 = 3483161) B3483161
theorem B683903 : Blo 455782 683903 := bstep (se 1 (by rfl) ⟨512927, by rfl⟩ : syracuseStep 683903 = 1025855) B1025855
theorem B1306505 : Blo 455782 1306505 := bstep (se 2 (by rfl) ⟨489939, by rfl⟩ : syracuseStep 1306505 = 979879) B979879
theorem B2977769 : Blo 455782 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B684239 : Blo 455782 684239 := bstep (se 1 (by rfl) ⟨513179, by rfl⟩ : syracuseStep 684239 = 1026359) B1026359
theorem B684359 : Blo 455782 684359 := bstep (se 1 (by rfl) ⟨513269, by rfl⟩ : syracuseStep 684359 = 1026539) B1026539
theorem B684827 : Blo 455782 684827 := bstep (se 1 (by rfl) ⟨513620, by rfl⟩ : syracuseStep 684827 = 1027241) B1027241
theorem B3699593 : Blo 455782 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B685103 : Blo 455782 685103 := bstep (se 1 (by rfl) ⟨513827, by rfl⟩ : syracuseStep 685103 = 1027655) B1027655
theorem B685151 : Blo 455782 685151 := bstep (se 1 (by rfl) ⟨513863, by rfl⟩ : syracuseStep 685151 = 1027727) B1027727
theorem B2323565 : Blo 455782 2323565 := bstep (se 3 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 2323565 = 871337) B871337
theorem B6255755 : Blo 455782 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B685211 : Blo 455782 685211 := bstep (se 1 (by rfl) ⟨513908, by rfl⟩ : syracuseStep 685211 = 1027817) B1027817
theorem B455847 : Blo 455782 455847 := bstep (se 1 (by rfl) ⟨341885, by rfl⟩ : syracuseStep 455847 = 683771) B683771
theorem B685223 : Blo 455782 685223 := bstep (se 1 (by rfl) ⟨513917, by rfl⟩ : syracuseStep 685223 = 1027835) B1027835
theorem B9696449 : Blo 455782 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B1471817 : Blo 455782 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B456295 : Blo 455782 456295 := bstep (se 1 (by rfl) ⟨342221, by rfl⟩ : syracuseStep 456295 = 684443) B684443
theorem B1570537 : Blo 455782 1570537 := bstep (se 2 (by rfl) ⟨588951, by rfl⟩ : syracuseStep 1570537 = 1177903) B1177903
theorem B685895 : Blo 455782 685895 := bstep (se 1 (by rfl) ⟨514421, by rfl⟩ : syracuseStep 685895 = 1028843) B1028843
theorem B1308487 : Blo 455782 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B456575 : Blo 455782 456575 := bstep (se 1 (by rfl) ⟨342431, by rfl⟩ : syracuseStep 456575 = 684863) B684863
theorem B456671 : Blo 455782 456671 := bstep (se 1 (by rfl) ⟨342503, by rfl⟩ : syracuseStep 456671 = 685007) B685007
theorem B456699 : Blo 455782 456699 := bstep (se 1 (by rfl) ⟨342524, by rfl⟩ : syracuseStep 456699 = 685049) B685049
theorem B686075 : Blo 455782 686075 := bstep (se 1 (by rfl) ⟨514556, by rfl⟩ : syracuseStep 686075 = 1029113) B1029113
theorem B456731 : Blo 455782 456731 := bstep (se 1 (by rfl) ⟨342548, by rfl⟩ : syracuseStep 456731 = 685097) B685097
theorem B456751 : Blo 455782 456751 := bstep (se 1 (by rfl) ⟨342563, by rfl⟩ : syracuseStep 456751 = 685127) B685127
theorem B686135 : Blo 455782 686135 := bstep (se 1 (by rfl) ⟨514601, by rfl⟩ : syracuseStep 686135 = 1029203) B1029203
theorem B686201 : Blo 455782 686201 := bstep (se 2 (by rfl) ⟨257325, by rfl⟩ : syracuseStep 686201 = 514651) B514651
theorem B456871 : Blo 455782 456871 := bstep (se 1 (by rfl) ⟨342653, by rfl⟩ : syracuseStep 456871 = 685307) B685307
theorem B686255 : Blo 455782 686255 := bstep (se 1 (by rfl) ⟨514691, by rfl⟩ : syracuseStep 686255 = 1029383) B1029383
theorem B2324699 : Blo 455782 2324699 := bstep (se 1 (by rfl) ⟨1743524, by rfl⟩ : syracuseStep 2324699 = 3487049) B3487049
theorem B686495 : Blo 455782 686495 := bstep (se 1 (by rfl) ⟨514871, by rfl⟩ : syracuseStep 686495 = 1029743) B1029743
theorem B686585 : Blo 455782 686585 := bstep (se 2 (by rfl) ⟨257469, by rfl⟩ : syracuseStep 686585 = 514939) B514939
theorem B457695 : Blo 455782 457695 := bstep (se 1 (by rfl) ⟨343271, by rfl⟩ : syracuseStep 457695 = 686543) B686543
theorem B687071 : Blo 455782 687071 := bstep (se 1 (by rfl) ⟨515303, by rfl⟩ : syracuseStep 687071 = 1030607) B1030607
theorem B457755 : Blo 455782 457755 := bstep (se 1 (by rfl) ⟨343316, by rfl⟩ : syracuseStep 457755 = 686633) B686633
theorem B687131 : Blo 455782 687131 := bstep (se 1 (by rfl) ⟨515348, by rfl⟩ : syracuseStep 687131 = 1030697) B1030697
theorem B457883 : Blo 455782 457883 := bstep (se 1 (by rfl) ⟨343412, by rfl⟩ : syracuseStep 457883 = 686825) B686825
theorem B19004669 : Blo 455782 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B458139 : Blo 455782 458139 := bstep (se 1 (by rfl) ⟨343604, by rfl⟩ : syracuseStep 458139 = 687209) B687209
theorem B687515 : Blo 455782 687515 := bstep (se 1 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 687515 = 1031273) B1031273
theorem B687593 : Blo 455782 687593 := bstep (se 2 (by rfl) ⟨257847, by rfl⟩ : syracuseStep 687593 = 515695) B515695
theorem B458223 : Blo 455782 458223 := bstep (se 1 (by rfl) ⟨343667, by rfl⟩ : syracuseStep 458223 = 687335) B687335
theorem B687599 : Blo 455782 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B687737 : Blo 455782 687737 := bstep (se 2 (by rfl) ⟨257901, by rfl⟩ : syracuseStep 687737 = 515803) B515803
theorem B1736387 : Blo 455782 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B458559 : Blo 455782 458559 := bstep (se 1 (by rfl) ⟨343919, by rfl⟩ : syracuseStep 458559 = 687839) B687839
theorem B687935 : Blo 455782 687935 := bstep (se 1 (by rfl) ⟨515951, by rfl⟩ : syracuseStep 687935 = 1031903) B1031903
theorem B458587 : Blo 455782 458587 := bstep (se 1 (by rfl) ⟨343940, by rfl⟩ : syracuseStep 458587 = 687881) B687881
theorem B687983 : Blo 455782 687983 := bstep (se 1 (by rfl) ⟨515987, by rfl⟩ : syracuseStep 687983 = 1031975) B1031975
theorem B688223 : Blo 455782 688223 := bstep (se 1 (by rfl) ⟨516167, by rfl⟩ : syracuseStep 688223 = 1032335) B1032335
theorem B688265 : Blo 455782 688265 := bstep (se 2 (by rfl) ⟨258099, by rfl⟩ : syracuseStep 688265 = 516199) B516199
theorem B688283 : Blo 455782 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B459111 : Blo 455782 459111 := bstep (se 1 (by rfl) ⟨344333, by rfl⟩ : syracuseStep 459111 = 688667) B688667
theorem B459231 : Blo 455782 459231 := bstep (se 1 (by rfl) ⟨344423, by rfl⟩ : syracuseStep 459231 = 688847) B688847
theorem B459311 : Blo 455782 459311 := bstep (se 1 (by rfl) ⟨344483, by rfl⟩ : syracuseStep 459311 = 688967) B688967
theorem B10584665 : Blo 455782 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B459355 : Blo 455782 459355 := bstep (se 1 (by rfl) ⟨344516, by rfl⟩ : syracuseStep 459355 = 689033) B689033
theorem B2196193 : Blo 455782 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B459519 : Blo 455782 459519 := bstep (se 1 (by rfl) ⟨344639, by rfl⟩ : syracuseStep 459519 = 689279) B689279
theorem B459611 : Blo 455782 459611 := bstep (se 1 (by rfl) ⟨344708, by rfl⟩ : syracuseStep 459611 = 689417) B689417
theorem B689471 : Blo 455782 689471 := bstep (se 1 (by rfl) ⟨517103, by rfl⟩ : syracuseStep 689471 = 1034207) B1034207
theorem B689615 : Blo 455782 689615 := bstep (se 1 (by rfl) ⟨517211, by rfl⟩ : syracuseStep 689615 = 1034423) B1034423
theorem B1738361 : Blo 455782 1738361 := bstep (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) B1303771
theorem B1542077 : Blo 455782 1542077 := bstep (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) B578279
theorem B1542185 : Blo 455782 1542185 := bstep (se 2 (by rfl) ⟨578319, by rfl⟩ : syracuseStep 1542185 = 1156639) B1156639
theorem B1739015 : Blo 455782 1739015 := bstep (se 1 (by rfl) ⟨1304261, by rfl⟩ : syracuseStep 1739015 = 2608523) B2608523
theorem B7047593 : Blo 455782 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B1542671 : Blo 455782 1542671 := bstep (se 1 (by rfl) ⟨1157003, by rfl⟩ : syracuseStep 1542671 = 2314007) B2314007
theorem B25857197 : Blo 455782 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B1740001 : Blo 455782 1740001 := bstep (se 2 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 1740001 = 1305001) B1305001
theorem B462287 : Blo 455782 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B1543751 : Blo 455782 1543751 := bstep (se 1 (by rfl) ⟨1157813, by rfl⟩ : syracuseStep 1543751 = 2315627) B2315627
theorem B112300127 : Blo 455782 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B99359227 : Blo 455782 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B1154209 : Blo 455782 1154209 := bstep (se 2 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 1154209 = 865657) B865657
theorem B1744649 : Blo 455782 1744649 := bstep (se 2 (by rfl) ⟨654243, by rfl⟩ : syracuseStep 1744649 = 1308487) B1308487
theorem B1548071 : Blo 455782 1548071 := bstep (se 1 (by rfl) ⟨1161053, by rfl⟩ : syracuseStep 1548071 = 2322107) B2322107
theorem B2466395 : Blo 455782 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B1549043 : Blo 455782 1549043 := bstep (se 1 (by rfl) ⟨1161782, by rfl⟩ : syracuseStep 1549043 = 2323565) B2323565
theorem B4170503 : Blo 455782 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B10593529 : Blo 455782 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B1549799 : Blo 455782 1549799 := bstep (se 1 (by rfl) ⟨1162349, by rfl⟩ : syracuseStep 1549799 = 2324699) B2324699
theorem B1157591 : Blo 455782 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B1780193 : Blo 455782 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B7940717 : Blo 455782 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B1026899 : Blo 455782 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B1027259 : Blo 455782 1027259 := bstep (se 1 (by rfl) ⟨770444, by rfl⟩ : syracuseStep 1027259 = 1540889) B1540889
theorem B2927825 : Blo 455782 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B1551743 : Blo 455782 1551743 := bstep (se 1 (by rfl) ⟨1163807, by rfl⟩ : syracuseStep 1551743 = 2327615) B2327615
theorem B1650143 : Blo 455782 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B8007497 : Blo 455782 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B1159231 : Blo 455782 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B1028987 : Blo 455782 1028987 := bstep (se 1 (by rfl) ⟨771740, by rfl⟩ : syracuseStep 1028987 = 1543481) B1543481
theorem B21116123 : Blo 455782 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B931547 : Blo 455782 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B2930489 : Blo 455782 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B31700807 : Blo 455782 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B1029959 : Blo 455782 1029959 := bstep (se 1 (by rfl) ⟨772469, by rfl⟩ : syracuseStep 1029959 = 1544939) B1544939
theorem B1030265 : Blo 455782 1030265 := bstep (se 2 (by rfl) ⟨386349, by rfl⟩ : syracuseStep 1030265 = 772699) B772699
theorem B1030319 : Blo 455782 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B1948207 : Blo 455782 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B4700855 : Blo 455782 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B25082567 : Blo 455782 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B4406075 : Blo 455782 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B769351 : Blo 455782 769351 := bstep (se 1 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 769351 = 1154027) B1154027
theorem B769513 : Blo 455782 769513 := bstep (se 2 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 769513 = 577135) B577135
theorem B1162907 : Blo 455782 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1163423 : Blo 455782 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B770539 : Blo 455782 770539 := bstep (se 1 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 770539 = 1155809) B1155809
theorem B869447 : Blo 455782 869447 := bstep (se 1 (by rfl) ⟨652085, by rfl⟩ : syracuseStep 869447 = 1304171) B1304171
theorem B1033307 : Blo 455782 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B1033343 : Blo 455782 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B869879 : Blo 455782 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B772031 : Blo 455782 772031 := bstep (se 1 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 772031 = 1158047) B1158047
theorem B6605185 : Blo 455782 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B2607497 : Blo 455782 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B871003 : Blo 455782 871003 := bstep (se 1 (by rfl) ⟨653252, by rfl⟩ : syracuseStep 871003 = 1306505) B1306505
theorem B2607815 : Blo 455782 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B773327 : Blo 455782 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B1297939 : Blo 455782 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B2609273 : Blo 455782 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B774265 : Blo 455782 774265 := bstep (se 2 (by rfl) ⟨290349, by rfl⟩ : syracuseStep 774265 = 580699) B580699
theorem B1953983 : Blo 455782 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B774407 : Blo 455782 774407 := bstep (se 1 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 774407 = 1161611) B1161611
theorem B2347471 : Blo 455782 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B3461777 : Blo 455782 3461777 := bstep (se 2 (by rfl) ⟨1298166, by rfl⟩ : syracuseStep 3461777 = 2596333) B2596333
theorem B12669779 : Blo 455782 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B775487 : Blo 455782 775487 := bstep (se 1 (by rfl) ⟨581615, by rfl⟩ : syracuseStep 775487 = 1163231) B1163231
theorem B1463923 : Blo 455782 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B2315951 : Blo 455782 2315951 := bstep (se 1 (by rfl) ⟨1736963, by rfl⟩ : syracuseStep 2315951 = 3473927) B3473927
theorem B3758089 : Blo 455782 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B1104479 : Blo 455782 1104479 := bstep (se 1 (by rfl) ⟨828359, by rfl⟩ : syracuseStep 1104479 = 1656719) B1656719
theorem B1301471 : Blo 455782 1301471 := bstep (se 1 (by rfl) ⟨976103, by rfl⟩ : syracuseStep 1301471 = 1952207) B1952207
theorem B580927 : Blo 455782 580927 := bstep (se 1 (by rfl) ⟨435695, by rfl⟩ : syracuseStep 580927 = 871391) B871391
theorem B974207 : Blo 455782 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B1858943 : Blo 455782 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B516127 : Blo 455782 516127 := bstep (se 1 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 516127 = 774191) B774191
theorem B2318543 : Blo 455782 2318543 := bstep (se 1 (by rfl) ⟨1738907, by rfl⟩ : syracuseStep 2318543 = 3477815) B3477815
theorem B6250891 : Blo 455782 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B2613647 : Blo 455782 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B3334567 : Blo 455782 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B3924571 : Blo 455782 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B8774243 : Blo 455782 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B27812555 : Blo 455782 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B3924845 : Blo 455782 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B877871 : Blo 455782 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B1861019 : Blo 455782 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B1861343 : Blo 455782 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B1763129 : Blo 455782 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B14903189 : Blo 455782 14903189 := bstep (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) B698587
theorem B3008477 : Blo 455782 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B1730555 : Blo 455782 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B6580273 : Blo 455782 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B977179 : Blo 455782 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B2648375 : Blo 455782 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B3467609 : Blo 455782 3467609 := bstep (se 2 (by rfl) ⟨1300353, by rfl⟩ : syracuseStep 3467609 = 2600707) B2600707
theorem B1305047 : Blo 455782 1305047 := bstep (se 1 (by rfl) ⟨978785, by rfl⟩ : syracuseStep 1305047 = 1957571) B1957571
theorem B1731239 : Blo 455782 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B551711 : Blo 455782 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B1731527 : Blo 455782 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B650587 : Blo 455782 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B5565833 : Blo 455782 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B11103641 : Blo 455782 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B486847 : Blo 455782 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B683711 : Blo 455782 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B7401253 : Blo 455782 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B1306687 : Blo 455782 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B1306847 : Blo 455782 1306847 := bstep (se 1 (by rfl) ⟨980135, by rfl⟩ : syracuseStep 1306847 = 1960271) B1960271
theorem B684329 : Blo 455782 684329 := bstep (se 2 (by rfl) ⟨256623, by rfl⟩ : syracuseStep 684329 = 513247) B513247
theorem B14872967 : Blo 455782 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B11891123 : Blo 455782 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B2945479 : Blo 455782 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B7434989 : Blo 455782 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B2094049 : Blo 455782 2094049 := bstep (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) B1570537
theorem B4158535 : Blo 455782 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B685247 : Blo 455782 685247 := bstep (se 1 (by rfl) ⟨513935, by rfl⟩ : syracuseStep 685247 = 1027871) B1027871
theorem B455935 : Blo 455782 455935 := bstep (se 1 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 455935 = 683903) B683903
theorem B456159 : Blo 455782 456159 := bstep (se 1 (by rfl) ⟨342119, by rfl⟩ : syracuseStep 456159 = 684239) B684239
theorem B685595 : Blo 455782 685595 := bstep (se 1 (by rfl) ⟨514196, by rfl⟩ : syracuseStep 685595 = 1028393) B1028393
theorem B456239 : Blo 455782 456239 := bstep (se 1 (by rfl) ⟨342179, by rfl⟩ : syracuseStep 456239 = 684359) B684359
theorem B685775 : Blo 455782 685775 := bstep (se 1 (by rfl) ⟨514331, by rfl⟩ : syracuseStep 685775 = 1028663) B1028663
theorem B882503 : Blo 455782 882503 := bstep (se 1 (by rfl) ⟨661877, by rfl⟩ : syracuseStep 882503 = 1323755) B1323755
theorem B456551 : Blo 455782 456551 := bstep (se 1 (by rfl) ⟨342413, by rfl⟩ : syracuseStep 456551 = 684827) B684827
theorem B686015 : Blo 455782 686015 := bstep (se 1 (by rfl) ⟨514511, by rfl⟩ : syracuseStep 686015 = 1029023) B1029023
theorem B456735 : Blo 455782 456735 := bstep (se 1 (by rfl) ⟨342551, by rfl⟩ : syracuseStep 456735 = 685103) B685103
theorem B456767 : Blo 455782 456767 := bstep (se 1 (by rfl) ⟨342575, by rfl⟩ : syracuseStep 456767 = 685151) B685151
theorem B456807 : Blo 455782 456807 := bstep (se 1 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 456807 = 685211) B685211
theorem B456815 : Blo 455782 456815 := bstep (se 1 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 456815 = 685223) B685223
theorem B882857 : Blo 455782 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B981409 : Blo 455782 981409 := bstep (se 2 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 981409 = 736057) B736057
theorem B686567 : Blo 455782 686567 := bstep (se 1 (by rfl) ⟨514925, by rfl⟩ : syracuseStep 686567 = 1029851) B1029851
theorem B457263 : Blo 455782 457263 := bstep (se 1 (by rfl) ⟨342947, by rfl⟩ : syracuseStep 457263 = 685895) B685895
theorem B457383 : Blo 455782 457383 := bstep (se 1 (by rfl) ⟨343037, by rfl⟩ : syracuseStep 457383 = 686075) B686075
theorem B457423 : Blo 455782 457423 := bstep (se 1 (by rfl) ⟨343067, by rfl⟩ : syracuseStep 457423 = 686135) B686135
theorem B457467 : Blo 455782 457467 := bstep (se 1 (by rfl) ⟨343100, by rfl⟩ : syracuseStep 457467 = 686201) B686201
theorem B457503 : Blo 455782 457503 := bstep (se 1 (by rfl) ⟨343127, by rfl⟩ : syracuseStep 457503 = 686255) B686255
theorem B1735613 : Blo 455782 1735613 := bstep (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) B650855
theorem B457663 : Blo 455782 457663 := bstep (se 1 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 457663 = 686495) B686495
theorem B457723 : Blo 455782 457723 := bstep (se 1 (by rfl) ⟨343292, by rfl⟩ : syracuseStep 457723 = 686585) B686585
theorem B458047 : Blo 455782 458047 := bstep (se 1 (by rfl) ⟨343535, by rfl⟩ : syracuseStep 458047 = 687071) B687071
theorem B458087 : Blo 455782 458087 := bstep (se 1 (by rfl) ⟨343565, by rfl⟩ : syracuseStep 458087 = 687131) B687131
theorem B458343 : Blo 455782 458343 := bstep (se 1 (by rfl) ⟨343757, by rfl⟩ : syracuseStep 458343 = 687515) B687515
theorem B458395 : Blo 455782 458395 := bstep (se 1 (by rfl) ⟨343796, by rfl⟩ : syracuseStep 458395 = 687593) B687593
theorem B458399 : Blo 455782 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B458491 : Blo 455782 458491 := bstep (se 1 (by rfl) ⟨343868, by rfl⟩ : syracuseStep 458491 = 687737) B687737
theorem B458623 : Blo 455782 458623 := bstep (se 1 (by rfl) ⟨343967, by rfl⟩ : syracuseStep 458623 = 687935) B687935
theorem B458655 : Blo 455782 458655 := bstep (se 1 (by rfl) ⟨343991, by rfl⟩ : syracuseStep 458655 = 687983) B687983
theorem B688103 : Blo 455782 688103 := bstep (se 1 (by rfl) ⟨516077, by rfl⟩ : syracuseStep 688103 = 1032155) B1032155
theorem B688169 : Blo 455782 688169 := bstep (se 2 (by rfl) ⟨258063, by rfl⟩ : syracuseStep 688169 = 516127) B516127
theorem B458815 : Blo 455782 458815 := bstep (se 1 (by rfl) ⟨344111, by rfl⟩ : syracuseStep 458815 = 688223) B688223
theorem B458843 : Blo 455782 458843 := bstep (se 1 (by rfl) ⟨344132, by rfl⟩ : syracuseStep 458843 = 688265) B688265
theorem B458855 : Blo 455782 458855 := bstep (se 1 (by rfl) ⟨344141, by rfl⟩ : syracuseStep 458855 = 688283) B688283
theorem B688871 : Blo 455782 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B688895 : Blo 455782 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B459647 : Blo 455782 459647 := bstep (se 1 (by rfl) ⟨344735, by rfl⟩ : syracuseStep 459647 = 689471) B689471
theorem B459743 : Blo 455782 459743 := bstep (se 1 (by rfl) ⟨344807, by rfl⟩ : syracuseStep 459743 = 689615) B689615
theorem B1738331 : Blo 455782 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B1738543 : Blo 455782 1738543 := bstep (se 1 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 1738543 = 2607815) B2607815
theorem B17238131 : Blo 455782 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B1739515 : Blo 455782 1739515 := bstep (se 1 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 1739515 = 2609273) B2609273
theorem B1543967 : Blo 455782 1543967 := bstep (se 1 (by rfl) ⟨1157975, by rfl⟩ : syracuseStep 1543967 = 2315951) B2315951
theorem B9868337 : Blo 455782 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B1545641 : Blo 455782 1545641 := bstep (se 2 (by rfl) ⟨579615, by rfl⟩ : syracuseStep 1545641 = 1159231) B1159231
theorem B1742249 : Blo 455782 1742249 := bstep (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) B1306687
theorem B1545695 : Blo 455782 1545695 := bstep (se 1 (by rfl) ⟨1159271, by rfl⟩ : syracuseStep 1545695 = 2318543) B2318543
theorem B1742431 : Blo 455782 1742431 := bstep (se 1 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 1742431 = 2613647) B2613647
theorem B1644263 : Blo 455782 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B9935459 : Blo 455782 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B2792065 : Blo 455782 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B2005651 : Blo 455782 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1153703 : Blo 455782 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B5544713 : Blo 455782 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B1186795 : Blo 455782 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B1154159 : Blo 455782 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B1154351 : Blo 455782 1154351 := bstep (se 1 (by rfl) ⟨865763, by rfl⟩ : syracuseStep 1154351 = 1731527) B1731527
theorem B3710555 : Blo 455782 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B4956659 : Blo 455782 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B7807589 : Blo 455782 7807589 := bstep (se 4 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 7807589 = 1463923) B1463923
theorem B2597609 : Blo 455782 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B4400381 : Blo 455782 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B1025801 : Blo 455782 1025801 := bstep (se 2 (by rfl) ⟨384675, by rfl⟩ : syracuseStep 1025801 = 769351) B769351
theorem B16721711 : Blo 455782 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B1157075 : Blo 455782 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B1026017 : Blo 455782 1026017 := bstep (se 2 (by rfl) ⟨384756, by rfl⟩ : syracuseStep 1026017 = 769513) B769513
theorem B7056443 : Blo 455782 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B8334521 : Blo 455782 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B1027385 : Blo 455782 1027385 := bstep (se 2 (by rfl) ⟨385269, by rfl⟩ : syracuseStep 1027385 = 770539) B770539
theorem B2928257 : Blo 455782 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B1158907 : Blo 455782 1158907 := bstep (se 1 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 1158907 = 1738361) B1738361
theorem B1028051 : Blo 455782 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B1028123 : Blo 455782 1028123 := bstep (se 1 (by rfl) ⟨771092, by rfl⟩ : syracuseStep 1028123 = 1542185) B1542185
theorem B1159343 : Blo 455782 1159343 := bstep (se 1 (by rfl) ⟨869507, by rfl⟩ : syracuseStep 1159343 = 1739015) B1739015
theorem B4698395 : Blo 455782 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B1028447 : Blo 455782 1028447 := bstep (se 1 (by rfl) ⟨771335, by rfl⟩ : syracuseStep 1028447 = 1542671) B1542671
theorem B1029167 : Blo 455782 1029167 := bstep (se 1 (by rfl) ⟨771875, by rfl⟩ : syracuseStep 1029167 = 1543751) B1543751
theorem B2307851 : Blo 455782 2307851 := bstep (se 1 (by rfl) ⟨1730888, by rfl⟩ : syracuseStep 2307851 = 3461777) B3461777
theorem B1161337 : Blo 455782 1161337 := bstep (se 2 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 1161337 = 871003) B871003
theorem B736319 : Blo 455782 736319 := bstep (se 1 (by rfl) ⟨552239, by rfl⟩ : syracuseStep 736319 = 1104479) B1104479
theorem B867449 : Blo 455782 867449 := bstep (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) B650587
theorem B867647 : Blo 455782 867647 := bstep (se 1 (by rfl) ⟨650735, by rfl⟩ : syracuseStep 867647 = 1301471) B1301471
theorem B1163099 : Blo 455782 1163099 := bstep (se 1 (by rfl) ⟨872324, by rfl⟩ : syracuseStep 1163099 = 1744649) B1744649
theorem B1032047 : Blo 455782 1032047 := bstep (se 1 (by rfl) ⟨774035, by rfl⟩ : syracuseStep 1032047 = 1548071) B1548071
theorem B1032353 : Blo 455782 1032353 := bstep (se 2 (by rfl) ⟨387132, by rfl⟩ : syracuseStep 1032353 = 774265) B774265
theorem B5849495 : Blo 455782 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B1032695 : Blo 455782 1032695 := bstep (se 1 (by rfl) ⟨774521, by rfl⟩ : syracuseStep 1032695 = 1549043) B1549043
theorem B3129961 : Blo 455782 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B1033199 : Blo 455782 1033199 := bstep (se 1 (by rfl) ⟨774899, by rfl⟩ : syracuseStep 1033199 = 1549799) B1549799
theorem B2311739 : Blo 455782 2311739 := bstep (se 1 (by rfl) ⟨1733804, by rfl⟩ : syracuseStep 2311739 = 3467609) B3467609
theorem B771727 : Blo 455782 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B870031 : Blo 455782 870031 := bstep (se 1 (by rfl) ⟨652523, by rfl⟩ : syracuseStep 870031 = 1305047) B1305047
theorem B5293811 : Blo 455782 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B1951883 : Blo 455782 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B1034495 : Blo 455782 1034495 := bstep (se 1 (by rfl) ⟨775871, by rfl⟩ : syracuseStep 1034495 = 1551743) B1551743
theorem B871231 : Blo 455782 871231 := bstep (se 1 (by rfl) ⟨653423, by rfl⟩ : syracuseStep 871231 = 1306847) B1306847
theorem B9915311 : Blo 455782 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B14077415 : Blo 455782 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B1953659 : Blo 455782 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B1232765 : Blo 455782 1232765 := bstep (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) B462287
theorem B774569 : Blo 455782 774569 := bstep (se 2 (by rfl) ⟨290463, by rfl⟩ : syracuseStep 774569 = 580927) B580927
theorem B3133903 : Blo 455782 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B2937383 : Blo 455782 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B775271 : Blo 455782 775271 := bstep (se 1 (by rfl) ⟨581453, by rfl⟩ : syracuseStep 775271 = 1162907) B1162907
theorem B775615 : Blo 455782 775615 := bstep (se 1 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 775615 = 1163423) B1163423
theorem B4446089 : Blo 455782 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B579631 : Blo 455782 579631 := bstep (se 1 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 579631 = 869447) B869447
theorem B5232761 : Blo 455782 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B514687 : Blo 455782 514687 := bstep (se 1 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 514687 = 772031) B772031
theorem B515551 : Blo 455782 515551 := bstep (se 1 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 515551 = 773327) B773327
theorem B529915877 : Blo 455782 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B74866751 : Blo 455782 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B8773697 : Blo 455782 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B1302655 : Blo 455782 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B516271 : Blo 455782 516271 := bstep (se 1 (by rfl) ⟨387203, by rfl⟩ : syracuseStep 516271 = 774407) B774407
theorem B1302905 : Blo 455782 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B8806913 : Blo 455782 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B8446519 : Blo 455782 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B516991 : Blo 455782 516991 := bstep (se 1 (by rfl) ⟨387743, by rfl⟩ : syracuseStep 516991 = 775487) B775487
theorem B2319677 : Blo 455782 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B2320001 : Blo 455782 2320001 := bstep (se 2 (by rfl) ⟨870000, by rfl⟩ : syracuseStep 2320001 = 1740001) B1740001
theorem B2484125 : Blo 455782 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B649129 : Blo 455782 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B1730585 : Blo 455782 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B649471 : Blo 455782 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B1239295 : Blo 455782 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B225995285 : Blo 455782 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B2354285 : Blo 455782 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B18541703 : Blo 455782 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B2780335 : Blo 455782 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B2616563 : Blo 455782 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B3927305 : Blo 455782 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B585247 : Blo 455782 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B1240679 : Blo 455782 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B1240895 : Blo 455782 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B1175419 : Blo 455782 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B1765583 : Blo 455782 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B684599 : Blo 455782 684599 := bstep (se 1 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 684599 = 1026899) B1026899
theorem B1471229 : Blo 455782 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B684839 : Blo 455782 684839 := bstep (se 1 (by rfl) ⟨513629, by rfl⟩ : syracuseStep 684839 = 1027259) B1027259
theorem B7402427 : Blo 455782 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B455807 : Blo 455782 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B5338331 : Blo 455782 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B5010785 : Blo 455782 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B456219 : Blo 455782 456219 := bstep (se 1 (by rfl) ⟨342164, by rfl⟩ : syracuseStep 456219 = 684329) B684329
theorem B7927415 : Blo 455782 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B1308545 : Blo 455782 1308545 := bstep (se 2 (by rfl) ⟨490704, by rfl⟩ : syracuseStep 1308545 = 981409) B981409
theorem B685991 : Blo 455782 685991 := bstep (se 1 (by rfl) ⟨514493, by rfl⟩ : syracuseStep 685991 = 1028987) B1028987
theorem B456831 : Blo 455782 456831 := bstep (se 1 (by rfl) ⟨342623, by rfl⟩ : syracuseStep 456831 = 685247) B685247
theorem B457063 : Blo 455782 457063 := bstep (se 1 (by rfl) ⟨342797, by rfl⟩ : syracuseStep 457063 = 685595) B685595
theorem B457183 : Blo 455782 457183 := bstep (se 1 (by rfl) ⟨342887, by rfl⟩ : syracuseStep 457183 = 685775) B685775
theorem B21133871 : Blo 455782 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B686639 : Blo 455782 686639 := bstep (se 1 (by rfl) ⟨514979, by rfl⟩ : syracuseStep 686639 = 1029959) B1029959
theorem B588335 : Blo 455782 588335 := bstep (se 1 (by rfl) ⟨441251, by rfl⟩ : syracuseStep 588335 = 882503) B882503
theorem B457343 : Blo 455782 457343 := bstep (se 1 (by rfl) ⟨343007, by rfl⟩ : syracuseStep 457343 = 686015) B686015
theorem B686843 : Blo 455782 686843 := bstep (se 1 (by rfl) ⟨515132, by rfl⟩ : syracuseStep 686843 = 1030265) B1030265
theorem B686879 : Blo 455782 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B1538945 : Blo 455782 1538945 := bstep (se 2 (by rfl) ⟨577104, by rfl⟩ : syracuseStep 1538945 = 1154209) B1154209
theorem B457711 : Blo 455782 457711 := bstep (se 1 (by rfl) ⟨343283, by rfl⟩ : syracuseStep 457711 = 686567) B686567
theorem B458735 : Blo 455782 458735 := bstep (se 1 (by rfl) ⟨344051, by rfl⟩ : syracuseStep 458735 = 688103) B688103
theorem B458779 : Blo 455782 458779 := bstep (se 1 (by rfl) ⟨344084, by rfl⟩ : syracuseStep 458779 = 688169) B688169
theorem B688235 : Blo 455782 688235 := bstep (se 1 (by rfl) ⟨516176, by rfl⟩ : syracuseStep 688235 = 1032353) B1032353
theorem B1736873 : Blo 455782 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B688361 : Blo 455782 688361 := bstep (se 2 (by rfl) ⟨258135, by rfl⟩ : syracuseStep 688361 = 516271) B516271
theorem B3899663 : Blo 455782 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B688463 : Blo 455782 688463 := bstep (se 1 (by rfl) ⟨516347, by rfl⟩ : syracuseStep 688463 = 1032695) B1032695
theorem B459247 : Blo 455782 459247 := bstep (se 1 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 459247 = 688871) B688871
theorem B459263 : Blo 455782 459263 := bstep (se 1 (by rfl) ⟨344447, by rfl⟩ : syracuseStep 459263 = 688895) B688895
theorem B688799 : Blo 455782 688799 := bstep (se 1 (by rfl) ⟨516599, by rfl⟩ : syracuseStep 688799 = 1033199) B1033199
theorem B3474413 : Blo 455782 3474413 := bstep (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) B1302905
theorem B1541159 : Blo 455782 1541159 := bstep (se 1 (by rfl) ⟨1155869, by rfl⟩ : syracuseStep 1541159 = 2311739) B2311739
theorem B689321 : Blo 455782 689321 := bstep (se 2 (by rfl) ⟨258495, by rfl⟩ : syracuseStep 689321 = 516991) B516991
theorem B689663 : Blo 455782 689663 := bstep (se 1 (by rfl) ⟨517247, by rfl⟩ : syracuseStep 689663 = 1034495) B1034495
theorem B821843 : Blo 455782 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B6623639 : Blo 455782 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B1545209 : Blo 455782 1545209 := bstep (se 2 (by rfl) ⟨579453, by rfl⟩ : syracuseStep 1545209 = 1158907) B1158907
theorem B6329573 : Blo 455782 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B353277251 : Blo 455782 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B49911167 : Blo 455782 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B5871275 : Blo 455782 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B1546451 : Blo 455782 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B1546667 : Blo 455782 1546667 := bstep (se 1 (by rfl) ⟨1160000, by rfl⟩ : syracuseStep 1546667 = 2320001) B2320001
theorem B11147807 : Blo 455782 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B1153723 : Blo 455782 1153723 := bstep (se 1 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 1153723 = 1730585) B1730585
theorem B12361135 : Blo 455782 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B1744375 : Blo 455782 1744375 := bstep (se 1 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 1744375 = 2616563) B2616563
theorem B827119 : Blo 455782 827119 := bstep (se 1 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 827119 = 1240679) B1240679
theorem B827263 : Blo 455782 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B18817181 : Blo 455782 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B1548449 : Blo 455782 1548449 := bstep (se 2 (by rfl) ⟨580668, by rfl⟩ : syracuseStep 1548449 = 1161337) B1161337
theorem B5284943 : Blo 455782 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B1025963 : Blo 455782 1025963 := bstep (se 1 (by rfl) ⟨769472, by rfl⟩ : syracuseStep 1025963 = 1538945) B1538945
theorem B4173281 : Blo 455782 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B1158887 : Blo 455782 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B183873397 : Blo 455782 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B1028969 : Blo 455782 1028969 := bstep (se 2 (by rfl) ⟨385863, by rfl⟩ : syracuseStep 1028969 = 771727) B771727
theorem B1160041 : Blo 455782 1160041 := bstep (se 2 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 1160041 = 870031) B870031
theorem B1029311 : Blo 455782 1029311 := bstep (se 1 (by rfl) ⟨771983, by rfl⟩ : syracuseStep 1029311 = 1543967) B1543967
theorem B865505 : Blo 455782 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B865961 : Blo 455782 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B1652393 : Blo 455782 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B1030427 : Blo 455782 1030427 := bstep (se 1 (by rfl) ⟨772820, by rfl⟩ : syracuseStep 1030427 = 1545641) B1545641
theorem B1161499 : Blo 455782 1161499 := bstep (se 1 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 1161499 = 1742249) B1742249
theorem B1030463 : Blo 455782 1030463 := bstep (se 1 (by rfl) ⟨772847, by rfl⟩ : syracuseStep 1030463 = 1545695) B1545695
theorem B1161641 : Blo 455782 1161641 := bstep (se 2 (by rfl) ⟨435615, by rfl⟩ : syracuseStep 1161641 = 871231) B871231
theorem B1096175 : Blo 455782 1096175 := bstep (se 1 (by rfl) ⟨822131, by rfl⟩ : syracuseStep 1096175 = 1644263) B1644263
theorem B2964059 : Blo 455782 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B3488507 : Blo 455782 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B769135 : Blo 455782 769135 := bstep (se 1 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 769135 = 1153703) B1153703
theorem B769439 : Blo 455782 769439 := bstep (se 1 (by rfl) ⟨577079, by rfl⟩ : syracuseStep 769439 = 1154159) B1154159
theorem B769567 : Blo 455782 769567 := bstep (se 1 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 769567 = 1154351) B1154351
theorem B2473703 : Blo 455782 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B5849131 : Blo 455782 5849131 := bstep (se 1 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 5849131 = 8773697) B8773697
theorem B4178537 : Blo 455782 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2933587 : Blo 455782 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B14828453 : Blo 455782 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B1656083 : Blo 455782 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B771383 : Blo 455782 771383 := bstep (se 1 (by rfl) ⟨578537, by rfl⟩ : syracuseStep 771383 = 1157075) B1157075
theorem B1034153 : Blo 455782 1034153 := bstep (se 2 (by rfl) ⟨387807, by rfl⟩ : syracuseStep 1034153 = 775615) B775615
theorem B5556347 : Blo 455782 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1952171 : Blo 455782 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B772841 : Blo 455782 772841 := bstep (se 2 (by rfl) ⟨289815, by rfl⟩ : syracuseStep 772841 = 579631) B579631
theorem B772895 : Blo 455782 772895 := bstep (se 1 (by rfl) ⟨579671, by rfl⟩ : syracuseStep 772895 = 1159343) B1159343
theorem B3132263 : Blo 455782 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B6278093 : Blo 455782 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B2313197 : Blo 455782 2313197 := bstep (se 3 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 2313197 = 867449) B867449
theorem B4934951 : Blo 455782 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B3558887 : Blo 455782 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B3722753 : Blo 455782 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B2674201 : Blo 455782 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B872363 : Blo 455782 872363 := bstep (se 1 (by rfl) ⟨654272, by rfl⟩ : syracuseStep 872363 = 1308545) B1308545
theorem B37539773 : Blo 455782 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B578431 : Blo 455782 578431 := bstep (se 1 (by rfl) ⟨433823, by rfl⟩ : syracuseStep 578431 = 867647) B867647
theorem B775399 : Blo 455782 775399 := bstep (se 1 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 775399 = 1163099) B1163099
theorem B11262025 : Blo 455782 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B3529207 : Blo 455782 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1301255 : Blo 455782 1301255 := bstep (se 1 (by rfl) ⟨975941, by rfl⟩ : syracuseStep 1301255 = 1951883) B1951883
theorem B6610207 : Blo 455782 6610207 := bstep (se 1 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 6610207 = 9915311) B9915311
theorem B2318057 : Blo 455782 2318057 := bstep (se 2 (by rfl) ⟨869271, by rfl⟩ : syracuseStep 2318057 = 1738543) B1738543
theorem B1302439 : Blo 455782 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B516379 : Blo 455782 516379 := bstep (se 1 (by rfl) ⟨387284, by rfl⟩ : syracuseStep 516379 = 774569) B774569
theorem B1958255 : Blo 455782 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B6578891 : Blo 455782 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B516847 : Blo 455782 516847 := bstep (se 1 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 516847 = 775271) B775271
theorem B2319353 : Blo 455782 2319353 := bstep (se 2 (by rfl) ⟨869757, by rfl⟩ : syracuseStep 2319353 = 1739515) B1739515
theorem B3696475 : Blo 455782 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B780329 : Blo 455782 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1567225 : Blo 455782 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B3304439 : Blo 455782 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B5205059 : Blo 455782 5205059 := bstep (se 1 (by rfl) ⟨3903794, by rfl⟩ : syracuseStep 5205059 = 7807589) B7807589
theorem B1731739 : Blo 455782 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B683867 : Blo 455782 683867 := bstep (se 1 (by rfl) ⟨512900, by rfl⟩ : syracuseStep 683867 = 1025801) B1025801
theorem B684011 : Blo 455782 684011 := bstep (se 1 (by rfl) ⟨513008, by rfl⟩ : syracuseStep 684011 = 1026017) B1026017
theorem B1568893 : Blo 455782 1568893 := bstep (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) B588335
theorem B150663523 : Blo 455782 150663523 := bstep (se 1 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 150663523 = 225995285) B225995285
theorem B2323241 : Blo 455782 2323241 := bstep (se 2 (by rfl) ⟨871215, by rfl⟩ : syracuseStep 2323241 = 1742431) B1742431
theorem B2618203 : Blo 455782 2618203 := bstep (se 1 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 2618203 = 3927305) B3927305
theorem B684923 : Blo 455782 684923 := bstep (se 1 (by rfl) ⟨513692, by rfl⟩ : syracuseStep 684923 = 1027385) B1027385
theorem B685367 : Blo 455782 685367 := bstep (se 1 (by rfl) ⟨514025, by rfl⟩ : syracuseStep 685367 = 1028051) B1028051
theorem B685415 : Blo 455782 685415 := bstep (se 1 (by rfl) ⟨514061, by rfl⟩ : syracuseStep 685415 = 1028123) B1028123
theorem B1177055 : Blo 455782 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B685631 : Blo 455782 685631 := bstep (se 1 (by rfl) ⟨514223, by rfl⟩ : syracuseStep 685631 = 1028447) B1028447
theorem B456399 : Blo 455782 456399 := bstep (se 1 (by rfl) ⟨342299, by rfl⟩ : syracuseStep 456399 = 684599) B684599
theorem B980819 : Blo 455782 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B456559 : Blo 455782 456559 := bstep (se 1 (by rfl) ⟨342419, by rfl⟩ : syracuseStep 456559 = 684839) B684839
theorem B686111 : Blo 455782 686111 := bstep (se 1 (by rfl) ⟨514583, by rfl⟩ : syracuseStep 686111 = 1029167) B1029167
theorem B686249 : Blo 455782 686249 := bstep (se 2 (by rfl) ⟨257343, by rfl⟩ : syracuseStep 686249 = 514687) B514687
theorem B3340523 : Blo 455782 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B1538567 : Blo 455782 1538567 := bstep (se 1 (by rfl) ⟨1153925, by rfl⟩ : syracuseStep 1538567 = 2307851) B2307851
theorem B457327 : Blo 455782 457327 := bstep (se 1 (by rfl) ⟨342995, by rfl⟩ : syracuseStep 457327 = 685991) B685991
theorem B14089247 : Blo 455782 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B457759 : Blo 455782 457759 := bstep (se 1 (by rfl) ⟨343319, by rfl⟩ : syracuseStep 457759 = 686639) B686639
theorem B457895 : Blo 455782 457895 := bstep (se 1 (by rfl) ⟨343421, by rfl⟩ : syracuseStep 457895 = 686843) B686843
theorem B457919 : Blo 455782 457919 := bstep (se 1 (by rfl) ⟨343439, by rfl⟩ : syracuseStep 457919 = 686879) B686879
theorem B687401 : Blo 455782 687401 := bstep (se 2 (by rfl) ⟨257775, by rfl⟩ : syracuseStep 687401 = 515551) B515551
theorem B490879 : Blo 455782 490879 := bstep (se 1 (by rfl) ⟨368159, by rfl⟩ : syracuseStep 490879 = 736319) B736319
theorem B688031 : Blo 455782 688031 := bstep (se 1 (by rfl) ⟨516023, by rfl⟩ : syracuseStep 688031 = 1032047) B1032047
theorem B7798841 : Blo 455782 7798841 := bstep (se 2 (by rfl) ⟨2924565, by rfl⟩ : syracuseStep 7798841 = 5849131) B5849131
theorem B458823 : Blo 455782 458823 := bstep (se 1 (by rfl) ⟨344117, by rfl⟩ : syracuseStep 458823 = 688235) B688235
theorem B458907 : Blo 455782 458907 := bstep (se 1 (by rfl) ⟨344180, by rfl⟩ : syracuseStep 458907 = 688361) B688361
theorem B458975 : Blo 455782 458975 := bstep (se 1 (by rfl) ⟨344231, by rfl⟩ : syracuseStep 458975 = 688463) B688463
theorem B688505 : Blo 455782 688505 := bstep (se 2 (by rfl) ⟨258189, by rfl⟩ : syracuseStep 688505 = 516379) B516379
theorem B2785691 : Blo 455782 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B459199 : Blo 455782 459199 := bstep (se 1 (by rfl) ⟨344399, by rfl⟩ : syracuseStep 459199 = 688799) B688799
theorem B459547 : Blo 455782 459547 := bstep (se 1 (by rfl) ⟨344660, by rfl⟩ : syracuseStep 459547 = 689321) B689321
theorem B689129 : Blo 455782 689129 := bstep (se 2 (by rfl) ⟨258423, by rfl⟩ : syracuseStep 689129 = 516847) B516847
theorem B459775 : Blo 455782 459775 := bstep (se 1 (by rfl) ⟨344831, by rfl⟩ : syracuseStep 459775 = 689663) B689663
theorem B689435 : Blo 455782 689435 := bstep (se 1 (by rfl) ⟨517076, by rfl⟩ : syracuseStep 689435 = 1034153) B1034153
theorem B3704231 : Blo 455782 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B1542131 : Blo 455782 1542131 := bstep (se 1 (by rfl) ⟨1156598, by rfl⟩ : syracuseStep 1542131 = 2313197) B2313197
theorem B1545371 : Blo 455782 1545371 := bstep (se 1 (by rfl) ⟨1159028, by rfl⟩ : syracuseStep 1545371 = 2318057) B2318057
theorem B1546235 : Blo 455782 1546235 := bstep (se 1 (by rfl) ⟨1159676, by rfl⟩ : syracuseStep 1546235 = 2319353) B2319353
theorem B1546721 : Blo 455782 1546721 := bstep (se 2 (by rfl) ⟨580020, by rfl⟩ : syracuseStep 1546721 = 1160041) B1160041
theorem B2202959 : Blo 455782 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B15016033 : Blo 455782 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1548665 : Blo 455782 1548665 := bstep (se 2 (by rfl) ⟨580749, by rfl⟩ : syracuseStep 1548665 = 1161499) B1161499
theorem B1548827 : Blo 455782 1548827 := bstep (se 1 (by rfl) ⟨1161620, by rfl⟩ : syracuseStep 1548827 = 2323241) B2323241
theorem B1025513 : Blo 455782 1025513 := bstep (se 2 (by rfl) ⟨384567, by rfl⟩ : syracuseStep 1025513 = 769135) B769135
theorem B730783 : Blo 455782 730783 := bstep (se 1 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 730783 = 1096175) B1096175
theorem B1025711 : Blo 455782 1025711 := bstep (se 1 (by rfl) ⟨769283, by rfl⟩ : syracuseStep 1025711 = 1538567) B1538567
theorem B1976039 : Blo 455782 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B1026089 : Blo 455782 1026089 := bstep (se 2 (by rfl) ⟨384783, by rfl⟩ : syracuseStep 1026089 = 769567) B769567
theorem B1649135 : Blo 455782 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B1157915 : Blo 455782 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B2599775 : Blo 455782 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B1027439 : Blo 455782 1027439 := bstep (se 1 (by rfl) ⟨770579, by rfl⟩ : syracuseStep 1027439 = 1541159) B1541159
theorem B3911449 : Blo 455782 3911449 := bstep (se 2 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 3911449 = 2933587) B2933587
theorem B3289967 : Blo 455782 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B2372591 : Blo 455782 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B4928633 : Blo 455782 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B2308013 : Blo 455782 2308013 := bstep (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) B865505
theorem B1030139 : Blo 455782 1030139 := bstep (se 1 (by rfl) ⟨772604, by rfl⟩ : syracuseStep 1030139 = 1545209) B1545209
theorem B235518167 : Blo 455782 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B33274111 : Blo 455782 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B3914183 : Blo 455782 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B1030967 : Blo 455782 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B2308985 : Blo 455782 2308985 := bstep (se 2 (by rfl) ⟨865869, by rfl⟩ : syracuseStep 2308985 = 1731739) B1731739
theorem B1031111 : Blo 455782 1031111 := bstep (se 1 (by rfl) ⟨773333, by rfl⟩ : syracuseStep 1031111 = 1546667) B1546667
theorem B867503 : Blo 455782 867503 := bstep (se 1 (by rfl) ⟨650627, by rfl⟩ : syracuseStep 867503 = 1301255) B1301255
theorem B1032299 : Blo 455782 1032299 := bstep (se 1 (by rfl) ⟨774224, by rfl⟩ : syracuseStep 1032299 = 1548449) B1548449
theorem B200884697 : Blo 455782 200884697 := bstep (se 2 (by rfl) ⟨75331761, by rfl⟩ : syracuseStep 200884697 = 150663523) B150663523
theorem B3523295 : Blo 455782 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B3490937 : Blo 455782 3490937 := bstep (se 2 (by rfl) ⟨1309101, by rfl⟩ : syracuseStep 3490937 = 2618203) B2618203
theorem B771241 : Blo 455782 771241 := bstep (se 2 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 771241 = 578431) B578431
theorem B1033865 : Blo 455782 1033865 := bstep (se 2 (by rfl) ⟨387699, by rfl⟩ : syracuseStep 1033865 = 775399) B775399
theorem B772591 : Blo 455782 772591 := bstep (se 1 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 772591 = 1158887) B1158887
theorem B4705609 : Blo 455782 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B577307 : Blo 455782 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B1101595 : Blo 455782 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B774427 : Blo 455782 774427 := bstep (se 1 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 774427 = 1161641) B1161641
theorem B4412069 : Blo 455782 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B9392831 : Blo 455782 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B512959 : Blo 455782 512959 := bstep (se 1 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 512959 = 769439) B769439
theorem B1102825 : Blo 455782 1102825 := bstep (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) B827119
theorem B9885635 : Blo 455782 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B2316275 : Blo 455782 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B514255 : Blo 455782 514255 := bstep (se 1 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 514255 = 771383) B771383
theorem B1301447 : Blo 455782 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B547895 : Blo 455782 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B515227 : Blo 455782 515227 := bstep (se 1 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 515227 = 772841) B772841
theorem B515263 : Blo 455782 515263 := bstep (se 1 (by rfl) ⟨386447, by rfl⟩ : syracuseStep 515263 = 772895) B772895
theorem B2088175 : Blo 455782 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B4185395 : Blo 455782 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B2481835 : Blo 455782 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B581575 : Blo 455782 581575 := bstep (se 1 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 581575 = 872363) B872363
theorem B25026515 : Blo 455782 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B4415759 : Blo 455782 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2089633 : Blo 455782 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B4416221 : Blo 455782 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B4219715 : Blo 455782 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B7431871 : Blo 455782 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B3565601 : Blo 455782 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B245164529 : Blo 455782 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B12544787 : Blo 455782 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B2091857 : Blo 455782 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1305503 : Blo 455782 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B4385927 : Blo 455782 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B8908061 : Blo 455782 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B683975 : Blo 455782 683975 := bstep (se 1 (by rfl) ⟨512981, by rfl⟩ : syracuseStep 683975 = 1025963) B1025963
theorem B520219 : Blo 455782 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B2618021 : Blo 455782 2618021 := bstep (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) B490879
theorem B3470039 : Blo 455782 3470039 := bstep (se 1 (by rfl) ⟨2602529, by rfl⟩ : syracuseStep 3470039 = 5205059) B5205059
theorem B2782187 : Blo 455782 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B455911 : Blo 455782 455911 := bstep (se 1 (by rfl) ⟨341933, by rfl⟩ : syracuseStep 455911 = 683867) B683867
theorem B456007 : Blo 455782 456007 := bstep (se 1 (by rfl) ⟨342005, by rfl⟩ : syracuseStep 456007 = 684011) B684011
theorem B685979 : Blo 455782 685979 := bstep (se 1 (by rfl) ⟨514484, by rfl⟩ : syracuseStep 685979 = 1028969) B1028969
theorem B456615 : Blo 455782 456615 := bstep (se 1 (by rfl) ⟨342461, by rfl⟩ : syracuseStep 456615 = 684923) B684923
theorem B686207 : Blo 455782 686207 := bstep (se 1 (by rfl) ⟨514655, by rfl⟩ : syracuseStep 686207 = 1029311) B1029311
theorem B456911 : Blo 455782 456911 := bstep (se 1 (by rfl) ⟨342683, by rfl⟩ : syracuseStep 456911 = 685367) B685367
theorem B456943 : Blo 455782 456943 := bstep (se 1 (by rfl) ⟨342707, by rfl⟩ : syracuseStep 456943 = 685415) B685415
theorem B1538297 : Blo 455782 1538297 := bstep (se 2 (by rfl) ⟨576861, by rfl⟩ : syracuseStep 1538297 = 1153723) B1153723
theorem B784703 : Blo 455782 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B457087 : Blo 455782 457087 := bstep (se 1 (by rfl) ⟨342815, by rfl⟩ : syracuseStep 457087 = 685631) B685631
theorem B653879 : Blo 455782 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B457407 : Blo 455782 457407 := bstep (se 1 (by rfl) ⟨343055, by rfl⟩ : syracuseStep 457407 = 686111) B686111
theorem B457499 : Blo 455782 457499 := bstep (se 1 (by rfl) ⟨343124, by rfl⟩ : syracuseStep 457499 = 686249) B686249
theorem B686951 : Blo 455782 686951 := bstep (se 1 (by rfl) ⟨515213, by rfl⟩ : syracuseStep 686951 = 1030427) B1030427
theorem B686975 : Blo 455782 686975 := bstep (se 1 (by rfl) ⟨515231, by rfl⟩ : syracuseStep 686975 = 1030463) B1030463
theorem B8813609 : Blo 455782 8813609 := bstep (se 2 (by rfl) ⟨3305103, by rfl⟩ : syracuseStep 8813609 = 6610207) B6610207
theorem B2325671 : Blo 455782 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B16481513 : Blo 455782 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B2325833 : Blo 455782 2325833 := bstep (se 2 (by rfl) ⟨872187, by rfl⟩ : syracuseStep 2325833 = 1744375) B1744375
theorem B458267 : Blo 455782 458267 := bstep (se 1 (by rfl) ⟨343700, by rfl⟩ : syracuseStep 458267 = 687401) B687401
theorem B1736585 : Blo 455782 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B458687 : Blo 455782 458687 := bstep (se 1 (by rfl) ⟨344015, by rfl⟩ : syracuseStep 458687 = 688031) B688031
theorem B688199 : Blo 455782 688199 := bstep (se 1 (by rfl) ⟨516149, by rfl⟩ : syracuseStep 688199 = 1032299) B1032299
theorem B20021377 : Blo 455782 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B459003 : Blo 455782 459003 := bstep (se 1 (by rfl) ⟨344252, by rfl⟩ : syracuseStep 459003 = 688505) B688505
theorem B133923131 : Blo 455782 133923131 := bstep (se 1 (by rfl) ⟨100442348, by rfl⟩ : syracuseStep 133923131 = 200884697) B200884697
theorem B459419 : Blo 455782 459419 := bstep (se 1 (by rfl) ⟨344564, by rfl⟩ : syracuseStep 459419 = 689129) B689129
theorem B2327291 : Blo 455782 2327291 := bstep (se 1 (by rfl) ⟨1745468, by rfl⟩ : syracuseStep 2327291 = 3490937) B3490937
theorem B459623 : Blo 455782 459623 := bstep (se 1 (by rfl) ⟨344717, by rfl⟩ : syracuseStep 459623 = 689435) B689435
theorem B2786177 : Blo 455782 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B689243 : Blo 455782 689243 := bstep (se 1 (by rfl) ⟨516932, by rfl⟩ : syracuseStep 689243 = 1033865) B1033865
theorem B6261887 : Blo 455782 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B6590423 : Blo 455782 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B1544183 : Blo 455782 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B2790263 : Blo 455782 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B5215265 : Blo 455782 5215265 := bstep (se 2 (by rfl) ⟨1955724, by rfl⟩ : syracuseStep 5215265 = 3911449) B3911449
theorem B16684343 : Blo 455782 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B693625 : Blo 455782 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B1317359 : Blo 455782 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1743677 : Blo 455782 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B8363191 : Blo 455782 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B2923951 : Blo 455782 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B1745347 : Blo 455782 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B43950701 : Blo 455782 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B1581727 : Blo 455782 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B3285755 : Blo 455782 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B1025531 : Blo 455782 1025531 := bstep (se 1 (by rfl) ⟨769148, by rfl⟩ : syracuseStep 1025531 = 1538297) B1538297
theorem B5875739 : Blo 455782 5875739 := bstep (se 1 (by rfl) ⟨4406804, by rfl⟩ : syracuseStep 5875739 = 8813609) B8813609
theorem B1550447 : Blo 455782 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B1550555 : Blo 455782 1550555 := bstep (se 1 (by rfl) ⟨1162916, by rfl⟩ : syracuseStep 1550555 = 2325833) B2325833
theorem B1157723 : Blo 455782 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1028087 : Blo 455782 1028087 := bstep (se 1 (by rfl) ⟨771065, by rfl⟩ : syracuseStep 1028087 = 1542131) B1542131
theorem B1028321 : Blo 455782 1028321 := bstep (se 2 (by rfl) ⟨385620, by rfl⟩ : syracuseStep 1028321 = 771241) B771241
theorem B9909161 : Blo 455782 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B1030121 : Blo 455782 1030121 := bstep (se 2 (by rfl) ⟨386295, by rfl⟩ : syracuseStep 1030121 = 772591) B772591
theorem B1030247 : Blo 455782 1030247 := bstep (se 1 (by rfl) ⟨772685, by rfl⟩ : syracuseStep 1030247 = 1545371) B1545371
theorem B9877949 : Blo 455782 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B1030823 : Blo 455782 1030823 := bstep (se 1 (by rfl) ⟨773117, by rfl⟩ : syracuseStep 1030823 = 1546235) B1546235
theorem B1031147 : Blo 455782 1031147 := bstep (se 1 (by rfl) ⟨773360, by rfl⟩ : syracuseStep 1031147 = 1546721) B1546721
theorem B6274145 : Blo 455782 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B5881733 : Blo 455782 5881733 := bstep (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) B1102825
theorem B1032443 : Blo 455782 1032443 := bstep (se 1 (by rfl) ⟨774332, by rfl⟩ : syracuseStep 1032443 = 1548665) B1548665
theorem B1032551 : Blo 455782 1032551 := bstep (se 1 (by rfl) ⟨774413, by rfl⟩ : syracuseStep 1032551 = 1548827) B1548827
theorem B1032569 : Blo 455782 1032569 := bstep (se 2 (by rfl) ⟨387213, by rfl⟩ : syracuseStep 1032569 = 774427) B774427
theorem B2377067 : Blo 455782 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B1099423 : Blo 455782 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B771943 : Blo 455782 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B870335 : Blo 455782 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B1461053 : Blo 455782 1461053 := bstep (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) B547895
theorem B2313359 : Blo 455782 2313359 := bstep (se 1 (by rfl) ⟨1735019, by rfl⟩ : syracuseStep 2313359 = 3470039) B3470039
theorem B1854791 : Blo 455782 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B157012111 : Blo 455782 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B2609455 : Blo 455782 2609455 := bstep (se 1 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 2609455 = 3914183) B3914183
theorem B578335 : Blo 455782 578335 := bstep (se 1 (by rfl) ⟨433751, by rfl⟩ : syracuseStep 578335 = 867503) B867503
theorem B775433 : Blo 455782 775433 := bstep (se 2 (by rfl) ⟨290787, by rfl⟩ : syracuseStep 775433 = 581575) B581575
theorem B5199227 : Blo 455782 5199227 := bstep (se 1 (by rfl) ⟨3899420, by rfl⟩ : syracuseStep 5199227 = 7798841) B7798841
theorem B7428509 : Blo 455782 7428509 := bstep (se 3 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 7428509 = 2785691) B2785691
theorem B9395453 : Blo 455782 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B974377 : Blo 455782 974377 := bstep (se 2 (by rfl) ⟨365391, by rfl⟩ : syracuseStep 974377 = 730783) B730783
theorem B2941379 : Blo 455782 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1468639 : Blo 455782 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B1468793 : Blo 455782 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B2943839 : Blo 455782 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B2944147 : Blo 455782 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B2813143 : Blo 455782 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B683675 : Blo 455782 683675 := bstep (se 1 (by rfl) ⟨512756, by rfl⟩ : syracuseStep 683675 = 1025513) B1025513
theorem B683807 : Blo 455782 683807 := bstep (se 1 (by rfl) ⟨512855, by rfl⟩ : syracuseStep 683807 = 1025711) B1025711
theorem B683945 : Blo 455782 683945 := bstep (se 2 (by rfl) ⟨256479, by rfl⟩ : syracuseStep 683945 = 512959) B512959
theorem B684059 : Blo 455782 684059 := bstep (se 1 (by rfl) ⟨513044, by rfl⟩ : syracuseStep 684059 = 1026089) B1026089
theorem B163443019 : Blo 455782 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B1733183 : Blo 455782 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B684959 : Blo 455782 684959 := bstep (se 1 (by rfl) ⟨513719, by rfl⟩ : syracuseStep 684959 = 1027439) B1027439
theorem B3470525 : Blo 455782 3470525 := bstep (se 3 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 3470525 = 1301447) B1301447
theorem B455983 : Blo 455782 455983 := bstep (se 1 (by rfl) ⟨341987, by rfl⟩ : syracuseStep 455983 = 683975) B683975
theorem B685673 : Blo 455782 685673 := bstep (se 2 (by rfl) ⟨257127, by rfl⟩ : syracuseStep 685673 = 514255) B514255
theorem B44365481 : Blo 455782 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B2193311 : Blo 455782 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B23754829 : Blo 455782 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B22313141 : Blo 455782 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B457319 : Blo 455782 457319 := bstep (se 1 (by rfl) ⟨342989, by rfl⟩ : syracuseStep 457319 = 685979) B685979
theorem B1538675 : Blo 455782 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B686759 : Blo 455782 686759 := bstep (se 1 (by rfl) ⟨515069, by rfl⟩ : syracuseStep 686759 = 1030139) B1030139
theorem B457471 : Blo 455782 457471 := bstep (se 1 (by rfl) ⟨343103, by rfl⟩ : syracuseStep 457471 = 686207) B686207
theorem B686969 : Blo 455782 686969 := bstep (se 2 (by rfl) ⟨257613, by rfl⟩ : syracuseStep 686969 = 515227) B515227
theorem B523135 : Blo 455782 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B687017 : Blo 455782 687017 := bstep (se 2 (by rfl) ⟨257631, by rfl⟩ : syracuseStep 687017 = 515263) B515263
theorem B2784233 : Blo 455782 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B687311 : Blo 455782 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B457967 : Blo 455782 457967 := bstep (se 1 (by rfl) ⟨343475, by rfl⟩ : syracuseStep 457967 = 686951) B686951
theorem B1539323 : Blo 455782 1539323 := bstep (se 1 (by rfl) ⟨1154492, by rfl⟩ : syracuseStep 1539323 = 2308985) B2308985
theorem B457983 : Blo 455782 457983 := bstep (se 1 (by rfl) ⟨343487, by rfl⟩ : syracuseStep 457983 = 686975) B686975
theorem B687407 : Blo 455782 687407 := bstep (se 1 (by rfl) ⟨515555, by rfl⟩ : syracuseStep 687407 = 1031111) B1031111
theorem B1539485 : Blo 455782 1539485 := bstep (se 3 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 1539485 = 577307) B577307
theorem B3309113 : Blo 455782 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B458799 : Blo 455782 458799 := bstep (se 1 (by rfl) ⟨344099, by rfl⟩ : syracuseStep 458799 = 688199) B688199
theorem B688295 : Blo 455782 688295 := bstep (se 1 (by rfl) ⟨516221, by rfl⟩ : syracuseStep 688295 = 1032443) B1032443
theorem B688367 : Blo 455782 688367 := bstep (se 1 (by rfl) ⟨516275, by rfl⟩ : syracuseStep 688367 = 1032551) B1032551
theorem B688379 : Blo 455782 688379 := bstep (se 1 (by rfl) ⟨516284, by rfl⟩ : syracuseStep 688379 = 1032569) B1032569
theorem B2327129 : Blo 455782 2327129 := bstep (se 2 (by rfl) ⟨872673, by rfl⟩ : syracuseStep 2327129 = 1745347) B1745347
theorem B459495 : Blo 455782 459495 := bstep (se 1 (by rfl) ⟨344621, by rfl⟩ : syracuseStep 459495 = 689243) B689243
theorem B1542239 : Blo 455782 1542239 := bstep (se 1 (by rfl) ⟨1156679, by rfl⟩ : syracuseStep 1542239 = 2313359) B2313359
theorem B4393615 : Blo 455782 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B3476843 : Blo 455782 3476843 := bstep (se 1 (by rfl) ⟨2607632, by rfl⟩ : syracuseStep 3476843 = 5215265) B5215265
theorem B4952339 : Blo 455782 4952339 := bstep (se 1 (by rfl) ⟨3714254, by rfl⟩ : syracuseStep 4952339 = 7428509) B7428509
theorem B6263635 : Blo 455782 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B3479273 : Blo 455782 3479273 := bstep (se 2 (by rfl) ⟨1304727, by rfl⟩ : syracuseStep 3479273 = 2609455) B2609455
theorem B29300467 : Blo 455782 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B924833 : Blo 455782 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B1155455 : Blo 455782 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B697513 : Blo 455782 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B11150921 : Blo 455782 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B1025783 : Blo 455782 1025783 := bstep (se 1 (by rfl) ⟨769337, by rfl⟩ : syracuseStep 1025783 = 1538675) B1538675
theorem B1026215 : Blo 455782 1026215 := bstep (se 1 (by rfl) ⟨769661, by rfl⟩ : syracuseStep 1026215 = 1539323) B1539323
theorem B1026323 : Blo 455782 1026323 := bstep (se 1 (by rfl) ⟨769742, by rfl⟩ : syracuseStep 1026323 = 1539485) B1539485
theorem B2206075 : Blo 455782 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B1551527 : Blo 455782 1551527 := bstep (se 1 (by rfl) ⟨1163645, by rfl⟩ : syracuseStep 1551527 = 2327291) B2327291
theorem B837397925 : Blo 455782 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B2108969 : Blo 455782 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B4174591 : Blo 455782 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1029257 : Blo 455782 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B1029455 : Blo 455782 1029455 := bstep (se 1 (by rfl) ⟨772091, by rfl⟩ : syracuseStep 1029455 = 1544183) B1544183
theorem B11122895 : Blo 455782 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B6338845 : Blo 455782 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B3750857 : Blo 455782 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B1162451 : Blo 455782 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B217924025 : Blo 455782 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B3916781 : Blo 455782 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B771113 : Blo 455782 771113 := bstep (se 2 (by rfl) ⟨289167, by rfl⟩ : syracuseStep 771113 = 578335) B578335
theorem B3917159 : Blo 455782 3917159 := bstep (se 1 (by rfl) ⟨2937869, by rfl⟩ : syracuseStep 3917159 = 5875739) B5875739
theorem B1033631 : Blo 455782 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B1033703 : Blo 455782 1033703 := bstep (se 1 (by rfl) ⟨775277, by rfl⟩ : syracuseStep 1033703 = 1550555) B1550555
theorem B771815 : Blo 455782 771815 := bstep (se 1 (by rfl) ⟨578861, by rfl⟩ : syracuseStep 771815 = 1157723) B1157723
theorem B31673105 : Blo 455782 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B6606107 : Blo 455782 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B2313683 : Blo 455782 2313683 := bstep (se 1 (by rfl) ⟨1735262, by rfl⟩ : syracuseStep 2313683 = 3470525) B3470525
theorem B29576987 : Blo 455782 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B1462207 : Blo 455782 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B1856155 : Blo 455782 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B1299169 : Blo 455782 1299169 := bstep (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) B974377
theorem B4182763 : Blo 455782 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B3921155 : Blo 455782 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B26695169 : Blo 455782 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B89282087 : Blo 455782 89282087 := bstep (se 1 (by rfl) ⟨66961565, by rfl⟩ : syracuseStep 89282087 = 133923131) B133923131
theorem B1857451 : Blo 455782 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B580223 : Blo 455782 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B974035 : Blo 455782 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B1236527 : Blo 455782 1236527 := bstep (se 1 (by rfl) ⟨927395, by rfl⟩ : syracuseStep 1236527 = 1854791) B1854791
theorem B1958185 : Blo 455782 1958185 := bstep (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) B1468639
theorem B1860175 : Blo 455782 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B516955 : Blo 455782 516955 := bstep (se 1 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 516955 = 775433) B775433
theorem B3466151 : Blo 455782 3466151 := bstep (se 1 (by rfl) ⟨2599613, by rfl⟩ : syracuseStep 3466151 = 5199227) B5199227
theorem B3925529 : Blo 455782 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B878239 : Blo 455782 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B1960919 : Blo 455782 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B2190503 : Blo 455782 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B683687 : Blo 455782 683687 := bstep (se 1 (by rfl) ⟨512765, by rfl⟩ : syracuseStep 683687 = 1025531) B1025531
theorem B1962559 : Blo 455782 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B455783 : Blo 455782 455783 := bstep (se 1 (by rfl) ⟨341837, by rfl⟩ : syracuseStep 455783 = 683675) B683675
theorem B455871 : Blo 455782 455871 := bstep (se 1 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 455871 = 683807) B683807
theorem B455963 : Blo 455782 455963 := bstep (se 1 (by rfl) ⟨341972, by rfl⟩ : syracuseStep 455963 = 683945) B683945
theorem B685391 : Blo 455782 685391 := bstep (se 1 (by rfl) ⟨514043, by rfl⟩ : syracuseStep 685391 = 1028087) B1028087
theorem B456039 : Blo 455782 456039 := bstep (se 1 (by rfl) ⟨342029, by rfl⟩ : syracuseStep 456039 = 684059) B684059
theorem B685547 : Blo 455782 685547 := bstep (se 1 (by rfl) ⟨514160, by rfl⟩ : syracuseStep 685547 = 1028321) B1028321
theorem B456639 : Blo 455782 456639 := bstep (se 1 (by rfl) ⟨342479, by rfl⟩ : syracuseStep 456639 = 684959) B684959
theorem B5863589 : Blo 455782 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B457115 : Blo 455782 457115 := bstep (se 1 (by rfl) ⟨342836, by rfl⟩ : syracuseStep 457115 = 685673) B685673
theorem B686747 : Blo 455782 686747 := bstep (se 1 (by rfl) ⟨515060, by rfl⟩ : syracuseStep 686747 = 1030121) B1030121
theorem B686831 : Blo 455782 686831 := bstep (se 1 (by rfl) ⟨515123, by rfl⟩ : syracuseStep 686831 = 1030247) B1030247
theorem B14875427 : Blo 455782 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B6585299 : Blo 455782 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B457839 : Blo 455782 457839 := bstep (se 1 (by rfl) ⟨343379, by rfl⟩ : syracuseStep 457839 = 686759) B686759
theorem B687215 : Blo 455782 687215 := bstep (se 1 (by rfl) ⟨515411, by rfl⟩ : syracuseStep 687215 = 1030823) B1030823
theorem B3898601 : Blo 455782 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B457979 : Blo 455782 457979 := bstep (se 1 (by rfl) ⟨343484, by rfl⟩ : syracuseStep 457979 = 686969) B686969
theorem B458011 : Blo 455782 458011 := bstep (se 1 (by rfl) ⟨343508, by rfl⟩ : syracuseStep 458011 = 687017) B687017
theorem B687431 : Blo 455782 687431 := bstep (se 1 (by rfl) ⟨515573, by rfl⟩ : syracuseStep 687431 = 1031147) B1031147
theorem B458207 : Blo 455782 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B458271 : Blo 455782 458271 := bstep (se 1 (by rfl) ⟨343703, by rfl⟩ : syracuseStep 458271 = 687407) B687407
theorem B458863 : Blo 455782 458863 := bstep (se 1 (by rfl) ⟨344147, by rfl⟩ : syracuseStep 458863 = 688295) B688295
theorem B458911 : Blo 455782 458911 := bstep (se 1 (by rfl) ⟨344183, by rfl⟩ : syracuseStep 458911 = 688367) B688367
theorem B458919 : Blo 455782 458919 := bstep (se 1 (by rfl) ⟨344189, by rfl⟩ : syracuseStep 458919 = 688379) B688379
theorem B689087 : Blo 455782 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B689135 : Blo 455782 689135 := bstep (se 1 (by rfl) ⟨516851, by rfl⟩ : syracuseStep 689135 = 1033703) B1033703
theorem B689273 : Blo 455782 689273 := bstep (se 2 (by rfl) ⟨258477, by rfl⟩ : syracuseStep 689273 = 516955) B516955
theorem B1542455 : Blo 455782 1542455 := bstep (se 1 (by rfl) ⟨1156841, by rfl⟩ : syracuseStep 1542455 = 2313683) B2313683
theorem B17796779 : Blo 455782 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B824351 : Blo 455782 824351 := bstep (se 1 (by rfl) ⟨618263, by rfl⟩ : syracuseStep 824351 = 1236527) B1236527
theorem B5577017 : Blo 455782 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1547261 : Blo 455782 1547261 := bstep (se 3 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 1547261 = 580223) B580223
theorem B39067289 : Blo 455782 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B5841341 : Blo 455782 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B3909059 : Blo 455782 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B7415263 : Blo 455782 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B2500571 : Blo 455782 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B2599067 : Blo 455782 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B1551419 : Blo 455782 1551419 := bstep (se 1 (by rfl) ⟨1163564, by rfl⟩ : syracuseStep 1551419 = 2327129) B2327129
theorem B1028159 : Blo 455782 1028159 := bstep (se 1 (by rfl) ⟨771119, by rfl⟩ : syracuseStep 1028159 = 1542239) B1542239
theorem B930017 : Blo 455782 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B21115403 : Blo 455782 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B4404071 : Blo 455782 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B59521391 : Blo 455782 59521391 := bstep (se 1 (by rfl) ⟨44641043, by rfl⟩ : syracuseStep 59521391 = 89282087) B89282087
theorem B1949609 : Blo 455782 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B770303 : Blo 455782 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B2310767 : Blo 455782 2310767 := bstep (se 1 (by rfl) ⟨1733075, by rfl⟩ : syracuseStep 2310767 = 3466151) B3466151
theorem B2474873 : Blo 455782 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B5194853 : Blo 455782 5194853 := bstep (se 4 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 5194853 = 974035) B974035
theorem B1034351 : Blo 455782 1034351 := bstep (se 1 (by rfl) ⟨775763, by rfl⟩ : syracuseStep 1034351 = 1551527) B1551527
theorem B2476601 : Blo 455782 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B9916951 : Blo 455782 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B774967 : Blo 455782 774967 := bstep (se 1 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 774967 = 1162451) B1162451
theorem B2610913 : Blo 455782 2610913 := bstep (se 2 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 2610913 = 1958185) B1958185
theorem B2611187 : Blo 455782 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B514075 : Blo 455782 514075 := bstep (se 1 (by rfl) ⟨385556, by rfl⟩ : syracuseStep 514075 = 771113) B771113
theorem B2480233 : Blo 455782 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B2611439 : Blo 455782 2611439 := bstep (se 1 (by rfl) ⟨1958579, by rfl⟩ : syracuseStep 2611439 = 3917159) B3917159
theorem B514543 : Blo 455782 514543 := bstep (se 1 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 514543 = 771815) B771815
theorem B1170985 : Blo 455782 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B2317895 : Blo 455782 2317895 := bstep (se 1 (by rfl) ⟨1738421, by rfl⟩ : syracuseStep 2317895 = 3476843) B3476843
theorem B19717991 : Blo 455782 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B3301559 : Blo 455782 3301559 := bstep (se 1 (by rfl) ⟨2476169, by rfl⟩ : syracuseStep 3301559 = 4952339) B4952339
theorem B2941433 : Blo 455782 2941433 := bstep (se 2 (by rfl) ⟨1103037, by rfl⟩ : syracuseStep 2941433 = 2206075) B2206075
theorem B2614103 : Blo 455782 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B5858153 : Blo 455782 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B2319515 : Blo 455782 2319515 := bstep (se 1 (by rfl) ⟨1739636, by rfl⟩ : syracuseStep 2319515 = 3479273) B3479273
theorem B2324522933 : Blo 455782 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B616555 : Blo 455782 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B2616745 : Blo 455782 2616745 := bstep (se 2 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 2616745 = 1962559) B1962559
theorem B1732225 : Blo 455782 1732225 := bstep (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) B1299169
theorem B5566121 : Blo 455782 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B2617019 : Blo 455782 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B7433947 : Blo 455782 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B8351513 : Blo 455782 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B683855 : Blo 455782 683855 := bstep (se 1 (by rfl) ⟨512891, by rfl⟩ : syracuseStep 683855 = 1025783) B1025783
theorem B684143 : Blo 455782 684143 := bstep (se 1 (by rfl) ⟨513107, by rfl⟩ : syracuseStep 684143 = 1026215) B1026215
theorem B684215 : Blo 455782 684215 := bstep (se 1 (by rfl) ⟨513161, by rfl⟩ : syracuseStep 684215 = 1026323) B1026323
theorem B1307279 : Blo 455782 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B558265283 : Blo 455782 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B1405979 : Blo 455782 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B455791 : Blo 455782 455791 := bstep (se 1 (by rfl) ⟨341843, by rfl⟩ : syracuseStep 455791 = 683687) B683687
theorem B8451793 : Blo 455782 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B686171 : Blo 455782 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B456927 : Blo 455782 456927 := bstep (se 1 (by rfl) ⟨342695, by rfl⟩ : syracuseStep 456927 = 685391) B685391
theorem B686303 : Blo 455782 686303 := bstep (se 1 (by rfl) ⟨514727, by rfl⟩ : syracuseStep 686303 = 1029455) B1029455
theorem B457031 : Blo 455782 457031 := bstep (se 1 (by rfl) ⟨342773, by rfl⟩ : syracuseStep 457031 = 685547) B685547
theorem B457831 : Blo 455782 457831 := bstep (se 1 (by rfl) ⟨343373, by rfl⟩ : syracuseStep 457831 = 686747) B686747
theorem B457887 : Blo 455782 457887 := bstep (se 1 (by rfl) ⟨343415, by rfl⟩ : syracuseStep 457887 = 686831) B686831
theorem B4390199 : Blo 455782 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B458143 : Blo 455782 458143 := bstep (se 1 (by rfl) ⟨343607, by rfl⟩ : syracuseStep 458143 = 687215) B687215
theorem B458287 : Blo 455782 458287 := bstep (se 1 (by rfl) ⟨343715, by rfl⟩ : syracuseStep 458287 = 687431) B687431
theorem B1540511 : Blo 455782 1540511 := bstep (se 1 (by rfl) ⟨1155383, by rfl⟩ : syracuseStep 1540511 = 2310767) B2310767
theorem B459391 : Blo 455782 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B459423 : Blo 455782 459423 := bstep (se 1 (by rfl) ⟨344567, by rfl⟩ : syracuseStep 459423 = 689135) B689135
theorem B459515 : Blo 455782 459515 := bstep (se 1 (by rfl) ⟨344636, by rfl⟩ : syracuseStep 459515 = 689273) B689273
theorem B689567 : Blo 455782 689567 := bstep (se 1 (by rfl) ⟨517175, by rfl⟩ : syracuseStep 689567 = 1034351) B1034351
theorem B11864519 : Blo 455782 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B2198269 : Blo 455782 2198269 := bstep (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) B824351
theorem B822073 : Blo 455782 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B1740791 : Blo 455782 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B1740959 : Blo 455782 1740959 := bstep (se 1 (by rfl) ⟨1305719, by rfl⟩ : syracuseStep 1740959 = 2611439) B2611439
theorem B1545263 : Blo 455782 1545263 := bstep (se 1 (by rfl) ⟨1158947, by rfl⟩ : syracuseStep 1545263 = 2317895) B2317895
theorem B13145327 : Blo 455782 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B2201039 : Blo 455782 2201039 := bstep (se 1 (by rfl) ⟨1650779, by rfl⟩ : syracuseStep 2201039 = 3301559) B3301559
theorem B1742735 : Blo 455782 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B3905435 : Blo 455782 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B1546343 : Blo 455782 1546343 := bstep (se 1 (by rfl) ⟨1159757, by rfl⟩ : syracuseStep 1546343 = 2319515) B2319515
theorem B3481217 : Blo 455782 3481217 := bstep (se 2 (by rfl) ⟨1305456, by rfl⟩ : syracuseStep 3481217 = 2610913) B2610913
theorem B3710747 : Blo 455782 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B1744679 : Blo 455782 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B2926799 : Blo 455782 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B1649915 : Blo 455782 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B1028303 : Blo 455782 1028303 := bstep (se 1 (by rfl) ⟨771227, by rfl⟩ : syracuseStep 1028303 = 1542455) B1542455
theorem B1651067 : Blo 455782 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B3486077 : Blo 455782 3486077 := bstep (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) B1307279
theorem B11744189 : Blo 455782 11744189 := bstep (se 3 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 11744189 = 4404071) B4404071
theorem B3488993 : Blo 455782 3488993 := bstep (se 2 (by rfl) ⟨1308372, by rfl⟩ : syracuseStep 3488993 = 2616745) B2616745
theorem B1031507 : Blo 455782 1031507 := bstep (se 1 (by rfl) ⟨773630, by rfl⟩ : syracuseStep 1031507 = 1547261) B1547261
theorem B2309633 : Blo 455782 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B9911929 : Blo 455782 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B13222601 : Blo 455782 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B2606039 : Blo 455782 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B1033289 : Blo 455782 1033289 := bstep (se 2 (by rfl) ⟨387483, by rfl⟩ : syracuseStep 1033289 = 774967) B774967
theorem B1549681955 : Blo 455782 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B1034279 : Blo 455782 1034279 := bstep (se 1 (by rfl) ⟨775709, by rfl⟩ : syracuseStep 1034279 = 1551419) B1551419
theorem B14076935 : Blo 455782 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B937319 : Blo 455782 937319 := bstep (se 1 (by rfl) ⟨702989, by rfl⟩ : syracuseStep 937319 = 1405979) B1405979
theorem B1561313 : Blo 455782 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B1299739 : Blo 455782 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B513535 : Blo 455782 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B3463235 : Blo 455782 3463235 := bstep (se 1 (by rfl) ⟨2597426, by rfl⟩ : syracuseStep 3463235 = 5194853) B5194853
theorem B9887017 : Blo 455782 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B26044859 : Blo 455782 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B3894227 : Blo 455782 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B1960955 : Blo 455782 1960955 := bstep (se 1 (by rfl) ⟨1470716, by rfl⟩ : syracuseStep 1960955 = 2941433) B2941433
theorem B14872045 : Blo 455782 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B1667047 : Blo 455782 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B1732711 : Blo 455782 1732711 := bstep (se 1 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 1732711 = 2599067) B2599067
theorem B11269057 : Blo 455782 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B5567675 : Blo 455782 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B455903 : Blo 455782 455903 := bstep (se 1 (by rfl) ⟨341927, by rfl⟩ : syracuseStep 455903 = 683855) B683855
theorem B685433 : Blo 455782 685433 := bstep (se 2 (by rfl) ⟨257037, by rfl⟩ : syracuseStep 685433 = 514075) B514075
theorem B685439 : Blo 455782 685439 := bstep (se 1 (by rfl) ⟨514079, by rfl⟩ : syracuseStep 685439 = 1028159) B1028159
theorem B456095 : Blo 455782 456095 := bstep (se 1 (by rfl) ⟨342071, by rfl⟩ : syracuseStep 456095 = 684143) B684143
theorem B456143 : Blo 455782 456143 := bstep (se 1 (by rfl) ⟨342107, by rfl⟩ : syracuseStep 456143 = 684215) B684215
theorem B3306977 : Blo 455782 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B620011 : Blo 455782 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B372176855 : Blo 455782 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B686057 : Blo 455782 686057 := bstep (se 2 (by rfl) ⟨257271, by rfl⟩ : syracuseStep 686057 = 514543) B514543
theorem B457447 : Blo 455782 457447 := bstep (se 1 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 457447 = 686171) B686171
theorem B457535 : Blo 455782 457535 := bstep (se 1 (by rfl) ⟨343151, by rfl⟩ : syracuseStep 457535 = 686303) B686303
theorem B39680927 : Blo 455782 39680927 := bstep (se 1 (by rfl) ⟨29760695, by rfl⟩ : syracuseStep 39680927 = 59521391) B59521391
theorem B8815067 : Blo 455782 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B1737359 : Blo 455782 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B688859 : Blo 455782 688859 := bstep (se 1 (by rfl) ⟨516644, by rfl⟩ : syracuseStep 688859 = 1033289) B1033289
theorem B459711 : Blo 455782 459711 := bstep (se 1 (by rfl) ⟨344783, by rfl⟩ : syracuseStep 459711 = 689567) B689567
theorem B689519 : Blo 455782 689519 := bstep (se 1 (by rfl) ⟨517139, by rfl⟩ : syracuseStep 689519 = 1034279) B1034279
theorem B4163501 : Blo 455782 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B14847133 : Blo 455782 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B19829393 : Blo 455782 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B2596151 : Blo 455782 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B826681 : Blo 455782 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B2499517 : Blo 455782 2499517 := bstep (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) B937319
theorem B2204651 : Blo 455782 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B13182689 : Blo 455782 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B26453951 : Blo 455782 26453951 := bstep (se 1 (by rfl) ⟨19840463, by rfl⟩ : syracuseStep 26453951 = 39680927) B39680927
theorem B13215905 : Blo 455782 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B1027007 : Blo 455782 1027007 := bstep (se 1 (by rfl) ⟨770255, by rfl⟩ : syracuseStep 1027007 = 1540511) B1540511
theorem B1033121303 : Blo 455782 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B7909679 : Blo 455782 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B9384623 : Blo 455782 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B1160527 : Blo 455782 1160527 := bstep (se 1 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 1160527 = 1740791) B1740791
theorem B1160639 : Blo 455782 1160639 := bstep (se 1 (by rfl) ⟨870479, by rfl⟩ : syracuseStep 1160639 = 1740959) B1740959
theorem B1030175 : Blo 455782 1030175 := bstep (se 1 (by rfl) ⟨772631, by rfl⟩ : syracuseStep 1030175 = 1545263) B1545263
theorem B8763551 : Blo 455782 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B2931025 : Blo 455782 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B1096097 : Blo 455782 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B1161823 : Blo 455782 1161823 := bstep (se 1 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 1161823 = 1742735) B1742735
theorem B2603623 : Blo 455782 2603623 := bstep (se 1 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 2603623 = 3905435) B3905435
theorem B2308823 : Blo 455782 2308823 := bstep (se 1 (by rfl) ⟨1731617, by rfl⟩ : syracuseStep 2308823 = 3463235) B3463235
theorem B1030895 : Blo 455782 1030895 := bstep (se 1 (by rfl) ⟨773171, by rfl⟩ : syracuseStep 1030895 = 1546343) B1546343
theorem B2473831 : Blo 455782 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B1163119 : Blo 455782 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B2310281 : Blo 455782 2310281 := bstep (se 2 (by rfl) ⟨866355, by rfl⟩ : syracuseStep 2310281 = 1732711) B1732711
theorem B69452957 : Blo 455782 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B15025409 : Blo 455782 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B1951199 : Blo 455782 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B1099943 : Blo 455782 1099943 := bstep (se 1 (by rfl) ⟨824957, by rfl⟩ : syracuseStep 1099943 = 1649915) B1649915
theorem B1100711 : Blo 455782 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B1467359 : Blo 455782 1467359 := bstep (se 1 (by rfl) ⟨1100519, by rfl⟩ : syracuseStep 1467359 = 2201039) B2201039
theorem B2320811 : Blo 455782 2320811 := bstep (se 1 (by rfl) ⟨1740608, by rfl⟩ : syracuseStep 2320811 = 3481217) B3481217
theorem B2222729 : Blo 455782 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B1732985 : Blo 455782 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B1307303 : Blo 455782 1307303 := bstep (se 1 (by rfl) ⟨980477, by rfl⟩ : syracuseStep 1307303 = 1960955) B1960955
theorem B684713 : Blo 455782 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B685535 : Blo 455782 685535 := bstep (se 1 (by rfl) ⟨514151, by rfl⟩ : syracuseStep 685535 = 1028303) B1028303
theorem B2324051 : Blo 455782 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B7829459 : Blo 455782 7829459 := bstep (se 1 (by rfl) ⟨5872094, by rfl⟩ : syracuseStep 7829459 = 11744189) B11744189
theorem B456955 : Blo 455782 456955 := bstep (se 1 (by rfl) ⟨342716, by rfl⟩ : syracuseStep 456955 = 685433) B685433
theorem B456959 : Blo 455782 456959 := bstep (se 1 (by rfl) ⟨342719, by rfl⟩ : syracuseStep 456959 = 685439) B685439
theorem B248117903 : Blo 455782 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B457371 : Blo 455782 457371 := bstep (se 1 (by rfl) ⟨343028, by rfl⟩ : syracuseStep 457371 = 686057) B686057
theorem B2325995 : Blo 455782 2325995 := bstep (se 1 (by rfl) ⟨1744496, by rfl⟩ : syracuseStep 2325995 = 3488993) B3488993
theorem B687671 : Blo 455782 687671 := bstep (se 1 (by rfl) ⟨515753, by rfl⟩ : syracuseStep 687671 = 1031507) B1031507
theorem B1539755 : Blo 455782 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B1540187 : Blo 455782 1540187 := bstep (se 1 (by rfl) ⟨1155140, by rfl⟩ : syracuseStep 1540187 = 2310281) B2310281
theorem B459239 : Blo 455782 459239 := bstep (se 1 (by rfl) ⟨344429, by rfl⟩ : syracuseStep 459239 = 688859) B688859
theorem B46301971 : Blo 455782 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B459679 : Blo 455782 459679 := bstep (se 1 (by rfl) ⟨344759, by rfl⟩ : syracuseStep 459679 = 689519) B689519
theorem B19796177 : Blo 455782 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B8788459 : Blo 455782 8788459 := bstep (se 1 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 8788459 = 13182689) B13182689
theorem B17635967 : Blo 455782 17635967 := bstep (se 1 (by rfl) ⟨13226975, by rfl⟩ : syracuseStep 17635967 = 26453951) B26453951
theorem B1547207 : Blo 455782 1547207 := bstep (se 1 (by rfl) ⟨1160405, by rfl⟩ : syracuseStep 1547207 = 2320811) B2320811
theorem B1481819 : Blo 455782 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B1547369 : Blo 455782 1547369 := bstep (se 2 (by rfl) ⟨580263, by rfl⟩ : syracuseStep 1547369 = 1160527) B1160527
theorem B1155323 : Blo 455782 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B3908033 : Blo 455782 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B1549097 : Blo 455782 1549097 := bstep (se 2 (by rfl) ⟨580911, by rfl⟩ : syracuseStep 1549097 = 1161823) B1161823
theorem B1549367 : Blo 455782 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B5219639 : Blo 455782 5219639 := bstep (se 1 (by rfl) ⟨3914729, by rfl⟩ : syracuseStep 5219639 = 7829459) B7829459
theorem B5842367 : Blo 455782 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B1550663 : Blo 455782 1550663 := bstep (se 1 (by rfl) ⟨1162997, by rfl⟩ : syracuseStep 1550663 = 2325995) B2325995
theorem B1026503 : Blo 455782 1026503 := bstep (se 1 (by rfl) ⟨769877, by rfl⟩ : syracuseStep 1026503 = 1539755) B1539755
theorem B1550825 : Blo 455782 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B5876711 : Blo 455782 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B1158239 : Blo 455782 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B733295 : Blo 455782 733295 := bstep (se 1 (by rfl) ⟨549971, by rfl⟩ : syracuseStep 733295 = 1099943) B1099943
theorem B733807 : Blo 455782 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B13219595 : Blo 455782 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B871535 : Blo 455782 871535 := bstep (se 1 (by rfl) ⟨653651, by rfl⟩ : syracuseStep 871535 = 1307303) B1307303
theorem B773759 : Blo 455782 773759 := bstep (se 1 (by rfl) ⟨580319, by rfl⟩ : syracuseStep 773759 = 1160639) B1160639
theorem B1102241 : Blo 455782 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B3298441 : Blo 455782 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B10016939 : Blo 455782 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1300799 : Blo 455782 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B2775667 : Blo 455782 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B11691701 : Blo 455782 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B1730767 : Blo 455782 1730767 := bstep (se 1 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 1730767 = 2596151) B2596151
theorem B13330757 : Blo 455782 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B978239 : Blo 455782 978239 := bstep (se 1 (by rfl) ⟨733679, by rfl⟩ : syracuseStep 978239 = 1467359) B1467359
theorem B1469767 : Blo 455782 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B8810603 : Blo 455782 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B684671 : Blo 455782 684671 := bstep (se 1 (by rfl) ⟨513503, by rfl⟩ : syracuseStep 684671 = 1027007) B1027007
theorem B688747535 : Blo 455782 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B5273119 : Blo 455782 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B456475 : Blo 455782 456475 := bstep (se 1 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 456475 = 684713) B684713
theorem B6256415 : Blo 455782 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B3471497 : Blo 455782 3471497 := bstep (se 2 (by rfl) ⟨1301811, by rfl⟩ : syracuseStep 3471497 = 2603623) B2603623
theorem B457023 : Blo 455782 457023 := bstep (se 1 (by rfl) ⟨342767, by rfl⟩ : syracuseStep 457023 = 685535) B685535
theorem B686783 : Blo 455782 686783 := bstep (se 1 (by rfl) ⟨515087, by rfl⟩ : syracuseStep 686783 = 1030175) B1030175
theorem B165411935 : Blo 455782 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B1539215 : Blo 455782 1539215 := bstep (se 1 (by rfl) ⟨1154411, by rfl⟩ : syracuseStep 1539215 = 2308823) B2308823
theorem B687263 : Blo 455782 687263 := bstep (se 1 (by rfl) ⟨515447, by rfl⟩ : syracuseStep 687263 = 1030895) B1030895
theorem B458447 : Blo 455782 458447 := bstep (se 1 (by rfl) ⟨343835, by rfl⟩ : syracuseStep 458447 = 687671) B687671
theorem B61735961 : Blo 455782 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B3479759 : Blo 455782 3479759 := bstep (se 1 (by rfl) ⟨2609819, by rfl⟩ : syracuseStep 3479759 = 5219639) B5219639
theorem B4397921 : Blo 455782 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B8887171 : Blo 455782 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B5873735 : Blo 455782 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B28123301 : Blo 455782 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4170943 : Blo 455782 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B110274623 : Blo 455782 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B1026143 : Blo 455782 1026143 := bstep (se 1 (by rfl) ⟨769607, by rfl⟩ : syracuseStep 1026143 = 1539215) B1539215
theorem B1026791 : Blo 455782 1026791 := bstep (se 1 (by rfl) ⟨770093, by rfl⟩ : syracuseStep 1026791 = 1540187) B1540187
theorem B2307689 : Blo 455782 2307689 := bstep (se 2 (by rfl) ⟨865383, by rfl⟩ : syracuseStep 2307689 = 1730767) B1730767
theorem B734827 : Blo 455782 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B867199 : Blo 455782 867199 := bstep (se 1 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 867199 = 1300799) B1300799
theorem B1031471 : Blo 455782 1031471 := bstep (se 1 (by rfl) ⟨773603, by rfl⟩ : syracuseStep 1031471 = 1547207) B1547207
theorem B1031579 : Blo 455782 1031579 := bstep (se 1 (by rfl) ⟨773684, by rfl⟩ : syracuseStep 1031579 = 1547369) B1547369
theorem B770215 : Blo 455782 770215 := bstep (se 1 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 770215 = 1155323) B1155323
theorem B2605355 : Blo 455782 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B1032731 : Blo 455782 1032731 := bstep (se 1 (by rfl) ⟨774548, by rfl⟩ : syracuseStep 1032731 = 1549097) B1549097
theorem B1032911 : Blo 455782 1032911 := bstep (se 1 (by rfl) ⟨774683, by rfl⟩ : syracuseStep 1032911 = 1549367) B1549367
theorem B1033775 : Blo 455782 1033775 := bstep (se 1 (by rfl) ⟨775331, by rfl⟩ : syracuseStep 1033775 = 1550663) B1550663
theorem B1033883 : Blo 455782 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B3917807 : Blo 455782 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B772159 : Blo 455782 772159 := bstep (se 1 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 772159 = 1158239) B1158239
theorem B3951517 : Blo 455782 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B11717945 : Blo 455782 11717945 := bstep (se 2 (by rfl) ⟨4394229, by rfl⟩ : syracuseStep 11717945 = 8788459) B8788459
theorem B459165023 : Blo 455782 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B2314331 : Blo 455782 2314331 := bstep (se 1 (by rfl) ⟨1735748, by rfl⟩ : syracuseStep 2314331 = 3471497) B3471497
theorem B581023 : Blo 455782 581023 := bstep (se 1 (by rfl) ⟨435767, by rfl⟩ : syracuseStep 581023 = 871535) B871535
theorem B515839 : Blo 455782 515839 := bstep (se 1 (by rfl) ⟨386879, by rfl⟩ : syracuseStep 515839 = 773759) B773759
theorem B13197451 : Blo 455782 13197451 := bstep (se 1 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 13197451 = 19796177) B19796177
theorem B6677959 : Blo 455782 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B11757311 : Blo 455782 11757311 := bstep (se 1 (by rfl) ⟨8817983, by rfl⟩ : syracuseStep 11757311 = 17635967) B17635967
theorem B1959689 : Blo 455782 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B978409 : Blo 455782 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B3894911 : Blo 455782 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B7794467 : Blo 455782 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B684335 : Blo 455782 684335 := bstep (se 1 (by rfl) ⟨513251, by rfl⟩ : syracuseStep 684335 = 1026503) B1026503
theorem B652159 : Blo 455782 652159 := bstep (se 1 (by rfl) ⟨489119, by rfl⟩ : syracuseStep 652159 = 978239) B978239
theorem B488863 : Blo 455782 488863 := bstep (se 1 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 488863 = 733295) B733295
theorem B456447 : Blo 455782 456447 := bstep (se 1 (by rfl) ⟨342335, by rfl⟩ : syracuseStep 456447 = 684671) B684671
theorem B3700889 : Blo 455782 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B8813063 : Blo 455782 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B457855 : Blo 455782 457855 := bstep (se 1 (by rfl) ⟨343391, by rfl⟩ : syracuseStep 457855 = 686783) B686783
theorem B458175 : Blo 455782 458175 := bstep (se 1 (by rfl) ⟨343631, by rfl⟩ : syracuseStep 458175 = 687263) B687263
theorem B17596601 : Blo 455782 17596601 := bstep (se 2 (by rfl) ⟨6598725, by rfl⟩ : syracuseStep 17596601 = 13197451) B13197451
theorem B1736903 : Blo 455782 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B688487 : Blo 455782 688487 := bstep (se 1 (by rfl) ⟨516365, by rfl⟩ : syracuseStep 688487 = 1032731) B1032731
theorem B688607 : Blo 455782 688607 := bstep (se 1 (by rfl) ⟨516455, by rfl⟩ : syracuseStep 688607 = 1032911) B1032911
theorem B41157307 : Blo 455782 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B689183 : Blo 455782 689183 := bstep (se 1 (by rfl) ⟨516887, by rfl⟩ : syracuseStep 689183 = 1033775) B1033775
theorem B689255 : Blo 455782 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B1542887 : Blo 455782 1542887 := bstep (se 1 (by rfl) ⟨1157165, by rfl⟩ : syracuseStep 1542887 = 2314331) B2314331
theorem B18748867 : Blo 455782 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B7838207 : Blo 455782 7838207 := bstep (se 1 (by rfl) ⟨5878655, by rfl⟩ : syracuseStep 7838207 = 11757311) B11757311
theorem B2596607 : Blo 455782 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B5218181 : Blo 455782 5218181 := bstep (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) B978409
theorem B1156265 : Blo 455782 1156265 := bstep (se 2 (by rfl) ⟨433599, by rfl⟩ : syracuseStep 1156265 = 867199) B867199
theorem B2467259 : Blo 455782 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B5875375 : Blo 455782 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B1026953 : Blo 455782 1026953 := bstep (se 2 (by rfl) ⟨385107, by rfl⟩ : syracuseStep 1026953 = 770215) B770215
theorem B7811963 : Blo 455782 7811963 := bstep (se 1 (by rfl) ⟨5858972, by rfl⟩ : syracuseStep 7811963 = 11717945) B11717945
theorem B1029545 : Blo 455782 1029545 := bstep (se 2 (by rfl) ⟨386079, by rfl⟩ : syracuseStep 1029545 = 772159) B772159
theorem B2931947 : Blo 455782 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B3915823 : Blo 455782 3915823 := bstep (se 1 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 3915823 = 5873735) B5873735
theorem B869545 : Blo 455782 869545 := bstep (se 2 (by rfl) ⟨326079, by rfl⟩ : syracuseStep 869545 = 652159) B652159
theorem B73516415 : Blo 455782 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B5196311 : Blo 455782 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B11849561 : Blo 455782 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B774697 : Blo 455782 774697 := bstep (se 2 (by rfl) ⟨290511, by rfl⟩ : syracuseStep 774697 = 581023) B581023
theorem B2611871 : Blo 455782 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B5561257 : Blo 455782 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B8903945 : Blo 455782 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B306110015 : Blo 455782 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B5268689 : Blo 455782 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2319839 : Blo 455782 2319839 := bstep (se 1 (by rfl) ⟨1739879, by rfl⟩ : syracuseStep 2319839 = 3479759) B3479759
theorem B1306459 : Blo 455782 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B684095 : Blo 455782 684095 := bstep (se 1 (by rfl) ⟨513071, by rfl⟩ : syracuseStep 684095 = 1026143) B1026143
theorem B684527 : Blo 455782 684527 := bstep (se 1 (by rfl) ⟨513395, by rfl⟩ : syracuseStep 684527 = 1026791) B1026791
theorem B651817 : Blo 455782 651817 := bstep (se 2 (by rfl) ⟨244431, by rfl⟩ : syracuseStep 651817 = 488863) B488863
theorem B979769 : Blo 455782 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B456223 : Blo 455782 456223 := bstep (se 1 (by rfl) ⟨342167, by rfl⟩ : syracuseStep 456223 = 684335) B684335
theorem B1538459 : Blo 455782 1538459 := bstep (se 1 (by rfl) ⟨1153844, by rfl⟩ : syracuseStep 1538459 = 2307689) B2307689
theorem B687647 : Blo 455782 687647 := bstep (se 1 (by rfl) ⟨515735, by rfl⟩ : syracuseStep 687647 = 1031471) B1031471
theorem B687719 : Blo 455782 687719 := bstep (se 1 (by rfl) ⟨515789, by rfl⟩ : syracuseStep 687719 = 1031579) B1031579
theorem B687785 : Blo 455782 687785 := bstep (se 2 (by rfl) ⟨257919, by rfl⟩ : syracuseStep 687785 = 515839) B515839
theorem B11731067 : Blo 455782 11731067 := bstep (se 1 (by rfl) ⟨8798300, by rfl⟩ : syracuseStep 11731067 = 17596601) B17596601
theorem B458991 : Blo 455782 458991 := bstep (se 1 (by rfl) ⟨344243, by rfl⟩ : syracuseStep 458991 = 688487) B688487
theorem B459071 : Blo 455782 459071 := bstep (se 1 (by rfl) ⟨344303, by rfl⟩ : syracuseStep 459071 = 688607) B688607
theorem B459455 : Blo 455782 459455 := bstep (se 1 (by rfl) ⟨344591, by rfl⟩ : syracuseStep 459455 = 689183) B689183
theorem B459503 : Blo 455782 459503 := bstep (se 1 (by rfl) ⟨344627, by rfl⟩ : syracuseStep 459503 = 689255) B689255
theorem B7833833 : Blo 455782 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B7899707 : Blo 455782 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B3476357 : Blo 455782 3476357 := bstep (se 4 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 3476357 = 651817) B651817
theorem B1741247 : Blo 455782 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B5935963 : Blo 455782 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B1741945 : Blo 455782 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B3478787 : Blo 455782 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B3512459 : Blo 455782 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B1644839 : Blo 455782 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B1546559 : Blo 455782 1546559 := bstep (se 1 (by rfl) ⟨1159919, by rfl⟩ : syracuseStep 1546559 = 2319839) B2319839
theorem B7415009 : Blo 455782 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B1025639 : Blo 455782 1025639 := bstep (se 1 (by rfl) ⟨769229, by rfl⟩ : syracuseStep 1025639 = 1538459) B1538459
theorem B5221097 : Blo 455782 5221097 := bstep (se 2 (by rfl) ⟨1957911, by rfl⟩ : syracuseStep 5221097 = 3915823) B3915823
theorem B1157935 : Blo 455782 1157935 := bstep (se 1 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 1157935 = 1736903) B1736903
theorem B1159393 : Blo 455782 1159393 := bstep (se 2 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 1159393 = 869545) B869545
theorem B1028591 : Blo 455782 1028591 := bstep (se 1 (by rfl) ⟨771443, by rfl⟩ : syracuseStep 1028591 = 1542887) B1542887
theorem B5225471 : Blo 455782 5225471 := bstep (se 1 (by rfl) ⟨3919103, by rfl⟩ : syracuseStep 5225471 = 7838207) B7838207
theorem B1032929 : Blo 455782 1032929 := bstep (se 2 (by rfl) ⟨387348, by rfl⟩ : syracuseStep 1032929 = 774697) B774697
theorem B770843 : Blo 455782 770843 := bstep (se 1 (by rfl) ⟨578132, by rfl⟩ : syracuseStep 770843 = 1156265) B1156265
theorem B1954631 : Blo 455782 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B54876409 : Blo 455782 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B3464207 : Blo 455782 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B196043773 : Blo 455782 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B204073343 : Blo 455782 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B1731071 : Blo 455782 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B24998489 : Blo 455782 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B684635 : Blo 455782 684635 := bstep (se 1 (by rfl) ⟨513476, by rfl⟩ : syracuseStep 684635 = 1026953) B1026953
theorem B456063 : Blo 455782 456063 := bstep (se 1 (by rfl) ⟨342047, by rfl⟩ : syracuseStep 456063 = 684095) B684095
theorem B456351 : Blo 455782 456351 := bstep (se 1 (by rfl) ⟨342263, by rfl⟩ : syracuseStep 456351 = 684527) B684527
theorem B653179 : Blo 455782 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B5207975 : Blo 455782 5207975 := bstep (se 1 (by rfl) ⟨3905981, by rfl⟩ : syracuseStep 5207975 = 7811963) B7811963
theorem B686363 : Blo 455782 686363 := bstep (se 1 (by rfl) ⟨514772, by rfl⟩ : syracuseStep 686363 = 1029545) B1029545
theorem B458431 : Blo 455782 458431 := bstep (se 1 (by rfl) ⟨343823, by rfl⟩ : syracuseStep 458431 = 687647) B687647
theorem B458479 : Blo 455782 458479 := bstep (se 1 (by rfl) ⟨343859, by rfl⟩ : syracuseStep 458479 = 687719) B687719
theorem B458523 : Blo 455782 458523 := bstep (se 1 (by rfl) ⟨343892, by rfl⟩ : syracuseStep 458523 = 687785) B687785
theorem B688619 : Blo 455782 688619 := bstep (se 1 (by rfl) ⟨516464, by rfl⟩ : syracuseStep 688619 = 1032929) B1032929
theorem B261391697 : Blo 455782 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B5212349 : Blo 455782 5212349 := bstep (se 3 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 5212349 = 1954631) B1954631
theorem B1543913 : Blo 455782 1543913 := bstep (se 2 (by rfl) ⟨578967, by rfl⟩ : syracuseStep 1543913 = 1157935) B1157935
theorem B1545857 : Blo 455782 1545857 := bstep (se 2 (by rfl) ⟨579696, by rfl⟩ : syracuseStep 1545857 = 1159393) B1159393
theorem B1154047 : Blo 455782 1154047 := bstep (se 1 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 1154047 = 1731071) B1731071
theorem B3480731 : Blo 455782 3480731 := bstep (se 1 (by rfl) ⟨2610548, by rfl⟩ : syracuseStep 3480731 = 5221097) B5221097
theorem B3483647 : Blo 455782 3483647 := bstep (se 1 (by rfl) ⟨2612735, by rfl⟩ : syracuseStep 3483647 = 5225471) B5225471
theorem B5222555 : Blo 455782 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B1160831 : Blo 455782 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B2341639 : Blo 455782 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B1096559 : Blo 455782 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B1031039 : Blo 455782 1031039 := bstep (se 1 (by rfl) ⟨773279, by rfl⟩ : syracuseStep 1031039 = 1546559) B1546559
theorem B2309471 : Blo 455782 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B7914617 : Blo 455782 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B870905 : Blo 455782 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B16665659 : Blo 455782 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B7820711 : Blo 455782 7820711 := bstep (se 1 (by rfl) ⟨5865533, by rfl⟩ : syracuseStep 7820711 = 11731067) B11731067
theorem B513895 : Blo 455782 513895 := bstep (se 1 (by rfl) ⟨385421, by rfl⟩ : syracuseStep 513895 = 770843) B770843
theorem B292674181 : Blo 455782 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B5266471 : Blo 455782 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B2317571 : Blo 455782 2317571 := bstep (se 1 (by rfl) ⟨1738178, by rfl⟩ : syracuseStep 2317571 = 3476357) B3476357
theorem B2319191 : Blo 455782 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B4943339 : Blo 455782 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B683759 : Blo 455782 683759 := bstep (se 1 (by rfl) ⟨512819, by rfl⟩ : syracuseStep 683759 = 1025639) B1025639
theorem B2322593 : Blo 455782 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B136048895 : Blo 455782 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B685727 : Blo 455782 685727 := bstep (se 1 (by rfl) ⟨514295, by rfl⟩ : syracuseStep 685727 = 1028591) B1028591
theorem B456423 : Blo 455782 456423 := bstep (se 1 (by rfl) ⟨342317, by rfl⟩ : syracuseStep 456423 = 684635) B684635
theorem B3471983 : Blo 455782 3471983 := bstep (se 1 (by rfl) ⟨2603987, by rfl⟩ : syracuseStep 3471983 = 5207975) B5207975
theorem B457575 : Blo 455782 457575 := bstep (se 1 (by rfl) ⟨343181, by rfl⟩ : syracuseStep 457575 = 686363) B686363
theorem B459079 : Blo 455782 459079 := bstep (se 1 (by rfl) ⟨344309, by rfl⟩ : syracuseStep 459079 = 688619) B688619
theorem B5276411 : Blo 455782 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B174261131 : Blo 455782 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B3474899 : Blo 455782 3474899 := bstep (se 1 (by rfl) ⟨2606174, by rfl⟩ : syracuseStep 3474899 = 5212349) B5212349
theorem B11110439 : Blo 455782 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B5213807 : Blo 455782 5213807 := bstep (se 1 (by rfl) ⟨3910355, by rfl⟩ : syracuseStep 5213807 = 7820711) B7820711
theorem B12488741 : Blo 455782 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B1545047 : Blo 455782 1545047 := bstep (se 1 (by rfl) ⟨1158785, by rfl⟩ : syracuseStep 1545047 = 2317571) B2317571
theorem B1546127 : Blo 455782 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B3481703 : Blo 455782 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B1548395 : Blo 455782 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B7021961 : Blo 455782 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B731039 : Blo 455782 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B1029275 : Blo 455782 1029275 := bstep (se 1 (by rfl) ⟨771956, by rfl⟩ : syracuseStep 1029275 = 1543913) B1543913
theorem B1030571 : Blo 455782 1030571 := bstep (se 1 (by rfl) ⟨772928, by rfl⟩ : syracuseStep 1030571 = 1545857) B1545857
theorem B3295559 : Blo 455782 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B773887 : Blo 455782 773887 := bstep (se 1 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 773887 = 1160831) B1160831
theorem B2314655 : Blo 455782 2314655 := bstep (se 1 (by rfl) ⟨1735991, by rfl⟩ : syracuseStep 2314655 = 3471983) B3471983
theorem B580603 : Blo 455782 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B2320487 : Blo 455782 2320487 := bstep (se 1 (by rfl) ⟨1740365, by rfl⟩ : syracuseStep 2320487 = 3480731) B3480731
theorem B2322431 : Blo 455782 2322431 := bstep (se 1 (by rfl) ⟨1741823, by rfl⟩ : syracuseStep 2322431 = 3483647) B3483647
theorem B685193 : Blo 455782 685193 := bstep (se 2 (by rfl) ⟨256947, by rfl⟩ : syracuseStep 685193 = 513895) B513895
theorem B455839 : Blo 455782 455839 := bstep (se 1 (by rfl) ⟨341879, by rfl⟩ : syracuseStep 455839 = 683759) B683759
theorem B90699263 : Blo 455782 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B390232241 : Blo 455782 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B457151 : Blo 455782 457151 := bstep (se 1 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 457151 = 685727) B685727
theorem B1538729 : Blo 455782 1538729 := bstep (se 2 (by rfl) ⟨577023, by rfl⟩ : syracuseStep 1538729 = 1154047) B1154047
theorem B687359 : Blo 455782 687359 := bstep (se 1 (by rfl) ⟨515519, by rfl⟩ : syracuseStep 687359 = 1031039) B1031039
theorem B1539647 : Blo 455782 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B7406959 : Blo 455782 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B2197039 : Blo 455782 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B3475871 : Blo 455782 3475871 := bstep (se 1 (by rfl) ⟨2606903, by rfl⟩ : syracuseStep 3475871 = 5213807) B5213807
theorem B8325827 : Blo 455782 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B1543103 : Blo 455782 1543103 := bstep (se 1 (by rfl) ⟨1157327, by rfl⟩ : syracuseStep 1543103 = 2314655) B2314655
theorem B1546991 : Blo 455782 1546991 := bstep (se 1 (by rfl) ⟨1160243, by rfl⟩ : syracuseStep 1546991 = 2320487) B2320487
theorem B1548287 : Blo 455782 1548287 := bstep (se 1 (by rfl) ⟨1161215, by rfl⟩ : syracuseStep 1548287 = 2322431) B2322431
theorem B60466175 : Blo 455782 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B260154827 : Blo 455782 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B1025819 : Blo 455782 1025819 := bstep (se 1 (by rfl) ⟨769364, by rfl⟩ : syracuseStep 1025819 = 1538729) B1538729
theorem B1026431 : Blo 455782 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B3517607 : Blo 455782 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B116174087 : Blo 455782 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B1030031 : Blo 455782 1030031 := bstep (se 1 (by rfl) ⟨772523, by rfl⟩ : syracuseStep 1030031 = 1545047) B1545047
theorem B1030751 : Blo 455782 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B1031849 : Blo 455782 1031849 := bstep (se 2 (by rfl) ⟨386943, by rfl⟩ : syracuseStep 1031849 = 773887) B773887
theorem B1949437 : Blo 455782 1949437 := bstep (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) B731039
theorem B1032263 : Blo 455782 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B774137 : Blo 455782 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B2316599 : Blo 455782 2316599 := bstep (se 1 (by rfl) ⟨1737449, by rfl⟩ : syracuseStep 2316599 = 3474899) B3474899
theorem B2321135 : Blo 455782 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B4681307 : Blo 455782 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B456795 : Blo 455782 456795 := bstep (se 1 (by rfl) ⟨342596, by rfl⟩ : syracuseStep 456795 = 685193) B685193
theorem B686183 : Blo 455782 686183 := bstep (se 1 (by rfl) ⟨514637, by rfl⟩ : syracuseStep 686183 = 1029275) B1029275
theorem B687047 : Blo 455782 687047 := bstep (se 1 (by rfl) ⟨515285, by rfl⟩ : syracuseStep 687047 = 1030571) B1030571
theorem B458239 : Blo 455782 458239 := bstep (se 1 (by rfl) ⟨343679, by rfl⟩ : syracuseStep 458239 = 687359) B687359
theorem B688175 : Blo 455782 688175 := bstep (se 1 (by rfl) ⟨516131, by rfl⟩ : syracuseStep 688175 = 1032263) B1032263
theorem B1544399 : Blo 455782 1544399 := bstep (se 1 (by rfl) ⟨1158299, by rfl⟩ : syracuseStep 1544399 = 2316599) B2316599
theorem B40310783 : Blo 455782 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B1547423 : Blo 455782 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B3120871 : Blo 455782 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B9380285 : Blo 455782 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B2599249 : Blo 455782 2599249 := bstep (se 2 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 2599249 = 1949437) B1949437
theorem B5550551 : Blo 455782 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B9875945 : Blo 455782 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B1028735 : Blo 455782 1028735 := bstep (se 1 (by rfl) ⟨771551, by rfl⟩ : syracuseStep 1028735 = 1543103) B1543103
theorem B2929385 : Blo 455782 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B1031327 : Blo 455782 1031327 := bstep (se 1 (by rfl) ⟨773495, by rfl⟩ : syracuseStep 1031327 = 1546991) B1546991
theorem B1032191 : Blo 455782 1032191 := bstep (se 1 (by rfl) ⟨774143, by rfl⟩ : syracuseStep 1032191 = 1548287) B1548287
theorem B77449391 : Blo 455782 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B2317247 : Blo 455782 2317247 := bstep (se 1 (by rfl) ⟨1737935, by rfl⟩ : syracuseStep 2317247 = 3475871) B3475871
theorem B516091 : Blo 455782 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B173436551 : Blo 455782 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B683879 : Blo 455782 683879 := bstep (se 1 (by rfl) ⟨512909, by rfl⟩ : syracuseStep 683879 = 1025819) B1025819
theorem B684287 : Blo 455782 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B686687 : Blo 455782 686687 := bstep (se 1 (by rfl) ⟨515015, by rfl⟩ : syracuseStep 686687 = 1030031) B1030031
theorem B457455 : Blo 455782 457455 := bstep (se 1 (by rfl) ⟨343091, by rfl⟩ : syracuseStep 457455 = 686183) B686183
theorem B687167 : Blo 455782 687167 := bstep (se 1 (by rfl) ⟨515375, by rfl⟩ : syracuseStep 687167 = 1030751) B1030751
theorem B458031 : Blo 455782 458031 := bstep (se 1 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 458031 = 687047) B687047
theorem B687899 : Blo 455782 687899 := bstep (se 1 (by rfl) ⟨515924, by rfl⟩ : syracuseStep 687899 = 1031849) B1031849
theorem B458783 : Blo 455782 458783 := bstep (se 1 (by rfl) ⟨344087, by rfl⟩ : syracuseStep 458783 = 688175) B688175
theorem B26873855 : Blo 455782 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B1544831 : Blo 455782 1544831 := bstep (se 1 (by rfl) ⟨1158623, by rfl⟩ : syracuseStep 1544831 = 2317247) B2317247
theorem B1029599 : Blo 455782 1029599 := bstep (se 1 (by rfl) ⟨772199, by rfl⟩ : syracuseStep 1029599 = 1544399) B1544399
theorem B1031615 : Blo 455782 1031615 := bstep (se 1 (by rfl) ⟨773711, by rfl⟩ : syracuseStep 1031615 = 1547423) B1547423
theorem B115624367 : Blo 455782 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1952923 : Blo 455782 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B26335853 : Blo 455782 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B51632927 : Blo 455782 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B3465665 : Blo 455782 3465665 := bstep (se 2 (by rfl) ⟨1299624, by rfl⟩ : syracuseStep 3465665 = 2599249) B2599249
theorem B6253523 : Blo 455782 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B455919 : Blo 455782 455919 := bstep (se 1 (by rfl) ⟨341939, by rfl⟩ : syracuseStep 455919 = 683879) B683879
theorem B456191 : Blo 455782 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B3700367 : Blo 455782 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B685823 : Blo 455782 685823 := bstep (se 1 (by rfl) ⟨514367, by rfl⟩ : syracuseStep 685823 = 1028735) B1028735
theorem B457791 : Blo 455782 457791 := bstep (se 1 (by rfl) ⟨343343, by rfl⟩ : syracuseStep 457791 = 686687) B686687
theorem B458111 : Blo 455782 458111 := bstep (se 1 (by rfl) ⟨343583, by rfl⟩ : syracuseStep 458111 = 687167) B687167
theorem B687551 : Blo 455782 687551 := bstep (se 1 (by rfl) ⟨515663, by rfl⟩ : syracuseStep 687551 = 1031327) B1031327
theorem B4161161 : Blo 455782 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B458599 : Blo 455782 458599 := bstep (se 1 (by rfl) ⟨343949, by rfl⟩ : syracuseStep 458599 = 687899) B687899
theorem B688121 : Blo 455782 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B688127 : Blo 455782 688127 := bstep (se 1 (by rfl) ⟨516095, by rfl⟩ : syracuseStep 688127 = 1032191) B1032191
theorem B4169015 : Blo 455782 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B2466911 : Blo 455782 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B77082911 : Blo 455782 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B1029887 : Blo 455782 1029887 := bstep (se 1 (by rfl) ⟨772415, by rfl⟩ : syracuseStep 1029887 = 1544831) B1544831
theorem B458751 : Blo 455782 458751 := bstep (se 1 (by rfl) ⟨344063, by rfl⟩ : syracuseStep 458751 = 688127) B688127
theorem B2603897 : Blo 455782 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B34421951 : Blo 455782 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B2310443 : Blo 455782 2310443 := bstep (se 1 (by rfl) ⟨1732832, by rfl⟩ : syracuseStep 2310443 = 3465665) B3465665
theorem B2774107 : Blo 455782 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B17915903 : Blo 455782 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B17557235 : Blo 455782 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B686399 : Blo 455782 686399 := bstep (se 1 (by rfl) ⟨514799, by rfl⟩ : syracuseStep 686399 = 1029599) B1029599
theorem B457215 : Blo 455782 457215 := bstep (se 1 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 457215 = 685823) B685823
theorem B458367 : Blo 455782 458367 := bstep (se 1 (by rfl) ⟨343775, by rfl⟩ : syracuseStep 458367 = 687551) B687551
theorem B687743 : Blo 455782 687743 := bstep (se 1 (by rfl) ⟨515807, by rfl⟩ : syracuseStep 687743 = 1031615) B1031615
theorem B458747 : Blo 455782 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B1540295 : Blo 455782 1540295 := bstep (se 1 (by rfl) ⟨1155221, by rfl⟩ : syracuseStep 1540295 = 2310443) B2310443
theorem B1644607 : Blo 455782 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B11704823 : Blo 455782 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B51388607 : Blo 455782 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B22947967 : Blo 455782 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B11943935 : Blo 455782 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B14795237 : Blo 455782 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B2779343 : Blo 455782 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B686591 : Blo 455782 686591 := bstep (se 1 (by rfl) ⟨514943, by rfl⟩ : syracuseStep 686591 = 1029887) B1029887
theorem B457599 : Blo 455782 457599 := bstep (se 1 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 457599 = 686399) B686399
theorem B1735931 : Blo 455782 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B458495 : Blo 455782 458495 := bstep (se 1 (by rfl) ⟨343871, by rfl⟩ : syracuseStep 458495 = 687743) B687743
theorem B9863491 : Blo 455782 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B122389157 : Blo 455782 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B7803215 : Blo 455782 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B1157287 : Blo 455782 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B1026863 : Blo 455782 1026863 := bstep (se 1 (by rfl) ⟨770147, by rfl⟩ : syracuseStep 1026863 = 1540295) B1540295
theorem B34259071 : Blo 455782 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B1852895 : Blo 455782 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B7962623 : Blo 455782 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B8771237 : Blo 455782 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B457727 : Blo 455782 457727 := bstep (se 1 (by rfl) ⟨343295, by rfl⟩ : syracuseStep 457727 = 686591) B686591
theorem B45678761 : Blo 455782 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B81592771 : Blo 455782 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B5308415 : Blo 455782 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B1543049 : Blo 455782 1543049 := bstep (se 2 (by rfl) ⟨578643, by rfl⟩ : syracuseStep 1543049 = 1157287) B1157287
theorem B13151321 : Blo 455782 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B5847491 : Blo 455782 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B1235263 : Blo 455782 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B5202143 : Blo 455782 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B684575 : Blo 455782 684575 := bstep (se 1 (by rfl) ⟨513431, by rfl⟩ : syracuseStep 684575 = 1026863) B1026863
theorem B108790361 : Blo 455782 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1647017 : Blo 455782 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B30452507 : Blo 455782 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B3538943 : Blo 455782 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B1028699 : Blo 455782 1028699 := bstep (se 1 (by rfl) ⟨771524, by rfl⟩ : syracuseStep 1028699 = 1543049) B1543049
theorem B8767547 : Blo 455782 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B3468095 : Blo 455782 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B456383 : Blo 455782 456383 := bstep (se 1 (by rfl) ⟨342287, by rfl⟩ : syracuseStep 456383 = 684575) B684575
theorem B3898327 : Blo 455782 3898327 := bstep (se 1 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 3898327 = 5847491) B5847491
theorem B2359295 : Blo 455782 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B72526907 : Blo 455782 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B5845031 : Blo 455782 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B1098011 : Blo 455782 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B20301671 : Blo 455782 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B2312063 : Blo 455782 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B5197769 : Blo 455782 5197769 := bstep (se 2 (by rfl) ⟨1949163, by rfl⟩ : syracuseStep 5197769 = 3898327) B3898327
theorem B685799 : Blo 455782 685799 := bstep (se 1 (by rfl) ⟨514349, by rfl⟩ : syracuseStep 685799 = 1028699) B1028699
theorem B13534447 : Blo 455782 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B1541375 : Blo 455782 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B732007 : Blo 455782 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B1572863 : Blo 455782 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B48351271 : Blo 455782 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B3465179 : Blo 455782 3465179 := bstep (se 1 (by rfl) ⟨2598884, by rfl⟩ : syracuseStep 3465179 = 5197769) B5197769
theorem B3896687 : Blo 455782 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B457199 : Blo 455782 457199 := bstep (se 1 (by rfl) ⟨342899, by rfl⟩ : syracuseStep 457199 = 685799) B685799
theorem B3904037 : Blo 455782 3904037 := bstep (se 4 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 3904037 = 732007) B732007
theorem B2597791 : Blo 455782 2597791 := bstep (se 1 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 2597791 = 3896687) B3896687
theorem B1027583 : Blo 455782 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B64468361 : Blo 455782 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B2310119 : Blo 455782 2310119 := bstep (se 1 (by rfl) ⟨1732589, by rfl⟩ : syracuseStep 2310119 = 3465179) B3465179
theorem B18045929 : Blo 455782 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B4194301 : Blo 455782 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B12030619 : Blo 455782 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B2602691 : Blo 455782 2602691 := bstep (se 1 (by rfl) ⟨1952018, by rfl⟩ : syracuseStep 2602691 = 3904037) B3904037
theorem B42978907 : Blo 455782 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B5592401 : Blo 455782 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B3463721 : Blo 455782 3463721 := bstep (se 2 (by rfl) ⟨1298895, by rfl⟩ : syracuseStep 3463721 = 2597791) B2597791
theorem B685055 : Blo 455782 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B1540079 : Blo 455782 1540079 := bstep (se 1 (by rfl) ⟨1155059, by rfl⟩ : syracuseStep 1540079 = 2310119) B2310119
theorem B229220837 : Blo 455782 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1026719 : Blo 455782 1026719 := bstep (se 1 (by rfl) ⟨770039, by rfl⟩ : syracuseStep 1026719 = 1540079) B1540079
theorem B2309147 : Blo 455782 2309147 := bstep (se 1 (by rfl) ⟨1731860, by rfl⟩ : syracuseStep 2309147 = 3463721) B3463721
theorem B16040825 : Blo 455782 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B3728267 : Blo 455782 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B456703 : Blo 455782 456703 := bstep (se 1 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 456703 = 685055) B685055
theorem B1735127 : Blo 455782 1735127 := bstep (se 1 (by rfl) ⟨1301345, by rfl⟩ : syracuseStep 1735127 = 2602691) B2602691
theorem B1156751 : Blo 455782 1156751 := bstep (se 1 (by rfl) ⟨867563, by rfl⟩ : syracuseStep 1156751 = 1735127) B1735127
theorem B10693883 : Blo 455782 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B152813891 : Blo 455782 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B2485511 : Blo 455782 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B684479 : Blo 455782 684479 := bstep (se 1 (by rfl) ⟨513359, by rfl⟩ : syracuseStep 684479 = 1026719) B1026719
theorem B1539431 : Blo 455782 1539431 := bstep (se 1 (by rfl) ⟨1154573, by rfl⟩ : syracuseStep 1539431 = 2309147) B2309147
theorem B101875927 : Blo 455782 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B1026287 : Blo 455782 1026287 := bstep (se 1 (by rfl) ⟨769715, by rfl⟩ : syracuseStep 1026287 = 1539431) B1539431
theorem B771167 : Blo 455782 771167 := bstep (se 1 (by rfl) ⟨578375, by rfl⟩ : syracuseStep 771167 = 1156751) B1156751
theorem B7129255 : Blo 455782 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B1657007 : Blo 455782 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B456319 : Blo 455782 456319 := bstep (se 1 (by rfl) ⟨342239, by rfl⟩ : syracuseStep 456319 = 684479) B684479
theorem B9505673 : Blo 455782 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B135834569 : Blo 455782 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B514111 : Blo 455782 514111 := bstep (se 1 (by rfl) ⟨385583, by rfl⟩ : syracuseStep 514111 = 771167) B771167
theorem B1104671 : Blo 455782 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B684191 : Blo 455782 684191 := bstep (se 1 (by rfl) ⟨513143, by rfl⟩ : syracuseStep 684191 = 1026287) B1026287
theorem B6337115 : Blo 455782 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B736447 : Blo 455782 736447 := bstep (se 1 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 736447 = 1104671) B1104671
theorem B90556379 : Blo 455782 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B685481 : Blo 455782 685481 := bstep (se 2 (by rfl) ⟨257055, by rfl⟩ : syracuseStep 685481 = 514111) B514111
theorem B456127 : Blo 455782 456127 := bstep (se 1 (by rfl) ⟨342095, by rfl⟩ : syracuseStep 456127 = 684191) B684191
theorem B60370919 : Blo 455782 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B4224743 : Blo 455782 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B456987 : Blo 455782 456987 := bstep (se 1 (by rfl) ⟨342740, by rfl⟩ : syracuseStep 456987 = 685481) B685481
theorem B981929 : Blo 455782 981929 := bstep (se 2 (by rfl) ⟨368223, by rfl⟩ : syracuseStep 981929 = 736447) B736447
theorem B40247279 : Blo 455782 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B2618477 : Blo 455782 2618477 := bstep (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) B981929
theorem B2816495 : Blo 455782 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B1745651 : Blo 455782 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B1877663 : Blo 455782 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B26831519 : Blo 455782 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1251775 : Blo 455782 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B1163767 : Blo 455782 1163767 := bstep (se 1 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 1163767 = 1745651) B1745651
theorem B17887679 : Blo 455782 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B1551689 : Blo 455782 1551689 := bstep (se 2 (by rfl) ⟨581883, by rfl⟩ : syracuseStep 1551689 = 1163767) B1163767
theorem B11925119 : Blo 455782 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B1669033 : Blo 455782 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B1034459 : Blo 455782 1034459 := bstep (se 1 (by rfl) ⟨775844, by rfl⟩ : syracuseStep 1034459 = 1551689) B1551689
theorem B7950079 : Blo 455782 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B2225377 : Blo 455782 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B689639 : Blo 455782 689639 := bstep (se 1 (by rfl) ⟨517229, by rfl⟩ : syracuseStep 689639 = 1034459) B1034459
theorem B11868677 : Blo 455782 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B10600105 : Blo 455782 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B459759 : Blo 455782 459759 := bstep (se 1 (by rfl) ⟨344819, by rfl⟩ : syracuseStep 459759 = 689639) B689639
theorem B14133473 : Blo 455782 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B7912451 : Blo 455782 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B9422315 : Blo 455782 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B21099869 : Blo 455782 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 455782 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B6281543 : Blo 455782 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B37510877 : Blo 455782 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B4187695 : Blo 455782 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 455782 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B100029005 : Blo 455782 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B66686003 : Blo 455782 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B3722395 : Blo 455782 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 455782 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B44457335 : Blo 455782 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B29638223 : Blo 455782 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B3308795 : Blo 455782 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 455782 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B19758815 : Blo 455782 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B1470575 : Blo 455782 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B13172543 : Blo 455782 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B3921533 : Blo 455782 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B8781695 : Blo 455782 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5854463 : Blo 455782 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B2614355 : Blo 455782 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B3902975 : Blo 455782 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B1742903 : Blo 455782 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B2601983 : Blo 455782 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B1161935 : Blo 455782 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B774623 : Blo 455782 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B1734655 : Blo 455782 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B2312873 : Blo 455782 2312873 := bstep (se 2 (by rfl) ⟨867327, by rfl⟩ : syracuseStep 2312873 = 1734655) B1734655
theorem B516415 : Blo 455782 516415 := bstep (se 1 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 516415 = 774623) B774623
theorem B688553 : Blo 455782 688553 := bstep (se 2 (by rfl) ⟨258207, by rfl⟩ : syracuseStep 688553 = 516415) B516415
theorem B1541915 : Blo 455782 1541915 := bstep (se 1 (by rfl) ⟨1156436, by rfl⟩ : syracuseStep 1541915 = 2312873) B2312873
theorem B459035 : Blo 455782 459035 := bstep (se 1 (by rfl) ⟨344276, by rfl⟩ : syracuseStep 459035 = 688553) B688553
theorem B1027943 : Blo 455782 1027943 := bstep (se 1 (by rfl) ⟨770957, by rfl⟩ : syracuseStep 1027943 = 1541915) B1541915
theorem B685295 : Blo 455782 685295 := bstep (se 1 (by rfl) ⟨513971, by rfl⟩ : syracuseStep 685295 = 1027943) B1027943
theorem B456863 : Blo 455782 456863 := bstep (se 1 (by rfl) ⟨342647, by rfl⟩ : syracuseStep 456863 = 685295) B685295

theorem C0 (j : ℕ) (h1 : 113945 ≤ j) (h2 : j ≤ 114644) : Blo 455782 (4 * j + 3) := by
  interval_cases j
  · exact B455783
  · exact B455787
  · exact B455791
  · exact B455795
  · exact B455799
  · exact B455803
  · exact B455807
  · exact B455811
  · exact B455815
  · exact B455819
  · exact B455823
  · exact B455827
  · exact B455831
  · exact B455835
  · exact B455839
  · exact B455843
  · exact B455847
  · exact B455851
  · exact B455855
  · exact B455859
  · exact B455863
  · exact B455867
  · exact B455871
  · exact B455875
  · exact B455879
  · exact B455883
  · exact B455887
  · exact B455891
  · exact B455895
  · exact B455899
  · exact B455903
  · exact B455907
  · exact B455911
  · exact B455915
  · exact B455919
  · exact B455923
  · exact B455927
  · exact B455931
  · exact B455935
  · exact B455939
  · exact B455943
  · exact B455947
  · exact B455951
  · exact B455955
  · exact B455959
  · exact B455963
  · exact B455967
  · exact B455971
  · exact B455975
  · exact B455979
  · exact B455983
  · exact B455987
  · exact B455991
  · exact B455995
  · exact B455999
  · exact B456003
  · exact B456007
  · exact B456011
  · exact B456015
  · exact B456019
  · exact B456023
  · exact B456027
  · exact B456031
  · exact B456035
  · exact B456039
  · exact B456043
  · exact B456047
  · exact B456051
  · exact B456055
  · exact B456059
  · exact B456063
  · exact B456067
  · exact B456071
  · exact B456075
  · exact B456079
  · exact B456083
  · exact B456087
  · exact B456091
  · exact B456095
  · exact B456099
  · exact B456103
  · exact B456107
  · exact B456111
  · exact B456115
  · exact B456119
  · exact B456123
  · exact B456127
  · exact B456131
  · exact B456135
  · exact B456139
  · exact B456143
  · exact B456147
  · exact B456151
  · exact B456155
  · exact B456159
  · exact B456163
  · exact B456167
  · exact B456171
  · exact B456175
  · exact B456179
  · exact B456183
  · exact B456187
  · exact B456191
  · exact B456195
  · exact B456199
  · exact B456203
  · exact B456207
  · exact B456211
  · exact B456215
  · exact B456219
  · exact B456223
  · exact B456227
  · exact B456231
  · exact B456235
  · exact B456239
  · exact B456243
  · exact B456247
  · exact B456251
  · exact B456255
  · exact B456259
  · exact B456263
  · exact B456267
  · exact B456271
  · exact B456275
  · exact B456279
  · exact B456283
  · exact B456287
  · exact B456291
  · exact B456295
  · exact B456299
  · exact B456303
  · exact B456307
  · exact B456311
  · exact B456315
  · exact B456319
  · exact B456323
  · exact B456327
  · exact B456331
  · exact B456335
  · exact B456339
  · exact B456343
  · exact B456347
  · exact B456351
  · exact B456355
  · exact B456359
  · exact B456363
  · exact B456367
  · exact B456371
  · exact B456375
  · exact B456379
  · exact B456383
  · exact B456387
  · exact B456391
  · exact B456395
  · exact B456399
  · exact B456403
  · exact B456407
  · exact B456411
  · exact B456415
  · exact B456419
  · exact B456423
  · exact B456427
  · exact B456431
  · exact B456435
  · exact B456439
  · exact B456443
  · exact B456447
  · exact B456451
  · exact B456455
  · exact B456459
  · exact B456463
  · exact B456467
  · exact B456471
  · exact B456475
  · exact B456479
  · exact B456483
  · exact B456487
  · exact B456491
  · exact B456495
  · exact B456499
  · exact B456503
  · exact B456507
  · exact B456511
  · exact B456515
  · exact B456519
  · exact B456523
  · exact B456527
  · exact B456531
  · exact B456535
  · exact B456539
  · exact B456543
  · exact B456547
  · exact B456551
  · exact B456555
  · exact B456559
  · exact B456563
  · exact B456567
  · exact B456571
  · exact B456575
  · exact B456579
  · exact B456583
  · exact B456587
  · exact B456591
  · exact B456595
  · exact B456599
  · exact B456603
  · exact B456607
  · exact B456611
  · exact B456615
  · exact B456619
  · exact B456623
  · exact B456627
  · exact B456631
  · exact B456635
  · exact B456639
  · exact B456643
  · exact B456647
  · exact B456651
  · exact B456655
  · exact B456659
  · exact B456663
  · exact B456667
  · exact B456671
  · exact B456675
  · exact B456679
  · exact B456683
  · exact B456687
  · exact B456691
  · exact B456695
  · exact B456699
  · exact B456703
  · exact B456707
  · exact B456711
  · exact B456715
  · exact B456719
  · exact B456723
  · exact B456727
  · exact B456731
  · exact B456735
  · exact B456739
  · exact B456743
  · exact B456747
  · exact B456751
  · exact B456755
  · exact B456759
  · exact B456763
  · exact B456767
  · exact B456771
  · exact B456775
  · exact B456779
  · exact B456783
  · exact B456787
  · exact B456791
  · exact B456795
  · exact B456799
  · exact B456803
  · exact B456807
  · exact B456811
  · exact B456815
  · exact B456819
  · exact B456823
  · exact B456827
  · exact B456831
  · exact B456835
  · exact B456839
  · exact B456843
  · exact B456847
  · exact B456851
  · exact B456855
  · exact B456859
  · exact B456863
  · exact B456867
  · exact B456871
  · exact B456875
  · exact B456879
  · exact B456883
  · exact B456887
  · exact B456891
  · exact B456895
  · exact B456899
  · exact B456903
  · exact B456907
  · exact B456911
  · exact B456915
  · exact B456919
  · exact B456923
  · exact B456927
  · exact B456931
  · exact B456935
  · exact B456939
  · exact B456943
  · exact B456947
  · exact B456951
  · exact B456955
  · exact B456959
  · exact B456963
  · exact B456967
  · exact B456971
  · exact B456975
  · exact B456979
  · exact B456983
  · exact B456987
  · exact B456991
  · exact B456995
  · exact B456999
  · exact B457003
  · exact B457007
  · exact B457011
  · exact B457015
  · exact B457019
  · exact B457023
  · exact B457027
  · exact B457031
  · exact B457035
  · exact B457039
  · exact B457043
  · exact B457047
  · exact B457051
  · exact B457055
  · exact B457059
  · exact B457063
  · exact B457067
  · exact B457071
  · exact B457075
  · exact B457079
  · exact B457083
  · exact B457087
  · exact B457091
  · exact B457095
  · exact B457099
  · exact B457103
  · exact B457107
  · exact B457111
  · exact B457115
  · exact B457119
  · exact B457123
  · exact B457127
  · exact B457131
  · exact B457135
  · exact B457139
  · exact B457143
  · exact B457147
  · exact B457151
  · exact B457155
  · exact B457159
  · exact B457163
  · exact B457167
  · exact B457171
  · exact B457175
  · exact B457179
  · exact B457183
  · exact B457187
  · exact B457191
  · exact B457195
  · exact B457199
  · exact B457203
  · exact B457207
  · exact B457211
  · exact B457215
  · exact B457219
  · exact B457223
  · exact B457227
  · exact B457231
  · exact B457235
  · exact B457239
  · exact B457243
  · exact B457247
  · exact B457251
  · exact B457255
  · exact B457259
  · exact B457263
  · exact B457267
  · exact B457271
  · exact B457275
  · exact B457279
  · exact B457283
  · exact B457287
  · exact B457291
  · exact B457295
  · exact B457299
  · exact B457303
  · exact B457307
  · exact B457311
  · exact B457315
  · exact B457319
  · exact B457323
  · exact B457327
  · exact B457331
  · exact B457335
  · exact B457339
  · exact B457343
  · exact B457347
  · exact B457351
  · exact B457355
  · exact B457359
  · exact B457363
  · exact B457367
  · exact B457371
  · exact B457375
  · exact B457379
  · exact B457383
  · exact B457387
  · exact B457391
  · exact B457395
  · exact B457399
  · exact B457403
  · exact B457407
  · exact B457411
  · exact B457415
  · exact B457419
  · exact B457423
  · exact B457427
  · exact B457431
  · exact B457435
  · exact B457439
  · exact B457443
  · exact B457447
  · exact B457451
  · exact B457455
  · exact B457459
  · exact B457463
  · exact B457467
  · exact B457471
  · exact B457475
  · exact B457479
  · exact B457483
  · exact B457487
  · exact B457491
  · exact B457495
  · exact B457499
  · exact B457503
  · exact B457507
  · exact B457511
  · exact B457515
  · exact B457519
  · exact B457523
  · exact B457527
  · exact B457531
  · exact B457535
  · exact B457539
  · exact B457543
  · exact B457547
  · exact B457551
  · exact B457555
  · exact B457559
  · exact B457563
  · exact B457567
  · exact B457571
  · exact B457575
  · exact B457579
  · exact B457583
  · exact B457587
  · exact B457591
  · exact B457595
  · exact B457599
  · exact B457603
  · exact B457607
  · exact B457611
  · exact B457615
  · exact B457619
  · exact B457623
  · exact B457627
  · exact B457631
  · exact B457635
  · exact B457639
  · exact B457643
  · exact B457647
  · exact B457651
  · exact B457655
  · exact B457659
  · exact B457663
  · exact B457667
  · exact B457671
  · exact B457675
  · exact B457679
  · exact B457683
  · exact B457687
  · exact B457691
  · exact B457695
  · exact B457699
  · exact B457703
  · exact B457707
  · exact B457711
  · exact B457715
  · exact B457719
  · exact B457723
  · exact B457727
  · exact B457731
  · exact B457735
  · exact B457739
  · exact B457743
  · exact B457747
  · exact B457751
  · exact B457755
  · exact B457759
  · exact B457763
  · exact B457767
  · exact B457771
  · exact B457775
  · exact B457779
  · exact B457783
  · exact B457787
  · exact B457791
  · exact B457795
  · exact B457799
  · exact B457803
  · exact B457807
  · exact B457811
  · exact B457815
  · exact B457819
  · exact B457823
  · exact B457827
  · exact B457831
  · exact B457835
  · exact B457839
  · exact B457843
  · exact B457847
  · exact B457851
  · exact B457855
  · exact B457859
  · exact B457863
  · exact B457867
  · exact B457871
  · exact B457875
  · exact B457879
  · exact B457883
  · exact B457887
  · exact B457891
  · exact B457895
  · exact B457899
  · exact B457903
  · exact B457907
  · exact B457911
  · exact B457915
  · exact B457919
  · exact B457923
  · exact B457927
  · exact B457931
  · exact B457935
  · exact B457939
  · exact B457943
  · exact B457947
  · exact B457951
  · exact B457955
  · exact B457959
  · exact B457963
  · exact B457967
  · exact B457971
  · exact B457975
  · exact B457979
  · exact B457983
  · exact B457987
  · exact B457991
  · exact B457995
  · exact B457999
  · exact B458003
  · exact B458007
  · exact B458011
  · exact B458015
  · exact B458019
  · exact B458023
  · exact B458027
  · exact B458031
  · exact B458035
  · exact B458039
  · exact B458043
  · exact B458047
  · exact B458051
  · exact B458055
  · exact B458059
  · exact B458063
  · exact B458067
  · exact B458071
  · exact B458075
  · exact B458079
  · exact B458083
  · exact B458087
  · exact B458091
  · exact B458095
  · exact B458099
  · exact B458103
  · exact B458107
  · exact B458111
  · exact B458115
  · exact B458119
  · exact B458123
  · exact B458127
  · exact B458131
  · exact B458135
  · exact B458139
  · exact B458143
  · exact B458147
  · exact B458151
  · exact B458155
  · exact B458159
  · exact B458163
  · exact B458167
  · exact B458171
  · exact B458175
  · exact B458179
  · exact B458183
  · exact B458187
  · exact B458191
  · exact B458195
  · exact B458199
  · exact B458203
  · exact B458207
  · exact B458211
  · exact B458215
  · exact B458219
  · exact B458223
  · exact B458227
  · exact B458231
  · exact B458235
  · exact B458239
  · exact B458243
  · exact B458247
  · exact B458251
  · exact B458255
  · exact B458259
  · exact B458263
  · exact B458267
  · exact B458271
  · exact B458275
  · exact B458279
  · exact B458283
  · exact B458287
  · exact B458291
  · exact B458295
  · exact B458299
  · exact B458303
  · exact B458307
  · exact B458311
  · exact B458315
  · exact B458319
  · exact B458323
  · exact B458327
  · exact B458331
  · exact B458335
  · exact B458339
  · exact B458343
  · exact B458347
  · exact B458351
  · exact B458355
  · exact B458359
  · exact B458363
  · exact B458367
  · exact B458371
  · exact B458375
  · exact B458379
  · exact B458383
  · exact B458387
  · exact B458391
  · exact B458395
  · exact B458399
  · exact B458403
  · exact B458407
  · exact B458411
  · exact B458415
  · exact B458419
  · exact B458423
  · exact B458427
  · exact B458431
  · exact B458435
  · exact B458439
  · exact B458443
  · exact B458447
  · exact B458451
  · exact B458455
  · exact B458459
  · exact B458463
  · exact B458467
  · exact B458471
  · exact B458475
  · exact B458479
  · exact B458483
  · exact B458487
  · exact B458491
  · exact B458495
  · exact B458499
  · exact B458503
  · exact B458507
  · exact B458511
  · exact B458515
  · exact B458519
  · exact B458523
  · exact B458527
  · exact B458531
  · exact B458535
  · exact B458539
  · exact B458543
  · exact B458547
  · exact B458551
  · exact B458555
  · exact B458559
  · exact B458563
  · exact B458567
  · exact B458571
  · exact B458575
  · exact B458579

theorem C1 (j : ℕ) (h1 : 114645 ≤ j) (h2 : j ≤ 114944) : Blo 455782 (4 * j + 3) := by
  interval_cases j
  · exact B458583
  · exact B458587
  · exact B458591
  · exact B458595
  · exact B458599
  · exact B458603
  · exact B458607
  · exact B458611
  · exact B458615
  · exact B458619
  · exact B458623
  · exact B458627
  · exact B458631
  · exact B458635
  · exact B458639
  · exact B458643
  · exact B458647
  · exact B458651
  · exact B458655
  · exact B458659
  · exact B458663
  · exact B458667
  · exact B458671
  · exact B458675
  · exact B458679
  · exact B458683
  · exact B458687
  · exact B458691
  · exact B458695
  · exact B458699
  · exact B458703
  · exact B458707
  · exact B458711
  · exact B458715
  · exact B458719
  · exact B458723
  · exact B458727
  · exact B458731
  · exact B458735
  · exact B458739
  · exact B458743
  · exact B458747
  · exact B458751
  · exact B458755
  · exact B458759
  · exact B458763
  · exact B458767
  · exact B458771
  · exact B458775
  · exact B458779
  · exact B458783
  · exact B458787
  · exact B458791
  · exact B458795
  · exact B458799
  · exact B458803
  · exact B458807
  · exact B458811
  · exact B458815
  · exact B458819
  · exact B458823
  · exact B458827
  · exact B458831
  · exact B458835
  · exact B458839
  · exact B458843
  · exact B458847
  · exact B458851
  · exact B458855
  · exact B458859
  · exact B458863
  · exact B458867
  · exact B458871
  · exact B458875
  · exact B458879
  · exact B458883
  · exact B458887
  · exact B458891
  · exact B458895
  · exact B458899
  · exact B458903
  · exact B458907
  · exact B458911
  · exact B458915
  · exact B458919
  · exact B458923
  · exact B458927
  · exact B458931
  · exact B458935
  · exact B458939
  · exact B458943
  · exact B458947
  · exact B458951
  · exact B458955
  · exact B458959
  · exact B458963
  · exact B458967
  · exact B458971
  · exact B458975
  · exact B458979
  · exact B458983
  · exact B458987
  · exact B458991
  · exact B458995
  · exact B458999
  · exact B459003
  · exact B459007
  · exact B459011
  · exact B459015
  · exact B459019
  · exact B459023
  · exact B459027
  · exact B459031
  · exact B459035
  · exact B459039
  · exact B459043
  · exact B459047
  · exact B459051
  · exact B459055
  · exact B459059
  · exact B459063
  · exact B459067
  · exact B459071
  · exact B459075
  · exact B459079
  · exact B459083
  · exact B459087
  · exact B459091
  · exact B459095
  · exact B459099
  · exact B459103
  · exact B459107
  · exact B459111
  · exact B459115
  · exact B459119
  · exact B459123
  · exact B459127
  · exact B459131
  · exact B459135
  · exact B459139
  · exact B459143
  · exact B459147
  · exact B459151
  · exact B459155
  · exact B459159
  · exact B459163
  · exact B459167
  · exact B459171
  · exact B459175
  · exact B459179
  · exact B459183
  · exact B459187
  · exact B459191
  · exact B459195
  · exact B459199
  · exact B459203
  · exact B459207
  · exact B459211
  · exact B459215
  · exact B459219
  · exact B459223
  · exact B459227
  · exact B459231
  · exact B459235
  · exact B459239
  · exact B459243
  · exact B459247
  · exact B459251
  · exact B459255
  · exact B459259
  · exact B459263
  · exact B459267
  · exact B459271
  · exact B459275
  · exact B459279
  · exact B459283
  · exact B459287
  · exact B459291
  · exact B459295
  · exact B459299
  · exact B459303
  · exact B459307
  · exact B459311
  · exact B459315
  · exact B459319
  · exact B459323
  · exact B459327
  · exact B459331
  · exact B459335
  · exact B459339
  · exact B459343
  · exact B459347
  · exact B459351
  · exact B459355
  · exact B459359
  · exact B459363
  · exact B459367
  · exact B459371
  · exact B459375
  · exact B459379
  · exact B459383
  · exact B459387
  · exact B459391
  · exact B459395
  · exact B459399
  · exact B459403
  · exact B459407
  · exact B459411
  · exact B459415
  · exact B459419
  · exact B459423
  · exact B459427
  · exact B459431
  · exact B459435
  · exact B459439
  · exact B459443
  · exact B459447
  · exact B459451
  · exact B459455
  · exact B459459
  · exact B459463
  · exact B459467
  · exact B459471
  · exact B459475
  · exact B459479
  · exact B459483
  · exact B459487
  · exact B459491
  · exact B459495
  · exact B459499
  · exact B459503
  · exact B459507
  · exact B459511
  · exact B459515
  · exact B459519
  · exact B459523
  · exact B459527
  · exact B459531
  · exact B459535
  · exact B459539
  · exact B459543
  · exact B459547
  · exact B459551
  · exact B459555
  · exact B459559
  · exact B459563
  · exact B459567
  · exact B459571
  · exact B459575
  · exact B459579
  · exact B459583
  · exact B459587
  · exact B459591
  · exact B459595
  · exact B459599
  · exact B459603
  · exact B459607
  · exact B459611
  · exact B459615
  · exact B459619
  · exact B459623
  · exact B459627
  · exact B459631
  · exact B459635
  · exact B459639
  · exact B459643
  · exact B459647
  · exact B459651
  · exact B459655
  · exact B459659
  · exact B459663
  · exact B459667
  · exact B459671
  · exact B459675
  · exact B459679
  · exact B459683
  · exact B459687
  · exact B459691
  · exact B459695
  · exact B459699
  · exact B459703
  · exact B459707
  · exact B459711
  · exact B459715
  · exact B459719
  · exact B459723
  · exact B459727
  · exact B459731
  · exact B459735
  · exact B459739
  · exact B459743
  · exact B459747
  · exact B459751
  · exact B459755
  · exact B459759
  · exact B459763
  · exact B459767
  · exact B459771
  · exact B459775
  · exact B459779

theorem solution (m : ℕ) (hlo : 455782 ≤ m) (hhi : m ≤ 459782) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 113945 ≤ j := by omega
    have hj2 : j ≤ 114944 := by omega
    have hb : Blo 455782 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 114645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
